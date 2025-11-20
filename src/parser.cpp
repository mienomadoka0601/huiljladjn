/**
 * @file parser.cpp
 * @brief Parsing implementation for Scheme syntax tree to expression tree conversion
 * 
 * This file implements the parsing logic that converts syntax trees into
 * expression trees that can be evaluated.
 * primitive operations, and function applications.
 */

#include "RE.hpp"
#include "Def.hpp"
#include "syntax.hpp"
#include "value.hpp"
#include "expr.hpp"
#include <map>
#include <string>
#include <iostream>

#define mp make_pair
using std::string;
using std::vector;
using std::pair;

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

/**
 * @brief Default parse method (should be overridden by subclasses)
 */
Expr Syntax::parse(Assoc &env) {
    throw RuntimeError("Unimplemented parse method");
}

Expr Number::parse(Assoc &env) {
    return Expr(new Fixnum(n));
}

Expr RationalSyntax::parse(Assoc &env) {
    //TODO: complete the rational parser
    return Expr(new RationalNum(numerator,denominator));
}

Expr SymbolSyntax::parse(Assoc &env) {
    return Expr(new Var(s));
}

Expr StringSyntax::parse(Assoc &env) {
    return Expr(new StringExpr(s));
}

Expr TrueSyntax::parse(Assoc &env) {
    return Expr(new True());
}

Expr FalseSyntax::parse(Assoc &env) {
    return Expr(new False());
}

Expr List::parse(Assoc &env) {
    if (stxs.empty()) {
        return Expr(new Quote(Syntax(new List())));
    }

    //TODO: check if the first element is a symbol
    //If not, use Apply function to package to a closure;
    //If so, find whether it's a variable or a keyword;
    SymbolSyntax *id = dynamic_cast<SymbolSyntax*>(stxs[0].get());
    if (id == nullptr) {
        //TODO: TO COMPLETE THE LOGIC
        Expr rator=stxs[0]->parse(env);
        vector<Expr> args;
        for(int i=1;i<stxs.size();i++)
            args.push_back(stxs[i]->parse(env));
        return Expr(new Apply(rator,args));
    }else{
    string op = id->s;
    if (reserved_words.count(op) != 0) {
    	switch (reserved_words[op]) {
			//TODO: TO COMPLETE THE reserve_words PARSER LOGIC
            case E_QUOTE:
            if (stxs.size() < 2) {
                throw RuntimeError("quote requires one argument");
            }
            return Expr(new Quote(stxs[1]));
            case E_BEGIN: {
                vector<Expr> es;
                for (size_t i = 1; i < stxs.size(); ++i) es.push_back(stxs[i].parse(env));
                return Expr(new Begin(es));
            }
            case E_IF: {
                if (stxs.size() != 4) {
                    throw RuntimeError("if requires 3 arguments: (if <cond> <then> <else>)");
                }
                Expr cond = stxs[1]->parse(env);
                Expr conseq = stxs[2]->parse(env);
                Expr alter = stxs[3]->parse(env);
                return Expr(new If(cond, conseq, alter));
            }
            case E_COND: {
                if(stxs.size()<=1)throw RuntimeError("Invalid cond clause");
                vector<vector<Expr>> clauses;
                for (size_t i = 1; i < stxs.size(); ++i) {
                    List *cl = dynamic_cast<List*>(stxs[i].get());
                    if (!cl) throw RuntimeError("cond clauses must be lists");
                    vector<Expr> clause_exprs;
                    for (auto &cstx : cl->stxs) clause_exprs.push_back(cstx.parse(env));
                    clauses.push_back(clause_exprs);
                }
                return Expr(new Cond(clauses));
            }
            case E_LAMBDA: {
                if (stxs.size() < 3) throw RuntimeError("lambda requires a parameter list and a body");
                List *plist = dynamic_cast<List*>(stxs[1].get());
                if (!plist) throw RuntimeError("lambda parameter list must be a list of symbols");
                vector<string> names;
                for (auto &p : plist->stxs) {
                    SymbolSyntax *sym = dynamic_cast<SymbolSyntax*>(p.get());
                    if (!sym) throw RuntimeError("lambda parameters must be symbols");
                    names.push_back(sym->s);
                }
                Assoc new_env = env;
                for (const auto &param : names) {
                    new_env = extend(param, IntegerV(0), new_env);
                }
                if (stxs.size() == 3) {
                    Expr body = stxs[2].parse(new_env);
                    return Expr(new Lambda(names, body));
                } else {
                    vector<Expr> bodies;
                    for (size_t i = 2; i < stxs.size(); ++i) bodies.push_back(stxs[i].parse(new_env));
                    return Expr(new Lambda(names, Expr(new Begin(std::move(bodies)))));
                }
            }
            case E_DEFINE: {
                if (stxs.size() < 3) throw RuntimeError("define requires a name and a value");
                auto func_list = dynamic_cast<List*>(stxs[1].get());
                    if (func_list != nullptr) {
                        if (func_list->stxs.empty()) {
                            throw RuntimeError("define: function name missing");
                        }
                        
                        auto func_name = dynamic_cast<SymbolSyntax*>(func_list->stxs[0].get());
                        if (func_name == nullptr) {
                            throw RuntimeError("define: function name must be a symbol");
                        }

                        std::vector<std::string> params;
                        for (size_t i = 1; i < func_list->stxs.size(); ++i) {
                            auto param = dynamic_cast<SymbolSyntax*>(func_list->stxs[i].get());
                            if (param == nullptr) {
                                throw RuntimeError("define: parameter must be a symbol");
                            }
                            params.push_back(param->s);
                        }
                        Assoc env2 = env;
                        for (const auto& p : params) {
                            env2 = extend(p, Value(nullptr), env2);
                        }
                        std::vector<Expr> body_exprs;
                        for (size_t i = 2; i < stxs.size(); ++i) {
                            body_exprs.push_back(stxs[i]->parse(env2));
                        }
                        Expr lambda_body(nullptr);
                        if (body_exprs.empty()) {
                            lambda_body = Expr(new MakeVoid());
                        } else if (body_exprs.size() == 1){
                            lambda_body = body_exprs[0];
                        } else {
                            lambda_body = Expr(new Begin(body_exprs));
                        }

                        Expr lambda_expr = Expr(new Lambda(params, lambda_body));
                        
                        return Expr(new Define(func_name->s, lambda_expr));
                    } else {
                        auto var_name = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                        if (var_name == nullptr) {
                            throw RuntimeError("define: variable of function name must be a symbol");
                        }
                        return Expr(new Define(var_name->s, stxs[2]->parse(env)));
                    }
            }
            case E_LET: {
                if (stxs.size() < 3) throw RuntimeError("let requires bindings and a body");
                List *bindlist = dynamic_cast<List*>(stxs[1].get());
                if (!bindlist) throw RuntimeError("let bindings must be a list");
                vector<pair<string, Expr>> binds;
                Assoc new_env=env;
                for (auto &b : bindlist->stxs) {
                    List *pairlst = dynamic_cast<List*>(b.get());
                    if (!pairlst || pairlst->stxs.size() != 2) throw RuntimeError("each let binding must be a (name expr) pair");
                    SymbolSyntax *name = dynamic_cast<SymbolSyntax*>(pairlst->stxs[0].get());
                    if (!name) throw RuntimeError("let binding name must be a symbol");
                    Expr val = pairlst->stxs[1].parse(env);
                    binds.push_back(mp(name->s, val));
                    new_env = extend(name->s, IntegerV(0), new_env);
                }
                if (stxs.size() == 3) {
                    Expr body = stxs[2].parse(new_env);
                    return Expr(new Let(binds, body));
                } else {
                    vector<Expr> bodies;
                    for (size_t i = 2; i < stxs.size(); ++i) bodies.push_back(stxs[i].parse(new_env));
                    Expr body = Expr(new Begin(bodies));
                    return Expr(new Let(binds, body));
                }
            }
            case E_LETREC: {
                if (stxs.size() < 3) throw RuntimeError("letrec requires bindings and a body");
                List *bindlist = dynamic_cast<List*>(stxs[1].get());
                if (!bindlist) throw RuntimeError("letrec bindings must be a list");
                vector<pair<string, Expr>> binds;
                Assoc new_env=env;
                for (auto &b : bindlist->stxs) {
                    List *pairlst = dynamic_cast<List*>(b.get());
                    if (!pairlst || pairlst->stxs.size() != 2) throw RuntimeError("each letrec binding must be a (name expr) pair");
                    SymbolSyntax *name = dynamic_cast<SymbolSyntax*>(pairlst->stxs[0].get());
                    if (!name) throw RuntimeError("letrec binding name must be a symbol");
                    new_env = extend(name->s, IntegerV(0), new_env);
                }
                for(auto &b : bindlist->stxs) {
                    List *binding_pair = dynamic_cast<List*>(b.get());
                    SymbolSyntax *var = dynamic_cast<SymbolSyntax*>(binding_pair->stxs[0].get());
                    Expr value_expr = binding_pair->stxs[1]->parse(new_env);
                    binds.push_back({var->s, value_expr});
                }
                if (stxs.size() == 3) {
                    Expr body = stxs[2].parse(new_env);
                    return Expr(new Letrec(binds, body));
                } else {
                    vector<Expr> bodies;
                    for (size_t i = 2; i < stxs.size(); ++i) bodies.push_back(stxs[i].parse(new_env));
                    Expr body = Expr(new Begin(bodies));
                    return Expr(new Letrec(binds, body));
                }
            }
            case E_SET: {
                if (stxs.size() != 3) throw RuntimeError("set! requires a name and a value");
                SymbolSyntax *name = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                if (!name) throw RuntimeError("set! first argument must be a symbol");
                Expr val = stxs[2].parse(env);
                return Expr(new Set(name->s, val));
            }
        	default:
            	throw RuntimeError("Unknown reserved word: " + op);
    	}
    }
    if (find(op, env).get() != nullptr) {
        Expr rator=Expr(new Var(op));
        vector<Expr>args;
        for(int i=1;i<stxs.size();i++) args.push_back(stxs[i]->parse(env));
        return Expr(new Apply(rator,args));
    }
    if (primitives.count(op) != 0) {
        vector<Expr> parameters;
        for (size_t i = 1; i < stxs.size(); ++i) {
            parameters.push_back(stxs[i]->parse(env));
        }
        ExprType op_type = primitives[op];
        if (op_type == E_PLUS) {
            if (parameters.size() == 2) {
                return Expr(new Plus(parameters[0], parameters[1])); 
            } else {
                return Expr(new PlusVar(parameters));
            }
        } else if (op_type == E_MINUS) {
            if(parameters.size()==2){
                return Expr(new Minus(parameters[0],parameters[1]));
            }
            else{
                return Expr(new MinusVar(parameters));
            }
            //TODO: TO COMPLETE THE LOGIC
        } else if (op_type == E_MUL) {
            //TODO: TO COMPLETE THE LOGIC
            if(parameters.size()==2){
                return Expr(new Mult(parameters[0],parameters[1]));
            }
            else{
                return Expr(new MultVar(parameters));
            }
        }  else if (op_type == E_DIV) {
            //TODO: TO COMPLETE THE LOGIC
            if(parameters.size()==2){
                return Expr(new Div(parameters[0],parameters[1]));
            }
            else{
                return Expr(new DivVar(parameters));
            }
        } else if (op_type == E_MODULO) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for modulo");
            }
            return Expr(new Modulo(parameters[0], parameters[1]));
        } else if (op_type == E_LIST) {
            return Expr(new ListFunc(parameters));
        } else if (op_type == E_LT) {
            //TODO: TO COMPLETE THE LOGIC
            if(parameters.size()<2){
                throw RuntimeError("Wrong number of arguments for less");
            }
            else if(parameters.size()==2){
            return Expr(new Less(parameters[0], parameters[1]));
            }
            else{
                return Expr(new LessVar(parameters));
            }
        } else if (op_type == E_LE) {
            //TODO: TO COMPLETE THE LOGIC
            if(parameters.size()<2){
                throw RuntimeError("Wrong number of arguments for lesseq");
            }
            else if(parameters.size()==2){
            return Expr(new LessEq(parameters[0], parameters[1]));
            }
            else{
            return Expr(new LessEqVar(parameters));
            }
        } else if (op_type == E_EQ) {
            //TODO: TO COMPLETE THE LOGIC
            if(parameters.size()<2){
                throw RuntimeError("Wrong number of arguments for equal");
            }
            else if(parameters.size()==2){
            return Expr(new Equal(parameters[0], parameters[1]));
            }
            else{
            return Expr(new EqualVar(parameters));
            }
        } else if (op_type == E_GE) {
            //TODO: TO COMPLETE THE LOGIC
            if(parameters.size()<2){
                throw RuntimeError("Wrong number of arguments for greateq");
            }
            else if(parameters.size()==2){
            return Expr(new GreaterEq(parameters[0], parameters[1]));
            }
            else{
            return Expr(new GreaterEqVar(parameters));
            }
        } else if (op_type == E_GT) {
            //TODO: TO COMPLETE THE LOGIC
            if(parameters.size()<2){
                throw RuntimeError("Wrong number of arguments for greater");
            }
            else if(parameters.size()==2){
            return Expr(new Greater(parameters[0], parameters[1]));
            }
            else{
            return Expr(new GreaterVar(parameters));
            }
        } else if (op_type == E_AND) {
            return Expr(new AndVar(parameters));
        } else if (op_type == E_OR) {
            return Expr(new OrVar(parameters));
        } else if(op_type==E_NOT){
            if(parameters.size()!=1) throw RuntimeError("Wrong number of arguments for not");
            return Expr(new Not(parameters[0]));
        }else if(op_type==E_CONS){
            if(parameters.size()!=2) throw RuntimeError("Wrong number of arguments for cons");
            return Expr(new Cons(parameters[0],parameters[1]));
        }else if(op_type==E_CAR){
            if(parameters.size()!=1) throw RuntimeError("Wrong number of arguments for car");
            return Expr(new Car(parameters[0]));
        }else if(op_type==E_CDR){
            if(parameters.size()!=1) throw RuntimeError("Wrong number of arguments for cdr");
            return Expr(new Cdr(parameters[0]));
        }else if(op_type==E_LIST){
            return Expr(new ListFunc(parameters));
        }else if(op_type==E_SETCAR){
            if(parameters.size()!=2) throw RuntimeError("Wrong number of arguments for setcar");
            return Expr(new SetCar(parameters[0],parameters[1]));
        }else if(op_type==E_SETCDR){
            if(parameters.size()!=2) throw RuntimeError("Wrong number of arguments for setcdr");
            return Expr(new SetCdr(parameters[0],parameters[1]));
        }else if(op_type==E_EQQ){
            if(parameters.size()!=2) throw RuntimeError("Wrong number of arguments for eq?");
            return Expr(new IsEq(parameters[0],parameters[1]));
        }else if(op_type==E_BOOLQ){
            if(parameters.size()!=1) throw RuntimeError("Wrong number of arguments for boolean?");
            return Expr(new IsBoolean(parameters[0]));
        }else if(op_type==E_INTQ){
            if(parameters.size()!=1) throw RuntimeError("Wrong number of arguments for number?");
            return Expr(new IsFixnum(parameters[0]));
        }else if(op_type==E_NULLQ){
            if(parameters.size()!=1) throw RuntimeError("Wrong number of arguments for null?");
            return Expr(new IsNull(parameters[0]));
        }else if(op_type==E_PAIRQ){
            if(parameters.size()!=1) throw RuntimeError("Wrong number of arguments for pair?");
            return Expr(new IsPair(parameters[0]));
        }else if(op_type==E_PROCQ){
            if(parameters.size()!=1) throw RuntimeError("Wrong number of arguments for procedure?");
            return Expr(new IsProcedure(parameters[0]));
        }else if(op_type==E_SYMBOLQ){
            if(parameters.size()!=1) throw RuntimeError("Wrong number of arguments for symbol?");
            return Expr(new IsSymbol(parameters[0]));
        }else if(op_type==E_LISTQ){
            if(parameters.size()!=1) throw RuntimeError("Wrong number of arguments for list?");
            return Expr(new IsList(parameters[0]));
        }else if(op_type==E_STRINGQ){
            if(parameters.size()!=1) throw RuntimeError("Wrong number of arguments for string?");
            return Expr(new IsString(parameters[0]));
        }else if(op_type==E_EXIT){
            if(!parameters.empty()) throw RuntimeError("Wrong number of arguments for exit");
            return Expr(new Exit());
        }else if(op_type==E_DISPLAY){
            if(parameters.size()!=1) throw RuntimeError("Wrong number of arguments for display");
            return Expr(new Display(parameters[0]));
        }else if(op_type==E_VOID){
            if(!parameters.empty()) throw RuntimeError("Wrong number of arguments for void");
            return Expr(new MakeVoid());
        }else if (op_type == E_EXPT) {
            if (parameters.size() != 2) throw RuntimeError("Wrong number of arguments for expt");
            return Expr(new Expt(parameters[0], parameters[1]));
        }else {
            //TODO: TO COMPLETE THE LOGIC
            throw RuntimeError("Unknown primitive operation");
        }
    }

    

    //default: use Apply to be an expression
    //TODO: TO COMPLETE THE PARSER LOGIC
    Expr rator=stxs[0]->parse(env);
    vector<Expr>args;
    for(int i=1;i<stxs.size();i++)args.push_back(stxs[i]->parse(env));
    return Expr(new Apply(rator,args));
}
}
