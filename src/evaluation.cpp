/**
 * @file evaluation.cpp
 * @brief Expression evaluation implementation for the Scheme interpreter
 * @author luke36
 * 
 * This file implements evaluation methods for all expression types in the Scheme
 * interpreter. Functions are organized according to ExprType enumeration order
 * from Def.hpp for consistency and maintainability.
 */

#include "value.hpp"
#include "expr.hpp" 
#include "RE.hpp"
#include "syntax.hpp"
#include <cstring>
#include <vector>
#include <map>
#include <climits>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;
Value syntaxToValue(const Syntax &stx) {
    if (Number *num = dynamic_cast<Number*>(stx.get())) {
        return IntegerV(num->n);
    }
    if (RationalSyntax *rat = dynamic_cast<RationalSyntax*>(stx.get())) {
        return RationalV(rat->numerator, rat->denominator);
    }
    if (TrueSyntax *t = dynamic_cast<TrueSyntax*>(stx.get())) {
        return BooleanV(true);
    }
    if (FalseSyntax *f = dynamic_cast<FalseSyntax*>(stx.get())) {
        return BooleanV(false);
    }
    if (SymbolSyntax *sym = dynamic_cast<SymbolSyntax*>(stx.get())) {
        return SymbolV(sym->s);
    }
    if (StringSyntax *str = dynamic_cast<StringSyntax*>(stx.get())) {
        return StringV(str->s);
    }
    if (List *lst = dynamic_cast<List*>(stx.get())) {
        const auto& stxs=lst->stxs;
        if(stxs.empty()) return NullV();
        Value result = NullV();
        int dot_pos=-1;
        for (int i=0;i<stxs.size();++i) {
            if(auto m=dynamic_cast<SymbolSyntax*>(stxs[i].get())){
                if (m->s == ".") 
                    dot_pos = i;
            }
        }
        if(dot_pos!=-1){
            Value car_list=NullV();
            for(int i=dot_pos-1;i>=0;i--){
                car_list=PairV(syntaxToValue(stxs[i]),car_list);
            }
            Value cdr=syntaxToValue(stxs[dot_pos+1]);
            if(car_list->v_type==V_NULL){
                return cdr;
            }
            else{
                Value current=car_list;
                while(1){
                    Pair* pair=dynamic_cast<Pair*>(current.get());
                    if(pair->cdr->v_type==V_NULL){
                        pair->cdr=cdr;
                        break;
                    }
                    current=pair->cdr;
                }
                return car_list;
            }
        }
        for (int i = stxs.size() - 1; i >= 0; --i) {
            result = PairV(syntaxToValue(stxs[i]), result);
        }
        return result;
    }
    throw RuntimeError("Unsupported quoted syntax");
}

Value Fixnum::eval(Assoc &e) { // evaluation of a fixnum
    return IntegerV(n);
}

Value RationalNum::eval(Assoc &e) { // evaluation of a rational number
    return RationalV(numerator, denominator);
}

Value StringExpr::eval(Assoc &e) { // evaluation of a string
    return StringV(s);
}

Value True::eval(Assoc &e) { // evaluation of #t
    return BooleanV(true);
}

Value False::eval(Assoc &e) { // evaluation of #f
    return BooleanV(false);
}

Value MakeVoid::eval(Assoc &e) { // (void)
    return VoidV();
}

Value Exit::eval(Assoc &e) { // (exit)
    return TerminateV();
}

Value Unary::eval(Assoc &e) { // evaluation of single-operator primitive
    return evalRator(rand->eval(e));
}

Value Binary::eval(Assoc &e) { // evaluation of two-operators primitive
    return evalRator(rand1->eval(e), rand2->eval(e));
}

Value Variadic::eval(Assoc &e) { // evaluation of multi-operator primitive
    // TODO: TO COMPLETE THE VARIADIC CLASS
    std::vector<Value> vals;
    for (auto &r : this->rands) vals.push_back(r->eval(e));
    return evalRator(vals);
}

Value Var::eval(Assoc &e) { // evaluation of variable
    // TODO: TO identify the invalid variable
    // We request all valid variable just need to be a symbol,you should promise:
    //The first character of a variable name cannot be a digit or any character from the set: {.@}
    //If a string can be recognized as a number, it will be prioritized as a number. For example: 1, -1, +123, .123, +124., 1e-3
    //Variable names can overlap with primitives and reserve_words
    //Variable names can contain any non-whitespace characters except #, ', ", `, but the first character cannot be a digit
    //When a variable is not defined in the current scope, your interpreter should output RuntimeError
    
    Value matched_value = find(x, e);
    if (matched_value.get() == nullptr) {
        if (primitives.count(x)) {
             static std::map<ExprType, std::pair<Expr, std::vector<std::string>>> primitive_map = {
                    {E_VOID,     {new MakeVoid(), {}}},
                    {E_EXIT,     {new Exit(), {}}},
                    {E_BOOLQ,    {new IsBoolean(new Var("parm")), {"parm"}}},
                    {E_INTQ,     {new IsFixnum(new Var("parm")), {"parm"}}},
                    {E_NULLQ,    {new IsNull(new Var("parm")), {"parm"}}},
                    {E_PAIRQ,    {new IsPair(new Var("parm")), {"parm"}}},
                    {E_PROCQ,    {new IsProcedure(new Var("parm")), {"parm"}}},
                    {E_SYMBOLQ,  {new IsSymbol(new Var("parm")), {"parm"}}},
                    {E_STRINGQ,  {new IsString(new Var("parm")), {"parm"}}},
                    {E_DISPLAY,  {new Display(new Var("parm")), {"parm"}}},
                    {E_PLUS,     {new PlusVar({}),  {}}},
                    {E_MINUS,    {new MinusVar({}), {}}},
                    {E_MUL,      {new MultVar({}),  {}}},
                    {E_DIV,      {new DivVar({}),   {}}},
                    {E_MODULO,   {new Modulo(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_EXPT,     {new Expt(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_EQQ,      {new EqualVar({}), {}}},
                    {E_EQ,       {new EqualVar({}), {}}},
                    {E_LT,       {new LessVar({}), {}}},
                    {E_LE,       {new LessEqVar({}), {}}},
                    {E_GE,       {new GreaterEqVar({}), {}}},
                    {E_GT,       {new GreaterVar({}), {}}},
                    {E_CONS,     {new Cons(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_CAR,      {new Car(new Var("parm")), {"parm"}}},
                    {E_CDR,      {new Cdr(new Var("parm")), {"parm"}}},
                    {E_NOT,      {new Not(new Var("parm")), {"parm"}}},
                    {E_LIST,     {new ListFunc({}), {}}},
                    {E_LISTQ,    {new IsList(new Var("parm")), {"parm"}}},
                    {E_SETCAR,   {new SetCar(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_SETCDR,   {new SetCdr(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_AND,      {new AndVar({}), {}}},
                    {E_OR,       {new OrVar({}), {}}}
            };

            auto it = primitive_map.find(primitives[x]);
            //TOD0:to PASS THE parameters correctly;
            //COMPLETE THE CODE WITH THE HINT IN IF SENTENCE WITH CORRECT RETURN VALUE
            if (it != primitive_map.end()) {
                //TODO
                return ProcedureV(it->second.second, it->second.first,e);
            }
      }
      throw(RuntimeError("Undefined variable"+x));
    }
    return matched_value;
}

Value Plus::evalRator(const Value &rand1, const Value &rand2) { // +
    //TODO: To complete the addition logic
    if (rand1->v_type == V_INT && rand2->v_type == V_INT){
        int plus1 = dynamic_cast<Integer*>(rand1.get())->n;
        int plus2 = dynamic_cast<Integer*>(rand2.get())->n;
        return IntegerV(plus1 + plus2);
    }
    else if(rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL){
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int numerator = r1->numerator * r2->denominator + r2->numerator * r1->denominator;
        int denominator = r1->denominator * r2->denominator;
        return RationalV(numerator, denominator);
    }
    else if(rand1->v_type == V_INT && rand2->v_type == V_RATIONAL){
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int numerator = dynamic_cast<Integer*>(rand1.get())->n * r2->denominator + r2->numerator;
        int denominator = r2->denominator;
        return RationalV(numerator, denominator);
    }
    else if(rand1->v_type == V_RATIONAL && rand2->v_type == V_INT){
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int numerator = r1->numerator + dynamic_cast<Integer*>(rand2.get())->n * r1->denominator;
        int denominator = r1->denominator;
        return RationalV(numerator, denominator);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Minus::evalRator(const Value &rand1, const Value &rand2) { // -
    //TODO: To complete the substraction logic
    if (rand1->v_type == V_INT && rand2->v_type == V_INT){
        int minus1 = dynamic_cast<Integer*>(rand1.get())->n;
        int minus2 = dynamic_cast<Integer*>(rand2.get())->n;
        return IntegerV(minus1 - minus2);
    }
    else if(rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL){
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int numerator = r1->numerator * r2->denominator - r2->numerator * r1->denominator;
        int denominator = r1->denominator * r2->denominator;
        return RationalV(numerator, denominator);
    }
    else if(rand1->v_type == V_INT && rand2->v_type == V_RATIONAL){
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int numerator = dynamic_cast<Integer*>(rand1.get())->n * r2->denominator - r2->numerator;
        int denominator = r2->denominator;
        return RationalV(numerator, denominator);
    }
    else if(rand1->v_type == V_RATIONAL && rand2->v_type == V_INT){
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int numerator = r1->numerator - dynamic_cast<Integer*>(rand2.get())->n * r1->denominator;
        int denominator = r1->denominator;
        return RationalV(numerator, denominator);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Mult::evalRator(const Value &rand1, const Value &rand2) { // *
    //TODO: To complete the Multiplication logic
    if (rand1->v_type == V_INT && rand2->v_type == V_INT){
        int mult1 = dynamic_cast<Integer*>(rand1.get())->n;
        int mult2 = dynamic_cast<Integer*>(rand2.get())->n;
        return IntegerV(mult1*mult2);
    }
    else if(rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL){
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int numerator = r1->numerator * r2->numerator;
        int denominator = r1->denominator * r2->denominator;
        return RationalV(numerator, denominator);
    }
    else if(rand1->v_type == V_INT && rand2->v_type == V_RATIONAL){
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int numerator = dynamic_cast<Integer*>(rand1.get())->n *r2->numerator;
        int denominator = r2->denominator;
        return RationalV(numerator, denominator);
    }
    else if(rand1->v_type == V_RATIONAL && rand2->v_type == V_INT){
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int numerator = dynamic_cast<Integer*>(rand2.get())->n * r1->numerator;
        int denominator = r1->denominator;
        return RationalV(numerator, denominator);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Div::evalRator(const Value &rand1, const Value &rand2) { // /
    //TODO: To complete the dicision logic
    if (rand1->v_type == V_INT && rand2->v_type == V_INT){
        int dividend = dynamic_cast<Integer*>(rand1.get())->n;
        int divisor = dynamic_cast<Integer*>(rand2.get())->n;
        if(divisor == 0){
            throw(RuntimeError("Division by zero"));
        }
        return IntegerV(dividend/divisor);
    }
    else if(rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL){
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int numerator = r1->numerator * r2->denominator;
        int denominator = r1->denominator * r2->numerator;
        return RationalV(numerator, denominator);
    }
    else if(rand1->v_type == V_INT && rand2->v_type == V_RATIONAL){
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int numerator = dynamic_cast<Integer*>(rand1.get())->n * r2->denominator;
        int denominator = r2->numerator;
        return RationalV(numerator, denominator);
    }
    else if(rand1->v_type == V_RATIONAL && rand2->v_type == V_INT){
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int numerator = r1->numerator;
        int denominator = dynamic_cast<Integer*>(rand2.get())->n*r1->denominator;
        return RationalV(numerator, denominator);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Modulo::evalRator(const Value &rand1, const Value &rand2) { // modulo
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int dividend = dynamic_cast<Integer*>(rand1.get())->n;
        int divisor = dynamic_cast<Integer*>(rand2.get())->n;
        if (divisor == 0) {
            throw(RuntimeError("Division by zero"));
        }
        return IntegerV(dividend % divisor);
    }
    throw(RuntimeError("modulo is only defined for integers"));
}

Value PlusVar::evalRator(const std::vector<Value> &args) { // + with multiple args
    //TODO: To complete the addition logic
    if (args.empty()) return IntegerV(0);
    bool anyRat = false;
    for (auto &a : args) if (a->v_type == V_RATIONAL) { anyRat = true; break; }
    if (!anyRat) {
        long long sum = 0;
        for (auto &a : args) {
            if (a->v_type != V_INT) throw(RuntimeError("Wrong typename"));
            sum += dynamic_cast<Integer*>(a.get())->n;
        }
        return IntegerV((int)sum);
    } else {
        long long num = 0, den = 1;
        bool first = true;
        for (auto &a : args) {
            long long n, d;
            if (a->v_type == V_INT) {
                n = dynamic_cast<Integer*>(a.get())->n;
                d = 1;
            } else if (a->v_type == V_RATIONAL) {
                Rational *r = dynamic_cast<Rational*>(a.get());
                n = r->numerator; d = r->denominator;
            } else throw(RuntimeError("Wrong typename"));

            if (first) { num = n; den = d; first = false; }
            else {
                long long new_num = num * d + n * den;
                long long new_den = den * d;
                num = new_num; den = new_den;
            }
        }
        return RationalV((int)num, (int)den);
    }
}

Value MinusVar::evalRator(const std::vector<Value> &args) { // - with multiple args
    //TODO: To complete the substraction logic
    if (args.empty()) throw(RuntimeError("Wrong number of arguments for -"));
    if (args.size() == 1) {
        Value a = args[0];
        if (a->v_type == V_INT) return IntegerV(-dynamic_cast<Integer*>(a.get())->n);
        if (a->v_type == V_RATIONAL) {
            Rational *r = dynamic_cast<Rational*>(a.get());
            return RationalV(-r->numerator, r->denominator);
        }
        throw(RuntimeError("Wrong typename"));
    }
    bool anyRat = false;
    for (auto &a : args) if (a->v_type == V_RATIONAL) { anyRat = true; break; }
    if (!anyRat) {
        long long res = dynamic_cast<Integer*>(args[0].get())->n;
        for (size_t i = 1; i < args.size(); ++i) {
            if (args[i]->v_type != V_INT) throw(RuntimeError("Wrong typename"));
            res -= dynamic_cast<Integer*>(args[i].get())->n;
        }
        return IntegerV((int)res);
    } else {
        long long num = 0, den = 1;
        if (args[0]->v_type == V_INT) { num = dynamic_cast<Integer*>(args[0].get())->n; den = 1; }
        else { Rational *r = dynamic_cast<Rational*>(args[0].get()); num = r->numerator; den = r->denominator; }
        for (size_t i = 1; i < args.size(); ++i) {
            long long n, d;
            if (args[i]->v_type == V_INT) { n = dynamic_cast<Integer*>(args[i].get())->n; d = 1; }
            else if (args[i]->v_type == V_RATIONAL) { Rational *r = dynamic_cast<Rational*>(args[i].get()); n = r->numerator; d = r->denominator; }
            else throw(RuntimeError("Wrong typename"));
            long long new_num = num * d - n * den;
            long long new_den = den * d;
            num = new_num; den = new_den;
        }
        return RationalV((int)num, (int)den);
    }
}

Value MultVar::evalRator(const std::vector<Value> &args) { // * with multiple args
    //TODO: To complete the multiplication logic
    if (args.empty()) return IntegerV(1);
    bool anyRat = false;
    for (auto &a : args) if (a->v_type == V_RATIONAL) { anyRat = true; break; }
    if (!anyRat) {
        long long prod = 1;
        for (auto &a : args) {
            if (a->v_type != V_INT) throw(RuntimeError("Wrong typename"));
            prod *= dynamic_cast<Integer*>(a.get())->n;
        }
        return IntegerV((int)prod);
    } else {
        long long num = 1, den = 1;
        for (auto &a : args) {
            long long n,d;
            if (a->v_type == V_INT) { n = dynamic_cast<Integer*>(a.get())->n; d = 1; }
            else if (a->v_type == V_RATIONAL) { Rational *r = dynamic_cast<Rational*>(a.get()); n = r->numerator; d = r->denominator; }
            else throw(RuntimeError("Wrong typename"));
            num *= n; den *= d;
        }
        return RationalV((int)num, (int)den);
    }
}

Value DivVar::evalRator(const std::vector<Value> &args) { // / with multiple args
    //TODO: To complete the divisor logic
    if (args.empty()) throw(RuntimeError("Wrong number of arguments for /"));
    if (args.size() == 1) {
        Value a = args[0];
        if (a->v_type == V_INT) return RationalV(1, dynamic_cast<Integer*>(a.get())->n);
        if (a->v_type == V_RATIONAL) {
            Rational *r = dynamic_cast<Rational*>(a.get());
            return RationalV(r->denominator, r->numerator);
        }
        throw(RuntimeError("Wrong typename"));
    }
    bool anyRat = false;
    for (auto &a : args) if (a->v_type == V_RATIONAL) { anyRat = true; break; }
    if (!anyRat) {
        long long res = dynamic_cast<Integer*>(args[0].get())->n;
        for (size_t i = 1; i < args.size(); ++i) {
            if (args[i]->v_type != V_INT) throw(RuntimeError("Wrong typename"));
            int d = dynamic_cast<Integer*>(args[i].get())->n;
            if (d == 0) throw(RuntimeError("Division by zero"));
            res /= d;
        }
        return IntegerV((int)res);
    } else {
        long long num, den;
        if (args[0]->v_type == V_INT) { num = dynamic_cast<Integer*>(args[0].get())->n; den = 1; }
        else { Rational *r = dynamic_cast<Rational*>(args[0].get()); num = r->numerator; den = r->denominator; }
        for (size_t i = 1; i < args.size(); ++i) {
            long long n,d;
            if (args[i]->v_type == V_INT) { n = dynamic_cast<Integer*>(args[i].get())->n; d = 1; }
            else { Rational *r = dynamic_cast<Rational*>(args[i].get()); n = r->numerator; d = r->denominator; }
            if (n == 0) throw(RuntimeError("Division by zero"));
            long long new_num = num * d;
            long long new_den = den * n;
            num = new_num; den = new_den;
        }
        return RationalV((int)num, (int)den);
    }
}

Value Expt::evalRator(const Value &rand1, const Value &rand2) { // expt
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int base = dynamic_cast<Integer*>(rand1.get())->n;
        int exponent = dynamic_cast<Integer*>(rand2.get())->n;
        
        if (exponent < 0) {
            throw(RuntimeError("Negative exponent not supported for integers"));
        }
        if (base == 0 && exponent == 0) {
            throw(RuntimeError("0^0 is undefined"));
        }
        
        long long result = 1;
        long long b = base;
        int exp = exponent;
        
        while (exp > 0) {
            if (exp % 2 == 1) {
                result *= b;
                if (result > INT_MAX || result < INT_MIN) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            b *= b;
            if (b > INT_MAX || b < INT_MIN) {
                if (exp > 1) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            exp /= 2;
        }
        
        return IntegerV((int)result);
    }
    throw(RuntimeError("Wrong typename"));
}

//A FUNCTION TO SIMPLIFY THE COMPARISON WITH INTEGER AND RATIONAL NUMBER
int compareNumericValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return (n1 < n2) ? -1 : (n1 > n2) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        int left = r1->numerator;
        int right = n2 * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = n1 * r2->denominator;
        int right = r2->numerator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = r1->numerator * r2->denominator;
        int right = r2->numerator * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    throw RuntimeError("Wrong typename in numeric comparison");
}

Value Less::evalRator(const Value &rand1, const Value &rand2) { // <
    //TODO: To complete the less logic
    if(compareNumericValues(rand1,rand2)==-1){
        return BooleanV(true);
    }
    else{
        return BooleanV(false);
    }
    throw(RuntimeError("Wrong typename"));
}

Value LessEq::evalRator(const Value &rand1, const Value &rand2) { // <=
    //TODO: To complete the lesseq logic
    if(compareNumericValues(rand1,rand2)!=1){
        return BooleanV(true);
    }
    else{
        return BooleanV(false);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Equal::evalRator(const Value &rand1, const Value &rand2) { // =
    //TODO: To complete the equal logic
    if(compareNumericValues(rand1,rand2)==0){
        return BooleanV(true);
    }
    else{
        return BooleanV(false);
    }
    throw(RuntimeError("Wrong typename"));
}

Value GreaterEq::evalRator(const Value &rand1, const Value &rand2) { // >=
    //TODO: To complete the greatereq logic
    if(compareNumericValues(rand1,rand2)!=-1){
        return BooleanV(true);
    }
    else{
        return BooleanV(false);
    }
    throw(RuntimeError("Wrong typename"));
}

Value Greater::evalRator(const Value &rand1, const Value &rand2) { // >
    //TODO: To complete the greater logic
    if(compareNumericValues(rand1,rand2)==1){
        return BooleanV(true);
    }
    else{
        return BooleanV(false);
    }
    throw(RuntimeError("Wrong typename"));
}

Value LessVar::evalRator(const std::vector<Value> &args) { // < with multiple args
    //TODO: To complete the less logic
    if (args.size() < 2) throw(RuntimeError("Wrong number of arguments for <"));
    for (size_t i = 0; i + 1 < args.size(); ++i) {
        if (compareNumericValues(args[i], args[i+1]) != -1) return BooleanV(false);
    }
    return BooleanV(true);
}

Value LessEqVar::evalRator(const std::vector<Value> &args) { // <= with multiple args
    //TODO: To complete the lesseq logic
    if (args.size() < 2) throw(RuntimeError("Wrong number of arguments for <="));
    for (size_t i = 0; i + 1 < args.size(); ++i) {
        if (compareNumericValues(args[i], args[i+1]) == 1) return BooleanV(false);
    }
    return BooleanV(true);
}

Value EqualVar::evalRator(const std::vector<Value> &args) { // = with multiple args
    //TODO: To complete the equal logic
    if (args.size() < 2) throw(RuntimeError("Wrong number of arguments for ="));
    for (size_t i = 0; i + 1 < args.size(); ++i) {
        if (compareNumericValues(args[i], args[i+1]) != 0) return BooleanV(false);
    }
    return BooleanV(true);
}

Value GreaterEqVar::evalRator(const std::vector<Value> &args) { // >= with multiple args
    //TODO: To complete the greatereq logic
     if (args.size() < 2) throw(RuntimeError("Wrong number of arguments for >="));
    for (size_t i = 0; i + 1 < args.size(); ++i) {
        if (compareNumericValues(args[i], args[i+1]) == -1) return BooleanV(false);
    }
    return BooleanV(true);
}

Value GreaterVar::evalRator(const std::vector<Value> &args) { // > with multiple args
    //TODO: To complete the greater logic
    if (args.size() < 2) throw(RuntimeError("Wrong number of arguments for >"));
    for (size_t i = 0; i + 1 < args.size(); ++i) {
        if (compareNumericValues(args[i], args[i+1]) != 1) return BooleanV(false);
    }
    return BooleanV(true);
}

Value Cons::evalRator(const Value &rand1, const Value &rand2) { // cons
    //TODO: To complete the cons logic
    return PairV(rand1, rand2);
}

Value ListFunc::evalRator(const std::vector<Value> &args) { // list function
    //TODO: To complete the list logic
    Value res = NullV();
    for (int i = (int)args.size() - 1; i >= 0; --i) res = PairV(args[i], res);
    return res;
}

Value IsList::evalRator(const Value &rand) { // list?
    //TODO: To complete the list? logic
    Value temp=rand;
    while(temp->v_type==V_PAIR){
        temp=dynamic_cast<Pair*>(temp.get())->cdr;
    }
    return BooleanV(temp->v_type == V_NULL);
}

Value Car::evalRator(const Value &rand) { // car
    //TODO: To complete the car logic
    if(rand->v_type != V_PAIR){
        throw(RuntimeError("car applied to non-pair"));
    }
    Pair* pair_ptr = dynamic_cast<Pair*>(rand.get());
    return pair_ptr->car;
}

Value Cdr::evalRator(const Value &rand) { // cdr
    //TODO: To complete the cdr logic
    if(rand->v_type != V_PAIR){
        throw(RuntimeError("cdr applied to non-pair"));
    }
    Pair* pair_ptr = dynamic_cast<Pair*>(rand.get());
    return pair_ptr->cdr;
}

Value SetCar::evalRator(const Value &rand1, const Value &rand2) { // set-car!
    //TODO: To complete the set-car! logic
    if (rand1->v_type != V_PAIR) throw(RuntimeError("set-car! applied to non-pair"));
    Pair *p = dynamic_cast<Pair*>(rand1.get());
    p->car = rand2;
    return VoidV();
}

Value SetCdr::evalRator(const Value &rand1, const Value &rand2) { // set-cdr!
   //TODO: To complete the set-cdr! logic
   if (rand1->v_type != V_PAIR) throw(RuntimeError("set-cdr! applied to non-pair"));
    Pair *p = dynamic_cast<Pair*>(rand1.get());
    p->cdr = rand2;
    return VoidV();
}

Value IsEq::evalRator(const Value &rand1, const Value &rand2) { // eq?
    // 检查类型是否为 Integer
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return BooleanV((dynamic_cast<Integer*>(rand1.get())->n) == (dynamic_cast<Integer*>(rand2.get())->n));
    }
    // 检查类型是否为 Boolean
    else if (rand1->v_type == V_BOOL && rand2->v_type == V_BOOL) {
        return BooleanV((dynamic_cast<Boolean*>(rand1.get())->b) == (dynamic_cast<Boolean*>(rand2.get())->b));
    }
    // 检查类型是否为 Symbol
    else if (rand1->v_type == V_SYM && rand2->v_type == V_SYM) {
        return BooleanV((dynamic_cast<Symbol*>(rand1.get())->s) == (dynamic_cast<Symbol*>(rand2.get())->s));
    }
    // 检查类型是否为 Null 或 Void
    else if ((rand1->v_type == V_NULL && rand2->v_type == V_NULL) ||
             (rand1->v_type == V_VOID && rand2->v_type == V_VOID)) {
        return BooleanV(true);
    } else {
        return BooleanV(rand1.get() == rand2.get());
    }
}

Value IsBoolean::evalRator(const Value &rand) { // boolean?
    return BooleanV(rand->v_type == V_BOOL);
}

Value IsFixnum::evalRator(const Value &rand) { // number?
    return BooleanV(rand->v_type == V_INT);
}

Value IsNull::evalRator(const Value &rand) { // null?
    return BooleanV(rand->v_type == V_NULL);
}

Value IsPair::evalRator(const Value &rand) { // pair?
    return BooleanV(rand->v_type == V_PAIR);
}

Value IsProcedure::evalRator(const Value &rand) { // procedure?
    return BooleanV(rand->v_type == V_PROC);
}

Value IsSymbol::evalRator(const Value &rand) { // symbol?
    return BooleanV(rand->v_type == V_SYM);
}

Value IsString::evalRator(const Value &rand) { // string?
    return BooleanV(rand->v_type == V_STRING);
}

Value Begin::eval(Assoc &e) {
    //TODO: To complete the begin logic
    Value result = VoidV();
    for (auto &expr : this->es) {
        result = expr->eval(e);
    }
    return result;
}

Value Quote::eval(Assoc& e) {
    //TODO: To complete the quote logic
    Quote *q_ptr = dynamic_cast<Quote*>(this);
    if (!q_ptr) throw RuntimeError("Internal error: Quote::eval on non-Quote object");
    return syntaxToValue(q_ptr->s);
}

Value AndVar::eval(Assoc &e) { // and with short-circuit evaluation
    //TODO: To complete the and logic
    if (rands.empty()) return BooleanV(true);
    Value last=VoidV();
    for (auto &rand : rands) {
        last = rand->eval(e);
        if (last->v_type == V_BOOL && !dynamic_cast<Boolean*>(last.get())->b) {
            return BooleanV(false);
        }
    }
    return last;
}

Value OrVar::eval(Assoc &e) { // or with short-circuit evaluation
    //TODO: To complete the or logic
    if (rands.empty()) return BooleanV(false);
    for (auto &rand : rands) {
        Value val = rand->eval(e);
        if (!(val->v_type == V_BOOL && !dynamic_cast<Boolean*>(val.get())->b)) {
            return val;
        }
    }
    return BooleanV(false);
}

Value Not::evalRator(const Value &rand) { // not
    //TODO: To complete the not logic
    if (rand->v_type != V_BOOL) return BooleanV(false);
    Boolean *b = dynamic_cast<Boolean*>(rand.get());
    return BooleanV(!b->b);
}

Value If::eval(Assoc &e) {
    //TODO: To complete the if logic
    Value cond_val = cond->eval(e);
    bool cond_true = !(cond_val->v_type == V_BOOL && !dynamic_cast<Boolean*>(cond_val.get())->b);
    if (cond_true)
        return conseq->eval(e);
    else
        return alter->eval(e);
}

Value Cond::eval(Assoc &env) {
    //TODO: To complete the cond logic
    for(auto &clause:clauses){
        if(clause.empty())continue;
        bool isElse=false;
        if(auto varx=dynamic_cast<Var*>(clause[0].get())){
            if(varx->x=="else"){
                isElse=true;
            }
        }
        Value testVal=isElse?BooleanV(true):clause[0]->eval(env);
        bool condTrue=true;
        if(testVal->v_type==V_BOOL){
            condTrue=dynamic_cast<Boolean*>(testVal.get())->b;
        }
        if(condTrue){
            Value result=VoidV();
            for(int i=1;i<clause.size();i++) {
                result=clause[i]->eval(env);
            }
            return result;
        } 
    }
    return VoidV();
}

Value Lambda::eval(Assoc &env) { 
    //TODO: To complete the lambda logic
    return ProcedureV(x, e, env);
}

Value Apply::eval(Assoc &e) {
    if (rator->eval(e)->v_type != V_PROC) {throw RuntimeError("Attempt to apply a non-procedure");}

    //TODO: TO COMPLETE THE CLOSURE LOGIC
    Value procVal = rator->eval(e);
    Procedure* clos_ptr = dynamic_cast<Procedure*>(procVal.get());
    
    //TODO: TO COMPLETE THE ARGUMENT PARSER LOGIC
    std::vector<Value> args;
    for (auto &arg_expr : this->rand) {
        args.push_back(arg_expr->eval(e));
    }
    if (auto varNode = dynamic_cast<Variadic*>(clos_ptr->e.get())) {
        //TODO
        return varNode->evalRator(args);
    }
    if (args.size() != clos_ptr->parameters.size()) throw RuntimeError("Wrong number of arguments");
    
    //TODO: TO COMPLETE THE PARAMETERS' ENVIRONMENT LOGIC
    Assoc param_env = clos_ptr->env;
    for (int i = args.size() - 1; i >= 0; --i) {
        param_env = extend(clos_ptr->parameters[i], args[i], param_env);
    }
    return clos_ptr->e->eval(param_env);
}

Value Define::eval(Assoc &env) {
    //TODO: To complete the define logic
    Value val = e->eval(env);
    modify(var, val, env);
    return VoidV();
}

Value Let::eval(Assoc &env) {
    //TODO: To complete the let logic
    Assoc new_env = env;
    std::vector<Value> values;
    for (auto &b : bind) {
        values.push_back(b.second->eval(env));
    }
    for (size_t i = 0; i < bind.size(); ++i) {
        new_env = extend(bind[i].first, values[i], new_env);
    }
    return body->eval(new_env);
}

Value Letrec::eval(Assoc &env) {
    //TODO: To complete the letrec logic
    Letrec *lr = dynamic_cast<Letrec*>(this);
    // create new env with placeholders so recursive refs work
    Assoc new_env = env;
    for (int i = (int)lr->bind.size() - 1; i >= 0; --i) {
        new_env = extend(lr->bind[i].first, VoidV(), new_env);
    }
    // evaluate each binding in new_env and update
    for (size_t i = 0; i < lr->bind.size(); ++i) {
        Value v = lr->bind[i].second->eval(new_env);
        modify(lr->bind[i].first, v, new_env);
    }
    return lr->body->eval(new_env);
}

Value Set::eval(Assoc &env) {
    //TODO: To complete the set logic
    Set *s = dynamic_cast<Set*>(this);
    // ensure variable exists
    Value existing = find(s->var, env);
    if (existing.get() == nullptr) throw RuntimeError("Unbound variable: " + s->var);
    Value v = s->e->eval(env);
    modify(s->var, v, env);
    return VoidV();
}

Value Display::evalRator(const Value &rand) { // display function
    if (rand->v_type == V_STRING) {
        String* str_ptr = dynamic_cast<String*>(rand.get());
        std::cout << str_ptr->s;
    } else {
        rand->show(std::cout);
    }
    
    return VoidV();
}
