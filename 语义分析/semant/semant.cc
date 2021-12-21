#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"

extern int semant_debug;
extern char *curr_filename;

static ostream& error_stream = cerr;
static int semant_errors = 0;

static Decl curr_decl = 0;
static bool has_return_bool = 0;
static int in_loop = 0;
static int has_return = 0;

typedef SymbolTable<Symbol, Symbol> ObjectEnvironment; // name, type
ObjectEnvironment objectEnv;

typedef std::map<Symbol, CallDecl> CallTable;
CallTable callTable;


///////////////////////////////////////////////
// helper func
///////////////////////////////////////////////


static ostream& semant_error() {
    semant_errors++;
    return error_stream;
}

static ostream& semant_error(tree_node *t) {
    error_stream << t->get_line_number() << ": ";
    return semant_error();
}

static ostream& internal_error(int lineno) {
    error_stream << "FATAL:" << lineno << ": ";
    return error_stream;
}

//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////

static Symbol 
    Int,
    Float,
    String,
    Bool,
    Void,
    Main,
    print
    ;

bool isValidCallName(Symbol type) {
    return type != (Symbol)print;
}

bool isValidTypeName(Symbol type) {
    return type != Void;
}

//
// Initializing the predefined symbols.
//

static void initialize_constants(void) {
    // 4 basic types and Void type
    Bool        = idtable.add_string("Bool");
    Int         = idtable.add_string("Int");
    String      = idtable.add_string("String");
    Float       = idtable.add_string("Float");
    Void        = idtable.add_string("Void");  
    // Main function
    Main        = idtable.add_string("main");

    // classical function to print things, so defined here for call.
    print        = idtable.add_string("printf");
}

/*
    TODO :
    you should fill the following function defines, so that semant() can realize a semantic 
    analysis in a recursive way. 
    Of course, you can add any other functions to help.
*/

static bool sameType(Symbol name1, Symbol name2) {
    return strcmp(name1->get_string(), name2->get_string()) == 0;
}

static void install_calls(Decls decls) {
    for (int i=decls->first(); decls->more(i); i=decls->next(i)){
        Decl tmp_decl = decls->nth(i);
        Symbol name = tmp_decl->getName();
        Symbol type = tmp_decl->getType();
        if (tmp_decl->isCallDecl()){
            CallDecl call = static_cast<CallDecl>(tmp_decl);
            if (callTable[name] != NULL) {
                // no repeat function declaration
                semant_error(tmp_decl) << "Function " << name << " has been previously defined." << endl;
            }
            else if (sameType(name, print)){
                semant_error(tmp_decl) << "Function printf cannot be redefination." << endl;
            }
            else if (!isValidCallName(name)) {
                // function printf can't be defined twice
                semant_error(tmp_decl) << "Function printf cannot have a name as printf." << endl;
            }
            else if (type != Bool && type != Int && type != String && type !=  Float && type != Void) {
                // return type must be int,void,string,float,bool
                semant_error(tmp_decl) << "Function returnType error." << endl;
            }
            else {
                // update tables
                callTable[name] = call;
            }
        }
    }
}

static void install_globalVars(Decls decls) {
    objectEnv.enterscope();
    for (int i=decls->first(); decls->more(i); i=decls->next(i)){
        Decl tmp_decl = decls->nth(i);
        Symbol name = tmp_decl->getName();
        Symbol type = tmp_decl->getType();
        if ( !tmp_decl->isCallDecl()) {
            VariableDecl variableDecl = static_cast<VariableDecl>(tmp_decl);
            if (objectEnv.lookup(name) != NULL){
                // global variable can't be named twice
                semant_error(tmp_decl) << "Global variable redefined." << endl;
            }
            else if (!isValidTypeName(type)) {
                // variable type can't be Void
                semant_error(tmp_decl) << "variable "<< name << " cannot be Void type. Void can just be used as return type." << endl;
            }
            else {
                objectEnv.addid(name, new Symbol(variableDecl->getType()));
            }
        }
    }
}

static void check_calls(Decls decls) {
    for (int i=decls->first(); decls->more(i); i=decls->next(i)) {
        Decl tmp_decl = decls->nth(i);
        if (tmp_decl->isCallDecl()) {
            tmp_decl->check();
        }
    }
}

static void check_main() {
    if (callTable.find(Main) == callTable.end()) {
        // has main or not
        semant_error() << "Main function is not defined." << endl;
    }
    else {
        curr_decl = callTable[Main];
        CallDecl main = static_cast<CallDecl>(curr_decl);
        if (main->getVariables()->len() != 0) {
            // main has no parameters
            semant_error(curr_decl) << "Main function should not have any parameters." << endl;
        }
        else if (main->getType() != Void) {
            // main return Void
            semant_error(curr_decl) << "Main function should have return type Void." << endl;
        }
    }
}

void VariableDecl_class::check() {
    Symbol name = this->getName();
    Symbol type = this->getType();
    if (objectEnv.probe(name)) {
        semant_error(this) <<"variable" << name << " was previously defined." << endl;
    }
    else if (!isValidTypeName(type)) {
        semant_error(this) << "variable " << name << " cannot be of type Void. Void can just be used as return type." << endl;
    }
    else {
        objectEnv.addid(name, new Symbol(type));
    }
}

void CallDecl_class::check() {
    objectEnv.enterscope();
    has_return_bool = 0;

    StmtBlock body = this->getBody();

    if (this->paras->len() > 6) {
    // func has more than 6 parameters
    semant_error(this) << "Function " << this->getName() << " has more than 6 parameters." << endl;
    }

    for (int i=paras->first(); paras->more(i); i=paras->next(i)) {
        Variable tmp_para = paras->nth(i);
        Symbol paraName = tmp_para->getName();
        Symbol paraType = tmp_para->getType();

        if(!isValidTypeName(paraType)) {
            // morphological parameters type can't be Void
            semant_error(this) << "Function " << this->getName() << " 's parameter has an invalid type Void." <<endl;
        }
        else if (objectEnv.probe(paraName)) {
            semant_error(this) << "Function " << this->getName() << " 's parameter has a duplicate name " << paraName << "." << endl;
        }
        else {
            objectEnv.addid(paraName, new Symbol(paraType));
        }
    }
    // not sure here
    body->check(getType());

    objectEnv.exitscope();
    if (!has_return_bool) {
        semant_error(this) << "Function " << this->getName() << " must have an overall return statement." << endl;
    }
}

void StmtBlock_class::check(Symbol type) {
    objectEnv.enterscope();
    has_return++;
    VariableDecls localVarDecls = this->getVariableDecls();
    for (int i=localVarDecls->first(); localVarDecls->more(i); i=localVarDecls->next(i)) {
        VariableDecl localVarDecl = localVarDecls->nth(i);
        localVarDecl->check();
    }

    Stmts localStmts = this->getStmts();
    for (int i=localStmts->first(); localStmts->more(i); i=localStmts->next(i)) {
        Stmt localStmt = localStmts->nth(i);
        localStmt->check(type);
    }
    has_return--;
    objectEnv.exitscope();
}

void IfStmt_class::check(Symbol type) {
    has_return++;
    Expr condition = this->getCondition();
    Symbol condType = condition->checkType();

    if (condType != Bool) {
        semant_error(this) << "Condition must be a Bool, got " << condType << '.' <<endl;
    }

    StmtBlock thenExpr = this->getThen();
    StmtBlock elseExpr = this->getElse();

    thenExpr->check(type);
    elseExpr->check(type);
    has_return--;
}

void WhileStmt_class::check(Symbol type) {
    has_return++;
    in_loop++;
    Expr condition = this->getCondition();
    Symbol condType = condition->checkType();

    if (condType != Bool) {
        semant_error(this) << "Condition must be a Bool, got " << condType << '.' <<endl;
    }

    StmtBlock body = this->getBody();
    body->check(type);
    in_loop--;
    has_return--;
}

void ForStmt_class::check(Symbol type) {
    has_return++;
    in_loop++;
    Expr init = this->getInit();
    Expr loop = this->getLoop();
    Expr condition = this->getCondition();

    init->checkType();
    loop->checkType();
    Symbol condType = condition->checkType();

    if(condType != Bool && !condition->is_empty_Expr()) {
        semant_error(this) << "Condition must be a Bool, got " << condType << '.' << endl;
    }

    StmtBlock body = this->getBody();
    body->check(type);
    in_loop--;
    has_return--;
}

void ReturnStmt_class::check(Symbol type) {
    if (has_return == 1){
        has_return_bool = 1;
    }

    Expr value = this->getValue();
    Symbol thisType = value->checkType();

    if (thisType != type) {
        semant_error(this) << "Returns " << thisType << " , but need " << type << '.' <<endl;
    }
}

void ContinueStmt_class::check(Symbol type) {
    if (in_loop == 0) {
        semant_error(this) << "continue must be used in a loop sentence." << endl;
    }
}

void BreakStmt_class::check(Symbol type) {
    if (in_loop == 0) {
        semant_error(this) << "break must be used in a loop sentence." << endl;
    }
}

Symbol Call_class::checkType(){
    Symbol callName = this->getName();
    Actuals actuals = this->getActuals();
    Symbol result;

    if (!isValidCallName(callName)) {
        if (actuals->len()) {
            if (sameType(actuals->nth(actuals->first())->checkType(), String)) {
                for (int i=actuals->next(actuals->first()); actuals->more(i); i=actuals->next(i)) {
                    Symbol actualType = actuals->nth(i)->checkType();
                }
                setType(Void);
                result = Void;
            }
            else {
                semant_error(this) << "printf()'s first parameter must be of type String." << endl;
                result = Void;
            }
        }
        else {
            semant_error(this) << "printf() must has at last one parameter of type String." << endl;
        }
    }
    else {
        if (callTable.find(callName) == callTable.end()) {
            semant_error(this) << "Function " << callName << " has not been defined." << endl;
            setType(Void);
            result = Void;
        }
        else {
            CallDecl call = callTable[callName];
            Variables formals = call->getVariables();
            bool typeWrong = 0;
            int k = actuals->first();
            for (int i=formals->first(); formals->more(i); i=formals->next(i)) {
                if (!actuals->more(k)) {
                    semant_error(this) << "Function " << callName << " called with wrong number of arguments." << endl;
                    break;
                }
                Symbol actualType = actuals->nth(k)->checkType();
                Symbol formalType = formals->nth(i)->getType();
                if (actualType != formalType) {
                    semant_error(this) << "Function " << callName << ", the " << k+1 << " parameter should be " << formalType << " but provided a " << actualType << '.' <<endl;
                    typeWrong = 1;
                    break;
                }
                k = actuals->next(k);
            }
            if (!typeWrong && actuals->more(k)) {
                semant_error(this) << "Function " << callName << " called with wrong number of arguments." << endl;
            }
            Symbol callType = call->getType();
            setType(callType);
            result = callType;
        }
    }
    return result;
}

Symbol Actual_class::checkType(){
    Symbol type = this->expr->checkType();
    setType(type);
    return type;
}

Symbol Assign_class::checkType(){
    Symbol expectType = *objectEnv.lookup(this->lvalue);
    Symbol result;
    if (expectType) {
        Symbol actualType = this->value->checkType();
        if (sameType(actualType, expectType)) {
            setType(expectType);
        }
        else if (sameType(expectType, Float) && sameType(actualType,Int)) {
            setType(Float);
        }
        else {
            semant_error(this) << "Right value must have type " << expectType << " , got " << actualType << '.' <<endl;
        }
        result = this->type;
    }
    else {
        semant_error(this) << "Left value " << this->lvalue << " has not been defined." << endl;
        result = Void;
    }
    return result;
}

Symbol Add_class::checkType(){
    Symbol leftType = this->e1->checkType();
    Symbol rightType = this->e2->checkType();

    if (sameType(leftType, Int) && sameType(rightType, Int)) {
        setType(Int);
    }
    else if (sameType(leftType, Float) && sameType(rightType, Float) || sameType(leftType, Float) && sameType(rightType, Int) || sameType(leftType, Int) && sameType(rightType, Float)) {
        setType(Float);
    }
    else {
        semant_error(this) << "Cannot add a " << leftType << " and a " << rightType << '.' << endl;
        setType(Void);
    }
    return this->type;
}

Symbol Minus_class::checkType(){
    Symbol leftType = this->e1->checkType();
    Symbol rightType = this->e2->checkType();

    if (sameType(leftType, Int) && sameType(rightType, Int)) {
        setType(Int);
    }
    else if (sameType(leftType, Float) && sameType(rightType, Float) || sameType(leftType, Float) && sameType(rightType, Int) || sameType(leftType, Int) && sameType(rightType, Float)) {
        setType(Float);
    }
    else {
        semant_error(this) << "Cannot minus a " << leftType << " by a " << rightType << '.' <<endl;
        setType(Void);
    }
    return this->type;
}

Symbol Multi_class::checkType(){
    Symbol leftType = this->e1->checkType();
    Symbol rightType = this->e2->checkType();

    if (sameType(leftType, Int) && sameType(rightType, Int)) {
        setType(Int);
    }
    else if (sameType(leftType, Float) && sameType(rightType, Float) || sameType(leftType, Float) && sameType(rightType, Int) || sameType(leftType, Int) && sameType(rightType, Float)) {
        setType(Float);
    }
    else {
        semant_error(this) << "Cannot multiply a " << leftType << " with a " << rightType << '.' <<endl;
        setType(Void);
    }
    return this->type;
}

Symbol Divide_class::checkType(){
    Symbol leftType = this->e1->checkType();
    Symbol rightType = this->e2->checkType();

    if (sameType(leftType, Int) && sameType(rightType, Int)) {
        setType(Int);
    }
    else if (sameType(leftType, Float) && sameType(rightType, Float) || sameType(leftType, Float) && sameType(rightType, Int) || sameType(leftType, Int) && sameType(rightType, Float)) {
        setType(Float);
    }
    else {
        semant_error(this) << "Cannot divide a " << leftType << " by a " << rightType << '.' <<endl;
        setType(Void);
    }
    return this->type;
}

Symbol Mod_class::checkType(){
    Symbol leftType = this->e1->checkType();
    Symbol rightType = this->e2->checkType();

    if (sameType(leftType, Int) && sameType(rightType, Int)) {
        setType(Int);
    }
    else {
        semant_error(this) << "Cannot mod a " << leftType << " and a " << rightType << '.' <<endl;
        setType(Void);
    }
    return this->type;
}

Symbol Neg_class::checkType(){
    Symbol leftType = this->e1->checkType();

    if (sameType(leftType, Int) || sameType(leftType, Float)) {
        setType(leftType);
    }
    else {
        semant_error(this) << "A " << leftType << " doesn't have a negative." << endl;
        setType(Void);
    }
    return this->type;
}

Symbol Lt_class::checkType(){
    Symbol leftType = this->e1->checkType();
    Symbol rightType = this->e2->checkType();

    if ((sameType(leftType, Int) || sameType(leftType, Float)) && (sameType(rightType, Int) || sameType(rightType, Float))) {
        setType(Bool);
    }
    else {
        semant_error(this) << "Cannot compare a " << leftType << " and a " << rightType << "(less)." << endl;
        setType(Void);
    }
    return this->type;
}

Symbol Le_class::checkType(){
    Symbol leftType = this->e1->checkType();
    Symbol rightType = this->e2->checkType();

    if ((sameType(leftType, Int) || sameType(leftType, Float)) && (sameType(rightType, Int) || sameType(rightType, Float))) {
        setType(Bool);
    }
    else {
        semant_error(this) << "Cannot compare a " << leftType << " and a " << rightType << "(less than or equal)." << endl;
        setType(Void);
    }
    return this->type;
}

Symbol Equ_class::checkType(){
    Symbol leftType = this->e1->checkType();
    Symbol rightType = this->e2->checkType();

    if ((sameType(leftType, Int) || sameType(leftType, Float)) && (sameType(rightType, Int) || sameType(rightType, Float)) || (sameType(leftType, Bool) && sameType(rightType, Bool))) {
        setType(Bool);
    }
    else {
        semant_error(this) << "Cannot compare a " << leftType << " and a " << rightType << "(equal)." << endl;
        setType(Void);
    }
    return this->type;
}

Symbol Neq_class::checkType(){
    Symbol leftType = this->e1->checkType();
    Symbol rightType = this->e2->checkType();

    if ((sameType(leftType, Int) || sameType(leftType, Float)) && (sameType(rightType, Int) || sameType(rightType, Float)) || (sameType(leftType, Bool) && sameType(rightType, Bool))) {
        setType(Bool);
    }
    else {
        semant_error(this) << "Cannot compare a " << leftType << " and a " << rightType << "(not equal)." << endl;
        setType(Void);
    }
    return this->type;
}

Symbol Ge_class::checkType(){
    Symbol leftType = this->e1->checkType();
    Symbol rightType = this->e2->checkType();

    if ((sameType(leftType, Int) || sameType(leftType, Float)) && (sameType(rightType, Int) || sameType(rightType, Float))) {
        setType(Bool);
    }
    else {
        semant_error(this) << "Cannot compare a " << leftType << " and a " << rightType << "(greater than or equal)." << endl;
        setType(Void);
    }
    return this->type;
}

Symbol Gt_class::checkType(){
    Symbol leftType = this->e1->checkType();
    Symbol rightType = this->e2->checkType();

    if ((sameType(leftType, Int) || sameType(leftType, Float)) && (sameType(rightType, Int) || sameType(rightType, Float))) {
        setType(Bool);
    }
    else {
        semant_error(this) << "Cannot compare a " << leftType << " and a " << rightType << "(greater)." << endl;
        setType(Void);
    }
    return this->type;
}

Symbol And_class::checkType(){
    Symbol leftType = this->e1->checkType();
    Symbol rightType = this->e2->checkType();

    if (sameType(leftType, Bool) && sameType(rightType, Bool)) {
        setType(Bool);
    }
    else {
        semant_error(this) << "Cannot use and(&&) between " << leftType << " and " << rightType << '.' <<endl;
        setType(Void);
    }
    return this->type;
}

Symbol Or_class::checkType(){
    Symbol leftType = this->e1->checkType();
    Symbol rightType = this->e2->checkType();

    if (sameType(leftType, Bool) && sameType(rightType, Bool)) {
        setType(Bool);
    }
    else {
        semant_error(this) << "Cannot use or(||) between " << leftType << " and " << rightType << '.' <<endl;
        setType(Void);
    }
    return this->type;
}

Symbol Xor_class::checkType(){
    Symbol leftType = this->e1->checkType();
    Symbol rightType = this->e2->checkType();

    if (sameType(leftType, Bool) && sameType(rightType, Bool)) {
        setType(Bool);
    }
    else {
        semant_error(this) << "Cannot use xor(^) between " << leftType << " and " << rightType << '.' <<endl;
        setType(Void);
    }
    return this->type;
}

Symbol Not_class::checkType(){
    Symbol leftType = this->e1->checkType();

    if (sameType(leftType, Bool)) {
        setType(Bool);
    }
    else {
        semant_error(this) << "Cannot use not(!) upon " << leftType << '.' <<endl;
        setType(Void);
    }
    return this->type;
}

Symbol Bitand_class::checkType(){
    Symbol leftType = this->e1->checkType();
    Symbol rightType = this->e2->checkType();

    if (sameType(leftType, Int) && sameType(rightType, Int)) {
        setType(Int);
    }
    else {
        semant_error(this) << "Cannot use bit-and(&) between " << leftType << " and " << rightType << '.' <<endl;
        setType(Void);
    }
    return this->type;
}

Symbol Bitor_class::checkType(){
    Symbol leftType = this->e1->checkType();
    Symbol rightType = this->e2->checkType();

    if (sameType(leftType, Int) && sameType(rightType, Int)) {
        setType(Int);
    }
    else {
        semant_error(this) << "Cannot use bit-or(|) between " << leftType << " and " << rightType << '.' <<endl;
        setType(Void);
    }
    return this->type;
}

Symbol Bitnot_class::checkType(){
    Symbol leftType = this->e1->checkType();

    if (sameType(leftType, Int)) {
        setType(Int);
    }
    else {
        semant_error(this) << "Cannot use unary not(~) upon " << leftType << '.' <<endl;
        setType(Void);
    }
    return this->type;
}

Symbol Const_int_class::checkType(){
    setType(Int);
    return type;
}

Symbol Const_string_class::checkType(){
    setType(String);
    return type;
}

Symbol Const_float_class::checkType(){
    setType(Float);
    return type;
}

Symbol Const_bool_class::checkType(){
    setType(Bool);
    return type;
}

Symbol Object_class::checkType(){
    Symbol expectType = *objectEnv.lookup(this->var);
    if (expectType) {
        setType(expectType);
    }
    else {
        semant_error(this) << "object " << this->var << " has not been defined." << endl;
        setType(Void);
    }
    return this->type;
}

Symbol No_expr_class::checkType(){
    setType(Void);
    return getType();
}

void Program_class::semant() {
    initialize_constants();
    install_calls(decls);
    check_main();
    install_globalVars(decls);
    check_calls(decls);
    
    if (semant_errors > 0) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }
}



