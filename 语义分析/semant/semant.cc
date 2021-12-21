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
static bool has_return = 0;
static int in_loop = 0;

typedef SymbolTable<Symbol, Symbol> ObjectEnvironment; // name, type
ObjectEnvironment objectEnv;

// Maps Defination:
typedef std::map<Symbol, CallDecl> CallTable;
//typedef std::map<Symbol, Symbol> GloabalVars;
//typedef std::map<Symbol, Symbol> LocalVars;
//typedef std::map<Symbol, bool> InstallTable;
//typedef std::map<Symbol, Symbol> ParaVars;
//typedef std::vector<Symbol> FuncPara;
//typedef std::map<Symbol, FuncPara> FuncParaTable;

// Maps instantiation:
CallTable callTable;
//GloabalVars globalVars;
//LocalVars localVars;
//InstallTable installTable;
//ParaVars paraVars;
//FuncParaTable funcParaTable;

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
                // installTable[name] = false;
                // tmp_decl->checkPara();
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
            semant_error(callTable[main]) << "Main function should have return type Void." << endl;
        }
    }
}

void VariableDecl_class::check() {
    Symbol name = this->getName();
    Symbol type = this->getType();
    if (!isValidTypeName(type)) {
        semant_error(this) << "variable " << name << " cannot be of type Void. Void can just be used as return type." << endl;
    }
    else if (localVars[name] != NULL) {
        semant_error(this) <<"variable" << name << " was previously defined." << endl;
    }
    localVars[name] = type;
    objectEnv.addid(name, new Symbol(type));
}

void CallDecl_class::check() {
    objectEnv.enterscope();

    Variables paras = this->getVariables();
    StmtBlock body = this->getBody();

    if (paras->len() > 6) {
    // func has more than 6 parameters
    semant_error(this) << "Function " << name << " has more than 6 parameters." << endl;
    }

    for (int i=paras->first(); paras->more(i); paras->next(i)) {
        Variable tmp_para = paras->nth(i);
        Symbol paraName = tmp_para->getName();
        Symbol paraType = tmp_para->getType();

        if(!isValidTypeName(paraType)) {
            // morphological parameters type can't be Void
            semant_error(this) << "Function " << this->getName() << " 's parameter has an invalid type Void." <<endl;
        }
        else if (objectEnv.probe(paraName)) {
            semant_error(this) << "Function " << this->getName() << " 's parameter has a duplicate name. " << paraName << endl;
        }
        else {
            objectEnv.addid(paraName, new Symbol(this->getType()));
        }
    }
    // not sure here
    body->check(getType());

    objectEnv.exitscope();
    if (!has_return) {
        semant_error(this) << "Function " << this->getName() << " must have an overall return statement." << endl;
    }
    
    objectEnv.exitscope();
}

void StmtBlock_class::check(Symbol type) {
    objectEnv.enterscope();
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
    objectEnv.exitscope();
}

void IfStmt_class::check(Symbol type) {
    Expr condition = this->getCondition();
    Symbol condType = condition->checkType();

    if (condType != Bool) {
        semant_error(this) << "Condition must be a Bool, got " << condType << endl;
    }

    StmtBlock thenExpr = this->getThen();
    StmtBlock elseExpr = this->getElse();

    thenExpr->check(type);
    elseExpr->check(type);
}

void WhileStmt_class::check(Symbol type) {
    in_loop++;
    Expr condition = this->getCondition();
    Symbol condType = condition->checkType();

    if (condType != Bool) {
        semant_error(this) << "Condition must be a Bool, got " << condType << endl;
    }

    StmtBlock body = this->getBody();
    body->check(type);
    in_loop--;
}

void ForStmt_class::check(Symbol type) {

}

void ReturnStmt_class::check(Symbol type) {

}

void ContinueStmt_class::check(Symbol type) {

}

void BreakStmt_class::check(Symbol type) {

}

Symbol Call_class::checkType(){

}

Symbol Actual_class::checkType(){

}

Symbol Assign_class::checkType(){

}

Symbol Add_class::checkType(){
 
}

Symbol Minus_class::checkType(){
 
}

Symbol Multi_class::checkType(){
 
}

Symbol Divide_class::checkType(){

}

Symbol Mod_class::checkType(){

}

Symbol Neg_class::checkType(){

}

Symbol Lt_class::checkType(){

}

Symbol Le_class::checkType(){

}

Symbol Equ_class::checkType(){

}

Symbol Neq_class::checkType(){

}

Symbol Ge_class::checkType(){

}

Symbol Gt_class::checkType(){

}

Symbol And_class::checkType(){

}

Symbol Or_class::checkType(){

}

Symbol Xor_class::checkType(){

}

Symbol Not_class::checkType(){

}

Symbol Bitand_class::checkType(){

}

Symbol Bitor_class::checkType(){

}

Symbol Bitnot_class::checkType(){

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



