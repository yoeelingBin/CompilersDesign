/*
*  seal.y
*              Parser definition for the SEAL language.
*
*/
%{
  #include <iostream>
  #include "seal-decl.h"
  #include "seal-stmt.h"
  #include "seal-expr.h"
  #include "stringtab.h"
  #include "utilities.h"

  extern char *curr_filename;
  /* Locations */
  #define YYLTYPE int              /* the type of locations */
  #define seal_yylloc curr_lineno  /* use the curr_lineno from the lexer
  for the location of tokens */
    
    extern int node_lineno;          /* set before constructing a tree node
    to whatever you want the line number
    for the tree node to be */
      
      
      #define YYLLOC_DEFAULT(Current, Rhs, N)         \
      Current = Rhs[1];                             \
      node_lineno = Current;
    
    
    #define SET_NODELOC(Current)  \
    node_lineno = Current;
    
    /* IMPORTANT NOTE ON LINE NUMBERS
    *********************************
    * The above definitions and macros cause every terminal in your grammar to 
    * have the line number supplied by the lexer. The only task you have to
    * implement for line numbers to work correctly, is to use SET_NODELOC()
    * before constructing any constructs from non-terminals in your grammar.
    * Example: Consider you are matching on the following very restrictive 
    * (fictional) construct that matches a plus between two integer constants. 
    * (SUCH A RULE SHOULD NOT BE PART OF YOUR PARSER):
    
    add_consts	: INT_CONST '+' INT_CONST 
    
    * where INT_CONST is a terminal for an integer constant. Now, a correct
    * action for this rule that attaches the correct line number to plus_const
    * would look like the following:
    
    add_consts	: INT_CONST '+' INT_CONST 
    {
      // Set the line number of the current non-terminal:
      // ***********************************************
      // You can access the line numbers of the i'th item with @i, just
      // like you acess the value of the i'th exporession with $i.
      //
      // Here, we choose the line number of the last INT_CONST (@3) as the
      // line number of the resulting expression (@$). You are free to pick
      // any reasonable line as the line number of non-terminals. If you 
      // omit the statement @$=..., bison has default rules for deciding which 
      // line number to use. Check the manual for details if you are interested.
      @$ = @3;
      
      
      // Observe that we call SET_NODELOC(@3); this will set the global variable
      // node_lineno to @3. Since the constructor call "plus" uses the value of 
      // this global, the plus node will now have the correct line number.
      SET_NODELOC(@3);
      
      // construct the result node:
      $$ = add(int_const($1), int_const($3));
    }
    
    */
    
    
    
    void yyerror(char *s);        /*  defined below; called for each parse error */
    extern int yylex();           /*  the entry point to the lexer  */
    
    /************************************************************************/
    /*                DONT CHANGE ANYTHING IN THIS SECTION                  */
    
    Program ast_root;	      /* the result of the parse  */
    //Decls parse_results;        /* for use in semantic analysis */
    int omerrs = 0;               /* number of errors in lexing and parsing */
    %}
    
    /* A union of all the types that can be the result of parsing actions. */
    %union {
      Boolean boolean;
      Symbol symbol;
      Program program;
      Decl decl;
      Decls decls;
      VariableDecl variableDecl;
      VariableDecls variableDecls;
      Variable variable;
      Variables variables;
      CallDecl callDecl;
      StmtBlock stmtBlock;
      Stmt stmt;
      Stmts stmts;
      IfStmt ifStmt;
      WhileStmt whileStmt;
      ForStmt forStmt;
      ReturnStmt returnStmt;
      ContinueStmt continueStmt;
      BreakStmt breakStmt;
      Expr expr;
      Exprs exprs;
      Call call;
      Actual actual;
      Actuals actuals;
      
      char *error_msg;
    }
    
    /* 
    Declare the terminals; a few have types for associated lexemes.
    The token ERROR is never used in the parser; thus, it is a parse
    error when the lexer returns it.
    
    The integer following token declaration is the numeric constant used
    to represent that token internally.  Typically, Bison generates these
    on its own, but we give explicit numbers to prevent version parity
    problems (bison 1.25 and earlier start at 258, later versions -- at
    257)
    */
    %token IF 258 ELSE 260 WHILE 261 FOR 262 BREAK 263 CONTINUE 264 
    %token FUNC 265 RETURN 266  
    %token VAR 271
	  %token AND 274 OR 275 EQUAL 276 NE 277 GE 278 LE 279
    %token <boolean> CONST_BOOL 267
    %token <symbol>  CONST_INT 268 CONST_STRING 269 CONST_FLOAT 270
    %token <symbol>  OBJECTID 284 TYPEID 285
    
	  %token UMINUS
    /*  DON'T CHANGE ANYTHING ABOVE THIS LINE, OR YOUR PARSER WONT WORK       */
    /**************************************************************************/
    
    /* Complete the nonterminal list below, giving a type for the semantic
    value of each non terminal. (See section 3.6 in the bison 
    documentation for details). */
    
    /* Declare types for the grammar's non-terminals. */
    /*非终结符的声明*/
    %type <program> program
    %type <decls> decl_list
    %type <decl> decl
    
    %type <variableDecl> variableDecl
    %type <variableDecls> variableDecl_list

    %type <variable> variable
    %type <variables> variable_list

    %type <call> call
    %type <callDecl> callDecl

    %type <stmt> stmt
    %type <stmts> stmt_list
    %type <stmtBlock> stmtBlock
    %type <ifStmt> ifStmt
    %type <whileStmt> whileStmt
    %type <forStmt> forStmt
    %type <breakStmt> breakStmt
    %type <continueStmt> continueStmt
    %type <returnStmt> returnStmt

    %type <expr> expr

    %type <actual> actual
    %type <actuals> actual_list

    /* Precedence declarations go here. */
    /*算符优先级声明*/
    %left '~' '&' '|' '^'
    %left '*' '/'
    %left '%'
    %left '+' '-'
    %nonassoc UMINUS '!'
	  %nonassoc '=' 
    %nonassoc EQUAL NE
    %nonassoc '<' LE GE '>'
    %right OR
    %right AND


%%

    /* Save the root of the abstract syntax tree in a global variable. */
	/* Add more rules here */
    /*Program->[Decl]+ */
    program		: decl_list {
        @$ = @1;
        ast_root = program($1); 
      }
      ;

    // add more syntax rules here
    /*Decl->VariableDecl|CallDecl*/
    decl  : variableDecl{
      $$ =  $1;
    }
    |  callDecl{
      $$ = $1;
    };
  
    /*decl_list*/
    decl_list   :decl {
      $$ = single_Decls($1);
    }
    |  decl_list decl {
      $$ = append_Decls($1, single_Decls($2));
    };
    
    /*variableDecl->var variable;*/
    variableDecl  : VAR variable ';'{
      $$ = variableDecl($2);
    };

    variableDecl_list  : variableDecl{
      $$ = single_VariableDecls($1);
    }
    |  variableDecl_list variableDecl {
      $$ = append_Variables($1, single_VariableDecls($2));
    };

    /*variable->TYPEID OBJECTID*/
    variable:  TYPEID OBJECTID {
      $$ = variable($1, $2);
    };

    /*variable_list*/
    variable_list:  {
      $$ = nil_Variables();
    }
    |  variable_list ',' variable {
      $$ = append_Variables($1, single_Variables($3));
    };

    /*CallDecl->TYPEID func object([Variable[[,Variable]]*]) StmtBlock*/
    callDecl:  TYPEID FUNC OBJECTID '(' variable_list ')' stmtBlock{
      $$ = callDecl($3, $5, $1, $7);
    };
    |  TYPEID FUNC OBJECTID '('  ')' stmtBlock{
      $$ = callDecl($3, nil_Variables(), $1, $6);
    };

    /*stmtBlock->{variableDecl* stmt*} */
    stmtBlock:  '{' variableDecl_list stmt_list '}' {
      $$ = stmtBlock($2, $3);
    }
    | '{' stmt_list '}' {
      $$ = stmtBlock(nil_VariableDecls(), $2);
    }
    | '{' variableDecl_list '}'{
      $$ = stmtBlock($2, nil_Stmts());
    }
    | '{' '}' {
      $$ = stmtBlock(nil_VariableDecls(), nil_Stmts());
    };

    /*stmt->;|Expr;|IfStmt|WhileStmt|ForStmt|BreakStmt|ContinueStmt|returnStmt|stmtBlock*/
    stmt: ';' {
      $$ = no_expr();
    }
    | expr ';' {
      $$ = $1;
    }
    | ifStmt {
      $$ = $1;
    }
    | whileStmt{
      $$ = $1;
    }
    | forStmt{
      $$ = $1;
    }
    | breakStmt{
      $$ = $1;
    }
    | continueStmt{
      $$ = $1;
    }
    | returnStmt{
      $$ = $1;
    }
    | stmtBlock{
      $$ = $1;
    };

    /*stmt_list*/
    stmt_list: {
      $$ = nil_Stmts();
    }
    | stmt_list stmt {
      $$ = append_Stmts($1, single_Stmts($2));
    };

    /*ifStmt->if Expr StmtBlock [else StmtBlock] */
    ifStmt: IF expr stmtBlock ELSE stmtBlock {
      $$ = ifstmt($2, $3, $5);
    }
    | IF expr stmtBlock{
      $$ = ifstmt($2, $3, stmtBlock(nil_VariableDecls(), nil_Stmts()));
    };

    /*WhileStmt->while Expr StmtBlock*/
    whileStmt: WHILE expr stmtBlock{
      $$ = whilestmt($2, $3);
    };

    /*ForStmt->aafor [Expr];[Expr];[Expr] StmtBlock*/
    forStmt: FOR expr ';' expr ';' expr stmtBlock{
      $$ = forstmt($2, $4, $6, $7);
    }
    | FOR expr ';' expr ';' stmtBlock{
      $$ = forstmt($2, $4, no_expr(), $6);
    }
    | FOR expr ';' ';' expr stmtBlock{
      $$ = forstmt($2, no_expr(), $5, $6);
    }
    | FOR ';' expr ';' expr stmtBlock{
      $$ = forstmt(no_expr(), $3, $5, $6);
    }
    | FOR expr ';' ';' stmtBlock{
      $$ = forstmt($2, no_expr(), no_expr(), $5);
    }
    | FOR ';' expr ';' stmtBlock{
      $$ = forstmt(no_expr(), $3, no_expr(), $5);
    }
    | FOR ';' ';' expr stmtBlock{
      $$ = forstmt(no_expr(), no_expr(), $4, $5);
    }
    | FOR ';' ';' stmtBlock{
      $$ = forstmt(no_expr(), no_expr(), no_expr(), $4);
    };

    /*ReturnStmt->return [Expr]; */
    returnStmt: RETURN expr ';' {
      $$ = returnstmt($2);
    }
    | RETURN ';' {
      $$ = returnstmt(no_expr());
    };

    /*ContinueStmt->continue; */
    continueStmt: CONTINUE ';' {
      $$ = continuestmt();
    };

    /*BreakStmt->break; */
    breakStmt: BREAK ';' {
      $$ = breakstmt();
    };

    /*expr   too much!*/
    expr: OBJECTID '=' expr {
      $$ = assign($1, $3);
    }
    | CONST_INT {
      $$ = const_int($1);
    }
    | CONST_BOOL {
      $$ = const_bool($1);
    }
    | CONST_STRING {
      $$ = const_string($1);
    }
    | CONST_FLOAT {
      $$ = const_float($1);
    }
    | call {
      $$ = $1;
    }
    | '(' expr ')' {
      $$ = $2;
    }
    | OBJECTID {
      $$ = object($1);
    }
    | expr '+' expr {
      $$ = add($1, $3);
    }
    | expr '-' expr {
      $$ = minus($1, $3);
    }
    | expr '*' expr {
      $$ = multi($1, $3);
    }
    | expr '/' expr {
      $$ = divide($1, $3);
    }
    | expr '%' expr {
      $$ = mod($1, $3);
    }
    | '-' expr %prec UMINUS {
      $$ = neg($2);
    }
    | expr '<' expr {
      $$ = lt($1, $3);
    }
    | expr LE expr {
      $$ = le($1, $3);
    }
    | expr EQUAL expr {
      $$ = equ($1, $3);
    }
    | expr NE expr {
      $$ = neq($1, $3);
    }
    | expr GE expr {
      $$ = ge($1, $3);
    }
    | expr '>' expr {
      $$ = gt($1, $3);
    }
    | expr AND expr {
      $$ = and_($1, $3);
    }
    | expr OR expr {
      $$ = or_($1, $3);
    }
    | expr '^' expr {
      $$ = xor_($1, $3);
    }
    | '!' expr {
      $$ = not_($2);
    }
    | '~' expr {
      $$ = bitnot($2);
    }
    | expr '&' expr {
      $$ = bitand_($1, $3);
    }
    | expr '|' expr {
      $$ = bitor_($1, $3);
    };

    /*Call->OBJECTID(Actuals) */
    call: OBJECTID '(' actual_list ')' {
      $$ = call($1, $3);
    }
    | OBJECTID '(' ')' {
      $$ = call($1, nil_Actuals());
    };

    /*actual->expr*/
    actual: expr {
      $$ = actual($1);
    };

    /*Actuals->[Expr[[,Expr]]* */
    actual_list: actual {
      $$ = single_Actuals($1);
    }
    | actual_list ',' actual {
      $$ = append_Actuals($1, single_Actuals($3));
    };

    /* end of grammar */
%%
    
    /* This function is called automatically when Bison detects a parse error. */
    void yyerror(char *s)
    {
      extern int curr_lineno;
      
      cerr << "\"" << curr_filename << "\", line " << curr_lineno << ": " \
      << s << " at or near ";
      print_seal_token(yychar);
      cerr << endl;
      omerrs++;
      
      if(omerrs>50) {fprintf(stdout, "More than 50 errors\n"); exit(1);}
    }
