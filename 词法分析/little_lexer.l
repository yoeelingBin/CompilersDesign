%{
#include <stdio.h>
#include <stdlib.h>

int lines = 1;
int words = 0;
int chars = 0;
%}

DELIM [\t\ ]
WS {DELIM}+
NEWLINE [\n]+
DIGIT [0-9]
LETTER [a-zA-Z]
FUNC func\ {OBJECTED}
OBJECTED [a-z]({LETTER}|_|{DIGIT})*
OPT ("+"|"-"|"*"|"/"|"^"|"&"|"|"|"~"|":="|">"|">="|"=="|"!="|"<="|"<"|"&&"|"||"|"!!=")
BRACKET (";"|"("|")"|"{"|"}")
PLAHOLD ("%f"|"%s"|"%lld") 
KEYWORD (fprintf)|(while)|(aafor)|(if)|(else)|(continue)|(break)|(return)
INT {DIGIT}+
FLOAT {DIGIT}+"."{DIGIT}+
TYPEID (Int)|(Float)|(String)|(Bool)|(Void)
COMMENT #.*
STD stderr|stdout
FILE ^#\ (({LETTER}|{DIGIT})+\.sealpp)


%%
{NEWLINE} {++lines; ++chars;}
{FILE} {printf("#name %s\n", yytext+2);}
{WS} {}
{COMMENT} {}
{KEYWORD} {printf("#%d KEYWORD %s\n", lines, yytext);}
{TYPEID} {printf("#%d TYPEID %s\n", lines, yytext);}
{OPT} {printf("#%d %s\n", lines, yytext);}
{BRACKET} {printf("#%d %s\n", lines, yytext);}
{PLAHOLD} {printf("#%d %s\n", lines, yytext);}
{STD} {}
{OBJECTED} {printf("#%d OBJECTED %s\n", lines, yytext);}
{FLOAT} {printf("#%d CONST %s\n", lines, yytext);}
{INT} {printf("#%d CONST %d\n", lines, atoi(yytext));}
{FUNC} {printf("#%d %s\n", lines, yytext);}
. {}
%%

int main(){
    yylex();
    fprintf(stderr,"lines:%d,words:%d,chars:%d\n", lines, words, chars);
    return 0;
}

int yywrap()
{
    return 1;
}
