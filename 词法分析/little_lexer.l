%{
#include <stdio.h>
#include <stdlib.h>

int lines = 1;
int words = 0;
int chars = 0;
%}

DELIM [\t " "]
WS {DELIM}+
NEWLINE [\n]+
DIGIT [0-9]
LETTER [a-zA-Z]
OBJECTED [a-z]({LETTER}|_|DIGIT)*
OPT ("+"|"-"|"*"|"/"|"^"|"&"|"|"|"~"|":="|">"|">="|"=="|"!="|"<="|"<"|"&&"|"||"|"!!=")
BRACKET (";"|"("|")"|"{"|"}")
PLAHOLD ("%f"|"%s"|"%lld") 
KEYWORD (fprintf)|(while)|(aafor)|(if)|(else)|(continue)|(break)|(return)
INT {DIGIT}+
FLOAT {DIGIT}+"."{DIGIT}+
TYPEID (Int)|(Float)|(String)|(Bool)|(Void)
ANNOT #.*
FUNC func" "{OBJECTED}

%%
{NEWLINE} {lines++; chars++;}
{WS} {/*no action and no return*/}
{ANNOT} {}
{KEYWORD} {printf("#%d KEYWORD %s\n", lines, yytext);}
{TYPEID} {printf("#%d TYPEID %s\n", lines, yytext);}
{FUNC} {printf("#%d func %s\n", lines, yytext);}
{OBJECTED} {printf("#%d OBJECTED %s\n", lines, yytext);}
{FLOAT} {printf("#%d CONST %.1f\n", lines, atof(yytext));}
{INT} {printf("#%d CONST %d\n", lines, atoi(yytext));}
{OPT} {printf("#%d %s\n", lines, yytext);}
{BRACKET} {printf("#%d %s\n", lines, yytext);}
%%

int main(){
    yylex();
    fprintf(stderr,"lines:%d,words:%d,chars:%d\n", lines, words, chars);
    return 0;
}
