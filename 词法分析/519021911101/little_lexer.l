%{
#include <stdio.h>
#include <stdlib.h>

int lines = 0;
int words = 0;
int chars = 0;

void count_chars(int yyleng);
void count_words();
void count_words_especially(char* yytext, int yyleng);
void count_lines(char* yytext, int yyleng);
int isContiWS(char x);
%}

DELIM [ \t\n\r]
WS {DELIM}+
DIGIT [0-9]
LETTER [a-zA-Z]
FUNC func\ {OBJECTED}
OBJECTED [a-z]({LETTER}|_|{DIGIT})*
OPT ("+"|"-"|"*"|"/"|"%"|"^"|"&"|"|"|"~"|":="|">"|">="|"=="|"!="|"<="|"<"|"&&"|"||"|"!!=")
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
{FILE} {printf("#name %s\n", yytext+2); count_chars(yyleng); count_words();}
{WS} {count_chars(yyleng); count_words(); count_lines(yytext, yyleng);}
{COMMENT} {count_chars(yyleng); count_words_especially(yytext, yyleng);}
{KEYWORD} {printf("#%d KEYWORD %s\n", lines, yytext); count_chars(yyleng);}
{TYPEID} {printf("#%d TYPEID %s\n", lines, yytext); count_chars(yyleng);}
{OPT} {printf("#%d %s\n", lines, yytext); count_chars(yyleng);}
{BRACKET} {printf("#%d %s\n", lines, yytext); count_chars(yyleng);}
{PLAHOLD} {printf("#%d %s\n", lines, yytext); count_chars(yyleng);}
{STD} {count_chars(yyleng);}
{OBJECTED} {printf("#%d OBJECTED %s\n", lines, yytext); count_chars(yyleng);}
{FLOAT} {printf("#%d CONST %s\n", lines, yytext); count_chars(yyleng);}
{INT} {printf("#%d CONST %d\n", lines, atoi(yytext)); count_chars(yyleng);}
{FUNC} {printf("#%d %s\n", lines, yytext); count_chars(yyleng); count_words_especially(yytext, yyleng);}
. {count_chars(yyleng);}
<<EOF>> {yyterminate();}
%%

int main(){
    yylex();
    fprintf(stderr,"lines:%d,words:%d,chars:%d\n", lines, words, chars);
    return 0;
}

void count_chars(int yyleng){
    chars += yyleng;
}

void count_words(){
    words++;
}

int isContiWS(char x){
    return (x == ' ' || x == '\t' || x == '\n');
}

void count_words_especially(char* yytext, int yyleng){
    for (int i = 0; i < yyleng; ++i)
    {
        if (isContiWS(yytext[i] ) && !isContiWS(yytext[i-1]))
            words++;
    }
}

void count_lines(char* yytext, int yyleng){
    for (int i = 0; i < yyleng; i++)
    {
        if (yytext[i] == '\n')
            lines++;
    }
}

int yywrap()
{
    return 1;
}
