%{
#include <stdio.h>
#include <stdlib.h>

int lines = 0;
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
KEYWORD (fprintf)|(while)|(aafor)|(if)|(else)|(continue)|(break)|(return)|(func)
INT {DIGIT}+
FLOAT {DIGIT}+"."{DIGIT}+
CONST ({INT}|{DIGIT})
TYPEID (Int)|(Float)|(String)|(Bool)|(Void)


%%
NEWLINE {lines++; chars++}

%%
int main(){

}
