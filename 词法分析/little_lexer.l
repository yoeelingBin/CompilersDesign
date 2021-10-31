%{
#include <stdio.h>
#include <stdlib.h>

int lines = 0;
int words = 0;
int chars = 0;
%}

DIGIT [0-9]
LETTER [a-zA-Z]
ID [a-z]({LETTER}|_|DIGIT)*
SYMBOL ("%"|"~"|"^"|"-"|"*"|"/"|"+"|";"|"="|":"|"|"|"&"|"{"|"}"|"("|")"|"<"|">"|">="|"<="|"&&"|"||"|"%f"|"%s"|"%lld") 
INT {DIGIT}+
FLOAT {DIGIT}+"."{DIGIT}+
TYPEID (Int)|(Float)|(String)|(Bool)|(Void)

%%

%%
int main(){

}
