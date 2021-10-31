%{
/*Lex program to convert uppercase to lowercase except inside comments*/
#include <stdio.h>
#include <ctype.h>
#ifndef FALSE
#define FALSE 0
#endif
#ifndef TRUE
#define TRUE 1
#endif
%}
%%
[A-Z] {putchar(tolower(yytext[0]));}
"/*" {   char c;
        int done = FALSE;
        do{
            while((c=input())!='*')
                putchar(c);
            putchar(c);
            while((c=input())=='*')
                putchar(c);
            putchar(c);
            if(c=='/')done=TRUE;
        }while(!done);
}
%%
void main(void)
{
    yylex();
}