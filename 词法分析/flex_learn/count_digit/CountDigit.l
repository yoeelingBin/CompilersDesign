%{
#include <stdio.h>
#include <stdlib.h>
int nDigitNumber=0;
%}
DIGIT [0-9]
%%
{DIGIT} {nDigitNumber=nDigitNumber+1;}
%%
int main()
{
    yylex();
    fprintf(stderr,"\nNumber of digit=%d\n", nDigitNumber);
    return(0);
}