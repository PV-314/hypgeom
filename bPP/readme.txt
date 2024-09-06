bPP-end-proof-check.gp
For the checks in Section 3.9, Small $a^{2} + b$ and small $y_{k}$.
It also outputs the Magma commands for all the equations that need checking using Magma
I used Magma's online calculator at http://magma.maths.usyd.edu.au/calc/
Use this after using bPP-Prop31-sequence-proof-calcs.gp

bPP-eqn-solution-search.gp
Finds small solutions of x^2-(a^2+mul*p^m)*y^4=-mul*p^m
Used for generating such examples in the Examples section

bPP-Lemma24-rep-check.gp
For checking examples to see that the statement of Lemma 2.4 holds.
Also has the function check_lemma24_dMod8_effect(), so examples with d=1 mod 8 and p odd can be found.
Other variations there too.

bPP-Prop31-sequence-proof-calcs.gp
This provides all the calculations of the quantities in the proof of Prop 3.1.
Use bPP-end-proof-check.gp afterwards to complete all the pre-Magma work for the proof of Prop 3.1

bPP-square-search.gp
This is used to find sequences with several squares in them, having b=2^ell*p^m, where ell=0,1,2,3,4
Used for generating such examples in the Examples section

bPP-yLB-check.gp
This is used to find examples for Lemma 2.1.
That is with y_k small relative to b^2 for k \neq 0



