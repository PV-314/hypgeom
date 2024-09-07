read("hypgeom\\general\\hypg-utils.gp");

\\ to check when we have one family of solutions
\\ We only need d=1 mod 8 if p \neq 2 in the definition of b

\\ need the m2>0 and d mod 8!=1 condition
\\ here are egs
\\ e1:=       104: d:= 17: x:=        23: y:=     5: v1:= 0.252825: v2:= 0.440931: x0:=  11: y0:=   1: t:=  66: u:=  16:
\\ e1:=       104: d:= 17: x:=        79: y:=    19: v1:= 0.559069: v2:= 0.747175: x0:=  11: y0:=   1: t:=  66: u:=  16:
\\ e1:=       104: d:= 17: x:=      1439: y:=   349: v1:= 1.252825: v2:= 1.440931: x0:=  11: y0:=   1: t:=  66: u:=  16:
\\ e1:=       104: d:= 17: x:=      5191: y:=  1259: v1:= 1.559069: v2:= 1.747175: x0:=  11: y0:=   1: t:=  66: u:=  16:
\\ e2:=      -104: d:= 17: x:=        27: y:=     7: v1:= 0.252825: v2:= 0.559069: x0:=   7: y0:=   3: t:=  66: u:=  16:
\\ e2:=      -104: d:= 17: x:=        61: y:=    15: v1:= 0.440931: v2:= 0.747175: x0:=   7: y0:=   3: t:=  66: u:=  16:
\\ e2:=      -104: d:= 17: x:=      1843: y:=   447: v1:= 1.252825: v2:= 1.559069: x0:=   7: y0:=   3: t:=  66: u:=  16:
\\ e2:=      -104: d:= 17: x:=      4053: y:=   983: v1:= 1.440931: v2:= 1.747175: x0:=   7: y0:=   3: t:=  66: u:=  16:

\\ 3 Sept 2024
check_lemma24()={
	do_lemma24_check(1);
}

\\ check what happens if we leave out the gcd(b,d)=1 condition
\\ 3 Sept 2024
check_lemma24_gcd_effect()={
	do_lemma24_check(0);
}

\\ check what happens if we leave out d=1 mod 8 condition for m2>0
\\ 4 Sept 2024
check_lemma24_dMod8_effect()={
	do_lemma24_check(1,0);
}

\\ 3 Sept 2024
do_lemma24_check(checkGcd,checkDMod8=1)={
	my(e1,e2,isDOK,solnP4,t,u);

	for(d=2,200,
		if(!issquare(d),
			if(d%10==1,print("starting d=",d));
			solnP4=solve_pell_plus4(d);
			if(length(solnP4)!=0,
				t=solnP4[1];
				u=solnP4[2];
				forprime(p=2,23,
				for(m1=0,5,
				for(m2=0,5,
					isDOK=true;
					if(checkDMod8,
						isDOK= (m2==0 || (m2>0 && d%8!=1));
					);
					if(isDOK,
						e1=2^m1*p^m2;
						if(!checkGcd || (checkGcd && gcd(e1,d)==1),
							check_d_and_e(d,e1,t,u);
						);
						e2=-2^m1*p^m2;
						if(!checkGcd || (checkGcd && gcd(e2,d)==1),
							check_d_and_e(d,e2,t,u);
						);
					);
				);
				);
				);
			);
		);
	);
}

\\ 6 Sept 2024 (pulled out of do_check() function)
check_d_and_e(d,e,t,u)={
	my(eps,isDone,logE,soln0,tol,v1,v1R,v1Tmp,v2,v2R,v2Tmp,x0,xSqr,y0,yUB);
	
	tol=0.0001;
	eps=(t+u*sqrt(d))/2;
	logE=log(eps);
	soln0=0;
	x0=0;
	y0=0;
	yUB=10000;
	for(y=1,yUB,
		xSqr=e+d*y*y;
		if(xSqr>0 && issquare(xSqr) && gcd(xSqr,y)==1,
			x=sqrtint(xSqr);
			if(soln0==0,
				x0=x;
				y0=y;
				soln0=x0+sqrt(d)*y0;
			);
			v1=(x+sqrt(d)*y)/soln0;
			v1=log(v1)/logE;
			v2=(x-sqrt(d)*y)/soln0;
			v2=log(abs(v2))/logE;
			if(abs(v1-round(v1))>tol && abs(v2-round(v2))>tol,
				printf("e(1):=%10d: d:=%3d: g:=%3d: x:=%10d: y:=%6d: v1:=%9.6f: v2:=%9.6f: x0:=%4d: y0:=%4d: t:=%4d: u:=%4d:\n",e,d,gcd(e,d),x,y,v1,v2,x0,y0,t,u);
			);
			isDone=0;
			if(abs(v1-round(v1))<tol,
				v1R=round(v1);
				v1Tmp=soln0*eps^v1R;
				if(abs((x+sqrt(d)*y)-v1Tmp)>tol,
					printf("e(2):=%10d: d:=%3d: g:=%3d: x:=%10d: y:=%6d: v1:=%9.6f: x+sqrt(d)y:=%9.6f: x0:=%4d: y0:=%4d: t:=%4d: u:=%4d:\n",e,d,gcd(e,d),x,y,v1,x+sqrt(d)*y,x0,y0,t,u);
				);
				if(abs((x+sqrt(d)*y)-v1Tmp)<tol,
					isDone=1;
				);
			);
			if(isDone==0 && abs(v2-round(v2))<tol,
				v2R=round(v2);
				\\ for e>0
				v2Tmp=soln0*(-eps^v2R);
				if(e<0,
					v2Tmp=soln0*eps^v2R;
				);
				if(abs((-x+sqrt(d)*y)-v2Tmp)>tol,
					printf("e(3):=%10d: d:=%3d: g:=%3d: x:=%10d: y:=%6d: x-sqrt(d)y:=%9.6f: v2:=%9.6f: x0:=%4d: y0:=%4d: t:=%4d: u:=%4d:\n",e,d,gcd(e,d),x,y,x-sqrt(d)*y,v2,x0,y0,t,u);
				);
			);
		);
	);
}

\\ the following test shows that a weaker version of gcd(d,e)=1 is needed, unless d is square-free
\\ the solution (x,y) comes from a unit in Q(sqrt(d/4)), not from in Z [ (1+sqrt(d))/2]
\\ run check_eg() in this file for more details: "C:\\MyStuff\\TeXFiles\\mypapers\\Hypergeometric\\My-Yuan-Zhang-Extension\\maple\\bad-b16pm-example.txt":
\\
\\ Digits:=40:t:=221994634540:u:=238309669:ep:=(t+u*sqrt(d))/2:epC:=(t-u*sqrt(d))/2:expand(ep*epC);epInv:=epC/%;
\\ (x1+y1^2*sqrt(d))/(x0+y0*sqrt(d));evalf(log(%)/log(ep));
\\    .6666666666666666666666666666666666666667
\\ (-x1+y1^2*sqrt(d))/(x0+y0*sqrt(d));evalf(log(%)/log(ep));
\\   -.7743219647984580403175408658451580956274
\\
\\ inside e2 useGCD if
\\ e(1):=   -185488: d:=867764: g:=  4: x:=32218340966: y:=34586161: v1:= 0.333333: v2:=-0.387161: x0:= 826: y0:=   1: t:=49281617764548161011602: u:=52903467877003367260:
\\ 7 Sept 2024
test1()={
	my(d,e,t,u);
	
	d=867764;
	e=-185488;
	t=49281617764548161011602;
	u=52903467877003367260;
	check_d_and_e(d,e,t,u);
}