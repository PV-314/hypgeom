\\ calc_gnd4LB                  given N_a, it calculates lower bound for g*\cN_{d,4}
\\ calc_gnd4_from_nrmACore_and_xk	what the name says
\\ calc_gnd4_from_xk		what the name says
\\ calc_gNSqr(t,u1,u2)		returns [gSqr,nd4Sqr] for the args
\\ check_minus4			returns 1 if x^2-d*y^2=-4 is solvable, 0 otherwise
\\ check_sequence		used in the end-proof-sequence-check scripts
\\ get_clean_solutions
\\ get_solns_from_e
\\ get_solns_from_e2
\\ get_val(v,p)			returns v_p(v)
\\ output_solns			used in the end-proof-sequence-check scripts
\\ quadcheck_a2b		returns 1 if gcd(a,b)=1 and x^2-(a*a+b)*y^2=-b*b has just one family of solutions. Returns 0 otherwise
\\ quadcheck_a2b2		returns 1 if gcd(a,b)=1 and x^2-(a*a+b*b)*y^2=-b*b has just one family of solutions. Returns 0 otherwise
\\ quadcheck_a2b2_minus4	returns 1 if gcd(a,b)=1 and x^2-(a*a+b*b)*y^2=-b*b has just one family of solutions and x^2-(a*a+b*b)*y^2=-4. Returns 0 otherwise
\\ round_down
\\ round_up
\\ solve_minus_a2b		checking for the number of families of solns of x^2-(a*a+b)*y^2=-b (calls to solve_minusb)
\\ solve_minus_a2b2		checking for the number of families of solns of x^2-(a*a+b*b)*y^2=-b*b (calls to solve_minusb)
\\ solve_minusb			checking for the number of families of solns of x^2-d*y^2=-b
\\ solve_pell_minus1		returns smallest [x,y] if x^2-d*y^2=-1 is solvable, [] otherwise
\\ solve_pell_minus1_with_cf
\\ solve_pell_minus4		returns smallest [x,y] if x^2-d*y^2=-4 is solvable, [] otherwise
\\ solve_pell_minus4_with_cf
\\ solve_pell_plus1		returns smallest [x,y] of x^2-d*y^2=1
\\ solve_pell_plus1_with_cf
\\ solve_pell_plus4		returns smallest [x,y] of x^2-d*y^2=4
\\ solve_pell_plus4_with_cf

\\ \p 50 is needed for a=47, b=78362 (does this mean d=a*a+b?)
\\ solve the Pell-ish equation x^2-d*y^2=-4 using ONLY cf
\\ the reason is that if we cannot find it from cf (due to precision etc)
\\ then it is too large for our interests
\\ if solvable return the smallest x and y in a vector[x,y]
\\ else return empty vector []
\\
\\ calls to solve_pell_minus4_with_cf(d,cf) to do the actual work
solve_pell_minus4(d)={
	my(cf,cvgts,index,pn,pn1,pn4,qn,qn1,qn4,t,v);

	\\ cf does not give solns for small d (fixed 7 Aug 2019)
	if(d<16,
		if(d==2,return([2,2]));
		if(d==5,return([1,1]));
		if(d==8,return([2,1]));
		if(d==10,return([6,2]));
		if(d==13,return([3,1]));
		return([]);
	);
	if(d%4==0,
		solnM1=solve_pell_minus1(d/4);
		if(length(solnM1)>0,
			return([2*solnM1[1], solnM1[2]]);
		);
		return([]);
	);
	if(d%4==2,
		solnM1=solve_pell_minus1(d);
		if(length(solnM1)>0,
			return([2*solnM1[1], 2*solnM1[2]]);
		);
		return([]);
	);
	\\ arguing mod 16, there is no solution in this case
	if(d%4==3,
		return([]);
	);
	
	cf=contfrac(sqrt(d));
	return(solve_pell_minus4_with_cf(d,cf));
}

\\ \p 50 is needed for a=47, b=78362
\\ solve the Pell-ish equation x^2-d*y^2=-4 using ONLY cf
\\ the reason is that if we cannot find it from cf (due to precision etc)
\\ then it is too large for our interests
\\ if solvable return the smallest x and y in a vector[x,y]
\\ else return empty vector []
\\
\\ does the actual work
solve_pell_minus4_with_cf(d,cf)={
	my(cvgts,index,pn,pn1,pn4,qn,qn1,qn4,t,v);

	\\ cf does not give solns for small d (fixed 7 Aug 2019)
	if(d<16,
		if(d==2,return([2,2]));
		if(d==5,return([1,1]));
		if(d==8,return([2,1]));
		if(d==10,return([6,2]));
		if(d==13,return([3,1]));
		return([]);
	);
	if(d%4==0,
		solnM1=solve_pell_minus1(d/4);
		if(length(solnM1)>0,
			return([2*solnM1[1], solnM1[2]]);
		);
		return([]);
	);
	if(d%4==2,
		solnM1=solve_pell_minus1_with_cf(d,cf);
		if(length(solnM1)>0,
			return([2*solnM1[1], 2*solnM1[2]]);
		);
		return([]);
	);
	\\ arguing mod 16, there is no solution in this case
	if(d%4==3,
		return([]);
	);
	
	t=2*floor(sqrt(d));
	index=0;
	for(i=1,length(cf),
		if(cf[i]==t && index==0,
			index=i;
		);
	);
	\\if(index==0,
	\\	print("need more accuracy for d=",d,", index>",length(cf));
	\\);
	\\print("d=",d,", index=",index);
	if(index>0,
		cvgts=contfracpnqn(cf,index);
		pn4=0;
		qn4=0;
		pn1=0;
		qn1=0;
		for(i=1,index,
			pn=cvgts[1,i];
			qn=cvgts[2,i];
			v=pn*pn-d*qn*qn;
			if(v==-4 && pn4==0,
				pn4=pn;
				qn4=qn;
				if(pn1==0 || pn4<2*pn1,
					return([pn4,qn4]);
				);
			);
			if(v==-1 && pn1==0,
				pn1=pn;
				qn1=qn;
			);
		);
		if(pn1!=0 && pn4==0,
			pn4=2*pn1;
			qn4=2*qn1;
		);
		if(pn4!=0 && qn4!=0,
			return([pn4,qn4]);
		);
	);
	return([]);
}

\\ \p 50 is needed for a=47, b=78362
\\ solve the Pell-ish equation x^2-d*y^2=-1 using ONLY cf
\\ if solvable return the smallest x and y in a vector[x,y]
\\ else return empty vector []
\\
\\ calls to solve_pell_minus1_with_cf(d,cf) to do the actual work
solve_pell_minus1(d)={
	my(cf);

	cf=contfrac(sqrt(d));
	return(solve_pell_minus1_with_cf(d,cf));
}

\\ \p 50 is needed for a=47, b=78362
\\ solve the Pell-ish equation x^2-d*y^2=-1 using ONLY cf
\\ if solvable return the smallest x and y in a vector[x,y]
\\ else return empty vector []
\\
\\ does the actual work
solve_pell_minus1_with_cf(d,cf)={
	my(cvgts,index,pn,qn,t,v);

	t=2*floor(sqrt(d));
	index=0;
	for(i=1,length(cf),
		if(cf[i]==t && index==0,
			index=i;
		);
	);
	\\if(index==0,
	\\	print("need more accuracy for d=",d,", index>",length(cf));
	\\);
	\\print("in solve_pell_minus1_with_cf(d,cf): d=",d,", index=",index,", cf=",cf);
	if(index>0,
		if(index%2!=0,
			return([]);
		);
		cvgts=contfracpnqn(cf,index);
		pn=cvgts[1,index-1];
		qn=cvgts[2,index-1];
		v=pn*pn-d*qn*qn;
		if(v==-1,
			return([pn,qn]);
		);
		if(v!=-1,
			print("ERROR: d=",d,", index=",index,", pn=",pn,", qn=",qn);
		);
	);
	return([]);
}

\\ \p 50 likely needed
\\ solve the Pell-ish equation x^2-d*y^2=1 using ONLY cf
\\ the reason is that if we cannot find it from cf (due to precision etc)
\\ then it is (?) too large for our interests
\\ if solvable return the smallest x and y in a vector[x,y]
\\ else return empty vector []
\\
\\ calls to solve_pell_plus1_with_cf(d,cf) to do the actual work
solve_pell_plus1(d)={
	my(cf,cvgts,index,pn,pn1,qn,qn1,t,v);
	
	cf=contfrac(sqrt(d));
	t=2*floor(sqrt(d));
	index=0;
	for(i=1,length(cf),
		if(cf[i]==t && index==0,
			index=i;
		);
	);
	if(index>0 && index%2==0 && (2*index-1>length(cf) || cf[2*index-1]!=t),
		index=0;
	);
	if(index%2==0 && index>0,
		index=2*index-1;
	);
	
	\\if(index==0,
	\\	print("need more accuracy for d=",d,", index>",length(cf));
	\\);
	if(index>0,
		cvgts=contfracpnqn(cf,index);
		pn=cvgts[1,index-1];
		qn=cvgts[2,index-1];
		v=pn*pn-d*qn*qn;
		if(v==1,
			return([pn,qn]);
		);
		if(v!=1,
			print("ERROR: d=",d,", index=",index,", pn=",pn,", qn=",qn);
		);
	);
	return([]);
}

solve_pell_plus1_with_cf(d,cf)={
	my(cvgts,index,pn,pn1,qn,qn1,t,v);
	
	t=2*floor(sqrt(d));
	index=0;
	for(i=1,length(cf),
		if(cf[i]==t && index==0,
			index=i;
		);
	);
	if(index>0 && index%2==0 && (2*index-1>length(cf) || cf[2*index-1]!=t),
		index=0;
	);
	if(index%2==0 && index>0,
		index=2*index-1;
	);
	
	\\if(index==0,
	\\	print("need more accuracy for d=",d,", index>",length(cf));
	\\);
	if(index>0,
		cvgts=contfracpnqn(cf,index);
		pn=cvgts[1,index-1];
		qn=cvgts[2,index-1];
		v=pn*pn-d*qn*qn;
		if(v==1,
			return([pn,qn]);
		);
		if(v!=1,
			print("ERROR: d=",d,", index=",index,", pn=",pn,", qn=",qn);
		);
	);
	return([]);
}

\\ \p 50 is needed for a=47, b=78362
\\ solve the Pell-ish equation x^2-d*y^2=4 using ONLY cf
\\ the reason is that if we cannot find it from cf (due to precision etc)
\\ then it is (?) too large for our interests
\\ if solvable return the smallest x and y in a vector[x,y]
\\ else return empty vector []
solve_pell_plus4(d,dbg=0)={
	my(cf);
	
	\\ cf does not give solns for small d (fixed 7 Aug 2019)
	if(d<16,
		if(d==2,return([6,4]));
		if(d==3,return([4,2]));
		if(d==5,return([3,1]));
		if(d==6,return([10,4]));
		if(d==7,return([16,6]));
		if(d==8,return([6,2]));
		if(d==10,return([38,12]));
		if(d==11,return([20,6]));
		if(d==12,return([4,1]));
		if(d==13,return([11,3]));
		if(d==14,return([30,8]));
		if(d==15,return([8,2]));
		return([]);
	);
	cf=contfrac(sqrt(d));
	return(solve_pell_plus4_with_cf(d,cf,dbg));
}

solve_pell_plus4_with_cf(d,cf,dbg=0)={
	my(cvgts,index,pn,pn1,pn4,qn,qn1,qn4,t,v);
	
	\\ cf does not give solns for small d (fixed 7 Aug 2019)
	if(d<16,
		if(d==2,return([6,4]));
		if(d==3,return([4,2]));
		if(d==5,return([3,1]));
		if(d==6,return([10,4]));
		if(d==7,return([16,6]));
		if(d==8,return([6,2]));
		if(d==10,return([38,12]));
		if(d==11,return([20,6]));
		if(d==12,return([4,1]));
		if(d==13,return([11,3]));
		if(d==14,return([30,8]));
		if(d==15,return([8,2]));
		return([]);
	);
	t=2*floor(sqrt(d));
	index=0;
	for(i=1,length(cf),
		if(dbg!=0,print("i=",i,", cf[i]=",cf[i],", t=",t));
		if(cf[i]==t && index==0,
			index=i;
		);
	);
	
	if(index>0 && index%2==0 && (2*index-1>length(cf) || cf[2*index-1]!=t),
		if(dbg!=0,
			print("index=",index,", 2*index-1=",(2*index-1),", length(cf)=",length(cf));
			if(2*index-1<=length(cf),
				print("   cf[2*index-1]=",cf[2*index-1]);
			);
		);
		index=0;
	);
	if(index%2==0 && index>0,
		index=2*index-1;
	);
	
	if(dbg!=0,
		print("d=",d,", index=",index);
		print("cf=",cf);
		if(index==0,
			print("need more accuracy for d=",d,", index>",length(cf));
		);
	);
	
	\\ try anyway
	\\d=47885 suggests this can sometimes help and my tests show it does not hurt
	if(index==0,
		index=length(cf)/2;
	);
	if(index>0,
		if(dbg!=0,print("d=",d,", index=",index,", length(cf)=",length(cf)));
		cvgts=contfracpnqn(cf,2*index);
		pn4=0;
		qn4=0;
		pn1=0;
		qn1=0;
		for(i=1,length(cvgts),
			pn=cvgts[1,i];
			qn=cvgts[2,i];
			v=pn*pn-d*qn*qn;
			if(dbg!=0,print("d=",d,", n=",i,", p_n=",pn,", q_n=",qn,", v=",v));
			if(v==4 && pn4==0,
				pn4=pn;
				qn4=qn;
				return([pn4,qn4]);
			);
			if(v==1 && pn1==0,
				pn1=pn;
				qn1=qn;
			);
		);
		\\ use (pn1,qn1) solution only if we have not found a (pn4,qn4) solution
		if(pn1!=0 && pn4==0,
			pn4=2*pn1;
			qn4=2*qn1;
		);
		if(dbg!=0,print("d=",d,", pn1=",pn1,", qn1=",qn1,"pn4=",pn4,", qn4=",qn4));
		if(pn4!=0 && qn4!=0,
			return([pn4,qn4]);
		);
	);
	return([]);
}

\\ returns 1 if x^2-dy^2=-4 is solvable
\\ else returns 0
\\ check via http://www.numbertheory.org/php/pell.html
check_minus4(d,dbg=0)={
	my(cf,f,index,isOK,K,m4Solns,m4Solvable,t);
	
	soln=solve_pell_minus4(d);
	if(length(soln)>1,return(1));
	K=bnfinit(x^2-d,1);

	fu=K.fu[1];
	nfu=norm(fu);
	if(nfu==-1,
		fu=nfeltmul(K,fu,fu);
	);
	fuAlg=lift(nfbasistoalg(K,fu));
	fuAlgC=fuAlg-2*polcoeff(fuAlg,0);
	m4Solns=get_clean_solutions(K,d,-4,fuAlg,fuAlgC,dbg);
	m4Solvable=0;
	for(i=1,length(m4Solns),
		f=m4Solns[i];
		if(poldegree(f)==1 && denominator(content(f))==1,
			m4Solvable=1;
		);
	);
	if(m4Solvable==0,
		solns=solve_pell_minus4(d);
		if(length(solns)>0,
			m4Solvable=1;
		);
	);
	return(m4Solvable);
}

\\ was quadcheck_ab
\\ this returns
\\ 1 if gcd(a,b)=1 and x^2-(a*a+b*b)*y^2=-b*b has just one family of solutions
\\ 0 otherwise
quadcheck_a2b2(a,b,dbg=0)={
	my();
	
	return(quadcheck_a2b(a,b*b,dbg));
}

\\ this returns
\\ 1 if gcd(a,b)=1 and x^2-(a*a+b)*y^2=-b has just one family of solutions
\\ 0 otherwise
quadcheck_a2b(a,b,dbg=0)={
	my(cnt,d);
	
	if(gcd(a,b)==1,
		d=a*a+b;
		if(!issquare(d),
			cnt=length(solve_minusb(d,b,dbg));
			if(cnt==0,
				return(1);
				\\printf("a=%4d, b=%4d=%s, m1Solvable=%1d, b2Solns=%s\n",a,b,factor(b),m1Solvable,b2Solns);
			);
		);
	);
	return(0);
}

\\ was quadcheck_ab_negpell(
\\ this returns
\\ 1 if x^2-(a*a+b*b)*y^2=-b*b has just one family of solutions
\\   and x^2-(a*a+b*b)*y^2=-4 is solvable (hence the function name)
\\ 0 otherwise
quadcheck_a2b2_minus4(a,b,dbg=0)={
	my(cnt,d,m4Solvable);
	
	if(gcd(a,b)==1,
		d=a*a+b*b;
		if(!issquare(d), \\ && d<3380,
			m4Solvable=check_minus4(d);
			if(m4Solvable==1,
				cnt=length(solve_minus_a2b2(a,b));
				if(cnt==0 && m4Solvable==1,
					return(1);
					\\printf("a=%4d, b=%4d=%s, m4Solvable=%1d, b2Solns=%s\n",a,b,factor(b),m4Solvable,b2Solns);
				);
			);
		);
	);
	return(0);
}

\\ returns a List of representatives of each distinct family of solutions of x^2-(a^2+b*b)*y^4=-b
\\ excluding the "trivial" family from (a,1)
solve_minus_a2b2(a,b,dbg=0)={
	return(solve_minusb(a*a+b*b,b*b,dbg));
}

\\ returns a List of representatives of each distinct family of solutions of x^2-(a^2+b)*y^4=-b
\\ excluding the "trivial" family from (a,1)
solve_minus_a2b(a,b,dbg=0)={
	return(solve_minusb(a*a+b,b,dbg));
}

\\ returns a List of representatives of each distinct family of solutions of x^2-d*y^2=-b
\\ excluding the "trivial" family from (a,1)
\\
\\ as of 22 May 2019, this only works correctly when d is squarefree
\\ if d `is not squarefree, it *may* count too few families (e.g., test_eg8() in hypg-tests.gp)
\\ as of 23 May 2019, some fixes for d not squarefree are in place, but it *may* still count too few families
solve_minusb(d,b,dbg=0)={
	my(bSolns,bSolns1,cnt,d1,df0,df1,f,f0,f1,fOld,fu,fuAlg,fuAlgC,isOK,K,nfu,solns,v1,v2);
	
	\\ make fu of norm 1
	K=bnfinit(x^2-d,1);
	fu=K.fu[1];
	nfu=norm(fu);
	if(nfu==-1,
		fu=nfeltmul(K,fu,fu);
	);
	fuAlg=lift(nfbasistoalg(K,fu));
	fuAlgC=fuAlg-2*x*polcoeff(fuAlg,1);
	
	solnP4=solve_pell_plus4(d);
	if(length(solnP4)>0,
		fuAlg=(solnP4[1]+x*solnP4[2])/2;
		fuAlgC=(solnP4[1]-x*solnP4[2])/2;
	);
	
	if(dbg!=0,
		print("solve_minusb(): fundamental unit for d=",d,", b=",b,": fu=",fuAlg,", fuC=",fuAlgC);
	);
	bSolns1=get_clean_solutions(K,d,-b,fuAlg,fuAlgC,dbg);
	
	\\ we will only count solutions that are not in the same class as (x,y)=(??,1)
	cnt=0;
	solns=List();

	for(i=1,length(bSolns1),
		f=bSolns1[i];
		if(dbg!=0,
			print("\nwith f: d=",d,", b=",b,", i=",i,", f=",f,", v1=",v1);
		);

		\\ do not want any constant elements (hence poldegree(f)==1)
		\\ want no common factors (either in denom or numerator, hence content(f)==1)
		\\ do not want to count (??,1) (hence abs(polcoeff(f,1))!=1)
		if(abs(polcoeff(f,1))!=1,
			if(dbg!=0,
				print("considering f: d=",d,", b=",b,", i=",i,", f=",f,", v1=",v1);
			);
			isOK=1;
			for(j=1,length(bSolns1),
				if(abs(polcoeff(f,1))>abs(polcoeff(bSolns1[j],1)),
					v1=lift(nfbasistoalg(K,nfeltmul(K,bSolns1[j],fuAlg)));
					if(dbg!=0,
						print("checking v1=bSolns1[j]*fuAlg: d=",d,", b=",b,", i=",i,", f=",f,", j=",j,", bSolns1[j]=",bSolns1[j],", v1=",v1);
					);
					if(abs(polcoeff(v1,1))==abs(polcoeff(f,1)),
						if(dbg!=0,
							print("v1 matches: d=",d,", b=",b,", i=",i,", f=",f,", j=",j,", bSolns1[j]=",bSolns1[j],", v1=",v1);
						);
						isOK=0;
					);
					if(isOK==1,
						v1=lift(nfbasistoalg(K,nfeltmul(K,v1,fuAlg)));
						if(dbg!=0,
							print("checking v1=bSolns1[j]*fuAlg^2: d=",d,", b=",b,", i=",i,", f=",f,", j=",j,", bSolns1[j]=",bSolns1[j],", v1=",v1);
						);
						if(abs(polcoeff(v1,1))==abs(polcoeff(f,1)),
							if(dbg!=0,
								print("v1 matches: d=",d,", b=",b,", i=",i,", f=",f,", j=",j,", bSolns1[j]=",bSolns1[j],", v1=",v1);
							);
							isOK=0;
						);
						if(isOK==1,
							v2=lift(nfbasistoalg(K,nfeltmul(K,bSolns1[j],fuAlgC)));
							if(dbg!=0,
								print("checking v2=bSolns1[j]*fuAlgC: d=",d,", b=",b,", i=",i,", f=",f,", j=",j,", bSolns1[j]=",bSolns1[j],", v2=",v2);
							);
							if(abs(polcoeff(v2,1))==abs(polcoeff(f,1)),
								if(dbg!=0,
									print("v2 matches: d=",d,", b=",b,", f=",f,", bSolns1[j]=",bSolns1[j],", v2=",v2);
								);
								isOK=0;
							);
							if(isOK==1,
								v2=lift(nfbasistoalg(K,nfeltmul(K,v2,fuAlgC)));
								if(dbg!=0,
									print("checking v2=bSolns1[j]*fuAlgC^2: d=",d,", b=",b,", i=",i,", f=",f,", j=",j,", bSolns1[j]=",bSolns1[j],", v2=",v2);
								);
								if(abs(polcoeff(v2,1))==abs(polcoeff(f,1)),
									if(dbg!=0,
										print("v2 matches: d=",d,", b=",b,", f=",f,", bSolns1[j]=",bSolns1[j],", v2=",v2);
									);
									isOK=0;
								);
							);
						);
					);
				);
			);
			if(isOK==1,
				cnt++;
				listput(solns,[f]);
			);
		);
	);
	if(dbg!=0,
		print("solve_minusb() finished: d=",d,", b=",b,", cnt=",cnt,", solns=",solns);
	);
	return(solns);
}

\\ finding solutions of bnfisintnorm(K,v)
\\ sorting out problems when d is not squarefree and also removing conjugates
get_clean_solutions(K,d,v,fuAlg,fuAlgC,dbg)={
	my(bSolns,bSolns1,bSolns2,denomUB,df0,df1,f,f0,f1,solnM4);
	
	bSolns=bnfisintnorm(K,v);

	\\ fix elements if d not squarefree
	if(dbg!=0,
		print("get_clean_solutions(), before fixing: length(bSolns)=",length(bSolns),"\n   bSolns=",bSolns);
	);
	if (!issquarefree(d),
		for(i=1,length(bSolns),
			f=bSolns[i];
			if(dbg!=0,
				print("   fixing with f: d=",d,", v=",v,", i=",i,", f=",f);
			);
			if (poldegree(f)==1,
				f0=polcoef(f,0);
				f1=polcoef(f,1);
				df0=denominator(f0);
				df1=denominator(f1);
				\\d1=sqrtint(d/core(d));
				if(df0!=1 || df1!=1,
					if(dbg!=0,
						print("   fixing with f: d=",d,", v=",v,", i=",i,", f=",f); \\,", df0=",df0,", df1=",df1,", d1=",d1);
					);
					fOld=f;
					f=nfeltmul(K,bSolns[i],fuAlg);
					f=lift(nfbasistoalg(K,f));
					if(content(f)==1,
						bSolns[i]=f;
						if(dbg!=0,
							print("   fixable with f: d=",d,", v=",v,", i=",i,", f=",bSolns[i],", fOld=",fOld);
						);
					);
					if(content(f)!=1,
						f=nfeltmul(K,bSolns[i],fuAlgC);
						f=lift(nfbasistoalg(K,f));
						if(content(f)==1,
							bSolns[i]=f;
							if(dbg!=0,
								print("   fixable with f: d=",d,", v=",v,", i=",i,", f=",bSolns[i],", fOld=",fOld);
							);
						);
						if(content(f)!=1,
							f=nfeltmul(K,bSolns[i],fuAlg);
							f=nfeltmul(K,f,fuAlg);
							f=lift(nfbasistoalg(K,f));
							if(content(f)==1,
								bSolns[i]=f;
								if(dbg!=0,
									print("   fixable with f: d=",d,", v=",v,", i=",i,", f=",bSolns[i],", fOld=",fOld);
								);
							);
						);
					);
				);
			);
		);
		\\if(dbg!=0,
		\\	print("\n");
		\\);
	);

	\\ remove conjugates
	bSolns1=List();
	for(i=1,length(bSolns),
		f=bSolns[i];
		isOK=1;
		for(j=1,i-1,
			if(abs(polcoeff(f,1))==abs(polcoeff(bSolns[j],1)),
				isOK=0;
			);
		);
		if(isOK==1,
			listput(bSolns1,f);
		);
	);
	if(dbg!=0,
		print("   after removing conjugates, bSolns1=",bSolns1);
	);
	
	\\ remove other things too
	solnM4=solve_pell_minus4(d);
	denomUB=1;
	if(length(solnM4)>0 && solnM4[1]%2==1 && solnM4[2]%2==1,
		denomUB=2;
	);
	bSolns2=List();
	for(i=1,length(bSolns1),
		f=bSolns1[i];
		if(poldegree(f)==1 && numerator(content(f))==1 && denominator(content(f))<=denomUB,
			listput(bSolns2,f);
		);
	);
	if(dbg!=0,
		print("get_clean_solutions(), after removing other things too, bSolns2=",bSolns2);
	);
	return(bSolns2);
}

\\ given a and b and a solution (t,u) of t^2-(a*a+b*c*c)u^2 = \pm 1
\\ note t and u may have denominators of 2
\\ this condition has been removed on 10 Nov 2019: with t and u not both integers if t^2-(a*a+b*c*c)u^2 =1 (because we will use e^2 below)
\\ 
\\ return a two-element array
\\ array[1] is a Pari Set of all the solutions of x^2-(a*a+b*c*c)y^4=-b
\\ that come from first few elements of
\\ (a+sqrt(a*a+b*c*c))*e^(2*k) (where e=t+u*sqrt(a*a+b*c*c) and k is small in absolute value)
\\ array[2] is a lower bound on y for any further solutions
\\
\\ last revised on 10 Nov 2019
get_solns_from_e2(a,b,c,t,u,dbg=0)={
	my(c0,c1,d,solns,xNegCurr2,xPosCurr2,yNegCurr,yNegPrev,yPosCurr,yPosPrev,yT);

	d=a*a+b*c*c;
	if(dbg!=0,print("get_solns_from_e2() start: a=",a,", b=",b,", c=",c,", d=",d,", t=",t,", u=",u));
	solns=Set([[a,1]]);
	\\ c1 is e^2+e^(-2) with e as above (where e^(-2) is the algebraic conjugate of e^2)
	\\ that is, it is twice the rational part of e^2
	c1=2*(t*t+d*u*u);
	c0=-1;
	
	\\ yP for the previous element
	\\ we have yPa and yPb. yPa is for the sequence y_k with k \geq 0
	\\ yPb is for the sequence y_k with k \leq 0
	yPosPrev=1;
	yNegPrev=1;

	yPosCurr=(2*a*t*u+t*t+u*u*d);
	xPosCurr2=d*yPosCurr*yPosCurr-b;

	yNegCurr=(-2*a*t*u+t*t+u*u*d);
	
	xNegCurr2=d*yNegCurr*yNegCurr-b;

	for(i=1,6,
		if(dbg!=0,print(i,": xPosCurr2=",xPosCurr2,", yPosCurr=",yPosCurr));
		if(xPosCurr2>0 && yPosCurr!=0 && gcd(xPosCurr2,yPosCurr)==1 && issquare(xPosCurr2) && issquare(abs(yPosCurr)),
			solns=setunion(solns,Set([[sqrtint(xPosCurr2),sqrtint(yPosCurr)]]));
			\\print(i,": added xPosCurr2,yPosCurr: solns=",solns);
		);
		yT=c1*yPosCurr+c0*yPosPrev;
		yPosPrerv=yPosCurr;
		yPosCurr=yT;
		xPosCurr2=d*yPosCurr*yPosCurr-b;

		if(dbg!=0,print(i,": xNegCurr2=",xNegCurr2,", yNegCurr=",yNegCurr));
		if(xNegCurr2>0 && yNegCurr!=0 && gcd(xNegCurr2,yNegCurr)==1 && issquare(xNegCurr2) && issquare(abs(yNegCurr)),
			solns=setunion(solns,Set([[sqrtint(xNegCurr2),sqrtint(yNegCurr)]]));
			\\print(i,": added xNegCurr2,yNegCurr: solns=",solns);
		);
		yT=c1*yNegCurr+c0*yNegPrev;
		yNegPrev=yNegCurr;
		yNegCurr=yT;
		xNegCurr2=d*yNegCurr*yNegCurr-b;
	);
	return([solns,min(yNegCurr,yPosCurr)]);
}

\\ given a and b and the fundamental solution (t,u) of t^2-(a^2+b)u^2 =1
\\ 
\\ return solutions of x^2-(a^2+b)y^4=-b that come from first few elements of
\\ (a+sqrt(a^2+b))*e (where e=t+u*sqrt(a^2+b) )
get_solns_from_e(a,b,t,u,dbg=0)={
	my(c0,c1,d,solns,xCa2,xCb2,xPa2,xPb2,yCa,yCb,yPa,yPb,yTa,yTb);

	d=a*a+b;	
	solns=Set([[a,1]]);
	\\ c1 is the rational term in e above
	c1=2*t;
	c0=-1;

	yPa=1;
	yPb=1;
	
	yCa=a*u+t;
	xCa2=d*yCa*yCa-b;
	if(dbg!=0,print("1: xCa2=",xCa2,", yCa=",yCa));
	if(xCa2>0 && yCa!=0 && gcd(xCa2,yCa)==1 && issquare(xCa2) && issquare(abs(yCa)),
		solns=setunion(solns,Set([[sqrtint(xCa2),sqrtint(yCa)]]));
	);

	\\y1b=-a1*t1*u1/2+a2*t1*t1/4+a2*u1*u1*d/4;
	yCb=t-a*u;
	xCb2=d*yCb*yCb-b;
	if(dbg!=0,print("1: xCb2=",xCb2,", yCb=",yCb));
	if(xCb2>0 && yCb!=0 && gcd(xCb2,yCb)==1 && issquare(xCb2) && issquare(abs(yCb)),
		solns=setunion(solns,Set([[sqrtint(xCb2),sqrtint(yCb)]]));
		\\print("1: added xCb2,yCb: solns=",solns);
	);
	
	for(i=2,6,
		yTa=c1*yCa+c0*yPa;
		yPa=yCa;
		yCa=yTa;
		xCa2=d*yCa*yCa-b;
		if(dbg!=0,print(i,": xCa2=",xCa2,", yCa=",yCa));
		if(xCa2>0 && yCa!=0 && gcd(xCa2,yCa)==1 && issquare(xCa2) && issquare(abs(yCa)),
			solns=setunion(solns,Set([[sqrtint(xCa2),sqrtint(yCa)]]));
			\\print(i,": added xCa2,yCa: solns=",solns);
		);

		yTb=c1*yCb+c0*yPb;
		yPb=yCb;
		yCb=yTb;
		xCb2=d*yCb*yCb-b;
		if(dbg!=0,print(i,": xCb2=",xCb2,", yCb=",yCb));
		if(xCb2>0 && yCb!=0 && gcd(xCb2,yCb)==1 && issquare(xCb2) && issquare(abs(yCb)),
			solns=setunion(solns,Set([[sqrtint(xCb2),sqrtint(yCb)]]));
			\\print(i,": added xCb2,yCb: solns=",solns);
		);
	);
	return(solns);
}

\\ return |g|\cN_{d,4}, hence the function name
\\ in fact, it is a lower bound for |g|\cN_{d,4} using the lower bound in Lemma~lem:gnd4
calc_gnd4LB(nrmA)={
	if(nrmA%2==1,return(2));
	if(nrmA%4==2,return(2*sqrt(2)));
	if(nrmA%8==4,return(2*2));
	if(nrmA%16==8,return(2*2*sqrt(2)));
	return(8);
}

\\ return [gSqr,nSqr] - use squares because both g and \cN_{d,4} can have square roots in them
\\ 16 June 2020 (but in g-values.gp from before (May 2020)
calc_gNSqr(t,u1,u2)={
	my(d,e2,g1,g2,g3,gNSqr,gSqr,nSqr,v1);
	
	if(t>-1,
		print("ERROR in calc_gNSqr(): t=",t," must be negative");
		1/0;
	);
	g1=gcd(u1,u2);
	g2=gcd(u1/g1,t);
	v1=(u1-u2)/g1;
	g3=4;
	if(v1%2==0 && t%4==3,
		g3=2;
	);
	if(v1%2==0 && t%4==1,
		g3=1;
	);
	gSqr=g1*g1*g2/g3;
	d=u2*u2*t/gSqr;
	e2=3; \\ the max value of exponent v_p(n)+1/(p-1)=v_2(4)+1/(2-1)=3
	nSqr=64;
	if(d%2==1,e2=0;nSqr=1);
	if(d%2==0 && d%4!=0,e2=1/2;nSqr=2);
	if(d%4==0 && d%8!=0,e2=1;nSqr=4);
	if(d%8==0 && d%16!=0,e2=3/2;nSqr=8);
	if(d%16==0 && d%32!=0,e2=2;nSqr=16);
	if(d%32==0 && d%64!=0,e2=5/2;nSqr=32);
	gNSqr=gSqr*nSqr;
	return([gSqr,nSqr]);
}

\\ return |g|\cN_{d,4} value from u1=2*xk, u2=\pm 2 and t=b
calc_gnd4_from_xk(b,xk)={
	my(gNSqr,t,u1,u2);
	
	t=-b;
	u1=2*xk;
	u2=2;
	gNSqr=calc_gNSqr(t,u1,u2);
	return(sqrt(gNSqr[1]*gNSqr[2]));
}

\\ return |g|\cN_{d,4}, hence the function name
\\ 15 May 2020
calc_gnd4_from_nrmACore_and_xk(nrmA,xk)={
	my(gNSqr,t,u1,u2);
	
	t=core(nrmA);
	u1=2*xk;
	u2=2*sqrtint(nrmA/t);
	gNSqr=calc_gNSqr(t,u1,u2);
	return(sqrt(gNSqr[1]*gNSqr[2]));
}

round_down(num,places)={
	if(type(num)=="t_POL" || type(num)=="t_RFRAC",
		print("ERROR in round_down(): num=",num," must a positive number. It is ",type(num));
		1/0;
		return();
	);
	if(num<0 || num==0,
		print("ERROR in round_down(): num=",num," must be positive");
		1/0;
		return();
	);
	e=floor(log(num)/log(10))-(places-1);
	\\print("num=",num,", e=",e);
	v=floor(num/10.0^e)*10.0^e;
	\\print("v=",v);
	return(v);
}

round_up(num,places)={
	if(type(num)=="t_POL" || type(num)=="t_RFRAC",
		print("ERROR in round_up(): num=",num," must a positive number. It is ",type(num));
		1/0;
		return();
	);
	if(num<0 || num==0,
		print("ERROR in round_up(): num=",num," must be positive");
		1/0;
		return();
	);
	e=floor(log(num)/log(10))-(places-1);
	v=ceil(num/10.0^e)*10.0^e;
	return(v);
}

\\ used in the end-of-proof-sequence-check scripts
\\ (as of 17 May 2021) returns the set of solutions rather than outputting them
check_sequence(a,b,t,u,yLB,yUB)={
	my(c0,c1,d,k,sqrSet,yNegCurr,yNegPrev,yPosCurr,yPosPrev,yTemp);

	sqrSet=Set(1); \\ 1 because we have the solution (a,1)

	d=a*a+b;
	\\ the recurrence coefficients when using e=(t+u*sqrt(d))/2
	c1=(t*t+d*u*u)/2;
	c0=-1;

	\\k negative
	yNegPrev=1;
	yNegCurr=((t-a*u)*(t-a*u)+b*u*u)/4;
	k=1;
	while(yNegCurr<=yUB && k<10,
		\\if(yNegCurr>yLB && issquare(yNegCurr) && denominator(yNegCurr)==1,
		if(issquare(yNegCurr) && denominator(yNegCurr)==1,
			sqrSet=setunion(sqrSet,Set(yNegCurr));
			\\printf("a=%5d, b=%8d, k=-%1d: y_k=%9d^2, d=%7d, t=%8d, u=%8d\n",a,b,k,sqrtint(yNegCurr),d,t,u);
		);
		yTemp=c1*yNegCurr+c0*yNegPrev;
		yNegPrev=yNegCurr;
		yNegCurr=yTemp;
		k=k+1;
	);

	\\k positive
	yPosPrev=1;
	yPosCurr=((t+a*u)*(t+a*u)+b*u*u)/4;
	k=1;
	while(yPosCurr<=yUB && k<10,
		\\if(yPosCurr>yLB && issquare(yPosCurr) && denominator(yPosCurr)==1,
		if(issquare(yPosCurr) && denominator(yPosCurr)==1,
			sqrSet=setunion(sqrSet,Set(yPosCurr));
			\\printf("a=%5d, b=%8d, k= %1d: y_k=%9d^2, d=%7d, t=%8d, u=%8d\n",a,b,k,sqrtint(yPosCurr),d,t,u);
		);
		yTemp=c1*yPosCurr+c0*yPosPrev;
		yPosPrev=yPosCurr;
		yPosCurr=yTemp;
		k=k+1;
	);
	return(sqrSet);
	\\if(length(sqrSet)>1,
	\\	printf("\nFOUND SOLN=%1d, a=%5d, b=%8d=%s, d=%8d, t=%6d, u=%6d\n",length(sqrSet),a,b,factor(b),d,t,u);
	\\	output_solns(a,b,t,u);
	\\);
}

\\ used in the end-of-proof-sequence-check scripts
output_solns(a,b,t,u)={
	my(d,k,yNegPrev,yNegCurr,yPosPrev,yPosCurryTemp);
	
	d=a*a+b;
	\\ the recurrence coefficients when using e=(t+u*sqrt(d))/2
	c1=(t*t+d*u*u)/2;
	c0=-1;

	\\k negative
	yNegPrev=1;
	yNegCurr=((t-a*u)*(t-a*u)+b*u*u)/4;
	k=1;
	while(k<10,
		\\if(k=3 && a==1 && b==7,print("yNegCurr=",yNegCurr));
		if(issquare(yNegCurr) && denominator(yNegCurr)==1,
			printf("a=%5d, b=%8d, k=-%1d: y_k=%9d^2, d=%7d, t=%8d, u=%8d\n",a,b,k,sqrtint(yNegCurr),d,t,u);
		);
		yTemp=c1*yNegCurr+c0*yNegPrev;
		yNegPrev=yNegCurr;
		yNegCurr=yTemp;
		k=k+1;
	);

	\\k positive
	yPosPrev=1;
	yPosCurr=((t+a*u)*(t+a*u)+b*u*u)/4;
	k=1;
	while(k<10,
		if(issquare(yPosCurr) && denominator(yPosCurr)==1,
			printf("a=%5d, b=%8d, k= %1d: y_k=%9d^2, d=%7d, t=%8d, u=%8d\n",a,b,k,sqrtint(yPosCurr),d,t,u);
		);
		yTemp=c1*yPosCurr+c0*yPosPrev;
		yPosPrev=yPosCurr;
		yPosCurr=yTemp;
		k=k+1;
	);
}

\\ 9 April 2020
\\ copied (bad!) from my-ell-utils.gp (in prim-div\general\pari)
get_val(v,p)={
	my(v1,vDen,vDenP,vNum,vNumP);

	if(type(v)!="t_INT" && type(v)!="t_FRAC",
		print("ERROR in get_val(): v=",v,", must be an integer or a rational number");
		1/0;
	);
	if(p<2,
		print("ERROR in get_val(): p=",p,", must be a positive integer that is prime");
		1/0;
	);
	if(!isprime(p),
		print("ERROR in get_val(): p=",p,", must be a positive integer that is prime");
		1/0;
	);
	if(v==0,return(10000));
	vNum=numerator(v);
	vNumP=1;
	c=0;
	while(vNum%p==0,
		vNum=vNum/p;
		vNumP=vNumP*p;
		c=c+1;
		\\print("p=",p,", vNum=",vNum);
		\\if(c>10,1/0);
	);
	
	vDen=denominator(v);
	vDenP=1;
	while(vDen%p==0,
		vDen=vDen/p;
		vDenP=vDenP*p;
	);
	v1=vNumP/vDenP;
	if(v1==1,return(0));
	return(factor(v1)[1,2]);
}

\\ 13 March 2023
get_radical(n)={
	my(fSize,nFact,nRad);
	
	nFact=factor(abs(n));
	fSize=matsize(nFact)[1];
	nRad=1;
	for(i=1,fSize,
		p=nFact[i,1];
		nRad=p*nRad;
	);
	return(nRad);
}

\\ 1 May 2023
get_largest_prime_factor(n)={
	my(fSize,nFact,pN);
	
	nFact=factor(abs(n));
	fSize=matsize(nFact)[1];
	pN=1;
	for(i=1,fSize,
		pN=nFact[i,1];
	);
	return(pN);
}

\\ given a, b, t, u so that e=(t+u*sqrt(d))/2 is a unit (necessary?)
\\ find integer squares among the first 20 (or whatever the upper bound in i for-loop) elements of the sequence formed from
\\ y_{n+1}=c1*y_n-c0*y_{n-1}, so y_{n-1}=(c1*y_n-y_{n+1})/c0
\\ the args d,a,b,t,u are only for logging. Here alpha=a+b*sqrt(d)
\\
\\ returns an array of three elements:
\\ 1) the indices of the squares found
\\ 2) the distinct square roots of the squares found
\\ 3) the minimum value of y_k and y_{-k} for the largest index k calculated
\\ 24 Jan 2020
make_sequences(c0,c1,yM1,y0,yP1,d,a,b,t,u,dbg=0)={
	my(iLB,indices,nrmA,solns,yNegCurr,yNegPrev,yPosCurr,yPosPrev,yT);
	
	\\ iLB=40 for d=5
	\\ iLB=13 for d=13
	\\ iLB=23 for d=2
	iLB=11; \\ had iLB=13, but no squares for d>13
	indices=Set();
	solns=Set();
	if(c0*c1!=0 && denominator(c0)==1 && denominator(c1)==1 && gcd(c0,c1)==1 && polisirreducible(x^2-c1*x+c0) && t*u!=0,
		solns=Set();
		if(issquare(y0) && denominator(y0)==1,
			indices=Set([0]);
			solns=Set([sqrtint(y0)]);
		);

		\\ yP for the previous element
		\\ we have yPa and yPb. yPa is for the sequence y_k with k \geq 0
		\\ yPb is for the sequence y_k with k \leq 0
		yPosPrev=y0;
		yNegPrev=y0;

		yPosCurr=yP1;
		yNegCurr=yM1;
		for(i=1,80,
			if(dbg!=0,print(i,": yPosCurr=",yPosCurr));
			if(yPosCurr>0 && denominator(yPosCurr)==1 && issquare(yPosCurr),
				if(dbg!=0,print("SQR ",i,": yPosCurr=",yPosCurr));
				indices=setunion(indices,Set([i]));
				solns=setunion(solns,Set([sqrtint(yPosCurr)]));
				if(i>iLB, \\ && length(solns)>3,
					nrmA=a*a-d*b*b;
					printf("BIG: added i:=%3d: yPosCurr:=%21d: for d:=%3d: a:=%8d: b:=%7d: t:=%5d: u:=%3d: nrmA:=%12d: solns:=%s:\n",i,yPosCurr,d,a,b,t,u,nrmA,solns);
				);
				if(dbg!=0,print(i,": added yPosCurr=",yPosCurr," to indices=",indices," and solns=",solns));
			);
			yT=c1*yPosCurr-c0*yPosPrev;
			yPosPrev=yPosCurr;
			yPosCurr=yT;

			if(dbg!=0,print(i,": yNegCurr=",yNegCurr));
			\\if(a==5 && b==8 && d==2,print("i=",i,", yNegCurr=",yNegCurr));
			if(yNegCurr>0 && denominator(yNegCurr)==1 && issquare(yNegCurr),
				if(dbg!=0,print("SQR ",-i,": yNegCurr=",yNegCurr));
				indices=setunion(indices,Set([-i]));
				solns=setunion(solns,Set([sqrtint(yNegCurr)]));
				if(i>iLB, \\ && length(solns)>3,
					nrmA=a*a-d*b*b;
					printf("BIG: added i:=%3d: yNegCurr:=%21d: for d:=%3d: a:=%8d: b:=%7d: t:=%5d: u:=%3d: nrmA:=%12d: solns:=%s:\n",-i,yNegCurr,d,a,b,t,u,nrmA,solns);
				);
				if(dbg!=0,print(-i,": added yNegCurr=",yNegCurr," to indices=",indices," and solns=",solns));
			);

			\\ need to solve c1*yNegCurr-c0*yT=yNegPrev
			yT=(c1*yNegCurr-yNegPrev)/c0; \\ y_{n-1}=(c1*y_n-y_{n+1})/c0
			yNegPrev=yNegCurr;
			yNegCurr=yT;
		);
	);
	return([indices,solns,min(yNegPrev,yPosPrev)]);
}

\\ ONLY WORKS WHEN sequence is generated by e^(2k), where e=(t+u*sqrt(d))/2 is a unit
\\ NOT when the sequence is generated by e^k
\\ this looks like the old notation where nrmA=-b and d=a^2+b
\\ also d1=sqrt(y0) (we assume y0 is a sqr)
\\ for helping with other functions
\\ 24 Jan 2020
output_squares(a,b,c0,c1,yM1,y0,yP1,t,u)={
	my(yNegCurr,yNegPrev,yPosCurr,yPosPrev,yT);

	yPosPrev=y0;
	yNegPrev=y0;

	yPosCurr=yP1;
	yNegCurr=yM1;

	printf("    %3d: y_i=%6d\n",0,y0);
	for(i=1,12,
		if(yPosCurr>0 && denominator(yPosCurr)==1 && issquare(yPosCurr),
			printf("    %3d: y_i=%6d\n",i,yPosCurr);
		);
		yT=c1*yPosCurr-c0*yPosPrev;
		yPosPrev=yPosCurr;
		yPosCurr=yT;

		if(yNegCurr>0 && denominator(yNegCurr)==1 && issquare(yNegCurr),
			if(dbg!=0,printf("    %3d: y_i=%6d\n",-i,yNegCurr));
		);

		\\ need to solve c1*yNegCurr-c0*yT=yNegPrev
		yT=(c1*yNegCurr-yNegPrev)/c0; \\ y_{n-1}=(c1*y_n-y_{n+1})/c0
		\\yT=c1*yNegCurr-c0*yNegPrev;
		yNegPrev=yNegCurr;
		yNegCurr=yT;
	);
}

\\ 10 Sept 2023
output_magma_procedure()={
	print("CheckEqn := procedure(d,nrmA)");
	print("s:=IntegralQuarticPoints([d, 0, 0, 0, nrmA]);");
	print("if (#s eq 4) then");
	print("printf \"**d=%7o, nrmA=%5o, number=%o, solns=%o, %o\\n\",d, nrmA, #s, s[1], s[3];");
	print("end if;");
	print("if (#s eq 6) then");
	print("printf \"**d=%7o, nrmA=%5o, number=%o, solns=%o, %o, %o\\n\",d, nrmA, #s, s[1], s[3], s[5];");
	print("end if;");
	print("if (#s gt 6) then");
	print("printf \"**d=%7o, nrmA=%5o, number=%o, solns=%o, %o, %o, %o\\n\",d, nrmA, #s, s[1], s[3], s[5], s[7];");
	print("end if;");
	print("end procedure;");
}

\\ 10 Sept 2023
do_magma_output(d,nrmA)={
	printf("d:=%7d;nrmA:=%4d;\n",d,nrmA);
	print("CheckEqn(d,nrmA);");
}