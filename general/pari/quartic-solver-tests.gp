\\ Focused regression tests and bounded exhaustive comparisons.
\\ run_tests() retains the original large ranges.
\\ run_tests(0,30,50,100): focused suite plus 1,250 bounded comparisons.
\\ run_tests(0,1,0,100): focused suite only.

\\ Separate deliberate-fault tests (PowerShell 7, temporary copies only):
\\ pwsh -File quartic_thue_mutation_tests.ps1 -GpPath C:/path/to/gp.exe
read("quartic-solver.gp");

qt_test_assert(ok,label)={
	if (!ok,error("quartic_thue test failure: ",label));
};

qt_test_throws(action,label)={
	my(caught=0);
	iferr(action(),e,caught=1);
	qt_test_assert(caught,Str("expected an error: ",label));
};

qt_test_state()={
	return([QT_CERTIFY_CLASSGROUP,QT_CERTIFY_THUE,QT_LOCAL_SIEVE,
		QT_LOCAL_MODULI,QT_LOCAL_PRIME_BOUND,QT_FAST_UNIT_RHS,
		getrand(),default(nbthreads)]);
};

qt_test_restore(state)={
	QT_CERTIFY_CLASSGROUP=state[1];
	QT_CERTIFY_THUE=state[2];
	QT_LOCAL_SIEVE=state[3];
	QT_LOCAL_MODULI=state[4];
	QT_LOCAL_PRIME_BOUND=state[5];
	QT_FAST_UNIT_RHS=state[6];
	setrand(state[7]);
	default(nbthreads,state[8]);
};

\\ Explicit restoration is essential: kill() can defeat local() restoration.
\\ Assigning an unset name its saved formal polynomial restores its GP value.
qt_test_isolated(action)={
	my(saved=qt_test_state(),result);
	QT_CERTIFY_CLASSGROUP=1;QT_CERTIFY_THUE=1;
	QT_LOCAL_SIEVE=1;QT_LOCAL_MODULI=[4,8,16,9];
	QT_LOCAL_PRIME_BOUND=199;QT_FAST_UNIT_RHS=1;
	iferr(result=action(),e,
		qt_test_restore(saved);
		error(e);
	);
	qt_test_restore(saved);
	return(result);
};

qt_test_descent_with_sieve(d,n,sieve,dbg=0)={
	local(QT_LOCAL_SIEVE=sieve);
	return(quartic_to_thue(d,n,dbg));
};

qt_test_brute(d,n,B)={
	my(L=List(),x,x2);
	for (y=0,B,
		x2=d*y^4+n;
		if (x2>=0 && issquare(x2,&x),
			listput(L,[x,y]);listput(L,[-x,y]);
			listput(L,[x,-y]);listput(L,[-x,-y]);
		);
	);
	return(Set(Vec(L)));
};

qt_test_signs(points)={
	my(L=List());
	for (i=1,#points,
		forstep (sx=-1,1,2,forstep (sy=-1,1,2,
			listput(L,[sx*points[i][1],sy*points[i][2]]);
		));
	);
	return(Set(Vec(L)));
};

\\ Verify every output point, even beyond the brute-force bound.
qt_test_solution_set(d,n,S,B)={
	my(z,expected);
	qt_test_assert(type(S)=="t_VEC","solution list must be a vector");
	for (i=1,#S,
		z=S[i];
		qt_test_assert(type(z)=="t_VEC" && #z==2,"solution pair shape");
		qt_test_assert(type(z[1])=="t_INT" && type(z[2])=="t_INT","integer coordinates");
		qt_test_assert(z[1]^2-d*z[2]^4==n,Str("invalid point: ",[d,n,z]));
	);
	qt_test_assert(#S==#Set(S),Str("duplicate points: ",[d,n]));
	qt_test_assert(Set(S)==qt_test_signs(S),Str("missing sign symmetry: ",[d,n]));
	expected=qt_test_brute(d,n,B);
	qt_test_assert(Set(select(z->abs(z[2])<=B,S))==expected,
		Str("bounded exhaustive comparison: ",[d,n,B]));
};

qt_test_normalisation()={
	my(R,A,S,T,N,pairs=[[2,-1],[3,-2],[7,-3],[12,-6]],scales=[1,2,3,6,30]);
	qt_test_assert(qt_square_normalise(352832,-1252096)==[5513,-19564,8],"normalisation example");
	qt_test_assert(qt_square_normalise(1800,-900)==[2,-1,30],"composite scale");
	qt_test_assert(qt_square_normalise(12,-6)==[12,-6,1],"squarefree common divisor");
	for (i=1,#pairs,
		T=quartic_thue_solve(pairs[i][1],pairs[i][2]);
		for (j=1,#scales,
			N=scales[j]^2*pairs[i];
			S=quartic_thue_solve(N[1],N[2]);
			qt_test_assert(S==Set(vector(#T,k,[scales[j]*T[k][1],T[k][2]])),
				Str("scaling bijection: ",[pairs[i],scales[j]]));
			qt_test_solution_set(N[1],N[2],S,100);
		);
	);
	setrand(12345);R=quartic_to_thue(352832,-1252096);
	setrand(12345);A=quartic_to_thue(5513,-19564);
	qt_test_assert(R[1][1..2]==[352832,-1252096] && R[1][10..12]==[8,5513,-19564],"normalisation metadata");
	qt_test_assert(R[2]==A[2] && R[3]==A[3],"same descent at the same random seed");
	S=quartic_thue_solve_from(R);T=quartic_thue_solve_from(A);
	qt_test_assert(S==Set(vector(#T,k,[8*T[k][1],T[k][2]])),"large-example recovery scaling");
	qt_test_assert(S==qt_test_signs([[2096,2],[17428018086352,171290]]),"large-example signed solutions");
	qt_test_solution_set(352832,-1252096,S,100);
	print("PASS: common-square normalisation");
};

qt_test_group_elements(cyc)={
	my(L=List(),v,z);
	for (k=0,prod(i=1,#cyc,cyc[i])-1,
		z=k;v=vector(#cyc);
		for (i=1,#cyc,v[i]=z%cyc[i];z=z\cyc[i]);
		listput(L,v);
	);
	return(Vec(L));
};

qt_test_class_roots()={
	my(groups=[[],[1],[2],[3],[4],[5],[8],[12],[4,2],[8,4],[3,3],[4,2,2]]);
	my(cyc,elts,a,expected,actual,count=0);
	for (g=1,#groups,
		cyc=groups[g];elts=qt_test_group_elements(cyc);
		for (j=1,#elts,
			a=elts[j];expected=List();
			for (k=1,#elts,
				if (sum(i=1,#cyc,(a[i]+4*elts[k][i])%cyc[i])==0,
					listput(expected,elts[k]);
				);
			);
			actual=qt_fourth_class_roots(cyc,a);
			qt_test_assert(#actual==#Set(actual) && Set(actual)==Set(Vec(expected)),
				Str("class-root enumeration: ",[cyc,a]));
			count++;
		);
	);
	print("PASS: class-root enumeration (",count," cases)");
};

qt_test_eval(P,u,v)={
	return(sum(k=0,4,polcoef(P,k)*u^k*v^(4-k)));
};

qt_test_basis_matrix(bp)={
	return([bp[1][1],bp[2][1];bp[1][2],bp[2][2]]);
};

qt_test_imag_form(q,kappa,bp)={
	my(a=bp[1][1]*qtU+bp[2][1]*qtV,b=bp[1][2]*qtU+bp[2][2]*qtV);
	return(kappa[2]*(a^4-6*q*a^2*b^2+q^2*b^4)+4*kappa[1]*a*b*(a^2-q*b^2));
};

qt_test_transformations()={
	local(QT_LOCAL_SIEVE=0);
	my(forms=[qtU^4+2*qtU^3-7*qtU^2+3*qtU-11,-3*qtU^4+qtU^3-qtU+2,qtU^4-2]);
	my(mats=[[0,1;1,0],[-1,0;0,1],[1,17;0,1],[1,0;-13,1],[2,1;1,1]]);
	my(bases=[[[1,0],[0,1]],[[1,0],[1/2,1/2]],[[3/2,1/2],[-1/3,2/3]]]);
	my(P,Q,M,z,red,bp,newbp,B,U,F,kappa,sfield,caseR,eqsol);
	for (i=1,#forms,
		P=forms[i];
		for (j=1,#mats,
			M=mats[j];Q=qt_pol_transform(P,M);
			for (u=-2,2,for (v=-2,2,
				z=M*[u,v]~;
				qt_test_assert(qt_test_eval(Q,u,v)==qt_test_eval(P,z[1],z[2]),"GL2 substitution");
			));
			red=qt_reduce_pol(Q,-7);
			qt_test_assert(abs(matdet(red[3]))==1,"unimodular reduction");
			qt_test_assert(qt_pol_transform(Q,red[3])*red[2]==-7*red[1],"reduction identity and RHS sign");
			qt_test_assert(qt_solver_height(red[1])<=qt_solver_height(Q),"nonincreasing reduction height");
		);
	);
	for (i=1,#bases,
		bp=bases[i];B=qt_test_basis_matrix(bp);
		for (j=1,#mats,
			newbp=qt_basis_transform(bp,mats[j]);
			qt_test_assert(qt_test_basis_matrix(newbp)==B*mats[j],"lattice basis transformation");
		);
		for (q=1,7,
			newbp=qt_lll_basis(q,bp);
			U=B^-1*qt_test_basis_matrix(newbp);
			qt_test_assert(denominator(U,1)==1 && abs(matdet(U))==1,"LLL preserves the fractional lattice");
		);
	);
	\\ Purely real kappa makes the original U^4 coefficient vanish.
	bp=[[1,0],[0,1]];
	kappa=[1,0];
	F=qt_make_form(1,kappa,bp,24);
	qt_test_assert(#F==5 && poldegree(F[1])==4,"initial change of variables restores degree four");
	qt_test_assert(24*F[3]==F[2]*qt_test_imag_form(1,kappa,F[5]),"initial change of variables and reconstructed lattice identity");
	\\ (2+i)^4=-7+24i: check its coordinates in the transformed lattice.
	z=qt_test_basis_matrix(F[5])^-1*[2,1]~;
	qt_test_assert(denominator(z,1)==1 &&
		setsearch(Set(thue(thueinit(F[1],1),F[2])),Vec(z)),
		"known solution survives the initial change of variables");
	bp=[[1,0],[1/2,1/2]];kappa=[1,1];sfield=7;
	F=qt_make_form(3,kappa,bp,sfield);
	qt_test_assert(#F==5 && content(F[1],1)==1,"half-integral form construction");
	qt_test_assert(sfield*F[3]==F[2]*qt_test_imag_form(3,kappa,F[5]),"fractional basis and RHS identity");
	\\ Axis coordinates and duplicate parametrisations must recover correctly.
	P=qtU^4+4*qtU^3-6*qtU^2-4*qtU+1;
	caseR=[[2,-1,1,1,1,-4,[],0,1,1,2,-1],
		[[P,1,qt_test_eval(P,qtU,qtV)]],
		[[1,[],0,[],0,[1,1],[[1,0],[0,1]],0]]];
	eqsol=[[[1,0],[-1,0],[0,1],[0,-1]]];
	qt_test_assert(qt_recover(caseR,eqsol)==[[1,-1],[1,1]],"axis solutions and recovery deduplication");
	print("PASS: form identities, lattice bases, unimodular changes, and recovery");
};

qt_test_filters()={
	my(P,rhs,count=0,R,S,T);
	local(QT_LOCAL_SIEVE=0);
	qt_test_assert(qt_make_form(1,[1,0],[[1,0],[0,1]],1)==[],"content obstruction without sieving");
	R=qt_make_form(1,[1,0],[[1,0],[0,1]],24);
	qt_test_assert(#R==5 && content(R[1],1)==1 && abs(R[2])==6,"content division preserves RHS");
	P=qtU^4+1;
	qt_test_assert(qt_has_solution_mod(P,3,2) && !qt_has_solution_mod(P,3,4),"modulo 4 obstruction");
	qt_test_assert(qt_has_solution_mod(P,4,4) && !qt_has_solution_mod(P,4,8),"modulo 8 obstruction");
	qt_test_assert(qt_has_solution_mod(P,3,3) && !qt_has_solution_mod(P,3,9),"modulo 9 obstruction");
	setrand(4567);
	for (j=1,20,
		P=sum(k=0,4,(random(41)-20)*qtU^k);
		forprime (p=2,31,
			for (r=1,4,
				rhs=[0,p,-p,random(61)-30][r];
				qt_test_assert(qt_has_solution_mod_prime(P,rhs,p)==qt_has_solution_mod(P,rhs,p),"projective vs affine residue search");
				count++;
			);
			qt_test_assert(qt_has_solution_mod_prime(p*qtU^4+qtU+1,1,p)==
				qt_has_solution_mod(p*qtU^4+qtU+1,1,p),"leading coefficient divisible by p");
		);
	);
	for (d=2,7,for (n=-7,-1,for (m=2,16,
		rhs=0;
		for (u=0,m-1,for (v=0,m-1,if ((u^2-d*v^4-n)%m==0,rhs=1)));
		qt_test_assert(qt_original_has_solution_mod(d,n,m)==rhs,"original-equation modular preflight");
	)));
	for (d=2,12,
		if (!issquare(d),
			for (n=-10,-1,
				QT_LOCAL_SIEVE=1;S=quartic_thue_solve(d,n);
				QT_LOCAL_SIEVE=0;T=quartic_thue_solve(d,n);
				qt_test_assert(S==T,Str("sieved vs unsieved: ",[d,n]));
			);
		);
	);
	print("PASS: content, prime powers, ",count," prime checks, and 80 sieve comparisons");
};

qt_test_regressions()={
	my(S,R,A,H);
	S=quartic_thue_solve(2,-1);
	qt_test_assert(S==qt_test_signs([[1,1],[239,13]]),"complete (2,-1) regression");
	R=qt_test_descent_with_sieve(15,-14,0);
	qt_test_assert(#R[2]==8,"eight unsieved (15,-14) equations");
	H=vector(#R[2],i,qt_pol_height(R[2][i][1]));
	qt_test_assert(vecmax(H)<=165,"(15,-14) coefficient height");
	S=quartic_thue_solve_from(R);
	qt_test_assert(S==qt_test_signs([[1,1]]),"(15,-14) solutions");
	A=qt_test_descent_with_sieve(15,-14,1);
	qt_test_assert(#A[2]==1 && quartic_thue_solve_from(A)==S,"(15,-14) sieved result");
	R=quartic_to_thue(580,-3041536);
	qt_test_assert(#R[2]==1 && #R[3]==2,"580 equation/case counts");
	S=quartic_thue_solve_from(R);
	qt_test_assert(S==qt_test_signs([[6738,17],[37090062,1241]]),"580 signed solutions");
	qt_test_solution_set(580,-3041536,S,1500);
	\\ Regenerate the old overflow case rather than reuse its enormous old form.
	R=quartic_to_thue(2,-983);
	qt_test_assert(#R[2]>0,"983 must exercise Thue solving");
	H=vector(#R[2],i,qt_pol_height(R[2][i][1]));
	qt_test_assert(vecmax(H)<=10000,"983 coefficient-growth regression");
	S=quartic_thue_solve_from(R);
	qt_test_assert(S==[],"983 no-solution regression");
	qt_test_solution_set(2,-983,S,10000);
	print("PASS: historical regressions, including (2,-983)");
};

qt_test_arithmetic()={
	my(nf,pr,R,S,half=0,units,qs=[1,3],examples=[[2,-1],[7,-3],[11,-7],[3,-2],[2,-2],[2,-3]]);
	nf=nfinit(qtZ^2+7);
	pr=idealprimedec(nf,2);
	qt_test_assert(#pr==2,"2 splits in Q(sqrt(-7))");
	qt_test_assert(Set(qt_local_options(pr,1,0))==Set([[0,1],[1,0]]),"good split prime");
	qt_test_assert(Set(qt_local_options(pr,1,1))==Set([[0,1],[1,0],[2,3],[3,2]]),"bad split prime");
	pr=idealprimedec(nf,3);
	qt_test_assert(#pr==1 && pr[1].f==2,"inert prime");
	qt_test_assert(qt_local_options(pr,1,1)==[],"inert odd valuation impossible");
	qt_test_assert(qt_local_options(pr,2,0)==[],"inert good-prime obstruction");
	qt_test_assert(qt_local_options(pr,0,0)==[[0]],"inert good-prime zero residue");
	qt_test_assert(Set(qt_local_options(pr,2,1))==Set([[1],[3]]),"inert bad-prime options");
	pr=idealprimedec(nf,7);
	qt_test_assert(pr[1].e==2,"ramified prime");
	for (v=0,7,qt_test_assert(qt_local_options(pr,v,1)==[[v%4]],"ramified residues"));
	for (i=1,#qs,
		R=qt_test_descent_with_sieve(examples[i][1],examples[i][2],0);
		units=Set(vector(#R[3],j,R[3][j][5]));
		qt_test_assert(#units==[4,6][i],"exceptional quadratic units");
		for (j=1,#R[3],if (denominator(R[3][j][7],1)>1,half=1));
	);
	qt_test_assert(half,"an actual descent exercises a fractional basis");
	for (i=1,#examples,
		R=quartic_to_thue(examples[i][1],examples[i][2]);
		S=quartic_thue_solve_from(R);
		qt_test_solution_set(examples[i][1],examples[i][2],S,200);
	);
	qt_test_assert(quartic_thue_solve(2,-2)==[[0,-1],[0,1]],"zero x and sign deduplication");
	qt_test_assert(quartic_thue_solve(2,-3)==[],"empty solution set");
	print("PASS: units, fractional bases, split/inert/ramified primes, and boundary cases");
};

qt_test_certification_and_errors()={
	my(R,A,S,P,E,H,blocks,expected,invalid=[[1,-1],[4,-1],[2,0],[2,1],[3/2,-1],[2,-1/2],["2",-1]]);
	kill(QT_CERTIFY_CLASSGROUP);kill(QT_CERTIFY_THUE);
	S=quartic_thue_solve(2,-2);
	qt_test_assert(S==[[0,-1],[0,1]],"unset certification flags");
	QT_CERTIFY_CLASSGROUP=1;QT_CERTIFY_THUE=1;
	R=quartic_to_thue(2,-1);S=quartic_thue_solve_from(R);
	qt_test_assert(qt_thue_group_flag(R[2],[1],1)==0,"unconditional unit-RHS shortcut");
	QT_FAST_UNIT_RHS=0;
	qt_test_assert(qt_thue_group_flag(R[2],[1],1)==1,"force certification");
	qt_test_assert(quartic_thue_solve_from(R)==S,"forced certification preserves solutions");
	kill(QT_FAST_UNIT_RHS);
	qt_test_assert(qt_thue_group_flag(R[2],[1],1)==0,"unset fast-unit flag");
	QT_FAST_UNIT_RHS=1;
	P=qtU^4-2;H=qt_test_eval(P,qtU,qtV);
	E=vector(3,i,[P,[-1,1,2][i],H]);
	for (order=1,2,
		for (i=1,#E,
			qt_test_assert(qt_thue_group_flag(E,[i],1)==1,"mixed RHS cache must certify every order");
			qt_test_assert(qt_thue_group_flag(E,[i],0)==0,"explicit conditional mode");
		);
		blocks=qt_solve_thue_task([E,[1,2,3],1]);
		expected=vector(3,i,[i,thue(thueinit(P,1),E[i][2])]);
		qt_test_assert(blocks==expected,"grouped shared-polynomial solve");
		E=Vecrev(E);
	);
	A=R;A[1]=R[1][1..9];
	qt_test_assert(quartic_thue_solve_from(A)==S,"legacy nine-entry metadata");
	qt_test_throws(()->qt_recover(R,[]),"missing equations");
	qt_test_throws(()->qt_recover(R,vector(#R[2])),"zero placeholders");
	qt_test_throws(()->qt_recover(R,[[[1/2,1]]]),"noninteger pair");
	qt_test_throws(()->qt_recover(R,[[[1]]]),"malformed pair");
	A=R;A[2][1][2]=1/2;
	qt_test_throws(()->quartic_thue_solve_from(A),"sequential Thue failure must propagate");
	qt_test_throws(()->quartic_thue_solve_parallel_from(A),"parallel Thue failure must propagate");
	for (i=1,#invalid,
		qt_test_throws(()->quartic_to_thue(invalid[i][1],invalid[i][2]),Str("invalid input ",invalid[i]));
	);
	qt_test_throws(()->qt_binary_flag(2,1,"test"),"nonbinary flag");
	qt_test_throws(()->qt_binary_flag("1",1,"test"),"string flag");
	qt_test_throws(()->qt_nonnegative_integer_setting(-1,199,"test"),"negative prime bound");
	qt_test_throws(()->qt_nonnegative_integer_setting(1/2,199,"test"),"fractional prime bound");
	qt_test_throws(()->qt_moduli_setting([4,0]),"zero modulus");
	qt_test_throws(()->qt_moduli_setting([4,3/2]),"fractional modulus");
	qt_test_assert(qt_moduli_setting([])==[],"empty modulus list is allowed");
	print("PASS: certification selection, grouped solving, invalid data, and failure propagation");
};

qt_test_parallel_and_seeds()={
	my(R,S,T,examples=[[2,-1],[15,-14],[2,-92],[352832,-1252096],[2,-983]]);
	default(nbthreads,2);
	R=quartic_to_thue(2,-92);
	qt_test_assert(#R[2]>1,"parallel regression has multiple equations");
	qt_test_assert(quartic_thue_solve_from(R)==quartic_thue_solve_parallel_from(R),"two-worker grouped solve");
	R=quartic_to_thue(352832,-1252096);
	qt_test_assert(#Set(vector(#R[2],j,R[2][j][1]))>1,"parallel regression has multiple worker tasks");
	qt_test_assert(quartic_thue_solve_from(R)==quartic_thue_solve_parallel_from(R),"multiple parallel polynomial groups");
	qt_test_assert(quartic_thue_solve(8,-4)==quartic_thue_solve_parallel(8,-4),"parallel square normalisation");
	qt_test_assert(quartic_thue_solve_parallel(2,-3)==[],"parallel empty solution set");
	R=quartic_to_thue(2,-3);
	qt_test_assert(#R[2]==0 && quartic_thue_solve_from(R)==[] &&
		quartic_thue_solve_parallel_from(R)==[],"empty generated equation list");
	for (i=1,#examples,
		setrand(1);S=quartic_thue_solve(examples[i][1],examples[i][2]);
		for (seed=2,4,
			setrand(seed);T=quartic_thue_solve(examples[i][1],examples[i][2]);
			qt_test_assert(S==T,Str("random-seed independence: ",[examples[i],seed]));
		);
	);
	print("PASS: two-worker parallel solving and four random seeds");
};

qt_test_mutate_settings(fail)={
	kill(QT_CERTIFY_CLASSGROUP);kill(QT_CERTIFY_THUE);kill(QT_FAST_UNIT_RHS);
	QT_LOCAL_SIEVE=0;QT_LOCAL_MODULI=[25];QT_LOCAL_PRIME_BOUND=7;
	setrand(98765);random(100);default(nbthreads,2);
	if (fail,error("intentional test-isolation failure"));
	return(123);
};

qt_test_isolation()={
	my(saved=qt_test_state());
	qt_test_assert(qt_test_isolated(()->qt_test_mutate_settings(0))==123,"isolated action result");
	qt_test_assert(qt_test_state()==saved,"restore settings after success and kill()");
	qt_test_throws(()->qt_test_isolated(()->qt_test_mutate_settings(1)),"isolated failure");
	qt_test_assert(qt_test_state()==saved,"restore settings after failure and kill()");
	kill(QT_FAST_UNIT_RHS);saved=qt_test_state();
	qt_test_isolated(()->qt_test_mutate_settings(0));
	qt_test_assert(qt_test_state()==saved,"restore an initially unset setting");
	QT_FAST_UNIT_RHS=1;
	print("PASS: settings, RNG, and worker restoration on success and failure");
};

\\ Audit each returned case using quadratic-field arithmetic, not qt_pair*,
\\ qt_test_imag_form, or the explicit quartic expansion in qt_make_form.
qt_test_audit_descent(R)={
	my(meta=R[1],nf=nfinit(qtZ^2+R[1][4]),ca,b1,b2,kap,B,idealI,C,J,U);
	my(e,G,im,Acheck,loc,pr,p,exponents,used=vector(#R[2]));
	qt_test_assert(meta[1]==meta[10]^2*meta[11] &&
		meta[2]==meta[10]^2*meta[12],"audit: original/reduced coefficients");
	qt_test_assert(meta[3]==-meta[12] && meta[3]==meta[4]*meta[5]^2 &&
		core(meta[4])==meta[4] && nf.disc==meta[6],"audit: quadratic field metadata");
	for (j=1,#R[3],
		ca=R[3][j];e=ca[1];
		qt_test_assert(type(e)=="t_INT" && e>=1 && e<=#R[2],"audit: equation reference");
		used[e]=1;
		b1=Mod(ca[7][1][1]+ca[7][1][2]*qtZ,nf.pol);
		b2=Mod(ca[7][2][1]+ca[7][2][2]*qtZ,nf.pol);
		kap=Mod(ca[6][1]+ca[6][2]*qtZ,nf.pol);
		B=Mat([nfalgtobasis(nf,b1),nfalgtobasis(nf,b2)]);
		qt_test_assert(matdet(B)!=0,"audit: independent lattice basis");
		\\ Form the O_K-ideal generated by the two elements.  Compare its
		\\ integral basis with their Z-span, so mere ideal membership is insufficient.
		idealI=idealadd(nf,idealhnf(nf,b1),idealhnf(nf,b2));
		U=idealI^-1*B;
		qt_test_assert(denominator(U,1)==1 && abs(matdet(U))==1,
			"audit: returned Z-basis spans the fractional ideal");
		C=idealinv(nf,idealI);
		qt_test_assert(denominator(C,1)==1,"audit: inverse lattice ideal is integral");
		J=idealmul(nf,ca[3],idealpow(nf,C,4));
		qt_test_assert(idealhnf(nf,kap)==J,"audit: principal ideal relation");
		qt_test_assert(ispower(idealnorm(nf,ca[3])/meta[11],4),
			"audit: residual ideal norm has the required fourth-power ratio");
		Acheck=idealhnf(nf,1);
		for (k=1,#ca[2],
			loc=ca[2][k];p=loc[1];exponents=loc[2];
			qt_test_assert(isprime(p) && (2*meta[3]*meta[11])%p==0,"audit: residual prime support");
			pr=idealprimedec(nf,p);
			qt_test_assert(#pr==#exponents,"audit: local exponent-vector length");
			for (h=1,#pr,
				qt_test_assert(type(exponents[h])=="t_INT" &&
					exponents[h]>=0 && exponents[h]<4,"audit: fourth-power-free exponents");
				Acheck=idealmul(nf,Acheck,idealpow(nf,pr[h],exponents[h]));
			);
		);
		qt_test_assert(Acheck==ca[3],"audit: residual ideal reconstructed from local data");
		\\ Expand in K and extract the sqrt(-q) coefficient independently.
		G=lift(kap*(b1*qtU+b2*(ca[8]*qtU+qtV))^4);
		im=polcoef(G,1,qtZ);
		qt_test_assert(R[2][e][2]*im==meta[5]*R[2][e][3],
			"audit: independent binary-form identity");
		qt_test_assert(R[2][e][3]==sum(k=0,4,polcoef(R[2][e][1],k)*qtU^k*qtV^(4-k)),
			"audit: polynomial and binary form agree");
		qt_test_assert(content(R[2][e][1],1)==1 && type(R[2][e][2])=="t_INT" &&
			R[2][e][2]!=0,"audit: primitive integral equation");
	);
	qt_test_assert(sum(i=1,#used,used[i])==#R[2],"audit: every equation has a descent case");
	return(#R[3]);
};

qt_test_independent_descents()={
	my(examples=[[2,-1],[7,-3],[15,-14],[22,-21],[66,-65],[106,-105],
		[580,-3041536],[352832,-1252096],[2,-983]],R,count=0);
	for (i=1,#examples,
		for (sieve=0,1,
			R=qt_test_descent_with_sieve(examples[i][1],examples[i][2],sieve);
			count+=qt_test_audit_descent(R);
		);
	);
	print("PASS: independent ideal, lattice, and field identities (",count," cases)");
};

qt_test_real_class_groups()={
	my(qs=[21,65,105],expectedCyc=[[2,2],[4,2],[2,2,2]]);
	my(bnf,nf,elts,states,a,roots,bruteRoots,R,S,cyc,multiple=0,rejected=0);
	for (i=1,#qs,
		bnf=bnfinit(qtZ^2+qs[i],1);
		qt_test_assert(bnfcertify(bnf),"certified noncyclic class group");
		nf=bnf.nf;cyc=bnf.cyc;
		qt_test_assert(cyc==expectedCyc[i],"actual noncyclic class-group type");
		elts=qt_test_group_elements(cyc);
		for (kind=1,2,
			\\ q+1 gives the known point (1,1); d=2 supplies impossible classes.
			states=qt_residue_ideals(nf,if(kind==1,qs[i]+1,2),qs[i]);
			qt_test_assert(#states>0,"nonempty residual ideal fixture");
			for (j=1,#states,
				a=Vec(bnfisprincipal(bnf,states[j][1],0));
				bruteRoots=List();
				for (k=1,#elts,
					if (sum(h=1,#cyc,(a[h]+4*elts[k][h])%cyc[h])==0,
						listput(bruteRoots,elts[k]);
					);
				);
				roots=qt_fourth_class_roots(cyc,a);
				qt_test_assert(#roots==#bruteRoots && Set(roots)==Set(Vec(bruteRoots)),
					"actual class roots agree with independent enumeration");
				if (#roots>1,multiple++);
				if (!#roots,rejected++);
			);
		);
		R=qt_test_descent_with_sieve(qs[i]+1,-qs[i],0);
		qt_test_assert(#R[3]>0,"noncyclic descent has surviving cases");
		qt_test_audit_descent(R);
		S=quartic_thue_solve_from(R);
		qt_test_assert(setsearch(S,[1,1]),"noncyclic descent recovers its prescribed point");
		qt_test_solution_set(qs[i]+1,-qs[i],S,100);
		R=qt_test_descent_with_sieve(2,-qs[i],0);
		qt_test_assert(#R[2]==0 && #R[3]==0,"impossible classes produce no descent cases");
	);
	qt_test_assert(multiple>0 && rejected>0,"exercise multiple roots and no-root classes");
	print("PASS: actual noncyclic fields; ",multiple," multiple-root and ",rejected," no-root ideals");
};

\\ Genuine odd-order and mixed-order noncyclic class groups.
qt_test_odd_and_mixed_class_groups()={
	my(fixtures=[[65,-3896,37,3],[3,-3299,128,9],[22,-89751,19,8]]);
	my(qs=[974,3299,89751],ss=[2,1,1],discs=[-3896,-3299,-89751]);
	my(expectedCyc=[[12,3],[9,3],[60,5]],kernelSizes=[4,1,4]);
	my(bnf,cyc,elts,a,roots,bruteRoots,soluble,rejected,R,S,T,d,n,x,y);
	for (i=1,#fixtures,
		[d,n,x,y]=fixtures[i];
		qt_test_assert(x^2-d*y^4==n,"odd/mixed fixture has its prescribed point");
		qt_test_assert(qt_square_normalise(d,n)==[d,n,1],
			"odd/mixed fixture preserves its quadratic field after normalization");
		qt_test_assert(-n==qs[i]*ss[i]^2 && issquarefree(qs[i]),
			"odd/mixed squarefree part and square factor");
		bnf=bnfinit(qtZ^2+qs[i],1);
		qt_test_assert(bnfcertify(bnf),"certified odd/mixed class group");
		cyc=bnf.cyc;
		qt_test_assert(bnf.disc==discs[i] && cyc==expectedCyc[i],
			"actual odd/mixed discriminant and class-group type");
		elts=qt_test_group_elements(cyc);
		qt_test_assert(#elts==bnf.no,"enumeration covers the entire class group");
		soluble=0;rejected=0;
		\\ Independently solve 4*c=-a for EVERY class a, including nonzero odd parts.
		for (j=1,#elts,
			a=elts[j];bruteRoots=List();
			for (k=1,#elts,
				if (sum(h=1,#cyc,(a[h]+4*elts[k][h])%cyc[h])==0,
					listput(bruteRoots,elts[k]);
				);
			);
			roots=qt_fourth_class_roots(cyc,a);
			qt_test_assert(#roots==#bruteRoots && Set(roots)==Set(Vec(bruteRoots)),
				Str("odd/mixed fourth roots agree with enumeration: ",[cyc,a]));
			if (#roots,
				qt_test_assert(#roots==kernelSizes[i],"odd/mixed fourth-root multiplicity");
				soluble++,
				rejected++;
			);
		);
		qt_test_assert(soluble==bnf.no/kernelSizes[i]
			&& rejected==bnf.no-bnf.no/kernelSizes[i],
			"odd/mixed counts of soluble and obstructed classes");
		\\ Audit the unfiltered descent, then compare certified solutions with filtering.
		setrand(20261027+i);
		R=qt_test_descent_with_sieve(d,n,0);
		qt_test_assert(R[1][4..7]==[qs[i],ss[i],discs[i],cyc],
			"odd/mixed descent field metadata");
		qt_test_assert(#R[2]>0 && #R[3]>0,"odd/mixed descent has surviving cases");
		qt_test_audit_descent(R);
		S=quartic_thue_solve_from(R);
		qt_test_assert(setsearch(Set(S),[x,y]),"odd/mixed descent recovers prescribed point");
		qt_test_solution_set(d,n,S,1000);
		setrand(20261027+i);
		R=qt_test_descent_with_sieve(d,n,1);
		qt_test_audit_descent(R);
		T=quartic_thue_solve_from(R);
		qt_test_solution_set(d,n,T,1000);
		qt_test_assert(Set(S)==Set(T),"odd/mixed sieved and unsieved solutions agree");
		print("PASS: n=",n,", class group ",cyc,"; ",soluble,
			" soluble and ",rejected," obstructed classes; certified descent");
	);
};

qt_test_large_valuations()={
	my(es=[3,4,5,7,8,9],qs=[1,3,7],nf,pr,all,expected,actual,ex);
	my(x,y,d,n,S,R,alpha,alphabar,common,r,s,q,p,count=0);
	\\ Norm valuations and coprimality independently determine the residue options.
	for (i=1,#qs,
		nf=nfinit(qtZ^2+qs[i]);
		pr=idealprimedec(nf,2);
		qt_test_assert(if(i==1,pr[1].e==2,if(i==2,pr[1].f==2,#pr==2)),
			"2 is respectively ramified, inert, split");
		for (j=1,#es,
			all=qt_test_group_elements(vector(#pr,k,4));expected=List();
			for (k=1,#all,
				ex=all[k];
				if ((sum(h=1,#pr,pr[h].f*ex[h])-es[j])%4==0,listput(expected,ex));
			);
			actual=qt_local_options(pr,es[j],1);
			qt_test_assert(#actual==#expected && Set(actual)==Set(Vec(expected)),
				"large 2-adic valuation residues");
		);
		\\ Common divisors of both conjugate factors survive normalization:
		\\ x=a*2^(2r), y=2^r, d=a^2+q, n=-q*2^(4r).
		for (r=1,3,
			q=qs[i];s=2^(2*r);x=if(q==1,1,2)*s;
			y=2^r;d=if(q==1,2,4+q);n=-q*s^2;
			qt_test_assert(qt_square_normalise(d,n)[3]==1,"common-ideal fixture is already normalized");
			alpha=x+s*Mod(qtZ,nf.pol);alphabar=x-s*Mod(qtZ,nf.pol);
			common=idealadd(nf,idealhnf(nf,alpha),idealhnf(nf,alphabar));
			for (k=1,#pr,
				qt_test_assert(idealval(nf,common,pr[k])>=2*r*pr[k].e,
					"substantial common conjugate ideal divisor");
			);
			R=quartic_to_thue(d,n);qt_test_audit_descent(R);
			S=quartic_thue_solve_from(R);
			qt_test_assert(setsearch(S,[x,y]),"recover point with high common ideal valuations");
			qt_test_solution_set(d,n,S,50);count++;
		);
	);
	\\ Exercise odd and even valuations on each side of multiples of four.
	for (pi=1,3,
		p=[2,3,5][pi];
		for (j=1,#es,
			d=2;n=-p^es[j];
			qt_test_assert(valuation(-n,p)==es[j] &&
				qt_square_normalise(d,n)[3]==1,"prescribed valuation survives normalization");
			R=quartic_to_thue(d,n);qt_test_audit_descent(R);
			S=quartic_thue_solve_from(R);
			qt_test_solution_set(d,n,S,30);count++;
		);
	);
	print("PASS: large valuations and all three behaviours of 2 (",count," complete solves)");
};

qt_test_prescribed_points()={
	my(triples=[[2,1,1],[7,2,1],[22,1,1],[66,1,1],[3,2,2],
		[2,101^2,101],[7,2*102^2,102],[11,3*103^2,103]],d,x,y,n,R,S);
		
	for (i=1,#triples,
		d=triples[i][1];x=triples[i][2];y=triples[i][3];
		n=x^2-d*y^4;
		qt_test_assert(n<0 && !issquare(d),"valid prescribed-point equation");
		R=quartic_to_thue(d,n);qt_test_audit_descent(R);
		S=quartic_thue_solve_from(R);
		qt_test_assert(#setminus(qt_test_signs([[x,y]]),S)==0,
			Str("prescribed solution lost: ",[d,n,x,y]));
		qt_test_solution_set(d,n,S,30);
	);
	qt_test_assert(triples[6][3]>100 && gcd(triples[7][2],triples[7][3])>1,
		"fixtures include large-y and nonprimitive solutions");
	print("PASS: independently prescribed solutions and all sign variants");
};

qt_test_large_exact_arithmetic()={
	my(s=2^80*3^20,d=2*s^2,n=-s^2,R,S,expected,N=10^30+7);
	my(P=qtU^4+2*qtU^3-7*qtU^2+3*qtU-11,M=[1,N;0,1],Q,red,v,w);
	
	qt_test_assert(s>2^64 && d>2^128,"large-integer fixture");
	qt_test_assert(qt_square_normalise(d,n)==[2,-1,s],"arbitrary-precision normalization");
	R=quartic_to_thue(d,n);qt_test_audit_descent(R);
	S=quartic_thue_solve_from(R);
	expected=qt_test_signs([[s,1],[239*s,13]]);
	qt_test_assert(S==expected,"arbitrary-precision recovery");
	qt_test_solution_set(d,n,S,100);
	Q=qt_pol_transform(P,M);
	qt_test_assert(qt_pol_height(Q)>2^128,"large coefficients created");
	qt_test_assert(qt_pol_transform(Q,M^-1)==P,"exact inverse of large unimodular change");
	red=qt_reduce_pol(Q,7);
	qt_test_assert(abs(matdet(red[3]))==1 &&
		qt_pol_transform(Q,red[3])*red[2]==7*red[1],"large exact reduction identity");
	v=[2,-3]~;w=M^-1*v;
	qt_test_assert(denominator(w,1)==1 && M*w==v &&
		qt_test_eval(Q,w[1],w[2])==qt_test_eval(P,v[1],v[2]),
		"large integer coordinate recovery");
	print("PASS: arbitrary-precision scaling, coefficients, and unimodular changes");
};

qt_test_body(dbg,dmax,nmax,ymax)={
	my(S,count=0);
	
	qt_test_assert(type(dmax)=="t_INT" && dmax>=1,"dmax must be an integer >= 1");
	qt_test_assert(type(nmax)=="t_INT" && nmax>=0,"nmax must be an integer >= 0");
	qt_test_assert(type(ymax)=="t_INT" && ymax>=0,"ymax must be an integer >= 0");
	qt_test_isolation();
	qt_test_normalisation();
	qt_test_class_roots();
	qt_test_transformations();
	qt_test_filters();
	qt_test_regressions();
	qt_test_arithmetic();
	qt_test_certification_and_errors();
	qt_test_parallel_and_seeds();
	qt_test_independent_descents();
	qt_test_real_class_groups();
	qt_test_odd_and_mixed_class_groups();
	qt_test_large_valuations();
	qt_test_prescribed_points();
	qt_test_large_exact_arithmetic();
	QT_CERTIFY_CLASSGROUP=1;QT_CERTIFY_THUE=1;
	for (d=2,dmax,
		if (!issquare(d),
			for (n=-nmax,-1,
				if (dbg,print("testing d=",d,", n=",n));
				S=quartic_thue_solve(d,n);
				qt_test_solution_set(d,n,S,ymax);
				count++;
			);
		);
	);
	print("quartic_thue: all focused tests and ",count,
		" bounded exhaustive comparisons passed (|y| <= ",ymax,")");
	return(count);
};

run_tests(dbg=0,dmax=1009,nmax=1009,ymax=10000)={
	return(qt_test_isolated(()->qt_test_body(dbg,dmax,nmax,ymax)));
};

\\ Retain the original slow overflow reproducer for manual investigation only.
\\ The automatic suite instead regenerates the descent for (2,-983).
run_error1()={
	my(form,t,rhs=2);
	form=5785066771608039779873689766746536762462433*qtU^4+2285500201543247644817612589071069290667652*qtU^3+338598803877911724690415295606530616347194*qtU^2+22294978463724875193283097852012899385892*qtU+550503345336516612414913569286566906223;
	t=thueinit(form,1);
	print("thueinit() done");
	return(thue(t,rhs));
};
