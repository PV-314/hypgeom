\\ Rigorous reduction of
\\             x^2 - d*y^4 = n,   d > 1, n < 0,
\\ to a finite list of quartic Thue equations.
\\ One entry point is
\\             quartic_to_thue(d,n)
\\ and the entry point for the solver, which is most likely what you want, is
\\             quartic_thue_solve(d,n).
\\
\\ A multithreaded PARI build may instead use
\\             quartic_thue_solve_parallel(d,n).
\\
\\ The returned object R has the following structure:
\\   R[1] = metadata:
\\          [d,n,m0,q,s0,field_discriminant,class_group_cyclic_factors,
\\           number_of_fourth_power_residue_ideals,class_group_certified,
\\           x_scale,d0,n0]
\\          where d,n are the original inputs, x=x_scale*X,
\\          X^2-d0*y^4=n0, and m0=-n0=q*s0^2 with q squarefree;
\\   R[2] = equations:
\\          R[2][j] is [P(T),c,H(U,V)], meaning H(U,V)=c, equivalently P(U/V)*V^4=c;
\\   R[3] = descent cases.  A case stores the ideal/class/unit and lattice
\\          data needed to reconstruct a solution of the original equation.
\\
\\ Set QT_CERTIFY_CLASSGROUP=0 before calling quartic_to_thue()
\\    if a conditional-on-GRH class group is acceptable.
\\    This is for the imaginary quadratic class group used to construct the Thue equations.
\\ Set QT_CERTIFY_THUE=0 before calling quartic_thue_solve()
\\    for conditional Thue solving (i.e., the flag argument to PARI's thueinit() function)
QT_CERTIFY_CLASSGROUP = 1;
QT_CERTIFY_THUE = 1;

\\ Exact one-sided local sieving.  QT_LOCAL_MODULI handles the useful
\\ small prime powers; QT_LOCAL_PRIME_BOUND scans all primes up to the
\\ stated bound using an O(p), rather than O(p^2), projective test.
\\ Set QT_LOCAL_SIEVE=0 to disable these tests for comparison/debugging.
QT_LOCAL_SIEVE = 1;
QT_LOCAL_MODULI = [4,8,16,9];
QT_LOCAL_PRIME_BOUND = 199;

\\ Private polynomial variables used by this file.
qtU = 'qtU;
qtV = 'qtV;
qtZ = 'qtZ;

quartic_thue_solve(d,n,dbg=0)={
	my(normalised);
	
	qt_check_input(d,n);
	normalised = qt_square_normalise(d,n);
	if (!qt_original_locally_possible(normalised[1],normalised[2]),
		return([]);
	);
	return(quartic_thue_solve_from(quartic_to_thue(d,n,dbg),dbg));
}


quartic_to_thue(d,n,dbg=0)={
	my(dorig=d, norig=n, normalised, xscale, m, cs, q, sfield, pol);
	my(bnf, nf, certified = 0, classflag);
	my(astates, eqs = List(), cases = List(), cyc, tu, w, zeta);
	my(i, j, u, A, alocal, acl, roots, c, C, J, principal, delta);
	my(Cinv, bp1, bp2, bp, bpcase, unit, kappa, formdata, eqno, meta);
	
	qt_check_input(d,n);
	normalised = qt_square_normalise(d,n);
	d = normalised[1];
	n = normalised[2];
	xscale = normalised[3];
	m = -n;
	cs = core(m,1);
	q = cs[1];
	sfield = cs[2];
	pol = qtZ^2 + q;
	classflag = qt_binary_flag(QT_CERTIFY_CLASSGROUP,1,"QT_CERTIFY_CLASSGROUP");
	
	\\ Flag 1 keeps exact algebraic data needed by bnfisprincipal.
	bnf = bnfinit(pol,1);
	nf = bnf.nf;
	if (classflag,
		if (!bnfcertify(bnf),
			error("quartic_to_thue: PARI could not certify the class group");
		);
		certified = 1;
	);

	astates = qt_residue_ideals(nf,d,m);
	cyc = bnf.cyc;
	tu = bnf.tu;
	w = tu[1];
	zeta = nfbasistoalg(nf,tu[2]);

	for (i = 1, #astates,
		A = astates[i][1];
		alocal = astates[i][2];
		acl = Vec(bnfisprincipal(bnf,A,0));
		roots = qt_fourth_class_roots(cyc,acl);
		for (j = 1, #roots,
			c = roots[j];
			if (#c,
				C = idealfactorback(nf,bnf.gen,c),
				C = idealhnf(nf,1)
			);
			C = idealred(nf,C);
			J = idealmul(nf,A,idealpow(nf,C,4));
			principal = bnfisprincipal(bnf,J);
			if (!qt_zerovec(principal[1]),
				error("quartic_to_thue: internal class-group inconsistency")
			);
			delta = nfbasistoalg(nf,principal[2]);

			Cinv = idealinv(nf,C);
			bp1 = qt_pair(nf,Cinv[,1]);
			bp2 = qt_pair(nf,Cinv[,2]);
			bp = [bp1,bp2];

			for (u = 0, w-1,
				unit = zeta^u;
				kappa = qt_pair(nf,unit*delta);
				formdata = qt_make_form(q,kappa,bp,sfield);
				if (#formdata,
					bpcase = formdata[5];
					eqno = qt_find_equation(eqs,formdata);
					if (!eqno,
						listput(eqs,[formdata[1],formdata[2],formdata[3]]);
						eqno = #eqs;
					);

					\\ [equation number, local A exponents, A, class root, unit exponent,
					\\  kappa pair, reduced inverse-class-ideal lattice basis,
					\\  legacy shear (now 0; retained for backward-compatible recovery)]
					listput(cases,[eqno,alocal,A,c,u,kappa,bpcase,formdata[4]]);
				);
			);
		);
	);

	meta = [dorig,norig,m,q,sfield,bnf.disc,cyc,#astates,certified,xscale,d,n];
	return([meta,Vec(eqs),Vec(cases)]);
}

\\ In GP, an unset variable evaluates to a formal polynomial bearing its name.
\\ This can happen after kill() or \k and used to make thueinit() see a
\\ t_POL where its integer flag was expected.
\\ Treat an unset setting as its rigorous default; reject every other non-binary value explicitly.
qt_binary_flag(v, fallback, setting_name)={
	if (type(v) == "t_POL", return(fallback));
	if (type(v) != "t_INT" || (v != 0 && v != 1),
		error(setting_name," must be 0 or 1")
	);
	return(v);
}

qt_nonnegative_integer_setting(v, fallback, setting_name)={
	if (type(v) == "t_POL", return(fallback));
	if (type(v) != "t_INT" || v < 0,
		error(setting_name," must be a nonnegative integer")
	);
	return(v);
}

qt_moduli_setting(v)={
	if (type(v) == "t_POL", return([4,8,16,9]));
	if (type(v) != "t_VEC" && type(v) != "t_COL",
		error("QT_LOCAL_MODULI must be a vector of integers >= 2");
	);
	for (i=1,length(v),
		if (type(v[i]) != "t_INT" || v[i] < 2,
			error("QT_LOCAL_MODULI must be a vector of integers >= 2");
		)
	);
	return(Vec(v));
}

qt_check_input(d,n)={
	if (type(d) != "t_INT" || type(n) != "t_INT",
		error("quartic_to_thue: d and n must be integers");
	);
	if (d <= 1, error("quartic_to_thue: require d>1"));
	if (n >= 0, error("quartic_to_thue: require n<0"));
	if (issquare(d), error("quartic_to_thue: d must not be a square"));
}

\\ Remove the largest square dividing both coefficients.  If scale^2 divides
\\ gcd(d,-n), then scale^2 divides x^2 in every solution and hence scale|x.
\\ Thus x=scale*X gives a bijection with X^2-d0*y^4=n0.  core(g,1)[2]
\\ is the largest scale for which scale^2 divides the positive integer g.
qt_square_normalise(d,n)={
	my(cs, scale);
	
	cs=core(gcd(d,-n),1);
	scale=cs[2];
	return([d/scale^2,n/scale^2,scale]);
}

qt_zerovec(v)={
	for(i = 1, #v,
		if (v[i] != 0,
			return(0);
		);
	);
	return(1);
}

\\ Convert an element of Q(sqrt(-q)), represented in any standard PARI
\\ number-field format, to the pair [a,b] representing a+b*qtZ.
qt_pair(nf, a)={
	my(z = lift(nfbasistoalg(nf, a)));
	
	if (type(z) == "t_POL",
		return([polcoef(z,0), polcoef(z,1)]);
	);
	return([z,0]);
}

qt_pairmul(q, a, b)={
	return([a[1]*b[1] - q*a[2]*b[2],a[1]*b[2] + a[2]*b[1]]);
}

qt_pairpow4(q, a)={
	my(a2);
	
	a2 = qt_pairmul(q,a,a);
	return(qt_pairmul(q,a2,a2));
}

qt_basis_transform(bp, M)={
	my(c1, c2);
	
	c1 = [bp[1][1]*M[1,1] + bp[2][1]*M[2,1], bp[1][2]*M[1,1] + bp[2][2]*M[2,1]];
	c2 = [bp[1][1]*M[1,2] + bp[2][1]*M[2,2], bp[1][2]*M[1,2] + bp[2][2]*M[2,2]];
	return([c1,c2]);
}

\\ LLL-reduce a basis of the fractional ideal for the positive norm form
\\ N(a+b*sqrt(-q))=a^2+q*b^2.  If B is the old basis matrix, qflllgram
\\ returns U with B*U reduced; U is unimodular, so the lattice is unchanged.
qt_lll_basis(q, bp)={
	my(G, U);
	
	G = [bp[1][1]^2 + q*bp[1][2]^2, bp[1][1]*bp[2][1] + q*bp[1][2]*bp[2][2];
		bp[1][1]*bp[2][1] + q*bp[1][2]*bp[2][2], bp[2][1]^2 + q*bp[2][2]^2];
	U = qflllgram(G);
	return(qt_basis_transform(bp,U));
}

qt_pol_transform(P, M)={
	my(Q);

	Q=0;	
	for (k=0,4,
		Q += polcoef(P,k)*(M[1,1]*qtU+M[1,2])^k*(M[2,1]*qtU+M[2,2])^(4-k);
	);
	return(Q);
}

qt_pol_height(P)={
	return(vecmax(apply(abs,Vec(P))));
}

\\ For P=a*x^4+b*x^3+... the standard integral monic polynomial used
\\ for its number field is a^3*P(x/a).  A binary quartic can have modest
\\ coefficients while this polynomial has enormous coefficients, making
\\ thueinit unnecessarily expensive.  Track its height as well.
qt_monic_height(P)={
	my(a,Q);
	
	a=polcoef(P,4);
	Q=qtU^4;
	for (k=0,3,
		Q += polcoef(P,k)*a^(3-k)*qtU^k;
	);
	return(qt_pol_height(Q));
}

qt_solver_height(P)={
	return(max(qt_pol_height(P),qt_monic_height(P)));
}

qt_equation_less(P,rhs,Q,qrhs)={
	my(sP=qt_solver_height(P),sQ=qt_solver_height(Q));
	my(hP=qt_pol_height(P),hQ=qt_pol_height(Q),k,a,b);
	
	if (sP<sQ,return(1));
	if (sP>sQ,return(0));
	if (hP<hQ,return(1));
	if (hP>hQ,return(0));
	forstep(k=4,0,-1,
		a=polcoef(P,k);
		b=polcoef(Q,k);
		if (a<b,return(1));
		if (a>b,return(0))
	);
	return(rhs<qrhs);
}

\\ Return 1 exactly when F(x,y)=rhs has a solution modulo m, where
\\ F(x,y)=y^4*P(x/y).  This is deliberately a one-sided sieve: only a
\\ proven failure modulo m is used to discard a global Thue equation.
qt_has_solution_mod(P,rhs,m)={
	my(a0=lift(Mod(polcoef(P,0),m)),
			a1=lift(Mod(polcoef(P,1),m)),
			a2=lift(Mod(polcoef(P,2),m)),
			a3=lift(Mod(polcoef(P,3),m)),
			a4=lift(Mod(polcoef(P,4),m)),
			target=lift(Mod(rhs,m)),x,y,v);
	for (x=0,m-1,
		for (y=0,m-1,
			v = a4*x^4 + a3*x^3*y + a2*x^2*y^2 + a1*x*y^3 + a0*y^4;
			if (v % m == target, return(1))
		)
	);
	return(0);
}

qt_is_fourth_power_mod_prime(a,p)={
	a = lift(Mod(a,p));
	if (!a, return(0));
	return(lift(Mod(a,p)^((p-1)/gcd(4,p-1))) == 1);
}

\\ For prime p not dividing rhs, every solution has either y != 0,
\\ when t=x/y and P(t)*y^4=rhs, or y=0.  This reduces the p^2 affine
\\ search to p+1 projective directions.  If p divides rhs, (0,0) is
\\ always a solution modulo p, so the prime test correctly does no work;
\\ the prime-power tests above can still detect valuation obstructions.
qt_has_solution_mod_prime(P,rhs,p)={
	my(t,v,a4=polcoef(P,4));

	if (rhs % p == 0, return(1));
	if (a4 % p &&
			qt_is_fourth_power_mod_prime(lift(Mod(rhs,p)/Mod(a4,p)),p),
		return(1)
	);
	for (t=0,p-1,
		v = subst(P,qtU,t);
		if (v % p &&
				qt_is_fourth_power_mod_prime(lift(Mod(rhs,p)/Mod(v,p)),p),
			return(1)
		)
	);
	return(0);
}

qt_locally_possible(P,rhs)={
	my(flag,mods,bound,i,p);
	flag = qt_binary_flag(QT_LOCAL_SIEVE,1,"QT_LOCAL_SIEVE");
	if (!flag, return(1));
	mods = qt_moduli_setting(QT_LOCAL_MODULI);
	for (i=1,#mods,
		if (!qt_has_solution_mod(P,rhs,mods[i]), return(0))
	);
	bound = qt_nonnegative_integer_setting(QT_LOCAL_PRIME_BOUND,199,
																					"QT_LOCAL_PRIME_BOUND");
	if (bound >= 2,
		forprime (p=2,bound,
			if (!qt_has_solution_mod_prime(P,rhs,p), return(0))
		)
	);
	return(1);
}

\\ A still cheaper preflight for the original equation.  This does not
\\ alter quartic_to_thue's output (whose descent cases may intentionally
\\ overcount), but lets the end-to-end solver return before any class-group
\\ or Thue work when x^2-d*y^4=n already fails a local test.
qt_original_has_solution_mod(d,n,m)={
	my(squares=vector(m),x,y,target);
	
	for (x=0,m-1, squares[lift(Mod(x^2,m))+1]=1);
	for (y=0,m-1,
		target=lift(Mod(d*y^4+n,m));
		if (squares[target+1], return(1))
	);
	return(0);
}

qt_original_locally_possible(d,n)={
	my(flag,mods,bound,i,p);
	
	flag = qt_binary_flag(QT_LOCAL_SIEVE,1,"QT_LOCAL_SIEVE");
	if (!flag, return(1));
	mods = qt_moduli_setting(QT_LOCAL_MODULI);
	for (i=1,#mods,
		if (!qt_original_has_solution_mod(d,n,mods[i]), return(0))
	);
	bound = qt_nonnegative_integer_setting(QT_LOCAL_PRIME_BOUND,199,
																					"QT_LOCAL_PRIME_BOUND");
	if (bound >= 2,
		forprime (p=2,bound,
			if (!qt_original_has_solution_mod(d,n,p), return(0))
		)
	);
	return(1);
}

\\ Exact local GL_2(Z) height reduction.  The objective controls both the
\\ binary-form height and the height of the associated monic field polynomial
\\ used by thueinit.  Small unimodular matrices remove local basis defects;
\\ the two centered shears can be arbitrarily large and remove large
\\ translations in either coordinate.  Equal-height moves are resolved
\\ lexicographically, which also canonicalizes sign/swap symmetries and lets
\\ equivalent descent cases share one thueinit call.
\\ Return [P,rhs,M], with the new equation obtained by z -> M*z.
qt_reduce_pol(P,rhs)={
	my(total=matid(2),cur=P,curR=rhs,bestP,bestR,bestM,cand,candR);
	my(a,b,c,d,k,k0,pass,M,lead,cubic,sgn);

	if (pollead(cur)<0,cur=-cur;curR=-curR);

	for (pass=1,20,
		bestP=cur; bestR=curR; bestM=matid(2);

		\\ Exhaust the small neighborhood in GL_2(Z).
		for (a=-2,2, for (b=-2,2, for (c=-2,2, for (d=-2,2,
			if (abs(a*d-b*c)==1,
				M=[a,b;c,d]; cand=qt_pol_transform(cur,M);
				if (poldegree(cand,qtU)==4,
					candR=curR;
					if (pollead(cand)<0,cand=-cand;candR=-candR);
					if (qt_equation_less(cand,candR,bestP,bestR),
						bestP=cand;bestR=candR;bestM=M
					)
				)
			)
		))));

		\\ Center x -> x+k in one exact step, allowing a large k.
		lead=polcoef(cur,4); cubic=polcoef(cur,3);
		if (lead,
			k0=round(-cubic/(4*lead));
			for (k=k0-2,k0+2,
				M=[1,k;0,1]; cand=qt_pol_transform(cur,M);
				candR=curR;
				if (pollead(cand)<0,cand=-cand;candR=-candR);
				if (qt_equation_less(cand,candR,bestP,bestR),
					bestP=cand;bestR=candR;bestM=M
				)
			)
		);

		\\ The conjugate operation y -> y+k*x centers the reciprocal form.
		lead=polcoef(cur,0); cubic=polcoef(cur,1);
		if (lead,
			k0=round(-cubic/(4*lead));
			for (k=k0-2,k0+2,
				M=[1,0;k,1]; cand=qt_pol_transform(cur,M);
				if (poldegree(cand,qtU)==4,
					candR=curR;
					if (pollead(cand)<0,cand=-cand;candR=-candR);
					if (qt_equation_less(cand,candR,bestP,bestR),
						bestP=cand;bestR=candR;bestM=M
					)
				)
			)
		);

		if (!qt_equation_less(bestP,bestR,cur,curR),break);
		cur=bestP;curR=bestR;total=total*bestM
	);
	return([cur,curR,total]);
}

\\ Local fourth-power residues for the primes above p.  Here vd=v_p(d)
\\ and bad says p | 2m.  Away from 2m, conjugate factors are coprime, so
\\ at most one prime in a split pair may have a nonzero residue.
qt_local_options(pr, vd, bad)={
	my(L = List(), a, b);

	if (#pr == 2,
		for (a = 0, 3,
			for (b = 0, 3,
				if (lift(Mod(a+b-vd,4)) == 0 && (bad || a == 0 || b == 0),
					listput(L,[a,b])
				)
			)
		);
		return(Vec(L))
	);

	\\ One prime above p: ramified (e=2) or inert (f=2).
	if (pr[1].e == 2,
		listput(L,[lift(Mod(vd,4))]);
		return(Vec(L))
	);

	if (pr[1].f == 2,
		if (vd % 2, return([]));
		for (a = 0, 3,
			if (lift(Mod(2*a-vd,4)) == 0 && (bad || a == 0),
				listput(L,[a])
			)
		);
		return(Vec(L))
	);

	error("quartic_to_thue: unexpected prime decomposition at p=",pr[1].p);
}

\\ Enumerate A with (x+s*sqrt(-q)) = A*B^4.  Only primes above 2md can
\\ occur in A.  Each state is [A, local_data], with local_data recording
\\ [p, exponent_vector].
qt_residue_ideals(nf, d, m)={
	my(F = factor(2*d*m), primes = Vec(F[,1]));
	my(states = List(), next, i, j, k, p, vd, bad, pr, opts, st, op, loc);

	listput(states,[idealhnf(nf,1), []]);
	for (i = 1, #primes,
		p = primes[i];
		vd = valuation(d,p);
		bad = (p == 2 || valuation(m,p) > 0);
		pr = idealprimedec(nf,p);
		opts = qt_local_options(pr,vd,bad);
		if (#opts == 0, return([]));

		next = List();
		for (j = 1, #states,
			st = states[j];
			for (k = 1, #opts,
				op = opts[k];
				loc = idealfactorback(nf,pr,op);
				listput(next,
					[idealmul(nf,st[1],loc), concat(st[2],[[p,op]])]
				)
			)
		);
		states = next
	);
	return(Vec(states));
}

\\ All c in direct_product Z/cyc[i]Z satisfying a+4c=0.
qt_fourth_class_roots(cyc, a) =
{
	my(R = List(), next, vals, i, j, k, h, g, h1, b, c0);
	listput(R,[]);

	for (i = 1, #cyc,
		h = cyc[i];
		b = lift(Mod(-a[i],h));
		g = gcd(4,h);
		if (b % g, return([]));
		h1 = h/g;
		if (h1 == 1,
			c0 = 0,
			c0 = lift(Mod(4/g,h1)^(-1) * Mod(b/g,h1))
		);
		vals = vector(g,k,c0+(k-1)*h1);

		next = List();
		for (j = 1, #R,
			for (k = 1, #vals,
				listput(next,concat(R[j],vals[k]))
			)
		);
		R = next
	);
	return(Vec(R));
}

\\ Construct an integral binary quartic from
\\ Im((kappa_1+kappa_2*sqrt(-q)) * beta^4)=sfield.
\\ The lattice basis is bp=[basis_pair_1,basis_pair_2].
\\ An initial shear is selected so that the dehomogenized polynomial really
\\ has degree 4; it and all later GL_2(Z) changes are folded into the returned
\\ lattice basis.
\\ Return [P,rhs,H,0,reduced_lattice_basis].
qt_make_form(q, kappa, bp, sfield)={
	my(A, B, real4, imag4, F0, den, F, P, H, rhs, h, shear=0, trial, red);

	bp = qt_lll_basis(q,bp);

	A = bp[1][1]*qtU + bp[2][1]*qtV;
	B = bp[1][2]*qtU + bp[2][2]*qtV;
	real4 = A^4 - 6*q*A^2*B^2 + q^2*B^4;
	imag4 = 4*A*B*(A^2-q*B^2);
	F0 = kappa[2]*real4 + kappa[1]*imag4;

	den = denominator(F0,1);
	F = den*F0;
	rhs = den*sfield;

	\\ A GP for-loop restores its index on exit.  Save the chosen shear
	\\ separately so the recovery lattice receives the same substitution.
	for (trial = 0, 4,
		P = subst(subst(F,qtV,trial*qtU+qtV),qtV,1);
		if (poldegree(P,qtU) == 4,
			shear = trial;
			break;
		);
	);
	if (poldegree(P,qtU) != 4,
		error("quartic_to_thue: could not dehomogenize a nonzero quartic form")
	);

	\\ The content of F must divide rhs.  Dividing only by their gcd would
	\\ leave a visibly impossible, nonprimitive Thue equation in the list.
	h = content(P,1);
	if (rhs % h, return([]));
	P = P/h;
	rhs = rhs/h;
	\\ Local solubility is invariant under every later GL_2(Z) reduction,
	\\ so reject here and avoid that reduction work as well as thueinit.
	if (!qt_locally_possible(P,rhs), return([]));
	bp = qt_basis_transform(bp,[1,0;shear,1]);
	red = qt_reduce_pol(P,rhs);
	P = red[1];
	rhs = red[2];
	bp = qt_basis_transform(bp,red[3]);
	H = sum(k=0,4,polcoef(P,k)*qtU^k*qtV^(4-k));
	return([P,rhs,H,0,bp]);
}

qt_find_equation(eqs, formdata)={
	for (i = 1, #eqs,
		if (eqs[i][1] == formdata[1] && eqs[i][2] == formdata[2],
			return(i);
		);
	);
	return(0);
}

quartic_to_thue_print(R)={
	my(M = R[1], E = R[2], i);
	print("x^2 - ",M[1],"*y^4 = ",M[2]);
	\\ Older saved descents have nine metadata entries and no scaling.
	if (#M >= 12,
		if (M[10] != 1,
			print("normalisation: x=",M[10],"*X; X^2 - ",
				M[11],"*y^4 = ",M[12]);
		);
	);
	print("m0=-n0=",M[3]," = ",M[4],"*",M[5],"^2");
	print("field discriminant = ",M[6],", class group factors = ",M[7]);
	print("class group certified = ",M[9]);
	print("residue ideals A = ",M[8],", descent cases = ",#R[3]);
	print("distinct quartic Thue equations = ",#E);
	for (i = 1, #E,
		print(i,".  ",E[i][3]," = ",E[i][2])
	);
}

\\ Recover all (x,y) from already-generated R and a vector eqsol for which
\\ eqsol[j] is the output of thue() for R[2][j].
qt_recover(R, eqsol)={
	my(M = R[1], dorig = M[1], norig = M[2], m = M[3]);
	my(q = M[4], sfield = M[5], xscale = 1, d = dorig);
	my(C = R[3], ans = List(), i, j, ca, sol, shear, rr, ss, r, s);
	my(bp, beta, gamma, X, x, y4, y);

	if (#M >= 12,
		xscale = M[10];
		d = M[11];
	);
	\\ Reject incomplete solver output, including a zero placeholder after failure.
	if (type(eqsol) != "t_VEC" || #eqsol != #R[2],
		error("qt_recover: require one solution vector per Thue equation");
	);
	for (i=1,#eqsol,
		if (type(eqsol[i]) != "t_VEC",
			error("qt_recover: missing solution vector for Thue equation ",i);
		);
		for (j=1,#eqsol[i],
			sol = eqsol[i][j];
			if (type(sol) != "t_VEC" || #sol != 2,
				error("qt_recover: malformed solution for Thue equation ",i);
			);
			if (type(sol[1]) != "t_INT" || type(sol[2]) != "t_INT",
				error("qt_recover: noninteger solution for Thue equation ",i);
			);
		);
	);

	for (i=1,#C,
		ca = C[i];
		shear = ca[8];
		bp = ca[7];
		sol = eqsol[ca[1]];
		for (j = 1, #sol,
			rr = sol[j][1];
			ss = sol[j][2];
			r = rr;
			s = shear*rr+ss;
			beta = [bp[1][1]*r+bp[2][1]*s,
			bp[1][2]*r+bp[2][2]*s];
			gamma = qt_pairmul(q,ca[6],qt_pairpow4(q,beta));

			if (gamma[2] == sfield && denominator(gamma[1]) == 1,
				X = gamma[1];
				y4 = (X^2+m)/d;
				if (type(y4) == "t_INT" && y4 >= 0 && ispower(y4,4,&y),
					x = xscale*X;
					if (x^2-dorig*y^4 == norig,
						listput(ans,[x,y]);
						if (y,
							listput(ans,[x,-y]);
						);
					);
				);
			);
		);
	);
	return(Set(Vec(ans)));
}

quartic_thue_solve_from(R,dbg=0)={
	my(E,initflag,j,polcache,S,startTime,T,thueflag,tnfcache);

	polcache=List();
	tnfcache=List();
	startTime=getwalltime();
	E = R[2];
	S = vector(#E);
	thueflag = qt_binary_flag(QT_CERTIFY_THUE,1,"QT_CERTIFY_THUE");
	if(dbg!=0,
		print("in quartic_thue_solve_from(): solving ",#E," Thue equations");
		print("E=",E);
	);
	for (i = 1, #E,
		j=0;
		print("starting a Thue equation: form=",E[i][1],", RHS=",E[i][2]);
		for (k=1,#polcache,
			if (polcache[k]==E[i][1],j=k;break)
		);
		if (!j,
			initflag=qt_thue_group_flag(E,[i],thueflag);
			\\ The one-index call above finds every matching polynomial in E.
			print("about to call thueinit() using initflag=",initflag);
			T=thueinit(E[i][1],initflag);
			listput(polcache,E[i][1]);
			listput(tnfcache,T);
			j=#polcache;
		);
		T=tnfcache[j];
		\\ Abort on failure: an unsolved equation must never count as no solutions.
		S[i] = thue(T,E[i][2]);
		if(dbg!=0,
			print("done a Thue equation: solns=",S[i],". form=",E[i][1],", RHS=",E[i][2]," time taken(ms)=",getwalltime()-startTime,"=",strtime(getwalltime()-startTime));
		);
	);
	return(qt_recover(R,S));
}

\\ PARI documents that thue() with rhs = +/-1 is unconditional even when
\\ thueinit used flag 0.  If every equation for a polynomial has unit rhs,
\\ avoid needless class-group certification.  A single nonunit rhs keeps
\\ flag 1 for the shared initialization.  QT_FAST_UNIT_RHS=0 forces the old
\\ behavior, without changing any other optimization.
qt_thue_group_flag(E,ind,requested_flag)={
	my(fast,i,j,P);
	if (!requested_flag,
		return(0);
	);
	fast=qt_binary_flag(QT_FAST_UNIT_RHS,1,"QT_FAST_UNIT_RHS");
	if (!fast,
		return(1);
	);
	P=E[ind[1]][1];
	for (i=1,length(E),
		if (E[i][1]==P && abs(E[i][2])!=1,
			return(1);
		);
	);
	return(0);
}

\\ Solve one group of equations sharing the same defining polynomial.
\\ The task contains all of its data explicitly, so it is safe to pass to
\\ PARI's parallel workers (which must not read mutable GP globals).
qt_solve_thue_task(task)={
	my(E=task[1], ind=task[2], thueflag=task[3], T, k);
	
	T = thueinit(E[ind[1]][1],thueflag);
	return(vector(#ind,k,[ind[k],thue(T,E[ind[k]][2])]));
}

\\ Parallel variant.  Equations with the same polynomial remain in one
\\ task so that thueinit is still computed only once.  PARI uses the value
\\ of default(nbthreads).  This entry point requires a PARI build providing
\\ parapply; use quartic_thue_solve on a single-thread-only build.
quartic_thue_solve_parallel_from(R)={
	my(E=R[2], S=vector(#E), pols=List(), groupno=vector(#E));
	my(groups,tasks,blocks,thueflag,i,j,k,g);
	
	if(!#E,
		return([]);
	);
	thueflag = qt_binary_flag(QT_CERTIFY_THUE,1,"QT_CERTIFY_THUE");
	for (i=1,#E,
		j=0;
		for (k=1,#pols,
			if (pols[k]==E[i][1],
				j=k;
				break;
			);
		);
		if (!j,
			listput(pols,E[i][1]);
			j=#pols;
		);
		groupno[i]=j;
	);
	
	groups=vector(#pols,j,List());
	for(i=1,#E,
		listput(groups[groupno[i]],i);
	);
	groups=vector(#groups,j,Vec(groups[j]));
	tasks=vector(#groups,j,[E,groups[j],qt_thue_group_flag(E,groups[j],thueflag)]);
	blocks=parapply(qt_solve_thue_task,tasks);
	for (g=1,#blocks,
		for (k=1,#blocks[g],
			S[blocks[g][k][1]]=blocks[g][k][2];
		);
	);
	return(qt_recover(R,S));
}

quartic_thue_solve_parallel(d,n)={
	my(normalised);
	
	qt_check_input(d,n);
	normalised = qt_square_normalise(d,n);
	if (!qt_original_locally_possible(normalised[1],normalised[2]),
		return([]);
	);
	return(quartic_thue_solve_parallel_from(quartic_to_thue(d,n)));
}