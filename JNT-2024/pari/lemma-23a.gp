\\ Calculations for Lemma 2.3(a), equation (2.2).
\\
\\ It suffices to take d' = 2^e, e = 0,...,6. Odd prime factors of d'
\\ cannot decrease N_{d',4,r}; the sign does not affect its coefficient gcd.
\\ For e >= 6, N_{d',4} = 8, while N_{d',4,r} is nondecreasing.
\\
\\ If D_{4,r} X_{1,4,r}(1-x) = sum_j b_j x^j, then
\\   N_{2^e,4,r} = gcd_j(b_j * 2^floor(e*j/2)).
\\ For odd e and odd j the remaining sqrt(2) is a basis element of
\\ Z[sqrt(2)], so it must not contribute an additional factor of 2.
\\
\\ GP vectors and matrices are indexed from 1. The entries corresponding
\\ to r,e are therefore denomValues[r+1], numerValues[r+1,e+1], S[k][r+1,e+1].

check_lemma23a(rUB=138)={
	my(a,approxVal,at,b,best,C,cont,d4LB,d4LBPowers,d4UB,den,denomExponent,denomValues,eb,eUB,
	gamma1,gamma2,locations,lowerBest,maxima,maxspec,numerValues,rb,S,sstar,term,whereMax);

	localprec(50);
	at = vector(2);
	best = [0,0];
	maxima = vector(2);
	maxspec = vector(2);
	whereMax = vector(2);
	eUB=6;
	S = vector(2, k, matrix(rUB+1,eUB+1));
	C = [293/250, 537/2000]; \\ max values of C_{4,1} and C_{4,2}
	denomExponent=42/25; \\ =1.68, denominator exponent

	\\ Rational bounds d4LB < exp(42/25) < d4UB.
	\\ After term 40, successive Taylor-term ratios are <= denomExponent/42.
	d4LB=1;
	term=1;
	for(j = 1, 40,
		term *= denomExponent/j;
		d4LB += term;
	);
	d4UB = d4LB + (term*denomExponent/41)/(1-denomExponent/42);

	d4LBPowers = vector(rUB+1, i, d4LB^(2*(i-1)));
	denomValues = vector(rUB+1);
	numerValues = matrix(rUB+1,eUB+1);
	
	gamma1=1; \\ gamma1 = Gamma(3/4)*r!/Gamma(r+3/4)
	gamma2=1/4; \\ gamma2 = Gamma(r+5/4)/(Gamma(1/4)*r!)
	for(r = 0,rUB,
		if(r > 0,
			gamma1 *= (4*r)/(4*r-1);
			gamma2 *= (4*r+1)/(4*r);
		);

		\\ a[j+1] = coefficient of x^j in 2F1(-r-1/4,-r;3/4;x).
		a = vector(r+1);
		a[1] = 1;
		for(j = 0, r-1,
			a[j+2] = a[j+1]*(r-j)*(4*r+1-4*j)/((j+1)*(4*j+3));
		);
		den = lcm(vector(r+1, i, denominator(a[i])));
		denomValues[r+1] = den;

		\\ Exact binomial substitution x -> 1-x:
		\\ b[i] is the coefficient of x^(i-1) in den*X_{1,4,r}(1-x).
		b = vector(r+1);
		for(i=1,r+1,
			b[i]=(-1)^(i-1)*sum(j = i-1, r, den*a[j+1]*binomial(j,i-1));
		);

		for(e=0,eUB,
			cont = gcd(vector(r+1, i, b[i]*2^floor(e*(i-1)/2)));
			numerValues[r+1,e+1] = cont;

			\\ Since N_{2^e,4} = 2^(e/2), the normalised ratios squared
			\\ are S[k][r+1,e+1]*exp(-2*denomExponent*r). Thus S is rational.
			S[1][r+1,e+1] = (gamma1*den/cont)^2 * 2^(e*r);
			S[2][r+1,e+1] = (gamma2*den/cont)^2 * 2^(e*r);

			for(k = 1, 2,
				\\ Exact certificate of strict inequality (2.2).
				if(S[k][r+1,e+1] >= C[k]^2*d4LBPowers[r+1],
					error("Bound ",k," not certified at r=",r,", e=",e)
				);
				approxVal = sqrt(S[k][r+1,e+1])*exp(-denomExponent*r);
				if(approxVal > best[k],
					best[k] = approxVal;
					at[k] = [r,e];
				);
			);
		);
	); \\ r for-loop

	\\ Certify each candidate maximum and all ties using rational comparisons.
	\\ Every other case has an upper bound below the candidate's lower bound.
	for(k=1,2,
		rb = at[k][1];
		eb = at[k][2];
		sstar = S[k][rb+1,eb+1];
		lowerBest = sstar/d4UB^(2*rb);
		locations = List();
		for(r=0,rUB,
			for(e=0,eUB,
				if(r==rb && S[k][r+1,e+1] == sstar,
					listput(locations, [r,e]),
					if(S[k][r+1,e+1] >= lowerBest*d4LBPowers[r+1],
						error("Maximum ",k," not certified at r=",r,", e=",e)
					)
				);
			);
		);

		\\ Exact specification [s,t] means sqrt(s)*exp(t).
		maxspec[k] = [sstar,-denomExponent*rb];
		maxima[k] = sqrt(sstar)*exp(-denomExponent*rb);
		whereMax[k] = Vec(locations);
	);

	\\print("All (rUB+1)*(eUB+1)=",((rUB+1)*(eUB+1))," cases passed both bounds, using exact rational arithmetic.");
	for(k = 1, 2,
		print("Maximum C_{4,",k,"} = sqrt(",maxspec[k][1],")*exp(",maxspec[k][2],")");
		printf("  approximately %.20f\n", maxima[k]);
		print("  attained at [r,e] = ",whereMax[k]," (d' = 2^e)");
	);
	\\print("Both maxima and all listed ties are certified exactly.");
};