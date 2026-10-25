read("..\..\..\general\pari\quartic_thue.gp");

\\ call the seven functions, check_b1(), check_b2(),..., check_b7()
\\ the other functions are only for use with these seven functions

check_d_n(d,nrmA,dbg=0)={
	my(allSolns,bfSolns,cSoln,startTime);
	
	startTime=getwalltime();
	print("\nd=",d,", nrmA=",nrmA,": ",factor(nrmA));
	soln=quartic_thue_solve(d,nrmA,dbg);
	allSolns=Set();
	for(i=1,length(soln),
		cSoln=soln[i];
		if(cSoln[1]>0 && cSoln[2]>0,
			allSolns=setunion(allSolns,[cSoln]);
		);
	);
	bfSolns=qt_test_brute(d,nrmA,dbg);
	print("Number of solutions=",length(allSolns),", allSolns=",allSolns,", time(ms)=",getwalltime()-startTime,"=",strtime(getwalltime()-startTime));
	if(length(allSolns)!=length(bfSolns),
		print("CHECK: length(allSolns)=",length(allSolns),", length(bfSolns)=",length(bfSolns));
		print("allSolns=",allSolns);
		print("total bfSolns=",bfSolns);
		return();
	);
	for(i=1,length(allSolns),
		ind=setsearch(bfSolns,allSolns[i]);
		if(ind==0,
			print("BAD: could not find allSolns[i]=",allSolns[i]," in bfSolns");
		);
	);
	if(length(allSolns)>3,
		print("BIG!!");
		return();
	);
}

qt_test_brute(d,n,dbg=0)={
	my(solns,x,x2,yUB);

	solns=Set();
	yUB=10*1000*1000;
	for(y=1,yUB,
		x2=d*y*y*y*y+n;
		if (x2>0 && issquare(x2),
			x=sqrtint(x2);
			solns=setunion(solns,[[x,y]]);
		);
	);
	return(solns);
}

check_b1()={
	my(a,b,d,dbg,nrmA,startTime,t,u);

	dbg=1;
	startTime=getwalltime();
	\\ u=1
	a=     1;b= 1;d=         8;t=     2;u= 1;nrmA=     -7;check_d_n(d,nrmA,dbg);
	a=     1;b= 1;d=        12;t=     4;u= 1;nrmA=    -11;check_d_n(d,nrmA,dbg);
	a=     2;b= 1;d=         8;t=     2;u= 1;nrmA=     -4;check_d_n(d,nrmA,dbg);
	a=     2;b= 1;d=        13;t=     3;u= 1;nrmA=     -9;check_d_n(d,nrmA,dbg);
	a=     4;b= 1;d=        32;t=     6;u= 1;nrmA=    -16;check_d_n(d,nrmA,dbg);
	a=    16;b= 1;d=       480;t=    22;u= 1;nrmA=   -224;check_d_n(d,nrmA,dbg);

	\\ u=2
	a=     1;b= 1;d=         2;t=     2;u= 2;nrmA=     -1;check_d_n(d,nrmA,dbg);
	a=     2;b= 1;d=         8;t=     6;u= 2;nrmA=     -4;check_d_n(d,nrmA,dbg);

	\\ u=4
	a=     1;b= 1;d=         2;t=     6;u= 4;nrmA=     -1;check_d_n(d,nrmA,dbg);
	print("total b=1 time(ms)=",getwalltime()-startTime,"=",strtime(getwalltime()-startTime));
}

check_b2()={
	my(a,b,d,dbg,nrmA,startTime,t,u);

	dbg=1;
	startTime=getwalltime();
	\\ u=1
	a=     1;b= 2;d=         8;t=     2;u= 1;nrmA=   -127;check_d_n(d,nrmA,dbg);
	a=     2;b= 2;d=        12;t=     4;u= 1;nrmA=   -188;check_d_n(d,nrmA,dbg);
	a=     4;b= 2;d=         8;t=     2;u= 1;nrmA=   -112;check_d_n(d,nrmA,dbg);
	a=     4;b= 2;d=        12;t=     4;u= 1;nrmA=   -176;check_d_n(d,nrmA,dbg);
	a=     6;b= 2;d=         5;t=     1;u= 1;nrmA=    -44;check_d_n(d,nrmA,dbg);
	a=     8;b= 2;d=         8;t=     2;u= 1;nrmA=    -64;check_d_n(d,nrmA,dbg);
	a=     8;b= 2;d=        13;t=     3;u= 1;nrmA=   -144;check_d_n(d,nrmA,dbg);
	a=     9;b= 2;d=         8;t=     2;u= 1;nrmA=    -47;check_d_n(d,nrmA,dbg);
	a=    11;b= 2;d=         8;t=     2;u= 1;nrmA=     -7;check_d_n(d,nrmA,dbg);
	a=    16;b= 2;d=        32;t=     6;u= 1;nrmA=   -256;check_d_n(d,nrmA,dbg);
	a=    19;b= 2;d=        29;t=     5;u= 1;nrmA=   -103;check_d_n(d,nrmA,dbg);
	a=    64;b= 2;d=       480;t=    22;u= 1;nrmA=  -3584;check_d_n(d,nrmA,dbg);

	\\ u=2
	a=     1;b= 2;d=         3;t=     4;u= 2;nrmA=    -47;check_d_n(d,nrmA,dbg);
	a=     2;b= 2;d=         2;t=     2;u= 2;nrmA=    -28;check_d_n(d,nrmA,dbg);
	a=     2;b= 2;d=         3;t=     4;u= 2;nrmA=    -44;check_d_n(d,nrmA,dbg);
	a=     4;b= 2;d=         2;t=     2;u= 2;nrmA=    -16;check_d_n(d,nrmA,dbg);
	a=     8;b= 2;d=         8;t=     6;u= 2;nrmA=    -64;check_d_n(d,nrmA,dbg);
	a=    32;b= 2;d=       120;t=    22;u= 2;nrmA=   -896;check_d_n(d,nrmA,dbg);

	\\ u=4
	a=     4;b= 2;d=         2;t=     6;u= 4;nrmA=    -16;check_d_n(d,nrmA,dbg);
	a=    16;b= 2;d=        30;t=    22;u= 4;nrmA=   -224;check_d_n(d,nrmA,dbg);
	print("total b=2 time(ms)=",getwalltime()-startTime,"=",strtime(getwalltime()-startTime));
}

check_b3(dbg=0)={
	my(a,b,d,dbg,nrmA,startTime,t,u);

	dbg=1;
	startTime=getwalltime();
	\\ u=1
	a=     7;b= 3;d=         5;t=     1;u= 1;nrmA=   -356;check_d_n(d,nrmA,dbg);
	a=    13;b= 3;d=         5;t=     1;u= 1;nrmA=   -236;check_d_n(d,nrmA,dbg);
	a=    16;b= 3;d=         5;t=     1;u= 1;nrmA=   -149;check_d_n(d,nrmA,dbg);
	a=    17;b= 3;d=         5;t=     1;u= 1;nrmA=   -116;check_d_n(d,nrmA,dbg);
	a=    17;b= 3;d=         5;t=     3;u= 1;nrmA=   -116;check_d_n(d,nrmA,dbg);
	a=    18;b= 3;d=         8;t=     2;u= 1;nrmA=   -324;check_d_n(d,nrmA,dbg);
	a=    18;b= 3;d=        13;t=     3;u= 1;nrmA=   -729;check_d_n(d,nrmA,dbg);
	a=    19;b= 3;d=         5;t=     1;u= 1;nrmA=    -44;check_d_n(d,nrmA,dbg);
	a=    19;b= 3;d=         5;t=     3;u= 1;nrmA=    -44;check_d_n(d,nrmA,dbg);
	a=    22;b= 3;d=         8;t=     2;u= 1;nrmA=   -164;check_d_n(d,nrmA,dbg);
	a=    31;b= 3;d=        12;t=     4;u= 1;nrmA=    -11;check_d_n(d,nrmA,dbg);
	a=    32;b= 3;d=        20;t=     4;u= 1;nrmA=   -596;check_d_n(d,nrmA,dbg);
	a=    32;b= 3;d=        85;t=     9;u= 1;nrmA=  -5861;check_d_n(d,nrmA,dbg);
	a=    34;b= 3;d=        20;t=     4;u= 1;nrmA=   -464;check_d_n(d,nrmA,dbg);
	a=    34;b= 3;d=        40;t=     6;u= 1;nrmA=  -2084;check_d_n(d,nrmA,dbg);
	a=    36;b= 3;d=        32;t=     6;u= 1;nrmA=  -1296;check_d_n(d,nrmA,dbg);
	a=    40;b= 3;d=        96;t=    10;u= 1;nrmA=  -6176;check_d_n(d,nrmA,dbg);
	a=    46;b= 3;d=        29;t=     5;u= 1;nrmA=   -233;check_d_n(d,nrmA,dbg);
	a=    55;b= 3;d=       221;t=    15;u= 1;nrmA= -14876;check_d_n(d,nrmA,dbg);
	a=    62;b= 3;d=        53;t=     7;u= 1;nrmA=   -449;check_d_n(d,nrmA,dbg);
	a=    70;b= 3;d=        68;t=     8;u= 1;nrmA=   -608;check_d_n(d,nrmA,dbg);
	a=    76;b= 3;d=        85;t=     9;u= 1;nrmA=  -1109;check_d_n(d,nrmA,dbg);
	a=    82;b= 3;d=        96;t=    10;u= 1;nrmA=  -1052;check_d_n(d,nrmA,dbg);
	a=   110;b= 3;d=       221;t=    15;u= 1;nrmA=  -5801;check_d_n(d,nrmA,dbg);
	a=   232;b= 3;d=       672;t=    26;u= 1;nrmA=   -608;check_d_n(d,nrmA,dbg);
	a=   608;b= 3;d=      4628;t=    68;u= 1;nrmA=  -5204;check_d_n(d,nrmA,dbg);

	\\ u=2
	a=     9;b= 3;d=         2;t=     2;u= 2;nrmA=    -81;check_d_n(d,nrmA,dbg);
	a=    11;b= 3;d=         2;t=     2;u= 2;nrmA=    -41;check_d_n(d,nrmA,dbg);
	a=    16;b= 3;d=         5;t=     4;u= 2;nrmA=   -149;check_d_n(d,nrmA,dbg);
	a=    17;b= 3;d=         5;t=     4;u= 2;nrmA=   -116;check_d_n(d,nrmA,dbg);
	a=    17;b= 3;d=        10;t=     6;u= 2;nrmA=   -521;check_d_n(d,nrmA,dbg);
	a=    18;b= 3;d=         8;t=     6;u= 2;nrmA=   -324;check_d_n(d,nrmA,dbg);
	a=    20;b= 3;d=        24;t=    10;u= 2;nrmA=  -1544;check_d_n(d,nrmA,dbg);
	a=    35;b= 3;d=        17;t=     8;u= 2;nrmA=   -152;check_d_n(d,nrmA,dbg);
	a=   116;b= 3;d=       168;t=    26;u= 2;nrmA=   -152;check_d_n(d,nrmA,dbg);
	a=   304;b= 3;d=      1157;t=    68;u= 2;nrmA=  -1301;check_d_n(d,nrmA,dbg);

	\\ u=4
	a=     9;b= 3;d=         2;t=     6;u= 4;nrmA=    -81;check_d_n(d,nrmA,dbg);
	a=    10;b= 3;d=         6;t=    10;u= 4;nrmA=   -386;check_d_n(d,nrmA,dbg);
	a=    58;b= 3;d=        42;t=    26;u= 4;nrmA=    -38;check_d_n(d,nrmA,dbg);

	\\ u=5
	a=   164;b= 3;d=       384;t=    98;u= 5;nrmA=  -4208;check_d_n(d,nrmA,dbg);

	\\ u=10
	a=    82;b= 3;d=        96;t=    98;u=10;nrmA=  -1052;check_d_n(d,nrmA,dbg);
	print("total b=3 time(ms)=",getwalltime()-startTime,"=",strtime(getwalltime()-startTime));
}

check_b4(dbg=0)={
	my(a,b,d,dbg,nrmA,startTime,t,u);

	dbg=1;
	startTime=getwalltime();
	\\ u=1
	a=     4;b= 4;d=         8;t=     2;u= 1;nrmA=  -2032;check_d_n(d,nrmA,dbg);
	a=     8;b= 4;d=        12;t=     4;u= 1;nrmA=  -3008;check_d_n(d,nrmA,dbg);
	a=    16;b= 4;d=         8;t=     2;u= 1;nrmA=  -1792;check_d_n(d,nrmA,dbg);
	a=    16;b= 4;d=        12;t=     4;u= 1;nrmA=  -2816;check_d_n(d,nrmA,dbg);
	a=    24;b= 4;d=         5;t=     1;u= 1;nrmA=   -704;check_d_n(d,nrmA,dbg);
	a=    32;b= 4;d=         8;t=     2;u= 1;nrmA=  -1024;check_d_n(d,nrmA,dbg);
	a=    32;b= 4;d=        13;t=     3;u= 1;nrmA=  -2304;check_d_n(d,nrmA,dbg);
	a=    34;b= 4;d=         5;t=     1;u= 1;nrmA=   -124;check_d_n(d,nrmA,dbg);
	a=    36;b= 4;d=         8;t=     2;u= 1;nrmA=   -752;check_d_n(d,nrmA,dbg);
	a=    44;b= 4;d=         8;t=     2;u= 1;nrmA=   -112;check_d_n(d,nrmA,dbg);
	a=    62;b= 4;d=       260;t=    16;u= 1;nrmA= -62716;check_d_n(d,nrmA,dbg);
	a=    64;b= 4;d=        32;t=     6;u= 1;nrmA=  -4096;check_d_n(d,nrmA,dbg);
	a=    76;b= 4;d=        29;t=     5;u= 1;nrmA=  -1648;check_d_n(d,nrmA,dbg);
	a=    81;b= 4;d=        68;t=     8;u= 1;nrmA= -10847;check_d_n(d,nrmA,dbg);
	a=    85;b= 4;d=        29;t=     5;u= 1;nrmA=   -199;check_d_n(d,nrmA,dbg);
	a=   113;b= 4;d=        60;t=     8;u= 1;nrmA=  -2591;check_d_n(d,nrmA,dbg);
	a=   256;b= 4;d=       480;t=    22;u= 1;nrmA= -57344;check_d_n(d,nrmA,dbg);

	\\ u=2
	a=     2;b= 4;d=         2;t=     2;u= 2;nrmA=   -508;check_d_n(d,nrmA,dbg);
	a=     4;b= 4;d=         3;t=     4;u= 2;nrmA=   -752;check_d_n(d,nrmA,dbg);
	a=     8;b= 4;d=         2;t=     2;u= 2;nrmA=   -448;check_d_n(d,nrmA,dbg);
	a=     8;b= 4;d=         3;t=     4;u= 2;nrmA=   -704;check_d_n(d,nrmA,dbg);
	a=    16;b= 4;d=         2;t=     2;u= 2;nrmA=   -256;check_d_n(d,nrmA,dbg);
	a=    18;b= 4;d=         2;t=     2;u= 2;nrmA=   -188;check_d_n(d,nrmA,dbg);
	a=    22;b= 4;d=         2;t=     2;u= 2;nrmA=    -28;check_d_n(d,nrmA,dbg);
	a=    31;b= 4;d=        65;t=    16;u= 2;nrmA= -15679;check_d_n(d,nrmA,dbg);
	a=    32;b= 4;d=         8;t=     6;u= 2;nrmA=  -1024;check_d_n(d,nrmA,dbg);
	a=   128;b= 4;d=       120;t=    22;u= 2;nrmA= -14336;check_d_n(d,nrmA,dbg);

	\\ u=4
	a=    16;b= 4;d=         2;t=     6;u= 4;nrmA=   -256;check_d_n(d,nrmA,dbg);
	a=    64;b= 4;d=        30;t=    22;u= 4;nrmA=  -3584;check_d_n(d,nrmA,dbg);
	print("total b=4 time(ms)=",getwalltime()-startTime,"=",strtime(getwalltime()-startTime));
}

check_b5(dbg=0)={
	my(a,b,d,dbg,nrmA,startTime,t,u);

	dbg=1;
	startTime=getwalltime();
	\\ u=1
	a=     1;b= 5;d=         8;t=     2;u= 1;nrmA=  -4999;check_d_n(d,nrmA,dbg);
	a=    11;b= 5;d=         5;t=     1;u= 1;nrmA=  -3004;check_d_n(d,nrmA,dbg);
	a=    41;b= 5;d=         5;t=     1;u= 1;nrmA=  -1444;check_d_n(d,nrmA,dbg);
	a=    50;b= 5;d=         8;t=     2;u= 1;nrmA=  -2500;check_d_n(d,nrmA,dbg);
	a=    52;b= 5;d=         5;t=     1;u= 1;nrmA=   -421;check_d_n(d,nrmA,dbg);
	a=    64;b= 5;d=         8;t=     2;u= 1;nrmA=   -904;check_d_n(d,nrmA,dbg);
	a=   100;b= 5;d=        32;t=     6;u= 1;nrmA= -10000;check_d_n(d,nrmA,dbg);
	a=   104;b= 5;d=        20;t=     4;u= 1;nrmA=  -1684;check_d_n(d,nrmA,dbg);
	a=   114;b= 5;d=        40;t=     6;u= 1;nrmA= -12004;check_d_n(d,nrmA,dbg);
	a=   128;b= 5;d=        32;t=     6;u= 1;nrmA=  -3616;check_d_n(d,nrmA,dbg);
	a=   274;b= 5;d=       125;t=    11;u= 1;nrmA=  -3049;check_d_n(d,nrmA,dbg);
	a=   288;b= 5;d=       629;t=    25;u= 1;nrmA=-310181;check_d_n(d,nrmA,dbg);
	a=   338;b= 5;d=       629;t=    25;u= 1;nrmA=-278881;check_d_n(d,nrmA,dbg);
	a=   964;b= 5;d=      3485;t=    59;u= 1;nrmA=-1248829;check_d_n(d,nrmA,dbg);

	\\ u=2
	a=    25;b= 5;d=         2;t=     2;u= 2;nrmA=   -625;check_d_n(d,nrmA,dbg);
	a=    32;b= 5;d=         2;t=     2;u= 2;nrmA=   -226;check_d_n(d,nrmA,dbg);
	a=    50;b= 5;d=         8;t=     6;u= 2;nrmA=  -2500;check_d_n(d,nrmA,dbg);
	a=    52;b= 5;d=         5;t=     4;u= 2;nrmA=   -421;check_d_n(d,nrmA,dbg);
	a=    57;b= 5;d=        10;t=     6;u= 2;nrmA=  -3001;check_d_n(d,nrmA,dbg);
	a=    64;b= 5;d=         8;t=     6;u= 2;nrmA=   -904;check_d_n(d,nrmA,dbg);

	\\ u=3
	a= 19696;b= 5;d=    666944;t=  2450;u= 3;nrmA=-28907584;check_d_n(d,nrmA,dbg);

	\\ u=4
	a=    25;b= 5;d=         2;t=     6;u= 4;nrmA=   -625;check_d_n(d,nrmA,dbg);
	a=    32;b= 5;d=         2;t=     6;u= 4;nrmA=   -226;check_d_n(d,nrmA,dbg);
	print("total b=5 time(ms)=",getwalltime()-startTime,"=",strtime(getwalltime()-startTime));
}

check_b6(dbg=0)={
	my(a,b,d,dbg,nrmA,startTime,t,u);

	dbg=1;
	startTime=getwalltime();
	\\ u=1
	a=    28;b= 6;d=         5;t=     1;u= 1;nrmA=  -5696;check_d_n(d,nrmA,dbg);
	a=    52;b= 6;d=         5;t=     1;u= 1;nrmA=  -3776;check_d_n(d,nrmA,dbg);
	a=    64;b= 6;d=         5;t=     1;u= 1;nrmA=  -2384;check_d_n(d,nrmA,dbg);
	a=    68;b= 6;d=         5;t=     1;u= 1;nrmA=  -1856;check_d_n(d,nrmA,dbg);
	a=    68;b= 6;d=         5;t=     3;u= 1;nrmA=  -1856;check_d_n(d,nrmA,dbg);
	a=    72;b= 6;d=         8;t=     2;u= 1;nrmA=  -5184;check_d_n(d,nrmA,dbg);
	a=    72;b= 6;d=        13;t=     3;u= 1;nrmA= -11664;check_d_n(d,nrmA,dbg);
	a=    74;b= 6;d=         5;t=     1;u= 1;nrmA=  -1004;check_d_n(d,nrmA,dbg);
	a=    76;b= 6;d=         5;t=     1;u= 1;nrmA=   -704;check_d_n(d,nrmA,dbg);
	a=    76;b= 6;d=         5;t=     3;u= 1;nrmA=   -704;check_d_n(d,nrmA,dbg);
	a=    79;b= 6;d=         5;t=     1;u= 1;nrmA=   -239;check_d_n(d,nrmA,dbg);
	a=    88;b= 6;d=         8;t=     2;u= 1;nrmA=  -2624;check_d_n(d,nrmA,dbg);
	a=   124;b= 6;d=        12;t=     4;u= 1;nrmA=   -176;check_d_n(d,nrmA,dbg);
	a=   128;b= 6;d=        20;t=     4;u= 1;nrmA=  -9536;check_d_n(d,nrmA,dbg);
	a=   128;b= 6;d=        85;t=     9;u= 1;nrmA= -93776;check_d_n(d,nrmA,dbg);
	a=   136;b= 6;d=        20;t=     4;u= 1;nrmA=  -7424;check_d_n(d,nrmA,dbg);
	a=   136;b= 6;d=        40;t=     6;u= 1;nrmA= -33344;check_d_n(d,nrmA,dbg);
	a=   144;b= 6;d=        32;t=     6;u= 1;nrmA= -20736;check_d_n(d,nrmA,dbg);
	a=   158;b= 6;d=        20;t=     4;u= 1;nrmA=   -956;check_d_n(d,nrmA,dbg);
	a=   160;b= 6;d=        96;t=    10;u= 1;nrmA= -98816;check_d_n(d,nrmA,dbg);
	a=   184;b= 6;d=        29;t=     5;u= 1;nrmA=  -3728;check_d_n(d,nrmA,dbg);
	a=   220;b= 6;d=       221;t=    15;u= 1;nrmA=-238016;check_d_n(d,nrmA,dbg);
	a=   248;b= 6;d=        53;t=     7;u= 1;nrmA=  -7184;check_d_n(d,nrmA,dbg);
	a=   280;b= 6;d=        68;t=     8;u= 1;nrmA=  -9728;check_d_n(d,nrmA,dbg);
	a=   304;b= 6;d=        85;t=     9;u= 1;nrmA= -17744;check_d_n(d,nrmA,dbg);
	a=   328;b= 6;d=        96;t=    10;u= 1;nrmA= -16832;check_d_n(d,nrmA,dbg);
	a=   397;b= 6;d=       125;t=    11;u= 1;nrmA=  -4391;check_d_n(d,nrmA,dbg);
	a=   440;b= 6;d=       221;t=    15;u= 1;nrmA= -92816;check_d_n(d,nrmA,dbg);
	a=   535;b= 6;d=       221;t=    15;u= 1;nrmA=   -191;check_d_n(d,nrmA,dbg);
	a=   535;b= 6;d=       229;t=    15;u= 1;nrmA= -10559;check_d_n(d,nrmA,dbg);
	a=   928;b= 6;d=       672;t=    26;u= 1;nrmA=  -9728;check_d_n(d,nrmA,dbg);
	a=  2432;b= 6;d=      4628;t=    68;u= 1;nrmA= -83264;check_d_n(d,nrmA,dbg);

	\\ u=2
	a=    36;b= 6;d=         2;t=     2;u= 2;nrmA=  -1296;check_d_n(d,nrmA,dbg);
	a=    44;b= 6;d=         2;t=     2;u= 2;nrmA=   -656;check_d_n(d,nrmA,dbg);
	a=    62;b= 6;d=         3;t=     4;u= 2;nrmA=    -44;check_d_n(d,nrmA,dbg);
	a=    64;b= 6;d=         5;t=     4;u= 2;nrmA=  -2384;check_d_n(d,nrmA,dbg);
	a=    68;b= 6;d=         5;t=     4;u= 2;nrmA=  -1856;check_d_n(d,nrmA,dbg);
	a=    68;b= 6;d=        10;t=     6;u= 2;nrmA=  -8336;check_d_n(d,nrmA,dbg);
	a=    72;b= 6;d=         8;t=     6;u= 2;nrmA=  -5184;check_d_n(d,nrmA,dbg);
	a=    79;b= 6;d=         5;t=     4;u= 2;nrmA=   -239;check_d_n(d,nrmA,dbg);
	a=    80;b= 6;d=        24;t=    10;u= 2;nrmA= -24704;check_d_n(d,nrmA,dbg);
	a=   140;b= 6;d=        17;t=     8;u= 2;nrmA=  -2432;check_d_n(d,nrmA,dbg);
	a=   164;b= 6;d=        24;t=    10;u= 2;nrmA=  -4208;check_d_n(d,nrmA,dbg);
	a=   464;b= 6;d=       168;t=    26;u= 2;nrmA=  -2432;check_d_n(d,nrmA,dbg);
	a=  1216;b= 6;d=      1157;t=    68;u= 2;nrmA= -20816;check_d_n(d,nrmA,dbg);

	\\ u=4
	a=    36;b= 6;d=         2;t=     6;u= 4;nrmA=  -1296;check_d_n(d,nrmA,dbg);
	a=    40;b= 6;d=         6;t=    10;u= 4;nrmA=  -6176;check_d_n(d,nrmA,dbg);
	a=    82;b= 6;d=         6;t=    10;u= 4;nrmA=  -1052;check_d_n(d,nrmA,dbg);
	a=   232;b= 6;d=        42;t=    26;u= 4;nrmA=   -608;check_d_n(d,nrmA,dbg);

	\\ u=5
	a=   656;b= 6;d=       384;t=    98;u= 5;nrmA= -67328;check_d_n(d,nrmA,dbg);

	\\ u=10
	a=   328;b= 6;d=        96;t=    98;u=10;nrmA= -16832;check_d_n(d,nrmA,dbg);

	\\ u=20
	a=   164;b= 6;d=        24;t=    98;u=20;nrmA=  -4208;check_d_n(d,nrmA,dbg);

	\\ u=40
	a=    82;b= 6;d=         6;t=    98;u=40;nrmA=  -1052;check_d_n(d,nrmA,dbg);
	print("total b=6 time(ms)=",getwalltime()-startTime,"=",strtime(getwalltime()-startTime));
}

check_b7(dbg=0)={
	my(a,b,d,dbg,nrmA,startTime,t,u);

	dbg=1;
	startTime=getwalltime();
	\\ u=1
	a=     2;b= 7;d=         8;t=     2;u= 1;nrmA= -19204;check_d_n(d,nrmA,dbg);
	a=    49;b= 7;d=         8;t=     2;u= 1;nrmA= -16807;check_d_n(d,nrmA,dbg);
	a=    98;b= 7;d=         8;t=     2;u= 1;nrmA=  -9604;check_d_n(d,nrmA,dbg);
	a=   107;b= 7;d=         5;t=     1;u= 1;nrmA=   -556;check_d_n(d,nrmA,dbg);
	a=   111;b= 7;d=        13;t=     3;u= 1;nrmA= -18892;check_d_n(d,nrmA,dbg);
	a=   114;b= 7;d=         8;t=     2;u= 1;nrmA=  -6212;check_d_n(d,nrmA,dbg);
	a=   136;b= 7;d=         8;t=     2;u= 1;nrmA=   -712;check_d_n(d,nrmA,dbg);
	a=   192;b= 7;d=       148;t=    12;u= 1;nrmA=-318484;check_d_n(d,nrmA,dbg);
	a=   196;b= 7;d=        32;t=     6;u= 1;nrmA= -38416;check_d_n(d,nrmA,dbg);
	a=   388;b= 7;d=        68;t=     8;u= 1;nrmA= -12724;check_d_n(d,nrmA,dbg);
	a=   638;b= 7;d=       173;t=    13;u= 1;nrmA=  -8329;check_d_n(d,nrmA,dbg);
	a=   784;b= 7;d=       480;t=    22;u= 1;nrmA=-537824;check_d_n(d,nrmA,dbg);
	a=   828;b= 7;d=       293;t=    17;u= 1;nrmA= -17909;check_d_n(d,nrmA,dbg);
	a=  1152;b= 7;d=      2405;t=    49;u= 1;nrmA=-4447301;check_d_n(d,nrmA,dbg);
	a=  5584;b= 7;d=     12992;t=   114;u= 1;nrmA= -12736;check_d_n(d,nrmA,dbg);
	a=  9112;b= 7;d=     34592;t=   186;u= 1;nrmA= -26848;check_d_n(d,nrmA,dbg);

	\\ u=2
	a=     1;b= 7;d=         2;t=     2;u= 2;nrmA=  -4801;check_d_n(d,nrmA,dbg);
	a=    49;b= 7;d=         2;t=     2;u= 2;nrmA=  -2401;check_d_n(d,nrmA,dbg);
	a=    57;b= 7;d=         2;t=     2;u= 2;nrmA=  -1553;check_d_n(d,nrmA,dbg);
	a=    68;b= 7;d=         2;t=     2;u= 2;nrmA=   -178;check_d_n(d,nrmA,dbg);
	a=    96;b= 7;d=        37;t=    12;u= 2;nrmA= -79621;check_d_n(d,nrmA,dbg);
	a=    98;b= 7;d=         8;t=     6;u= 2;nrmA=  -9604;check_d_n(d,nrmA,dbg);
	a=   194;b= 7;d=        17;t=     8;u= 2;nrmA=  -3181;check_d_n(d,nrmA,dbg);
	a=   392;b= 7;d=       120;t=    22;u= 2;nrmA=-134456;check_d_n(d,nrmA,dbg);
	a=  2792;b= 7;d=      3248;t=   114;u= 2;nrmA=  -3184;check_d_n(d,nrmA,dbg);
	a=  4556;b= 7;d=      8648;t=   186;u= 2;nrmA=  -6712;check_d_n(d,nrmA,dbg);

	\\ u=4
	a=    49;b= 7;d=         2;t=     6;u= 4;nrmA=  -2401;check_d_n(d,nrmA,dbg);
	a=   196;b= 7;d=        30;t=    22;u= 4;nrmA= -33614;check_d_n(d,nrmA,dbg);
	a=  1396;b= 7;d=       812;t=   114;u= 4;nrmA=   -796;check_d_n(d,nrmA,dbg);
	a=  2278;b= 7;d=      2162;t=   186;u= 4;nrmA=  -1678;check_d_n(d,nrmA,dbg);

	\\ u=8
	a=   698;b= 7;d=       203;t=   114;u= 8;nrmA=   -199;check_d_n(d,nrmA,dbg);
	print("total b=7 time(ms)=",getwalltime()-startTime,"=",strtime(getwalltime()-startTime));
}