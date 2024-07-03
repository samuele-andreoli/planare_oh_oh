getDpoly:=function(R,i)
	x:=R.1;
	F:=BaseRing(R);
	p:=Characteristic(F);
	n:=Degree(F);
	if not IsDivisibleBy(n,2) then
	return [];
	end if;
	m:=n div 2;
	q:=p^m;
	t:=x^q-x;
	L:=(8)^(-1) *(x^(p^i)-x);
	f:=Evaluate(L,t^2)+(x^2/2);
	return (f mod (x^(p^n)-x));
end function;

//a is such that a=b^q-b for b not in GF(q)
getCGpoly:=function(R,a)
	x:=R.1;
	F:=BaseRing(R);
	p:=Characteristic(F);
	n:=Degree(F);
	if p ne 3 or not IsDivisibleBy(n,2) then
	return [];
	end if;
	m:=n div 2;
	q:=p^m;
	t:=x^q-x;
	L:=-x^9- a*x^3 +(1-a^4)*x;
	f:=Evaluate(L,t^2)+(x^2/2);
	return (f mod (x^(p^n)-x));
end function;

//a is such that a=b^q-b for b not in GF(q)
getGpoly:=function(R,a)
	x:=R.1;
	F:=BaseRing(R);
	p:=Characteristic(F);
	n:=Degree(F);
	if p ne 3 or not IsDivisibleBy(n,2) then
	return [];
	end if;
	m:=n div 2;
	q:=p^m;
	t:=x^q-x;
	L:= -a^(-5)*x^3 + x;
	D:=-a^(-10) *x^10;
	f:=Evaluate(L,t^2)+Evaluate(D,t)+(x^2/2);
	return (f mod (x^(p^n)-x));
end function;

//a is such that a=b^q-b for b not in GF(q)
getPWpoly:=function(R,a)
	x:=R.1;
	F:=BaseRing(R);
	p:=Characteristic(F);
	n:=Degree(F);
	if [p,n] ne [3,10] then
	return [];
	end if;
	m:=n div 2;
	q:=p^m;
	t:=x^q-x;
	L:=-(a^(-53)*x^27 +a^(-18) *x^9 -x);
	f:=Evaluate(L,t^2)+(x^2/2);
	return (f mod (x^(p^n)-x));
end function;
