AttachSpec("EarlierCode/magma.spec");
Attach("Modular.m"); 

/*  
    The following is the list of all congruence subgroups of SL(2,Z), up to conjugacy in GL(2,Z),
    that contain -I, have genus at least 3, and have gonality 2.  They are given by their 
    Cummins-Pauli label.  Congruence subgroups of genus 1 and 2 always have gonality 2.
*/
gonality_equals_2:=[ "8B3", "10B3", "12C3", "12D3", "12E3", "12F3", "12G3", "12H3", "12K3", 
    "12L3", "14A3", "14C3", "14F3", "15F3", "15G3", "16B3", "16C3", "16D3", "16E3", "16F3", 
    "16I3", "16J3", "16M3", "16S3", "18A3", "18C3", "18F3", "18G3", "20C3", "20F3", "20G3", 
    "20H3", "20I3", "20J3", "20M3", "20O3", "21A3", "21B3", "21D3", "24A3", "24B3", "24C3", 
    "24G3", "24I3", "24K3", "24L3", "24M3", "24S3", "24U3", "24V3", "24W3", "28C3", "28E3", 
    "30B3", "30G3", "30J3", "30K3", "30L3", "32B3", "32C3", "32D3", "32H3", "32K3", "32M3", 
    "33C3", "34B3", "35A3", "36E3", "36F3", "36G3", "39A3", "40D3", "40E3", "40F3", "40I3", 
    "41A3", "42E3", "48C3", "48E3", "48F3", "48H3", "48I3", "48J3", "48M3", "50A3", "54A3", 
    "60C3", "60D3", "64A3", "96A3", "18B4", "25A4", "25D4", "32B4", "36C4", "42A4", "44B4", 
    "47A4", "48C4", "50A4", "50D4", "10A5", "14C5", "16G5", "18A5", "24A5", "24D5", "26A5", 
    "30C5", "30F5", "36A5", "36B5", "36H5", "40A5", "42A5", "44B5", "45A5", "45C5", "46A5", 
    "48A5", "48E5", "48F5", "48G5", "48H5", "50A5", "50D5", "50F5", "52B5", "54A5", "57A5", 
    "58A5", "59A5", "60A5", "96A5", "48A6", "71A6", "32E7", "48N7", "56B7", "64D7", "82B7", 
    "96A7", "93A8", "50A9", "50D9", "96B9", "48B11", "72A11", "96B11"];

/*  
    The following is the list of all congruence subgroups of SL(2,Z), up to conjugacy in GL(2,Z),
    that contain -I, have genus at least 5, and have gonality 3.  They are given by their 
    Cummins-Pauli label.  Congruence subgroups of genus 3 and 4 that do not have gonality 2
    have gonality 3.
*/
gonality_equals_3:=[ "54C5", "16A6", "18A6", "18D6", "24D6", "27A6", "28D6", "28E6", 
    "30C6", "32A6", "36C6", "36H6", "36J6", "36K6", "39A6", "45D6", "54A6", "54B6", "56D6", 
    "64A6", "84A6", "108A6", "27B7", "27C7", "30D7", "42M7", "24A8", "24B8", "36H8", "36I8", 
    "36J8", "36K8", "48A8", "48C8", "48E8", "72F8", "72G8", "84A8", "96A8", "108A8", "108B8", 
    "144A8", "15A10", "36A10", "36C10", "42G10", "72A10", "75A10", "108A10", "108C10", "108A12"];

/*  
    The following is the list of all congruence subgroups of SL(2,Z), up to conjugacy in GL(2,Z),
    that contain -I and for which the canonical model is isomorphic to a smooth plane quinitic. 
    They are given by their Cummins-Pauli label.  
*/
smooth_plane_quintic:=["75A6","75D6"];



function HasGonalityTwo(M : prec:=10)
    /*
        Input: 
            M - record that encodes a modular curve X_G with G an open subgroup of GL(2,Zhat) containing -I
        Output:
            A boolean that is "true" when the geometric gonality of X_G is 2 and "false" otherwise.

        "prec" is an optional parameter for the initial precision of q-expansions to consider.
    */

    g:=M`genus;
    if g eq 0 then return false; end if;  // gonality 1 case
    if g in {1,2} then return true; end if;  // always have gonality 2
    
    // Compute relevant cusp forms of weight 2 if not already computed
    if not assigned M`k or M`k ne 2 or not assigned M`F or not assigned M`prec then
        M:=FindModularForms(2,M);
        M:=FindCuspForms(M: lll:=[true,false]); 
    end if;

    prec:=Maximum(0,prec);
    
    repeat
        // Increase precision of cusp forms
        M:=IncreaseModularFormPrecision(M,prec);
        F:=[M`F0[i]: i in [1..M`dimSk]];

        // Find dimension of quadratic relations in F (given computed q-expansions)
        d:=FindRelationsOverKG(M,F,2 : lll:=false, dim_only:=true);

        if d lt ((g-1)*(g-2)) div 2 then
            // Too few relations to be hyperelliptic
            return  false;
        end if;

        if d eq ((g-1)*(g-2)) div 2 then
            // Perhaps it is hyperelliptic.  We actually compute the quadratic relations this time.
            I2,proved:=FindRelationsOverKG(M,F,2 : lll:=false , Proof:=true, k:=2);
            if #I2 eq ((g-1)*(g-2)) div 2 and proved then
                // enough terms of q-expansions have been computed to ensure we have found all quadratic relations
                return true;
            end if;
        end if;

        // Inconclusive so far, so we increase the precision and try again!
        prec:=prec+15;        
    until false;
end function;


function HasGonalityThree(M)
    /*
        Input: 
            M - record that encodes a modular curve X_G with G an open subgroup of GL(2,Zhat) containing -I
        Output:
            A boolean that is "true" when the geometric gonality of X_G is 3 and "false" otherwise.

            When X_G has genus 6 also returns a second boolean that is "true" if and only if X_G is
            geometrically isomorphic to a smooth plane quintic.
    */
    g:=M`genus;
    if g in {0,1,2} or (g le 11 and M`CPname in gonality_equals_2) then  
        //Detects cases where the gonality is 1 or 2.

        if g eq 6 then return false, false; end if;
        // If genus is 6 and gonality is 2, then it's not isomorphic to a smooth plane quintic
        // since the ideal of the canonical model is generated by the quadratic relations.
        
        return false;
    end if;
    
    // From Brill-Noether theory, the gonality is bounded by Floor((g+3)/2).
    // When the genus is 3 or 4, the gonality is at most 3 (and already we know it is not 1 or 2)    
    if g in {3,4} then 
        return true;
    end if;

    // Compute cusp forms of weight 2 
    M:=FindModularForms(2,M : lll:=[true,false], saturation:=[true,false]);
    M:=FindCuspForms(M: lll:=true, saturation:=true);


    prec:=Minimum([ (M`sl2level div M`widths[i])*M`prec[i] : i in [1..M`vinf]]);
    repeat
        // Increase precision of cusp forms
        time M:=IncreaseModularFormPrecision(M,prec);
        F:=[M`F0[i]: i in [1..M`dimSk]];

        // Find dimension of quadratic relations in F (given computed q-expansions)
        time d:=FindRelationsOverKG(M,F,2 : lll:=false, dim_only:=true);

        // Increase precision in case we have to try again
        prec:=prec+15;
    until d eq ((g-2)*(g-3)) div 2;

    KN:=CyclotomicField(M`N);
    ON:=RingOfIntegers(KN);
    R_ON:=PowerSeriesRing(ON);

    den:=LCM(&cat[[Denominator(a): a in Coefficients(f[i])]  :  f in F, i in [1..M`vinf]]);
    F:=[[den*a : a in f] : f in F];
    F:=[[R_ON!a : a in f] : f in F];


    /*  For the ideal I of the canonical model of our modular curve, we want to compute
        the dimension of the space of cubic relations generated by the quadratic relations.
        
        If the dimension is "Binomial(g+3-1,3)-(2*3-1)*(g-1)", which is the largest it can be,
        then our modular curve does not have gonality 3 and is not a smooth plane quintic.
        
        To make this more efficient, we first compute the related dimension modulo several small primes.
    */
    // We find the first 10 primes that split completely in KN
    primes:=[];
    p:=1;
    while #primes ne 10 do
        p:=p+M`N;
        if IsPrime(p) then
            primes:=primes cat [p];
        end if;
    end while;

    for p in primes do
        P:=Factorization(ideal<ON|[p]>)[1][1];
        FF,iota:=ResidueClassField(P);
        R_FF<q>:=PowerSeriesRing(FF);

        // Cusp forms modulo P
        F_P:=[ [&+[iota(Coefficient(f,n))*q^n: n in [0..AbsolutePrecision(f)-1]]+O(q^AbsolutePrecision(f))  : f in h] : h in F];

        // Compute the quadratic relations of these reductions of cusp forms
        Pol_FF<[x]>:=PolynomialRing(FF,g);
        mon:=MonomialsOfWeightedDegree(Pol_FF,2);
        mon_:=[ [Evaluate(m,[f[i]: f in F_P]) : i in [1..M`vinf]] : m in mon];
        prec:=[ Minimum([AbsolutePrecision(f[i]) : f in mon_]) : i in [1..M`vinf]];
        A:=[];
        for i in [1..M`vinf] do
            A:=A cat [ [Coefficient(f[i],j) : f in mon_] : j in [0..prec[i]-1] ];
        end for;
        A:=Matrix(A);
        basis:=[Eltseq(b): b in Basis(NullspaceOfTranspose(A))];
        I2:=[ &+[b[i]*mon[i]: i in [1..#mon]] : b in basis ];
        if #I2 ne ((g-2)*(g-3)) div 2 then continue p; end if;

        mon:=MonomialsOfWeightedDegree(Pol_FF,3);
        B:=Matrix([ [MonomialCoefficient(x[i]*f,m):m in mon] : f in I2, i in [1..g]]);
        time rankB:=Rank(B);
        if Rank(B) eq Binomial(g+3-1,3)-(2*3-1)*(g-1) then
            if g eq 6 then return false, false; end if;
            return false;
        end if;

    end for;

    // We now actually compute quadratic relations.
    I2:=FindRelationsOverKG(M,F,2 : lll:=false);  
        
    K:=M`KG;
    PolK<[x]>:=PolynomialRing(K,g);
    mon:=MonomialsOfWeightedDegree(PolK,3);
    I2:=[PolK!f: f in I2];

    A:=Matrix([ [MonomialCoefficient(x[i]*f,m): m in mon] : f in I2, i in [1..g] ]);    
    rankA:=Rank(A);    
    assert rankA in {Binomial(g+3-1,3)-(2*3-1)*(g-1), Binomial(g+3-1,3)-(2*3-1)*(g-1)-(g-3)};

    if rankA eq Binomial(g+3-1,3)-(2*3-1)*(g-1) then
        if g eq 6 then return false, false; end if;
        return false; 
    end if;        

    if g ne 6 then 
        return true;
    end if;

    // In the remaining case, our modular curve has genus 6 and either has gonality 3 
    // or is geometrically isomorphic to a smooth plane quintic.

    // We compute the canonical model and use a Magma function that actually computes the (geometric) gonality
    M:=FindCanonicalModel(M);
    P5:=ProjectiveSpace(M`KG,5);
    C:=Scheme(P5,M`psi);
    
    assert Dimension(C) eq 1; 
    // This ensures "FindCanonicalModel" is correct; the issue is our classification of gonality 3  
    // curves and smooth plane quintics is used by this function and we want to avoid a circular 
    // argument!  Note: if only quadratic relations were considered this scheme would have dimension 2 instead.

    C:=Curve(P5,M`psi);
    gonality,info:=Genus6GonalMap(C);
    // this will output the geometric gonality

    if gonality eq 3 then
        return true, false;
    end if;
    assert gonality eq 4;

    return false, true;
end function;



function IsBielliptic0(K,g,psi)
    /*
        Let K be a perfect field and let g>3 be an integer.   Suppose that psi is a minimal set 
        of generators for the ideal I(C) in K[x_1,..,x_g] of a canonical curve C in P^{g-1}_K 
        of genus g.

        The function returns a boolean which is true if and only if C is geometrically bielliptic.

        When K is finite, a second boolean is also returned.  Suppose that C is obtained as good 
        reduction from a canonical curve C' in P^{g-1}_F over some number field F; assume further
        that there is a mininmal set of generators of the ideal I(C') so that reduction induces
        a bijection with psi.  If the second boolean returned is true, then C' is geometrically
        bielliptic.  If it is false, no conclusion is made.
    */
    assert g gt 3;

    psi2:=[f: f in psi | Degree(f) eq 2];
    psi3:=[f: f in psi | Degree(f) eq 3];
    assert #psi eq #psi2 + #psi3;

    if g ge 5 and #psi3 ne 0 then
        return false, false;
        //Castelnuovo–Severi inequality implies that a curve of genus at least 5 cannot be bielliptic and trigonal
        //TODO: plane quintic case
    end if;

    // With our assumptions, any degree 2 morphism from C to a genus 1 curve will arise
    // by projecting P^{g-1} from a unique point a not in C.
    // We construct the scheme whose points will contain all such a.
    Pol1<[a]>:=PolynomialRing(K,g);
    Pol2<[x]>:=PolynomialRing(Pol1,g);
    PP:=[];
    for f in psi2 do
        // For each f in psi2, we compute the polynomial P(a,x) such that 
        //      f(a+x)=f(a)+P(a,x)+f(x)
        P:=Pol2!0;
        R:=Parent(f);
        for i,j in [1..g] do
            if i le j then
                v:=[0: k in [1..g]];
                v[i]:=v[i]+1; 
                v[j]:=v[j]+1;
                P:=P + MonomialCoefficient(f,Monomial(R,v))*(x[i]*a[j]+a[i]*x[j]);
            end if;
        end for;
        PP:=PP cat [P];
    end for;

    if g ge 5 then
        // In this case, psi consists only of quadratic polynomials.
        FF:=[Evaluate(f,[a[i]: i in [1..g]]): f in psi];
        d:=#FF;
        A:=[];
        for i in [1..d] do
        for j in [i+1..d] do
            A:=A cat Coefficients(PP[i]*FF[j]-PP[j]*FF[i]);
        end for;
        end for;

        R:=PolynomialRing(K,g);
        A:=[R!g: g in A];

        I:=ideal<R|[R!f: f in psi]>;
        J0:=ideal<R|A>;
        J:=IdealQuotient(J0,I); 
        J:=Radical(J);

        PP:=ProjectiveSpace(K,g-1);
        V:=Scheme(PP,Basis(J));
        if IsEmpty(V) then
            return false, false;
        end if;

        assert IsReduced(V);
        if IsFinite(K) then
            // Check using Hensel's lemma like construction if the point a lifts to characteristic 0.
            for c in IrreducibleComponents(V) do
                F:=RandomExtension(K,Degree(c));
                PolF<[y]>:=PolynomialRing(F,g-1);
                c_:=ChangeRing(c,F);
                for a_ in Points(c_) do
                    a:=Eltseq(a_);
                    assert exists(i0){i: i in [1..g] | a[i] ne 0};
                    a:=[a[i]/a[i0]: i in [1..g]];  
                    yy:=[a[i]+y[i]: i in [1..g] | i lt i0] cat [1] cat [a[i]+y[i-1]: i in [1..g] | i gt i0];
                    A_:=[Evaluate(f,yy): f in A];

                    B:=[ [MonomialCoefficient(h,y[i]): i in [1..g-1]] : h in A_];
                    B:=Matrix(B);
                    if Rank(B) eq Ncols(B) then
                        return true, true;
                    end if;
                end for;  
            end for;      
        end if;
        return true,false;
    end if;

    if g eq 4 then
        // In this case, psi will consist of one quadratic polynomial and one cubic polynomial.
        assert #psi2 eq 1 and #psi3 eq 1;
        f:=psi2[1];        
        h:=psi3[1];
        assert Degree(f) eq 2 and Degree(h) eq 3;
        P:=PP[1];

        // We compute the polynomials Q(a,x) and R(a,x) such that 
        //      h(u*a+v*x)=u^3*h(a)+u^2*v*Q(a,x)+u*v^2*R(a,x)+v^3*h(x)
        hx:=Evaluate(h,[x[i]: i in [1..g]]);
        ha:=Evaluate(h,[a[i]: i in [1..g]]);
        hh:=Evaluate(h,[a[i]+x[i]: i in [1..g]]);
        Q:=&+[MonomialCoefficient(hh,x[i])*x[i] : i in [1..g]];
        R:=&+[MonomialCoefficient(hh,x[i]*x[j])*x[i]*x[j] : i,j in [1..g] | i le j];
        assert hh eq ha+Q+R+hx;
        fa:=Evaluate(f,[a[i]: i in [1..g]]);
        fx:=Evaluate(f,[x[i]: i in [1..g]]);

        // Case where f(a)=0
        // (Here a could lie on the surface cut out by the quadratic relation but not on the curve)
        A:=Coefficients(P) cat [fa];
        Delta:=Q^2-4*Evaluate(h,[a[i]: i in [1..g]])*R;
        mon:=Monomials(fx)[1];
        A:=A cat Coefficients(Delta-MonomialCoefficient(Delta,mon)/MonomialCoefficient(fx,mon)*fx);
        
        PolK:=PolynomialRing(K,g);
        J0:=ideal<PolK|[PolK!g: g in A]>;
        J0:=Radical(J0);
        I:=ideal<PolK|[PolK!f: f in psi]>;
        J:=IdealQuotient(J0,I);   
        if J ne PolK then
            PP:=ProjectiveSpace(K,g-1);
            V:=Scheme(PP,Basis(J));
            if IsFinite(K) eq false then
                return true, false;
            else    
                // Check using Hensel's lemma like construction if the point a lifts to characteristic 0.
                for c in [c:c in IrreducibleComponents(V)] do
                    F:=RandomExtension(K,Degree(c));
                    PolF<[y]>:=PolynomialRing(F,g-1);
                    c_:=ChangeRing(c,F);
                    for a_ in Points(c_) do
                        a:=Eltseq(a_);
                        assert exists(i0){i: i in [1..g] | a[i] ne 0};
                        a:=[a[i]/a[i0]: i in [1..g]];  
                        yy:=[a[i]+y[i]: i in [1..g] | i lt i0] cat [1] cat [a[i]+y[i-1]: i in [1..g] | i gt i0];
                        A_:=[Evaluate(f,yy): f in A];
                        B:=[ [MonomialCoefficient(h,y[i]): i in [1..g-1]] : h in A_];
                        B:=Matrix(B);
                        if Rank(B) eq Ncols(B) then
                            return true, true;
                        end if;
                    end for;  
                end for;
                return true, false;
            end if;         
        end if;

        // case where f(a) ne 0
        D:=P^2*ha-fa*P*Q+fa^2*R;
        mon:=Monomials(fx)[1];
        A:=Coefficients(D-MonomialCoefficient(D,mon)/MonomialCoefficient(fx,mon)*fx);
        A:=[PolK!g: g in A];
        PolK:=PolynomialRing(K,g);
        J0:=ideal<PolK|A>;
        J0:=Radical(J0);
        I:=ideal<PolK|[PolK!f: f in psi]>;
        J:=IdealQuotient(J0,I);  
        if J ne PolK then
            PP:=ProjectiveSpace(K,g-1);
            V:=Scheme(PP,Basis(J));
            assert IsReduced(V);
            if IsFinite(K) eq false then
                return true, false;
            else 
                // Check using Hensel's lemma like construction if the point a lifts to characteristic 0.
                for c in [c:c in IrreducibleComponents(V)] do
                    F:=RandomExtension(K,Degree(c));
                    PolF<[y]>:=PolynomialRing(F,g-1);
                    c_:=ChangeRing(c,F);
                    for a_ in Points(c_) do
                        a:=Eltseq(a_);
                        assert exists(i0){i: i in [1..g] | a[i] ne 0};
                        a:=[a[i]/a[i0]: i in [1..g]];  
                        yy:=[a[i]+y[i]: i in [1..g] | i lt i0] cat [1] cat [a[i]+y[i-1]: i in [1..g] | i gt i0];
                        A_:=[Evaluate(f,yy): f in A];                                                
                        B:=[ [MonomialCoefficient(h,y[i]): i in [1..g-1]] : h in A_];
                        B:=Matrix(B);
                        if Rank(B) eq Ncols(B) then
                            return true, true;
                        end if;
                    end for;  
                end for;
                return true, false;
            end if;         
        end if;

        return false, false;
    end if;
end function;

function HyperellipticCurveIsBielliptic(F)
    /*
        Suppose that F is a separable polynomial in K[x], with K a field whose
        characteristic is not 2, such that y^2=F(x) defines a hyperelliptic 
        curve C over K of genus 2 or 3.

        This function returns true if and only if C is geometrically bielliptic.
    */
    K:=BaseRing(Parent(F));
    assert IsSeparable(F) and Degree(F) ge 5 and Characteristic(K) ne 2;

    //"splitting";


    //if Characteristic(K) eq 0 then
    //    time SplittingField([F]);
    //end if;

    //K;
    K:=SplittingField(F);
    //time L,roots:=RootsInSplittingField(f);
    //L;

    //F:=ChangeRing(F,K);
    //"automorphisms";
        //C:=HyperellipticCurve(F);
        
        //A:=AutomorphismGroup(C);
        //#A;
        //return true;

    roots:=[[r[1],1]: r in Roots(ChangeRing(F,K))];
    if IsOdd(#roots) then 
        roots:=roots cat [[1,0]];
    end if;
    g:=(#roots-2) div 2;
    assert g in {2,3};

    P1:=ProjectiveSpace(K,1);

    for i1 in [1..#roots] do
    for i2 in [j: j in [1..#roots] | i1 lt j] do
    for i3 in [j: j in [1..#roots] | j notin {i1,i2}] do
    for i4 in [j: j in [1..#roots] | i3 lt j and j notin {i1,i2}] do

        v1:=Vector(roots[i1]);
        v2:=Vector(roots[i2]);
        V:=VectorSpaceWithBasis([v1,v2]);

        v3:=Vector(roots[i3]);
        v4:=Vector(roots[i4]);
        c3:=Coordinates(V,v3);
        c4:=Coordinates(V,v4);
        alpha:=c3[1]^(-1)*c4[2];
        beta:=c3[2]^(-1)*c4[1];

        A:=Transpose(Matrix([v1,v2]));
        B:=Transpose(Matrix([alpha*v2,beta*v1]));
        _,C:=IsConsistent(A,B);
        assert C*A eq B;
        Ct:=Transpose(C);
        assert v1*Ct eq alpha*v2; 
        assert v2*Ct eq beta*v1; 
        assert v3*Ct eq v4;
        
        S:={P1!Eltseq(Vector(r)*Ct): r in roots} diff {P1!r: r in roots};

        if IsEmpty(S) then
            return true;
        end if;

    end for;
    end for;
    end for;
    end for;

    return false;

end function;

function HyperellipticCurveIsBiellipticNew(f)
    /*
        FIX
        Suppose that f is a separable polynomial in K[x], with K a field whose
        characteristic is not 2, such that y^2=f(x) defines a hyperelliptic 
        curve C over K of genus 2 or 3.

        This function returns true if and only if C is geometrically bielliptic.
    */
    K:=BaseRing(Parent(f));
    PolK<x>:=PolynomialRing(K);
    f:=PolK!f;
    assert IsFinite(K) and Characteristic(K) ne 2;
    assert IsSeparable(f) and Degree(f) in {5,6,7,8};
    if IsOdd(Degree(f)) then
        while Evaluate(f,0) eq 0 do
            f:=Evaluate(f,x+Random(K));
            //fails for small K
        end while;
        d:=Degree(f)+1;
        f:=PolK!(x^d*Evaluate(f,1/x));
    end if;

    Pol1<a,b,c,d>:=PolynomialRing(K,4);

    Pol2<x>:=PolynomialRing(Pol1);

    f2:=Pol2!((c*x+d)^Degree(f)*Evaluate(f,(a*x+b)/(c*x+d)));
    eqns:=Coefficients(LeadingCoefficient(f2)*Evaluate(f,x) - LeadingCoefficient(f)*f2);
    eqns:=eqns cat [a^2+b*c-1, b*a+d*b, c*a+d*c, b*c+d^2-1];



    PolK<[y]>:=PolynomialRing(K,4);
    I:=ideal<PolK|[y[1]^2-1,y[1]-y[4],y[2],y[3]]>;
    J:=ideal<PolK|eqns>;
    J:=IdealQuotient(J,I); 
    J:=Radical(J);
    eqns:=Basis(J);
    
    if J eq PolK then return false; end if;

    AA:=AffineSpace(K,4);
    V:=Scheme(AA,Basis(J));
    for c in IrreducibleComponents(V) do
        F:=RandomExtension(K,Degree(c));
        PolF<[y]>:=PolynomialRing(F,4);
        c_:=ChangeRing(c,F);
        for a_ in Points(c_) do
            a:=Eltseq(a_);
            eqns_:=[Evaluate(h,[a[i]+y[i]: i in [1..4]]) : h in eqns];
            B:=[ [MonomialCoefficient(h,y[i]): i in [1..4]] : h in eqns_];
            B:=Matrix(B);
            if Rank(B) eq Ncols(B) then
                return true, true;
            end if;

            //assert exists(i0){i: i in [1..g] | a[i] ne 0};
            //a:=[a[i]/a[i0]: i in [1..g]];  
            //yy:=[a[i]+y[i]: i in [1..g] | i lt i0] cat [1] cat [a[i]+y[i-1]: i in [1..g] | i gt i0];
            //A_:=[Evaluate(f,yy): f in A];

            //B:=[ [MonomialCoefficient(h,y[i]): i in [1..g-1]] : h in A_];
            //B:=Matrix(B);
            //if Rank(B) eq Ncols(B) then
            //    return true, true;
            //end if;
        end for;  
    end for;

    assert false;
    return true;

    assert false;

    //"splitting";


    //if Characteristic(K) eq 0 then
    //    time SplittingField([F]);
    //end if;

    //K;
    K:=SplittingField(F);
    //time L,roots:=RootsInSplittingField(f);
    //L;

    //F:=ChangeRing(F,K);
    //"automorphisms";
        //C:=HyperellipticCurve(F);
        
        //A:=AutomorphismGroup(C);
        //#A;
        //return true;

    roots:=[[r[1],1]: r in Roots(ChangeRing(F,K))];
    if IsOdd(#roots) then 
        roots:=roots cat [[1,0]];
    end if;
    g:=(#roots-2) div 2;
    assert g in {2,3};

    P1:=ProjectiveSpace(K,1);

    for i1 in [1..#roots] do
    for i2 in [j: j in [1..#roots] | i1 lt j] do
    for i3 in [j: j in [1..#roots] | j notin {i1,i2}] do
    for i4 in [j: j in [1..#roots] | i3 lt j and j notin {i1,i2}] do

        v1:=Vector(roots[i1]);
        v2:=Vector(roots[i2]);
        V:=VectorSpaceWithBasis([v1,v2]);

        v3:=Vector(roots[i3]);
        v4:=Vector(roots[i4]);
        c3:=Coordinates(V,v3);
        c4:=Coordinates(V,v4);
        alpha:=c3[1]^(-1)*c4[2];
        beta:=c3[2]^(-1)*c4[1];

        A:=Transpose(Matrix([v1,v2]));
        B:=Transpose(Matrix([alpha*v2,beta*v1]));
        _,C:=IsConsistent(A,B);
        assert C*A eq B;
        Ct:=Transpose(C);
        assert v1*Ct eq alpha*v2; 
        assert v2*Ct eq beta*v1; 
        assert v3*Ct eq v4;
        
        S:={P1!Eltseq(Vector(r)*Ct): r in roots} diff {P1!r: r in roots};

        if IsEmpty(S) then
            return true;
        end if;

    end for;
    end for;
    end for;
    end for;

    return false;

end function;

function IsBielliptic1(M)
    /*  
        Let M be a modular curve that is geometrically hyperelliptic and has genus 2 or 3.
        This function returns true if and only if M is geometrically bielliptic.
    */
    g:=M`genus;
    assert g in {2,3};
    if g eq 3 then 
        assert M`CPname in gonality_equals_2;
    end if;

    N:=M`N;
    KN:=CyclotomicField(N);
    R<q>:=LaurentSeriesRing(KN);

    // We first construct a hyperelliptic model of the modular curve M
    // that is defined over KN by using one of the cusps.

    M:=FindCanonicalModel(M);
    _,k:=Maximum(M`widths);
    prec:=[0:i in [1..M`vinf]];
    prec[k]:=2*g+2+20;  //20? TODO
    M:=IncreaseModularFormPrecision(M,prec);
    prec:=M`prec;
    A:=Matrix([ [Coefficient(M`F0[i][k],n) : n in [0..prec[k]-1]] : i in [1..g] ]);
    assert Rank(A) eq g;
    B,U:=EchelonForm(A);
    assert B eq U*A;
    
    // Two cusp forms over KN given at single cusp
    F:=[ &+[U[j,i]*M`F0[i][k] : i in [1..g]]  : j in [1..g]];

    w1:=R!F[g-1]/q;
    w2:=R!F[g]/q;
    // Divide by q since we want to view them as differential forms (with an implicit dq)

    x:=w1/w2;
    dx:=&+[Coefficient(x,n)*n*q^(n-1): n in [Valuation(x)..AbsolutePrecision(x)-1]] + O(q^(AbsolutePrecision(x)-1));   // up to scalar multiple
    y:=dx/w2;

    // We should now have y^2=F(x) for a unique polynomial F of degree at most 2g+2; this is a hyperelliptic model of M over KN.    
    e:=Valuation(x);
    y2:=y^2;
    coeff:=[];
    for i in Reverse([0..2*g+2]) do
        c:=Coefficient(y2,i*e)/LeadingCoefficient(x)^i;
        y2:=y2-c*x^i;
        coeff:=[c] cat coeff;
    end for;
    PolKN<u>:=PolynomialRing(KN);
    F:=&+[coeff[i]*u^(i-1):i in [1..#coeff]];
    assert IsSeparable(F);
    assert IsWeaklyZero(Evaluate(F,x)-y^2); //check

    den:=LCM([Denominator(c): c in Coefficients(F)]);
    F:=den^2*F; // scale by a square so that coefficients are algebraic

    OO:=RingOfIntegers(KN);
    F:=ChangeRing(F,OO);
    bad:=2*Norm(Discriminant(F));

    // We find the first 50 primes that split completely in KN
    primes:=[];
    p:=1;
    while #primes ne 50 do
        p:=p+M`N;
        if IsPrime(p) then
            primes:=primes cat [p];
        end if;
    end while;

    for p in primes do
        P:=Factorization(ideal<OO|[p]>)[1][1];
        FF,iota:=ResidueClassField(P);
        PolFF<x>:=PolynomialRing(FF);
        F_P:=&+[iota(Coefficient(F,i))*x^i: i in [0..Degree(F)]];
        is_bielliptic_P:=HyperellipticCurveIsBielliptic(F_P);
        is_bielliptic_P_new:=HyperellipticCurveIsBiellipticNew(F_P);
        if not is_bielliptic_P then
            return false;
        end if;
    end for;


    //TODO: HARD CHECK

    //"bielliptic";
    //F:=ChangeRing(F,KN);
    //HyperellipticCurveIsBielliptic(F);
    

    return true;

    //B := [M`F0[i][k] : i in [1..g]];
	//C := HyperellipticModel(B);

        return true;

    assert false;

    /*
    C;
    return true;
	if Dimension(Ambient(C)) eq 3 then
		C := SimplifyGeometricHyperellipticCurve(C);
	end if;
	isH, H := IsHyperelliptic(C);
	if isH then
		H := ReducedMinimalWeierstrassModel(H);
		P2<X,Y,Z> := CoordinateRing(Ambient(H));
	end if;    
    H;
    return true;
    assert false;
    */
    
    M1:=CreateModularCurveRec(M`G);
    M1:=FindModelOfXG(M1);
    
    C:=Curve(ProjectiveSpace(M`KG,3),M1`psi);
    
    assert false;

    return true; //TODO:  HARD CHECK
    assert false;

    /*
    M:=FindModularFormsWithVanishingConditions(M,mult);


    FF:=[];
    repeat 
        M:=FindModularFormsWithVanishingConditions(M,mult);
        FF:=FF cat [ M`F0 ];
        multi[j]:=mult[j]+1;
    until #M`F0 eq 0;


    [#F: F in FF];
    */

    assert false;
    return false;
end function;

function IsBielliptic(X)
    /* 
        The input is a modular curve X that has genus at least 3 and is not
        geometrically hyperelliptic.

        The function determines whether X is bielliptic over some extension of X`KG.
    */
    g:=X`genus;

    if g eq 2 or (g eq 3 and X`CPname in gonality_equals_2) then
        return IsBielliptic1(X);
    end if;

    assert g ge 3;
    assert g gt 24 or X`CPname notin gonality_equals_2; // Assuming X is not geometrically hyperelliptic

    if not assigned X`psi or not assigned X`k or X`k ne 2 or Set(X`mult) ne {1} then
        X:=FindCanonicalModel(X);
    end if;

    if g eq 3 then
        // When the genus is 3 and the curve is not hyperelliptic, we search directly for a bielliptic involution.
        assert #X`psi eq 1 and Degree(X`psi[1]) eq 4;

        // We now search for all bielliptic involutions of X_G.
        // They are given by a 3x3 matrix A=[a1,a2,a3; a4,a5,a6; a7,a8,a9], acting on the projective
        // space containing the canonical model, such that A^2=1 and tr(A)=-1.
        Pol<[a]>:=PolynomialRing(X`KG,9);
        Pol2<[x]>:=PolynomialRing(Pol,3);
        c:=[a[1]^2+a[4]*a[2]+a[7]*a[3]-1, a[2]*a[1]+a[5]*a[2]+a[8]*a[3], a[3]*a[1]+a[6]*a[2]+a[9]*a[3], 
            a[4]*a[1]+a[5]*a[4]+a[7]*a[6], a[4]*a[2]+a[5]^2+a[8]*a[6]-1, a[4]*a[3]+a[6]*a[5]+a[9]*a[6],
            a[7]*a[1]+a[8]*a[4]+a[9]*a[7], a[7]*a[2]+a[8]*a[5]+a[9]*a[8], a[7]*a[3]+a[8]*a[6]+a[9]^2-1];
        c:=c cat [a[1]+a[5]+a[9]+1];
        F:=X`psi[1];
        h:=Evaluate(F,[a[1]*x[1]+a[2]*x[2]+a[3]*x[3],a[4]*x[1]+a[5]*x[2]+a[6]*x[3], a[7]*x[1]+a[8]*x[2]+a[9]*x[3]])
           -Evaluate(F,[x[1],x[2],x[3]]);
        c:=c cat Coefficients(h);
        V:=Scheme(AffineSpace(X`KG,9),c);
        if IsEmpty(V) eq false then
            // bielliptic involutions exist!
            assert IsReduced(V);            
            return true;
        else
            return false;
        end if;
    end if;


    OO:=RingOfIntegers(X`KG);   

    // Coerce X`psi to have coefficients in OO and keep track of coefficients so we can reduce them modulo P.
    PolOO:=PolynomialRing(OO,g);
    psi:=[PolOO!f: f in X`psi];
    coeff:=[Coefficients(f): f in psi];
    exp:=[[Exponents(m): m in Monomials(f)]: f in psi];

    // An integer whose prime divisors we will avoid while searching for prime ideals of OO for which the
    // canonical model of X has good reduction.
    bad:=X`N;

    // We convert our cusp forms and their q-expansions into a matrix over the integers.
    A:=Matrix([ &cat[&cat[Eltseq(Coefficient(f[i],j)) : j in [0..X`prec[i]-1]]:i in [1..X`vinf]] : f in X`F0]);
    
    den:=Denominator(A);  
    bad:=bad*den;
    A:=ChangeRing(den*A,Integers());
    bad:=bad* &*ElementaryDivisors(A);

    F0:=[X`F0[i]: i in [1..g]];
    B:=Matrix([ &cat[&cat[Eltseq(Coefficient(u*f[i],j)) : j in [0..X`prec[i]-1]]:i in [1..X`vinf]] : f in F0, u in X`KG_integral_basis_cyclotomic]);
    B:=ChangeRing(den*B,Integers());
    V:=RowSpace(A);
    W:=sub<V|Rows(B)>;
    bad:=bad * #quo<V|W>;

    // We now look for primes P of OO for which the canonical model has good reduction and check if the reduction is bielliptic
    bad:=PrimeDivisors(bad);
    primes:=[p: p in PrimesUpTo(500) | p notin bad]; // These will be enough primes in any practical case
    size:=[ #ResidueClassField(Factorization(ideal<OO|[p]>)[1][1] ) : p in primes ]; 
    ParallelSort(~size,~primes); // order primes by size of residue fields for OO.
    primes:=[primes[i]: i in [1..20]];

    for p in primes do
        P:=Factorization(ideal<OO|[p]>)[1][1];
        FF,iota:=ResidueClassField(P);
        
        //reduce coefficents modulo P
        PolFF<[x]>:=PolynomialRing(FF,g);
        psi_P:=[ &+[iota(coeff[k][i])*&*[x[j]^exp[k][i][j]: j in [1..g]]  : i in [1..#coeff[k]]]  : k in [1..#psi] ];
        psi2_P:=[f: f in psi_P | Degree(f) eq 2];
        psi3_P:=[f: f in psi_P | Degree(f) eq 3];
        if #psi_P ne #psi2_P + #psi3_P then 
            continue p;
        end if;

        // Want quadratic relations in psi to still be independent modulo P
        mon:=MonomialsOfWeightedDegree(PolFF,2);
        A:=[[MonomialCoefficient(f,m):m in mon] : f in psi2_P];
        if Rank(Matrix(A)) ne Binomial(g+2-1,2)-(2*2-1)*(g-1) then
            continue p;
        end if;

        // Want cubic relations coming from psi modulo P to have same dimension
        mon:=MonomialsOfWeightedDegree(PolFF,3);
        A:=[[MonomialCoefficient(f,m):m in mon] : f in [f*x[i]: f in psi2_P, i in [1..g]]];
        if  (#psi3_P eq 0 and Rank(Matrix(A)) ne Binomial(g+3-1,3)-(2*3-1)*(g-1)) or
            (#psi3_P ne 0 and Rank(Matrix(A)) ne Binomial(g+3-1,3)-(2*3-1)*(g-1)-(g-3)) then
            continue p;
        end if;
        if #psi3_P ne 0 then
            A:=[[MonomialCoefficient(f,m):m in mon] : f in [f*x[i]: f in psi2_P, i in [1..g]] cat psi3_P];
            if Rank(Matrix(A)) ne Binomial(g+3-1,3)-(2*3-1)*(g-1) then
                continue p; 
            end if;
        end if;
        
        KN:=BaseRing(Parent(X`F[1][1])); // our q-expansions will have values in this field; X`KG is a subfield
        KN:=CyclotomicField(X`N);
        ON:=RingOfIntegers(KN);
        PN:=Factorization(ideal<ON|Generators(P)>)[1][1];
        FF_,iota_:=ResidueClassField(PN);
        
        // Check that there are still the same number of linearly independent quadratic relations modulo P.
        // Note that this can fail if the reduction of X modulo P is hyperelliptic.
        F0:=[[den*f: f in X`F0[i]]: i in [1..g]];
        mon:=MonomialsOfWeightedDegree(PolynomialRing(Integers(),g),2);
        Q:=[];
        for m in mon do
            m_F0:=[ Evaluate(m,[f[i]: f in F0]) : i in [1..X`vinf] ];
            v:=&cat[ [ iota_(ON!Coefficient(m_F0[i],j)) : j in [0..X`prec[i]-1] ] : i in [1..X`vinf] ];
            Q:=Q cat [v];
        end for;
        Q:=Matrix(Q);
        // TODO: Over FF_ and not FF now
        d:=Nrows(Q)-Rank(Q);        
        if d ne Binomial(g+2-1,2)-(2*2-1)*(g-1) then
            continue p;
        end if;

        I_P:=ideal<PolFF|psi_P>;

        // We check the Hilbert polynomial (not needed but quick reality check)
        PolQ<xx>:=PolynomialRing(Rationals());
        HP:=PolQ!HilbertPolynomial(I_P);
        assert HP eq (2*g-2)*xx-g+1;
        
        is_bielliptic_P, proof :=IsBielliptic0(FF,g,psi_P);
        if is_bielliptic_P eq false then
            return false;
        end if;

        if is_bielliptic_P and proof then
            return true;
        end if;
        
    end for;

    // Reducing modulo prime has not definitively determined if X is bielliptic or not.
    // We now check directly.

    return IsBielliptic0(X`KG,X`genus,X`psi);
end function;
