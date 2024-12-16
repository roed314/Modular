
/* 
    This is the list of all congruence subgroups of SL(2,Z), up to conjugacy in GL(2,Z), that contains -I, 
    have genus at least 5, and have gonality 3.
    
    From Brill-Noether theory, TODO: or extend list....  
    
    
    These groups are given by their Cummins-Pauli label.

    This code check that the list indeed has these properties!
*/

gonality_equals_3:=[ "54C5", "16A6", "18A6", "18D6", "24D6", "27A6", "28D6", "28E6", 
    "30C6", "32A6", "36C6", "36H6", "36J6", "36K6", "39A6", "45D6", "54A6", "54B6", "56D6", 
    "64A6", "84A6", "108A6", "27B7", "27C7", "30D7", "42M7", "24A8", "24B8", "36H8", "36I8", 
    "36J8", "36K8", "48A8", "48C8", "48E8", "72F8", "72G8", "84A8", "96A8", "108A8", "108B8", 
    "144A8", "15A10", "36A10", "36C10", "42G10", "72A10", "75A10", "108A10", "108C10", "108A12"];


AttachSpec("EarlierCode/magma.spec");
Attach("Modular.m"); 
load "hyperelliptic.m";

// load Cummins-Pauli data
filename:="CPdata/CPdata.dat";  
I:=Open(filename, "r"); 
_,cp_data:=ReadObjectCheck(I); 

// We have already computed the congruence subgroups of gonality at most 2 //TODO: hard code
gonality2:=[ "8B3", "10B3", "12C3", "12D3", "12E3", "12F3", "12G3", "12H3", "12K3", 
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

gonality_at_most_2:=[r`name: r in cp_data | r`genus le 2 or r`name in gonality2];

total_time:=Realtime();


// list of congruence subgroups with gonality 3 found so far
gonality_at_most_3:=[];

for r in cp_data do
    // We check all congruence subgroups in Cummin-Pauli data
    //TODO: genus 25??

    if r`name in gonality_at_most_2 then
        gonality_at_most_3 cat:= [r`name];
        continue r; 
    end if;

    // From Brill-Noether theory, the gonality is bounded by Floor((g+3)/2).
    // When the genus is 3 or 4, the gonality is at most 3 (and we know it is not 1 or 2)
    if r`genus in {3,4} then
        gonality_at_most_3 cat:=[r`name];
        continue r;
    end if;

    if (r`level le 226 and r`index gt 287) or (r`level gt 226 and r`index gt 302) then
        // Our gonality bounds show that gonality is not 3
        continue r;
    end if;
        
    for p in [2,3,5,7] do
        if r`level mod p ne 0 and r`index gt 36*(p^2+1)/(p-1) then
            // Our gonality bounds show that gonality is not 3
            continue r;        
        end if;
    end for;


    for i in r`supergroups do
        s:=cp_data[i];
        // corresponds to a larger congruence subgroup

        // A curve of gonality 3 can only map to a curve of gonality at most 3 
        // Note that groups in "cp_data" are listed in terms of increasing genus, 
        // then increasing level, then increasing index.
        if s`name notin gonality_at_most_3 then
            continue r;
        end if;

        d1:=r`index div s`index; 
        if s`genus eq 0 and d1 eq 3 then
            // curve is a degree 3 cover of a modular curve of genus 0,
            // and hence gonality is 3 (since it not 1 or 2)
            gonality_at_most_3 cat:=[r`name];            
            continue r;           
        end if;

    end for;

    // We now check the Castelnuovo-Severi inequality using all strictly 
    // larger congruence subgroups.  We first find the set of I of these larger 
    // groups up to conjugacy in GL(2,Z).
    I_:=Set(r`supergroups);
    repeat
        I:=I_;
        I_:=I join &join[ Set(cp_data[i]`supergroups): i in I];
    until I eq I_;
    for i in I do
        s:=cp_data[i];
        d1:=r`index div s`index;
		g1:=s`genus;
		g :=r`genus;
        if g gt d1*g1+(d1-1)*2 then
            //Castelnuovo-Severi inequality fails if the gonality was 3
            continue r;
        end if;
    end for;

    /*  
        We now construct an open subgroup G of GL(2,Zhat) such that the intersection of G with 
        SL(2,Zhat) corresponds to the congruence subgroup.

        We find G so that the index of det(G) in Zhat^* is minimal and G has the same level
        as the congruence subgroup.
    */

    N:=r`level; 
    gens:=r`matgens;
    SL2:=SL2Ambient(N);
    GL2:=GL2Ambient(N);   
    H:=sub<SL2|gens>; 
    H`SL:=true;
    H`Index:=r`index;
    H`Genus:=r`genus;
    H`Order:=SL2Size(N) div H`Index;
 
    GG:=Normalizer(GL2,H);
    HH:=SL2Intersection(GG);
    GG`Order:=GL2Order(GG); 

    Q,iota:=quo<GG|H>;
    iotaHH:=iota(HH);
    MM:=[M`subgroup @@ iota: M in Subgroups(Q) | #(iotaHH meet M`subgroup) eq 1];
 
    min:=Minimum([GL2Index(M): M in MM]);
    MM:=[M: M in MM | GL2Index(M) eq min];
    G:=MM[1];
    assert SL2Intersection(G) eq H;
    assert GL2Level(G) eq N;

    " ",r`name;
    "[KG:Q]=",GL2DeterminantIndex(G); // TODO: remove

    "Create model";
    // Create the modular curve X_G
    time X:=CreateModularCurveRec(G); 

    // Checks whether gonality is 3
    b:=HasGonalityThree(X);
    if b then
        gonality_at_most_3 cat:=[r`name];
    end if;
    

end for;

// Check that our list matches agrees with the one computed!
for r in cp_data do
    if r`genus ge 5 then
        assert (r`name in gonality_at_most_3 and r`name notin gonality_at_most_2) eq r`name in gonality_equals_3;
    end if;
end for;


"Done";
"Total time:",Realtime(total_time);




/*

gonality_equals_3;
[ 7A3, 8A3, 9A3, 10A3, 10C3, 10D3, 11A3, 12A3, 12B3, 12I3, 12J3, 12M3, 12N3, 
12O3, 12P3, 13A3, 13B3, 13C3, 14B3, 14D3, 14E3, 15A3, 15B3, 15C3, 15D3, 15E3, 
15H3, 15I3, 16A3, 16G3, 16H3, 16K3, 16L3, 16N3, 16O3, 16P3, 16Q3, 16R3, 18B3, 
18D3, 18E3, 18H3, 18I3, 18J3, 18K3, 20A3, 20B3, 20D3, 20E3, 20K3, 20L3, 20N3, 
20P3, 20Q3, 20R3, 20S3, 20T3, 21C3, 24D3, 24E3, 24F3, 24H3, 24J3, 24N3, 24O3, 
24P3, 24Q3, 24R3, 24T3, 24X3, 24Y3, 24Z3, 24AA3, 24AB3, 24AC3, 26A3, 27A3, 27B3,
27C3, 28A3, 28B3, 28D3, 30A3, 30C3, 30D3, 30E3, 30F3, 30H3, 30I3, 32A3, 32E3, 
32F3, 32G3, 32I3, 32J3, 32L3, 32N3, 32O3, 32P3, 32Q3, 33A3, 33B3, 34A3, 34C3, 
36A3, 36B3, 36C3, 36D3, 36H3, 36I3, 36J3, 36K3, 40A3, 40B3, 40C3, 40G3, 40H3, 
40J3, 42A3, 42B3, 42C3, 42D3, 42F3, 43A3, 45A3, 45B3, 45C3, 45D3, 48A3, 48B3, 
48D3, 48G3, 48K3, 48L3, 49A3, 51A3, 52A3, 52B3, 54B3, 54C3, 55A3, 56A3, 56B3, 
56C3, 56D3, 60A3, 60B3, 64B3, 66A3, 72A3, 84A3, 9A4, 9B4, 9C4, 10A4, 10B4, 11A4,
12A4, 12B4, 12C4, 12D4, 14A4, 14B4, 15A4, 15B4, 15C4, 15D4, 15E4, 16A4, 16B4, 
16C4, 17A4, 17B4, 18A4, 18C4, 18D4, 18E4, 18F4, 18G4, 18H4, 18I4, 18J4, 18K4, 
18L4, 18M4, 18N4, 18O4, 18P4, 18Q4, 18R4, 18S4, 18T4, 20A4, 20B4, 20C4, 20D4, 
20E4, 21A4, 21B4, 21C4, 21D4, 21E4, 22A4, 22B4, 24A4, 24B4, 24C4, 24D4, 24E4, 
24F4, 24G4, 24H4, 24I4, 24J4, 24K4, 24L4, 24M4, 24N4, 24O4, 24P4, 24Q4, 24R4, 
24S4, 24T4, 25B4, 25C4, 25E4, 25F4, 25G4, 26A4, 26B4, 26C4, 27A4, 27B4, 27C4, 
27D4, 28A4, 28B4, 28C4, 28D4, 28E4, 28F4, 29A4, 30A4, 30B4, 30C4, 30D4, 30E4, 
30F4, 30G4, 30H4, 30I4, 32A4, 32C4, 33A4, 35A4, 35B4, 35C4, 36A4, 36B4, 36D4, 
36E4, 36F4, 36G4, 36H4, 36I4, 36J4, 36K4, 36L4, 36M4, 36N4, 36O4, 36P4, 36Q4, 
36R4, 36S4, 37A4, 37B4, 38A4, 38B4, 39A4, 39B4, 39C4, 40A4, 40B4, 40C4, 40D4, 
42B4, 42C4, 42D4, 42E4, 42F4, 42G4, 42H4, 42I4, 44A4, 44C4, 44D4, 45A4, 45B4, 
45C4, 46A4, 48A4, 48B4, 48D4, 48E4, 48F4, 48G4, 48H4, 48I4, 48J4, 50B4, 50C4, 
50E4, 50F4, 52A4, 53A4, 54A4, 54B4, 54C4, 54D4, 54E4, 55A4, 56A4, 56B4, 56C4, 
58A4, 60A4, 60B4, 60C4, 61A4, 62A4, 63A4, 65A4, 66A4, 70A4, 70B4, 70C4, 72A4, 
72B4, 72C4, 72D4, 72E4, 74A4, 75A4, 76A4, 77A4, 77B4, 78A4, 80A4, 81A4, 84A4, 
84B4, 90A4, 108A4, 54C5, 16A6, 18A6, 18D6, 24D6, 27A6, 28D6, 28E6, 30C6, 32A6, 
36C6, 36H6, 36J6, 36K6, 39A6, 45D6, 54A6, 54B6, 56D6, 64A6, 84A6, 108A6, 27B7, 
27C7, 30D7, 42M7, 24A8, 24B8, 36H8, 36I8, 36J8, 36K8, 48A8, 48C8, 48E8, 72F8, 
72G8, 84A8, 96A8, 108A8, 108B8, 144A8, 15A10, 36A10, 36C10, 42G10, 72A10, 75A10,
108A10, 108C10, 108A12 ]


*/