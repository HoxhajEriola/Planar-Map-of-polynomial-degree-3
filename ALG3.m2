

--    This program is free software: you can redistribute it and/or modify
--   it under the terms of the GNU General Public License as published by
--   the Free Software Foundation, either version 3 of the License, or
--   (at your option) any later version.

--    This program is distributed in the hope that it will be useful,
--   but WITHOUT ANY WARRANTY; without even the implied warranty of
--   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
--   GNU General Public License for more details.

--    You should have received a copy of the GNU General Public License
--   along with this program.  If not, see <http://www.gnu.org/licenses/>.


--"This file contains interactive macaulay2 code for computing";
--" planar map of polynomial of degree three" ;

needsPackage "Elimination"
needsPackage "FastMinors"
needsPackage "RationalMaps"



k=ZZ/32003;
P2=k[s,t,u];
RC=k[y,z,w];
RDC=k[s,t,u,y,z,w];
P9=k[x_0..x_9]




AdIdeal3 = (B) -> (
--INPUT: the definig polynomial of a planar curve B which has nodes and cusps 
--as singularities such that the degree can be factored as 3d(d-1).
--OUTPUT: the  adjoint ideal which is equal to the radical of the ideal of  
--the singular locus (jacobian ideal)
      
      use RC;
      J:=jacobian(ideal(B));
      J1:= radical(B+ minors(1,J));
      J1
    )   


--------------------------------------------------------------------------------


--time AdIdeal3(B)     --ideal of RC, used 7.63589


--------------------------------------------------------------------------------




LNormalize = (B)->(
--INPUT: the definig polynomial of a planar curve B which has nodes and cusps 
--as singularities such that the degree can be factored as 3d(d-1).
--First find the adjoint ideal and pick a form of degree less then deg(B)
--then compute the quotient ideal as in the Theorem in the paper.
--OUTPUT: map for finding the linear normalization of the curve B.

  A := AdIdeal3(B);
  g:=A_0;
  g1=A_1;
  g2:=A_2;
  g3:=A_3;
  g4:=A_4;
  g5:=A_5;
  g6:=A_6;
  g7:=A_7;
  
  B1:=RC/ideal(B);
  psi := map(B1,P9,{y*g,z*g,w*g,g1,g2,g3,g4,g5,g6,g7});
  psi
  
  )
  
  
--------------------------------------------------------------------------------
  
  
--time psi=LNormalize(B)  --used 7.74667 seconds
  
  
--------------------------------------------------------------------------------
  
  
   
  
  Veronese =(B)->(
--INPUT: the definig polynomial of a planar curve B which nodes and cusps 
--as singularities such that the degree can be factored as 3d(d-1).
--First we find the linear normalization of the curve B, denoted imB
--then we use the method of linear syzygies explained in the paper.
--OUTPUT: the defining ideal of the Veronese surface.
 
  B2:=RC/ideal(B);
  I:= ideal basis ({2},P9); 
  J:=ideal basis ({30},B2);
  
  psi:=LNormalize(B);
  
  psiI:= sub(psi I,B2); 
  N:=(gens psiI)//(gens J);
  
  
  
  l:=getSubmatrixOfRank(27,N, Strategy=>StrategyRandom);
  M:=N^(l#0); 
  
  A:=substitute(gens ker M,P9);
  imB:=ideal((gens I)*A);
  
  Syz:=syz gens imB;
  G:=gens imB;
  d:= first(degrees target Syz/sum);
  v:= vars P9 ** P9^{d+1};
  L1:=for i to numcols Syz - 1 list try transpose Syz_{i} // v else continue;
  L2:=apply(L1,A->A*transpose G);
  
  
  I1:=ideal L2;
  G1:= ideal gens gb I1;  
  Ls:= for i from 0 to 27 list G1_i;
  L:=select(Ls, f ->degree f <= {2});
  V:=ideal L; 
  
  V
 )


--------------------------------------------------------------------------------  
  
  
  --time Veronese(B)    --used 12.927 seconds
  
  
--------------------------------------------------------------------------------

  

PointVeronese =(B) ->(

--INPUT:the definig polynomial of a planar curve B which has nodes and cusps 
--as singularities such that the degree can be factored as 3d(d-1).
--First we compute the defining ideal of the Veronese surface, then we cut the
--surface with a linear space. 
--OUTPUT: the maximal ideal of a point in Veronese surface
    
    found=false;
    while not found do (
    l1:=random(1,P9);
    l2:=random(1,P9);
    l:=ideal(l1,l2);
    V:=Veronese(B);
    J:=V+l;
    J1:=eliminate(J,{x_2,x_3,x_4,x_5,x_6,x_7,x_8,x_9});
    Pr:=primaryDecomposition J1;
    if degree(Pr_0)==1 then found =true);
    M:=Pr_0+J;
    M
    )


--------------------------------------------------------------------------------


--time PointVeronese (B) --used 22 seconds

--------------------------------------------------------------------------------




OsculatingSpace=(B)->(


--INPUT: the definig polynomial of a planar curve B which has nodes and cusps 
--as singularities such that the degree can be factored as 3d(d-1).
--We compute a Veronese surface and a point on it, 
--then we compute 2nd & 3rd osculating spaces on that point. 
--OUTPUT: the definig ideal of 2nd & 3rd osculating spaces
        
      V:=Veronese(B);
      M:=PointVeronese(B); 
        
      Iaff:=ideal gens gb sub(V,{x_9=>1});
      Maff:=ideal gens gb sub (M,{x_9=>1});
      
      Osc1:=ideal gens gb (Maff^3+Iaff);
      Osc2:=ideal gens gb (Maff^2+Iaff);

      OSC1:= ideal gens gb Osc1;
      Lst1:=for i from 0 to 18 list  OSC1_i;
      L1:=select(Lst1, f ->degree f == {1});
      
      OSC2:= ideal gens gb Osc2;
      Lst2:=for i from 0 to 9 list  OSC2_i;
      L2:=select(Lst2, f ->degree f == {1});
      
      V1:=ideal L1;
      V2:=ideal L2;
      V1,V2
      )
      


--------------------------------------------------------------------------------     
 
 
  --time OsculatingSpace(B1)     --used 34.4347 seconds
 
 -------------------------------------------------------------------------------
 
  
   
      
ParametrizationVeronese=(B) -> (

--INPUT: the definig polynomial of a planar curve B which has nodes and cusps 
--as singularities such that the degree can be factored as 3d(d-1).
--First we apply twice the function for finding the 2nd & 3rd osculating space
--at the Veronese surface containing the linear normalization of the curve B.
--Next we intersect the osculating spaces of different points with different
-- order. Then we collect the linear forms of these intersections. After that we
-- take minimal generators of the union of these linear forms. The basis of the
-- last vector space of the union  define a rational map from Veronese 
--to the plane, and then find its inverse which is exactly the parametrization.
-- OUTPUT: the parametrization of the Veronese surface.



      (V3,V4):=OsculatingSpace(B);
      (V5,V6):=OsculatingSpace(B);
      
      
      Id1:=intersect(V3,V6);
      
      A1:= for i from 0 to numgens(Id1)-1 list Id1_i;
      A:=select(A1,a-> degree a=={1});
     
      Id2:=intersect(V4,V5);
      C1:= for i from 0 to numgens(Id2)-1 list Id2_i;
      C:=select(C1,c-> degree c=={1});
      

      I1:=ideal A;
      I2:=ideal C;
      
      I:=trim(I1+I2);
      
      use P9;
      J:=homogenize(I,x_9);
      V:=Veronese(B);
      RV:=P9/V;
      

      q:=map(RV,P2,{J_0,J_1,J_2});
      
     
      
      InversE:=inverseOfMap q;
     
        InversE
      )
      
      
--------------------------------------------------------------------------------     
      
      
--ParametrizationVeronese (B) --used 65.0948 seconds

--------------------------------------------------------------------------------



PlanarMap=(B)->(

--INPUT: defining polynomial of a planar curve B which has nodes and cusps 
--as singularities such that the degree can be factored as 3d(d-1)
--The first step is finding the parametrization of the Veronese surface
--where the linear normalization of the curve B lies.
--The next step is to compose the parametrization with
--projection to the first three coordinates. 

--OUTPUT: a planar map such that the curve B is ist branching curve.
       
       Par:=ParametrizationVeronese(B);
       Parm:=matrix map Par;
       
       Entr := entries Parm;
       f1:=factor(Entr#0#0);
       f2:=factor(Entr#0#1);
       com := gcd(Entr#0#0,Entr#0#1);
       
       ParSimp := apply(Entr#0, i->(quotientRemainder(i,com))#0);
       ParProj:= drop(ParSimp,{3,9});
       PlanarMap:=map(P2,RC,ParProj)
       
       )


--------------------------------------------------------------------------------

time plmap=PlanarMap(B)  --used 87.91753 seconds

