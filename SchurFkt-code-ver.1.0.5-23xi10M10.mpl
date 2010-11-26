#############################################################################
#
# This is the source code file of the "SchurFkt" package
# SchurFkt Version 1.0.5 (23 xi 2010) 
# file:   SchurFkt-code-ver.1.0.4-23xi10_M10.mws
# date:   Nov 23, 2010
#
# copyright (c) Bertfried Fauser, & Rafal Ablamowicz
#               June 2003-November 2010, all rights reserved.
#
#############################################################################
#                                                                           #
#  DISCLAIMER:                                                              #
#                                                                           #
#  THERE IS NO WARRANTY FOR THE SCHURFKT PACKAGE TO THE EXTENT PERMITTED    #
#  BY APPLICABLE LAW. EXCEPT WHEN OTHERWISE STATED IN WRITING THE COPYRIGHT #
#  HOLDERS AND/OR OTHER PARTIES PROVIDE THE PROGRAM "AS IS" WITHOUT         #
#  WARRANTY OF ANY KIND, EITHER EXPRESSED OR IMPLIED, INCLUDING, BUT NOT    #
#  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR    #
#  A PARTICULAR PURPOSE. THE ENTIRE RISK AS TO THE QUALITY AND PERFORMANCE  #
#  OF THE PROGRAM IS WITH YOU. SHOULD THE PROGRAM PROVE DEFECTIVE, YOU      #
#  ASSUME THE COST OF ALL NECESSARY SERVICING, REPAIR OR CORRECTION.        #
#                                                                           #
#############################################################################
#
#  If you want to use this code or parts of it under a GPL LICENCE, please
#  contact the authors:
#  rablamowicz <at> tntech.edu                 or 
#  B.Fauser <at> cs.bham.ac.uk
#
#
# +++ The package computes some products and coproducts for Schur functions
# --- 
# --- Remember: elementary symmetric functions are s[1^r] 
# ---           complete symmetric functions are s[r]
# ---           m[r] equals p[r]
# ---           m[1,...,1] equals e[r]  (r-ones)
#
# +++ Main functions are:
# --- outer      : the outer product of Schur functions outer(s[3,2],s[1],...)
# --- inner      : the inner product of Schur functions inner(s[2,2],s[3,1],...)
# --- skew       : the (outer) skew product of two Schur functions skew(s[3,2,1],s[2])
# --- couter     : the outer coproduct of a Schur function couter(s[4,2])
# --- cinner     : the inner coproduct of a Schur function cinner(s[4,2,2])
# --- antipS     : the antipode of a Schur function AntipS(s[lambda])= (-1)^|lambda|*s[lambda']
#                  w.r.t. the outer(!) Hopf algebra
# --- plethS     : the plethysm of two Schur function polynomials over a ring extension
#                  i.e. one can compute plethysms of the form 
#                  plethS(a*s[3]+s[1],q*s[2,1]+s[2])
#
# --- KostkaTable: computes the Kostka matrix of rank n
# --- isLattice  : returns true is a Young tableau filled with letters (0) 1..n is a 
#                  lattice permutation
#                  the tableau has to be given as [[row1 list ,...],[row2 list, ...],...] 
#                  (mainly internal use)
#
# +++ TYPES:
#           Are exposed globally to Maple via the init routine of the package, any
#           new basis requires an own type. Later versions of Schur may allow the 
#           user to create own types!
#
# --- s-functions come in monoms, terms and polynoms
# --- m-functions come in monoms, terms and polynoms
# --- p-functions come in monoms, terms and polynoms
# --- e-functions come in monoms, terms and polynoms
# --- h-functions come in monoms, terms and polynoms
# --- f-functions come in monoms, terms and polynoms
# 
#     There is a need to introduce orthogonal and symplectic Schur functions and other bases
#     currently these are dealt with using the _same_ names but _different_ algebraic maps!!
#
# ===> some symmetric function bases and or operations in several bases are not yet available 
#
SchurFkt:=module()
   export MLIN,FLAT,
          fallingFactorial,risingFactorial,
          lehmerCodeToPermutation,permutationToLehmerCode,
          lehmerCodeToSchurFkt,schurToLehmerCode,schurToLehmerCode1,
          skewToLehmerCode,
          transition,
          Descents,
          isLattice,
          makeBasList,
          concatM,LaplaceM,LaplaceM2,LP_mon,LaplaceM_mon,LaplaceTable,
          outer,outerLS,outerS,outerM,outerH,outerE,outerP,
          skew,skewLR,skewLS,
          couter,couterM,couterH,couterE,couterP,
          counitS,counitP,counitM,counitH,counitE,counitF,
          antipS,antipP,antipH,antipE,antipM,antipMC,
          KostkaTable,KostkaPC,
          Scalar,ScalarP,ScalarMH,ScalarHM,ScalarBinomialP,ScalarBinomialS,
          AlexComp,grAlexComp,PartNM,partitionsInShape,CompNM,
          zee,zeeP,zeebarP,zeeS,zeebarS,
          truncWT,truncLEN,truncPART,collect_sfkt,sfkt_terms,
          part2mset,partRisingFac,partGCD,partLCM,partBinomial,
	  mset2part,conjpart,cmp2prtMult,cmp2part,Frob2part,part2Frob,
          MurNak,MurNak2,CharHook,sq_coeff,
          dimSN,dimSNP,dimSNM,dimSNH,dimSNE,
          dimGL,dimGLP,dimGLM,dimGLH,dimGLE,
          GesselThetaP,GesselThetaS,
          inner,innerP,innerH,innerM,
          cinner,counitInnerS,cinnerP,counitInnerP,
          cdiag,
          plethP,cplethP,plethSAxNB,plethS,plethSnm,cplethS,
          p_to_m,p_to_s,
          m_to_p,m_to_pMat,m_to_e,m_to_h,m_to_s,
          s_to_p,s_to_x,s_to_h,s_to_hMat,s_to_hJT,s_to_e,s_to_hmat,s_to_m,
          h_to_s,h_to_m,h_to_p,
          e_to_h,e_to_s,e_to_m,
          x_to_s,
          evalJacobiTrudiMatrix,maxlengthSymFkt,
          outerON,couterON,getSfktSeries,branch;
   global `type/cliscalar`, `type/mydomain`,
          `type/hfktmonom`, `type/hfktterm`, `type/hfktpolynom`,
          `type/efktmonom`, `type/efktterm`, `type/efktpolynom`,
          `type/sfktmonom`, `type/sfktterm`, `type/sfktpolynom`,
          `type/pfktmonom`, `type/pfktterm`, `type/pfktpolynom`,
          `type/ffktmonom`, `type/ffktterm`, `type/ffktpolynom`,
          `type/mfktmonom`, `type/mfktterm`, `type/mfktpolynom`,
          `type/symfktmonom`, `type/symfktterm`, `type/symfktpolynom`;
   local  init,exit,ADD,LRR,getPart,makeRimRep,removeRimHook,MurNakRim,
          partitionsInShape_gen,
          dimSN_mon,dimGL_mon,dimGLP_mon,
          LaplaceMset,couterMproper1n,LP_l1,concatM_mon,concat_mon,
          inner_mon,cinner_mon,innerP_mon,cinnerP_mon,innerH_mon,
          couter_mon,couterM_mon,couterH_mon,couterE_mon,couterP_mon,
          antipS_mon,antipP_mon,antipH_mon,antipE_mon,antipM_mon,
          p_to_mM,m_to_pM,
          list_divisors,truncLEN_mon,GesselThetaP_mon,GesselThetaS_mon,
          plethPsingleP,
          x_to_sM,
          s_to_xM,s_to_hM,s_to_mM,
          h_to_sM,h_to_mM,h_to_pM,
          m_to_hM,m_to_sM,
          etoh,e_to_hM,e_to_sM,e_to_mM,
          plethP_mon,plethsp,plethSP,plethS_mon,cplethS_mon,
          sfktmon_to_hmatrix,
          outerON_monom,couterON_monom,branch_monom;  
   option package,
          load=init,
          unload=exit;
#################################################################################
#
#  init exposes several types in the global name space, it greets the user
#       and initialized the tensor product.
#
init:=proc()
  global FIELD;
#
#
#
printf("SchurFkt Version 1.0.5 (23 xi 2010) at your service\n(c) 2003-2010 BF&RA, no warranty, no fitness for anything!\n",%s);
#
# set the global variable FIELD to specify the ground field of the ring /\ and 
#     sepcify the linearity of the tensor product &t in use
#
# overwirte a possibly set type cliscalar, which is to radical in its linearity
  `type/cliscalar`:=proc(x)
         type(x,'rational');
  end proc:
#
  FIELD := radalgfun(rational,[q,t,u,v]);
  `type/mydomain`:=proc(x) 
         type(x,radalgfun(rational,[q,t,u,v]));
  end proc:
  if assigned(`&t`) then unassign(`&t`) end if;
  if assigned(`type/cliscalar`) then unassign(`type/cliscalar`) end if;
  `type/cliscalar`:=proc(x) 
         type(x,radalgfun(rational,[q,t,u,v]));
  end proc:
  define(`&t`,multilinear,flat,domain='cliscalar');
#
# type:   SYM-Fkt (general symmetric function type)
#
  `type/symfktmonom`:=proc(a)
     option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
     member(op(0,a),{s,p,h,m,e,f});
  end proc:
#
  `type/symfktterm`:=proc(a)
     option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
     if type(a,`symfktmonom`) then return true end if; 
     if type(a,`*`) and 1<>select(type,a,`symfktmonom`) then
       true;
     else
       false; 
     end if;
  end proc:
#
  `type/symfktpolynom`:=proc(a) 
     option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
     if type(a,`symfktterm`) then return true end if:
     if type(a,`+`) then 
       return evalb(map(type,{op(a)},symfktterm)={true})
     else
       return false;
     end if;
  end proc:
#
# type:   S-Fkt{monom,term,polynom}
#
  `type/sfktmonom`:=proc(a)
     option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
     evalb(`s`=op(0,a));
  end proc:
#
  `type/sfktterm`:=proc(a)
     option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
     if type(a,`sfktmonom`) then return true end if; 
     if type(a,`*`) and 1<>select(type,a,`sfktmonom`) then
       true;
     else
       false; 
     end if;
  end proc:
#
  `type/sfktpolynom`:=proc(a) 
     option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
     if type(a,`sfktterm`) then return true end if:
     if type(a,`+`) then 
       return evalb(map(type,{op(a)},sfktterm)={true})
     else
       return false;
     end if;
  end proc:
#
# type:   p-Fkt{monom,term,polynom}
#
  `type/pfktmonom`:=proc(a)
     option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
     evalb(`p`=op(0,a));
  end proc:
#
  `type/pfktterm`:=proc(a)
     option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
     if type(a,`pfktmonom`) then return true end if; 
     if type(a,`*`) and 1<>select(type,a,`pfktmonom`) then
       true;
     else
       false; 
     end if;
  end proc:
#
  `type/pfktpolynom`:=proc(a) 
     option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
     if type(a,`pfktterm`) then return true end if:
     if type(a,`+`) then 
       return evalb(map(type,{op(a)},pfktterm)={true})
     else
       return false;
     end if;
  end proc:
#
# type:   m-Fkt{monom,term,polynom}
#
  `type/mfktmonom`:=proc(a)
     option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
     evalb(`m`=op(0,a));
  end proc:
#
  `type/mfktterm`:=proc(a)
     option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
     if type(a,`mfktmonom`) then return true end if; 
     if type(a,`*`) and 1<>select(type,a,`mfktmonom`) then
       true;
     else
       false; 
     end if;
  end proc:
#
  `type/mfktpolynom`:=proc(a) 
     option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
     if type(a,`mfktterm`) then return true end if:
     if type(a,`+`) then 
       return evalb(map(type,{op(a)},mfktterm)={true})
     else
       return false;
     end if;
  end proc:
#
# type:   h-Fkt{monom,term,polynom}
#
  `type/hfktmonom`:=proc(a)
     option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
     evalb(`h`=op(0,a));
  end proc:
#
  `type/hfktterm`:=proc(a)
     option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
     if type(a,`hfktmonom`) then return true end if; 
     if type(a,`*`) and 1<>select(type,a,`hfktmonom`) then
       true;
     else
       false; 
     end if;
  end proc:
#
  `type/hfktpolynom`:=proc(a) 
     option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
     if type(a,`hfktterm`) then return true end if:
     if type(a,`+`) then 
       return evalb(map(type,{op(a)},hfktterm)={true})
     else
       return false;
     end if;
  end proc:
#
# type:   e-Fkt{monom,term,polynom}
#
  `type/efktmonom`:=proc(a)
     option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
     evalb(`e`=op(0,a));
  end proc:
#
  `type/efktterm`:=proc(a)
     option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
     if type(a,`efktmonom`) then return true end if; 
     if type(a,`*`) and 1<>select(type,a,`efktmonom`) then
       true;
     else
       false; 
     end if;
  end proc:
#
  `type/efktpolynom`:=proc(a) 
     option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
     if type(a,`efktterm`) then return true end if:
     if type(a,`+`) then 
       return evalb(map(type,{op(a)},efktterm)={true})
     else
       return false;
     end if;
  end proc:
#
#
# type:   f-Fkt{monom,term,polynom}
#
  `type/ffktmonom`:=proc(a)
     option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
     evalb(`f`=op(0,a));
  end proc:
#
  `type/ffktterm`:=proc(a)
     option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
     if type(a,`ffktmonom`) then return true end if; 
     if type(a,`*`) and 1<>select(type,a,`ffktmonom`) then
       true;
     else
       false; 
     end if;
  end proc:
#
  `type/ffktpolynom`:=proc(a) 
     option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
     if type(a,`ffktterm`) then return true end if:
     if type(a,`+`) then 
       return evalb(map(type,{op(a)},ffktterm)={true})
     else
       return false;
     end if;
  end proc:
#
# -- we protect the labesl for the various Schur function bases, so that no
# -- mischieve can happen
#
# protect the names of basis elements
  protect('h','m','e','f','s','p');
#
#
end proc: # init 
#
#
#
exit:=proc()
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
  printf("SchurFkt Version 1.0.5 says 'Good bye...'\n",%s);
end proc:
##################################################################################
#
# Actual package starts here with some helper and internal functions 
#
##################################################################################
##################################################################################
#
# Helper functions
#
##################################################################################
#
# MLIN is a function which allows to make a procedure multilinear w.r.t. the integers
#      or any ground field specified in the global variable FIELD
#      Mostly internal use!
# +++ (warning may be replaced in future releases, don't use it in own code!)
#
MLIN:=proc()
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
  local i,P,pt,res,sg;
  for i from 1 to nargs do
    lst||i:=args[i];
    if type(lst||i,`+`) then lst||i:=[op(lst||i)] else lst||i:=[lst||i] end if;
  end do:
  sg:=proc(x)
    local cf,tm;
    if type(x,symfktmonom) then 
      return 1 
    elif type(x,symfktterm) then 
      tm,cf:=selectremove(type,x,symfktmonom);
      return cf; 
    else 
      error "this should not happen"; 
    end if; 
  end proc:
  res:=0:
  P:=combinat[cartprod]([seq(lst||i,i=1..nargs)]):
  while not P[finished] do 
    pt:=P[nextvalue]();
    res:=res+mul(sg(pt[i]),i=1..nops(pt))*_T(seq(pt[i]/sg(pt[i]),i=1..nops(pt)));
  end do;
  eval(subs(_T=`&t`, res ));
end proc:
#
# FLAT is a function which allows to impose the associativity of functions 
#      (flaten expressions) Mostly internal use.
# +++  (warning may be replaced in future releases, don't use it in own code!)
#
FLAT:=proc()
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
  local x,lst,drp,cf,term;
  x:=eval(subs(T=MLIN,args));
  drp:=proc() args end proc:
  if type(x,`+`) then 
    return eval(subs(T=MLIN,map(procname,x)))
  elif type(x,`*`) then 
    cf,term:=selectremove(type,x,'integer');
    return cf*eval(subs(T=MLIN,T(eval(subs(T=drp,term)))));
  else
    return eval(subs(T=MLIN,T(eval(subs(T=drp,x)))));
  end if;
end proc:
################################################################################
#
# fallingFactorial is the polynomial Pochhammer symbol (for nonnegative integral N)
# risingFactorial  seems not to be implemented in Maple
#
fallingFactorial:=(x,N)->mul((x-k),k=0..N-1):
risingFactorial:=(x,N)->mul((x+k),k=0..N-1):
#
#
##########################
#
# Combinatorial functions
#
##########################
#
# KostkaPC computes the Kostka coefficient between a partition and a composition.
#          Every composition lies in a symmetric group orbit of a particular 
#          partition, on which the Kostka coefficient is actually constant.
#          KostkaPC is defined as the Schur-Hall scalar product of the h[comp[i]]
#          (=s[comp[i]) and the Schur function with partition part. Since the outer
#          product is commutative and since zero parts of the composition turn into
#          the multiplicative unit, we compute just the outer product of the one
#          part Schurfunctions and then the scalar product. 
#
KostkaPC:=proc(part1,part2)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local mks;
  mks:=(lst)->map(i->s[op(i)],lst);
  subs(s[0]=1,
      Scalar(outer(op(map(i->mks(i),part2))),s[op(part1)])
      );
end proc:
#
# grAlexcomp establishes the graded (by parts) anti lexicographical ordering on integer 
#            partitions or compositions.
#
grAlexComp:=proc(x,y)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
  if nops(x)<nops(y) then 
    true
  else
     AlexComp(x,y)
  end if;
end proc:
#
# AlexComp  establishes the anti lexicographical ordering on integer partitions or
#           compositions.
#
AlexComp:=proc(x,y)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local i,bool;
  i:=1;
  while i <= min(nops(x),nops(y)) do
    if x[i]>y[i] then return true elif x[i]<y[i] then return false end if;
    i:=i+1;
  end do;
  true;   
end proc:
#
# isLattice checks if a tableaux (Young diagram or shape filled with (non negative) 
#           integers is a Lattice permutation (ballot sequence)
#
isLattice:=proc(tbl)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`
         ,remember;  
  local cl,lst,i,nl,T;
  cl:=nops(tbl);
  lst:=map(x->if x=0 then NULL else x end if,[seq(op(tbl[cl+1-i]),i=1..cl)]);
  nl:=max(op(lst));
  for i from 1 to nl do
    T[i]:=0:
  end do:
  for i from nops(lst) by -1 to 1 do
    T[lst[i]]:=T[lst[i]]+1;
    if member(false,{seq(evalb(T[i]>=T[i+1]),i=1..nl-1)}) then 
      return false;
    end if;
  end do;
  true; 
end proc:
#
# ADD (internal use) adds a single letter named 'let' (integer) to a tableau in such
#     a way, that the resulting word is a lattice permutation (i.e. in a way which is
#     allowed by the Littlewood Richardson rule). This is the function which actually
#     implements the Littlewood Richardson rule. It tries to be clever about summation
#     but might be greatly improved on speed still, but uses option remember.
#     
ADD:=proc(tbl,let)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`
         ,remember;
  local cl,rl,ad,min,res,i;
#####
# +++ preliminary stuff
  cl:=nops(tbl); 
  rl:=map(x->nops(x),tbl);
  ad:=(x,y)->[op(x),y]:
  res:=[]:
# ---  
#####
# +++ find first row with letter 'let'
# --- descending search
  min:=cl+1:
  if member(let,{op(map(x->op(x),tbl))}) then
    for i from cl by -1 to 1 do
      if member(let,{op(tbl[i])}) then min:=i: break; end if;
    end do:
  else # -- no let 'let'
    min:=1;
  end if;
#####
# +++ find first row with more letters let-1 than letters 'let'
# +++ but start at row 'min'
# --- ascending search
  if let>1 then 
    for i from max(1,min-1) to cl do
      if `+`(op( map(x->op(x),[seq( map( x->if x=let-1 then -1 elif x=let then 1 else NULL end if,
                       tbl[k]), k=1..i)]) )) < 0 then min:=i+1: break; 
      end if;
    end do:
  end if;
##### 
  #
  # +++ now start to put the letter in any possible place
  # --- beginning with row 'min'
  #
  for i from min to cl do
  #
  # +++ case i=1 is different
  #
    if i=1 then 
      if (tbl[i][-1]<=let or tbl[i][-1]=0) then  
        if isLattice(subsop(i=ad(tbl[i],let),tbl)) then 
          res:=[op(res),subsop(i=ad(tbl[i],let),tbl)];
        end if; 
      end if;
    else
  # +++ cases i=2..cl
      if (rl[i-1]>rl[i]) then 
        if (tbl[i][-1]<=let or tbl[i][-1]=0) then
          if (tbl[i-1][rl[i]+1]<let or tbl[i-1][rl[i]+1]=0) then
            if isLattice(subsop(i=ad(tbl[i],let),tbl)) then 
              res:=[op(res),subsop(i=ad(tbl[i],let),tbl)];
            end if;      
          end if;
        end if;
      end if;
    end if;
  end do:
  # +++ last row
  if (tbl[cl][1]<let or tbl[cl][1]=0) then
    if isLattice([op(tbl),[let]]) then 
          res:=[op(res), [op(tbl),[let]] ];
    end if;      
  end if;
  op(res);
end proc:
#
# LLR (internal use) is the Littlewood Richardson rule. This function is based on 
#     the functionality of ADD adding one letter at a time. LLR evacuates one tableau 
#     by adding its letters successively to the (list of) tableaux emerging from 
#     previous adds. 
#
LRR:=proc(lst1,lst2)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`
         ,remember;
  local i,j,k,TT,srt;
  #
  if lst1=[0] then return s[op(lst2)] end if;
  if lst2=[0] then return s[op(lst1)] end if;
  #
  TT:=[[seq([0$lst1[j]],j=1..nops(lst1))]]:
  for i from 1 to nops(lst2) do
  for j from 1 to lst2[i] do
    TT:=map(ADD,TT,i);    end do;
  end do;
  `+`(op(map(x->s[op(x)],[seq(map(x->nops(x),TT[k]),k=1..nops(TT))]))); 
end proc:
#
# (obsolete function, internal use only)
#
# getPart strips of the name of a symmetric function n[a,b,c] returning the indexing list.
# +++     no longer used, inline use in code as [op(x)] directly. 
getPart:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;  
  [op(x)];
end proc:
#
# PartNM returns a list of partitions of N with M parts.
#        PartNM returns a list ordered inversely to teh standard Maple
#        combinat package! 
#
PartNM := proc(n, m)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
         remember;
  local i, p, s, t;
  if n = 0 then
    return [[]]
  elif m = 1 then
    return [[`$`(1,n)]]
  else
    for i to m do
      t := procname(n-i,min(n-i,i));
      p[i] := seq([i, op(s)],s = t)
    end do;
    [seq](p[m+1-i],i = 1 .. m);
  end if;
end proc:
#
#
# partitionsInShape_gen(par) produces a _set_ of all partitions which fit into the shape par
#         these are partitions of all weights wt, 0 <= wt <= weight(par). These partitions
#         form the set of possibly non-trivial skews, and generate a minimal number of
#         partitions for the Schur outer coproduct. This routine is not optimal as it internally
#         produces some partitions with a multiplicity, this is removed by the set data structure.
#         (internal use only)
#
partitionsInShape_gen:=proc(par)
   local res,i,newpar,min,k;
   if par=[] then return [[0]] end if;
   if nops(par)=1 then return [seq([par[1]-i],i=0..par[1])] end if; 
   res:={par};
   #-- for all descents delete a box
   for i from 1 to nops(par)-1 do
      if par[i]>par[i+1] then
         newpar:=par;
         newpar[i]:=newpar[i]-1;
         res:={op(res),op(procname(newpar))};
      end if;
   end do;
   #-- last index, i points already to last index
   if par[i]>1 then
      newpar:=par;
      newpar[i]:=newpar[i]-1;
      res:={op(res),op(procname(newpar))};
   else
      newpar:=par[1..-2];
      res:={op(res),op(procname(newpar))};
   end if;
   res; 
end proc:
#
# partitionsInShape(par) returns a sorted (wrt AlexComp) list of all partitions, including
#         the emty one and the input partition par of partitions mu such that mu in par. These
#         are the pertitions which potentially occure in the skew (and hence in the outer
#         coproduct).
#
partitionsInShape:=(par)->sort(ListTools:-Reverse([op(partitionsInShape_gen(par))]),AlexComp):
#
#
#
# CompNM returns a list of compositions of N with M parts
#
CompNM:=proc(N,M)
   option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
          remember;
   local res,i;
   if M<1 then return [] end if;
   if M=1 then return [N] end if;
   if M=2 then return [seq([N-i,i],i=0..N)] end if;
   res:=[];
   for i from N to 0 by -1 do
     res:=[op(res),op(map(x->[i,op(x)],procname(N-i,M-1)))];
   end do;
   res;
end proc:
#
# part2mset transforms a partition into multiset format, that is a composition
#           which gives the multiplicities of parts [4,4,2,1,1] -> [2,1,0,2]
#
part2mset:=proc(part)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
          remember;
  local m,mset,i;
  if part=[0] then return [] end if;
  m:=max(op(part));
  mset:=[seq(0,i=1..m)];
  for i from 1 to nops(part) do
    mset[part[i]]:=mset[part[i]]+1;
  end do;
  mset; 
end proc:
#
# mset2part transforms a partition in multi set representation into an ordinary partition
#           represented by nonnegative integer parts
#
mset2part:=proc(mset)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
          remember;
  local prt,i;
  prt:=[];
  for i from 1 to nops(mset) do
    prt:=[i$mset[i],op(prt)]
  end do;
  if prt=[] then return [0] end if;
  prt;
end proc:
#
# conjpart gives the conjugated partition of the partition part
#
conjpart:=proc(part)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`
         ,remember;
  local len,res,ppart;
  if part=[] or part=[0] then return [0] end if;
  len:=nops(part);
  ppart:=part;
  res:=[];
  while ppart<>[] do
    res:=[op(res),len$ppart[-1]];
    ppart:=map(x->if x=ppart[-1] then NULL else x-ppart[-1] end if,ppart);
    len:=nops(ppart);
  end do;
  res;
end proc:
#
# partRisingFactorial : n is an integer or ring element, part an partition.
#      partRisingFactorial computes the rising factorial w.r.t. this partition.
#      In the case part=[m] this is the ordinary rising factorial
#      In teh case part[1^m] this is the falling factorial
#
#
partRisingFac:=proc(n,part)
  local i,j;
  if part=[0] or part=[] then return 0 end if;
  mul(mul(n-j+i,i=1..part[j]),j=1..nops(part));
end proc:
#
# partGCD(par1,par2) :  computes the gratest common divisor of two partitions
#
#
partGCD:=proc(par1,par2)
  local mset1,mset2;
  mset1,mset2:=part2mset(par1),part2mset(par2);
  if nops(mset1)>nops(mset2) then mset2:=[op(mset2),0$(nops(mset1)-nops(mset2))]; end if;
  if nops(mset2)>nops(mset1) then mset1:=[op(mset1),0$(nops(mset2)-nops(mset1))]; end if;
  mset2part(zip((i,j)->min(i,j),mset1,mset2));
end proc:
#
# partLCM(par1,par2) : computes the least common multiple of two partitions
#
#
partLCM:=proc(par1,par2)
  local mset1,mset2;
  mset1,mset2:=part2mset(par1),part2mset(par2);
  if nops(mset1)>nops(mset2) then mset2:=[op(mset2),0$(nops(mset1)-nops(mset2))]; end if;
  if nops(mset2)>nops(mset1) then mset1:=[op(mset1),0$(nops(mset2)-nops(mset1))]; end if;
  mset2part(zip((i,j)->max(i,j),mset1,mset2));
end proc:
#
# zee gives the factor z(lambda) in the schur scalar product of power sums.
#
#
zee:=proc(part)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`
         ,remember;
  local mset;
  mset:=part2mset(part);
  mul(i^mset[i]*mset[i]!,i=1..nops(mset));
end proc:
#
# zeeP : computes the linear form p_\mu |--> z_\mu
#
#
zeeP:=proc(x)
  local cf,term;
  if x=0 then return 0 end if;
  if type(x,`+`) then
    return map(procname,x);
  elif type(x,`*`) then
    term,cf:=selectremove(type,x,pfktmonom);
    return cf*procname(term);
  else
    zee([op(x)]);
  end if;
end proc:
#
# zeebarP : computes the linear form p_\mu |--> 1/z_\mu
#
#
zeebarP:=proc(x)
  local cf,term;
  if x=0 then return 0 end if;
  if type(x,`+`) then
    return map(procname,x);
  elif type(x,`*`) then
    term,cf:=selectremove(type,x,pfktmonom);
    return cf*procname(term);
  else
    1/zee([op(x)]);
  end if;
end proc:
#
# zeeS : computes the linear form s_\mu |--> \sum_\rho \chi^\mu(\rho)
#
#
zeeS:=proc(x)
  local cf,term;
  if x=0 then return 0 end if;
  if type(x,`+`) then
    return map(procname,x);
  elif type(x,`*`) then
    term,cf:=selectremove(type,x,sfktmonom);
    return cf*procname(term);
  else
    if x=s[0] then return 1 end if;
    add(MurNak(i,[op(x)]), i in PartNM(`+`(op(x)),`+`(op(x))));
  end if;
end proc:
#
# zeebarS: computes the linear form s_\mu |--> \sum_\rho \chi^\mu(\rho)/z^2_\rho
#
#
zeebarS:=proc(x)
  local cf,term;
  if x=0 then return 0 end if;
  if type(x,`+`) then
    return map(procname,x);
  elif type(x,`*`) then
    term,cf:=selectremove(type,x,sfktmonom);
    return cf*procname(term);
  else
    if x=s[0] then return 1 end if;
    add(MurNak(i,[op(x)])/zee(i)^2, i in PartNM(`+`(op(x)),`+`(op(x))));
  end if;
end proc:
#
# partBinomial : is the binomial function for two partitions
#
#
partBinomial:=proc(prt1,prt2)
  local mset1,mset2;
  mset1,mset2:=part2mset(prt1),part2mset(prt2);
  if nops(mset1)>nops(mset2) then mset2:=[op(mset2),0$(nops(mset1)-nops(mset2))]; end if;
  if nops(mset2)>nops(mset1) then mset1:=[op(mset1),0$(nops(mset2)-nops(mset1))]; end if;
  mul( binomial(mset1[i]+mset2[i],mset1[i]), i=1..nops(mset1)); 
end proc:
#
#
##############################################################################
#
#  cmp2prtMult gives the multiplicity of the orbit of a composition
#              of its associated partition under the S_n
#
cmp2prtMult:=proc(comp)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
          remember;
  local nc,part,f,cnt0;
  nc:=nops(comp);
  cnt0:=0;
  part:=map(x->if x=0 then cnt0:=cnt0+1; NULL else x end if,
            sort(comp,(i,j)->if i>=j then true else false end if) );
  part:=map(x->if x=0 then NULL else x end if,part2mset(part));
  if cnt0=0 then part:=part[1..-2] end if;
  #################
  f:=(ri,N)->mul(N-k,k=0..ri-1)/ri!;
  #################
  mul(f(part[k],nc+part[1]-add(part[m],m=1..k)),k=1..nops(part));
end proc:
#
# cmp2part takes a composition and transforms it into a partition.
#          This is a projection and a 'base point projection'.
#
cmp2part:=proc(comp)
   option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
          remember;
   map(x->if x=0 then NULL else x end if,
   sort(comp,(i,j)->if i>=j then true else false end if) );
end proc:
#
# part2Frob (internal usage) maps a partition into Frobenius notation.
#
part2Frob:=proc(Part)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
          remember;
  local res,part;
  if Part=[0] or Part=[] then return [[],[]] end if;
  part,res:=Part,[[],[]];
  while part<>[] do
    res[1]:=[op(res[1]),part[1]-1];
    res[2]:=[op(res[2]),nops(part)-1];
    part:=map(x->if x>1 then x-1 else NULL end if,part[2..-1]);
  end do;
  res;
end proc:
#
# Frob2part (internal use) maps a partition in Frobenius notation into a 
#           standard partition
#
Frob2part:=proc(LList)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
          remember;
  local res,llist,row;
  if LList=[[],[]] then return [0] end if;
  res:=[LList[1][-1]+1,1$LList[2][-1]];
  if nops(LList[1])=1 then return res end if;
  llist:=[LList[1][1..-2],LList[2][1..-2]];
  while llist<>[[],[]] do
     row:=[1$llist[2][-1]];
     res:=[llist[1][-1]+1,op(zip((i,j)->i+j,row,res,0))];
     llist:=[llist[1][1..-2],llist[2][1..-2]];  
  end do;
  res;
end proc:
###################################################################################
#
# T R U N C functions
#
###################################################################################
#
# truncWT truncates the input to partitions of weight less or equal to the seond 
#         argument N
#
truncWT:=proc(x,N)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm,n1,plst1,plst2,i;
  if type(x,`+`) then 
    return map(procname,x,N);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,symfktmonom);
    return cf*procname(tm,N)
  else
    if `+`(op(x))>N then return 0 else return x end if;
  end if;
end proc:
#
# truncLEN_mon truncates partitions of any type of symmetric function monoms
#       to length less or equal to L
#
truncLEN_mon:=proc(sfkt,L)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
   if nops([op(sfkt)])=1 and L=0 then 
     if [op(sfkt)]=[0] then return sfkt; else return 0 end if; 
   end if;
   if nops([op(sfkt)])<=L then
     return sfkt
   else
     return 0
   end if;
end proc:
#
# truncLEN truncates the partitions of a symmetric function polynom
#       to length smaller or euqlt to L, it is a linear function
#
#
truncLEN:=proc(symfkt,L)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,term;
if symfkt=0 then return 0 end if;
  if type(symfkt,symfktmonom) then
    truncLEN_mon(symfkt,L)
  elif type(symfkt,`*`) then
    term,cf:=selectremove(type,symfkt,symfktmonom);
    return cf*truncLEN_mon(term,L);
  else
    map(procname,symfkt,L);
  end if;
end proc:
#
# truncPART projects on symmetric functions where the parts of the involved
#           partitions is less than or equal to N
#
truncPART:=proc(x,N)
  local cf,term,prt;
  if type(x,`+`) then
     return map(procname,x,N);
  elif type(x,`*`) then
     term,cf:=selectremove(type,x,symfktmonom);
     return cf*procname(term,N);
  else
     if max(op(x))>N then 
       return 0;
     else
       return x;
     end if;     
  end if;
end proc:

#################################################################
#
# collect_sfkt collects a polynomial with respect to an sfunction 
#      basis 's,p,m,h,f,e' and returns the prefactors factorized.
#      The basis is by default the Schur function basis and may be
#      altered by giving a letter from the set 's,p,m,h,f,e' as
#      second argument.
#
#################################################################
collect_sfkt:=proc(X)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local x,lst,i,term,terms,termTbl,TYPE;
  if nargs=2 then
    TYPE:=args[2];
    if not member(TYPE,{s,p,m,h,f,e}) then
      error "You picked a type '%1' which is not in my list of known types\n
             's,p,m,h,f,e' !",TYPE;
    end if;
  else 
    TYPE:='s';
  end if;
  if X=0 then return 0 end if;
  x:=expand(X);
  terms:={}; 
  if type(x,cat(TYPE,fktmonom)) then 
     return x;
  elif type(x,cat(TYPE,fktterm)) then
      return x;
  elif type(x,`+`) then
      lst:=[op(x)];
      for i from 1 to nops(lst) do
        if type(lst[i],cat(TYPE,fktmonom)) then
          termTbl:=(lst[i])=1;
        else
          term:=select(type,lst[i],cat(TYPE,fktmonom));
          terms:={op(terms),term};
        end if;
      end do;
      if terms={1} then
        error "I didn't find a basis element, provide a correct basis!";
      end if;
      return map(factor,collect(x,terms));
  end if;
end proc:
#################################################################
#
#  sfkt_terms returns a set of basis monoms of an input expression. 
#      The basis is by default the Schur function basis and may be
#      altered by giving a letter from the set 's,p,m,h,f,e' as
#      second argument.
#
#################################################################
sfkt_terms:=proc(X)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,x,lst,i,term,terms,termTbl,TYPE;
  if nargs=2 then
    TYPE:=args[2];
    if not member(TYPE,{s,p,m,h,f,e}) then
      error "You picked a type '%1' which is not in my list of known types\n 's,p,m,h,f,e' !",TYPE;
    end if;
  else 
    TYPE:='s';
  end if;
  x:=expand(X);
  if X=0 then return 0 end if;
  terms:={}; 
  if type(x,cat(TYPE,fktmonom)) then 
     return {x};
  elif type(x,cat(TYPE,fktterm)) then
      term,cf:=selectremove(type,x,cat(TYPE,fktterm));
      return {term};
  elif type(x,`+`) then
      lst:=[op(x)];
      for i from 1 to nops(lst) do
        if type(lst[i],cat(TYPE,fktmonom)) then
          terms:={op(terms),lst[i]};
        else
          term:=select(type,lst[i],cat(TYPE,fktmonom));
          terms:={op(terms),term};
        end if;
      end do;
      if terms={1} then error "Couldn't find a basis monom!\nyou can provide a second argument with the name of the basis like 's', 'p', 'h', 'f', 'e' \n";
      end if;
      return terms;
  end if;
end proc:
#############################################
#
#
# makeBasList produces a list of basis monomials for the basis `name`
#     with partitions of weight N to M
#
makeBasList:=proc(name,N,M)
  local n;
  if N=0 then
    map(x->name[op(x)],[[0],seq(op(PartNM(i,i)),i=1..M)]);
  else
    map(x->name[op(x)],[seq(op(PartNM(i,i)),i=N..M)]);
  end if;
end proc:
#################################################################
#
# Functions related to the Lascoux Schuetzenberger algorithm 
#
#          to multiply and skew Schur functions
#
#################################################################
#
#
# lehmerCodeToPermutation transform a Lehmer code of a permutation
#           into the list representation of that permutation, that
#           is the list of the image of the permutaion of of the
#           standatd list [1..n]
#
#     Note: we prune trailing fixed points, it the second variable is set to "prune"
#           including quotes
#
#   -- The algorithm use is the following recursion:
#   -- let ordLst be the orderd list [1..n]
#   -- \pi_1 is the lement ordLst_{code[1]+1}
#   -- remove the element ordLst_{code[1]+1} from the list ordList
#   -- \pi_2 is the lement ordLst_{code[2]+1}
#   -- remove the element ordLst_{code[2]+1} from the list ordList
#   -- repeat unless ordLst is empty
#   -- if "prune" is set, we skip trailing fixed points, that is
#   -- we reduce the permutation from S_n (n=card(ordLst)) to a smaller
#   -- S_k which acts on the first [1..k] entries, in this way S_k is
#   -- canonically embedded into S_n for n>k.
#
lehmerCodeToPermutation:=proc(code)
  option remember;
  local ordLst,i,idx,per,prune;
  if nargs=2 and args[2]="prune" then prune:=true; print("prune is true now"); else prune:=false; end if;
  ordLst:=[seq(i,i in 1..nops(code))];
  per:=[];
  for i from 1 to nops(code) do
     idx:=ordLst[code[i]+1];
     per:=[op(per),idx];
     ordLst:=subs(idx=NULL,ordLst);
  end do;
  if prune=true then
     i:=nops(per);
     while per[i]=i and i>1 do
        i:=i-1;
        per:=per[1..-2];
     end do;
   end if;
  per;
end proc:
#
# permutationToLehmerCode transforms a permutation \pi in list representation (image
#             of \pi acting on the standard set [1..n]) into the Lehmer code of the
#             permutation
#
#     -- The Lehmer code of a permutation is given by code:=[l1,..,ln] with
#     -- lk :=Card { j>k, \pi[k]>\pi[j] }
#     -- The Lehmer code is a factorial number system adapted to permutations
#     -- since card S_n = n! This allows a one-one relation between such codes
#     -- and permutations.
#     -- If S_k is embedded into S_n in such a way that S_k permuste the first [1..k]
#     -- entries of the standard set while S_n permutes [1..n], then the Lehmer code
#     -- of a permutation S_k transforms under this injection into the Lehmer code of
#     -- \pi in S_n by adding appropriatly many trailing zeros.
#
permutationToLehmerCode:=proc(per)
  option remember;
  local idx,lehmer,res,k,j;
  if per=[] then return [] end if;
  if {op(per)}<>{seq(i,i in 1..nops(per))} then error "input was not a permutation of the form (i1,i2,...in) with entries ik in [1..n]" end if;
  if per=[] then return [0] end if;
  lehmer:=[];
  for k from 1 to nops(per)-1 do
     idx:=0;
     for j from k+1 to nops(per) do
        if per[j]<per[k] then idx:=idx+1 end if;
     end do;
     lehmer:=[op(lehmer),idx];
   end do;
  [op(lehmer),0];
end proc:
#
# Descents takes a permutation pi and returns the the list of descents of pi
#         ++ the list of descents is in decreasing order
#         ++ Descents describe important facts about the structure of
#         ++ reduced words representing permutations when written as
#         ++ product of elementary transpositions (i,i+1)
#
Descents:=proc(per)
   option remember;
   local des,i;
   des:=[];
   for i from 1 to nops(per)-1 do
      if per[i]>per[i+1] then des:=[i,op(des)]; end if;
   end do;
   des;
end proc:
#
# lehmerCodeToSchurFkt transforms a Lehmer code of a Grassmannian permutation
#         ++ that is a permutation which respresents a Schur function into
#         ++ the Schurfunction with the corresponding partition lable
#         ++ NOTE: No check is performed if the input is a Lehmer code of a Grassmanian
#         ++       permutation. This routine is meant for internal use mainly.
#
lehmerCodeToSchurFkt:=proc(code)
   option remember;
   local i,prt;
   ## ++ no check included, user or algorithm must make sure
   ## ++ input represents a Schur function, otherwise return value is invalid_operation
   prt:=[];
   for i from 1 to nops(code) do
     if code[i]<>0 then
       prt:=[code[i],op(prt)];
     end if;
   end do;
   ## -- possibly needs to be sorted, if vexillary permutations are used, if the
   ## -- transition algorithm runs through, till the permutation has only one
   ## -- descent, it seems to be unnecessary to sort here.
   s[op(prt)]
end proc:
#
# schurToLehmerCode implements the relation between a Schurfunction {\lambda}^m
#     {\lambda}^m=s_\lambda(x1,...xm) in exactly m-variables and a Grassmannian
#     Lehmer code of a permutation (that is a permutation with exactly one descent.
#     The parameter m gived the muner of variables. Caution, if m is too small,
#     the Schur function may be unrepresentable (=0) in that Z[x1,..,xm]
#     An optimal embedding is reached by setting m=length(\lambda), resulting in
#     no leading zerors on teh Lehmer code.
#     We don't add trailing zeros, but keep the minimal number of _required_
#     trailing zeros
#
schurToLehmerCode:=proc(sfkt,m)
   option remember;
   local code,i,par,wt;
   par:=[op(sfkt)];
   wt:=`+`(op(sfkt));
   code:=[];
   for i from 1 to nops(par) do
      code:=[par[i],op(code)];
   end do;
   code:=[op(code),0$par[1]];
   [0$(m-nops(par)),op(code)];
end proc:
#
# schurToLehmerCode1 computes automatically the minimal embedding of the Schur function
#     in terms of Lehmer codes
#
schurToLehmerCode1:=proc(x) schurToLehmerCode(x,nops([op(x)])) end proc:
#
# skewToLehmerCode transforms two partitions of two schur functions
#      which are to be skewed into the Lehmer code representing the
#      skew partitions schur function.
#
skewToLehmerCode:=proc(sf1,sf2)
   option remember;
   local prt,i,code,k,elem;
   prt:=[op(sf1)];
   code:=[];
   for i from 1 to nops(prt) do
      code:=[prt[i],op(code)];
   end do;
   code:=[op(code),0$code[-1]];
   if sf2=s[0] then return code end if;
   k:=nops(prt);
   prt:=[op(sf2)];
   for i from 1 to nops(prt) do
      code[k+prt[i]]:=code[k]-prt[i];
      code[k]:=0;
      k:=k-1;
   end do;
   [op(code)];
end proc:
#
# transition implements an algorithmy by Lascoux and Schuetzernberger Lett. Math. Phys. 10 (1985) 111-124
#      this paper does not give a full description of the implemented code, but uses vexillary permutations.
#      We use a variant of the algorithm described by Axel Konhner, who was also helpful in proding
#      details and further information, see:
#      A. Kohner, Schubert polynomials and skew Schur functions, 1991
#      A. Kohner, The use of Schubert polynomials in SYMCHAR (later SYMMETRICA), 1991
#      A further usefull resource is
#      R. Winkel, Recursive and combinatorial properties of Schubert polynomials, 
#                 Sem. Lotharigien de Comb. Vol38 1996 B38c 29pp 
#
#      The algorithms is as follows:
#      input a permutation pi, not of Grassmanian type (two or more descents)
#      1) compute the right most descent k
#      2) swap the element pi[k] and the largest pi[l] to the right smaller than pi[k]
#      3) find all elements to the left of k such that
#         -- pi[l] is smaller than pi[k]
#         -- there is no pi[j] with pi[l]<pi[j]<pi[k] for l<j<k
#         produce all permutationes obtained by swapping the pi[l] with pi[k]
#         Note: We had to add the following rule:
#         -- If the search for pi[l] returns no element, then return the partition
#            which is obtained by shifting the Lehmer code of the _input_ partition
#            by one to the right inserting a 0 at place 1
#            [On the partition this means add a 1 to each part and concatenate
#              1 |_| 1+[pi]
#      4) output the list of the produced permutations
#
#
transition:=proc(perIN)
   option remember;
   local max,per,k,l,i,elem,res,sp_min,newper,code;
   # -- per needs to have nops(per)>2 check?
   max:=nops(perIN);
   per:=perIN;
   # -- ingone final fixed points
   while per[max]=max do max:=max-1; end do;
   # -- find last descent
   k:=max-1;
   while per[k]<per[k+1] do k:=k-1; end do;
   # find largest per[l] to the right of per[k] with per[l]<per[k]
   l:=k+1;
   elem:=per[l];
   for i from k+2 to max do
      if per[i]<per[k] and elem<per[i] then elem:=per[i]; l:=i end if;
   end do;
   ## -- switch places k,l, note elem:=per[l]
   per[l]:=per[k];
   per[k]:=elem;
   # -- find all elements left to k which fulfill
   # -- per[l]<per[k] and no element exists with
   # -- per[l}<per[i]<per[k] for l<i<k
   # -- switch these elements and return the list or permutations
   res:=[];
   # -- find elements smaller per[k] to the left
   # -- special case k=1
   if k=1 then return [per] end if;
   l:=k-1;
   sp_min:=0;  
   while l>0 do
        if sp_min<per[l] and per[l]<per[k] then
        # -- make new permutation with (l,k) switched
        sp_min:=per[l];
        newper:=per;
        newper[l]:=per[k];
        newper[k]:=per[l];
        res:=[op(res),newper];
      end if;
      # -- else proceed
      l:=l-1; 
   end do;
   ## A. Kohnert says keep this:
   if l=0 and res=[] then
   # -- However, we need to add a prefix 0 to the Lehmer code of perIN
   # -- otherwise the algorithm cannot find an element in the left search
      if perIN[nops(perIN)]=nops(perIN) then
        res:=[[1,seq(perIN[i]+1,i in 1..nops(perIN)-1)]];
      else
        res:=[[1,seq(perIN[i]+1,i in 1..nops(perIN))]];
      end if;
   end if;
   res;
end proc:
#
#################################################################
#
# basis transformations
#
#################################################################
#
# s_to_xM transforms an S-function into a polynom of x-monomials in
#         N variables (x1,x2,...,xn) (N should be greater or equal
#         to the weight of the partition.
#
#         <internal use; users use the linear version s_to_x>
#
s_to_xM:=proc(sfkt,N)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`
         ,remember;
  local cmp;
  cmp:=CompNM(`+`(op(sfkt)),N);
  add(KostkaPC([op(sfkt)],k)*x[op(k)],k=cmp);
end proc:
#
# x_to_sM gets a monomial and transforms it back into an S-function.
#         This transformation is critical, since the transformation matrix
#         K is rectangular! The inverse is computes on the maximal rank
#         subspace, and suitably normalized, so that the collextion of
#         *all* x monomials which give rise to the same S-functions
#         adds up to the integral result
#
#         <internal use; users use the linear version x_to_s>
#
x_to_sM:=proc(xfkt)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`
         ,remember;
  local wgt,prt,KMat,tab,tabc,cmp,matT;
  wgt:=`+`(op(xfkt));
  prt:=PartNM(wgt,wgt);
  KMat :=evalm(linalg[matrix](nops(prt),nops(prt),(i,j)->KostkaPC(prt[i],prt[j]))^(-1));
  tab:=table([seq((prt[k])=k,k=1..nops(prt))]);
  cmp:=CompNM(wgt,nops([op(xfkt)]));
  matT:=linalg[matrix](nops(cmp),nops(prt),
       (i,j)->1/cmp2prtMult(cmp[i])*KMat[tab[cmp2part(cmp[i])],tab[prt[j]]]);
  ## new index  
  tabc:=1; while [op(xfkt)]<>cmp[tabc] do tabc:=tabc+1; end do;
  add(matT[tabc,k]*s[op(prt[k])],k=1..nops(prt));
end proc:
#
# s_to_x linear version of the transformation of S functions to x monomials
#
s_to_x:=proc(sfkt,weight)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
          remember;
  local cf,term,lst;
  if weight=0 then return 1 end if;
  if sfkt=0 then 
    return 0;
  elif type(sfkt,`+`) then 
    return map(procname,sfkt,weight)
  elif type(sfkt,`*`) then
    term,cf:=selectremove(type,sfkt,sfktmonom);
    return cf*procname(term,weight)
  else
    s_to_xM(sfkt,weight);
  end if; 
end proc:
#
# x_to_s linear version of the transformation of x monomials to S functions
#
x_to_s:=proc(xfkt)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
          remember;
  local cf,term,lst;
  if type(xfkt,`+`) then 
    return map(procname,xfkt)
  elif type(xfkt,`*`) then
    cf,term:=selectremove(type,xfkt,{'integer','fraction'});
    return cf*procname(term)
  else
    x_to_sM(xfkt);
  end if; 
end proc:
###############################################################################
#
# h_to_s transformes a complete symmetric function into an s-function polynomial.
#        
h_to_sM:=proc(hfkt)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
          remember;
  if hfkt=0 then return 0 end if;
  outer(op(map(i->s[i],[op(hfkt)])));
end proc:
h_to_s:=proc(hfkt)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local n1,prt,cf,term,lst;
  if hfkt=0 then return 0 end if;
  if not type(hfkt,hfktpolynom) then 
     error("wrong basis as input, need complete symmetric functions"); 
  end if;
  if hfkt=h[0] then return s[0] end if;
  if type(hfkt,`+`) then 
    return map(procname,hfkt)
  elif type(hfkt,`*`) then
    term,cf:=selectremove(type,hfkt,hfktmonom);
    return cf*procname(term)
  else
    return h_to_sM(hfkt)
  end if; 
end proc:
###############################################################################
#
# s_to_h transformes a s-function polynomial into complete symmetric functions.
#
# WARNING: SLOW!! Uses the inverse Kostka Matrix
#          better use the Jacobi-Trudi formula!
#        
s_to_hM:=proc(sfkt)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
          remember;
  local prt,N,KI,i;
  KI:=evalm(rhs(KostkaTable(`+`(op(sfkt))))^(-1));
  N:=`+`(op(sfkt));
  prt:=PartNM(N,N);
  i:=1: while prt[i]<>[op(sfkt)] do i:=i+1 end do;
  add(KI[j,i]*h[op(prt[j])],j=1..nops(prt));
end proc:
s_to_hMat:=proc(sfkt)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local n1,prt,cf,term,lst;
  if sfkt=0 then return 0 end if;
  if sfkt=s[0] then return h[0] end if;
  if type(sfkt,`+`) then 
    return map(procname,sfkt)
  elif type(sfkt,`*`) then
    term,cf:=selectremove(type,sfkt,sfktmonom);
    return cf*procname(term)
  else
    return s_to_hM(sfkt)
  end if; 
end proc:
###############################################################################
#
# s_to_h recursive faster version
#
s_to_h:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local term,cf;
  if x=0 then return 0 end if;
  if x=s[0] then return h[0] end if;
  if type(x,`+`) then
     map(procname,x)
  elif type(x,`*`) then
    term,cf:=selectremove(type,x,sfktmonom);
    return cf*procname(term);
  else
    return h[op(x)] + procname(x-h_to_s(h[op(x)]));
  end;
end proc:
#
###############################################################################
#
# sfktmon_to_hmatrix transforms a sfktmonom (Schur basis function) into
#   -- a matrix in such a way, that the determinant of the matrix w.r.t
#   -- the outer product yields back the Schur function monom.
#   -- the entries of the matrix are one part Schur functions, and hence
#   -- can be multiplies by teh outer product in teh complete symmetric function
#   -- basis, this gives teh Jacobi-Trudi formula for Schur functions
#   -- s_\lambda = det( h_[\lambda_i-i+j]) 
#   -- (there is a similar formula for the elementray symetric functions)
#
sfktmon_to_hmatrix:=proc(x)
  local l,f,dim,lst;
  l,dim:=nops([op(x)]),0;
  if nargs=2 then l:=max(l,args[2]) end if;
  lst:=[op(x),0$(l-nops([op(x)]))];
  f:=(x)->if x<0 then 0 else h[x] end if;
  evalm(linalg[matrix](l,l,(i,j)->f(lst[i]-i+j)));
end proc:
#
# s_to_hmat transforms an sfunction into a Toeplitz matrix of complete one part
#    -- symmetric functions. It takes as a second argument a dimension, which can
#    -- be taken to be the largest length of all involved partitions in teh sfktpolynom
#    -- see : "maxlengthSymFkt()" below
#
s_to_hmat:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm,dim;
  if nargs=2 then dim:=args[2] else dim:=NULL end if;
  if type(x,`+`) then 
    return map(procname,x,dim);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,sfktmonom);
    return cf*procname(tm,dim)
  else
    sfktmon_to_hmatrix(x,dim);  
  end if;
end proc:
#
# evalJacobiTrudiMatrix given an Jacobi-Trudin matrix (say from sfktmon_to_hmatrix)
#    -- this function evaluates the determinant w.r.t. the outer product in the 
#    -- complete symmetric function basis.
#    -- NOTE: one can give a multiplication as second argument! 
#
evalJacobiTrudiMatrix:=proc(matrix)
  local mdim,lst,i,k,l,fun;
  if nargs=2 then fun:=args[2] else fun:=outerH end if;
  mdim:=linalg[rowdim](matrix);
  if mdim=1 then return matrix[1,1] end if;
  lst:=[seq(i,i=1..mdim)];
  add((-1)^(i-1)*expand(fun(matrix[i,1],
       procname(linalg[submatrix](
     matrix,map(x->if x=i then NULL else x end if,lst),[seq(k,k=2..mdim)]))))
     ,i=1..mdim);
end proc:
#
# s_to_hJT linear version of the transition from the s-basis into the h-basis
#   -- useing the Jacobi-Trudi formula
#
s_to_hJT:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm,fun;
  if nargs=2 then fun:=args[2] else fun:=outerH end if;
  if type(x,`+`) then 
    return map(procname,x);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,sfktmonom);
    return cf*procname(tm)
  else
    evalJacobiTrudiMatrix(sfktmon_to_hmatrix(x),fun);  
  end if;
end proc:
#
# maxlengthSymFkt gives the maximal length of a partition index in a
#  -- symfktpolynom of type {s,p,m,h,f,e}
#
#
maxlengthSymFkt:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm;
  if type(x,`+`) then 
    return max(op(map(procname,[op(x)])));
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,symfktmonom);
    return nops([op(tm)])
  else
    return nops([op(x)])  
  end if;
end proc:
###############################################################################
#
# etoh is the transition from elementary to complete symmetric functions for
#     -- one part elementary symmetric functions e_n. It is done using the fact
#     -- that the generating functions H_t=\sum_n {n]t^n and E_-t = \sum_m (-1)^m {1^m}t^m
#     -- are inverse series under the pointwise product of functions
#     -- Note: H_t = M_t and E_-t = M_t[-s_1] = \sum_n S({n})t^n
#
etoh:=proc(x)
  local n;
  n:=op(x);
  if n=1 then return h[1] elif n=0 then return h[0] end if;
  add((-1)^(n-r-1)*outerH(h[n-r],procname(e[r])),r=0..n-1);
end proc:
#
# e_to_hM is the basis change e_to_h on a single efktmonom, it uses the fact that the '
#     -- elementary symmetric functions for a multiplicative basis and employs `etoh'
#
e_to_hM:=proc(x)
  local prt;
  prt:=[op(x)];
  outerH(op(map(etoh,map(x->[x],prt))));
end proc:
#
# e_to_h linear version of the transformation of elementary functions into complete functions
#
e_to_h:=proc(efkt)
  local cf,term,lst;
  if efkt=0 then return 0 end if;
  if efkt=e[0] then return h[0] end if;
  if type(efkt,`+`) then 
    return map(procname,efkt)
  elif type(efkt,`*`) then
    term,cf:=selectremove(type,efkt,efktmonom);
    return cf*procname(term)
  else
    e_to_hM(efkt);
  end if; 
end proc:
#
# e_to_sM is the transition from elementary symmetric function monoms to Schur functions
#    -- it uses the fact that e_k=s[1,1,...,1] (k ones) 
#
e_to_sM:=proc(x)
  if x=0 then return 0 end if;
  if x=e[0] then return s[0] end if;
  outerS(op(map((x)->s[1$x],[op(x)])));
end proc:
#
# e_to_s linear version of the transformation of elementary functions into Schur functions
#
e_to_s:=proc(efkt)
  local cf,term,lst;
  if type(efkt,`+`) then 
    return map(procname,efkt)
  elif type(efkt,`*`) then
    term,cf:=selectremove(type,efkt,efktmonom);
    return cf*procname(term)
  else
    e_to_sM(efkt);
  end if; 
end proc:
#
# e_to_mM ist the basis change from e-fkt to m-fkt on monomials
#
e_to_mM:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local lst;
  lst:=[op(x)];
  outerM(op(map(x->m[1$x],lst)));
end proc:
#
# e_to_m is the linear basis change from elementary symmetric functions to
#        monomial symmetric functions
#
e_to_m:=proc(x)
   option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
          remember;
   local cf,tm;
   if x=0 then return 0 end if;
   if x=e[0] then return m[0] end if;
   if type(x,`+`) then 
     return map(procname,x);
   elif type(x,`*`) then 
     tm,cf:=selectremove(type,x,efktmonom);
     return cf*procname(tm,x)
   else
     e_to_mM(x);  
   end if;
 end proc:
###############################################################################
#
# h_to_mM is the basis transformation from complete to monomials ymmetric functions
#   -- it is computed along the lines of Rota-Stein using the multiplicativity of 
#   -- the complete basis. The coproduct is used in disguise in the formula
#   -- h_(n) = \sum_{\mu|-n} m_\mu, and the multiplicativity is translated into
#   -- the nonmultiplicative outerM product.
#
h_to_mM:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
          remember;
  local lst,f;
  if x=0 then 
    return 0
  elif x=h[0] then
    return m[0]
  end if;
  #  -- h(n) = \sum_rho p[rho] = \sum_\rho \prod_i p[rho_i]
  #  -- and use p(n)==m(n)
  f:=(x)->add(m[op(i)],i=PartNM(x,x));
  lst:=[op(x)];
  outerM(op(map(f,lst)));
end proc:
#
# h_to_m linear version of the transformation of complete functions into monomial functions
#
h_to_m:=proc(hfkt)
   option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,term,lst;
  if type(hfkt,`+`) then 
    return map(procname,hfkt)
  elif type(hfkt,`*`) then
    term,cf:=selectremove(type,hfkt,hfktmonom);
    return cf*procname(term)
  else
    h_to_mM(hfkt);
  end if; 
end proc:
#
# h_to_pM is the transformation from h-basis monomials to p-bases
#
h_to_pM:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
         remember;
  local lst,f;
  f:=(x)->add(p[op(i)],i=PartNM(x,x));
  if x=0 then 
    return 0
  elif x=h[0] then
    return m[0]
  end if;
  lst:=[op(x)];
  outerP(op(map(f,lst))); 
end proc:
#
# h_to_p linear version of the transformation of complete functions into power sums
#
h_to_p:=proc(hfkt)
   option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,term,lst;
  if type(hfkt,`+`) then 
    return map(procname,hfkt)
  elif type(hfkt,`*`) then
    term,cf:=selectremove(type,hfkt,hfktmonom);
    return cf*procname(term)
  else
    h_to_pM(hfkt);
  end if; 
end proc:
###############################################################################
#
# p_to_s transformes a power sum polynomial into an s-function polynomial.
#        This version was checked against SCHUR
#
p_to_s:=proc(pfkt)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local n1,prt,cf,term,lst;
  if pfkt=0 then return 0 end if;
  if pfkt=p[0] or pfkt=p[] then return s[0] end if;
  if type(pfkt,`+`) then 
    return map(procname,pfkt)
  elif type(pfkt,`*`) then
    term,cf:=selectremove(type,pfkt,pfktmonom);
    return cf*procname(term)
  else
    n1:=`+`(op(pfkt));   
    prt:=PartNM(n1,n1);
    add(s[op(i)]*MurNak([op(pfkt)],i),i=prt);
  end if; 
end proc:
###############################################################################
#
# p_to_s recursive version INACTIVE about 10 times slower than the combinatorial
#        version using the Murnaghan Nakayama rule
#
###############################################################################
#p_to_sM:=proc(x)
#  option remember;
#  local k,lst;
#  if x=0 then return 0 end if;
#  if nops([op(x)])=1 then
#    return s[op(x)]+add((-1)^k*s[op(x)-k,1$k],k=1..op(x)-1);
#  else
#    lst:=[op(x)];
#    return outer(op(map((a)->s[op(a)]+add((-1)^k*s[op(a)-k,1$k],k=1..op(a)-1) ,lst)));
#  end if;
#end proc:
#
#p_to_s2:=proc(x)
#  local cf,term;
#  if x=0 then return 0 end if;
#  if type(x,`+`) then
#    return map(procname,x);
#  elif type(x,`*`) then
#    term,cf:=selectremove(type,x,pfktmonom);
#    return expand(cf*procname(term));
#  else
#    return p_to_sM(x);
#  end if;
#end proc:
################################################################################
#
# s_to_p transformes an s-function into power sums.
#        This version was checked against SCHUR, but *differs*
#        in that effect, that it does not introduce an artificial 
#        factor n! to avaoid fractional coefficients
#
#
s_to_p:=proc(xfkt)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,term,lst,mat,np,prt,i;
  if xfkt=0 then return 0 end if;
  if xfkt=s[0] then return p[0] end if;
  if type(xfkt,`+`) then 
    return map(procname,xfkt)
  elif type(xfkt,`*`) then
    term,cf:=selectremove(type,xfkt,sfktmonom);
    return cf*procname(term)
  else
    np:=`+`(op(xfkt));
    prt:=PartNM(np,np);   
    i:=1:
    while prt[i]<>[op(xfkt)] do i:=i+1 end do;
    #
    #+++ use the Murnaghan-Nakayama rules directly without the matrix inversion
    #
    add(1/zee(prt[k])*MurNak(prt[k],prt[i])*p[op(prt[k])],k=1..nops(prt));
  end if; 
end proc:
###############################################################################
#
# s_to_e transformes a s-function polynomial into elementary symmetric functions.
#
s_to_e:=proc(sfkt)
  local cf,term;
  if sfkt=0 then return 0 end if;
  if sfkt=s[0] then return e[0] end if;
  if type(sfkt,`+`) then
     return map(procname,sfkt);
  elif type(sfkt,`*`) then
     term,cf:=selectremove(type,sfkt,sfktmonom);
     return cf*procname(term);
  else
     if `+`(op(sfkt))=nops([op(sfkt)]) then return e[`+`(op(sfkt))] end if;
     return e[op(conjpart([op(sfkt)]))]+procname(sfkt-e_to_s(e[op(conjpart([op(sfkt)]))]));
  end if;
end proc:
#
# s_to_mM basis change from Schur functions to monomial symmetric functions
#
s_to_mM:=proc(sfkt)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
         remember;
  local prt,pt,k;
  if sfkt=0 then 
    return 0
  elif sfkt=s[0] then 
    return m[0];
  else
    prt:=PartNM(`+`(op(sfkt)),`+`(op(sfkt)));
    add(subs(s[0]=1,Scalar(sfkt,outer(op(map(k->s[k],pt)))))*m[op(pt)], pt in prt)
  end if;
end proc:
#
# s_to_m linear basis change from Schur functions to monomial symmetric functions
#
s_to_m:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,tm;
  if type(x,`+`) then 
    return map(procname,x);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,sfktmonom);
    return expand(cf*procname(tm))
  else
    s_to_mM(x,N);  
  end if;
end proc:
#
# m_to_sM basis change from monomial to Schur functions
#
m_to_sM:=proc(mfkt)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
         remember;
  local prt,pt,k;
  if mfkt=0 then 
    return 0
  elif mfkt=m[0] then 
    return s[0];
  else
    prt:=PartNM(`+`(op(mfkt)),`+`(op(mfkt)));
    add(subs(s[0]=1,ScalarMH(mfkt,s_to_h(s[op(pt)])))*s[op(pt)], pt in prt)
  end if;
end proc:
#
# m_to_s linear basis change from monomial to Schur functions
#
m_to_s:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,tm;
  if type(x,`+`) then 
    return map(procname,x);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,mfktmonom);
    return expand(cf*procname(tm))
  else
    m_to_sM(x,N);  
  end if;
end proc:
#
# p_to_mM is an internal function computing the transition from a power sum monomial
#         into a monomial symmetric function. Internal use only.
#
p_to_mM:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
          remember;
  if x=0 then return 0 end if;
  if nops([op(x)])<1 then return m[0] end if;
  outerM(seq(m[op([op(x)][k])],k=1..nops([op(x)])))
end proc:
#
# p_to_m linear version of the transformation of power sums into monomial functions
#
p_to_m:=proc(pfkt)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,term,lst;
  if type(pfkt,`+`) then 
    return map(procname,pfkt)
  elif type(pfkt,`*`) then
    term,cf:=selectremove(type,pfkt,pfktmonom);
    return cf*procname(term)
  else
    p_to_mM(pfkt);
  end if; 
end proc:
#
# m_to_pM transferes monomial symmetric function basis monoms into power sum symmetric
#         functions. Internal use only. 
#
# SLOW!! This routine uses matrix inversion and not a direct combinatorial algorithm !!! 
#
m_to_pM:=proc(mfkt)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
          remember;
  local nm,np,mat,prt,k;
  if mfkt=0 then return 0 end if;
  if mfkt=m[0] then return p[0] end if;
  nm:=`+`(op(mfkt));
  prt:=PartNM(nm,nm);
  np:=nops(prt);
  mat:=linalg[matrix](np,np,(i,j)->coeff(p_to_mM(prt[i]),m[op(prt[j])]));
  mat:=evalm(mat^(-1));
  k:=1: while prt[k]<>[op(mfkt)] do k:=k+1; end do:
  add(mat[k,i]*p[op(prt[i])],i=1..nops(prt));
end proc:
#
# m_to_p linear version of the transformation of monomial functions into power sums
#
m_to_pMat:=proc(mfkt)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,term,lst;
  if type(mfkt,`+`) then 
    return map(procname,mfkt)
  elif type(mfkt,`*`) then
    term,cf:=selectremove(type,mfkt,mfktmonom);
    return cf*procname(term)
  else
    m_to_pM(mfkt);
  end if; 
end proc:
###############################################################
#
# m_to_p recursive faster version
#
###############################################################
m_to_p:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local term,cf,y,const;
  if x=0 then return 0 end if;
  if x=m[0] then return p[0] end if;
  if type(x,`+`) then
     map(procname,x)
  elif type(x,`*`) then
    term,cf:=selectremove(type,x,mfktmonom);
    return cf*procname(term);
  else
    y:=p_to_m(x);
    const:=subs(s[0]=1, ScalarMH(y,h[op(x)]));
    return p[op(x)]/const+ procname(x-y/const);
  end;
end proc:
#################################################################################
#
# m_to_hM is the basis change from monomial to complete symmetric functions
#         it uses the m_to_p function to evaluate the Scalar product in terms
#         of poer sum symmetric functions
#
#################################################################################
m_to_hM:=proc(x)
  local prt,pt;
  if x=0 then return 0 end if;
  if x=m[0] then return h[0] end if;
  prt:=[op(PartNM(`+`(op(x)),`+`(op(x))))];
  add( subs(s[0]=1, ScalarP( m_to_p(x), m_to_p(m[op(pt)]) ))*h[op(pt)] ,pt in prt);
end proc:
#################################################################################
#
# m_to_h is the linear version of m_to_pM basis change from monomial to
#        complete symmetrc functions
#
#################################################################################
m_to_h:=proc(x)
  local cf,term;
  if type(x,`+`) then
    return map(procname,x);
  elif type(x,`*`) then
    term,cf:=selectremove(type,x,mfktmonom);
    return expand(cf*procname(term));
  else
    return m_to_hM(x);
  end if; 
end proc:
#
###############################################################
#
# m_to_e transformation from m-bases to p-bases
#
###############################################################
m_to_e:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local term,cf,y,const,len,mred;
  if x=0 then return 0 end if;
  if x=m[0] then return e[0] end if;
  if type(x,`+`) then
     map(procname,x)
  elif type(x,`*`) then
    term,cf:=selectremove(type,x,mfktmonom);
    return cf*procname(term);
  else
    len:=nops([op(x)]);
    mred:=subs(0=NULL,m[ op([op(x)]-[1$len]) ]);
    if mred=m[] then mred:=m[0] end if;
    #const:=coeff(outerM(op(map(z->m[op(z)],[op(x)]))),m[1$`+`(op(x))]);
    return outerE( e[len] , procname( mred ))
          - procname( outerM(m[1$len],  mred ) - x);
  end;
end proc:
###############################################################
###############################################################
#
# makeRimRep is a cast from a partition into a representation of a 
#            partition by noting its E-N directions by 1-0 symbols
#            This sequence is infinite having infinit many leading 0
#            and traling 1s (which are of course not stored)
#
makeRimRep:=proc(part)
   option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`
          ,remember;
   local n1,diff,res,i;
   n1:=nops(part);
   diff:=[part[-1],seq(-part[n1+1-i]+part[n1-i],i=1..n1-1)];
   res:=[];
   for i from 1 to nops(diff) do
      res:=[op(res),seq(1,j=1..diff[i]),0];
   end do;
   res;
end proc:
#
#  removeRimHook removes a rim hook (edgewise conected boundary strip)
#                of length hocklength in all possible ways. It returns 
#                a list with the rimrepresented partitions of the remaining
#                part of the partition and a list with the rimheight attached to
#                the removed hoocks.
#
removeRimHook:=proc(rimrep,hooklength)
   option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
          remember;
   local i,j,mult,redrimrep,rimhieght,nrr,tmprim,del0,del1;
   redrimrep:=[];
   rimhieght:=[];
   nrr:=nops(rimrep);
   for i from 1 to nrr-1 do
     if rimrep[i]=1 then
       for j from i+1 to nrr do
         if rimrep[j]=0 then
           if j-i=hooklength then
             tmprim:=rimrep;
             tmprim[i]:=0;
             tmprim[j]:=1; 
             redrimrep:=[op(redrimrep),tmprim];
             rimhieght  :=[op(rimhieght),
                         `+`(op(map(x->if x=0 then 1 else 0 end if,[seq(tmprim[k],k=i+1..j-1)])))] 
           end if;              
         end if;  
       end do;   
     end if;
   end do;
###############
      del0:=proc(lst)
        local flag;
        flag:=false;
        map(x->if x=0 and flag=false then return NULL else flag:=true; return x end if,lst); 
      end proc:
      del1:=proc(lst)
        local flag,f,res,i;
        flag:=false;
        f:=x->if x=1 and flag=false then return NULL else flag:=true; return x end if;
        res:=[];
        for i from nops(lst) to 1 by -1 do
          res:=[f(lst[i]),op(res)];
        end do; 
      end proc:
################    
   map(del0,map(del1,redrimrep)),rimhieght;
end proc:
#
# MurNakRim This is the function which computes the Murnaghan Nakayama rule
#           in terms of the rim representation of a shape. It is internal,
#           since rim representations of shapes are not supported on the user 
#           side of the package.
#
MurNakRim:=proc(rimRep,part2)
   option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
          remember;
   local pt1,pt2,lst,sign;
   if nops(part2)=1 then
      lst,sign:=removeRimHook(rimRep,part2[1]);
      return add((-1)^i,i=sign);
   else
      pt1:=part2[1];
      pt2:=part2[2..-1];
      lst,sign:=removeRimHook(rimRep,pt1);
      return add((-1)^sign[i]*procname(lst[i],pt2),i=1..nops(lst));
   end if;
end proc:
#
# MurNak This function provides the interface for the function MurNakRim to
#        compute the Murnaghan-Nakayama rule. This function returns the character
#        value of an S_n character with cycletype part1 on an element of S_n
#        with cycletype part2.
#
# NOTE:  MurNak should be defined as scalar(s[part1],p[part2]) which is the
#        _transpodes_ of the present MurNak!
#
MurNak:=proc(part1,part2)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
          remember;
  if `+`(op(part1))<>`+`(op(part2)) then 
    # -- This function is graded, for different grades return zero 
    return 0;
  else
    # -- else use MurNakRim which needs a rim representation in the first argument
    # -- MurNak is _not_ symmetric in its entries
    return MurNakRim(makeRimRep(part2),part1);
  end if;
end proc:
#
# CharHook compute the character <sfkt,pfkt> if pfkt is a one part partition power
#          sum. The result is zero unless sfkt={a+1,1^b} is a Hook in which case
#          the value of the character is (-1)^b, the height of the hook (leglength)
#
CharHook:=proc(sfkt,pfkt)
   option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
          remember;
   local spart,ppart,ns,np;
   spart:=[op(sfkt)];
   ppart:=[op(pfkt)];
   np:=ppart[1];
   ns:=`+`(op(spart));
   if ns<>np then return 0 end if;
## -- check if s is a hook
   if spart[1]+nops(spart)-1<>ns then return 0 end if;
   (-1)^(nops(spart)-1);    
end proc:
#
# sq_coeff returns the square of the coefficients of a symmetric
#          function polynomial of a certain type.
#
#
sq_coeff:=proc(x,typ::type)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local  lst;
  if x=0 then 
    return 0
  elif type(x,`+`) then 
    lst:=[op(x)];
  else 
    lst:=[x];
  end if;
  lst:=map(x->if type(x,`*`) then remove(type,x,typ) else 1 end if,lst);
  add(i^2,i=lst);
end proc:
#
#
#
# MurNak2 is a function which as a proof of concept shows how the Murnaghan Nakayama
#         rule can be evaluatedon base of the Littlewood Richardson rule and the
#         character formula on Hook Shapes \Chi^\lambda_n=Scalar(s_\lambda,p[n]). It
#         is much slower than the rimRep based function.
#
# WARINING: MurNak2 needs FLAT and MLIN which make functions associative and multilinear
#         This should be replaced by a better version of 'define' which specifies not
#         the base ring, but the types of the generating basis elemnts.
#
MurNak2:=proc(sfkt,pfkt)
   option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`
          ,remember;
   local spart,ppart,ns,np,sw,CH;
   spart:=[op(sfkt)];
   ppart:=[op(pfkt)];
#   sw:=proc() T(args[1],args[3],args[2],args[4]) end proc:
#   CH:=proc() CharHook(args[1],args[2])*MurNak2(args[3],args[4]) end proc:
   CH:=(a1,a2,a3,a4) -> CharHook(a1,a3)*MurNak2(a2,a4): 
   if nops(pfkt)=1 then 
      return CharHook(sfkt,pfkt);
   else
     T(subs(`&t`=T,couter(sfkt)),s[ppart[1]],s[op(ppart[2..-1])]);
     FLAT(eval(subs(T=MLIN,%)));
#     eval(subs(T=sw,%));
     eval(subs(T=CH,%));
   end if;
end proc:
########################################
#
# dimSN_mon computes the dimension of an SN character
#           according to the hook rule for an Sn character
#           s[lambda] (Schur function monom)
#           ++ dimSN(s[\lambda]) = 
#           ++   factorial(|\lambda|)/\prod_{i,j} h_ij  where
#           ++   h_ij is the length of the hook at position (i,j)
#           ++   in the Young diagram of \lambda 
#
#
dimSN_mon:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,remember;
  local part,part_conj,np,i,j,hooks;
  if x=0 then return 0 end if;
  part:=[op(x)];
  if part=[0] then return 0 end if;
  np:=nops(part);
  part_conj:=conjpart(part);
  hooks:=1;
  for i from 1 to np do
  for j from 1 to part[i] do
     hooks:=hooks *( (part[i]-j+1)+max(part_conj[j]-i , 0) );
  end do;end do;
  factorial(`+`(op(part)))/hooks;
end proc:
#
# dimSN is the multilinear version of simSN_mon
#
dimSN:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,tm,n1,plst1,plst2,i;
  if type(x,`+`) then 
    return map(procname,x,y);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,sfktmonom);
    return cf*procname(tm,y)
  else
    dimSN_mon(x);  
  end if;
end proc:
#
# dimSNP gives the dimension of S_n-modules in the 
#        power sum symmetric function basis
#
dimSNP:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,tm;
  if x=0 then return 0 end if;
  if x=p[0] then return 0 end if;
  if type(x,`+`) then 
    return map(procname,x);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,pfktmonom);
    return cf*procname(tm)
  else
    if `+`(op(x))=nops([op(x)]) then
      return `+`(op(x))!;
    else 
      return 0;
    end if;  
  end if;
end proc:
#
# dimSNM gives the dimension of S_n-modules in the 
#        monomial symmetric function basis
#
dimSNM:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,tm;
  if x=0 then return 0 end if;
  if x=m[0] then return 0 end if;
  if type(x,`+`) then 
    return map(procname,x);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,mfktmonom);
    return cf*procname(tm)
  else
    if `+`(op(x))=nops([op(x)]) then
      return 1
    else 
      return 0;
    end if;  
  end if;
end proc:
#
# dimSNH gives the dimension of S_n-modules in the 
#        compleete symmetric function basis
#
dimSNH:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,tm;
  if x=0 then return 0 end if;
  if x=h[0] then return 0 end if;
  if type(x,`+`) then 
    return map(procname,x);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,hfktmonom);
    return cf*procname(tm)
  else
    return combinat:-multinomial(`+`(op(x)),op(x));
  end if;
end proc:
#
# dimSNE gives the dimension of S_n-modules in the 
#        elementray symmetric function basis
#
dimSNE:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,tm;
  if x=0 then return 0 end if;
  if x=e[0] then return 0 end if;
  if type(x,`+`) then 
    return map(procname,x);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,efktmonom);
    return cf*procname(tm)
  else
    return combinat:-multinomial(`+`(op(x)),op(x));
  end if;
end proc:
########################################
#
# dimGL_mon computes the dimension of an GL(N) character
#           according to the hook rule for an Sn character
#           s[lambda] (Schur function monom)
#           ++ dimGL(s[\lambda],N) = 
#           ++   content/\prod_{i,j} h_ij  where
#           ++   h_ij is the length of the hook at position (i,j)
#           ++   in the Young diagram of \lambda,
#           ++   content is the product of the content of the 
#           ++   boxes x(i,j)=N-i+j  (i,j = row,column) and N the dim
#           ++ of the vectorspace underlying GL(N) 
#
#
dimGL_mon:=proc(x,N)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,remember;
  local part,part_conj,np,i,j,hooks,content;
  if x=0 then return 0 end if;
  part:=[op(x)];
  if part=[0] then return 1 end if;
  np:=nops(part);
  part_conj:=conjpart(part);
  hooks:=1;
  content:=1;
  for i from 1 to np do
  for j from 1 to part[i] do
     hooks:=hooks *( (part[i]-j+1)+max(part_conj[j]-i , 0) );
     content:=content*(N-i+j);
  end do;end do;
  content/hooks;
end proc:
#
# dimGL is the multilinear version of dimGL_mon
#
dimGL:=proc(x,N)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,tm,n1,plst1,plst2,i;
  if type(x,`+`) then 
    return map(procname,x,N);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,sfktmonom);
    return cf*procname(tm,N)
  else
    dimGL_mon(x,N);  
  end if;
end proc:
################################################
#
# dimGLP_mon gives the dimension of a monomial representing a module in the 
#        power sum symmetric function basis
#
#
dimGLP_mon:=proc(pfkt,N)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  if pfkt=0 then 
    return 0
  elif pfkt=p[0] then 
    return 1
  else
    N^(nops([op(pfkt)]));
  end if;
end proc:
#
# dimGLP gives the dimension of a sum of GL-modules in the 
#        power sum symmetric function basis
#
dimGLP:=proc(x,N)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,tm;
  if x=0 then return 0 end if;
  if x=p[0] then return 1 end if;
  if type(x,`+`) then 
    return map(procname,x,N);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,pfktmonom);
    return cf*procname(tm,N)
  else
    dimGLP_mon(x,N);  
  end if;
end proc:
#
# dimGLM gives the dimension of a sum of GL-modules in the 
#        monomial symmetric function basis
#
dimGLM:=proc(x,N)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,tm;
  if x=0 then return 0 end if;
  if x=m[0] then return 1 end if;
  if type(x,`+`) then 
    return map(procname,x,N);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,mfktmonom);
    return cf*procname(tm,N)
  else
    factor(1/(`*`(op(map(x->x!,part2mset([op(x)])))))*fallingFactorial(N,nops([op(x)])));
  end if;
end proc:
#
# dimGLH gives the dimension of a sum of GL-modules in the 
#        compleete symmetric function basis
#
dimGLH:=proc(x,N)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,tm;
  if x=0 then return 0 end if;
  if x=h[0] then return 1 end if;
  if type(x,`+`) then 
    return map(procname,x,N);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,hfktmonom);
    return cf*procname(tm,N)
  else
    factor(1/(`*`(op(map(x->x!,[op(x)])))) * `*`(op(map2(risingFactorial,N,[op(x)]))));
 end if;
end proc:
#
# dimGLE gives the dimension of a sum of GL-modules in the 
#        elementray symmetric function basis
#
dimGLE:=proc(x,N)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,tm;
  if x=0 then return 0 end if;
  if x=e[0] then return 1 end if;
  if type(x,`+`) then 
    return map(procname,x,N);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,efktmonom);
    return cf*procname(tm,N)
  else
    factor(1/(`*`(op(map(x->x!,[op(x)])))) * `*`(op(map2(fallingFactorial,N,[op(x)]))));
 end if;
end proc:
###############################################################################
#
# G E S S E L T H E T A functions
#
###############################################################################
#
# GesselTheta is the Gessel map from a polynomial ring in infinitley many
#     (finitely many) variables 'u1,u2,u3,...' into a polynomial ring
#     in one variable 'z', say. The map is ussefull for counting purpose and
#     defined as follows:
#
# -- i)   \Theta(1) = 1
# -- ii)  \Theta(p_n(u)) = z if n=1 else 0
#
#     we have therefore for S-functiuons
#
# -- iii) \Theta(s_\lambda(u)) = f^\lambda z^(|\lambda|) / (|\lambda|)!
#
#    where |\lambda| is the weight of a partition lambda and
#    f^\lambda is the number of standard Young tableau of shape
#    \lambda i.e. SYT(\lambda)=dimSN(s[\lambda](u))
#
###############################################################################
#
# GesselThetaP_mon is the theta function given for power sum monomials
#
GesselThetaP_mon:=proc(x,var)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remeber;
  local n;
  if (x=p[0] or x=1) then return 1 end if;
  n:=nops([op(x)]);
  if n=`+`(op(x)) then var^n else 0 end if;
end proc:
#
# GesselThetaP is the linear version for the Gessel map theta for 
#              power sum polynomials
#
GesselThetaP:=proc(x,var)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,tm;
  if type(x,`+`) then 
    return map(procname,x,var);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,pfktmonom);
    return cf*GesselThetaP_mon(tm,var)
  else
    GesselThetaP_mon(x,var);  
  end if;
end proc:
#
# GesselThetaS_mon is the theta function given for Schur function monomials
#
GesselThetaS_mon:=proc(x,var)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remeber;
  local N;
  if (x=s[0] or x=1) then return 1 end if;
  N:=`+`(op(x));
  dimSN(x)*var^N/factorial(N); 
end proc:
#
# GesselThetaS is the linear version for the Gessel map theta for 
#              Schur function polynomials
#
GesselThetaS:=proc(x,var)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,tm;
  if type(x,`+`) then 
    return map(procname,x,var);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,sfktmonom);
    return cf*GesselThetaS_mon(tm,var)
  else
    GesselThetaS_mon(x,var);  
  end if;
end proc:

########################################
#
# Functions for s-functions
#
########################################


################################################################################
#
# S C A L A R PRODUCTS
#
#     for different bases
#
################################################################################
#
# +++ scalar product of schur functions
#
Scalar:=proc(x,y)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,tm,p1,p2;
  if x=0 or y=0 then return 0 end if;
  if not (type(x,sfktpolynom) and type(y,sfktpolynom)) then error "wrong type\n" end if;
  if type(x,`+`) then 
    return map(procname,x,y);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,sfktmonom);
    return cf*procname(tm,y)
  else
    if type(y,`+`) then 
      return map2(procname,x,y);
    elif type(y,`*`) then
      tm,cf:=selectremove(type,y,sfktmonom);
      return cf*procname(x,tm)
    else
      p1:=getPart(x):p2:=getPart(y):
      if   nops(p1)<nops(p2) then p1:=[op(p1),0$(nops(p2)-nops(p1))];
      elif nops(p1)>nops(p2) then p2:=[op(p2),0$(nops(p1)-nops(p2))];
      end if;
      if {op(zip((i,j)->i-j,p1,p2))}={0} then return s[0] else return 0 end if;
    end if;
  end if;
end proc:
#####################################################################################
#
# ScalarP is the Schur-Hall scalar product on power sum functions
#
ScalarP:=proc(x,y)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,tm,p1,p2;
  if not (type(x,pfktpolynom) and type(y,pfktpolynom)) then error "wrong type\n" end if;
  if type(x,`+`) then 
    return map(procname,x,y);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,pfktmonom);
    return cf*procname(tm,y)
  else
    if type(y,`+`) then 
      return map2(procname,x,y);
    elif type(y,`*`) then
      tm,cf:=selectremove(type,y,pfktmonom);
      return cf*procname(x,tm)
    else
      ###
      p1:=[op(x)];
      p2:=[op(y)];
      if `+`(op(p1))<>`+`(op(p2)) then return 0 end if;
      if {op(zip((x,y)->x-y,p1,p2))}={0} then 
        return zee(p1) 
      end if;
      0;
      ### 
    end if;
  end if;
end proc:
##################################################################################
#
# ScalarMH is the Schur-Hall scalar product for the dual pair of complete symmetric 
#          functions and monomial symmetric functions. Alias is ScalarHM
#
#
ScalarMH:=proc(x,y)
   option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved`;
   if x=0 or y=0 then return 0 end if;
   if type(x,mfktpolynom) and type(y,hfktpolynom) then 
      return Scalar(subs(`m`=s,x),subs(`h`=s,y)) end if;
      if type(x,hfktpolynom) and type(y,mfktpolynom) then 
      return Scalar(subs(`h`=s,x),subs(`m`=s,y)) end if;
   error "unknown type in ScalarHM";
end proc:
ScalarHM:=(x,y)->ScalarMH(y,x);
################################################################################
#
# ScalarBinomialP is the bilinear form which extends the binomial of partitions
#
# 
ScalarBinomialP:=proc(x,y)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,tm,p1,p2;
  if x=0 or y=0 then return 0 end if;
  if not (type(x,pfktpolynom) and type(y,pfktpolynom)) then error "wrong type\n" end if;
  if type(x,`+`) then
    return map(procname,x,y);
  elif type(x,`*`) then
    tm,cf:=selectremove(type,x,pfktmonom);
    return cf*procname(tm,y)
  else
    if type(y,`+`) then
      return map2(procname,x,y);
    elif type(y,`*`) then
      tm,cf:=selectremove(type,y,pfktmonom);
      return cf*procname(x,tm)
    else
      partBinomial([op(x)],[op(y)]);
    end if;
  end if;
end proc:
################################################################################
#
# ScalarBinomialS is the bilinear form which extends the binomial of partritions
#     in the p-basis to the S-basis. We use that binomial coefficients fulfil:
#     
#       binomialP(\mu,\nu) =  zeeP(p_\mu,p_\nu)*zeebarP(p_\mu)*zeebarP(p_\nu)
# 
#     which can be generalized to the S-function situation. 
#
ScalarBinomialS:=proc(x,y)
  zeeS(outer(x,y))*zeebarS(x)*zeebarS(y);  
end proc:
#
#####################################################################################
#
# O U T E R MONOID
#
#####################################################################################
#
#
# outer product for S functions, this is the default proceedure, alias is outerS
#
outer:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,tm,p1,p2,y;
  if nargs=1 then return x end if;
  y:=args[2];
  if x=0 or y=0 then return 0 end if;
  if nargs>2 then return procname(expand(procname(x,y)),args[3..-1]) end if;
  if not(type(x,sfktpolynom) and type(args[2],sfktpolynom)) then error "wrong type\n" end if;
  if type(x,`+`) then 
    return map(procname,x,y);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,sfktmonom);
    return cf*procname(tm,y)
  else
    if type(y,`+`) then 
      return map2(procname,x,y);
    elif type(y,`*`) then
      tm,cf:=selectremove(type,y,sfktmonom);
      return cf*procname(x,tm)
    else
      if x=0 or y=0 then return 0 end if;
      p1:=getPart(x): p2:=getPart(y):
# +++ it is faster to add fewer boxes
# --- the product is symmetric
      if `+`(op(p1))<`+`(op(p2)) then 
        return LRR(p2,p1);
      else
        return LRR(p1,p2);
      end if;
    end if;
  end if;
end proc:
#
# +++ alias for outer product in Schur function basis
#
outerS:=outer:
#
#
# outerLS computes the product of two or any number of Schur functions [monoms]
#     using the Lascoux Schuetzenberger transition algorithm. after some checking
#     of the input for invalid or special input, we produce the permutation
#     which is isomorphic to the concatenation of the Lehmer codes od the
#     input Schur functions. The transition algorithm descomposes this
#     permutation into Grassmannian ones which are turned byck into Schur functions
#     and then added up for output.
#
outerLS:=proc(x)
  local perLst,res,res2,per,i,nopsD;
  #-- nothing to do
  if nargs=1 then return x end if;
  #-- concattenate the Lehmer codes of inputs and turn into a permutation
  perLst:= [ lehmerCodeToPermutation( op([ map(op@schurToLehmerCode1,[args])])) ];
  nopsD:=nops(Descents(op(perLst)));
  #-- deal with special cases 0 descest output s[0], 
  #-- 1 descent=Grassmannian permutation = Schur function
  if nopsD=0 then 
     return s[0]
  elif nopsD=1 then 
     return lehmerCodeToSchurFkt(permutationToLehmerCode(op(perLst)))
  end if;
  # start computation: for all permutations in perlst applay the
  # transition algorithm (possibly increasing the length of the list)
  # If the number of descents for a permutatin is 1 add to result
  # othewise feed back to perLst
  res:=0;
  while perLst<>[] do
    per:=perLst[1];
    perLst:=perLst[2..-1];
    res2:=transition(per);
    for i from 1 to nops(res2) do 
       if nops(Descents(res2[i]))=1 then 
          res:=res+lehmerCodeToSchurFkt(permutationToLehmerCode(res2[i]));
       else
          perLst:=[res2[i],op(perLst)];
       end if;
    end do;
  end do;  
  res;
end proc:
#
#
# concatM_mon multiplies two monomials (mfktmonom) using the divided power representation of 
#             Rota-Stein 94
# WARNING:    this is _not_ the outer product of symmetric functions, but a concatenation 
#             product in a divided powers algebra!
#
#             (Internal use only)
#
concatM_mon:=proc(fkt1,fkt2)
   option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
   remember;
   local mset1,mset2,n1,n2,N,lst,cf,res,i;
   if fkt1=0 or fkt2=0 then return 0 end if;
   mset1,mset2:=part2mset([op(fkt1)]),part2mset([op(fkt2)]);
   n1,n2:=nops(mset1),nops(mset2);
   if n1>n2 then
     N:=n1;
     mset2:=[op(mset2),0$(n1-n2)];
   elif n2>n1 then
     N:=n2;
     mset1:=[op(mset1),0$(n2-n1)];
   else
     N:=n1;
   end if;
   lst:=[seq([binomial(mset1[i]+mset2[i],mset1[i]),mset1[i]+mset2[i]] ,i=1..N)];
   cf,res:=1,[];
   for i in lst do
     cf:=cf*i[1];
     res:=[op(res),i[2]];
   end do;   
   cf*m[op(mset2part(res))];
end proc:
#
# concatM provides the concatemation product of m-functions (not the outer product of 
#         symmetric functions!) This product is needed to produce a 'clifford' type
#         product for the outer m-function product
#
#
concatM:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm,p1,p2,y;
  if nargs=1 then return x end if;
  y:=args[2];
  if x=0 or y=0 then return 0 end if;
  if nargs>2 then return procname(expand(procname(x,y)),args[3..-1]) end if;
  if not(type(x,mfktpolynom) and type(args[2],mfktpolynom)) then error "wrong type\n" end if;
  if type(x,`+`) then 
    return map(procname,x,y);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,mfktmonom);
    return cf*procname(tm,y)
  else
    if type(y,`+`) then 
      return map2(procname,x,y);
    elif type(y,`*`) then
      tm,cf:=selectremove(type,y,mfktmonom);
      return cf*procname(x,tm)
    else
      if x=0 or y=0 then return 0 end if;
      concatM_mon(x,y)
    end if;
  end if;
end proc:
#
#
# concat_mon multiplies two monomials (e-, h-, p-function monoms) 
#            This _is_ the outer product! for these bases 
#
#             (Internal use only)
#
concat_mon:=proc(fkt1,fkt2,name)
   option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
   remember;
   local lst;
   lst:=[op(fkt1),op(fkt2)];
   name[op(sort(lst,(i,j)->if i>j then true else false end if))];
end proc:
#
# outerH,E,P are functions providing the outer product of complete, elementary and power sum
#         symmetric functions. These products are the outer products on these bases, since
#         these particular bases are multiplicateive bases.
#
#
outerH:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm,p1,p2,y;
  if nargs=1 then return x end if;
  y:=args[2];
  if x=0 or y=0 then return 0 end if;
  if nargs>2 then return procname(expand(procname(x,y)),args[3..-1]) end if;
  if not(type(x,hfktpolynom) and type(y,hfktpolynom)) then error "wrong type\n" end if;
  if type(x,`+`) then 
    return map(procname,x,y);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,hfktmonom);
    return cf*procname(tm,y)
  else
    if type(y,`+`) then 
      return map2(procname,x,y);
    elif type(y,`*`) then
      tm,cf:=selectremove(type,y,hfktmonom);
      return cf*procname(x,tm)
    else
      if x=0 or y=0 then return 0 end if;
      if x=h[0] then return y end if;
      if y=h[0] then return x end if;
      concat_mon(x,y,`h`)
    end if;
  end if;
end proc:
#
#
#
outerE:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm,p1,p2,y;
  if nargs=1 then return x end if;
  y:=args[2];
  if x=0 or y=0 then return 0 end if;
  if nargs>2 then return procname(expand(procname(x,y)),args[3..-1]) end if;
  if not(type(x,efktpolynom) and type(args[2],efktpolynom)) then error "wrong type\n" end if;
  if type(x,`+`) then 
    return map(procname,x,y);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,efktmonom);
    return cf*procname(tm,y)
  else
    if type(y,`+`) then 
      return map2(procname,x,y);
    elif type(y,`*`) then
      tm,cf:=selectremove(type,y,efktmonom);
      return cf*procname(x,tm)
    else
      if x=0 or y=0 then return 0 end if;
      if x=e[0] then return y end if;
      if y=e[0] then return x end if;
      concat_mon(x,y,`e`)
    end if;
  end if;
end proc:
#
#
#
outerP:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm,p1,p2,y;
  if nargs=1 then return x end if;
  y:=args[2];
  if x=0 or y=0 then return 0 end if;
  if nargs>2 then return procname(expand(procname(x,y)),args[3..-1]) end if;
  if not(type(x,pfktpolynom) and type(args[2],pfktpolynom)) then error "wrong type\n" end if;
  if type(x,`+`) then 
    return map(procname,x,y);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,pfktmonom);
    return cf*procname(tm,y)
  else
    if type(y,`+`) then 
      return map2(procname,x,y);
    elif type(y,`*`) then
      tm,cf:=selectremove(type,y,pfktmonom);
      return cf*procname(x,tm)
    else
      if x=0 or y=0 then return 0 end if;
      if x=p[0] then return y end if;
      if y=p[0] then return x end if;
      concat_mon(x,y,`p`)
    end if;
  end if;
end proc:
########################################################################################
#
# O U T E R COMONOID
#
#
########################################################################################
#
# couterM_mon computes the outer coproduct of the m-basis m-functions
#
# (Internal use only)
#
couterM_mon:=proc(mfkt)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local mset,T,res,nT;
  if mfkt=0 then return(0) end if;
  mset:=part2mset([op(mfkt)]);
  T:=combinat[cartprod]([seq([seq(k,k=0..mset[i])],i=1..nops(mset))]):
  res:=[];
  while not T[finished] do
    nT:=T[nextvalue](); 
    res:=[op(res),[mset-nT,nT]] 
  end do;
  add(&t(m[op(mset2part(i[1]))],m[op(mset2part(i[2]))]),i=res);
end proc:
#
#
# couterM computes the outer coproduct in the m-basis. This is essentially a wrapper
#         function for couterM_mon on monomials, making it multilinear over the
#         integers.
#
#
couterM:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm,n1,plst1,plst2,i;
  if x=0 then return(0) end if;
  if type(x,`+`) then 
    return map(procname,x,y);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,mfktmonom);
    return cf*procname(tm,y)
  else
    if x=m[0] then return &t(m[0],m[0]) end if;
    couterM_mon(x);  
  end if;
end proc:
#
# LaplaceMset is a internal function which implements the Laplace Pairing of Rota-Stein
#             in tha case of monomial symmetric functions. For efficiency reasons, it
#             uses a third representation of sparse-multisets M(\prod_k [i_k,ni_k])
#             where the zero entries [n,0] are omitted! 
#
#
LaplaceMset:=proc(Mset1,Mset2)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local n1,n2,T,nT,res,a,b,c,d;
  n1,n2:=nops(Mset1),nops(Mset2);
  # -- check for m[0]=1 cases directly
  if n1=0 and n2=0 then return M() end if;
  if n1=0 or n2=0 then return 0 end if;
  if n1=1 then
    if n2=1 then
      # -- case n1=n2=1 definition applies directly
      if op(Mset1)[2]=op(Mset2)[2] then 
        return M([op(Mset1)[1]+op(Mset2)[1],op(Mset1)[2]]);
      else
        return 0;
      end if; 
    else
      # --n1=1, n2 a product
      return add(MCAT(
                      procname( M([ op(Mset1)[1] , k ]) , M( op(Mset2)[1] ) )
                     ,procname( M([ op(Mset1)[1] , op(Mset1)[2]-k ]), M( op(Mset2)[2..-1] ) )   
                     )
                ,k=0..op(Mset1)[2] );
    end if;
  else
    # -- n1 a product
    if n2=1 then
      # -- n2 not a product
      return add(MCAT(
                      procname( M([ op(Mset2)[1] , k ]) , M( op(Mset1)[1] ) )
                     ,procname( M([ op(Mset2)[1] , op(Mset2)[2]-k ]), M( op(Mset1)[2..-1] ) )
                     )
                ,k=0..op(Mset2)[2] );
    else
      # -- n1 and n2 products, expand second argument ...
      a,b:=M([op(Mset1)][1]),M(op([op(Mset1)][2..-1]));
      c:=[seq([op(Mset2)][i][1],i=1..nops([op(Mset2)]))];
      d:=[seq([op(Mset2)][i][2],i=1..nops([op(Mset2)]))];
      T:=combinat[cartprod]([seq([seq(k,k=0..[op(Mset2)][i][2])],i=1..nops([op(Mset2)]))]):
      res:=[];
      while not T[finished] do
        nT:=T[nextvalue](); 
        res:=[op(res),[d-nT,nT]] 
      end do;
      add(MCAT(
               procname(a,M(seq([c[k],i[1][k]],k=1..nops(c)) ))
              ,procname(b,M(seq([c[k],i[2][k]],k=1..nops(c)) ))
              )
          ,i=res);
    end if;
  end if;
end proc:
#
# LaplaceM_mon is the wrapper function for LaplaceMset and computes the Laplace pairing
#          between two _monomials_ in the monoamial symmetric function basis. Unless
#          it is bilinear it is for internal use in the outerM product mainly.
#
#
LaplaceM_mon:=proc(mfkt1,mfkt2)
   option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
   remember;
   local mset1,mset2,f;
# -- SPECIAL CASES
# -- LaplaceM is _not_ graded, by weight of the partitions of the mfkt's
# -- However, LaplaceM _is graded_ by the _length_ of the partitions!!
# -- The case m[0] is crittical since part2mset does return an empty list
# -- we deal hence with these cases seperately:
# -- LaplaceM(m[0],m[0])=m[0]
# -- LaplaceM(m[0],<any-mfkt>) = 0 = LaplaceM(<any-mfkt>,m[0])
   if nops([op(mfkt1)])<>nops([op(mfkt2)]) then return 0 end if;
   if mfkt1=m[0] and mfkt2=m[0] then return m[0] end if;
   if mfkt1=m[0] or mfkt2=m[0] then return 0 end if;
# -- transform partitions into msets M([i1,ni1],[i2,ni2],...)
   mset1,mset2:=part2mset([op(mfkt1)]),part2mset([op(mfkt2)]);
# -- f is a helper function which turns M-set representations back into
# -- a partition representation
   f:=proc()
      local x,n;
      x,n:=args,nargs;
      m[op( sort([seq([x][k][1]$[x][k][2],k=1..n)]) )];
   end proc:
# -- call the actual LaplaceMset proceedure
   LaplaceMset(M(seq([k,mset1[k]],k=1..nops(mset1))),M(seq([k,mset2[k]],k=1..nops(mset2))));
# -- Turn the M-set representation output of LaplaceMset into a partition based form
   eval(subs(M=f,%));
# -- substitute the unevaluated concatenation product MCAT into the actual concatM product
# -- and return the final result 
   eval(subs(MCAT=concatM,%));
end proc:
#
# The wrapper which makes LaplaceM_mon multilinear
#
LaplaceM2:=proc(x,y)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,tm,p1,p2;
  if x=0 or y=0 then return 0 end if;
  if not (type(x,mfktpolynom) and type(y,mfktpolynom)) then error "wrong type\n" end if;
  if type(x,`+`) then 
    return map(procname,x,y);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,mfktmonom);
    return cf*procname(tm,y)
  else
    if type(y,`+`) then 
      return map2(procname,x,y);
    elif type(y,`*`) then
      tm,cf:=selectremove(type,y,mfktmonom);
      return cf*procname(x,tm)
    else
#      if x=m[0] then return y end if;
#      if y=m[0] then return x end if;
      LaplaceM_mon(x,y);
    end if;
  end if;
end proc:
####################################################################################
#
# Laplace helper functions:
#
# ----------------------------------------------------------------------------------
#
# LP_l1 computes the LaplaceM pairing for monomials of length < 2
# 
LP_l1:=proc(x,y)
  option remember;
  if x=m[0] or y=m[0] then
    if y=x then
      return m[0]
    else 
      return 0
    end if;
  end if;
  return m[op(x)+op(y)];
end proc:
#
# couterMproper1n computes the proper coproduct slice of length 1,n where
#                 the original monomial has length n+1
#
couterMproper1n:=proc(x)
  option remember;
  local lst,mset;
  if x=0 then return 0 end if;
  if x=m[0] then return &t(m[0],m[0]) end if;
  lst:={op(x)};
  mset:=part2mset([op(x)]);
  add(&t(m[i],m[op( mset2part(mset-[0$(i-1),1,0$(nops(mset)-i)]))]) ,i in lst);
end proc:
#
# LP_mon is the actual LaplaceM pairing evaluated on arbitrary m-basis monomials
#        LP_mon is faster and more memory efficient than the old algorithm. It was 
#        seriously tested against the old routine.
#
LP_mon:=proc(x,y)
  option remember;
  local lx,ly,f0,beta,res;
  lx,ly:=nops([op(x)]),nops([op(y)]);
  if lx<>ly then return 0 end if;
  if lx<2 then return LP_l1(x,y) end if;
  # -- the Laplace property (due to the length constraint we need only one direction)
  # -- we split of a single entry in the second fcator
  # -- the coproduct needs only terms of the length type 1,n, this is provided by
  # -- the function couterMproper1n
  # -- beta is a numerical factor needed to split m-basis monomials into a
  # -- concatenation product of two parts : concatM(A,B)/beta(C) = C
  beta:=coeff(concatM(m[[op(y)][1]], m[op([op(y)][2..-1])]),y);
  f0:=(a,b,c,d)->concatM(LP_mon(a,c),LP_mon(b,d));
  eval(1/beta*subs(`&t`=f0, 
     &t( couterMproper1n(x),  m[[op(y)][1]], m[op([op(y)][2..-1])] )
  ));   
end proc:
#
# The wrapper which makes LaplaceM_mon multilinear
#
LaplaceM:=proc(x,y)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,tm,p1,p2;
  if x=0 or y=0 then return 0 end if;
  if not (type(x,mfktpolynom) and type(y,mfktpolynom)) then error "wrong type\n" end if;
  if type(x,`+`) then 
    return map(procname,x,y);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,mfktmonom);
    return cf*procname(tm,y)
  else
    if type(y,`+`) then 
      return map2(procname,x,y);
    elif type(y,`*`) then
      tm,cf:=selectremove(type,y,mfktmonom);
      return cf*procname(x,tm)
    else
      LP_mon(x,y);
    end if;
  end if;
end proc:
#
# outerM the cliffordization of the concatM product, the outer product in the monomial
#        symmetric function basis. This function takes 1,2, or n variables (associactive)
#        and is multilinear over the integers / fractions.
#
#
outerM:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm,p1,p2,y,f;
  if nargs=1 then return x end if;
  y:=args[2];
  if x=0 or y=0 then return 0 end if;
  if nargs>2 then return procname(expand(procname(x,y)),args[3..-1]) end if;
  if not(type(x,mfktpolynom) and type(args[2],mfktpolynom)) then error "wrong type\n" end if;
  if type(x,`+`) then 
    return map(procname,x,y);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,mfktmonom);
    return cf*procname(tm,y)
  else
    if type(y,`+`) then 
      return map2(procname,x,y);
    elif type(y,`*`) then
      tm,cf:=selectremove(type,y,mfktmonom);
      return cf*procname(x,tm)
    else
      if x=0 or y=0 then return 0 end if;
      f:=(a,b,c,d)->concatM(LaplaceM_mon(a,c),concatM_mon(b,d));
      eval(subs(`&t`=f,&t(couterM(x),couterM(y))));
    end if;
  end if;
end proc:
########################################################################################
#
# A D J O I N T OPERATIONS / SKEWS
#
########################################################################################
#
#  +++ skew shur functions
#
#  skewLR computes the skew operation by dualiting the outer product based
#     on the Littlewood-Richarson rule, this is slow and ineefective, see skewLS below
#
skewLR:=proc(x,y)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,tm,n1,n2,n3,plst;
  if y=s[0] then return x; end if;
  if type(x,`+`) then 
    return map(procname,x,y);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,sfktmonom);
    return cf*procname(tm,y)
  else
    if type(y,`+`) then 
      return map2(procname,x,y);
    elif type(y,`*`) then
      tm,cf:=selectremove(type,y,sfktmonom);
      return cf*procname(x,tm)
    else
      n1:=`+`(op(getPart(x))):n2:=`+`(op(getPart(y))):
      n3:=n1-n2;
      if n3<0 then return 0 
      elif n3=0 then return Scalar(x,y) 
      else
        plst:=map(x->s[op(x)],[op(PartNM(n3,n3))]);
        return add(outer(Scalar(x,outer(y,z)),z),z=plst);
      end if;
    end if;
  end if;
end proc:
#
# skewLS computes the skew using the Lascoux Schuetzenberger transition algorithm
#     this is by fare the faster skew operation then the above one obtained by 
#     duality and is therefore set as default
#
skewLS:=proc(sf1,sf2)
  local perLst,res,res2,per,i,nopsD;
  #-- sf2=s[0] then nothing to do
  if sf2=s[0] then return sf1 end if;
  #-- check if sf1 covers sf2, otherwise zero
  if nops([op(sf1)])<nops([op(sf2)]) then return 0 end if;
  for i in zip((i,j)->i-j,[op(sf1)],[op(sf2)]) do
     if i<0 then return 0 end if;
  end do;
  #-- construct the permutation of the Lehmer code of the skew diagram
  perLst:=[lehmerCodeToPermutation( skewToLehmerCode(sf1,sf2) )];
  nopsD:=nops(Descents(op(perLst)));
  #-- deal with special cases 0 descest output s[0], 
  #-- 1 descent=Grassmannian permutation = Schur function
  if nopsD=0 then 
     return s[0]
  elif nopsD=1 then 
     return lehmerCodeToSchurFkt(permutationToLehmerCode(op(perLst)))
  end if;
  # start computation: for all permutations in perlst applay the
  # transition algorithm (possibly increasing the length of the list)
  # If the number of descents for a permutatin is 1 add to result
  # othewise feed back to perLst
  res:=0;
  while perLst<>[] do
    per:=perLst[1];
    perLst:=perLst[2..-1];
    res2:=transition(per);
    for i from 1 to nops(res2) do 
       if nops(Descents(res2[i]))=1 then 
          res:=res+lehmerCodeToSchurFkt(permutationToLehmerCode(res2[i]));
       else
          perLst:=[res2[i],op(perLst)];
       end if;
    end do;
  end do;  
  res;
end proc:
#
# DEFAULT: skewLS made linear
#
skew:=proc(x,y)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,tm,n1,n2,n3,plst;
  if y=s[0] then return x; end if;
  if type(x,`+`) then 
    return map(procname,x,y);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,sfktmonom);
    return cf*procname(tm,y)
  else
    if type(y,`+`) then 
      return map2(procname,x,y);
    elif type(y,`*`) then
      tm,cf:=selectremove(type,y,sfktmonom);
      return cf*procname(x,tm)
    else
      return skewLS(x,y);
    end if;
  end if;
end proc:
#
#
#
couter_mon:=proc(x)
   local par,parLst,pr;
   if x=s[0] then return &t(s[0],s[0]); end if;
   if x=s[1] then return &t(s[1],s[0])+&t(s[0],s[1]); end if;
   par:=[op(x)];
   parLst:=partitionsInShape(par);
   add(&t(s[op(pr)],skewLS(x,s[op(pr)])), pr in parLst);
end proc:
#
#
#
couter:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,tm,n1,plst1,plst2,i;
  if not type(x,sfktpolynom) then return x*procname(s[0]) end if;
  if type(x,`+`) then 
    return map(procname,x);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,sfktmonom);
    return cf*procname(tm)
  else
#----- obsolete code
#    if x=s[0] then return &t(s[0],s[0]) end if;
#    n1:=`+`(op(getPart(x))):
#    tm:=&t(s[0],x)+&t(x,s[0]);
#    for i from 1 to n1-1 do
#       plst1:=map(x->s[op(x)],PartNM(n1-i,n1));
#       plst2:=map(x->s[op(x)],PartNM(i,n1));
#       tm:=tm+add(add(subs(s[0]=1,Scalar(x,outer(y,z)))*&t(y,z),y=plst1),z=plst2);
#    end do;
#    return tm;
    return couter_mon(x);
  end if;
end proc:
#
#
# couterH_monom is the internal function computing the outer product on complete
#              symmetric functions monoms
#
#
couterH_mon:=proc(x)
   option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
          remember;
   local prtx,p1,f,g,l;
   prtx:=[op(x)];
   if prtx=[] or prtx=[0] then return &t(h[0],h[0]) end if;
   if nops(prtx)=1 then return add(&t(h[prtx[1]-i],h[i]),i=0..prtx[1]) end if;
   p1:=prtx[1];
   prtx:=prtx[2..-1];
   f:=(x,y,z)->&t(x,z,y):
   l:=proc(x)
      h[op(subs(0=NULL,[op(x)]))]; 
      if %=h[] then h[0] else % end if:
   end proc:
   g:=(x,y,s,t)->&t(l(outerH(x,y)),l(outerH(s,t))):
   eval(subs(`&t`=g,
          add(f(h[p1-i],h[i],procname(h[op(prtx)])) ,i=0..p1) ));
end proc:
#
#
# couterH computes the outer coproduct in the h-basis. This is essentially a wrapper
#         function for couterH_mon on monomials, making it multilinear over the
#         integers.
#
#
couterH:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm,n1,plst1,plst2,i;
  ####if not type(x,efktpolynom) then return x*procname(h[0]) end if;#####<<<<<BUG
  if not type(x,hfktpolynom) then return x*procname(h[0]) end if;
  if type(x,`+`) then 
    return map(procname,x,y);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,hfktmonom);
    return cf*procname(tm,y)
  else
    if type(y,`+`) then 
      return map2(procname,x,y);
    elif type(y,`*`) then
      cf,tm:=selectremove(type,y,integer);
      return cf*procname(x,tm)
    else
      if x=h[0] then return &t(h[0],h[0]) end if;
      couterH_mon(x);  
    end if;
  end if;
end proc:
#
#
# couterE_mon is the internal function computing the outer product on elementary
#              symmetric functions monoms
#
#
couterE_mon:=proc(x)
   option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
          remember;
   local prtx,p1,f,g,l;
   prtx:=[op(x)];
   if prtx=[] or prtx=[0] then return &t(e[0],e[0]) end if;
   if nops(prtx)=1 then return add(&t(e[prtx[1]-i],e[i]),i=0..prtx[1]) end if;
   p1:=prtx[1];
   prtx:=prtx[2..-1];
   f:=(x,y,z)->&t(x,z,y):
   l:=proc(x)
      e[op(subs(0=NULL,[op(x)]))]; 
      if %=e[] then e[0] else % end if:
   end proc:
   g:=(x,y,s,t)->&t(l(outerE(x,y)),l(outerE(s,t))):
   eval(subs(`&t`=g,
          add(f(e[p1-i],e[i],procname(e[op(prtx)])) ,i=0..p1) ));
end proc:
#
#
# couterE computes the outer coproduct in the e-basis. This is essentially a wrapper
#         function for couterE_mon on monomials, making it multilinear over the
#         integers.
#
#
couterE:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm,n1,plst1,plst2,i;
  if not type(x,efktpolynom) then return x*procname(e[0]) end if;
  if type(x,`+`) then 
    return map(procname,x,y);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,efktmonom);
    return cf*procname(tm,y)
  else
    couterE_mon(x);  
  end if;
end proc:
#
#
# couterP_mon is the internal function computing the outer product on power sum
#              symmetric functions monoms
#
#
couterP_mon:=proc(x)
   option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
          remember;
   local prtx,p1,f,g,l;
   prtx:=[op(x)];
   if prtx=[] or prtx=[0] then return &t(p[0],p[0]) end if;
   if nops(prtx)=1 then return &t(x,p[0])+&t(p[0],x) end if;
   p1:=prtx[1];
   prtx:=prtx[2..-1];
   f:=(x,y,z)->&t(x,z,y):
   l:=proc(x)
      p[op(subs(0=NULL,[op(x)]))]; 
      if %=p[] then p[0] else % end if:
   end proc:
   g:=(x,y,s,t)->&t(l(outerP(x,y)),l(outerP(s,t))):
   eval(subs(`&t`=g,
          f(p[p1],p[0],procname(p[op(prtx)]))
         +f(p[0],p[p1],procname(p[op(prtx)])) ));
end proc:
#
#
# couterP computes the outer coproduct in the p-basis. This is essentially a wrapper
#         function for couterP_mon on monomials, making it multilinear over the
#         integers.
#
#
couterP:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm,n1,plst1,plst2,i;
  if not type(x,pfktpolynom) then error "Power sum polynom expected...."; end if;
  if x=0 then return 0 end if;
  if type(x,`+`) then 
    return map(procname,x,y);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,pfktmonom);
    return cf*procname(tm,y)
  else
    couterP_mon(x);  
  end if;
end proc:
##################################################################################
#
# counits
#
counitS:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  coeff(x,s[0]); 
end proc;
#
counitP:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  coeff(x,p[0]); 
end proc;
#
counitM:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  coeff(x,m[0]);
end proc;
#
counitE:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  coeff(x,e[0]);
end proc;
#
counitH:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  coeff(x,h[0]);
end proc;
#
counitF:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  coeff(x,f[0]);
end proc;
#
#counitM:=proc(x)
#  local cf,term;
#  if type(x,`+`) then
#    return map(procname,x);
#  elif type(x,`*`) then
#    term,cf:=selectremove(type,x,mfktmonom);
#    return cf*procname(term);
#  else
#    if x=m[0] then 
#       return x;
#    else
#       return 0;
#    end if;
#  end if;
#end proc:
#
##################################################################################
#
# antipode for the Sfunctions
#
#
antipS_mon:=proc(sfkt)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`; 
  local p1,Lambda,i,k,N;
  p1:=[op(sfkt)];
  if `+`(op(p1))=0 then return s[0] end if;
  Lambda:=[0$`+`(op(p1))]:
  for i from 1 to nops(p1) do
  for k from 1 to p1[i] do
    Lambda[k]:=Lambda[k]+1;
  end do: end do:
  Lambda:=map(x-> if x=0 then NULL else x end if ,Lambda);   
  (-1)^(`+`(op(p1)))*s[op(Lambda)]; 
end proc:
#
# linear version for the antipode of the Sfunctions
#
#
antipS:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm,n1,plst1,plst2,i;
  if x=0 then return 0 end if;
  if x=s[0] then return s[0] end if;
  if type(x,`+`) then 
    return map(procname,x);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,sfktmonom);
    return cf*procname(tm)
  else
    antipS_mon(x);  
  end if;
end proc:
#
# antipode in the power sum basis
#
#
antipP_mon:=proc(pfkt)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  (-1)^(nops([op(pfkt)]))*pfkt; 
end proc:
#
# linear form of the power sum antipode
#
#
antipP:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm,n1,plst1,plst2,i;
  if x=0 then return 0 end if;
  if x=p[0] then return p[0] end if;
  if type(x,`+`) then 
    return map(procname,x);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,pfktmonom);
    return cf*procname(tm)
  else
    antipP_mon(x);  
  end if;
end proc:
#
# antipH_mon is the recursively defined antipode for the complete symmetric 
#            functions (internal use only)
#
antipH_mon:=proc(hfktmonom)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
         remember;
  local f;
  if op(hfktmonom)=0 then return h[0] end if;
  f:=(x,y)->outerH(antipH_mon(x),y):
  eval(subs(`&t`=f,-couterH(hfktmonom)+&t(hfktmonom,h[0])));
end proc:
#
# antipH is the linear version of antiH_mon
#
antipH:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm,n1,plst1,plst2,i;
  if x=0 then return 0 end if;
  if x=h[0] then return h[0] end if;
  if type(x,`+`) then 
    return map(procname,x);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,hfktmonom);
    return cf*procname(tm)
  else
    antipH_mon(x);  
  end if;
end proc:
#
# antipE_mon is the recursively defined antipode for the elementary symmetric 
#            functions (internal use only)
#
antipE_mon:=proc(efktmonom)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
         remember;
  local f;
  if op(efktmonom)=0 then return e[0] end if;
  f:=(x,y)->outerE(antipE_mon(x),y):
  eval(subs(`&t`=f,-couterE(efktmonom)+&t(efktmonom,e[0])));
end proc:
#
# antipE is the linear version of antiE_mon
#
antipE:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm,n1,plst1,plst2,i;
  if x=0 then return 0 end if;
  if x=e[0] then return e[0] end if;
  if type(x,`+`) then 
    return map(procname,x);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,efktmonom);
    return cf*procname(tm)
  else
    antipE_mon(x);  
  end if;
end proc:
#
# antipM_mon is the recursively defined antipode for the monomial symmetric 
#            functions (internal use only)
#
antipM_mon:=proc(mfktmonom)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
         remember;
  local f;
  if op(mfktmonom)=0 then return m[0] end if;
  f:=(x,y)->outerM(antipM_mon(x),y):
  eval(subs(`&t`=f,-couterM(mfktmonom)+&t(mfktmonom,m[0])));
end proc:
#
# antipM is the linear version of antipM_mon
#
antipM:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm,n1,plst1,plst2,i;
  if x=0 then return 0 end if;
  if x=m[0] then return m[0] end if;
  if type(x,`+`) then 
    return map(procname,x);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,mfktmonom);
    return cf*procname(tm)
  else
    antipM_mon(x);  
  end if;
end proc:
#
# linear version for the antipode of the Hopf algebra of outer coproduct and concatenation
#   -- in the monomial basis...
#
#
antipMC:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,term;
  if x=0 then return 0 end if;
  if x=m[0] then return m[0] end if;
  if type(x,`+`) then 
    return map(procname,x);
  elif type(x,`*`) then 
    term,cf:=selectremove(type,x,mfktmonom);
    return cf*procname(term)
  else
    return (-1)^nops(op([x]))*x;  
  end if;
end proc:
########################################################################################
#
# T A B L E S
#
########################################################################################
#
# KostkaTable returns an equation Kostka'N'=matrix where matrix is the matrix of
#             Kostka numbers in the anti lexicographic ordering of partitions
#
KostkaTable:=proc(N::integer)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`; 
  local part,sn,mks;
  mks:=(lst)->map(i->s[op(i)],lst);
  part:=PartNM(N,N);
  sn:=map(i->mks(i),part);
  cat(Kostka,N)=subs(s[0]=1,evalm(linalg[matrix](nops(part),nops(part),(i,j)->Scalar( s[op(part[i])],outer(op(sn[j]))))));
end proc:
#
# LaplaceTable returns the matrix of the Rota-Stein Laplace pairing for the monomial
#              symmetric function deformation. It is presented in the graded anti
#              lexicographic ordering, which respects the grading of the Laplace
#              pairing (block diagonal form). First row and colums show the basis 
#              partitions
#
LaplaceTable:=proc(N,M)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local prtN,prtM;
  prtN,prtM:=sort(PartNM(N,N),grAlexComp),sort(PartNM(M,M),grAlexComp);
  linalg[matrix](nops(prtN)+1,nops(prtM)+1,
       (i,j)->if i=1 and j=1 then 
                `<x|y>` elif j=1 then 
                prtN[i-1] elif i=1 then 
                prtM[j-1] else   
                LaplaceM_mon(prtN[i-1],prtM[j-1]) 
              end if);
end proc:

##########################################################################
#
# I N N E R MONOID and COMONOID
#
#           Power Sum Basis 
#
##########################################################################

##########################################################################
#
# innerH_mon the inner product of symmetric functions in the h-basis
#     -- it is based on the Laplace property of the inner and outer products
#     -- i)  (a.b) o c = \sum_(c)  (a o c_(1)) . (b o c_(2))
#     -- ii) c o (a.b) = \sum_(c)  (c_(1) o a) . (c_(2) o b)
#     -- where we have used:
#     --  . outer product
#     --  \Delta(c)= \sum_(c) c_(1) otimes c_(2) outer coproduct
#     --  o inner product 
#
innerH_mon:=proc(hfktmon1,hfktmon2)
  local n,m,coh,f;
  n,m:=nops([op(hfktmon1)]),nops([op(hfktmon2)]);
  if `+`(op(hfktmon1))<> `+`(op(hfktmon2)) then
     return 0;
  elif n=1 then
     return hfktmon2;
  elif m=1 then
     return hfktmon1;
  elif n<m then
     f:=(a,b,x,y)->outerH(innerH_mon(a,x),innerH_mon(b,y)); 
     coh:=&t(couterH(hfktmon1),h[[op(hfktmon2)][1]],h[op([op(hfktmon2)][2..-1])]);
     return eval(subs(`&t`=f,coh));
  else
     f:=(a,b,x,y)->outerH(innerH_mon(a,x),innerH_mon(b,y)); 
     coh:=&t(couterH(hfktmon2),h[[op(hfktmon1)][1]],h[op([op(hfktmon1)][2..-1])]);
     return eval(subs(`&t`=f,coh));
  end if;
end proc:
#
# innerH is the linear version of innerH_mon
#
#
innerH:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm,p1,p2,y,f;
  if nargs=1 then return x end if;
  y:=args[2];
  if x=0 or y=0 then return 0 end if;
  if nargs>2 then return procname(expand(procname(x,y)),args[3..-1]) end if;
  if not(type(x,hfktpolynom) and type(args[2],hfktpolynom)) then error "wrong type\n" end if;
  if type(x,`+`) then 
    return map(procname,x,y);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,hfktmonom);
    return cf*procname(tm,y)
  else
    if type(y,`+`) then 
      return map2(procname,x,y);
    elif type(y,`*`) then
      tm,cf:=selectremove(type,y,hfktmonom);
      return cf*procname(x,tm)
    else
      innerH_mon(x,y);
    end if;
  end if;
end proc:
#######################################################################################
#
# inner is the inner product on Schur functions. It establishes the tensor product
#    of S_n representations in terms of their characters under the Frobenius 
#    characteristic map.
#
inner_mon := proc(sfkt1,sfkt2)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`; 
  local n1,n2,prt,mat,i,k,lst1,lst2,m;
  lst1:=[op(sfkt1)];
  lst2:=[op(sfkt2)];
  n1:=`+`(op(lst1));
  n2:=`+`(op(lst2));
  if n1<>n2 then return 0 end if;
  if op(sfkt1)=0 and op(sfkt2)=0 then return s[0] end if;
  prt:=PartNM(n1,n1);
  n2:=nops(prt);
  mat:=matrix(n2,n2,(i,j)->MurNak(prt[j],prt[i]));
 # -- find position of lst1, and lst2 in prt
  i:=1:while prt[i]<>lst1 do i:=i+1; end do;
  k:=1:while prt[k]<>lst2 do k:=k+1; end do;
 # -- use the characters to generate the multp. table
  add(add(
    zee(prt[l])^(-1)*mat[i,l]*mat[k,l]*mat[m,l]*s[op(prt[m])]
      ,l=1..nops(prt)),m=1..n2);
########################################################
##
##  this is a direct way to compute the inner product, needs to be tested
##  in speed against the above version, rsults are the same.
##  Note: in MurNak seems to be a transposition, so that here
##        MurNak(par1,par2) = scalarPS(p[par1],s[par2])
##
##  add(add(
##    zee(rho)^(-1)*MurNak(rho,lst1)*MurNak(rho,lst2)*MurNak(rho,lambda)*s[op(lambda)]
##      ,rho in prt),lambda in prt)

end proc:
#
#
inner:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm,p1,p2,y,f;
  if nargs=1 then return x end if;
  y:=args[2];
  if x=0 or y=0 then return 0 end if;
  if nargs>2 then return procname(procname(x,y),args[3..-1]) end if;
  if not(type(x,sfktpolynom) and type(args[2],sfktpolynom)) then error "wrong type\n" end if;
  if type(x,`+`) then 
    return map(procname,x,y);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,sfktmonom);
    return cf*procname(tm,y)
  else
    if type(y,`+`) then 
      return map2(procname,x,y);
    elif type(y,`*`) then
      tm,cf:=selectremove(type,y,sfktmonom);
      return cf*procname(x,tm)
    else
      if x=0 or y=0 then return 0 end if;
      inner_mon(x,y)
    end if;
  end if;
end proc:
#####################################################################################
#
# innerM implements the inner product for monomial symmetric function bases
#
#####################################################################################
innerM:=proc(x)
   local y,lst;
   if nargs=1 then return x end if;
   if nargs>2 then
     y:=args[2];
     lst:=args[3..-1];
     return procname(expand(procname(x,y)),lst); 
   else
     y:=args[2];
     p_to_m(innerP(m_to_p(x),m_to_p(y)));
   end if;
end proc:
#
# cinner_mon is the inner coproduct on monomials, it is the Schur-Hall dual of 
#            the inner product of Schur functions and is computed by using that
#            particular fact.
#
cinner_mon:=proc(sfkt)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`; 
  local n1,n2,prt,lst;
  if sfkt=0 then return 0 end if;
  lst:=[op(sfkt)];
  if sfkt=s[0] then return &t(s[0],s[0]) end if;
  n1:=`+`(op(lst));
  prt:=SchurFkt:-PartNM(n1,n1);
  add(&t(s[op(i)],inner(s[op(i)],s[op(lst)])),i=prt);
end proc:
#
# cinner is the linear version of cinner_mon
#
cinner:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm,n1,plst1,plst2,i;
  if type(x,`+`) then 
    return map(procname,x);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,sfktmonom);
    return cf*procname(tm)
  else
    cinner_mon(x);  
  end if;
end proc:
#
# counitInnerS computes the counit of the inner coporduct in the
#        Schur function basis
#
counitInnerS:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm;
  if type(x,`+`) then 
    return map(procname,x,serName);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,sfktmonom);
    return cf*procname(tm,serName)
  else
    subs(s[0]=1,Scalar(x,s[`+`(op(x))]));
  end if;
end proc:
#
# innerP_mon computer the inner product of power sum functions. 
#
innerP_mon := proc(pfkt1,pfkt2)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`; 
  local n1,n2,bool,lst1,lst2;
  n1:=`+`(op(pfkt1));
  n2:=`+`(op(pfkt2));
  if n1<>n2 then return 0 end if;
  bool:=map(x->if x=0 then true else false end if,zip((x,y)->x-y,[op(pfkt1)],[op(pfkt2)]));
  if convert(bool,set)={true} then
    return zee([op(pfkt1)])*pfkt1;
  else 
    return 0;
  end if; 
end proc:
#
# innerP is the multilinear version of the inner product in power sum basis
#
innerP:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm,p1,p2,y,f;
  if nargs=1 then return x end if;
  y:=args[2];
  if x=0 or y=0 then return 0 end if;
  if nargs>2 then return procname(expand(procname(x,y)),args[3..-1]) end if;
  if not(type(x,pfktpolynom) and type(args[2],pfktpolynom)) then error "wrong type\n" end if;
  if type(x,`+`) then 
    return map(procname,x,y);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,pfktmonom);
    return cf*procname(tm,y)
  else
    if type(y,`+`) then 
      return map2(procname,x,y);
    elif type(y,`*`) then
      tm,cf:=selectremove(type,y,pfktmonom);
      return cf*procname(x,tm)
    else
      innerP_mon(x,y);
    end if;
  end if;
end proc:
#
# cinnerP_mon computes the inner coproduct on monomials in the power sum
#             basis, this coproduct is grouplike on all basis elements
#             x |-->  &t(x,x) 
#
cinnerP_mon:=proc(x)
  &t(x,x);
end proc:
#
# cinnerP linear version of the inner coproduct in the power sum basis
#
#
cinnerP:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2008. All rights reserved.`,
  remember;
  local cf,tm;
  if type(x,`+`) then 
    return map(procname,x);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,pfktmonom);
    return cf*procname(tm)
  else
    cinnerP_mon(x);
  end if;
end proc:
#
# cinnerP linear version of the inner coproduct in the power sum basis
#
#
counitInnerP:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2008. All rights reserved.`,
  remember;
  local cf,tm;
  if type(x,`+`) then 
    return map(procname,x);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,sfktmonom);
    return cf*procname(tm)
  else
    return 1;
  end if;
end proc:
#################################################################
#
#  cdiag implements the diagonalization coproduc in all 5 standard
#        bases the default basis is the 'p-basis' of power sums
#        This implements (if based on power sums) effectively the
#        inner coproduct.
#  NOTE: The cdiag(x,TYPE) functions are _different_ if another
#        basis is chosen. cdiag(x,s) <> cdiag(x,m) etc. 
#
#################################################################
cdiag:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,term,TYPE;
  if nargs=2 then
    TYPE:=args[2];
    if not member(TYPE,{s,p,m,h,f,e}) then
      error "You picked a type '%1' which is not in my list of known types\n 's,p,m,h,f,e' !",TYPE;
    end if;
  else 
    TYPE:='p';
  end if;
  if x=0 then return 0; end if;
  if type(x,cat(TYPE,fktpolynom)) then
    if type(x,`+`) then
      return map(procname,x,TYPE);
    elif type(x,`*`) then
      term,cf:=selectremove(type,x,cat(TYPE,fktmonom));
      return cf*procname(term,TYPE);
    else
      return &t(x,x);
    end if;
  else
    error "No basis monom of type `%1` found, allowed types are in {s,p,h,m,e,f}!\n",TYPE;
  end if;
end proc:
####################################################################################
#
# Plethysms
#
####################################################################################
#
# list_divisors(n::posint) -> a list of all natrural numbers which divide n 
#
list_divisors:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`; 
  local i,t,res;
  if x=1 then return [1] end if;
  res:=[];
  for i from 1 to floor(x/2) do
    t:=irem(x,i);
    if t = 0 then
      res:=[op(res),i];
    end if;
  end do;  
  [op(res),x];
end:
####################################################################################
#
# plethysm coproduct of a single part power sum 
#
####################################################################################
plethPsingleP:=proc(pfkt)
   option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`; 
   local part,ld;
   part:=[op(pfkt)];
   ld:=list_divisors(op(part));
   add(&t(p[i],p[op(part)/i]),i=ld);
end proc:
#
# plethP_mon computes the plethysm between two power sum basis monoms. We have
#       -- p_0[p\mu]=p[0]
#       -- p_\mu[p_0]=p_0
#       -- p_n[p_m]=p_n.m
#       -- p_n[p_mu]=p_\mu[p_n] and hence
#       -- p_\mu[p_\nu] = \prod_(i,j) p_[\mu_i.\nu_j]
#
# NOTE: THIS VERSION SEEMS TO BE SLOWER THAN THE BELOW GIVEN BY A FACTOR 1.5
#
#plethP_mon:=proc(x,y)
#  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
#         remember;
#  local p1,p2;
#  p1,p2:=[op(x)],[op(y)];
#  if p1=[0] or p2=[0] then return p[0] end if;
#  if nops(p1)=1 then
#    if nops(p2)=1 then
#       return p[op(p1)*op(p2)]
#    else
#       return p[op(map(x->op(p1)*x,p2))]
#    end if
#  else
#    outerP(seq(procname(p[l],y),l in p1));
#  end if;
#end proc:
##################################################################################
# plethP_mon is the plethysm product on power sum symmetric monomial functions
#   -- nonrecursive version
#
#
plethP_mon:=proc(pfkt1,pfkt2)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local part1,part2;
  part1:=[op(pfkt1)];
  part2:=[op(pfkt2)];
     p[op(sort(
         [seq(seq(part1[i]*part2[j],i=1..nops(part1)),j=1..nops(part2))],
         (i,j)->if i>j then true else false end if
           ))];
end proc:
#
# plethysm of power sum polynomials ...
#
# plethP(P,Q) = P[Q]
#  -- linear in P   (P1+P2)[Q]=P1[Q]+P2[Q]
#  -- not linear in Q, that is
#  -- P[Q1+Q2]=P_(1)[Q1].P_(2)[Q2]  where \Delta(P)=P_(1) \otimes P_(2) is the outer coproduct
#  -- P[Q1.Q2]=P_[1][Q1].P_[2][Q2]  where \delta(P)=P_[1] \otimes P_[2] is the inner corpoduct
#                                   (this case is trated in plethP_mon
#  -- P[-Q]=(antipP(P))[Q]          hence we need to split Q in to a positive and negative
#                                   part
#
plethP:=proc(x,y)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
         remember;
  local cf,term,term2,cout,sgn,f0,f1,a,b;
  if type(x,pfktmonom) then
    if x=p[0] then return p[0] end if;
    if x=p[1] then return y end if;
    if type(y,pfktmonom) then
      if y=p[0] then return p[0] end if;
      if y=p[1] then return x end if;
      return plethP_mon(x,y)
    elif type(y,`*`) then
#  -- note that cf*term = term+term+...+term is the additive case!!
      term,cf:=selectremove(type,y,pfktmonom);
      if type(cf,integer) then
        if cf<0 then
          return (-1)^nops([op(x)])*procname(x,-cf*term);
        end if;
#  -- put a bracket [cf-1] to prevent linear expansion in the tensor &t(...)
        cout:=&t(couterP(x),[cf-1],term); 
        f0:=(u,v,c,t)->outerP(plethP(u,t),plethP(v,op(c)*t));
        return eval(subs(`&t`=f0,cout));
      else
#  -- put a bracket [cf] to prevent linear expansion in the tensor &t(...)
   #  -- works but is slower than a direct computation...
   #     cout:=&t(cinnerP(x),[cf],term);
   #     f1:=(x1,x2,cf,term)->dimGLP(x1,op(cf))*plethP_mon(x2,term);
   #     return eval(subs(`&t`=f1,cout ));
   #     error("2nd argument need to be a polynomial over the integers but received: %1\n",y);
        return cf^nops([op(x)])*plethP_mon(x,term);
      end if;
    else
      cout:=[op(y)];
      a,b:=cout[1],cout[2..-1];
      cout:=&t(couterP(x),[a],b);
      f0:=(u,v,c,t)->outerP(plethP(u,op(c)),plethP(v,`+`(op(t)))):
         return eval(subs(`&t`=f0,cout));   
    end if;
  elif type(x,`*`) then
    term,cf:=selectremove(type,x,pfktmonom);
    return cf*procname(term,y);
  else
    return map(procname,x,y);
  end if;
end proc:
#
# cplethP is the plethystic coproduct on power sum functions
#
#
cplethP:=proc(pfkt)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local cf,term,llst,dlst,res,i,Npi,pi,dPi;
##
  if pfkt=p[0] then return &t(p[0],p[0]); end if;
  if type(pfkt,`+`) then 
    return map(procname,pfkt)
  elif type(pfkt,`*`) then
    term,cf:=selectremove(type,pfkt,pfktmonom);
    return cf*procname(term)
  else
  ######
    pi:=[op(pfkt)];
    Npi:=`+`(op(pi));
    dPi:=list_divisors(Npi);
    res:=0;
    for i in dPi do
       llst:=PartNM(i,i);
       dlst:=PartNM(Npi/i,Npi/i);
       res:=res+
         add(add(
            1/(zee(l)*zee(d))
            *ScalarP(p[op(pi)],plethP(p[op(l)],p[op(d)]))*&t(p[op(d)],p[op(l)])
            ,l=llst),d=dlst);
    end do;
    res;
  ######
  end if; 
end proc:
#################################################################################
#
#    SFunction PLETHYSMS
#
#################################################################################
#
# plethysm of two complete symmetric functions aka s[n],s[m]
#
#   -- we use the notation P[Q]=pleth(P,Q), hence the plethysm is linear in P (first variable)
#   -- the plethysm is not linear in the second variable Q, it distributes with the inner
#   -- coproduct over the the second argument:
#   -- P[Q1.Q2]=P_{[1]}[Q1].P_{[2]}[Q2]
#   -- if P is given in a power sum basis, then \delta P = P_[1]\otimes P_[2] = P \otimes P
#
#  +++ plethsp(sfkt,pfkt) -> sfkt
#   --         this function is based on the transition s_to_p and the power sum plethysm
#   --         of pfktmonomials, followed by a transformation back into sfunctions!
#   --         plethP_mon computes pfktmonom[pfktmonom] plethysms 
#   --         Since x=s[n] is a one row sfkt (complete function), the characters in the
#   --         expansions are all 1 and dissapear from the computation.
#
plethsp:=proc(x,y)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local n;
  n:=op(x);
  p_to_s(add(1/zee(i)*plethP(y,p[op(i)]),i in PartNM(n,n)));
end proc:
#
# +++ plethSnm(sfkt,sfkt) -> sfkt
#  --      this function expands the outer one row Sfunction into power sums (without
#  --      characters as in plethsp above) and uses afterwards the fact that 
#  --      p_n[Q] = Q[p_n] for one part (primitive) power sum functions. The remaining
#  --      plethysms are of the form s_n[p_k] which can be computed via the function
#  --      plethsp defined above.
#  --      This function does not make use of a possible cancellation of terms due
#  --      to the finiteness of dimenions (the alphabet involved)
#  --      This function is by fare not optimal (see Axel Kohnert's algorithm)
#
plethSnm:=proc(x,y)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local n,m;
  n,m:=op(x),op(y);
  if n=0 then 
    return s[0]
  elif m=0 then 
    return s[0]
  elif n=1 then
    return y
  elif m=1 then 
    return x
  end if; 
  add(1/zee(i)*outer(op(map((k)->plethsp(s[m],p[k]),[op(i)]))) ,i in PartNM(n,n));
end proc:
#
# plethSP: sfkt x pfkt --> sfkt
# +++   plethSP realized the pletysm of an Sfucntion monom by a pfktmonom for general
#  --   partitions \lambda,\mu. This time we need to insert the characters of the
#  --   s_to_p transition computed via the Murnaghan Nakayama rule.
#
#  ++   plethSP shows that
#  ++   plethSP(s[n],p[0]) = s[0]
#  ++   plethSP(s[lambda],p[0]) = 0  for \length(lambda)>1
#
plethSP:=proc(x,y)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local i,n;
  n:=`+`(op(x));
  p_to_s(add(1/zee(i)*MurNak(i,[op(x)])*plethP(y,p[op(i)]),i in PartNM(n,n)));
end proc:
#
#
# plethS_mon : sfkt x sfkt --> sfkt
# +++ plethS_mon computes the pletysm of two SFunction monoms. It uses the expansion 
#  -- s_to_p and thereby the Murnaghan Nakayama coefficients. The second step is once 
#  -- more to use p_n[s_\lambda] = s_\lambda[p_n] and compute these plethysms via
#  -- plethSP
#
plethS_mon:=proc(x,y)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
         remember;
  local n,m,i;
  n,m:=`+`(op(x)),`+`(op(y));
  if n=0 then 
    return s[0]
  elif m=0 then
    # -- according to SCHUR (and plethSP see above)
    # -- plethS(s[n],s[0]) = s[0]
    # -- plethS(s[lambda],s[0]) = 0 if length(lambda)>1
    if nops([op(x)]) > 1 then  
      return 0
    else
      return s[0]
    end if;
  elif n=1 then
    return y
  elif m=1 then 
    return x
  end if; 
  expand(
     add(1/zee(i)*MurNak(i,[op(x)])*outer(op(map((k)->plethSP(y,p[k]),[op(i)]))) 
         ,i in PartNM(n,n))  );
end proc:
########################################################################
#
# plethSAxNB computes the plethysm of a Schur function A with the
#    n-fold multiple of a Schur function B  A[n.B] using the inner
#    coproduct. This can be used to produce q-deformed symmetric
#    functions [see Francesco Brenti, A Class of q-Symmetric Functions
#    Arising from Plethysm, J. Comb.Theor. Series A 91, 2000:137-170]
#
########################################################################
plethSAxNB:=proc(sfkta,sfktb,N)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local f;
  if N=1 then return plethS(sfkta,sfktb) end if;
  if N=0 then return 0 end if;
  f:=(x,y,n,sb)->dimGL(x,op(n))*plethS(y,sb):
  eval(subs(`&t`=f,  &t(cinner(sfkta),[N],sfktb)  ));
end proc:
#
#  X[Y] is linear in X and not linear in Y
#  -- (X+Y)[Z] = X[Z] + Y[Z]
#  -- X[Y+Z] = X(1)[Y] . X(2)[Z]   where . = outer, couter(X)=X(1) x X(2)
#  -- X[YZ] = X[1] . X[2]  where . = outer, cinner(X) =X[1] x X[2]
#  --         this case does not appear in the function, since unevaluated
#  --         outer products YZ do not appear.
#
plethS:=proc(x,y)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
         remember;
  local cf,tm,p1,p2,a,b,f;
# ++ special cases
# -- one argument numerical zero
  if x=0 then 
     return 0
  elif y=0 then 
     return 0
  end if;
# ++ typecheck
  if not(type(x,sfktpolynom) and type(y,sfktpolynom)) then 
     error "wrong type\n" 
  end if;
  if x=s[0] then 
  #-- s_(0)[s_(lambda)] = s_(0) for all lambda
    return s[0]
  # -- the case y=s[0] needs a more sophisticated treatment
  # -- which is done in plethS_mon
  # ++ s[1] is left and right unit of plethS
  elif x=s[1] then
    return y
  elif y=s[1] then
    return x
  end if;
## -- end of special cases
## -- plethS is linear in x but _not_ linear in y
## ++ linearity in x 
  if type(x,`+`) then 
    return map(procname,x,y);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,sfktmonom);
    return cf*procname(tm,y)
  else
## -- the y argument distributes using coproducts
## -- outer roducts do not happen, so we need to distinguish
## -- two types of additive terms y = a+b and y = a+a = 2a
## -- different terms have type `+`
##
## -- the following code cures a subtle error in the plethysm routine
## -- found via computing a problem of Ralf Holtkamp
## -- one needs to make sure that the `+`(op(b_)) is only evaluated
## -- after the expansion has taken place!
## -- change this part of teh code only with care and severe checkig
## -- of at least 3 summand entries for x,y
    if type(y,`+`) then 
      b:=[op(y)];
      a:=&t(couter(x),[b[1]],b[2..-1]);
      f:=(x_,y_,a_,b_)->outer( plethS(x_,op(a_)),expand( plethS(y_,`+`(op(b_))) ) );
      return eval(subs(`&t`=f,a));
## -- numerical multiples of the same term
    elif type(y,`*`) then
      tm,cf:=selectremove(type,y,sfktmonom);
##//// here we could use plethSAxNB to allow even symbolic prefactors
      if not type(cf,integer) then
         return expand(plethSAxNB(x,tm,cf));
##//// we do not put this error message any longer  
##       error "Second input must be a polynomial over the integers, but received ",y; 
      end if;
      if cf>0 then
        return expand(plethSAxNB(x,tm,cf));
        #-- obsolete code
        #--a:=&t(couter(x),tm,[cf-1]);
        #--f:=(x_,y_,a_,b_)->outer(plethS_mon(x_,a_),plethS(y_,op(b_)*a_));
        #--return eval(subs(`&t`=f,a));
      else
        return procname(antipS(x),-y);
      end if;
    else
## ++ if neither x nor y has type `+` or `*` then we have tow sfktmonomials 
      plethS_mon(x,y)
    end if;
  end if;
end proc:
###########################################################################
#
# cplethS_mon is the plethysm coproduct of a sfktmonom
#    -- the plethysm coproduct is obtained by dualizing the plethysm operation w.r.t
#    -- the Schur-Hall scalar product:
#    -- cplethS(x) = \sum_(y,z)  < x ,plethS(y,z) > (y &t z)
#    -- where <,> is the scalar product and plethS is the pelthysm of sfunctions
#    -- note that this is a noncocommutative operation and the order of y,z matters.
#
cplethS_mon:=proc(x)
  local n,divx,prta,prtb;
  n:=`+`(op(x));
  divx:=list_divisors(n);
  add(add(add(
     eval(subs(s[0]=1,Scalar(x,plethS(s[op(b)],s[op(a)]))))*&t(s[op(a)],s[op(b)]), 
    b in PartNM(n/i,n/i)), a in PartNM(i,i)), i in divx);
end proc:
#
# cplethS is the linear version of cplethS_mon establishing the plethysm coproduct of 
#    -- SFunctions.  
#
#
cplethS:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm,n1,plst1,plst2,i;
  if x=0 then return 0 end if;
  if type(x,`+`) then 
    return map(procname,x);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,sfktmonom);
    return cf*procname(tm)
  else
    if x=s[0] then return &t(s[0],s[0]) end if;
    cplethS_mon(x);  
  end if;
end proc:
###########################################################################
#
#
#########
######### Orthogonal Hopf algebra
#########
#
# outerON_monom outer product on s-function monoms of the orthogonal group
#
#
outerON_monom:=proc(x,y)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local N,prt;
  N:=min(`+`(op(x)),`+`(op(y)));
  prt:=[s[0],op(map(x->s[op(x)],[seq(op(PartNM(i,i)),i=1..N)]))];
  add(outer(skew(x,s[op(i)]),skew(y,s[op(i)])),i=prt);
end proc:
#
# outerON outer product of s-function polynoms fro orthogonal groups
#
#
#
outerON:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local cf,tm,p1,p2,y,f;
  if nargs=1 then return x end if;
  y:=args[2];
  if x=0 or y=0 then return 0 end if;
  if nargs>2 then return procname(expand(procname(x,y)),args[3..-1]) end if;
  if not(type(x,sfktpolynom) and type(args[2],sfktpolynom)) then error "wrong type\n" end if;
  if type(x,`+`) then 
    return map(procname,x,y);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,sfktmonom);
    return cf*procname(tm,y)
  else
    if type(y,`+`) then 
      return map2(procname,x,y);
    elif type(y,`*`) then
      tm,cf:=selectremove(type,y,sfktmonom);
      return cf*procname(x,tm)
    else
      outerON_monom(x,y);
    end if;
  end if;
end proc:
#
# couterON_monom outer coproduct of s-function monoms for the orthogonal groups 
#
#
couterON_monom:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local prt, del;
  prt:=[[0],seq(op(PartNM(i,i)),i=1..`+`(op(x)))];
  del:=map(x->2*x,[[0],seq(op(PartNM(i,i)),i=1..floor(`+`(op(x)))/2)]);
  add(&t(skew(x,outer(add(s[op(k)],k=del),s[op(i)])),s[op(i)]),i=prt); 
end proc:
#
# couterON outer coproduct of sfunction polynoms for the orthogonal groups 
#
couterON:=proc(x)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
         remember;
  local cf,tm;
  if type(x,`+`) then 
    return map(procname,x);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,sfktmonom);
    return cf*procname(tm)
  else
    couterON_monom(x);  
  end if;
end proc:
########################################################################################
##
## S-function Series facilities
##
########################################################################################
#
#  getSfktSeries returns a sum of S-functions of a known Schur function series
#
#  -- currently known series are M,L,D,B,F
#
getSfktSeries:=proc(name)
   option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
          remember;
   local N,prt,serFlag,t,f,m,i,j;
   if nargs=1 then
      if args[1]='names' then 
        return "Known Series are: A,B,C,D,E,F,L,M";
      else
        error "Usage: either give one argument 'names' or [2|3] arguments, see help page";
      end if;
   end if; 
   if nargs>=2 then N:=args[2] end if;
   if nargs=3 then serFlag:=true; t:=args[3] else serFlag:=false end if;
   ## ///////////////////////////
   ## M-series = \sum {m} t^m
   ##
   if name='M' then
      if serFlag=false then
         return [seq(s[m],m=0..N)];
      else
         add(s[m]*t^m,m=0..N);
      end if;
   ## ///////////////////////////
   ## L-series = \sum (-1)^m {1^m} t^m
   ##
   ## (special care for zero partition)
   ##
   elif name='L' then
      if serFlag=false then
         return [seq((-1)^m*s[m],m=0..N)];
      else
         f:=m->if m=0 then 0 else 1$m end if:
         add((-1)^m*s[f(m)]*t^m,m=0..N);
      end if;
   ## ///////////////////////////
   ## C-series = \sum {} (inverse of the D series)
   ##
   ## (we scale the parameter t also!)
   elif name='C' then
      prt:=[s[0],op(
              map(x->if {1}={op(zip((i,j)->i-j,op(part2Frob([op(x)]))))} then 
                  (-1)^(`+`(op(x))/2)*x else   NULL end if,procname(F,N))  )];
      if serFlag=false then
         return prt;
      else
        ## --- take care of the sign
        f:=proc(x,t)
           local cf,term;
           cf:=1:
           if type(x,`*`) then
             term,cf:=selectremove(type,x,sfktmonom);
             return (cf*t)^(`+`(op(term)))
           else
             return (cf*t)^(`+`(op(x)))
           end if;
         end proc:
         ## ---        
         add(i*f(i,t),i=prt);
      end if;
   ## ///////////////////////////
   ## D-series = \sum {delta}   delta=even parts only
   ##
   ## (we scale the parameter t also!)
   elif name='D' then
      prt:=map(x->2*x,[[0],seq(op(PartNM(i,i)),i=1..floor(N/2))]);
      if serFlag=false then
         return map(x->s[op(x)],prt);
      else
         add(s[op(i)]*t^(`+`(op(i))),i=prt);
      end if;
   ## ///////////////////////////   
   ## B-series = \sum {beta}   conjpart(beta)=even parts only
   ##
   ## (we scale the parameter t also!)
   elif name='B' then
      prt:=map(x->2*x,[[0],seq(op(PartNM(i,i)),i=1..floor(N/2))]);
      prt:=map(x->conjpart(x),prt);
      if serFlag=false then
         return map(x->s[op(x)],prt);
      else
         add(s[op(i)]*t^(`+`(op(i))),i=prt);
      end if;
   ## ///////////////////////////
   ## A-series  
   ##
   elif name='A' then 
      prt:=[s[0],op(
              map(x->if {1}={op(zip((i,j)->j-i,op(part2Frob([op(x)]))))} then 
                  (-1)^(`+`(op(x))/2)*x else   NULL end if,procname(F,N))  )];
      if serFlag=false then
         return prt;
      else
        ## --- take care of the sign
        f:=proc(x,t)
           local cf,term;
           cf:=1:
           if type(x,`*`) then
             term,cf:=selectremove(type,x,sfktmonom);
             return (cf*t)^(`+`(op(term)))
           else
             return (cf*t)^(`+`(op(x)))
           end if;
         end proc:
         ## ---        
         add(i*f(i,t),i=prt);
      end if;
   ## ///////////////////////////
   ## E-series  = \sum_self conj part (-)^(|x|+r) *s[prt]
   ##              r = Frobenius rank of the partition
   ##
   elif name='E' then 
      prt:=[s[0],op(
              map(x->if {0}={op(zip((i,j)->j-i,op(part2Frob([op(x)]))))} then 
                     x else NULL end if,procname(F,N))  )];
      if serFlag=false then
         return map(x->(-1)^((`+`(op(x))+nops(part2Frob([op(x)])[1]))/2)*x ,prt);
      else
         add((-1)^((`+`(op(i))+nops(part2Frob([op(i)])[1]))/2)*i
             *t^(`+`(op(i))),i=prt);
      end if;
   ## ///////////////////////////
   ## F-series = \sum {zeta}  all partitions 
   ##
   elif name='F' then
      prt:=[[0],seq(op(PartNM(i,i)),i=1..N)];
      if serFlag=false then
         return map(x->s[op(x)],prt);
      else
         add(s[op(i)]*t^(`+`(op(i))),i=prt);
      end if;
    else
      error "unrecognized series name: use getSfktSeries(names) to see which names are known!";
   end if;
end proc:
#
# branch_monom internal function for branchings on monoms
#
# +++ !!!! this function should be already multilinear !!!!
# +++ remove branch and rename this one after a test!
branch_monom:=proc(x,serName)
   option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`;
  local ser;
  ser:=getSeries(serName,`+`(op(x)),1);
  skew(x,ser);
end proc:
#
# branch computes the reduction of induction of characters with respect to
#        certain S-function series
#
branch:=proc(x,serName)
  option `Copyright (c) B. Fauser & R. Ablamowicz 2004-2010. All rights reserved.`,
  remember;
  local ser,cf,tm,n1,plst1,plst2,i;
  if type(x,`+`) then 
    return map(procname,x,serName);
  elif type(x,`*`) then 
    tm,cf:=selectremove(type,x,sfktmonom);
    return cf*procname(tm,serName)
  else
    ser:=SchurFkt:-getSfktSeries(serName,`+`(op(x)),1);
    skew(x,ser);  
  end if;
end proc:

end module:
##
# libname:="/usr/local/maple/maple14/Cliffordlib",libname;
# savelibname := cat(kernelopts(mapledir), kernelopts(dirsep), "Cliffordlib");
libname;
savelib('SchurFkt');
# End
###################################################################################
