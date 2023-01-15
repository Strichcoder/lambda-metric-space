import lambda_metric_space

set_option old_structure_cmd true

universe u

namespace algebra.order.group

-- This file contains a formal proof for some results from the paper 
-- '(In)dependence of the axioms of Λ-trees' https://arxiv.org/abs/2112.02704
-- by Raphael Appenzeller

-- it relies on the general theory of Λ-metric spaces and Λ-trees 
-- formalized in lambda_metric_space.lean.

-- Statements that appear in the paper will be tagged with [paper]
-- This file was created in 2022/2023.

-- Content:
-- Lemma 1 from [paper]
-- Lemma 2 from [paper]
-- The main direction of Theorem 1 using the supremum assumption
-- The main direction of Theorem 1 using the maximum assumption from [paper]
-- A corollary for Λ = 2Λ

variables (Λ :Type*)[linear_ordered_add_comm_group Λ]

-- This is Lemma 3.6 in Chiswel [Chi] or Lemma 1 in [paper], 
-- This is axioms_1_2_imply_unique_1 in lambda_metric_space.lean
lemma lemma_3 (Λ  : Type*) [linear_ordered_add_comm_group Λ] (X:Type*)[lambda_metric_space Λ X]
        : axiom_1 Λ X ∧ axiom_2 Λ X → axiom_unique_1 Λ X :=
begin
  apply axioms_1_2_imply_unique_1 Λ X, 
end

-- This is a Lemma 2 in [paper] with [x,y]=f, [x,z]=f1, [z,y]=f2, [z,p]=g, 
-- This is segments_intersect_once in lambda_metric_space.lean
lemma lemma_5 (Λ : Type*)  [linear_ordered_add_comm_group Λ] (X : Type*) [lambda_metric_space Λ X]
      (x y z p: X) (f1 f2 f g : segment_map Λ X ) (h1 : f1.p = x) (h2 : f1.q = z) (h3 : f2.p = z) (h4 : f2.q = y)
      (h5: f.p = x) (h6 : f.q = y) (h7 : g.p = z) (h8 : g.q = p) (h9 : segment Λ X f1 ∪ segment Λ X f2 = segment Λ X f)
      : segment Λ X f1 ∩ segment Λ X g = {z} ∨ segment Λ X f2 ∩ segment Λ X g = {z} :=
begin
  apply segments_intersect_once Λ X x y z p f1 f2 f g h1 h2 h3 h4 h5 h6 h7 h8 h9,
end

-- a basic lemma.
lemma two_nonneg_imp_nonneg (Λ : Type*) [linear_ordered_add_comm_group Λ]
  (a : Λ) : 0 ≤ a + a → 0 ≤ a :=
begin
   contrapose, intro h1,
   have h2 : 0 > a,
   exact not_le.mp h1,
   have h3 : 0 > a + a,
   exact left.add_neg h2 h2, 
   exact not_le.mpr h3,  
end

def is_supremum_of (Λ  : Type*) [linear_ordered_add_comm_group Λ]  (t : Λ ) ( S : set Λ )
    := (∀ (s : Λ) (s ∈ S) , s ≤ t ) ∧ (∀ t' : Λ , (∀ (s : Λ) (s ∈ S) , s ≤ t' ) → t ≤ t')

-- This lemma is just to split up the main theorem
lemma rrleqd {Λ : Type*} [linear_ordered_add_comm_group Λ] {X:Type*} [lambda_metric_space Λ X]
      (r d : Λ) (hsup : is_supremum_of Λ r {t : Λ | 0 ≤ t + t ∧ t + t ≤ d}) :
      r + r ≤ d :=
begin
  let S : set Λ := {t : Λ | 0 ≤ t + t ∧ t + t ≤ d }, 
  cases hsup with hr1 supmin,
  
  have tt'ledyz : ∀ (t t' : Λ) (ht : t ∈ S)(ht' : t' ∈ S ) , t + t' ≤ d,
  intros t t' ht ht', 
  have hy : t+t + (t' + t') ≤ d + d,
  exact add_le_add ht.2 ht'.2, 
  have hyy : 0 ≤ d - (t+t') + (d - (t+t')),
  rw ← sub_nonneg at hy ⊢ , abel at hy ⊢, exact hy,
  have hyyy : 0 ≤ d - (t+t'),
  apply (two_nonneg_imp_nonneg Λ (d - (t+t')) ) ,  exact hyy,  
  rw ← sub_nonneg at hyyy ⊢ , abel at hyyy ⊢, exact hyyy,  -- we proved tt'ledyz

  have rledt : ∀ (t : Λ)(ht : t ∈ S) , r ≤ d - t, 
  intros t ht, specialize supmin (d - t), apply supmin, 
  intro throwaway, intros t' ht', 
  specialize tt'ledyz t , specialize tt'ledyz t', 
  have go : t + t' ≤ d,
  apply tt'ledyz,  exact ht, exact ht', 
  rw ← sub_nonneg at go ⊢ , abel at go ⊢, exact go, -- we proved rledt
  
  have tledr : ∀ (t:Λ)(ht : t ∈ S)  , t ≤ d - r,
  intros t ht, specialize rledt t, specialize rledt ht, 
  rw ← sub_nonneg at rledt ⊢ , abel at rledt ⊢, exact rledt, -- we proved tledr

  have rledr : r  ≤ d - r,
  specialize supmin (d - r), apply supmin, 
  intro throwaway, intros t ht,
  specialize tledr t, specialize tledr ht, exact tledr,  -- we proved rledr
  rw ← sub_nonneg at rledr ⊢ , abel at rledr ⊢, exact rledr, -- we proved rrled  
end

-- This proof requires to increase the Lean Time Limit in VSCode (set it to 0), (ctrl + ,) 
-- https://leanprover-community.github.io/tips_and_tricks.html
-- It still takes over 100s to check this proof.
set_option profiler true -- for debugging
set_option timeout 0
-- This is the main proof of the direction (a) implies (b) of Theorem 1 in [paper].
-- For historical reasons, the assumption based on supremum is being used.
theorem main_theorem {Λ : Type*} [linear_ordered_add_comm_group Λ] {X:Type*} [lambda_metric_space Λ X] 
   : (∀ t_0 : Λ , t_0 ≥ 0 → ∃ sup : Λ , is_supremum_of Λ sup {t : Λ | 0 ≤ t + t ∧ t + t ≤ t_0} ) →  
     axiom_1 Λ X ∧ axiom_2 Λ X → axiom_3 Λ X :=
begin
  intros cond_sup a12 f f' cond_a3,        

  wlog wlog_assumption_f : f.b - f.a ≤ f'.b - f'.a using [f f' , f' f],  
  -- first we prove that phi.b ≤ psi.b or psi.b ≤ phi.b
  { by_cases f.b-f.a ≤ f'.b - f'.a , left, exact h,
  have h' : f'.b - f'.a ≤ f.b - f.a, exact le_of_not_ge h, right, 
  exact h', },

  cases cond_a3 with x hx, cases hx with hxf hxf',
  have au1 : axiom_unique_1 Λ X,
  apply axioms_1_2_imply_unique_1 Λ X, exact a12,
  cases a12 with a1 a2,
  let phi : segment_map Λ X := seg_reparam_0_def f,
  let psi : segment_map Λ X := seg_reparam_0_def f',

  have wlog_assumption : phi.b ≤ psi.b, 
  { calc phi.b = f.b - f.a : by refl
    ...        ≤ f'.b - f'.a : by exact wlog_assumption_f
    ...        = psi.b : by refl,},

  have phibinpsi : phi.b ∈ interval_a_b Λ psi.a psi.b,
  split, 
  have psia0 : psi.a=0, refl,
  have phia0 : phi.a=0, refl,
  rw psia0, rw ← phia0, exact phi.h,
  exact wlog_assumption,
  let z : X := psi.to_fun ⟨ phi.b, phibinpsi⟩,
  have zdef : z = psi.to_fun ⟨ phi.b, phibinpsi⟩, triv,
  let y : X := phi.q,
  have ydef : y = phi.q, triv, 
  have a1' : axiom_1 Λ X, exact a1,
  specialize a1' y z,
  cases a1' with f'' hsegyz,
  let sigma : segment_map Λ X := seg_reparam_0_def f'',

  let S : set Λ := {t : Λ | 0 ≤ t + t ∧ t + t ≤ dist Λ X y z },
  specialize cond_sup (dist Λ X y z),
  cases (cond_sup (lambda_metric_space.dist_nonneg y z)) with r hr,
  
  have rrled : r + r ≤ dist Λ X y z,
  apply rrleqd r (dist Λ X y z) hr, exact X, assumption,
  cases hr with hr1 supmin,

  let l : Λ := (dist Λ X y z - r),
  have ldef : l =  (dist Λ X y z - r), triv,
  have rlel : r ≤ l,--
  have rlel' : r ≤ (dist Λ X y z - r),
  rw ← sub_nonneg at rrled ⊢ , abel at rrled ⊢, exact rrled,  
  exact rlel', 

  have rgeq0 : 0 ≤ r, --
  specialize hr1 0, specialize hr1 0, apply hr1, split, simp only [add_zero], 
  simp only [add_zero], apply lambda_metric_space.dist_nonneg,

  have rinsigma : r ∈ interval_a_b Λ sigma.a sigma.b, --
  split, 
  exact rgeq0, have rrledr : r+r +0 ≤ dist Λ X y z + r, exact add_le_add rrled rgeq0,     
  have rleqba : r ≤ dist Λ X y z,
  rw ← sub_nonneg at rrledr ⊢ , abel at rrledr ⊢, exact rrledr, -- we proved rleqba
  { calc r  ≤ dist Λ X y z : by exact rleqba 
    ...       ≤ dist Λ X y f''.q : by rw ← hsegyz.2
    ...       ≤ dist Λ X f''.p f''.q : by rw ← hsegyz.1
    ...       = f''.b - f''.a : by exact dist_p_q_in_seg Λ X f''  
    ...       ≤ sigma.b : by triv, } ,  
  
  have linsigma : l ∈ interval_a_b Λ sigma.a sigma.b, --
  split, 
  { calc sigma.a = 0  : by refl
    ...    ≤ r : by exact rgeq0
    ...    ≤ l : by exact rlel, },
  have helper: dist Λ X y z - r ≤ dist Λ X y z,
  rw ← sub_nonneg, simp only [sub_sub_cancel],  exact rgeq0, 
  { calc l = dist Λ X y z - r : by refl
    ...    ≤ dist Λ X y z : by exact helper
    ...    ≤ dist Λ X y f''.q : by rw ← hsegyz.2
    ...    ≤ dist Λ X f''.p f''.q : by rw ← hsegyz.1
    ...    = f''.b - f''.a : by exact dist_p_q_in_seg Λ X f''  
    ...    ≤ sigma.b : by triv, } ,  
  
  have mlinphi : phi.b-l ∈ interval_a_b Λ phi.a phi.b,  
  {
  split, 
  have h1 : dist Λ X y z ≤ phi.b + phi.b,
  { calc dist Λ X y z ≤ dist Λ X y phi.p + dist Λ X phi.p z : by apply lambda_metric_space.dist_triangle
    ...               = dist Λ X phi.p y + dist Λ X phi.p z : by rw ←  dist_sym Λ X y phi.p
    ...               = dist Λ X phi.p phi.q + dist Λ X f.p z : by refl
    ...               = dist Λ X phi.p phi.q + dist Λ X x z : by rw hxf 
    ...               = dist Λ X phi.p phi.q + dist Λ X f'.p z : by rw ← hxf' 
    ...               = phi.b - phi.a + dist Λ X f'.p z : by rw dist_p_q_in_seg Λ X phi
    ...               = phi.b - phi.a + dist Λ X psi.p (psi.to_fun ⟨ phi.b , phibinpsi⟩ ) : by refl
    ...  = phi.b - phi.a + (((⟨ phi.b , phibinpsi⟩:interval_a_b Λ psi.a psi.b):Λ) - psi.a) : by rw ← dist_p_ft_in_seg Λ X psi ⟨ phi.b , phibinpsi⟩
    ...               = phi.b - 0 + (phi.b - 0) : by refl
    ...               = phi.b + phi.b : by simp only [tsub_zero], },
  have h2 : dist Λ X y z + dist Λ X y z ≤ phi.b + phi.b + dist Λ X y z,
  have h2' : dist Λ X y z ≤ dist Λ X y z, refl,
  exact add_le_add h1 h2',
  have h3 : dist Λ X y z - phi.b + (dist Λ X y z - phi.b) ≤ dist Λ X y z,
  rw ← sub_nonneg at h2 ⊢ , abel at h2 ⊢ , exact h2,
  specialize (hr1 0) (dist Λ X y z - phi.b),  
  by_cases 0 ≤ dist Λ X y z - phi.b, -- by cases
  have h4 : dist Λ X y z - phi.b ≤ r,
  apply hr1, split,
  have h4' : 0 + 0 ≤ dist Λ X y z - phi.b + (dist Λ X y z - phi.b), exact add_le_add h h , 
  simp only [add_zero] at h4',  exact h4', exact h3, 
  rw ← sub_nonneg at h4 ⊢, 
  have hphia : phi.a = 0, triv,
  rw hphia, 
  rw ldef, abel at h4 ⊢ , exact h4, 
  -- now comes the other by cases
  have h' :   dist Λ X y z - phi.b ≤ 0,
  exact le_of_not_ge h, 
  have h1 :  dist Λ X y z ≤ phi.b ,
  rw ← sub_nonneg at h' ⊢, abel at h' ⊢, exact h',
  have defn : r = dist Λ X y z - l, rw ← sub_eq_zero , rw ldef,  abel, 
  have gol : phi.a ≤ dist Λ X y z - l,    
  { calc phi.a = 0 : by triv
    ...        ≤ r : by exact rgeq0
    ...        = dist Λ X y z - l : by exact defn, } ,  
  rw ← sub_nonneg at gol h1 ⊢, 
  have goll : 0 + 0 ≤ phi.b - dist Λ X y z + ( dist Λ X y z - l - phi.a),
  exact add_le_add h1 gol ,  
  rw ← sub_nonneg at goll ⊢, abel at goll ⊢, exact goll,    
  have lgeq0 : 0 ≤ l,
  { calc 0 ≤ r : by exact rgeq0
    ...    ≤ l : by exact rlel, } ,  
  rw ← sub_nonneg at lgeq0 ⊢, abel at lgeq0 ⊢, exact lgeq0,  -- finally proved mlinphi 
  },
  
  have mlinpsi : phi.b-l ∈ interval_a_b Λ psi.a psi.b, --
  begin --{
  cases mlinphi with hP hQ,
  split, 
  exact hP, 
  { calc phi.b - l ≤ phi.b : by exact hQ
    ...            ≤ psi.b : by exact wlog_assumption, }, 
  end, --},
 
  let p : X := sigma.to_fun ⟨ r , rinsigma⟩, 
  let q : X := sigma.to_fun ⟨ l , linsigma⟩,
  let y' : X := phi.to_fun ⟨ phi.b-l , mlinphi⟩,
  have yydef : y' = phi.to_fun ⟨ phi.b-l , mlinphi⟩, triv,
  let z' : X := psi.to_fun ⟨ phi.b-l , mlinpsi⟩,
  have zzdef : z' = psi.to_fun ⟨ phi.b-l , mlinpsi⟩, triv,
  -- goal y' = z',
  have a1' : axiom_1 Λ X, exact a1,
  specialize a1' y' p,
  cases a1' with fy hfy,
  have a1' : axiom_1 Λ X, exact a1,
  specialize a1' z' p,
  cases a1' with fz hfz,
  
  have phialephibl : phi.a ≤ phi.b - l,
  exact mlinphi.left,
  have phibllephib : phi.b - l ≤ phi.b,
  exact mlinphi.right,
  have psialephibl : psi.a ≤ phi.b - l,
  exact mlinpsi.left,
  have phibllepsib : phi.b - l ≤ psi.b,
  exact mlinpsi.right, 
  
  -- next define phi1 phi2 psi1 psi2 using subsegments..
  let phi1 : segment_map Λ X := seg_reparam_sub_def phi ⟨ phi.a , a_in_interval phi⟩ 
                                                        ⟨ phi.b-l , mlinphi⟩ phialephibl,
  let phi2 : segment_map Λ X := seg_reparam_sub_def phi  ⟨ phi.b-l , mlinphi⟩ 
                                                         ⟨ phi.b , b_in_interval phi⟩ phibllephib,
  let psi1 : segment_map Λ X := seg_reparam_sub_def psi ⟨ psi.a , a_in_interval psi⟩ 
                                                        ⟨ phi.b-l , mlinpsi⟩ psialephibl,
  let psi2 : segment_map Λ X := seg_reparam_sub_def psi  ⟨ phi.b-l , mlinpsi⟩ 
                                                         ⟨ psi.b , b_in_interval psi⟩ phibllepsib, 

  have h_1 : phi1.p = phi.p, 
  { calc phi1.p = phi.to_fun ⟨ phi.a , a_in_interval phi⟩ : by refl
    ...         = phi.p : by rw phi.to_p, },  
  have h_2 : phi1.q = y', 
  { calc phi1.q = phi.to_fun ⟨ phi.b-l , mlinphi⟩ : by refl
    ...         = y' : by rw ← yydef, }, 
  have case1 : segment Λ X phi1 ∩ segment Λ X fy = {y'} ∨ segment Λ X phi2 ∩ segment Λ X fy = {y'},
  {
  have h_3 : phi2.p = y', 
  { calc phi2.p = phi.to_fun ⟨ phi.b-l , mlinphi⟩ : by refl
    ...         = y' : by rw ← yydef, },
  have h_4 : phi2.q = phi.q, 
  { calc phi2.q = phi.to_fun ⟨ phi.b , b_in_interval phi⟩ : by refl
    ...         = phi.q : by rw ← phi.to_q,}, 
  have h_5 : phi.p = phi.p, refl,
  have h_6 : phi.q = phi.q, refl,
  have h_7 : fy.p = y', exact hfy.left,
  have h_8 : fy.q = p, exact hfy.right,
  have h_9 : segment Λ X phi1 ∪ segment Λ X phi2 = segment Λ X phi, exact partition_seg phi ⟨ phi.b-l , mlinphi⟩,
  exact segments_intersect_once Λ X phi.p phi.q y' p phi1 phi2 phi fy h_1 h_2 h_3 h_4 h_5 h_6 h_7 h_8 h_9,
  -- we proved case1,
  },
  
  have f_1 : psi1.p = psi.p, 
  { calc psi1.p = psi.to_fun ⟨ psi.a , a_in_interval psi⟩ : by refl
    ...         = psi.p : by rw psi.to_p, },  
  have f_2 : psi1.q = z', 
  { calc psi1.q = psi.to_fun ⟨ phi.b-l , mlinpsi⟩ : by refl
    ...         = z' : by rw ← zzdef, },
  have case2 : segment Λ X psi1 ∩ segment Λ X fz = {z'} ∨ segment Λ X psi2 ∩ segment Λ X fz = {z'},
  {
  have f_3 : psi2.p = z',
  { calc psi2.p = psi.to_fun ⟨ phi.b-l , mlinpsi⟩ : by refl
    ...         = z' : by rw ← zzdef, },
  have f_4 : psi2.q = psi.q, 
  { calc psi2.q = psi.to_fun ⟨ psi.b , b_in_interval psi⟩ : by refl
    ...         = psi.q : by rw ← psi.to_q,}, 
  have f_5 : psi.p = psi.p, refl,
  have f_6 : psi.q = psi.q, refl,
  have f_7 : fz.p = z', exact hfz.left,
  have f_8 : fz.q = p, exact hfz.right,
  have f_9 : segment Λ X psi1 ∪ segment Λ X psi2 = segment Λ X psi, exact partition_seg psi ⟨ phi.b-l , mlinpsi⟩,
  exact segments_intersect_once Λ X psi.p psi.q z' p psi1 psi2 psi fz f_1 f_2 f_3 f_4 f_5 f_6 f_7 f_8 f_9,
  -- we proved case2,
  },

  have goa : y' = z',
  cases case1 with c1a c1b,
  
  --  The following is useful for both Case 1a and Case 2a in paper
  have exphip : ∃ (h : segment_map Λ X), segment Λ X h = segment Λ X phi1 ∪ segment Λ X fy 
                                       ∧ h.p = phi1.p ∧ h.q = fy.q,
  {have a2' : axiom_2 Λ X, exact a2,
  specialize a2' phi1, specialize a2' fy,
  apply a2', use y', split, exact c1a, split, exact h_2.symm, rw hfy.left, -- we proved exphip
  }, 
  cases exphip with phip hphip, cases hphip with hphipseg hphip,
  have yyinphip : y'∈ segment Λ X phip,
  rw hphipseg, left, rw ← h_2, exact q_in_seg phi1,
  
  cases case2 with c2a c2b,
  { -- or.inl
  -- Case 1a in paper
  have expsip : ∃ (h : segment_map Λ X), segment Λ X h = segment Λ X psi1 ∪ segment Λ X fz 
                                       ∧ h.p = psi1.p ∧ h.q = fz.q,
  {
  have a2' : axiom_2 Λ X, exact a2,
  specialize a2' psi1, specialize a2' fz,
  apply a2', use z', split, exact c2a, split,  exact f_2.symm, rw hfz.left, --we proved expsip 
  },
  cases expsip with psip hpsip, cases hpsip with hpsipseg hpsip,
  have zzinpsip : z'∈ segment Λ X psip,
  rw hpsipseg, left, rw ← f_2, exact q_in_seg psi1,
  have au1': axiom_unique_1 Λ X, exact au1,
  specialize au1' phip, specialize au1' psip,
  have segs : segment Λ X psip = segment Λ X phip, 
  apply au1', split,
  rw hphip.left, rw hpsip.left,
  { calc phi1.p = phi.to_fun ⟨ phi.a , a_in_interval phi ⟩  : by refl
    ...         = phi.p : by exact phi.to_p
    ...         = f.p : by refl
    ...         = x : by exact hxf.symm
    ...         = f'.p : by exact hxf'
    ...         = psi.p : by refl
    ...         = psi.to_fun ⟨ psi.a , a_in_interval psi ⟩ : by exact psi.to_p.symm
    ...         = psi1.p : by refl,},  
  { calc phip.q = fy.q : by exact hphip.right
    ...         = p : by exact hfy.right
    ...         = fz.q : by exact hfz.right.symm
    ...         = psip.q : by exact hpsip.right.symm,}, 
  rw segs at zzinpsip, 
  have deqd : dist Λ X phip.p y' = dist Λ X phip.p z',
  { calc dist Λ X phip.p y' = dist Λ X phi1.p y' : by rw hphip.left
    ...                     = dist Λ X phi.p y' : by rw h_1
    ...                     = dist Λ X phi.p (phi.to_fun ⟨ phi.b - l , mlinphi⟩) : by refl
    ...                     = (phi.b - l) - phi.a : by exact dist_p_ft_in_seg Λ X phi ⟨ phi.b - l , mlinphi⟩
    ...                     = (phi.b - l) - 0 : by refl
    ...                     = (phi.b - l) - psi.a : by refl
    ...                     = dist Λ X psi.p (psi.to_fun ⟨ phi.b - l , mlinpsi⟩) : by 
                                            exact (dist_p_ft_in_seg Λ X psi ⟨ phi.b - l , mlinpsi⟩).symm
    ...                     = dist Λ X psi.p z' : by refl
    ...                     = dist Λ X f'.p z' : by refl
    ...                     = dist Λ X x z' : by rw ← hxf'
    ...                     = dist Λ X f.p z' : by rw hxf
    ...                     = dist Λ X phi.p z' : by refl
    ...                     = dist Λ X phi1.p z' : by rw ← h_1         
    ...                     =  dist Λ X phip.p z' :by rw ← hphip.left, },
  exact seg_d_p_z_determines_z phip y' z' yyinphip zzinpsip deqd, -- case 1a done
  },
   
  {-- case 2a in paper
  have subgoal: z'=p, 
  {
  have phibinpsi2 : phi.b ∈ interval_a_b Λ psi2.a psi2.b,
  split, 
  { calc phi2.a = phi.b - l : by triv
    ...         ≤ phi.b : by exact mlinphi.right,}, 
  { calc phi.b ≤ psi.b : by exact wlog_assumption
    ...        = psi2.b : by triv,},
  let psi22temp : segment_map Λ X := (seg_reparam_sub_def psi2 
                          ⟨ phi.b - l, a_in_interval psi2⟩ ⟨ phi.b, phibinpsi2  ⟩ mlinphi.right ),
  have hpsi22temp :   segment Λ X psi22temp ⊆ segment Λ X psi2,
  exact reparam_sub_seg psi2 ⟨ phi.b - l, a_in_interval psi2⟩ ⟨ phi.b, phibinpsi2⟩ mlinphi.right, 
  let psi22: segment_map Λ X := seg_reparam_inv psi22temp,
  have hpsi22: segment Λ X psi22temp = segment Λ X psi22,
  exact reparam_inv_seg psi22temp,
  have expsip : ∃ (h : segment_map Λ X), segment Λ X h = segment Λ X psi22 ∪ segment Λ X fz 
                                       ∧ h.p = psi22.p ∧ h.q = fz.q,
  have a2' : axiom_2 Λ X, exact a2,
  specialize a2' psi22, specialize a2' fz,
  apply a2', use z', split, -- current goal: segment Λ X psi22 ∩ segment Λ X fz = {z'}
  ext, split, intro hx_1, cases hx_1 with hx_1a hx_1b, 
  have hyp : x_1 ∈ segment Λ X psi2, apply hpsi22temp, 
  rw hpsi22, exact hx_1a, 
  rw ← c2b, split, exact hyp, exact hx_1b,
  intro hx_1, split, rw ← hpsi22, 
  have hx_1 : x_1 = z', exact hx_1, 
  rw hx_1, exact p_in_seg psi22temp,  
  have hx_1 : x_1 = z', exact hx_1, 
  rw hx_1, rw ← hfz.left, exact p_in_seg fz,
  split,
  { calc z' = psi22temp.p : by refl
    ...     = psi22.q : by refl,},
  exact hfz.left.symm, -- we proved expsip
  cases expsip with psip hpsip, cases hpsip with hpsipseg hpsip,
  have deqd : dist Λ X psip.p z' = dist Λ X psip.p p,
  { calc dist Λ X psip.p z' = dist Λ X psi22.p z' : by rw hpsip.left
    ...                      = dist Λ X psi22temp.q z' : by refl
    ...                      = dist Λ X psi22temp.q psi22temp.p : by refl
    ...                      = dist Λ X psi22temp.p psi22temp.q : by rw dist_sym Λ X psi22temp.p psi22temp.q
    ...                      = psi22temp.b - psi22temp.a : by exact dist_p_q_in_seg Λ X psi22temp
    ...                      = phi.b - (phi.b - l) : by refl
    ...                      = l : by simp only [sub_sub_cancel]
    ...                      = dist Λ X y z - r : by refl
    ...                      = dist Λ X f''.p z - r : by rw ← hsegyz.left
    ...                      = dist Λ X f''.p f''.q - r : by rw ← hsegyz.right
    ...                      = dist Λ X sigma.p sigma.q - r : by refl
    ...                      = (sigma.b - sigma.a) - r : by rw dist_p_q_in_seg Λ X sigma
    ...                      = (sigma.b - 0) - r : by refl
    ...                      = sigma.b - r : by simp only [tsub_zero]
    ...                      = dist Λ X (sigma.to_fun ⟨ r , rinsigma⟩ ) sigma.q : 
                                              by exact (dist_ft_q_in_seg Λ X sigma ⟨ r , rinsigma ⟩).symm
    ...                      = dist Λ X p sigma.q : by refl
    ...                      = dist Λ X p f''.q : by refl
    ...                      = dist Λ X p z : by rw hsegyz.right
    ...                      = dist Λ X p (psi.to_fun ⟨ phi.b , phibinpsi⟩ ) : by refl
    ...                      = dist Λ X p psi22temp.q : by refl
    ...                      = dist Λ X p psi22.p : by refl
    ...                      = dist Λ X psi22.p p : by rw dist_sym Λ X psi22.p p
    ...                     = dist Λ X psip.p p : by rw ← hpsip.left,},  
  have zzinpsip : z' ∈ segment Λ X psip,
  rw hpsipseg, right, rw ← hfz.left, exact p_in_seg fz, 
  have pinpsip : p ∈ segment Λ X psip,
  rw hpsipseg, right, rw ← hfz.right, exact q_in_seg fz,  
  exact seg_d_p_z_determines_z psip z' p zzinpsip pinpsip deqd,  -- we proved subgoal
  },


  
  have deqd : dist Λ X phip.p y' = dist Λ X phip.p z',
  { calc dist Λ X phip.p y' = dist Λ X phi1.p y' : by rw hphip.left
    ...                     = dist Λ X phi.p y' : by rw h_1
    ...                     = dist Λ X phi.p (phi.to_fun ⟨ phi.b - l , mlinphi⟩) : by refl
    ...                     = (phi.b - l) - phi.a : by exact dist_p_ft_in_seg Λ X phi ⟨ phi.b - l , mlinphi⟩
    ...                     = (phi.b - l) - 0 : by refl
    ...                     = (phi.b - l) - psi.a : by refl
    ...                     = dist Λ X psi.p (psi.to_fun ⟨ phi.b - l , mlinpsi⟩) : by 
                                            exact (dist_p_ft_in_seg Λ X psi ⟨ phi.b - l , mlinpsi⟩).symm
    ...                     = dist Λ X psi.p z' : by refl
    ...                     = dist Λ X f'.p z' : by refl
    ...                     = dist Λ X x z' : by rw ← hxf'
    ...                     = dist Λ X f.p z' : by rw hxf
    ...                     = dist Λ X phi.p z' : by refl
    ...                     = dist Λ X phi1.p z' : by rw ← h_1         
    ...                     =  dist Λ X phip.p z' :by rw ← hphip.left, },
  have zzinphip : z' ∈ segment Λ X phip,
  rw hphipseg, right, rw subgoal, rw ← hfy.right, exact q_in_seg fy,
  exact seg_d_p_z_determines_z phip y' z' yyinphip zzinphip deqd, -- case 2a done
  },
  -- 3 goals remaining?

  -- The following is useful for both of the last two cases:
  let phi22: segment_map Λ X := seg_reparam_inv phi2,
  have hphi22: segment Λ X phi2 = segment Λ X phi22,
  exact reparam_inv_seg phi2,
  have exphip : ∃ (h : segment_map Λ X), segment Λ X h = segment Λ X phi22 ∪ segment Λ X fy 
                                       ∧ h.p = phi22.p ∧ h.q = fy.q,
  {
  have a2' : axiom_2 Λ X, exact a2,
  specialize a2' phi22, specialize a2' fy,
  apply a2', use y', split, rw ← hphi22, exact c1b,
  split,
  { calc y' = phi2.p : by refl
    ...     = phi22.q : by refl,},
  exact hfy.left.symm, -- we proved exphip
  }, 
  cases exphip with phip hphip, cases hphip with hphipseg hphip,

  have subgoal: y'=p, -- subgoal
  have step1 : dist Λ X y y' = l,
  have phiblinphi2 : phi.b - l ∈ interval_a_b Λ phi2.a phi2.b,
  split, refl, exact phibllephib, 
  { calc dist Λ X y y' = dist Λ X y' y : by rw dist_sym Λ X y y'
    ...                = dist Λ X (phi2.to_fun ⟨ phi.b - l , phiblinphi2⟩)  y : by refl
    ...                = dist Λ X (phi2.to_fun ⟨ phi.b - l , phiblinphi2⟩) phi.q : by refl
    ...                = dist Λ X (phi.to_fun ⟨ phi.b-l , mlinphi⟩ ) phi.q : by refl
    ...                = phi.b - (phi.b - l) : by exact dist_ft_q_in_seg Λ X phi ⟨phi.b - l , mlinphi⟩
    ...                = l : by simp only [sub_sub_cancel],},
  have step2 : dist Λ X y y' + 0 ≤ dist Λ X y y' + dist Λ X y' p,
  apply add_le_add, refl, exact lambda_metric_space.dist_nonneg y' p,
  have step3 :  dist Λ X phip.p y' + dist Λ X y' phip.q = dist Λ X phip.p phip.q ,
  have yyinphip : y' ∈ segment Λ X phip,
  rw hphipseg, right, rw ← hfy.left, exact p_in_seg fy, 
  exact dist_in_seg_p_q Λ X phip ⟨ y' , yyinphip ⟩, 
  have yisphipp : y = phip.p,
  { calc y = phi.q : by refl
    ...    = (phi.to_fun ⟨ phi.b, b_in_interval phi ⟩) : by rw phi.to_q
    ...    = (phi2.to_fun ⟨ phi.b, _ ⟩) : by refl
    ...    = (phi2.to_fun ⟨ phi2.b, b_in_interval phi2 ⟩) : by refl
    ...    = phi2.q : by rw ← phi2.to_q
    ...    = phi22.p : by refl
    ...    = phip.p : by rw ← hphip.left, },
  have step4 : l ≤ r,
  { calc l = dist Λ X y y' : by rw ← step1
    ...    = dist Λ X y y' + 0 : by simp only [add_zero]
    ...    ≤ dist Λ X y y' + dist Λ X y' p : by exact step2
    ...    = dist Λ X phip.p y' + dist Λ X y' p : by rw yisphipp
    ...    = dist Λ X phip.p y' + dist Λ X y' fy.q : by rw ← hfy.right
    ...    = dist Λ X phip.p y' + dist Λ X y' phip.q : by rw ← hphip.right
    ...    = dist Λ X phip.p phip.q : by exact step3
    ...    = dist Λ X y phip.q : by rw ← yisphipp
    ...    = dist Λ X y fy.q : by rw hphip.right 
    ...    = dist Λ X y p : by rw hfy.right
    ...    = dist Λ X f''.p p : by rw ← hsegyz.left
    ...    = dist Λ X sigma.p p : by refl
    ...    = dist Λ X sigma.p (sigma.to_fun ⟨ r, rinsigma⟩ ) : by refl
    ...    = r - sigma.a : by exact dist_p_ft_in_seg Λ X sigma ⟨ r, rinsigma⟩ 
    ...    = r - 0 : by refl
    ...    = r : by simp only [tsub_zero],},  
  have reql : r = l,
  exact ge_antisymm step4 rlel,
  have deqd : dist Λ X phip.p y' = dist Λ X phip.p p,
  { calc dist Λ X phip.p y' = dist Λ X y y' : by rw ← yisphipp
    ...                     = l : by exact step1
    ...                     = r : by exact reql.symm
    ...                     = r - 0 : by simp only [tsub_zero]
    ...                     = r - sigma.a : by refl
    ...                     = dist Λ X sigma.p (sigma.to_fun ⟨ r , rinsigma⟩) 
                                              : by exact (dist_p_ft_in_seg Λ X sigma ⟨ r , rinsigma⟩).symm
    ...                     = dist Λ X sigma.p p : by refl
    ...                     = dist Λ X f''.p p : by refl
    ...                     = dist Λ X y p : by rw hsegyz.left
    ...                     = dist Λ X phip.p p : by rw yisphipp, },
  have yyinphip : y' ∈ segment Λ X phip,
  rw hphipseg, right, rw ← hfy.left, exact p_in_seg fy, 
  have pinphip : p ∈ segment Λ X phip,
  rw hphipseg, right, rw ← hfy.right, exact q_in_seg fy,  
  exact seg_d_p_z_determines_z phip y' p yyinphip pinphip deqd,  -- we proved subgoal y' = p

  cases case2 with c2a c2b,
  
  
  -- This is case 1b in the paper
  have expsip : ∃ (h : segment_map Λ X), segment Λ X h = segment Λ X psi1 ∪ segment Λ X fz 
                                       ∧ h.p = psi1.p ∧ h.q = fz.q,
  have a2' : axiom_2 Λ X, exact a2,
  specialize a2' psi1, specialize a2' fz,
  apply a2', use z', split, exact c2a, split,  exact f_2.symm, rw hfz.left, --we proved expsip 
  cases expsip with psip hpsip, cases hpsip with hpsipseg hpsip,
  have zzinpsip : z'∈ segment Λ X psip,
  rw hpsipseg, left, rw ← f_2, exact q_in_seg psi1,
  have au1': axiom_unique_1 Λ X, exact au1,
  specialize au1' phi1, specialize au1' psip,
  have segs : segment Λ X psip = segment Λ X phi1, 
  apply au1', split, 
  rw hpsip.left,
  { calc phi1.p = phi.to_fun ⟨ phi.a , a_in_interval phi ⟩  : by refl
    ...         = phi.p : by exact phi.to_p
    ...         = f.p : by refl
    ...         = x : by exact hxf.symm
    ...         = f'.p : by exact hxf'
    ...         = psi.p : by refl
    ...         = psi.to_fun ⟨ psi.a , a_in_interval psi ⟩ : by exact psi.to_p.symm
    ...         = psi1.p : by refl,},  
  { calc phi1.q = y' : by exact h_2
    ...         = p : by exact subgoal
    ...         = fz.q : by exact hfz.right.symm
    ...         = psip.q : by exact hpsip.right.symm,}, -- we proved segs
  rw segs at zzinpsip, 
  have deqd : dist Λ X phi1.p y' = dist Λ X phi1.p z',
  { calc dist Λ X phi1.p y' = dist Λ X phi.p y' : by rw h_1
    ...                     = dist Λ X phi.p (phi.to_fun ⟨ phi.b - l , mlinphi⟩) : by refl
    ...                     = (phi.b - l) - phi.a : by exact dist_p_ft_in_seg Λ X phi ⟨ phi.b - l , mlinphi⟩
    ...                     = (phi.b - l) - 0 : by refl
    ...                     = (phi.b - l) - psi.a : by refl
    ...                     = dist Λ X psi.p (psi.to_fun ⟨ phi.b - l , mlinpsi⟩) : by 
                                            exact (dist_p_ft_in_seg Λ X psi ⟨ phi.b - l , mlinpsi⟩).symm
    ...                     = dist Λ X psi.p z' : by refl
    ...                     = dist Λ X f'.p z' : by refl
    ...                     = dist Λ X x z' : by rw ← hxf'
    ...                     = dist Λ X f.p z' : by rw hxf
    ...                     = dist Λ X phi.p z' : by refl
    ...                     = dist Λ X phi1.p z' : by rw ← h_1, },
  have yyinphi1 : y' ∈ segment Λ X phi1, rw ← h_2, exact q_in_seg phi1,
  exact seg_d_p_z_determines_z phi1 y' z' yyinphi1 zzinpsip deqd, -- case 2a done


  -- This is case 2b in the paper (it is the last case)
  have subgoal2: z'=p,  
  have phibinpsi2 : phi.b ∈ interval_a_b Λ psi2.a psi2.b,
  split, 
  { calc phi2.a = phi.b - l : by triv
    ...         ≤ phi.b : by exact mlinphi.right,}, 
  { calc phi.b ≤ psi.b : by exact wlog_assumption
    ...        = psi2.b : by triv,},
  let psi22temp : segment_map Λ X := (seg_reparam_sub_def psi2 
                          ⟨ phi.b - l, a_in_interval psi2⟩ ⟨ phi.b, phibinpsi2  ⟩ mlinphi.right ),
  have hpsi22temp :   segment Λ X psi22temp ⊆ segment Λ X psi2,
  exact reparam_sub_seg psi2 ⟨ phi.b - l, a_in_interval psi2⟩ ⟨ phi.b, phibinpsi2⟩ mlinphi.right, 
  let psi22: segment_map Λ X := seg_reparam_inv psi22temp,
  have hpsi22: segment Λ X psi22temp = segment Λ X psi22,
  exact reparam_inv_seg psi22temp,
  have expsip : ∃ (h : segment_map Λ X), segment Λ X h = segment Λ X psi22 ∪ segment Λ X fz 
                                       ∧ h.p = psi22.p ∧ h.q = fz.q,
  have a2' : axiom_2 Λ X, exact a2,
  specialize a2' psi22, specialize a2' fz,
  apply a2', use z', split, -- current goal: segment Λ X psi22 ∩ segment Λ X fz = {z'}
  ext, split, intro hx_1, cases hx_1 with hx_1a hx_1b, 
  have hyp : x_1 ∈ segment Λ X psi2, apply hpsi22temp, 
  rw hpsi22, exact hx_1a, 
  rw ← c2b, split, exact hyp, exact hx_1b,
  intro hx_1, split, rw ← hpsi22, 
  have hx_1 : x_1 = z', exact hx_1, 
  rw hx_1, exact p_in_seg psi22temp,  
  have hx_1 : x_1 = z', exact hx_1, 
  rw hx_1, rw ← hfz.left, exact p_in_seg fz,
  split,
  { calc z' = psi22temp.p : by refl
    ...     = psi22.q : by refl,},
  exact hfz.left.symm, -- we proved expsip
  cases expsip with psip hpsip, cases hpsip with hpsipseg hpsip,
  have deqd : dist Λ X psip.p z' = dist Λ X psip.p p,
  { calc dist Λ X psip.p z' = dist Λ X psi22.p z' : by rw hpsip.left
    ...                      = dist Λ X psi22temp.q z' : by refl
    ...                      = dist Λ X psi22temp.q psi22temp.p : by refl
    ...                      = dist Λ X psi22temp.p psi22temp.q : by rw dist_sym Λ X psi22temp.p psi22temp.q
    ...                      = psi22temp.b - psi22temp.a : by exact dist_p_q_in_seg Λ X psi22temp
    ...                      = phi.b - (phi.b - l) : by refl
    ...                      = l : by simp only [sub_sub_cancel]
    ...                      = dist Λ X y z - r : by refl
    ...                      = dist Λ X f''.p z - r : by rw ← hsegyz.left
    ...                      = dist Λ X f''.p f''.q - r : by rw ← hsegyz.right
    ...                      = dist Λ X sigma.p sigma.q - r : by refl
    ...                      = (sigma.b - sigma.a) - r : by rw dist_p_q_in_seg Λ X sigma
    ...                      = (sigma.b - 0) - r : by refl
    ...                      = sigma.b - r : by simp only [tsub_zero]
    ...                      = dist Λ X (sigma.to_fun ⟨ r , rinsigma⟩ ) sigma.q : 
                                              by exact (dist_ft_q_in_seg Λ X sigma ⟨ r , rinsigma ⟩).symm
    ...                      = dist Λ X p sigma.q : by refl
    ...                      = dist Λ X p f''.q : by refl
    ...                      = dist Λ X p z : by rw hsegyz.right
    ...                      = dist Λ X p (psi.to_fun ⟨ phi.b , phibinpsi⟩ ) : by refl
    ...                      = dist Λ X p psi22temp.q : by refl
    ...                      = dist Λ X p psi22.p : by refl
    ...                      = dist Λ X psi22.p p : by rw dist_sym Λ X psi22.p p
    ...                     = dist Λ X psip.p p : by rw ← hpsip.left,},  
  have zzinpsip : z' ∈ segment Λ X psip,
  rw hpsipseg, right, rw ← hfz.left, exact p_in_seg fz, 
  have pinpsip : p ∈ segment Λ X psip,
  rw hpsipseg, right, rw ← hfz.right, exact q_in_seg fz,  
  exact seg_d_p_z_determines_z psip z' p zzinpsip pinpsip deqd,  -- we proved subgoal2
  
  rw subgoal, rw subgoal2, -- we proved the last case and now have y' = z'
  
  use phi1,
  have goal : segment Λ X phi1 = segment Λ X phi ∩ segment Λ X psi,
  ext, split, 
  intro hx_1, split,
  apply reparam_sub_points phi ⟨ phi.a , a_in_interval phi⟩  ⟨ phi.b-l , mlinphi⟩ phialephibl x_1,
  exact hx_1,
  apply reparam_sub_points psi ⟨ psi.a , a_in_interval psi⟩ ⟨ phi.b-l , mlinpsi⟩ psialephibl x_1,
  have uni : segment Λ X phi1 = segment Λ X psi1,
  have au1' : axiom_unique_1 Λ X , exact au1,
  apply au1', split, 
  { calc psi1.p = psi.p : by exact f_1 
    ...         = f'.p : by refl
    ...         = x : by exact hxf'.symm
    ...         = f.p : by exact hxf
    ...         = phi.p : by refl
    ...         = phi1.p : by exact h_1.symm,}, 
  { calc psi1.q = z' : by exact f_2
    ...         = y' : by exact goa.symm
    ...         = phi1.q : by exact h_2.symm,}, -- we proved uni  
  rw ← uni, exact hx_1,  -- we proved seg phi1 ⊆ seg phi ∩ seg psi
  
  intro hx_1, cases hx_1 with hhx1 hhx2,
  have tphi : ∃ t: interval_a_b Λ phi.a phi.b, phi.to_fun t = x_1,
  exact seg_exists_z Λ X phi ⟨ x_1, hhx1⟩, 
  cases tphi with tphi htphi, 
  have tpsi : ∃ t: interval_a_b Λ psi.a psi.b, psi.to_fun t = x_1,
  exact seg_exists_z Λ X psi ⟨ x_1, hhx2⟩, 
  cases tpsi with tpsi htpsi,
  have teqt : (tphi:Λ) = tpsi,
  { calc (tphi:Λ) = (tphi:Λ) - 0 : by simp only [tsub_zero]
    ...           = (tphi:Λ) - phi.a : by refl
    ...           = dist Λ X phi.p (phi.to_fun tphi) : by rw ← dist_p_ft_in_seg Λ X phi tphi
    ...           = dist Λ X phi.p x_1 : by rw htphi
    ...           = dist Λ X f.p x_1 : by refl
    ...           = dist Λ X x x_1 : by rw ← hxf
    ...           = dist Λ X f'.p x_1 : by rw hxf'
    ...           = dist Λ X psi.p x_1 : by refl
    ...           = dist Λ X psi.p (psi.to_fun tpsi) : by rw ← htpsi
    ...           = (tpsi : Λ) - psi.a : by rw dist_p_ft_in_seg Λ X psi tpsi
    ...           = (tpsi : Λ) - 0 : by refl
    ...           = (tpsi:Λ) : by simp only [tsub_zero],},
  let t: Λ := (tphi:Λ),
  have step1 : dist Λ X y z ≤ (phi.b - t) + (phi.b - t),
  have step1' : dist Λ X (psi.to_fun tpsi) (psi.to_fun ⟨ phi.b , phibinpsi ⟩) = phi.b - (tpsi:Λ),
  have step1'': dist Λ X (psi.to_fun tpsi) (psi.to_fun ⟨ phi.b , phibinpsi ⟩) = |phi.b - (tpsi:Λ)|,
  exact psi.isom tpsi ⟨ phi.b , phibinpsi ⟩, rw step1'', 
  have step1''' : (tpsi:Λ) ≤ phi.b,
  rw ← teqt, exact tphi.prop.right, 
  have step1'''' : 0 ≤ phi.b - (tpsi:Λ), exact sub_nonneg.mpr step1''',
  exact abs_of_nonneg step1'''', -- we proved step1'
  { calc dist Λ X y z ≤ dist Λ X y x_1 + dist Λ X x_1 z : by exact lambda_metric_space.dist_triangle y z x_1
    ...               = dist Λ X y (phi.to_fun tphi) + dist Λ X x_1 z : by rw ← htphi
    ...               = dist Λ X y (phi.to_fun tphi) + dist Λ X (psi.to_fun tpsi) z : by rw ← htpsi
    ...               = dist Λ X (phi.to_fun tphi) y + dist Λ X (psi.to_fun tpsi) z : 
                                by rw dist_sym Λ X (phi.to_fun tphi) y
    ...               = dist Λ X (phi.to_fun tphi) phi.q + dist Λ X (psi.to_fun tpsi) z : by rw ← ydef
    ...               = (phi.b - (tphi:Λ)) + dist Λ X (psi.to_fun tpsi) z : by rw dist_ft_q_in_seg Λ X phi tphi
    ...               = (phi.b - t) + dist Λ X (psi.to_fun tpsi) (psi.to_fun ⟨ phi.b , phibinpsi ⟩) : by refl
    ...               = (phi.b - t) + (phi.b - (tpsi:Λ)) : by rw step1'
    ...               = (phi.b - t) + (phi.b - t) : by rw ← teqt,},
  have step2 : (dist Λ X y z - (phi.b - t)) + (dist Λ X y z - (phi.b - t)) ≤ dist Λ X y z,
  { calc (dist Λ X y z - (phi.b - t)) + (dist Λ X y z - (phi.b - t))
          = dist Λ X y z + (-(phi.b - t) + (dist Λ X y z - (phi.b - t)))  : by abel
    ...   ≤ ((phi.b - t) + (phi.b - t)) + (-(phi.b - t) + (dist Λ X y z - (phi.b - t)))  
                           : add_le_add_right step1 (-(phi.b - t) + (dist Λ X y z - (phi.b - t)))
    ...   ≤ dist Λ X y z : by abel,},  
  have step3 : dist Λ X y z - (phi.b - t) ≤ r,
  by_cases 0 ≤ dist Λ X y z - (phi.b - t),
  apply hr1 (dist Λ X y z - (phi.b - t)), split, exact add_nonneg h h, exact step2, 
  have h' : dist Λ X y z - (phi.b - t) ≤ 0,
  exact le_of_not_ge h,
  { calc dist Λ X y z - (phi.b -t) ≤ 0 : by exact h'
    ...                            ≤ r : by exact rgeq0,}, -- we proved step3
  have step4 : l ≤ phi.b - t,
  have step4' : dist Λ X y z - r ≤ phi.b - t,
  rw ← sub_nonneg at step3 ⊢, abel at step3 ⊢, exact step3,
  exact step4', 
  have step5 : t ≤ phi.b - l,
  rw ← sub_nonneg at step4 ⊢, abel at step4 ⊢, exact step4,
  have step6 : t ∈ interval_a_b Λ phi1.a phi1.b,
  split, 
  { calc phi1.a = 0 : by refl
    ...         = phi.a : by refl
    ...         ≤ t : by exact tphi.prop.left,}, 
  { calc t ≤ phi.b - l : by exact step5
    ...    = phi1.b : by refl,}, 
  use ⟨ t, step6⟩,  
  { calc phi1.to_fun ⟨t, step6⟩ = phi.to_fun tphi : by refl
    ...                        = x_1 : by exact htphi,},
 
  rw reparam_0_seg f, rw reparam_0_seg f', exact goal, 
  
  -- now some cleanup from the wlog
  have segs : segment Λ X f ∩ segment Λ X f' = segment Λ X f' ∩ segment Λ X f,
  exact (segment Λ X f).inter_comm (segment Λ X f'),
  rw segs, apply this, 
  cases cond_a3 with x_1 hx_1, use x_1, split, exact hx_1.right, exact hx_1.left,  
end


def is_max_of (Λ  : Type*) [linear_ordered_add_comm_group Λ]  (t : Λ ) ( S : set Λ )
    := (t ∈  S) ∧ (∀ (s: Λ) (s ∈ S), s ≤ t) 

-- This is the direction (a) implies (b) of Theorem 1 in [paper].
theorem main_theorem_var {Λ : Type*} [linear_ordered_add_comm_group Λ] {X:Type*} [lambda_metric_space Λ X] 
   : (∀ t_0 : Λ , t_0 ≥ 0 → ∃ max : Λ , is_max_of Λ max {t : Λ | 0 ≤ t + t ∧ t + t ≤ t_0} ) →  
     axiom_1 Λ X ∧ axiom_2 Λ X → axiom_3 Λ X :=
begin
  intro hyp,
  have alternate_hyp : (∀ t_0 : Λ , t_0 ≥ 0 → ∃ sup : Λ , is_supremum_of Λ sup {t : Λ | 0 ≤ t + t ∧ t + t ≤ t_0} ), 
  intros t0 ht0,
  specialize hyp t0, 
  have hypmax :  ∃ max : Λ , is_max_of Λ max {t : Λ | 0 ≤ t + t ∧ t + t ≤ t0},
  apply hyp, exact ht0,
  cases hypmax with max,
  use max,
  cases hypmax_h with h1 h2,
  split,
  exact h2,
  intros t' ht',
  have hel : ∀ (s : Λ), s ∈ {t : Λ | 0 ≤ t + t ∧ t + t ≤ t0} → s ≤ t',
  apply ht', exact t',
  specialize hel max, apply hel, exact h1,
  intro ass,
  apply main_theorem, exact alternate_hyp, exact ass,   
end


def Lambda_is_two_Lambda (Λ : Type*)[linear_ordered_add_comm_group Λ] := ∀ b : Λ , ∃ a : Λ , a + a = b

-- This is a corollary from Theorem 1
theorem main_corollary (Λ : Type*) [linear_ordered_add_comm_group Λ] (X:Type*)[lambda_metric_space Λ X] 
        : Lambda_is_two_Lambda Λ → axiom_1 Λ X ∧ axiom_2 Λ X → axiom_3 Λ X :=
begin
  intro hl2l,
  
  have assumption :(∀ t_0 : Λ , t_0 ≥ 0 → ∃ sup : Λ , is_supremum_of Λ sup {t : Λ | 0 ≤ t + t ∧ t + t ≤ t_0} ),
  intro t_0, 
  specialize hl2l t_0, cases hl2l with sup hsup, intro t_0pos,
  use sup, split,  intro L, intro t, intro hypt,   
  cases hypt with hypt1 hypt2,
  have tpos : 0 ≤ t, 
    exact two_nonneg_imp_nonneg Λ t hypt1, 
    rw ← hsup at hypt2, rw ← sub_nonneg at hypt2 ⊢, 
  have hypt2' : 0 ≤ (sup - t) + (sup -t), abel at hypt2 ⊢ , exact hypt2 ,
  exact two_nonneg_imp_nonneg Λ (sup -t) hypt2', -- proved first part of the sup-property

  have h : 0 ≤ t_0 + t_0, 
  exact add_nonneg t_0pos t_0pos,
  intro t', intro hyp_sup, specialize hyp_sup sup, specialize hyp_sup sup, apply hyp_sup,
  have suppos : 0 ≤ sup,
  have supsuppos : 0 ≤ sup + sup,
  rw hsup, exact two_nonneg_imp_nonneg Λ t_0 h, exact two_nonneg_imp_nonneg Λ sup supsuppos,
  split, exact add_nonneg suppos suppos, exact (eq.symm hsup).ge, -- we proved the assumption

  apply main_theorem, exact assumption, 
end


end algebra.order.group