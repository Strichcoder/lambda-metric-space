import tactic
import algebra.order.group.defs
import logic.function.basic
import data.set.basic
import data.subtype
import data.real.basic

set_option old_structure_cmd true

universe u

namespace algebra.order.group

-- This file contains definitions for Λ-metric spaces, where Λ is an ordered abelian group (not necessarily ℝ).

-- Content:
-- Definition and basic properties of Λ-metric space
-- Definition and basic properties of Λ-interval
-- Definition and basic properties of Λ-segments
-- Definition of Λ-trees.
-- We prove that axioms (1) and (2) imply unique (1), Lemma 3.6 in Chiswell [Chi]

-- A good reference is Ian Chiswell's book 'Introduction to Λ-trees' [Chi]

-- This file was created by Raphael Appenzeller in 2022
-- accompanying the paper '(In)dependence of the axioms of Λ-trees' https://arxiv.org/abs/2112.02704
-- Statements that appear in the paper will be tagged with [paper]
-- While this file contains statements of general interest about Λ-metric spaces,
-- further results specific to the paper can be found in the file lambda_tree_theorem.lean.

variables (Λ :Type*)[linear_ordered_add_comm_group Λ]

-- main definition
class lambda_metric_space (Λ : Type*) [linear_ordered_add_comm_group Λ] (X : Type*)  := 
(dist : X → X → Λ)
(dist_nonneg : ∀ p q : X, dist p q ≥ 0)
(dist_self : ∀ p : X, dist p p = 0)
(eq_of_dist_eq_zero : ∀ p q : X, dist p q = 0 → p = q)
(dist_comm : ∀ p q : X, dist p q = dist q p)
(dist_triangle : ∀ p q r : X, dist p q ≤ dist p r + dist r q)

def dist (Λ : Type*) (X : Type*) [linear_ordered_add_comm_group Λ] [lambda_metric_space Λ X] : X → X → Λ :=
lambda_metric_space.dist

lemma dist_sym (Λ : Type*) [linear_ordered_add_comm_group Λ] (X:Type*) [lambda_metric_space Λ X]
      (x y : X) : dist Λ X x y = dist Λ X y x :=
begin
  have h : ∀ p q : X, dist Λ X p q = dist Λ X q p,
  exact lambda_metric_space.dist_comm, 
  specialize h x, specialize h y, exact h,  
end

lemma dist_nonneg (Λ : Type*) [linear_ordered_add_comm_group Λ] (X:Type*) [lambda_metric_space Λ X]
      (x y : X) : 0 ≤ dist Λ X x y :=
begin
  have h : ∀ p q : X, dist Λ X p q ≥ 0,
  exact lambda_metric_space.dist_nonneg,
  specialize h x, specialize h y, exact h,
end

-- We prove that Λ itself is a Λ-metric space
def lambda_as_lambda_metric_space (Λ : Type u) [linear_ordered_add_comm_group Λ] : lambda_metric_space Λ Λ :=
{   
    dist := λ x y ,  |x-y|,
    dist_nonneg := 
    begin
      intros p q,
      change |p - q | ≥ 0,
      have h : ∀ x : Λ, |x| ≥ 0,
      exact abs_nonneg,
      apply h,
    end,
    dist_self := 
    begin
      intro p,
      change |p - p| = 0,
      have h : p-p = 0,
      exact sub_self p,
      rw h,
      exact abs_zero,
    end,
    eq_of_dist_eq_zero := 
    begin
      intros p q,
      intro hyp,
      change |p - q| = 0 at hyp,
      exact eq_of_abs_sub_eq_zero hyp,
    end,
    dist_comm := 
    begin
      intros p q,
      change |p-q| = |q - p|,
      have hyp : |p - q| = | - (p-q)|,
      exact (abs_neg (p - q)).symm,
      rw hyp,
      have hyp2 : - (p-q) = q - p,
      exact neg_sub p q,
      rw hyp2,
    end,
    dist_triangle := 
    begin
      intros p q r,
      change |p-q| ≤ |p-r|+ |r-q|,
      exact abs_sub_le p r q,
    end,
}

-- The following function is needed, as isometry has two lambda_metric_spaces and lean might think that 
-- there are two Λ that cannot be compared.
structure lambda_isometry (Λ : Type*) [ linear_ordered_add_comm_group Λ]
             (X Y : Type*) [ lambda_metric_space Λ X] [ lambda_metric_space Λ Y] := 
(to_fun : X → Y)
(isom : ∀ x1 x2 : X , dist  Λ _ x1 x2 = dist  Λ Y (to_fun x1) (to_fun x2) )

-- We define a Λ-interval from a to b and show basic properties in what follows.
def interval_a_b (Λ : Type*) [linear_ordered_add_comm_group Λ] (a b : Λ)  := {t : Λ | a ≤ t ∧ t ≤ b}
-- TODO: Introduce notation [a , b]_Λ

lemma a_in_interval_a_b (Λ : Type*) [linear_ordered_add_comm_group Λ] (a b : Λ) (h: a≤ b)
    : a ∈ interval_a_b Λ a b :=
begin
  have hyp : a ≤ a ∧ a ≤ b,
  split,
  exact rfl.ge,
  exact h,
  have hh :  a ≤ a ∧ a ≤ b ↔ a ∈ interval_a_b Λ a b ,
  refl,
  rw hh at hyp,
  exact hyp,
end
lemma b_in_interval_a_b (Λ : Type*) [linear_ordered_add_comm_group Λ] (a b : Λ)  (h : a ≤ b) 
    : b ∈ interval_a_b Λ a b :=
begin
  have hyp : a ≤ b ∧ b ≤ b,
  split,
  exact h,
  exact rfl.ge,
  have hh :  a ≤ b ∧ b ≤ b ↔ b ∈ interval_a_b Λ a b ,
  refl,
  rw hh at hyp,
  exact hyp,
end
lemma dist_in_interval_a_b (Λ : Type*) [linear_ordered_add_comm_group Λ] (a b : Λ)  (h : a ≤ b)
      (t : interval_a_b Λ a b) : |(t:Λ)-a| + |b-t| = |b-a| :=
begin
  have htt : a ≤ t ∧ (t:Λ) ≤ b,
  exact t.prop, -- NICE
  cases htt with htt1 htt2,
  have rew: (t:Λ)-a + b - t = b -a,
  rw add_comm,
  have hhhh : b - a + t - t = b - a,
  have hhhhh : b - a + (t - t) = b - a,
  have hhhhhh : b - a = b - a,
  refl,
  have tit : (t:Λ) - t = 0,
  exact sub_self t,
  rw tit,
  rw add_zero,
  exact add_sub_cancel (b - a) t,
  rw ← hhhh,
  rw add_comm,
  rw add_comm (b-a) t,
  have h2 : b - a = -a + b,
  exact sub_eq_neg_add b a,
  rw h2,
  rw ←  add_assoc,
  have h3: (t:Λ) - a = t + (-a),
  exact sub_eq_add_neg t a,
  rw h3,
  have h4: 0 ≤ (t:Λ) - a,
  exact sub_nonneg.mpr htt1,
  have h5: |(t:Λ) - a| = t -a,
  exact abs_of_nonneg h4,
  have h6: 0 ≤ b - t,
  exact sub_nonneg.mpr htt2,
  have h7: |b - t| = b -t,
  exact abs_of_nonneg h6,
  have h8: 0 ≤ b - a,
  exact sub_nonneg.mpr h,
  have h9: |b - a| = b -a,
  exact abs_of_nonneg h8,
  rw h9,
  rw h7,
  rw h5,
  exact sub_add_sub_cancel' t a b,
end
-- We will show provide some lemmas about reparametrizing intervals.
lemma interval_reparam_0 (Λ : Type*) [linear_ordered_add_comm_group Λ] (a b : Λ)  (h : a ≤ b)
      (t : interval_a_b Λ 0 (b - a)) : (t:Λ) + a ∈ interval_a_b Λ a b:=
begin
  cases t.prop with tP tQ,
  split,
  exact le_add_of_nonneg_left tP,
  exact le_sub_iff_add_le.mp tQ,
end
lemma interval_reparam_trans (Λ : Type*) [linear_ordered_add_comm_group Λ] (a b a' b' : Λ)  (h : a ≤ b) (h' : a' ≤ b')
      (hlen : b-a = b'-a') (t : interval_a_b Λ a b) : (t:Λ) + a' - a ∈ interval_a_b Λ a' b':=
begin
  cases t.prop with ht1 ht2,
  split,
  rw ← sub_nonneg at ht1 ⊢, abel at ht1 ⊢, exact ht1,
  rw ← sub_eq_zero at hlen,  rw ← sub_nonneg at ht2 ⊢, rw ← hlen at ht2, 
  rw ← sub_nonneg at ht2, abel at ht2 ⊢, exact ht2,
end
lemma interval_reparam_sub (Λ : Type*) [linear_ordered_add_comm_group Λ] (a b : Λ) (h : a ≤ b)
      (a' b' : interval_a_b Λ a b) (hab : a' ≤ b') (s: interval_a_b Λ a' b') : (s:Λ) ∈ interval_a_b Λ a b:=
begin
  have hsub :  (s:Λ) ∈ interval_a_b Λ a' b' → (s:Λ) ∈ interval_a_b Λ a b,
    intro hs, 
    cases hs with hP hQ,
    cases a'.prop with ha1 ha2,
    cases b'.prop with hb1 hb2,  
    split,
  { calc a  ≤ (a':Λ) : by exact ha1 
    ...       ≤ (s:Λ) : by exact hP , } ,   
  { calc (s:Λ) ≤ (b':Λ) : by exact hQ
    ...       ≤ b : by exact hb2 , } , 
    apply hsub, 
    exact s.prop, 
end
lemma interval_reparam_inv (Λ : Type*) [linear_ordered_add_comm_group Λ] (a b : Λ) (h : a ≤ b)
      (s: interval_a_b Λ a b) : a + b - (s:Λ) ∈ interval_a_b Λ a b :=
begin
  cases s.prop with s1 s2,
  split, 
  rw ← sub_nonneg at s2 ⊢, abel at s2 ⊢, exact s2,
  rw ← sub_nonneg at s1 ⊢, abel at s1 ⊢, exact s1,
end
-- As an example we show that an Λ-interval is actually a Λ-metric space
instance interval_a_b_is_lambda_metric_space (Λ : Type*) [linear_ordered_add_comm_group Λ]  (a b : Λ) : 
     lambda_metric_space Λ (interval_a_b Λ a b) :=
{
  dist := λ x y , |x - y|,
  dist_nonneg := 
    begin
      intros p q,
      change |(p:Λ) - q | ≥ 0,
      have h : ∀ x : Λ, |x| ≥ 0,
      exact abs_nonneg,
      apply h,
    end,
    dist_self := 
    begin
      intro p,
      change |(p:Λ) - p| = 0,
      have h : (p:Λ)-p = 0,
      exact sub_self p,
      rw h,
      exact abs_zero,
    end,
    eq_of_dist_eq_zero := 
    begin
      intros p q,
      intro hyp,
      change |(p:Λ) - q| = 0 at hyp,
      have hyp2 : (p:Λ) = q,
      refine eq_of_abs_sub_eq_zero hyp,
      refine subtype.ext hyp2,
    end,
    dist_comm := 
    begin
      intros p q,
      change |(p:Λ)-q| = |q - p|,
      have hyp : |(p:Λ) - q| = | - (p-q)|,
      exact (abs_neg ((p:Λ) - q)).symm,
      rw hyp,
      have hyp2 : - ((p:Λ)-q) = q - p,
      exact neg_sub p q,
      rw hyp2,
    end,
    dist_triangle := 
    begin
      intros p q r,
      change |(p:Λ)-q| ≤ |p-r|+ |r-q|,
      exact abs_sub_le p r q,
    end,
}

-- not used
def isom_to_interval_a_b (Λ : Type*) [linear_ordered_add_comm_group Λ] (a b : Λ)
               (X : Type*) [lambda_metric_space Λ X] :=
  lambda_isometry Λ (interval_a_b Λ a b) X 

-- We would like to define what a segment in a Λ-metric space is. 
-- In ℝ-metric spaces the corresponding notion is that of geodesic segment.
structure segment_map (Λ : Type*) [linear_ordered_add_comm_group Λ] 
              (X : Type*) [lambda_metric_space Λ X] :=
(a b : Λ)
(h : a ≤ b)
(p q : X)
(to_fun : (interval_a_b Λ a b : set Λ )  → X)
(to_p : to_fun ⟨ a , a_in_interval_a_b Λ a b h ⟩  = p)
(to_q : to_fun ⟨ b , b_in_interval_a_b Λ a b h ⟩  = q)
(isom : ∀ t s : interval_a_b Λ a b , lambda_metric_space.dist (to_fun t) (to_fun s) = |(s:Λ) - t| )

def segment (Λ : Type*) [linear_ordered_add_comm_group Λ] (X : Type*) [lambda_metric_space Λ X] 
            (f : segment_map Λ X) :=
    { x : X | ∃ t : interval_a_b Λ f.a f.b, f.to_fun t = x }

def axiom_1 (Λ : Type*) [linear_ordered_add_comm_group Λ] (X : Type*) [lambda_metric_space Λ X] :=
  ∀ x y : X , ∃ f : segment_map Λ X, f.p = x ∧ f.q = y

def axiom_unique_1 (Λ : Type*) [linear_ordered_add_comm_group Λ]  (X : Type*) [lambda_metric_space Λ X] :=
  ∀ f f' : segment_map Λ X, (f.p = f'.p  ∧ f.q = f'.q ) → (segment Λ X f' = segment Λ X f) 

def axiom_2 (Λ : Type*) [linear_ordered_add_comm_group Λ]  (X : Type*) [lambda_metric_space Λ X] :=
  ∀ f g : segment_map Λ X, 
        ((∃ x_0 : X, segment Λ X f ∩ segment Λ X g = {x_0} ∧  x_0 = f.q ∧ x_0 = g.p ) 
             → ∃ h : segment_map Λ X, segment Λ X h = segment Λ X f ∪ segment Λ X g ∧ h.p = f.p ∧ h.q = g.q )

def axiom_3 (Λ : Type*) [linear_ordered_add_comm_group Λ]  (X : Type*) [lambda_metric_space Λ X] :=
  ∀ f g : segment_map Λ X, 
        (∃ x_0 : X, x_0 = f.p ∧ x_0 = g.p ) 
             → ∃ h : segment_map Λ X, segment Λ X h = segment Λ X f ∩ segment Λ X g

-- An important class of Λ-metric spaces is Λ-trees.
class lambda_tree (Λ : Type*) [linear_ordered_add_comm_group Λ] (X : Type*) extends lambda_metric_space Λ X :=
(a1 : axiom_1 Λ X )
(a2 : axiom_2 Λ X)
(a3 : axiom_3 Λ X)

-- Here we start proving things about Lambda-trees.
lemma a_in_interval {Λ : Type*} [linear_ordered_add_comm_group Λ] {X : Type*} [lambda_metric_space Λ X]
      (f : segment_map Λ X) : f.a ∈ interval_a_b Λ f.a f.b := by exact a_in_interval_a_b Λ f.a f.b f.h
lemma b_in_interval {Λ : Type*} [linear_ordered_add_comm_group Λ] {X : Type*} [lambda_metric_space Λ X]
      (f : segment_map Λ X) : f.b ∈ interval_a_b Λ f.a f.b := by exact b_in_interval_a_b Λ f.a f.b f.h

-- f.p is contained in the segment f
lemma p_in_seg {Λ : Type*}  [linear_ordered_add_comm_group Λ] {X : Type*} [lambda_metric_space Λ X]
      (f : segment_map Λ X ) : f.p ∈ segment Λ X f :=
begin
  have h : ∃ t : interval_a_b Λ f.a f.b, f.to_fun t = f.p,
  use f.a,
  apply a_in_interval_a_b Λ f.a f.b,
  apply f.h,
  apply f.to_p,
  -- proving the rest with hypothesis h
  have hh : ∀ xx : X, ( ∃ t : interval_a_b Λ f.a f.b, f.to_fun t = xx ) 
                        ↔ ( xx ∈ { x : X | ∃ t : interval_a_b Λ f.a f.b, f.to_fun t = x} ),
  intro xx,
  refl,
  specialize hh f.p,
  rw hh at h,
  exact h,
end
-- f.q is contained in the segment f
lemma q_in_seg {Λ : Type*}  [linear_ordered_add_comm_group Λ] {X : Type*} [lambda_metric_space Λ X]
      (f : segment_map Λ X ) : f.q ∈ segment Λ X f :=
begin
  have h : ∃ t : interval_a_b Λ f.a f.b, f.to_fun t = f.q,
  use f.b,
  apply b_in_interval_a_b Λ f.a f.b,
  apply f.h,
  apply f.to_q,
  -- proving the rest with hypothesis h
  have hh : ∀ xx : X, ( ∃ t : interval_a_b Λ f.a f.b, f.to_fun t = xx ) 
                        ↔ ( xx ∈ { x : X | ∃ t : interval_a_b Λ f.a f.b, f.to_fun t = x} ),
  intro xx,
  refl,
  specialize hh f.q,
  rw hh at h,
  exact h,
end
-- for t in interval, d(p,t) = t - a
lemma dist_p_ft_in_seg (Λ : Type*) [linear_ordered_add_comm_group Λ] (X : Type*) [lambda_metric_space Λ X]
      (f : segment_map Λ X) (t : interval_a_b Λ f.a f.b) 
      : dist Λ X f.p (f.to_fun t) = (t:Λ) - f.a :=
begin
  have h1 : dist Λ X f.p (f.to_fun t) = |(t:Λ) - f.a|,
  have isom : ∀ t s : interval_a_b Λ f.a f.b , lambda_metric_space.dist (f.to_fun t) (f.to_fun s) = |(s:Λ) - t|,
  exact f.isom,
  specialize isom ⟨ f.a , a_in_interval_a_b Λ f.a f.b f.h⟩,
  specialize isom t,
  rw f.to_p at isom,
  have h2: lambda_metric_space.dist (f.p ) (f.to_fun t) =dist Λ X (f.p ) (f.to_fun t) ,
  triv,
  rw h2 at isom,
  rw isom,
  triv,
  rw h1,
  have h2 : f.a ≤ t,
  have h3 : f.a ≤ t ∧ (t:Λ) ≤ f.b,
  exact t.prop,
  cases h3 with h3a h3b,
  exact h3a,
  have h3 : 0 ≤ (t:Λ) - f.a,
  exact sub_nonneg.mpr h2,
  exact abs_of_nonneg h3,
end
-- for t in interval, d(t,q) = b - t
lemma dist_ft_q_in_seg (Λ : Type*) [linear_ordered_add_comm_group Λ] (X : Type*) [lambda_metric_space Λ X]
      (f : segment_map Λ X) (t : interval_a_b Λ f.a f.b) 
      : dist Λ X (f.to_fun t) f.q  = f.b - (t:Λ) :=
begin
  have h1 : dist Λ X (f.to_fun t) f.q = |f.b - (t:Λ) |,
  have isom : ∀ t s : interval_a_b Λ f.a f.b , lambda_metric_space.dist (f.to_fun t) (f.to_fun s) = |(s:Λ) - t|,
  exact f.isom,
  specialize isom t,
  specialize isom ⟨ f.b , b_in_interval_a_b Λ f.a f.b f.h⟩,
  rw f.to_q at isom,
  have h2: lambda_metric_space.dist  (f.to_fun t) f.q =dist Λ X  (f.to_fun t) f.q ,
  triv,
  rw h2 at isom,
  rw isom,
  triv,
  rw h1,
  have h2 : (t:Λ) ≤ f.b,
  have h3 : f.a ≤ t ∧ (t:Λ) ≤ f.b,
  exact t.prop,
  cases h3 with h3a h3b,
  exact h3b,
  have h3 : 0 ≤ f.b - (t:Λ),
  exact sub_nonneg.mpr h2,
  exact abs_of_nonneg h3,
end
-- d(f.p , f.q) = f.b - f.a
lemma dist_p_q_in_seg (Λ : Type*) [linear_ordered_add_comm_group Λ] (X : Type*) [lambda_metric_space Λ X]
      (f : segment_map Λ X) : dist Λ X f.p f.q  = f.b - f.a :=
begin
  rw ←  f.to_q,
  exact dist_p_ft_in_seg Λ X f ⟨ f.b , b_in_interval_a_b Λ f.a f.b f.h⟩,
end

-- segment_map f.to_fun is surjective
lemma seg_exists_z (Λ : Type*)  [linear_ordered_add_comm_group Λ] (X : Type*) [lambda_metric_space Λ X]
      (f:segment_map Λ X) (z : segment Λ X f ) : ∃ t : interval_a_b Λ f.a f.b, f.to_fun t = z :=
begin
  have equiv : ∀ zz : X , ( zz ∈  segment Λ X f ) ↔  ∃ t : interval_a_b Λ f.a f.b, f.to_fun t = zz,
  intro zz,
  refl,
  specialize equiv z,
  rw ← equiv,
  exact z.prop,
end

-- segment_map f.to_fun is injective
def seg_unique_t (Λ : Type*)  [linear_ordered_add_comm_group Λ] (X : Type*) [lambda_metric_space Λ X]
      (f: segment_map Λ X) (t t' : interval_a_b Λ f.a f.b) (ht : f.to_fun t = f.to_fun t')
      : t = t' :=
begin
  have h1 :  dist Λ X f.p (f.to_fun t) = (t:Λ) - f.a ,
  exact dist_p_ft_in_seg Λ X f t,
  have h2 :  dist Λ X f.p (f.to_fun t') = (t':Λ) - f.a ,
  exact dist_p_ft_in_seg Λ X f t',
  rw ←  ht at h2,
  rw h1 at h2,
  have h3 : (t : Λ) = t',
  refine sub_left_inj.mp h2,
  refine subtype.ext h3,
end

-- for properties see seg_to_interval_prop a bit lower.
def seg_to_interval {Λ : Type*}  [linear_ordered_add_comm_group Λ] {X : Type*} [lambda_metric_space Λ X]
      (f:segment_map Λ X) (z : segment Λ X f ) : interval_a_b Λ f.a f.b :=
{
  val := f.a + dist Λ X f.p z ,
  property := 
  begin
    split,
    rw ← sub_nonneg, simp, apply lambda_metric_space.dist_nonneg,  
    cases z.prop with tz htz,
    have dta : dist Λ X f.p (f.to_fun tz) = (tz:Λ) - f.a,
    exact dist_p_ft_in_seg Λ X f tz ,  
    rw ← htz, rw dta, cases tz.prop with tz1 tz2,
    rw ← sub_nonneg at tz2 ⊢ , abel at tz2 ⊢, exact tz2, 
  end
} 

-- knowing d(f.p, z) determines z in segment
def seg_d_p_z_determines_z {Λ : Type*}  [linear_ordered_add_comm_group Λ] {X : Type*} [lambda_metric_space Λ X]
      (f: segment_map Λ X) (z1 z2 : X) (hz1 : z1 ∈  segment Λ X f) (hz2 : z2 ∈ segment Λ X f)
      (deqd : dist Λ X f.p z1 = dist Λ X f.p z2)
      : z1 = z2:=
begin
  cases hz1 with t1 ht1, cases hz2 with t2 ht2, 
  have dpz1 : dist Λ X f.p z1 = (t1:Λ )- f.a,
  rw ← ht1, exact dist_p_ft_in_seg Λ X f t1,  
  have dpz2 : dist Λ X f.p z2 = (t2:Λ )- f.a,
  rw ← ht2, exact dist_p_ft_in_seg Λ X f t2, 
  rw dpz1 at deqd, rw dpz2 at deqd, simp at deqd,  
  rw ← ht1, rw ← ht2,
  have de : t1 = t2 , apply subtype.eq, exact deqd, 
  rw de,  
end

lemma seg_to_interval_prop {Λ : Type*}  [linear_ordered_add_comm_group Λ] {X : Type*} [lambda_metric_space Λ X]
      (f:segment_map Λ X) (z : segment Λ X f ) : f.to_fun (seg_to_interval f z) = z :=
begin
  let z1 : X := f.to_fun (seg_to_interval f z) ,
  have hz1 : z1 ∈ segment Λ X f,
  use seg_to_interval f z, 
  have deqd : dist Λ X f.p z1 = dist Λ X f.p z, 
  { calc dist Λ X f.p z1 = dist Λ X f.p (f.to_fun (seg_to_interval f z)) : by refl
    ...                  = (seg_to_interval f z :Λ) - f.a : by exact dist_p_ft_in_seg Λ X f (seg_to_interval f z)
    ...                  = f.a + dist Λ X f.p z - f.a : by refl
    ...                  = dist Λ X f.p z : by simp, }, 
  exact seg_d_p_z_determines_z f (z1:X) (z:X) hz1 z.prop deqd, 
end

-- knowing d(z, q) determines z in segment
def seg_d_z_q_determines_z {Λ : Type*}  [linear_ordered_add_comm_group Λ] {X : Type*} [lambda_metric_space Λ X]
      (f: segment_map Λ X) (z1 z2 : X) (hz1 : z1 ∈  segment Λ X f) (hz2 : z2 ∈ segment Λ X f)
      (deqd : dist Λ X z1 f.q = dist Λ X z2 f.q)
      : z1 = z2 :=
begin
  cases hz1 with t1 ht1, cases hz2 with t2 ht2, 
  have dpz1 : dist Λ X z1 f.q = f.b - (t1:Λ),
  rw ← ht1, exact dist_ft_q_in_seg Λ X f t1,  
  have dpz2 : dist Λ X z2 f.q = f.b - (t2:Λ),
  rw ← ht2, exact dist_ft_q_in_seg Λ X f t2,  
  rw dpz1 at deqd, rw dpz2 at deqd, simp at deqd,  
  rw ← ht1, rw ← ht2,
  have de : t1 = t2 , apply subtype.eq, exact deqd, 
  rw de,  
end
-- given two subsegments of a segment, if p is in the first subsegment, then it is in the big segment
lemma mem_seg_mem_union_seg (Λ : Type*)  [linear_ordered_add_comm_group Λ] (X : Type*) [lambda_metric_space Λ X]
      (f1 f2 f : segment_map Λ X) (h : segment Λ X f1 ∪ segment Λ X f2 = segment Λ X f)
      (p:X) (hyp : p ∈ segment Λ X f1 ) : p ∈ segment Λ X f :=
begin
  have hypp : p ∈ segment Λ X f1 ∪ segment Λ X f2,
  exact (segment Λ X f2).mem_union_left hyp,
  rw ← h,
  exact hypp,
end    
-- for t in interval, d(p,f(t)) + d(f(t),q) = d(p,q)
lemma dist_in_seg_p_q_var (Λ : Type*)  [linear_ordered_add_comm_group Λ] (X : Type*) [lambda_metric_space Λ X]
      (f : segment_map Λ X) (t : interval_a_b Λ f.a f.b ) 
      : dist Λ X f.p (f.to_fun t ) + dist Λ X (f.to_fun t ) f.q = dist Λ X f.p f.q  :=
begin
  have isom: ∀ t s : interval_a_b Λ f.a f.b ,
          lambda_metric_space.dist (f.to_fun t) (f.to_fun s) = |(s:Λ) - t|,
  exact f.isom,
  have ha : f.a ∈ interval_a_b Λ f.a f.b,
  apply a_in_interval_a_b Λ f.a f.b,
  exact f.h,
  have hb : f.b ∈ interval_a_b Λ f.a f.b,
  apply b_in_interval_a_b Λ f.a f.b,
  exact f.h,

  have hyp : |(t:Λ)-f.a| + |f.b-t| = |f.b-f.a|,
  exact dist_in_interval_a_b Λ f.a f.b f.h t , -- This is the main step
  -- now do the following 3 times.
  have h1 : dist Λ X (f.to_fun⟨ f.a , ha⟩ ) (f.to_fun t) = |(t:Λ) - f.a|,
  specialize isom ⟨ f.a , ha⟩,
  specialize isom t, 
  have hh: dist Λ X (f.to_fun⟨ f.a , ha⟩ ) (f.to_fun t) = lambda_metric_space.dist (f.to_fun⟨ f.a , ha⟩ ) (f.to_fun t),
  refl,
  rw hh,
  rw isom,
  refl,
  -- second time.
  have h2 : dist Λ X (f.to_fun t ) (f.to_fun ⟨ f.b , hb ⟩) = |(f.b:Λ) - t|,
  specialize isom t,
  specialize isom ⟨ f.b , hb ⟩, 
  have hh: dist Λ X (f.to_fun t ) (f.to_fun ⟨f.b, hb⟩) = lambda_metric_space.dist (f.to_fun t ) (f.to_fun ⟨f.b, hb⟩),
  refl,
  rw hh,
  rw isom,
  refl,
  -- third time.
  have h3 : dist Λ X (f.to_fun⟨ f.a , ha ⟩ ) (f.to_fun ⟨ f.b , hb ⟩) = |(f.b:Λ) - f.a|,
  specialize isom ⟨ f.a , ha⟩,
  specialize isom ⟨ f.b , hb ⟩, 
  have hh: dist Λ X (f.to_fun⟨ f.a , ha⟩ ) (f.to_fun ⟨f.b, hb⟩) = lambda_metric_space.dist (f.to_fun⟨ f.a , ha⟩ ) (f.to_fun ⟨f.b, hb⟩),
  refl,
  rw hh,
  rw isom,
  refl,
  rw ← f.to_p,
  rw ← f.to_q,
  rw h1,
  rw h2,
  rw h3,
  exact hyp,
end
-- for z in segment, d(p,z) + d(z,q) = d(p,q)
lemma dist_in_seg_p_q (Λ : Type*) [linear_ordered_add_comm_group Λ] (X : Type*) [lambda_metric_space Λ X]
      (f : segment_map Λ X) (z : segment Λ X f ) 
      : dist Λ X f.p z + dist Λ X z f.q = dist Λ X f.p f.q  :=
begin
  have h1 : ∃ t : interval_a_b Λ f.a f.b, f.to_fun t = z,  
  apply z.prop,
  cases z.prop with t ht,

  have h3 : dist Λ X f.p (f.to_fun t ) + dist Λ X (f.to_fun t) f.q = dist Λ X f.p f.q,
  apply dist_in_seg_p_q_var Λ X f t,
  rw ←  ht,
  exact h3,
end

-- UNUSED?
-- The following lemmas state how to translate between segments with the same starting point p.
lemma segs_same_p (Λ : Type*)  [linear_ordered_add_comm_group Λ] (X : Type*) [lambda_metric_space Λ X]
      (f1 f : segment_map Λ X) (hseg : segment Λ X f1 ⊆ segment Λ X f) (hp : f1.p = f.p) 
      (t1 : interval_a_b Λ f1.a f1.b ) : (t1:Λ)-f1.a + f.a ∈ interval_a_b Λ f.a f.b :=
begin
  have hh : f1.a ≤ (t1:Λ) ∧ (t1:Λ) ≤ f1.b,
  exact t1.prop,
  have hat : f.a ≤ (t1:Λ) - f1.a + f.a,
  have hat2 : 0 ≤ (t1:Λ) - f1.a,
  cases hh with h1 h2,
  exact sub_nonneg.mpr h1,
  exact le_add_of_nonneg_left hat2,
  -- for the ≤ b, we first need to know that d(f.p, f.q) ≥ d(f1.p, f1.q)
  have hbt : (t1:Λ) - f1.a + f.a ≤ f.b,
  have h1: f1.to_fun ⟨ t1 , t1.prop⟩ ∈ segment Λ X f1,
  have h2: ∃ s : interval_a_b Λ f1.a f1.b, f1.to_fun s = f1.to_fun (⟨ t1 , t1.prop ⟩), 
  use ⟨ t1 , t1.prop⟩,
  apply h2,
  have h2: f1.to_fun ⟨ t1, t1.prop⟩ ∈ segment Λ X f,
  apply hseg,
  apply h1,
  
  have h3 : dist Λ X f.p (f1.to_fun ⟨ t1, t1.prop⟩)  + dist Λ X  (f1.to_fun ⟨ t1, t1.prop⟩) f.q = dist Λ X f.p f.q,
  apply dist_in_seg_p_q Λ X f ⟨ _ , h2⟩,
  have h4 :  dist Λ X  (f1.to_fun ⟨ t1, t1.prop⟩) f.q ≥ 0,
  apply lambda_metric_space.dist_nonneg,
  have h5 : dist Λ X f.p (f1.to_fun ⟨ t1, t1.prop⟩)  ≤  dist Λ X f.p f.q, 
  have hh3: dist Λ X  (f1.to_fun ⟨ t1, t1.prop⟩) f.q =  dist Λ X f.p f.q - dist Λ X f.p (f1.to_fun ⟨ t1, t1.prop⟩),
  rw ←  h3,
  rw add_comm,
  exact eq_sub_of_add_eq rfl,
  rw hh3 at h4,
  exact sub_nonneg.mp h4,
  have h5 : dist Λ X f1.p (f1.to_fun ⟨ t1, t1.prop⟩)  ≤  dist Λ X f.p f.q, 
  rw hp,
  exact h5,
  have h6 :  dist Λ X f1.p (f1.to_fun ⟨ t1, t1.prop⟩) = (t1:Λ) - f1.a,
  have h7 : dist Λ X f1.p (f1.to_fun ⟨ t1, t1.prop⟩) =  |(t1:Λ) - f1.a|,
  have h8 :  f1.to_fun ⟨ f1.a , a_in_interval_a_b Λ f1.a f1.b f1.h⟩ = f1.p,
  exact  f1.to_p,
  rw ← h8,
  have isom : ∀ t s : interval_a_b Λ f1.a f1.b , lambda_metric_space.dist (f1.to_fun t) (f1.to_fun s) = |(s:Λ) - t|,
  exact f1.isom,
  specialize isom ⟨ f1.a , a_in_interval_a_b Λ f1.a f1.b f1.h⟩ ,
  specialize isom ⟨ (t1:Λ), t1.prop ⟩ ,
  have isom2 : lambda_metric_space.dist (f1.to_fun ⟨ f1.a , a_in_interval_a_b Λ f1.a f1.b f1.h⟩) 
                        (f1.to_fun ⟨ (t1: Λ) , t1.prop⟩) = |(t1:Λ) - f1.a  |,
  exact isom,
  have isom3 : dist Λ X (f1.to_fun ⟨ f1.a , a_in_interval_a_b Λ f1.a f1.b f1.h⟩) (f1.to_fun ⟨ (t1: Λ) , t1.prop⟩) 
                   = |(t1:Λ) - f1.a  |,
  exact isom2,
  exact isom3, -- we have now proved h7
  cases hh with hP hQ,
  have hPP : 0 ≤  (t1:Λ) - f1.a,
  exact sub_nonneg.mpr hP,
  have h8 : |(t1:Λ) - f1.a| = (t1:Λ)- f1.a,
  exact abs_of_nonneg hPP,
  rw ← h8,
  exact h7, -- we proved h6
  have h7 :  dist Λ X f.p f.q = f.b - f.a , 
  rw ←  f.to_q,
  exact dist_p_ft_in_seg Λ X f ⟨ f.b , b_in_interval_a_b Λ f.a f.b f.h⟩, -- we proved h7
  rw h6 at h5,
  rw h7 at h5,
  exact le_sub_iff_add_le.mp h5,
  have h8: f.a ≤ (t1:Λ) - f1.a + f.a ∧  (t1:Λ) - f1.a + f.a ≤ f.b,
  split,
  exact hat,
  exact hbt,
  exact h8,
end

-- if f(t) = f1(t1) ∈ segf1 ⊆ segf, where f.p=f1.p, then t=t1-f1.a+f.a
lemma subseg_p_in_interval_fa (Λ : Type*)  [linear_ordered_add_comm_group Λ] (X : Type*) [lambda_metric_space Λ X]
      (f1 f : segment_map Λ X) (hseg : segment Λ X f1 ⊆ segment Λ X f) (hp : f1.p = f.p) 
      (t : interval_a_b Λ f.a f.b )(t1 : interval_a_b Λ f1.a f1.b)
      (hyp : f.to_fun (t) = f1.to_fun (t1)) : (t:Λ) = t1 -f1.a + f.a :=
begin
  have h1 : dist Λ X f.p (f.to_fun t) = (t:Λ) - f.a,
  exact dist_p_ft_in_seg Λ X f t,
  have h2 : dist Λ X f1.p (f1.to_fun t1) = (t1:Λ) - f1.a,
  exact dist_p_ft_in_seg Λ X f1 t1,
  rw hyp at h1,
  rw ←  hp at h1,
  rw h1 at h2,
  exact eq_add_of_sub_eq h2,
end

-- if f(t) = f1(t1) ∈ segf2 ⊆ segf, where f.q=f2.q, then t=t2 +f.b - f2.b
lemma subseg_q_in_interval_fb (Λ : Type*)  [linear_ordered_add_comm_group Λ] (X : Type*) [lambda_metric_space Λ X]
      (f2 f : segment_map Λ X) (hseg : segment Λ X f2 ⊆ segment Λ X f) (hp : f2.q = f.q) 
      (t : interval_a_b Λ f.a f.b )(t2 : interval_a_b Λ f2.a f2.b)
      (hyp : f.to_fun (t) = f2.to_fun (t2)) : (t:Λ) = t2 + f.b - f2.b :=
begin
  have h1 : dist Λ X (f.to_fun t) f.q = f.b - (t:Λ) ,
  exact dist_ft_q_in_seg Λ X f t,
  have h2 : dist Λ X (f2.to_fun t2) f2.q = f2.b - (t2:Λ) ,
  exact dist_ft_q_in_seg Λ X f2 t2,
  rw hyp at h1,
  rw ←  hp at h1,
  rw h1 at h2,
  have h3 : f.b = f2.b -(t2 : Λ) + (t : Λ)  ,
  exact eq_add_of_sub_eq h2,
  have h4 : 0 = f2.b -(t2 : Λ) + (t : Λ) -f.b ,
  rw ←  sub_eq_zero,
  simp,
  exact sub_eq_zero.mpr h3,
  have h5:  f2.b -(t2 : Λ) + (t : Λ) -f.b = f2.b -(t2 : Λ)  -f.b + (t : Λ),
  abel,
  rw h5 at h4,
  have h4 :  f2.b -(t2 : Λ) + (t : Λ) -f.b = 0,
  exact (rfl.congr (eq.symm h4)).mp h5,
  have h5 :  f2.b -(t2 : Λ)  -f.b + (t : Λ) - (t : Λ) = -(t:Λ ),
  rw  sub_eq_neg_self,
  abel,
  abel at h4,
  exact h4,
  abel at h5,
  rw neg_inj.symm,
  abel,
  exact h5.symm,
  exact subtraction_monoid.to_has_involutive_neg Λ,
end

-- HERE WE DEFINE VARIOUS REPARAMETRIZATIONS --
def seg_reparam_0_def {Λ : Type*} [linear_ordered_add_comm_group Λ] {X : Type*} [lambda_metric_space Λ X]
      (f : segment_map Λ X)  :  segment_map Λ X :=
{   
    a := 0,
    b := f.b - f.a,
    h := 
    begin 
      have h11 : f.a ≤ f.b,
      exact f.h,
      exact sub_nonneg.mpr h11,
    end,
    p := f.p,
    q := f.q,
    to_fun := λ t : (interval_a_b Λ 0 (f.b-f.a) : set Λ ), 
                  f.to_fun ( ⟨ (t:Λ) + f.a , interval_reparam_0 Λ f.a f.b f.h t ⟩  ), 
    to_p := 
    begin
      have ha : (0:Λ) ≤ f.b - f.a,
        have h11 : f.a ≤ f.b,
        exact f.h,
        exact sub_nonneg.mpr h11,
      have hh : 0 + f.a = f.a,
      exact zero_add f.a,
      have proof : f.a ∈ interval_a_b Λ f.a f.b,
      exact a_in_interval_a_b Λ f.a f.b f.h,
      have h2 :  f.to_fun (⟨ f.a , proof ⟩  ) = f.p,
      exact f.to_p,
      have h1 :  f.to_fun (⟨ 0 + f.a , 
                  interval_reparam_0 Λ f.a f.b f.h (⟨ 0 , a_in_interval_a_b Λ 0 (f.b - f.a) ha  ⟩) ⟩ ) = f.p,
      have hu : (⟨ f.a , proof ⟩ : interval_a_b Λ f.a f.b)  = ⟨ 0 + f.a , 
                  interval_reparam_0 Λ f.a f.b f.h (⟨ 0 , a_in_interval_a_b Λ 0 (f.b - f.a) ha  ⟩) ⟩,
      exact subtype.eq (eq.symm hh),
      rw ← hu,
      exact h2,
      exact h1,   
    end,
    to_q := 
    begin
      have ha : (0:Λ) ≤ f.b - f.a,
        have h11 : f.a ≤ f.b,
        exact f.h,
        exact sub_nonneg.mpr h11,
      have hh : (f.b-f.a) + f.a = f.b,
      abel,
      have proof : f.b ∈ interval_a_b Λ f.a f.b,
      exact b_in_interval_a_b Λ f.a f.b f.h,
      have h2 :  f.to_fun (⟨ f.b , proof ⟩  ) = f.q,
      exact f.to_q,
      have h1 :  f.to_fun (⟨ (f.b-f.a) + f.a , 
                  interval_reparam_0 Λ f.a f.b f.h (⟨ (f.b-f.a) , b_in_interval_a_b Λ 0 (f.b - f.a) ha  ⟩) ⟩ ) = f.q,
      have hu : (⟨ f.b , proof ⟩ : interval_a_b Λ f.a f.b)  = ⟨ (f.b-f.a) + f.a , 
                  interval_reparam_0 Λ f.a f.b f.h (⟨ (f.b-f.a) , b_in_interval_a_b Λ 0 (f.b - f.a) ha  ⟩) ⟩,
      exact subtype.eq (eq.symm hh),
      rw ← hu,
      exact h2,
      exact h1, 
    end,
    isom := 
    begin
      intros t s,
      have tin0ba : (t: Λ) + f.a ∈ interval_a_b Λ f.a f.b,
      exact interval_reparam_0 Λ f.a f.b f.h t,
      have sin0ba : (s: Λ) + f.a ∈ interval_a_b Λ f.a f.b,
      exact interval_reparam_0 Λ f.a f.b f.h s,
      have hm : (dist Λ X) (f.to_fun ⟨ (t:Λ) + f.a , tin0ba ⟩ ) ( f.to_fun ⟨ (s:Λ) + f.a , sin0ba ⟩  ) 
           =  |((s:Λ) + f.a) - ((t:Λ) + f.a)| ,    
      have hf : ∀ tf sf : interval_a_b Λ f.a f.b , dist Λ X (f.to_fun tf) (f.to_fun sf) = |(sf:Λ) - tf|,
      exact f.isom,
      specialize hf ⟨ ((t:Λ)+ f.a) , tin0ba⟩ ,
      specialize hf ⟨ ((s:Λ)+ f.a) , sin0ba⟩ ,
      rw hf,
      simp,
      have hn : |(s:Λ) - t| = |(s:Λ)+ f.a  - (t + f.a)|,
      simp,
      rw hn,
      exact hm,  
    end,
}

lemma reparam_0_seg {Λ : Type*} [linear_ordered_add_comm_group Λ] {X : Type*} [lambda_metric_space Λ X]
      (f : segment_map Λ X) : segment Λ X f = segment Λ X (seg_reparam_0_def f) :=
begin
  let ff : segment_map Λ X := (seg_reparam_0_def f), 
  ext, 
  split,
  intro hP,  
  cases hP with tf htf, 
  cases tf.prop with tf1 tf2, 
  have htf' : (tf:Λ) - f.a ∈ interval_a_b Λ 0 (f.b - f.a),
  split, 
  rw ← sub_nonneg at tf1, exact tf1, 
  rw ← sub_nonneg at tf2 ⊢, abel at tf2 ⊢, exact tf2,  
  have htf'' : (tf:Λ) - f.a ∈ interval_a_b Λ ff.a ff.b,
  have hha : ff.a = 0, refl, 
  have hhb : ff.b = f.b - f.a, refl,
  rw hha, rw hhb,   exact htf',
  use (⟨ (tf:Λ) - f.a , htf'' ⟩ : interval_a_b Λ ff.a ff.b) ,      
  rw ← htf, 
  have tfprop :  tf = ⟨ ((tf:Λ) - f.a) + f.a , interval_reparam_0 Λ f.a f.b f.h ⟨ (tf:Λ) - f.a , htf''⟩  ⟩,  
  abel, apply subtype.eq, refl, 
  have rew : ff.to_fun ⟨ (tf:Λ) - f.a , htf'' ⟩ =
       f.to_fun  ⟨ ((tf:Λ) - f.a) + f.a , interval_reparam_0 Λ f.a f.b f.h ⟨ (tf:Λ) - f.a , htf''⟩  ⟩,
  refl, rw rew, rw ← tfprop, 
  -- prove other implication
  intro hP, 
  cases hP with tf htf, 
  cases tf.prop with tf1 tf2,
  have htf' : (tf:Λ) + f.a ∈ interval_a_b Λ f.a f.b,
  have haff : (ff.a:Λ) = 0, refl,
  have hbff : (ff.b:Λ) = f.b - f.a, refl, 
  split,
  have tf1' : 0 ≤ (tf : Λ), 
  rw ← haff, exact tf1,     
  rw ← sub_nonneg at tf1 ⊢, abel, exact tf1',   -- first split done 
  have tf2' : (tf:Λ) ≤ f.b - f.a, rw ←  hbff, exact tf2,
  rw ← sub_nonneg at tf2' ⊢ , abel at tf2' ⊢ , exact tf2',  
  use ⟨ (tf:Λ) + f.a , htf'⟩ ,
  rw ← htf, refl, 
end


-- reparametrize so that f(a)=0, TODO should be a definition with lemmas about it
lemma seg_reparam_0 (Λ : Type*)  [linear_ordered_add_comm_group Λ] (X : Type*) [lambda_metric_space Λ X]
      (f : segment_map Λ X) : ∃ f' : segment_map Λ X, 
          f'.a = 0 ∧ f'.b = dist Λ X f.p f.q ∧ f'.p = f.p ∧ f'.q = f.q ∧ segment Λ X f = segment Λ X f' :=
begin
  have ha : (0:Λ) ≤ f.b - f.a,
  have h11 : f.a ≤ f.b,
    exact f.h,
    exact sub_nonneg.mpr h11,
  let ff : segment_map Λ X :=  
  {   
    a := 0,
    b := f.b - f.a,
    h := by exact ha,
    p := f.p,
    q := f.q,
    to_fun := λ t : (interval_a_b Λ 0 (f.b-f.a) : set Λ ), 
                  f.to_fun ( ⟨ (t:Λ) + f.a , interval_reparam_0 Λ f.a f.b f.h t ⟩  ), 
    to_p := 
    begin
      have hh : 0 + f.a = f.a,
      exact zero_add f.a,
      have proof : f.a ∈ interval_a_b Λ f.a f.b,
      exact a_in_interval_a_b Λ f.a f.b f.h,
      have h2 :  f.to_fun (⟨ f.a , proof ⟩  ) = f.p,
      exact f.to_p,
      have h1 :  f.to_fun (⟨ 0 + f.a , 
                  interval_reparam_0 Λ f.a f.b f.h (⟨ 0 , a_in_interval_a_b Λ 0 (f.b - f.a) ha  ⟩) ⟩ ) = f.p,
      have hu : (⟨ f.a , proof ⟩ : interval_a_b Λ f.a f.b)  = ⟨ 0 + f.a , 
                  interval_reparam_0 Λ f.a f.b f.h (⟨ 0 , a_in_interval_a_b Λ 0 (f.b - f.a) ha  ⟩) ⟩,
      exact subtype.eq (eq.symm hh),
      rw ← hu,
      exact h2,
      exact h1,  
    end,
    to_q := 
    begin
      have hh : (f.b-f.a) + f.a = f.b,
      abel,
      have proof : f.b ∈ interval_a_b Λ f.a f.b,
      exact b_in_interval_a_b Λ f.a f.b f.h,
      have h2 :  f.to_fun (⟨ f.b , proof ⟩  ) = f.q,
      exact f.to_q,
      have h1 :  f.to_fun (⟨ (f.b-f.a) + f.a , 
                  interval_reparam_0 Λ f.a f.b f.h (⟨ (f.b-f.a) , b_in_interval_a_b Λ 0 (f.b - f.a) ha  ⟩) ⟩ ) = f.q,
      have hu : (⟨ f.b , proof ⟩ : interval_a_b Λ f.a f.b)  = ⟨ (f.b-f.a) + f.a , 
                  interval_reparam_0 Λ f.a f.b f.h (⟨ (f.b-f.a) , b_in_interval_a_b Λ 0 (f.b - f.a) ha  ⟩) ⟩,
      exact subtype.eq (eq.symm hh),
      rw ← hu,
      exact h2,
      exact h1,
    end,
    isom := 
    begin
      intros t s,
      have tin0ba : (t: Λ) + f.a ∈ interval_a_b Λ f.a f.b,
      exact interval_reparam_0 Λ f.a f.b f.h t,
      have sin0ba : (s: Λ) + f.a ∈ interval_a_b Λ f.a f.b,
      exact interval_reparam_0 Λ f.a f.b f.h s,
      have hm : (dist Λ X) (f.to_fun ⟨ (t:Λ) + f.a , tin0ba ⟩ ) ( f.to_fun ⟨ (s:Λ) + f.a , sin0ba ⟩  ) 
           =  |((s:Λ) + f.a) - ((t:Λ) + f.a)| ,    
      have hf : ∀ tf sf : interval_a_b Λ f.a f.b , dist Λ X (f.to_fun tf) (f.to_fun sf) = |(sf:Λ) - tf|,
      exact f.isom,
      specialize hf ⟨ ((t:Λ)+ f.a) , tin0ba⟩ ,
      specialize hf ⟨ ((s:Λ)+ f.a) , sin0ba⟩ ,
      rw hf,
      simp,
      have hn : |(s:Λ) - t| = |(s:Λ)+ f.a  - (t + f.a)|,
      simp,
      rw hn,
      exact hm, 
    end,
  },
  use ff,
  split,
  exact rfl,
  split,
  rw dist_p_q_in_seg Λ X f,
  split,
  exact rfl,
  split,
  exact rfl,
  ext, 
  split, 
  -- prove one implication
  intro hP,  
  --have hP :  ∃ t : interval_a_b Λ f.a f.b, f.to_fun t = x,
  --exact hP, 
  cases hP with tf htf, 
  cases tf.prop with tf1 tf2, 
  have htf' : (tf:Λ) - f.a ∈ interval_a_b Λ 0 (f.b - f.a),
  split, 
  rw ← sub_nonneg at tf1, exact tf1, 
  rw ← sub_nonneg at tf2 ⊢, abel at tf2 ⊢, exact tf2,  
  have htf'' : (tf:Λ) - f.a ∈ interval_a_b Λ ff.a ff.b,
  have hha : ff.a = 0, refl, 
  have hhb : ff.b = f.b - f.a, refl,
  rw hha, rw hhb,   exact htf',
  use (⟨ (tf:Λ) - f.a , htf'' ⟩ : interval_a_b Λ ff.a ff.b) ,      
  rw ← htf, 
  have tfprop :  tf = ⟨ ((tf:Λ) - f.a) + f.a , interval_reparam_0 Λ f.a f.b f.h ⟨ (tf:Λ) - f.a , htf''⟩  ⟩,  
  abel, apply subtype.eq, refl, 
  have rew : ff.to_fun ⟨ (tf:Λ) - f.a , htf'' ⟩ =
       f.to_fun  ⟨ ((tf:Λ) - f.a) + f.a , interval_reparam_0 Λ f.a f.b f.h ⟨ (tf:Λ) - f.a , htf''⟩  ⟩,
  refl, rw rew, rw ← tfprop, 
  -- prove other implication
  intro hP, 
  cases hP with tf htf, 
  cases tf.prop with tf1 tf2,
  have htf' : (tf:Λ) + f.a ∈ interval_a_b Λ f.a f.b,
  have haff : (ff.a:Λ) = 0, refl,
  have hbff : (ff.b:Λ) = f.b - f.a, refl, 
  split,
  have tf1' : 0 ≤ (tf : Λ), 
  rw ← haff, exact tf1,     
  rw ← sub_nonneg at tf1 ⊢, abel, exact tf1',   -- first split done 
  have tf2' : (tf:Λ) ≤ f.b - f.a, rw ←  hbff, exact tf2,
  rw ← sub_nonneg at tf2' ⊢ , abel at tf2' ⊢ , exact tf2',  
  use ⟨ (tf:Λ) + f.a , htf'⟩ ,
  rw ← htf, 
end 

def seg_reparam_sub_def {Λ : Type*} [linear_ordered_add_comm_group Λ] {X : Type*} [lambda_metric_space Λ X]
      (f : segment_map Λ X) (a' b' : interval_a_b Λ f.a f.b) (hab : a' ≤ b') :  segment_map Λ X :=
{
    a := (a':Λ),
    b := (b':Λ),
    h := hab,
    p := f.to_fun a',
    q := f.to_fun b',
    to_fun := λ t : (interval_a_b Λ a' b' : set Λ ), f.to_fun ⟨ t , 
                                  interval_reparam_sub Λ f.a f.b f.h a' b' hab t ⟩ ,
    to_p := 
    begin
      have hf : f.to_fun ⟨ (a': Λ) , interval_reparam_sub Λ f.a f.b f.h a' b' hab 
                                           ⟨ a' , a_in_interval_a_b Λ (a':Λ) (b':Λ) hab⟩ ⟩  = f.to_fun a',
      have ha : (⟨ (a': Λ) , interval_reparam_sub Λ f.a f.b f.h a' b' hab 
                                   ⟨ a' , a_in_interval_a_b Λ (a':Λ) (b':Λ) hab⟩ ⟩ : interval_a_b Λ f.a f.b) = a',
      exact subtype.coe_eta a' (interval_reparam_sub Λ f.a f.b f.h a' b' hab ⟨↑a', a_in_interval_a_b Λ ↑a' ↑b' hab⟩),
      rw ha,
      exact hf,
    end,
    to_q := 
    begin
      have hf : f.to_fun ⟨ (b': Λ) , interval_reparam_sub Λ f.a f.b f.h a' b' hab 
                                           ⟨ b' , b_in_interval_a_b Λ (a':Λ) (b':Λ) hab⟩ ⟩  = f.to_fun b',
      have hb : (⟨ (b': Λ) , interval_reparam_sub Λ f.a f.b f.h a' b' hab 
                                   ⟨ b' , b_in_interval_a_b Λ (a':Λ) (b':Λ) hab⟩ ⟩ : interval_a_b Λ f.a f.b) = b',
      exact subtype.coe_eta b' (interval_reparam_sub Λ f.a f.b f.h a' b' hab ⟨↑b', b_in_interval_a_b Λ ↑a' ↑b' hab⟩),
      rw hb,
      exact hf,
    end,
    isom := 
    begin
      intros t s,
      have fisom :  ∀ t s : interval_a_b Λ f.a f.b , lambda_metric_space.dist (f.to_fun t) (f.to_fun s) = |(s:Λ) - t|,
      exact f.isom,
      specialize fisom ⟨ t, interval_reparam_sub Λ f.a f.b f.h a' b' hab t ⟩,
      specialize fisom ⟨ s, interval_reparam_sub Λ f.a f.b f.h a' b' hab s ⟩,
      exact fisom,
    end,
}
-- property for reparam_sub for t ∈ interval
lemma reparam_sub_param {Λ : Type*} [linear_ordered_add_comm_group Λ] {X : Type*} [lambda_metric_space Λ X]
      (f : segment_map Λ X) (a' b' : interval_a_b Λ f.a f.b) (hab : a' ≤ b') 
      : ∀ t : interval_a_b Λ a' b' , (seg_reparam_sub_def f a' b' hab).to_fun t =  
         f.to_fun ⟨ t , interval_reparam_sub Λ f.a f.b f.h a' b' hab t ⟩   := 
begin
  intro t, triv,  
end
-- property for reparam_sub for segments
lemma reparam_sub_seg {Λ : Type*} [linear_ordered_add_comm_group Λ] {X : Type*} [lambda_metric_space Λ X]
      (f : segment_map Λ X)  (a' b' : interval_a_b Λ f.a f.b) (hab : a' ≤ b') 
      :  segment Λ X (seg_reparam_sub_def f a' b' hab) ⊆ segment Λ X f := 
begin 
  let ff : segment_map Λ X := seg_reparam_sub_def f a' b' hab,
  intros x hx, cases hx with tx htx,
  have hinf : (tx:Λ) ∈ interval_a_b Λ f.a f.b,
  exact interval_reparam_sub Λ f.a f.b f.h a' b' ff.h tx, 
  use ⟨ tx , hinf⟩, rw ← htx, triv, 
end
-- property for reparam_sub for x ∈ segment
lemma reparam_sub_points {Λ : Type*} [linear_ordered_add_comm_group Λ] {X : Type*} [lambda_metric_space Λ X]
      (f : segment_map Λ X) (a' b' : interval_a_b Λ f.a f.b) (hab : a' ≤ b') (x : X)
      : x ∈  segment Λ X (seg_reparam_sub_def f a' b' hab) → x ∈ segment Λ X f  := 
begin
let ff : segment_map Λ X := seg_reparam_sub_def f a' b' hab,
  intros hx, 
  have subs :  segment Λ X ff ⊆ segment Λ X f, exact reparam_sub_seg f a' b' hab,
  specialize subs hx, exact subs,
end
-- segment f1 ∪ segment f2 = segment f
lemma partition_seg {Λ : Type*} [linear_ordered_add_comm_group Λ] {X : Type*} [lambda_metric_space Λ X]
      (f : segment_map Λ X) (t : interval_a_b Λ f.a f.b)
      : segment Λ X (seg_reparam_sub_def f ⟨ f.a , a_in_interval f ⟩ t (t.prop).left)
      ∪ segment Λ X (seg_reparam_sub_def f t ⟨ f.b , b_in_interval f ⟩ (t.prop).right)
      = segment Λ X f  := 
begin
  ext w, split,
  intro hw, cases hw with hw1 hw2, 
  apply reparam_sub_points f ⟨ f.a , a_in_interval f⟩ t t.prop.left w, exact hw1,
  apply reparam_sub_points f t ⟨ f.b , b_in_interval f⟩ t.prop.right w, exact hw2, 
  intro hw, let tw : interval_a_b Λ f.a f.b := seg_to_interval f ⟨ w , hw⟩ ,
  by_cases (tw:Λ) ≤ t, -- first case:
  left,  
  use tw, cases tw.prop with hP hQ, split, exact hP, exact h, 
  have alt : f.to_fun tw = w, exact seg_to_interval_prop f ⟨ w , hw⟩ , 
  rw ← alt, refl, 
  -- now the other case:
  have h' : (t:Λ) ≤ tw, exact le_of_not_ge h, 
  right,  
  use tw, cases tw.prop with hP hQ, split, exact h', exact hQ, 
  have alt : f.to_fun tw = w, exact seg_to_interval_prop f ⟨ w , hw⟩ , 
  rw ← alt, refl, 
end

-- TODO should be a definition with lemmas about it
lemma seg_reparam_sub (Λ : Type*)  [linear_ordered_add_comm_group Λ] (X : Type*) [lambda_metric_space Λ X]
      (f : segment_map Λ X) (a' b' : interval_a_b Λ f.a f.b) (hab : a' ≤ b') : ∃ f' : segment_map Λ X, ( 
           f'.a = (a':Λ) ∧ f'.b = (b':Λ) ∧ (∀ (t : interval_a_b Λ f.a f.b) (ht : (t:Λ) ∈ interval_a_b Λ f'.a f'.b) 
          (h1 : (f'.a:Λ) ∈  interval_a_b Λ f.a f.b) (h2 : (f'.b:Λ) ∈  interval_a_b Λ f.a f.b) , f'.to_fun  ⟨ t , ht⟩  = 
          f.to_fun t ) ):= 
begin
  let ff : segment_map Λ X :=  
  {   
    a := (a':Λ),
    b := (b':Λ),
    h := hab,
    p := f.to_fun a',
    q := f.to_fun b',
    to_fun := λ t : (interval_a_b Λ a' b' : set Λ ), f.to_fun ⟨ t , 
                                  interval_reparam_sub Λ f.a f.b f.h a' b' hab t ⟩ ,
    to_p := 
    begin
      have hf : f.to_fun ⟨ (a': Λ) , interval_reparam_sub Λ f.a f.b f.h a' b' hab 
                                           ⟨ a' , a_in_interval_a_b Λ (a':Λ) (b':Λ) hab⟩ ⟩  = f.to_fun a',
      have ha : (⟨ (a': Λ) , interval_reparam_sub Λ f.a f.b f.h a' b' hab 
                                   ⟨ a' , a_in_interval_a_b Λ (a':Λ) (b':Λ) hab⟩ ⟩ : interval_a_b Λ f.a f.b) = a',
      exact subtype.coe_eta a' (interval_reparam_sub Λ f.a f.b f.h a' b' hab ⟨↑a', a_in_interval_a_b Λ ↑a' ↑b' hab⟩),
      rw ha,
      exact hf,
    end,
    to_q := 
    begin
      have hf : f.to_fun ⟨ (b': Λ) , interval_reparam_sub Λ f.a f.b f.h a' b' hab 
                                           ⟨ b' , b_in_interval_a_b Λ (a':Λ) (b':Λ) hab⟩ ⟩  = f.to_fun b',
      have hb : (⟨ (b': Λ) , interval_reparam_sub Λ f.a f.b f.h a' b' hab 
                                   ⟨ b' , b_in_interval_a_b Λ (a':Λ) (b':Λ) hab⟩ ⟩ : interval_a_b Λ f.a f.b) = b',
      exact subtype.coe_eta b' (interval_reparam_sub Λ f.a f.b f.h a' b' hab ⟨↑b', b_in_interval_a_b Λ ↑a' ↑b' hab⟩),
      rw hb,
      exact hf,
    end,
    isom := 
    begin
      intros t s,
      have fisom :  ∀ t s : interval_a_b Λ f.a f.b , lambda_metric_space.dist (f.to_fun t) (f.to_fun s) = |(s:Λ) - t|,
      exact f.isom,
      specialize fisom ⟨ t, interval_reparam_sub Λ f.a f.b f.h a' b' hab t ⟩,
      specialize fisom ⟨ s, interval_reparam_sub Λ f.a f.b f.h a' b' hab s ⟩,
      exact fisom,
    end,
  },
  use ff,
  split, 
  exact rfl,
  split,
  exact rfl,
  intros t tff h1 h2, 
  have hhy: ff.a = a',
  refl,
  rw hhy at h1,    
  have hhz: ff.b = b',
  refl,
  rw hhz at h2,  
  have ϕ :  (⟨((⟨ (t:Λ) , tff⟩ : interval_a_b Λ ff.a ff.b):Λ ) , 
          interval_reparam_sub Λ f.a f.b f.h a' b' ff.h ⟨(t:Λ), tff⟩⟩:interval_a_b Λ f.a f.b) = t,    
  apply subtype.ext,   
  refl, 
  have hihi : ff.to_fun ⟨ (t:Λ), tff⟩ = f.to_fun  (⟨((⟨ (t:Λ) , tff⟩ : interval_a_b Λ ff.a ff.b):Λ ) , 
          interval_reparam_sub Λ f.a f.b f.h a' b' ff.h ⟨(t:Λ), tff⟩⟩:interval_a_b Λ f.a f.b),
  refl, rw hihi, rw ϕ, 
end

def seg_reparam_inv {Λ : Type*} [linear_ordered_add_comm_group Λ] {X : Type*} [lambda_metric_space Λ X]
      (f : segment_map Λ X)  :  segment_map Λ X :=
{   
    a := f.a,
    b := f.b,
    h := f.h,
    p := f.q,
    q := f.p,
    to_fun := λ t : (interval_a_b Λ f.a f.b : set Λ ), f.to_fun ⟨ f.a + f.b - (t:Λ) , 
                                  interval_reparam_inv Λ f.a f.b f.h t ⟩ ,
    to_p := 
    begin
      rw ← f.to_q, 
      have h : (⟨f.a + f.b - ((⟨f.a, a_in_interval f⟩:interval_a_b Λ f.a f.b):Λ), 
      interval_reparam_inv Λ f.a f.b f.h ⟨f.a, a_in_interval f⟩⟩ : interval_a_b Λ f.a f.b) 
      = ⟨f.b , b_in_interval f⟩,
      apply subtype.eq, 
      have h2: f.a + f.b - ((⟨f.a, a_in_interval f⟩:interval_a_b Λ f.a f.b):Λ) =f.b, simp,
      exact h2, 
      rw h,  
    end,
    to_q := 
    begin
      rw ← f.to_p, 
      have h : (⟨f.a + f.b - ((⟨f.b, b_in_interval f⟩:interval_a_b Λ f.a f.b):Λ), 
      interval_reparam_inv Λ f.a f.b f.h ⟨f.b, b_in_interval f⟩⟩ : interval_a_b Λ f.a f.b) 
      = ⟨f.a , a_in_interval f⟩,
      apply subtype.eq, 
      have h2: f.a + f.b - ((⟨f.b, b_in_interval f⟩:interval_a_b Λ f.a f.b):Λ) =f.a, simp,
      exact h2, 
      rw h,  
    end,
    isom := 
    begin
      intros t s,
      have fisom :  ∀ t s : interval_a_b Λ f.a f.b , lambda_metric_space.dist (f.to_fun t) (f.to_fun s) = |(s:Λ) - t|,
      exact f.isom,
      specialize fisom ⟨ f.a + f.b - (t:Λ), interval_reparam_inv Λ f.a f.b f.h t ⟩,
      specialize fisom ⟨ f.a + f.b - (s:Λ), interval_reparam_inv Λ f.a f.b f.h s ⟩,
      have hh : ((⟨f.a + f.b - ↑s, interval_reparam_inv Λ f.a f.b f.h s⟩:interval_a_b Λ f.a f.b ):Λ) 
                   - (⟨f.a + f.b - ↑t, interval_reparam_inv Λ f.a f.b f.h t⟩:interval_a_b Λ f.a f.b) 
                         = f.a + f.b - (s:Λ) - (f.a + f.b - (t:Λ)),
      refl,  
      rw hh at fisom, simp at fisom, 
      have sy : |(s:Λ) - t| = |(t:Λ)- s|,
      refine abs_sub_comm ↑s ↑t,
      rw sy, exact fisom,  
    end,
}

lemma reparam_inv_seg {Λ : Type*} [linear_ordered_add_comm_group Λ] {X : Type*} [lambda_metric_space Λ X]
      (f : segment_map Λ X) : segment Λ X f = segment Λ X (seg_reparam_inv f) :=
begin
  ext, split,
  intro hx,
  cases hx with tx htx, 
  use (⟨ f.a + f.b - (tx:Λ) , interval_reparam_inv Λ f.a f.b f.h tx ⟩:interval_a_b Λ f.a f.b),
  have h: ( ⟨ f.a + f.b - ((⟨f.a + f.b - ↑tx, interval_reparam_inv Λ f.a f.b f.h tx⟩:interval_a_b Λ f.a f.b):Λ ) , 
               interval_reparam_inv Λ f.a f.b f.h ⟨f.a + f.b - ↑tx, interval_reparam_inv Λ f.a f.b f.h tx⟩ ⟩ 
               :interval_a_b Λ f.a f.b).1 = f.a + f.b  - (f.a + f.b - tx.1),
  refl, 
  have h2: ( ⟨ f.a + f.b - ((⟨f.a + f.b - ↑tx, interval_reparam_inv Λ f.a f.b f.h tx⟩:interval_a_b Λ f.a f.b):Λ ) , 
               interval_reparam_inv Λ f.a f.b f.h ⟨f.a + f.b - ↑tx, interval_reparam_inv Λ f.a f.b f.h tx⟩ ⟩ 
               :interval_a_b Λ f.a f.b).1 = tx.1,
  rw h, simp, 
  have h3: ( ⟨ f.a + f.b - ((⟨f.a + f.b - ↑tx, interval_reparam_inv Λ f.a f.b f.h tx⟩:interval_a_b Λ f.a f.b):Λ ) , 
               interval_reparam_inv Λ f.a f.b f.h ⟨f.a + f.b - ↑tx, interval_reparam_inv Λ f.a f.b f.h tx⟩ ⟩ 
               :interval_a_b Λ f.a f.b) = tx,
  apply subtype.eq, exact h2, rw ← htx,   
  have h4 : (seg_reparam_inv f).to_fun ⟨f.a + f.b - ↑tx, interval_reparam_inv Λ f.a f.b f.h tx ⟩
                  = f.to_fun ⟨f.a + f.b - (⟨f.a + f.b - ↑tx, interval_reparam_inv Λ f.a f.b f.h tx⟩:interval_a_b Λ f.a f.b).1, 
                   interval_reparam_inv Λ f.a f.b f.h ⟨f.a + f.b - ↑tx, interval_reparam_inv Λ f.a f.b f.h tx ⟩ ⟩,
  triv,  
  let n : X := f.to_fun tx,
  have hyp : n = f.to_fun tx , triv, 
  rw  ← hyp, 
  rw ← h3 at hyp, rw hyp, exact h4, 
  -- sorry for the mess,

  intro hx,
  cases hx with tx htx,
  use ⟨ f.a + f.b - (tx:Λ) , interval_reparam_inv Λ f.a f.b f.h tx⟩, 
  rw ← htx, refl,  
end

-- for 3 points,  d(f(u),f(v)) + d(f(v),f(w)) = d(f(u),f(w)) 
lemma dist_in_seg_u_v_w (Λ : Type*) [linear_ordered_add_comm_group Λ] (X : Type*) [lambda_metric_space Λ X]
      (f : segment_map Λ X) (u v w : interval_a_b Λ f.a f.b) (huv : u ≤ v) (hvw : v ≤ w) 
      : dist Λ X (f.to_fun u) (f.to_fun v) + dist Λ X (f.to_fun v) (f.to_fun w) = dist Λ X (f.to_fun u) (f.to_fun w)  :=
begin
  have huw : u ≤ w, 
  {calc u ≤ v : by exact huv 
      ... ≤ w : by exact hvw , } ,
  have hv : (v:Λ) ∈ interval_a_b Λ (u:Λ) w,
  split, exact huv, exact hvw,
  have hf : ∃ f' : segment_map Λ X, ( 
           f'.a = (u:Λ) ∧ f'.b = (w:Λ) ∧ (∀ (t : interval_a_b Λ f.a f.b) (ht : (t:Λ) ∈ interval_a_b Λ f'.a f'.b) 
          (h1 : (f'.a:Λ) ∈  interval_a_b Λ f.a f.b) (h2 : (f'.b:Λ) ∈  interval_a_b Λ f.a f.b) , f'.to_fun  ⟨ t , ht⟩  = 
          f.to_fun t ) ),
  exact seg_reparam_sub Λ X f u w huw,  
  cases hf with f' hf',
  cases hf' with ha hf',
  cases hf' with hb hf',
  have haa : f'.a ∈ interval_a_b Λ f.a f.b,
  rw ha, exact u.prop,
  have hbb : f'.b ∈ interval_a_b Λ f.a f.b,
  rw hb, exact w.prop, 
  have htu : (u:Λ) ∈ interval_a_b Λ f'.a f'.b,
  rw ← ha, exact a_in_interval_a_b Λ f'.a f'.b f'.h,
  have htw : (w:Λ) ∈ interval_a_b Λ f'.a f'.b,
  rw ← hb, exact b_in_interval_a_b Λ f'.a f'.b f'.h, 
  have htv : (v:Λ) ∈ interval_a_b Λ f'.a f'.b,
  split, rw ha, exact huv, rw hb, exact hvw, 
  have ftof'u : f'.to_fun ⟨ u , htu⟩ = f.to_fun u,
  specialize hf' u, specialize hf' htu, specialize hf' haa, specialize hf' hbb, exact hf',  
  have ftof'v : f'.to_fun ⟨ v , htv⟩ = f.to_fun v,
  specialize hf' v, specialize hf' htv, specialize hf' haa, specialize hf' hbb, exact hf', 
  have ftof'w : f'.to_fun ⟨ w , htw⟩ = f.to_fun w,
  specialize hf' w, specialize hf' htw, specialize hf' haa, specialize hf' hbb, exact hf', 
  rw ← ftof'u, rw ← ftof'v , rw ← ftof'w, 
  have haaa : (f'.a : Λ) ∈ interval_a_b Λ f'.a f'.b,
  exact a_in_interval_a_b Λ f'.a f'.b f'.h,
  have hbbb : (f'.b : Λ) ∈ interval_a_b Λ f'.a f'.b,
  exact b_in_interval_a_b Λ f'.a f'.b f'.h, 
  have hv : f'.to_fun ⟨ (v:Λ), htv ⟩ ∈ segment Λ X f',
  have pro : ∃ t : interval_a_b Λ f'.a f'.b, f'.to_fun t = f'.to_fun ⟨ (v:Λ), htv ⟩,
  use ⟨ (v:Λ) , htv⟩,
  exact pro, -- now we proved hv
  have tri : dist Λ X f'.p (f'.to_fun ⟨ (v:Λ), htv ⟩)  + dist Λ X (f'.to_fun ⟨ (v:Λ), htv ⟩) f'.q = dist Λ X f'.p f'.q,
  exact dist_in_seg_p_q Λ X f'  ⟨ f'.to_fun ⟨ (v:Λ), htv ⟩ , hv⟩  , 
  have hhu : f'.to_fun ⟨ u , htu ⟩ = f'.p,
  rw ← f'.to_p,     
  have helper : (⟨ u , htu⟩:interval_a_b Λ f'.a f'.b) = ⟨ f'.a , haaa ⟩    ,
  exact subtype.eq (eq.symm ha),
  rw helper, 
  have hhw : f'.to_fun ⟨ w , htw ⟩ = f'.q,
  rw ← f'.to_q,     
  have helper : (⟨ w , htw⟩:interval_a_b Λ f'.a f'.b) = ⟨ f'.b , hbbb ⟩    ,
  exact subtype.eq (eq.symm hb),
  rw helper, 
  rw hhu, rw hhw, exact tri,  
end

-- We will now prove some basic lemmas whose main point is:
-- If axiom (1) is in presence of axiom (2) or (3), then unique (1) holds.

-- helper for segments_intersect_once
lemma calculation_lemma_1 (Λ : Type* ) [linear_ordered_add_comm_group Λ] (txf tyf fa fb f1a f1b f2a f2b : Λ ) 
(h1 :txf - fa + f1a ≤ f1b) (h2 : f2a ≤ tyf - fb + f2b) (h3: f1b - f1a + (f2b - f2a) = fb -fa): txf ≤ tyf :=
begin
  have h4 : txf ≤ f1b - f1a + fa  , -- using h1
  have h4' : txf - fa + f1a + (fa - f1a) ≤ f1b  + ( fa -f1a),
  apply add_le_add_right h1 (fa - f1a), 
  abel at h4',
  abel,
  exact h4', -- proved h4

  have h5 : f1b - f1a + fa = f2a - f2b + fb, -- using h3
  have h5' : f1b - f1a + (f2b - f2a) + (fa - f2b + f2a) = fb - fa + (fa - f2b + f2a),
  exact congr_fun (congr_arg has_add.add h3) (fa - f2b + f2a),
  abel at h5',
  abel,
  exact h5', -- proved h5

  have h6 : f2a - f2b + fb ≤ tyf, -- using h2
  have h6' : f2a + (fb - f2b) ≤ tyf - fb + f2b + (fb - f2b),
  apply add_le_add_right h2 (fb - f2b),
  abel at h6',
  abel,
  exact h6', -- proved h6

  rw h5 at h4,
  exact le_trans h4 h6, 
end

-- This is a stronger version of Lemma 2 in [paper].
lemma segments_intersect_once (Λ : Type*)  [linear_ordered_add_comm_group Λ] (X : Type*) [lambda_metric_space Λ X]
      (x y z p: X) (f1 f2 f g : segment_map Λ X ) (h1 : f1.p = x) (h2 : f1.q = z) (h3 : f2.p = z) (h4 : f2.q = y)
      (h5: f.p = x) (h6 : f.q = y) (h7 : g.p = z) (h8 : g.q = p) (h9 : segment Λ X f1 ∪ segment Λ X f2 = segment Λ X f)
      : segment Λ X f1 ∩ segment Λ X g = {z} ∨ segment Λ X f2 ∩ segment Λ X g = {z} :=
begin
  have rewrite: (∀ u : X, u ∈ (segment Λ X f1 ∩ segment Λ X g) → u = z)
                ∨ (∀ v : X, v ∈ (segment Λ X f2 ∩ segment Λ X g) → v = z),  
  simp_rw [← forall_or_distrib_right, ← forall_or_distrib_left ], --forall_or_distrib_right,
  intros x' hx' y' hy',
  -- Now prove x' y' ∈ f
  have hinfx' : x' ∈ segment Λ X f,
  have hhx' : x' ∈ segment Λ X f1,
  exact set.mem_of_mem_inter_left hx',
  rw ← h9,
  exact (segment Λ X f2).mem_union_left hhx',
  have hinfy' : y' ∈ segment Λ X f,
  have hhy' : y' ∈ segment Λ X f2,
  exact set.mem_of_mem_inter_left hy',
  rw ← h9,
  exact (segment Λ X f1).mem_union_right hhy',
  -- Now prove x' y' ∈ g
  have hingx' : x' ∈ segment Λ X g,
  have hhx' : x' ∈ segment Λ X g,
  exact set.mem_of_mem_inter_right hx',
  exact hhx',
  have hingy' : y' ∈ segment Λ X g,
  have hhy' : y' ∈ segment Λ X g,
  exact set.mem_of_mem_inter_right hy',
  exact hhy',
  -- parametrize in f
  have htxf: ∃ txf : interval_a_b Λ f.a f.b, f.to_fun txf = x',
  apply seg_exists_z Λ X f ⟨ x' ,  hinfx' ⟩ ,
  have htyf: ∃ tyf : interval_a_b Λ f.a f.b, f.to_fun tyf = y',
  apply seg_exists_z Λ X f ⟨ y' , hinfy'⟩ ,
  cases htxf with txf htxf,
  cases htyf with tyf htyf,
  
  -- our goal is to prove d x' z + d z y' = d x' z'  
  have hseg1 : segment Λ X f1 ⊆ segment Λ X f, 
  have hh1 : ∀ x, x ∈ segment Λ X f1  → x ∈ segment Λ X f, 
  intro xx,
  intro hxx,
  have hh2 : xx ∈ segment Λ X f1 ∪ segment Λ X f2,
  exact (segment Λ X f2).mem_union_left hxx,
  rw h9 at hh2,
  exact hh2, 
  exact hh1, -- we now proved hseg1
  have hseg2 : segment Λ X f2 ⊆ segment Λ X f,
  have hh1 : ∀ x, x ∈ segment Λ X f2  → x ∈ segment Λ X f,
  intro xx,
  intro hxx,
  have hh2 : xx ∈ segment Λ X f1 ∪ segment Λ X f2,
  exact (segment Λ X f1).mem_union_right hxx,
  rw h9 at hh2,
  exact hh2,
  exact hh1, -- we now proved hseg2
  have hp : f1.p = f.p,
  rw h5,
  rw ← h1,
  have hq : f2.q = f.q,
  rw h6,
  rw ← h4,
  have hh2 : (txf:Λ)-f.a + f1.a ∈ interval_a_b Λ f1.a f1.b, -- start hh2
  have hinf1x' : x' ∈ segment Λ X f1,
  have hhh1 : x' ∈ segment Λ X f1 ∧ x' ∈ segment Λ X g,
  exact hx',
  cases hhh1 with hP hQ,
  exact hP,
  have hh3t1 : ∃ t1 : interval_a_b Λ f1.a f1.b, f1.to_fun t1 = x',
  exact seg_exists_z Λ X f1 ⟨ x' , hinf1x'⟩ ,
  cases hh3t1 with t1 ht1,
  rw ← htxf at ht1,
  have hh4 : (txf:Λ) = t1 -f1.a + f.a,
  exact subseg_p_in_interval_fa Λ X f1 f hseg1 hp txf t1 ht1.symm, -- main statement we used for hh2
  rw hh4,
  have hhhhh : (t1:Λ) = ↑t1 - f1.a + f.a - f.a + f1.a,
  simp,
  rw ← hhhhh,
  exact t1.prop, -- we now proved hh2
  have hh3 :(tyf:Λ) - f.b + f2.b ∈ interval_a_b Λ f2.a f2.b, -- start hh3
  have hinf2y' : y' ∈ segment Λ X f2,
  have hhh1 : y' ∈ segment Λ X f2 ∧ y' ∈ segment Λ X g,
  exact hy',
  cases hhh1 with hP hQ,
  exact hP,
  have hh3t2 : ∃ t2 : interval_a_b Λ f2.a f2.b, f2.to_fun t2 = y',
  exact seg_exists_z Λ X f2 ⟨ y' , hinf2y'⟩ ,
  cases hh3t2 with t2 ht2,
  rw ← htyf at ht2,
  have hh4 : (tyf:Λ) = t2 + f.b - f2.b,
  
  exact subseg_q_in_interval_fb Λ X f2 f hseg2 hq tyf t2 ht2.symm, -- main statement 2 we used
  rw hh4,
  have hhhhh : (t2:Λ) = ↑t2 + f.b - f2.b - f.b + f2.b,
  abel,
  rw ← hhhhh,
  exact t2.prop, -- we now proved hh3

  have hz :  ∃ t : interval_a_b Λ f.a f.b, f.to_fun t = z ,
  have hhz : z ∈ segment Λ X f,
  have hhhz : z ∈ segment Λ X f1,
  rw ← h2, exact q_in_seg f1, 
  have hhhhz : z ∈ segment Λ X f1 ∨ z ∈ segment Λ X f2,
  left, exact hhhz, 
  rw ←  h9, exact hhhhz, 
  exact hhz, 

  cases hz with tzf hz, 
  
  -- we will spend some time proving the following now
  have hdf : dist Λ X (f.to_fun txf) (f.to_fun tzf) + dist Λ X (f.to_fun tzf) (f.to_fun tyf) = dist Λ X (f.to_fun txf) (f.to_fun tyf),

  have hx'z : (txf:Λ) ≤ tzf,
  have tzf1 : (tzf:Λ) = f1.b -f1.a + f.a ,
  have hypz : f.to_fun tzf = f1.to_fun ⟨ f1.b , b_in_interval_a_b Λ f1.a f1.b f1.h⟩ ,
  rw hz, rw f1.to_q, rw h2, 
  exact subseg_p_in_interval_fa Λ X f1 f hseg1 hp tzf ⟨ f1.b , b_in_interval_a_b Λ f1.a f1.b f1.h⟩ hypz,
  cases hh2 with hP1 hQ1,
  have tzf1' : (tzf:Λ) -f.a + f1.a = f1.b,
  rw tzf1, simp, 
  rw ← tzf1' at hQ1, rw ← sub_nonneg at hQ1 ⊢, abel at hQ1 ⊢, exact hQ1, 

  have hzy' :  (tzf:Λ) ≤ tyf,
  have tzf2 : (tzf:Λ) = f2.a + f.b - f2.b, -- (t:Λ) = t2 + f.b - f2.b
  have hypz : f.to_fun tzf = f2.to_fun ⟨ f2.a , a_in_interval_a_b Λ f2.a f2.b f2.h⟩ ,
  rw hz, rw f2.to_p, rw h3,  
  exact subseg_q_in_interval_fb Λ X f2 f hseg2 hq tzf ⟨ f2.a , a_in_interval_a_b Λ f2.a f2.b f2.h⟩ hypz,
  cases hh3 with hP2 hQ2, 
  have tzf2' : (tzf:Λ) - f.b + f2.b = f2.a,
  rw tzf2, abel, 
  rw ← tzf2' at hP2, rw ← sub_nonneg at hP2 ⊢, abel at hP2 ⊢, exact hP2,  
 
  -- now we finally prove d x' z + d z y' = d x' z'
  exact dist_in_seg_u_v_w Λ X f txf tzf tyf hx'z hzy', 
  rw htxf at hdf, rw htyf at hdf, rw hz at hdf,  
  
  -- next we rewrite the distances in terms of g
  have g0 : ∃ gg : segment_map Λ X, gg.a = 0 ∧ gg.b = dist Λ X g.p g.q ∧ gg.p = g.p ∧ gg.q = g.q  ∧ segment Λ X g = segment Λ X gg,
    exact seg_reparam_0 Λ X g, 
  cases g0 with gg hgg, 
  cases hgg with gga ggb, cases ggb with ggb ggp, cases ggp with ggp ggq, cases ggq with ggq ggseg,   
  have hinggx' : x' ∈ segment Λ X gg, rw ← ggseg, exact hingx',  
  have hinggy' : y' ∈ segment Λ X gg, rw ← ggseg, exact hingy',  

  have htxg: ∃ txg : interval_a_b Λ gg.a gg.b, gg.to_fun txg = x',
  apply seg_exists_z Λ X gg ⟨ x' ,  hinggx' ⟩ ,
  have htyg: ∃ tyg : interval_a_b Λ gg.a gg.b, gg.to_fun tyg = y',
  apply seg_exists_z Λ X gg ⟨ y' ,  hinggy' ⟩ ,
  cases htxg with txg htxg,
  cases htyg with tyg htyg,

  have dzxg : dist Λ X x' z = (txg:Λ), 
  have dzxg' : dist Λ X gg.p (gg.to_fun txg) = (txg:Λ) - gg.a ,
  exact dist_p_ft_in_seg Λ X gg txg,  
  rw htxg at dzxg', rw ggp at dzxg', rw h7 at dzxg', 
  have h0 : (txg : Λ) - 0 = txg, 
  simp, 
  rw ← gga at h0, rw ← h0,  
  have com : ∀ p q : X, dist Λ X p q = dist Λ X q p,
  exact lambda_metric_space.dist_comm,   
  specialize com x', specialize com z,  
  rw com, exact dzxg',  

  have dyzg : dist Λ X z y' = (tyg:Λ), 
  have dyzg' : dist Λ X gg.p (gg.to_fun tyg) = (tyg:Λ) - gg.a ,
  exact dist_p_ft_in_seg Λ X gg tyg,  
  rw htyg at dyzg', rw ggp at dyzg', rw h7 at dyzg', 
  have h0 : (tyg : Λ) - 0 = tyg, 
  simp, 
  rw ← gga at h0, rw ← h0, exact dyzg',  

  by_cases (txg:Λ) ≤ tyg,
  left, -- we prove x' = z
  
  have dyxg : dist Λ X x' y' = (tyg:Λ) - txg, 
  have isomg: ∀ t s : interval_a_b Λ gg.a gg.b , lambda_metric_space.dist (gg.to_fun t) (gg.to_fun s) = |(s:Λ) - t|,
  exact gg.isom,        
  specialize isomg txg, specialize isomg tyg, 
  rw htxg at isomg, rw htyg at isomg, 
  have hhhhh : | (tyg:Λ) - txg | = (tyg:Λ) - txg,  
  have hhhhhh : 0 ≤ (tyg:Λ) - txg, rw ← sub_nonneg at h, exact h,   
  exact abs_of_nonneg hhhhhh, 
  rw ← hhhhh, exact isomg,   

  rw dzxg at hdf, rw dyxg at hdf, rw dyzg at hdf,     
  
  have h2 : (txg:Λ) = - txg,
  rw ← sub_eq_zero at hdf ⊢ , abel at hdf ⊢, exact hdf, 
  have hx0 : (txg:Λ) = 0,
  exact eq_zero_of_neg_eq (eq.symm h2),  
  have hx00 : (txg:Λ) = gg.a,
  rw ← gga at hx0, exact hx0,
  have hx000 : txg = ⟨ gg.a , a_in_interval_a_b Λ gg.a gg.b gg.h⟩, apply subtype.eq, exact hx00, 
  rw ← htxg, rw ← h7, rw ← ggp, rw ← gg.to_p, rw ← hx000,

  right,     -- we prove y' = z
  have h' : (tyg:Λ) < txg, exact not_le.mp h,  
  have h : (tyg:Λ) ≤ txg,
  exact le_of_lt h', 

  have dyxg : dist Λ X x' y' = (txg:Λ) - tyg, 
  have isomg: ∀ t s : interval_a_b Λ gg.a gg.b , dist Λ X (gg.to_fun t) (gg.to_fun s) = |(s:Λ) - t|,
  exact gg.isom,        
  specialize isomg tyg, specialize isomg txg, 
  rw htyg at isomg, rw htxg at isomg, 
  have hhhhh : | (txg:Λ) - tyg | = (txg:Λ) - tyg,  
  have hhhhhh : 0 ≤ (txg:Λ) - tyg, rw ← sub_nonneg at h, exact h,   
  exact abs_of_nonneg hhhhhh,  
  rw ← hhhhh, 
  have com : ∀ p q : X, dist Λ X p q = dist Λ X q p,
  exact lambda_metric_space.dist_comm,   
  specialize com x', specialize com y',  
  rw com,
  exact isomg,       

  rw dzxg at hdf, rw dyxg at hdf, rw dyzg at hdf,   

  have h2 : (tyg:Λ) = - tyg,
  rw ← sub_eq_zero at hdf ⊢ , abel at hdf ⊢, exact hdf, 
  have hy0 : (tyg:Λ) = 0,
  exact eq_zero_of_neg_eq (eq.symm h2),  
  have hy00 : (tyg:Λ) = gg.a,
  rw ← gga at hy0, exact hy0,
  have hy000 : tyg = ⟨ gg.a , a_in_interval_a_b Λ gg.a gg.b gg.h⟩, apply subtype.eq, exact hy00, 
  rw ← htyg, rw ← h7, rw ← ggp, rw ← gg.to_p, rw ← hy000, 
  -- this concludes the proof of rewrite  
  -- now solve the rewrite, first hleft
  cases rewrite with hleft hright,
  left,
  ext,
  split,
  intro propx_1,
  specialize hleft x_1,
  apply hleft,
  exact propx_1,
  intro hh,
  have hypp : x_1 = z,
  exact set.mem_singleton_iff.mp hh,
  have inf1 : x_1 ∈ segment Λ X f1,
  rw ←  h2 at hypp,
  rw hypp,
  apply q_in_seg,
  have inf2 : x_1 ∈ segment Λ X g,
  rw ← h7 at hypp,
  rw hypp,
  apply p_in_seg, 
  have hyppp : x_1 ∈ segment Λ X f1 ∧  x_1 ∈ segment Λ X g,
  split,
  exact inf1,
  exact inf2,
  exact hyppp, 
  -- now solve hright the same way:
  right,
  ext,
  split,
  intro propx_1,
  specialize hright x_1, 
  apply hright,
  exact propx_1,
  intro hh,
  have hypp : x_1 = z,
  exact set.mem_singleton_iff.mp hh,
  have inf1 : x_1 ∈ segment Λ X f2,
  rw ←  h3 at hypp,
  rw hypp,
  apply p_in_seg,
  have inf2 : x_1 ∈ segment Λ X g,
  rw ← h7 at hypp,
  rw hypp,
  apply p_in_seg, 
  have hyppp : x_1 ∈ segment Λ X f2 ∧  x_1 ∈ segment Λ X g,
  split,
  exact inf1,
  exact inf2,
  exact hyppp,     
end

-- The following is the main content of the succeeding Lemma, Lemma 3.6 in Chiswel [Chi]
lemma axioms_1_2_imply_unique_1_f_f' (Λ  : Type*) [linear_ordered_add_comm_group Λ] (X:Type*)[lambda_metric_space Λ X]
      (f f' : segment_map Λ X) (hh: f.p = f'.p ∧ f.q = f'.q)
     : axiom_1 Λ X ∧ axiom_2 Λ X → (segment Λ X f ⊆ segment Λ X f') :=
begin
  intros h, 
  cases h with h1 h2, 
  cases hh with hh1 hh2,
  intro z, 
  intro hz, 
  have ht : ∃ t : interval_a_b Λ f.a f.b, f.to_fun t = z,
  exact seg_exists_z Λ X f ⟨ z, hz ⟩ , 
  cases ht with tz htz,
  have hlen : f.b - f.a = f'.b -f'.a , 
  rw ← dist_p_q_in_seg Λ X f, rw ← dist_p_q_in_seg Λ X f', rw hh1, rw hh2, 
  have htz' : (tz:Λ) + f'.a - f.a ∈ interval_a_b Λ f'.a f'.b,
  exact interval_reparam_trans Λ f.a f.b f'.a f'.b f.h f'.h hlen tz,
  let p : X := f'.to_fun ⟨ (tz:Λ)+ f'.a - f.a , htz' ⟩,
  --have a1: ∀ x y : X , ∃ f : segment_map Λ X, f.p = x ∧ f.q = y, exact h1,
  specialize h1 z, specialize h1 p, cases h1 with g hg, cases hg with hgp hgq,
   
  have hsub1: ∃ f1 : segment_map Λ X, ( f1.a = (f.a:Λ) ∧ f1.b = (tz:Λ) ∧ (∀ (t : interval_a_b Λ f.a f.b)
           (ht : (t:Λ) ∈ interval_a_b Λ f1.a f1.b) (h1 : (f1.a:Λ) ∈  interval_a_b Λ f.a f.b)
           (h2 : (f1.b:Λ) ∈  interval_a_b Λ f.a f.b) , f1.to_fun  ⟨ t , ht⟩  =  f.to_fun t ) ),
  exact seg_reparam_sub Λ X f ⟨ f.a , a_in_interval_a_b Λ f.a f.b f.h ⟩  tz tz.prop.1, 
  cases hsub1 with f1 hf1, cases hf1 with hf1a hf1b, cases hf1b with hf1b hf1, 
 
  have hsub2: ∃ f2 : segment_map Λ X, ( f2.a = (tz:Λ) ∧ f2.b = f.b ∧ (∀ (t : interval_a_b Λ f.a f.b)
           (ht : (t:Λ) ∈ interval_a_b Λ f2.a f2.b) (h1 : (f2.a:Λ) ∈  interval_a_b Λ f.a f.b)
           (h2 : (f2.b:Λ) ∈  interval_a_b Λ f.a f.b) , f2.to_fun  ⟨ t , ht⟩  =  f.to_fun t ) ),
  exact seg_reparam_sub Λ X f  tz ⟨ f.b , b_in_interval_a_b Λ f.a f.b f.h ⟩  tz.prop.2,  
  cases hsub2 with f2 hf2, cases hf2 with hf2a hf2b, cases hf2b with hf2b hf2,  
  
  have hf1ainf1 : f1.a ∈ interval_a_b Λ f1.a f1.b, exact a_in_interval_a_b Λ f1.a f1.b f1.h,
  have hf1ainf : f1.a ∈ interval_a_b Λ f.a f.b, rw hf1a, exact a_in_interval_a_b Λ f.a f.b f.h,
  have hfainf1 : f.a ∈ interval_a_b Λ f1.a f1.b, rw ← hf1a, exact hf1ainf1, 
  have hf1binf : f1.b ∈ interval_a_b Λ f.a f.b, rw hf1b, exact tz.prop,
  have hf1binf1 : f1.b ∈ interval_a_b Λ f1.a f1.b, exact b_in_interval_a_b Λ f1.a f1.b f1.h, 
  have hf2ainf : f2.a ∈ interval_a_b Λ f.a f.b, rw hf2a, exact tz.prop, 
  have hf2ainf2 : f2.a ∈ interval_a_b Λ f2.a f2.b, exact a_in_interval_a_b Λ f2.a f2.b f2.h, 
  have hf2binf : f2.b ∈ interval_a_b Λ f.a f.b, rw hf2b, exact b_in_interval f,     
  have hf2binf2 : f2.b ∈ interval_a_b Λ f2.a f2.b, exact b_in_interval f2, --rw hf2b,  
  have hfbinf2 : f.b ∈ interval_a_b Λ f2.a f2.b, rw ←  hf2b, exact hf2binf2,  

  -- our goal is to prove that f1 and g or f2 and g intersect only in z. We will collect some assumptions
  -- and write the statement a bit later, to keep the tactic view a bit cleaner.
  have h_1 : f1.p = f.p, 
  rw ← f.to_p, rw ← f1.to_p, 
  specialize hf1 ⟨ f.a , a_in_interval_a_b Λ f.a f.b f.h⟩ _, 
  rw hf1a at hf1ainf1,  rw hf1a, exact hf1ainf1, 
  have temp : (⟨ f1.a , hf1ainf1⟩ : interval_a_b Λ f1.a f1.b) = ⟨ f.a , hfainf1 ⟩ , exact subtype.eq hf1a,
  rw temp, apply hf1, exact hf1ainf, exact hf1binf, 

  have h_2 : f1.q = z, 
  rw ← f1.to_q, rw ← htz,  --rw ← hf1b,  
  specialize hf1 ⟨ f1.b , hf1binf⟩ _ , exact hf1binf1, 
  have temp :  (⟨ f1.b , hf1binf⟩:interval_a_b Λ f.a f.b) = tz , exact subtype.eq hf1b,
  rw ← temp, apply hf1, exact hf1ainf, exact hf1binf,  

  have h_3 : f2.p = z,
  rw ← f2.to_p, rw ← htz,
  specialize hf2 ⟨ f2.a, hf2ainf⟩ _ , exact hf2ainf2,
  have temp : (⟨ f2.a , hf2ainf⟩ : interval_a_b Λ f.a f.b ) = tz, exact subtype.eq hf2a, 
  rw ← temp, apply hf2, exact hf2ainf, exact hf2binf,

  have h_4 : f2.q = f.q,
  rw ← f.to_q, rw ← f2.to_q, 
  specialize hf2 ⟨ f.b , b_in_interval_a_b Λ f.a f.b f.h⟩ _, exact hfbinf2, 
  have temp : (⟨ f2.b , hf2binf2⟩ : interval_a_b Λ f2.a f2.b) = ⟨ f.b , hfbinf2 ⟩ , exact subtype.eq hf2b, 
  rw temp, apply hf2, exact hf2ainf, exact hf2binf,  

  have hintersect : segment Λ X f1 ∩ segment Λ X g = {z} ∨ segment Λ X f2 ∩ segment Λ X g = {z}, 

  have h_5 : f.p = f.p, refl,
  have h_6 : f.q = f.q, refl, 
  have h_9 : segment Λ X f1 ∪ segment Λ X f2 = segment Λ X f,
  ext, split,
  intro xinunion,
  cases xinunion with xinf1 xinf2,
  -- first x in f1
  have htx : ∃ t : interval_a_b Λ f1.a f1.b, f1.to_fun t = x, exact seg_exists_z Λ X f1 ⟨ x, xinf1⟩ ,
  cases htx with tx htx,
  have htxinf : (tx:Λ) ∈ interval_a_b Λ f.a f.b, cases tx.prop with tx1 tx2, split, 
  rw ← hf1a, exact tx1,   
  cases tz.prop with htz1 htz2, rw ← hf1b at htz2, exact le_trans tx2 htz2, 
  rw ← htx, 
  have transl : f1.to_fun tx = f.to_fun ⟨ tx , htxinf ⟩, 
  specialize hf1 ⟨ tx , htxinf ⟩ _ , exact tx.prop,  
  have temp : (⟨ (⟨ (tx:Λ) , htxinf ⟩: interval_a_b Λ f.a f.b) , tx.prop ⟩  : interval_a_b Λ f1.a f1.b)
                   = tx ,  
  apply subtype.eq, refl,  rw temp at hf1,   
  apply hf1, exact hf1ainf, exact hf1binf, -- proved transl here
  rw transl, 
  have trans : ∃ t : interval_a_b Λ f.a f.b ,  f.to_fun t = f.to_fun ⟨ (tx:Λ) , htxinf⟩,  
  use ⟨ (tx:Λ) , htxinf⟩,  exact trans,  
  -- now x in f2
  have htx : ∃ t : interval_a_b Λ f2.a f2.b, f2.to_fun t = x, exact seg_exists_z Λ X f2 ⟨ x, xinf2⟩ ,
  cases htx with tx htx,
  have htxinf : (tx:Λ) ∈ interval_a_b Λ f.a f.b, cases tx.prop with tx1 tx2, split,   
  cases tz.prop with htz1 htz2,  rw ← hf2a at htz1,  exact le_trans htz1 tx1 ,     
  rw ← hf2b,  exact tx2,    
  rw ← htx, 
  have transl : f2.to_fun tx = f.to_fun ⟨ tx , htxinf ⟩, 
  specialize hf2 ⟨ tx , htxinf ⟩ _ , exact tx.prop,  
  have temp : (⟨ (⟨ (tx:Λ) , htxinf ⟩: interval_a_b Λ f.a f.b) , tx.prop ⟩  : interval_a_b Λ f2.a f2.b)
                   = tx ,  
  apply subtype.eq, refl,  rw temp at hf2,   
  apply hf2, exact hf2ainf, exact hf2binf, -- proved transl here
  rw transl, 
  have trans : ∃ t : interval_a_b Λ f.a f.b ,  f.to_fun t = f.to_fun ⟨ (tx:Λ) , htxinf⟩,  
  use ⟨ (tx:Λ) , htxinf⟩,  exact trans,  
  -- now other implication
  intro xinf, 
  cases xinf with tx htx,
  by_cases (tx:Λ) ≤ tz,
  left, -- tx ≤ tz
  have htxinf1 : (tx:Λ) ∈ interval_a_b Λ f1.a f1.b , 
  split,
  cases tx.prop with htx1 htx2,
  rw hf1a,  exact htx1,
  rw hf1b,  exact h, -- we proved htxinf1
  use ⟨ tx , htxinf1  ⟩ ,
  rw ← htx, 
  apply hf1, exact hf1ainf, exact hf1binf, 
  -- now tz ≤ tx
  right, 
  have h' : (tz:Λ) < tx, exact not_le.mp h,  
  have h : (tz:Λ) ≤ tx,
  exact le_of_lt h',   
  have htxinf2 : (tx:Λ) ∈ interval_a_b Λ f2.a f2.b , 
  split,   
  rw hf2a,  exact h, 
  cases tx.prop with htx1 htx2, 
  rw hf2b,  exact htx2,  -- we proved htxinf2
  use ⟨ tx , htxinf2  ⟩ ,
  rw ← htx, 
  apply hf2, exact hf2ainf, exact hf2binf, -- we proved h_9
  -- we can now prove hintersect
  exact segments_intersect_once Λ X f.p f.q z p f1 f2 f g h_1 h_2 h_3 h_4 h_5 h_6 hgp hgq h_9, 

  cases hintersect with hP hQ,
  -- we prove it first for hP : h = f1 ∪ g
  have hh : ∃ h : segment_map Λ X, segment Λ X h = segment Λ X f1 ∪ segment Λ X g ∧ h.p = f1.p ∧ h.q = g.q,
  specialize h2 f1 g,
  apply h2, use z, 
  split, 
  exact hP, split, exact h_2.symm, exact hgp.symm,  
  cases hh with h hhh,
  have dxp : dist Λ X f.p p = ((⟨ (tz:Λ) + f'.a -f.a , htz'⟩ : interval_a_b Λ f'.a f'.b) :Λ) -f'.a, 
  rw hh1, 
  exact dist_p_ft_in_seg Λ X f' ⟨ (tz:Λ) + f'.a - f.a , htz'⟩,    
  have dxz : dist Λ X f.p z = (tz:Λ) - f.a,
  rw ← htz, 
  exact dist_p_ft_in_seg Λ X f tz,  
  have deqd : dist Λ X f.p z = dist Λ X f.p p,
  have temp : ((⟨ (tz:Λ) + f'.a -f.a , htz'⟩ : interval_a_b Λ f'.a f'.b) :Λ) -f'.a = (tz:Λ) - f.a,
  have temp1 : ((⟨ (tz:Λ) + f'.a -f.a , htz'⟩ : interval_a_b Λ f'.a f'.b) :Λ) = (tz:Λ) + f'.a - f.a, refl,
  rw temp1,  abel, -- this proves temp 
  rw ← dxp at temp, rw ← dxz at temp,  exact temp.symm,  
  
  cases hhh with segeq hhh, cases hhh with ha hb,
  have hz1 : z ∈ segment Λ X h,
  rw segeq, right,
  rw ←  hgp, exact p_in_seg g,   
  have hz2 : p ∈ segment Λ X h,
  rw segeq, right,
  rw ←  hgq, exact q_in_seg g, 
  have deqd : dist Λ X h.p z = dist Λ X h.p p,
  rw ha, rw h_1, exact deqd, 

  have zeqp : z = p,
  exact seg_d_p_z_determines_z h z p hz1 hz2 deqd, 
  rw zeqp, 
  use ⟨↑tz + f'.a - f.a, htz'⟩, -- we have proved it for h = f1 ∪ g

  let f3 : segment_map Λ X := seg_reparam_inv f2,
  
  have hP3 : segment Λ X f2 ∩ segment Λ X g = segment Λ X f3 ∩ segment Λ X g,
  have seg23 : segment Λ X f2 = segment Λ X f3,
  exact reparam_inv_seg f2, 
  ext, split, 
  intro hx, cases hx with hx1 hx2,
  split,
  rw ← seg23, exact hx1,
  exact hx2,
  intro hx, cases hx with hx1 hx2,
  split,
  rw seg23, exact hx1,
  exact hx2, 
  have hP : segment Λ X f3 ∩ segment Λ X g = {z},
  rw ← hP3, exact hQ,
  -- now the situation should be analogous to f1
  have hh : ∃ h : segment_map Λ X, segment Λ X h = segment Λ X f3 ∪ segment Λ X g ∧ h.p = f3.p ∧ h.q = g.q,
  specialize h2 f3 g,
  apply h2, use z, 
  split,  
  exact hP, split, exact h_3.symm, exact hgp.symm,  
  cases hh with h hhh,
  have dyp : dist Λ X p f.q = f'.b - ((⟨ (tz:Λ) + f'.a -f.a , htz'⟩ : interval_a_b Λ f'.a f'.b) :Λ) ,
  rw hh2, 
  exact dist_ft_q_in_seg Λ X f' ⟨ (tz:Λ) + f'.a - f.a , htz'⟩,    
  have dyz : dist Λ X z f.q = f.b - (tz:Λ) ,
  rw ← htz, 
  exact dist_ft_q_in_seg Λ X f tz,   
  have deqd : dist Λ X z f.q = dist Λ X p f.q,
  have temp : f'.b - ((⟨ (tz:Λ) + f'.a -f.a , htz'⟩ : interval_a_b Λ f'.a f'.b) :Λ)  = f.b - (tz:Λ),
  have temp1 : ((⟨ (tz:Λ) + f'.a -f.a , htz'⟩ : interval_a_b Λ f'.a f'.b) :Λ) = (tz:Λ) + f'.a - f.a, refl,
  rw temp1,  
  have dtot : f'.b - f'.a = f.b - f.a,
  rw ← (dist_p_q_in_seg Λ X f'),  rw ← (dist_p_q_in_seg Λ X f),  rw hh1 , rw hh2,  
  rw ← sub_eq_zero at dtot ⊢, abel at dtot ⊢, exact dtot, -- this proves temp 
  rw ← dyp at temp, rw ← dyz at temp,  exact temp.symm,  -- this proves deqd
  
  cases hhh with segeq hhh, cases hhh with ha hb,
  have hz1 : z ∈ segment Λ X h,
  rw segeq, right,
  rw ←  hgp, exact p_in_seg g,   
  have hz2 : p ∈ segment Λ X h,
  rw segeq, right,
  rw ←  hgq, exact q_in_seg g, 
  have deqd : dist Λ X z h.p = dist Λ X p h.p, 
  rw ha,
  have f23pq : f3.p = f2.q, refl,  
  rw f23pq, rw h_4, exact deqd,  
  have real_deqd : dist Λ X h.p z = dist Λ X h.p p,
  rw (dist_sym Λ X h.p z), rw (dist_sym Λ X h.p p), exact deqd, 

  have zeqp : z = p,
  exact seg_d_p_z_determines_z h z p hz1 hz2 real_deqd, 
  rw zeqp, 
  use ⟨↑tz + f'.a - f.a, htz'⟩,  -- we have proved it for h = f2 ∪ g

  -- we have shown that if z ∈ seg f, then z ∈ seg f' ! 
     
end

-- This is Lemma 3.6 in Chiswel [Chi] or Lemma 1 in [paper], 
-- the main proof consists of the previous lemma axioms_1_2_imply_unique_1_f_f'
lemma axioms_1_2_imply_unique_1 (Λ  : Type*) [linear_ordered_add_comm_group Λ] (X:Type*)[lambda_metric_space Λ X]
        : axiom_1 Λ X ∧ axiom_2 Λ X → axiom_unique_1 Λ X :=
begin
  intro h,
  intro f, intro f', intro hh, 
  have i1 :  segment Λ X f ⊆ segment Λ X f',
  apply (axioms_1_2_imply_unique_1_f_f' Λ X f f' hh), 
  exact h, 
  have i2 :  segment Λ X f' ⊆ segment Λ X f,
  have hh' : f'.p = f.p ∧ f'.q = f.q,
  cases hh with hh1 hh2,
  split,
  exact hh1.symm, exact hh2.symm,
  apply (axioms_1_2_imply_unique_1_f_f' Λ X f' f hh'), 
  exact h,     
  exact subset_antisymm i2 i1, 
end

end algebra.order.group
