import Mathlib.GroupTheory.Coxeter.Bruhat
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Algebra.Ring.MinimalAxioms

variable {B : Type}
variable {W : Type} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable {l : List B} {t : W}

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length
local prefix:100 "ris" => cs.rightInvSeq
local prefix:100 "lis" => cs.leftInvSeq

-- set_option maxHeartbeats 40000

namespace CoxeterSystem

abbrev Hecke := cs.Group →₀ (LaurentPolynomial ℤ)

end CoxeterSystem

namespace Hecke

open CoxeterSystem Bruhat LaurentPolynomial

open Classical (choose choose_spec)

-- instance : Module (LaurentPolynomial ℤ) cs.Hecke := sorry

local notation : max "End_ε" => Module.End (LaurentPolynomial ℤ) cs.Hecke

noncomputable instance : Ring End_ε := Module.End.ring

noncomputable def T : cs.Group → cs.Hecke := fun w => Finsupp.single w 1

#synth Module (LaurentPolynomial ℤ) cs.Hecke

local notation : max "q" => @LaurentPolynomial.T ℤ _ (1)

local notation : max "q⁻¹" => @LaurentPolynomial.T ℤ _ (-1)
local notation : max "T₁" => T cs 1


--trans
lemma cons_reduced {l : List B} {i : B} (hl : cs.IsReduced l) (h : ℓ (π l) < ℓ (s i * π l)) :
    cs.IsReduced ([i] ++ l) := by
  simp [IsReduced]
  rcases cs.length_simple_mul (π l) i with hlt | hgt
  · rwa [←hl]
  · omega

noncomputable section Hecke

instance : One (cs.Hecke) where
  one := T₁

lemma one_def : 1 = T₁ := rfl

@[simp]
lemma one_apply : (1 : cs.Hecke) 1 = 1 := by simp [one_def, T]

@[simp]
lemma T_apply (w : cs.Group) : (T cs w) w = 1 := by simp [T]

instance : Basis W (LaurentPolynomial ℤ) cs.Hecke := Finsupp.basisSingleOne

lemma T_repr (h : cs.Hecke) : h = h.sum fun w r => r • T cs w := by
  rw [←Finsupp.sum_single h]
  simp [T]

section HeckeMul

def simple_mul_T (i : B) (w : cs.Group) :=
  ite (ℓ w < ℓ (s i * w)) (T cs (s i * w)) ((q-1) • T cs w + q • T cs (s i * w))

def simple_mul (i : B) (h : cs.Hecke) : cs.Hecke :=
  finsum (fun w:cs.Group => h w • simple_mul_T cs i w)

lemma simple_mul_T₁ (i : B) : simple_mul_T cs i 1 = T cs (s i) := by simp [simple_mul_T]

lemma finsupp_smul (x : cs.Hecke) (i : B) :
    (Function.support fun w ↦ x w • simple_mul_T cs i w).Finite := by
  suffices (Function.support fun w ↦ x w • simple_mul_T cs i w) ⊆ x.support by
    apply Set.Finite.subset (by simp) this
  simp [not_imp_not]
  intro w hw
  simp [hw]

open Classical in
@[simp]
lemma simple_mul_one (i : B) : simple_mul cs i 1 = T cs (s i) := by
  simp [simple_mul]
  suffices ∑ᶠ (w : cs.Group), T₁ w • simple_mul_T cs i w = T₁ 1 • simple_mul_T cs i 1 by
    simp [← one_def] at this
    simp [this, simple_mul_T₁]
  apply finsum_eq_single
  simp [T, Finsupp.single_apply]
  tauto

lemma simple_mul_smul (r : ℤ[T;T⁻¹]) (i : B) (h : cs.Hecke) :
    simple_mul cs i (r • h) = r • simple_mul cs i h := by
  simp [simple_mul]
  rw [smul_finsum' _ (finsupp_smul cs h i)]
  simp_rw [smul_smul]

lemma simple_mul_distrib (i : B) (h₁ h₂ : cs.Hecke) :
    simple_mul cs i (h₁ + h₂) = simple_mul cs i h₁ + simple_mul cs i h₂ := by
  simp [simple_mul, add_smul]
  rw [finsum_add_distrib (finsupp_smul cs h₁ i) ((finsupp_smul cs h₂ i))]

open Classical in
lemma simple_mul_sq (i : B) : simple_mul cs i (T cs (s i)) = (q - 1) • T cs (s i) + q • 1 := by
  nth_rw 1 [simple_mul]
  suffices ∑ᶠ (u : cs.Group), (T cs (s i)) u • simple_mul_T cs i u =
    (T cs (s i)) (s i) • simple_mul_T cs i (s i) by
      nth_rw 1 [this, T]
      simp [Finsupp.single_apply, simple_mul_T, one_def]
  apply finsum_eq_single
  simp [T, Finsupp.single_apply]
  exact fun x h1 h2 => False.elim <| h1 h2.symm

open Classical in
lemma simple_mul_of_lt {i : B} {w : cs.Group} (hlt : ℓ w < ℓ (s i * w)) :
    simple_mul cs i (T cs w) = T cs (cs.simple i * w) := by
  simp [simple_mul]
  suffices ∑ᶠ (u : cs.Group), (T cs w) u • simple_mul_T cs i u =
      (T cs w) w • simple_mul_T cs i w by
    nth_rw 1 [this, T]
    simp [Finsupp.single_apply, simple_mul_T]
    intro
    linarith
  apply finsum_eq_single
  simp [T, Finsupp.single_apply]
  exact fun x h1 h2 => False.elim <| h1 h2.symm

open Classical in
lemma simple_mul_of_gt {i : B} {w : cs.Group} (hlt : ℓ (s i * w) < ℓ w) :
    simple_mul cs i (T cs w) = (q-1) • T cs w + q • T cs (s i * w) := by
  simp [simple_mul]
  suffices ∑ᶠ (u : cs.Group), (T cs w) u • simple_mul_T cs i u =
      (T cs w) w • simple_mul_T cs i w by
    nth_rw 1 [this, T]
    simp [Finsupp.single_apply, simple_mul_T]
    intro
    linarith
  apply finsum_eq_single
  simp [T, Finsupp.single_apply]
  exact fun x h1 h2 => False.elim <| h1 h2.symm

def T_mul_simple (w : cs.Group) (i : B) :=
  ite (ℓ w < ℓ (w * s i)) (T cs (w * s i)) ((q-1) • T cs w + q • T cs (w * s i))

def mul_simple (h : cs.Hecke) (i : B) : cs.Hecke :=
  finsum (fun w:cs.Group => h w • T_mul_simple cs w i)

lemma finsupp_muls (x : cs.Hecke) (i : B) :
    (Function.support fun w ↦ x w • T_mul_simple cs w i).Finite := by
  suffices (Function.support fun w ↦ x w • T_mul_simple cs w i) ⊆ x.support by
    apply Set.Finite.subset (by simp) this
  simp [not_imp_not]
  intro w hw
  simp [hw]

lemma mul_simple_smul (r : ℤ[T;T⁻¹]) (h : cs.Hecke) (j : B) :
    mul_simple cs (r • h) j = r • mul_simple cs h j := by
  simp [mul_simple]
  rw [smul_finsum' _ (finsupp_muls cs h j)]
  simp_rw [smul_smul]

lemma mul_simple_distrib (h₁ h₂ : cs.Hecke) (j : B) :
    mul_simple cs (h₁ + h₂) j = mul_simple cs h₁ j + mul_simple cs h₂ j := by
  simp [mul_simple, add_smul]
  rw [finsum_add_distrib (finsupp_muls cs h₁ j) (finsupp_muls cs h₂ j)]

open Classical in
lemma mul_simple_of_lt {i : B} {w : cs.Group} (h : ℓ w < ℓ (w * s i)) :
    mul_simple cs (T cs w) i = T cs (w * s i) := by
  simp [mul_simple]
  suffices ∑ᶠ (u : cs.Group), (T cs w) u • T_mul_simple cs u i =
      (T cs w) w • T_mul_simple cs w i by
    nth_rw 1 [this, T]
    simp [Finsupp.single_apply, T_mul_simple]
    intro
    linarith
  apply finsum_eq_single
  simp [T, Finsupp.single_apply]
  exact fun x h1 h2 => False.elim <| h1 h2.symm

open Classical in
lemma mul_simple_of_gt {i : B} {w : cs.Group} (h : ℓ (w * s i) < ℓ w) :
    mul_simple cs (T cs w) i = (q-1) • T cs w + q • T cs (w * s i) := by
  simp [mul_simple]
  suffices ∑ᶠ (u : cs.Group), (T cs w) u • T_mul_simple cs u i =
      (T cs w) w • T_mul_simple cs w i by
    nth_rw 1 [this, T]
    simp [Finsupp.single_apply, T_mul_simple]
    intro
    linarith
  apply finsum_eq_single
  simp [T, Finsupp.single_apply]
  exact fun x h1 h2 => False.elim <| h1 h2.symm

end HeckeMul


def opl (i : B) : End_ε where
  toFun := fun h => simple_mul cs i h
  map_add' := by
    intro x y
    simp [simple_mul, add_smul]
    rw [finsum_add_distrib]
    all_goals apply finsupp_smul
  map_smul' := by
    intro r x
    simp [simple_mul, mul_smul]
    rw [smul_finsum']
    apply finsupp_smul

def opr (i : B) : End_ε where
  toFun := fun h => mul_simple cs h i
  map_add' := by
    intro x y
    simp [mul_simple, add_smul]
    rw [finsum_add_distrib]
    all_goals apply finsupp_muls
  map_smul' := by
    intro r x
    simp [mul_simple, mul_smul]
    rw [smul_finsum']
    apply finsupp_muls

lemma both_lt_of_length_lt_iwj {i j : B} {w : cs.Group} (h : ℓ w < ℓ (s i * w * s j)) :
    ℓ w + 1 = ℓ (s i * w) ∧ ℓ w + 1 = ℓ (w * s j) := by
  constructor
  · rcases cs.length_simple_mul w i with h1 | h1
    · exact h1.symm
    · rcases cs.length_mul_simple (s i * w) j with h2 | h2 <;> omega
  · rcases cs.length_mul_simple w j with h1 | h1
    · exact h1.symm
    · rcases cs.length_simple_mul (w * s j) i with h2 | h2 <;>
      simp [←mul_assoc] at h2 <;> omega

lemma both_gt_of_length_gt_iwj {i j : B} {w : cs.Group} (h : ℓ (s i * w * s j) < ℓ w) :
    ℓ w = ℓ (s i * w) + 1 ∧ ℓ w = ℓ (w * s j) + 1 := by
  constructor
  · rcases cs.length_simple_mul w i with h1 | h1
    · rcases cs.length_mul_simple (s i * w) j with h2 | h2 <;> omega
    · exact h1.symm
  · rcases cs.length_mul_simple w j with h1 | h1
    · rcases cs.length_simple_mul (w * s j) i with h2 | h2 <;>
      simp [←mul_assoc] at h2 <;> omega
    · exact h1.symm

private lemma length_iwj_of_both_lt {i j : B} {w : cs.Group} (hi : ℓ w + 1 = ℓ (s i * w))
    (hj : ℓ w + 1 = ℓ (w * s j)) : ℓ w < ℓ (s i * w * s j) ∨ ℓ w = ℓ (s i * w * s j) := by
  by_contra!
  have h1 : ℓ (s i * w * s j) < ℓ w := by omega
  replace h1 := both_gt_of_length_gt_iwj cs h1
  omega

private lemma length_iwj_of_both_gt {i j : B} {w : cs.Group} (hi : ℓ (s i * w) + 1 = ℓ w)
    (hj : ℓ (w * s j) + 1 = ℓ w) : ℓ (s i * w * s j) < ℓ w ∨ ℓ w = ℓ (s i * w * s j) := by
  by_contra!
  have h1 : ℓ w < ℓ (s i * w * s j) := by omega
  replace h1 := both_lt_of_length_lt_iwj cs h1
  omega

private lemma length_iwj_of_lti_of_gtj {i j : B} {w : cs.Group} (hi : ℓ w + 1 = ℓ (s i * w))
    (hj : ℓ (w * s j) + 1 = ℓ w) : ℓ w = ℓ (s i * w * s j) := by
  by_contra!
  rcases ne_iff_lt_or_gt.1 this with hlt | hgt
  · replace hlt := both_lt_of_length_lt_iwj cs hlt; omega
  · replace hgt := both_gt_of_length_gt_iwj cs hgt; omega

private lemma length_iwj_of_gti_of_ltj {i j : B} {w : cs.Group} (hi : ℓ (s i * w) + 1 = ℓ w)
    (hj : ℓ w + 1 = ℓ (w * s j)) : ℓ w = ℓ (s i * w * s j) := by
  by_contra!
  rcases ne_iff_lt_or_gt.1 this with hlt | hgt
  · replace hlt := both_lt_of_length_lt_iwj cs hlt; omega
  · replace hgt := both_gt_of_length_gt_iwj cs hgt; omega

lemma length_iwj_eq_add_two_of_lt {i j : B} {w : cs.Group} (h : ℓ w < ℓ (s i * w * s j)) :
    ℓ (s i * w * s j) = ℓ w + 2 := by
  have h1 : ℓ (s i * w) = ℓ w + 1 := by
    rcases cs.length_simple_mul w i with h1 | h1
    · omega
    · rcases cs.length_mul_simple (s i * w) j with h2 | h2 <;> omega
  have h2 : ℓ (s i * w * s j) = ℓ (s i * w) + 1 := by
    rcases cs.length_mul_simple (s i * w) j with h2 | h2 <;> omega
  omega

lemma length_iwj_add_two_eq_of_gt {i j : B} {w : cs.Group} (h : ℓ (s i * w * s j) < ℓ w) :
    ℓ (s i * w * s j) + 2 = ℓ w := by
  have h1 : ℓ (s i * w) + 1 = ℓ w := by
    rcases cs.length_simple_mul w i with h1 | h1
    · rcases cs.length_mul_simple (s i * w) j with h2 | h2 <;> omega
    · omega
  have h2 : ℓ (s i * w * s j) + 1 = ℓ (s i * w) := by
    rcases cs.length_mul_simple (s i * w) j with h2 | h2 <;> omega
  omega

open Classical in
lemma smul_eq_muls_of_lt {i j : B} {w : cs.Group} (h1 : ℓ (s i * w * s j) = ℓ w)
    (h2 : ℓ (s i * w) = ℓ (w * s j)) (h3 : ℓ (s i * w) = ℓ w + 1) : s i * w = w * s j := by
  have h4 : ℓ (s i * w * s j) < ℓ (s i * w) := by omega
  have hl := choose_spec <| cs.exists_reduced_word w
  set l := choose <| cs.exists_reduced_word w
  let L := [i] ++ l
  have hL : cs.IsReduced ([i] ++ l) := by
    apply cons_reduced cs (by simp [IsReduced, ←hl.2]; exact hl.1.symm)
    simp [←hl.2]; omega
  have hL' : π ([i] ++ l) = s i * w := by simp [wordProd_cons, hl.2]
  simp [←hL'] at h4
  have h5 := StrongExchange'' cs (cs.isReflection_simple j) h4
  set idx := List.idxOf (s j) (cs.rightInvSeq (i :: l)) with hidx
  by_cases lnil : l = []
  · simp [lnil] at hl h5
    simp [hl.2, h5]
  · have h6 := (cs.rightInvSeq (i :: l)).getD_eq_getElem 1 (List.idxOf_lt_length h5)
    rw [List.getElem_idxOf] at h6
    by_cases idx0 : idx = 0
    · simp [←hidx, idx0] at h6
      simp [←h6, rightInvSeq, ←hl.2]
      group
    · have h8 : s i * w * s j = π ((i :: l).eraseIdx idx) := by
        rw [←h6, ←hL', ←cs.wordProd_mul_getD_rightInvSeq (i :: l) idx]
        simp [idx]
      rw [show idx = idx - 1 + 1 by omega,  List.eraseIdx_cons_succ] at h8
      simp [wordProd_cons, mul_assoc] at h8
      replace h8 : ℓ (w * s j) < ℓ w := by
        have := cs.length_wordProd_le (l.eraseIdx (idx - 1))
        have h9 : idx - 1 < l.length := by
          apply Nat.sub_lt_left_of_lt_add (by omega)
          convert List.idxOf_lt_length h5
          simp [length_rightInvSeq, add_comm]
        rw [List.length_eraseIdx_of_lt h9, hl.1, ←h8] at this
        exact Nat.lt_of_le_sub_one (hl.1 ▸ List.length_pos.2 lnil) this
      omega

lemma smul_eq_muls {i j : B} {w : cs.Group} (h1 : ℓ (s i * w * s j) = ℓ w)
    (h2 : ℓ (s i * w) = ℓ (w * s j)) : s i * w = w * s j := by
  rcases cs.length_simple_mul w i with hlt | hgt
  · exact smul_eq_muls_of_lt cs h1 h2 hlt
  · have : s i * (s i * w) = (s i * w) * s j :=
      smul_eq_muls_of_lt cs (w := s i * w) (by simp [h2]) (by simp [h1]) (by simp [hgt])
    simp only [mul_assoc] at this
    exact mul_left_cancel this

lemma opl_commute_opr : ∀ i j : B, LinearMap.comp (opr cs j) (opl cs i) =
    LinearMap.comp (opl cs i) (opr cs j) := by
  intro i j
  apply LinearMap.ext
  suffices ∀ w : cs.Group, (opr cs j ∘ₗ opl cs i) (T cs w) = (opl cs i ∘ₗ opr cs j) (T cs w) by
    intro x
    rw [T_repr cs x]
    simp only [Finsupp.sum, map_sum, map_smul, LinearMap.coe_comp, Function.comp_apply]
    simp at this
    simp_rw [this]
  intro w
  simp [opl, opr]
  rcases cs.length_simple_mul w i with lti | gti <;>
  rcases cs.length_mul_simple w j with ltj | gtj
  · rcases length_iwj_of_both_lt cs lti.symm ltj.symm with ltiwj | eqiwj
    · replace ltiwj : ℓ (s i * w * s j) = ℓ w + 2 := length_iwj_eq_add_two_of_lt cs ltiwj
      rw [simple_mul_of_lt, mul_simple_of_lt, mul_simple_of_lt, simple_mul_of_lt, mul_assoc]
      any_goals omega
      simp [←mul_assoc]; omega
    · rw [simple_mul_of_lt, mul_simple_of_gt, mul_simple_of_lt, simple_mul_of_gt,
        mul_assoc, smul_eq_muls]
      any_goals omega
      simp [←mul_assoc]; omega
  · have := length_iwj_of_lti_of_gtj cs lti.symm gtj
    rw [simple_mul_of_lt cs (by omega), mul_simple_of_gt cs (by omega),
      mul_simple_of_gt cs (by omega)]
    simp only [simple_mul_distrib, simple_mul_smul]
    rw [simple_mul_of_lt, simple_mul_of_lt, mul_assoc]
    any_goals omega
    simp [←mul_assoc]; omega
  · have := length_iwj_of_gti_of_ltj cs gti ltj.symm
    rw [simple_mul_of_gt cs (by omega), mul_simple_of_lt cs (by omega),
      simple_mul_of_gt cs (by simp [←mul_assoc]; omega)]
    simp only [mul_simple_distrib, mul_simple_smul]
    rw [mul_simple_of_lt cs (by omega), mul_simple_of_lt cs (by omega), mul_assoc]
  · rcases length_iwj_of_both_gt cs gti gtj with gtiwj | eqiwj
    · replace gtiwj : ℓ (s i * w * s j) + 2 = ℓ w := length_iwj_add_two_eq_of_gt cs gtiwj
      rw [simple_mul_of_gt cs (by omega), mul_simple_of_gt cs (by omega)]
      simp only [mul_simple_distrib, mul_simple_smul, simple_mul_distrib, simple_mul_smul]
      rw [mul_simple_of_gt cs (by omega), simple_mul_of_gt cs (by omega)]
      rw [mul_simple_of_gt cs (by omega), simple_mul_of_gt cs (by simp [←mul_assoc]; omega)]
      simp [smul_add, smul_smul]
      noncomm_ring
    · rw [simple_mul_of_gt cs (by omega), mul_simple_of_gt cs (by omega)]
      simp only [mul_simple_distrib, mul_simple_smul, simple_mul_distrib, simple_mul_smul]
      rw [mul_simple_of_gt cs (by omega), simple_mul_of_gt cs (by omega)]
      rw [mul_simple_of_lt cs (by omega), simple_mul_of_lt cs (by simp [←mul_assoc]; omega)]
      rw [mul_assoc, smul_eq_muls cs eqiwj.symm (by omega)]

def generator_set := opl cs '' (Set.univ)

def generator_set' := opr cs '' (Set.univ)

def subalg := Algebra.adjoin (LaurentPolynomial ℤ) (generator_set cs)

def subalg' := Algebra.adjoin (LaurentPolynomial ℤ) (generator_set' cs)

def alg_hom : subalg cs → cs.Hecke := fun f => f.1 T₁

def alg_hom' : subalg' cs → cs.Hecke := fun f => f.1 T₁

instance subalg.Algebra: Algebra (LaurentPolynomial ℤ) (subalg cs) :=
  Subalgebra.algebra (subalg cs)

instance subalg'.Algebra: Algebra (LaurentPolynomial ℤ) (subalg' cs) :=
  Subalgebra.algebra (subalg' cs)

lemma subalg_commute_subalg'_aux (f : subalg cs) (hf : f.1 ∈ generator_set cs) (g : subalg' cs) :
  f.1 ∘ g.1 = g.1 ∘ f.1 := by
    rcases hf with ⟨u, hu⟩
    rw [←hu.2]
    revert g
    simp [subalg']
    apply Algebra.adjoin_induction
    · intro g ⟨v, hv⟩
      rw [←hv.2, ←LinearMap.coe_comp, ←LinearMap.coe_comp, opl_commute_opr cs u v]
    · intro r
      ext
      simp
    · intro f1 f2 f1mem hf2mem hf1 hf2
      rw [←LinearMap.coe_comp, ←LinearMap.coe_comp] at hf1 hf2
      rw [←LinearMap.coe_comp, LinearMap.comp_add]
      ext
      simp [hf1, hf2]
    · intro f1 f2 f1mem f2mem hf1 hf2
      ext
      have h1 := congrFun hf1
      have h2 := congrFun hf2
      simp at h1 h2 ⊢
      rw [←h2, h1]

lemma subalg_commute_subalg' (f : subalg cs) (g : subalg' cs) : f.1 ∘ g.1 = g.1 ∘ f.1 := by
  revert f
  simp [subalg]
  apply Algebra.adjoin_induction
  · intro f hf
    apply subalg_commute_subalg'_aux cs ⟨f, Algebra.subset_adjoin hf⟩
    simp [hf]
  · intro r
    ext
    simp
  · intro f1 f2 f1mem f2mem hf1 hf2
    ext h
    have h1 := congrFun hf1
    have h2 := congrFun hf2
    simp at h1 h2 ⊢
    rw [h1, h2]
  · intro f1 f2 f1mem f2mem hf1 hf2
    ext h _ _
    have h1 := congrFun hf1
    have h2 := congrFun hf2
    simp at h1 h2 ⊢
    rw [h2, h1]

lemma T_subset_image_of_subalg' (w : cs.Group) : ∃ f, alg_hom' cs f = T cs w := by

  sorry

lemma alg_hom'_surj : Function.Surjective (alg_hom' cs) := by
  intro h
  simp [alg_hom']
  have := Basis.linearCombination_repr Finsupp.basisSingleOne h
  rw [Finsupp.linearCombination_apply] at this
  let preimage : cs.Group → subalg' cs :=
    fun w => Classical.choose <| T_subset_image_of_subalg' cs w
  have preimage_apply (w : cs.Group) : T cs w = alg_hom' cs (preimage w) := by
    simp [preimage]
    exact (Classical.choose_spec <| T_subset_image_of_subalg' cs w).symm
  use (Finsupp.basisSingleOne.repr h).sum fun i a ↦ a • preimage i
  constructor
  · simp
    apply Subalgebra.sum_mem
    intro x hx
    simp
    exact Subalgebra.smul_mem _ (by simp [preimage]) _
  · have h1 (i : cs.Group) : alg_hom' cs (preimage i) = (preimage i).1 T₁ := by simp [alg_hom']
    simp [← h1, ← preimage_apply]
    nth_rw 2 [← this]
    simp [T]

lemma inj_aux (f : subalg cs) (h : alg_hom cs f = 0) : f = 0 := by
  simp [alg_hom] at h
  have h1 : ∀ g : subalg' cs, (g.1 ∘ f.1) T₁ = 0 := by simp [h]
  have h2 : ∀ g : subalg' cs, (f.1 ∘ g.1) T₁ = 0 := by
    intro g
    rw [subalg_commute_subalg' cs f g]
    exact h1 g
  rw [←Subtype.val_inj]
  apply LinearMap.ext
  intro x
  simp at h2
  rcases alg_hom'_surj cs x with ⟨a, ha⟩
  specialize h2 a a.2
  simp [alg_hom'] at ha
  rw [ha] at h2
  simp [h2]

instance isLinearMap : IsLinearMap (LaurentPolynomial ℤ) (alg_hom cs) where
  map_add := by simp [alg_hom]
  map_smul := by simp [alg_hom]

lemma alg_hom_inj : Function.Injective (alg_hom cs) := by
  intro ⟨f,hf⟩  ⟨g, hg⟩ h
  simp [alg_hom] at h
  have h2 : ∀ {f : subalg cs}, f.1 1 = 0 → f = 0 := by
    intro f h1
    exact inj_aux cs f h1
  suffices f - g = 0 by
    have : f = g := eq_of_sub_eq_zero this
    simpa
  have h3 : (⟨f - g, Subalgebra.sub_mem (subalg cs) hf hg⟩ : subalg cs) = 0 :=
    h2 (by simp [one_def, h])
  simp [←Subalgebra.coe_eq_zero] at h3
  exact h3

lemma alg_hom_surj : Function.Surjective (alg_hom cs) := by sorry

lemma alg_hom_bijective : Function.Bijective (alg_hom cs) :=
  ⟨alg_hom_inj cs, alg_hom_surj cs⟩

def algEquiv : LinearEquiv (RingHom.id (LaurentPolynomial ℤ)) (subalg cs) cs.Hecke :=
  LinearEquiv.ofBijective ((isLinearMap cs).mk' (alg_hom cs) ) (alg_hom_bijective cs)

@[simp]
lemma alg_hom_apply_one : alg_hom cs 1 = 1 := by simp [one_def, alg_hom]

@[simp]
lemma algEquiv.invFun_apply_one : (algEquiv cs).invFun 1 = 1 := by
  simp [LinearEquiv.symm_apply_eq (algEquiv cs)]
  simp [algEquiv]

#exit
def HeckeMul : cs.Hecke → cs.Hecke → cs.Hecke :=
  fun x y => (algEquiv cs).toFun ((algEquiv cs).invFun x * (algEquiv cs).invFun y)

instance : Mul cs.Hecke where
  mul := HeckeMul cs

lemma mul_def (a b : cs.Hecke) : a * b = HeckeMul cs a b := rfl

lemma mul_zero (a : cs.Hecke) : a * 0 = 0 := by simp [HeckeMul, mul_def]

lemma zero_mul (a : cs.Hecke) : 0 * a = 0 := by simp [HeckeMul, mul_def]

lemma left_distrib (a b c : cs.Hecke) : a * (b + c) = a * b + a * c := by
  simp [HeckeMul, NonUnitalNonAssocSemiring.left_distrib, mul_def]

lemma right_distrib (a b c : cs.Hecke) : (a + b) * c = a * c + b * c := by
  simp [HeckeMul, NonUnitalNonAssocSemiring.right_distrib, mul_def]

lemma mul_assoc (a b c : cs.Hecke) : a * b * c = a * (b * c) := by
  simp [HeckeMul, _root_.mul_assoc, mul_def]

@[simp]
lemma one_mul (a : cs.Hecke) :  1 * a = a := by simp [mul_def, HeckeMul]

@[simp]
lemma mul_one (a : cs.Hecke) :  a * 1 = a := by simp [mul_def, HeckeMul]

instance : MulOneClass cs.Hecke where
  one_mul := one_mul cs
  mul_one := mul_one cs

instance : NonUnitalNonAssocSemiring cs.Hecke where
  mul_zero := mul_zero cs
  zero_mul := zero_mul cs
  left_distrib := left_distrib cs
  right_distrib := right_distrib cs

instance : NonUnitalNonAssocRing cs.Hecke where
  __ := inferInstanceAs (NonUnitalNonAssocSemiring cs.Hecke)
  zsmul := zsmulRec
  neg_add_cancel := by simp
  sub_eq_add_neg := by simp [SubNegMonoid.sub_eq_add_neg]

instance semiring : Semiring (cs.Hecke) where
  __ := inferInstanceAs (NonUnitalNonAssocRing cs.Hecke)
  __ := inferInstanceAs (MulOneClass cs.Hecke)
  mul_assoc := mul_assoc cs

lemma smul_assoc (r : LaurentPolynomial ℤ) (x y : cs.Hecke) :
  (r • x) * y = r • (x * y) := by simp [mul_def, HeckeMul]

lemma smul_comm (r : LaurentPolynomial ℤ) (x y : cs.Hecke) :
  HeckeMul cs x (r • y) = r • (HeckeMul cs x y) := by simp [HeckeMul]

instance : Algebra (LaurentPolynomial ℤ) cs.Hecke :=
  Algebra.ofModule (smul_assoc cs) (smul_comm cs)


end Hecke

abbrev Coxeter.wf : WellFoundedRelation cs.Group := measure cs.length

@[simp]
lemma rel_iff_length_lt (u v : cs.Group) : (Coxeter.wf cs).rel u v ↔ ℓ u < ℓ v := by rfl

noncomputable section HeckeMul

noncomputable def choose_reduced_word (w : cs.Group) : List B :=
  Classical.choose <| CoxeterSystem.exists_reduced_word cs w

lemma algEquiv.invFun_apply_T_simple (i : B) : (algEquiv cs).symm (T cs (s i)) =
  ⟨opl cs i, Algebra.subset_adjoin (by simp [generator_set])⟩ := by
    apply (algEquiv cs).injective
    simp [algEquiv, alg_hom, opl, ←one_def, simple_mul_one]

lemma T_simple_sq (i : B) : T cs (s i) * T cs (s i) = (q - 1) • T cs (s i) + q • T₁ := by
  simp [mul_def, HeckeMul]
  nth_rw 1 [algEquiv]
  simp [mul_def, LinearEquiv.apply_symm_apply]
  simp [alg_hom, algEquiv.invFun_apply_T_simple, opl, ←one_def, simple_mul_one, simple_mul_sq]

lemma TsT_of_lt {i : B} {w : cs.Group} (hlt : ℓ w < ℓ (s i * w)) :
  T cs (s i) * T cs w = T cs (s i * w) := by
    simp [mul_def, HeckeMul]
    nth_rw 1 [algEquiv]
    simp [alg_hom, algEquiv.invFun_apply_T_simple]
    rw [←alg_hom]
    have h1  (f : subalg cs) : alg_hom cs f = algEquiv cs f := by
      simp only [alg_hom, algEquiv, LinearEquiv.ofBijective_apply, IsLinearMap.mk'_apply]
    rw [h1]
    simp [opl, simple_mul_of_lt cs i w hlt]

lemma TsT_of_gt {i : B} {w : cs.Group} (hlt : ℓ (s i * w) < ℓ w) :
  T cs (s i) * T cs w = (q - 1) •  T cs w + q • T cs (s i * w) := by
    have h1 : ℓ (s i * w) < ℓ (s i * (s i * w)) := by simp [hlt]
    have h2 := TsT_of_lt cs h1
    nth_rw 1 [← cs.simple_mul_simple_cancel_left i (w := w), ←h2, ←mul_assoc,T_simple_sq cs i]
    simp [right_distrib, ←one_def, h2]

--trans
lemma length_smuls_lt_length_muls {i j: B} {w : cs.Group} (hj : ℓ w < ℓ (w * s j))
    (hi : ℓ (s i * w) < ℓ w) : ℓ (s i * w * s j) < ℓ (w * s j) := by
  have h : ℓ (s i * w) + 1 = ℓ w := by
    rcases cs.length_simple_mul w i with hgt | hlt <;> omega
  have h' : ℓ (s i * w * s j) ≤ ℓ (w) := by
    rcases cs.length_mul_simple (s i * w) j with hgt | hlt <;> omega
  linarith

lemma length_smuls_gt_length_smul {i j: B} {w : cs.Group} (hj : ℓ w < ℓ (w * s j))
    (hi : ℓ (s i * w) < ℓ w) : ℓ (s i * w) < ℓ (s i * w * s j) := by
  have h : ℓ (w * s j) = ℓ w + 1 := by
    rcases cs.length_mul_simple w j with hgt | hlt <;> linarith
  have h' : ℓ (w) ≤  ℓ (s i * w * s j) := by
    rw [_root_.mul_assoc]
    rcases cs.length_simple_mul (w * s j) i with hgt | hlt  <;> omega
  linarith

lemma TTs_of_lt {i : B} {w : cs.Group} (hlt : ℓ w < ℓ (w * s i)) :
    T cs w * T cs (s i) = T cs (w * s i) := by
  induction w using WellFounded.induction
  · exact (Coxeter.wf cs).wf
  · rename_i w ih
    simp at ih
    by_cases w1 : w = 1
    · simp [w1, ←one_def]
    · obtain ⟨j, hj⟩ := cs.exists_leftDescent_of_ne_one w1
      rw [←cs.simple_mul_simple_cancel_left (w:=w) j]
      have h1 : ℓ (s j * w) < ℓ (s j * (s j * w)) := by simpa
      have h2 : ℓ (s j * w) < ℓ (s j * w * s i) := length_smuls_gt_length_smul cs hlt hj
      have h3 : ℓ (s j * w * s i) < ℓ (s j * (s j * w * s i)) := by
        simp [show s j * (s j * w * s i) = s j * s j * w * s i by noncomm_ring]
        exact length_smuls_lt_length_muls cs hlt hj
      rw [←TsT_of_lt cs h1, mul_assoc, ih (s j * w) hj h2, TsT_of_lt cs h3]
      congr 1
      noncomm_ring

lemma TTs_of_gt {i : B} {w : cs.Group} (hlt : ℓ (w * s i) < ℓ w) :
    T cs w * T cs (s i) = (q - 1) • T cs w + q • T cs (w * s i):= by
  have h1 : ℓ (w * s i) < ℓ (w * s i * s i) := by simpa
  nth_rw 1 [← cs.simple_mul_simple_cancel_right i (w := w), ←TTs_of_lt cs h1, mul_assoc]
  simp [T_simple_sq, left_distrib, TTs_of_lt cs h1, ←one_def]

end HeckeMul

noncomputable section HeckeInv

def T_simple (i : B) := T cs (s i)

def T_simple_inv (i : B) := q⁻¹ • T cs (s i) - (1 - q⁻¹) • 1

local notation : max "Tₛ" => T_simple cs

lemma isLeftInv (i : B) : T_simple_inv cs i * T cs (s i) = 1 := by
  simp [T_simple_inv, sub_mul, T_simple_sq cs i]
  rw [smul_smul, smul_smul, mul_sub, ←LaurentPolynomial.T_add]
  simp [one_def]

lemma isRightInv (i : B) : T cs (s i) * T_simple_inv cs i = 1 := by
  simp [T_simple_inv, mul_sub, T_simple_sq cs i]
  rw [smul_smul, smul_smul, mul_sub, ←LaurentPolynomial.T_add]
  simp [one_def]

def Tprod (l : List B) : cs.Hecke := (l.map Tₛ).prod

lemma Tprod_hom_of_reduced (l : List B) (h : cs.IsReduced l) : Tprod cs l = T cs (π l) := by
  induction' l with head tail ih
  · simp [Tprod, one_def]
  · simp [Tprod, wordProd_cons] at ih ⊢
    have h1 : cs.IsReduced tail := CoxeterSystem.IsReduced.drop h 1
    rw [←TsT_of_lt, ih h1]
    · simp [T_simple]
    · rw [IsReduced] at h h1
      simp [h, h1, ← wordProd_cons]

lemma Tprod_eq_of_reduced_of_wordProd_eq {l₁ l₂ : List B} (h1 : cs.IsReduced l₁)
    (h2 : cs.IsReduced l₂) (h : π l₁ = π l₂) : Tprod cs l₁ = Tprod cs l₂ := by
  simp [Tprod_hom_of_reduced cs l₁ h1, Tprod_hom_of_reduced cs l₂ h2, h]

def inv_aux (l : List B) := ((l.reverse).map (T_simple_inv cs)).prod

def Tinv (w : cs.Group) : cs.Hecke :=
  let l := Classical.choose <| cs.exists_reduced_word w;
  inv_aux cs l

lemma Tprod_mul_inv_aux_eq_one (l : List B) : Tprod cs l * inv_aux cs l = 1 := by
  simp [Tprod, inv_aux]
  induction l with
  | nil => simp
  | cons i l ih => simp [←mul_assoc]; nth_rw 2 [mul_assoc]; simp [ih, T_simple, isRightInv]

lemma inv_aux_mul_Tprod_eq_one (l : List B) : inv_aux cs l * Tprod cs l = 1 := by
  simp [Tprod, inv_aux]
  induction l with
  | nil => simp
  | cons i l ih => simp [←mul_assoc]; nth_rw 2 [mul_assoc]; simp [ih, T_simple, isLeftInv]

lemma inv_aux_reduced_word_eq {l₁ l₂ : List B} (h1 : cs.IsReduced l₁) (h2 : cs.IsReduced l₂)
    (h : π l₁ = π l₂) : inv_aux cs l₁ = inv_aux cs l₂ := by
  suffices inv_aux cs l₁ * Tprod cs l₂ = 1 by
    apply_fun (· * inv_aux cs l₂) at this
    simpa [mul_assoc, Tprod_mul_inv_aux_eq_one] using this
  simp [←Tprod_eq_of_reduced_of_wordProd_eq cs h1 h2 h, inv_aux_mul_Tprod_eq_one]

lemma Tinv_eq_inv_aux_reduced_word {w : cs.Group} {l : List B} (hl : cs.IsReduced l)
    (h : π l = w) : Tinv cs w = inv_aux cs l := by
  simp [Tinv]
  have := (choose_spec <|cs.exists_reduced_word w)
  apply inv_aux_reduced_word_eq cs _ hl (by simp [h, ←this.2])
  simp [IsReduced, ←this.2, this.1]

local notation : max "T⁻¹" => Tinv cs

@[simp]
lemma Tinv_one : T⁻¹ 1 = 1 := by
  have : (Classical.choose <| cs.exists_reduced_word 1) = []:= by
    set l  := Classical.choose <| cs.exists_reduced_word 1 with ll
    set hl := Classical.choose_spec <| cs.exists_reduced_word 1
    rw [←ll, length_one] at hl
    simp at hl
    exact hl.1
  rw [Tinv, this]
  simp [inv_aux]

lemma Tinv_simple (i : B) : T⁻¹ (s i) = T_simple_inv cs i := by
  have := Tinv_eq_inv_aux_reduced_word cs (singletonIsReduced cs rfl) (show π [i] = s i by simp)
  simp [this, inv_aux]

lemma Tinv_simple' (i : B) : T⁻¹ (s i) = q⁻¹ • T cs (s i) - (1 - q⁻¹) • 1 := by
  simp [Tinv_simple, T_simple_inv]

lemma inv_aux_cons (i : B) (l : List B) :
    inv_aux cs (i :: l) = inv_aux cs l * T_simple_inv cs i := by simp [inv_aux]

-- key : use the lemma `Tinv_eq_inv_aux_reduced_word`
lemma Tinv_isLeftInv (w : cs.Group) : T⁻¹ w * T cs w = 1 := by
  induction' w using WellFounded.induction with w ih
  · exact (Coxeter.wf cs).wf
  · simp only [rel_iff_length_lt] at ih
    by_cases w1 : w = 1
    · simp [w1, ←one_def]
    · obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one w1
      rw [←cs.simple_mul_simple_cancel_left (w:=w) i]
      obtain ⟨l, hl⟩ := cs.exists_reduced_word' (s i * w)
      simp [hl]
      have h1 : ℓ (s i * w) < ℓ (s i * (s i * w)) := by simpa
      have h2 : cs.IsReduced ([i] ++ l) := cons_reduced cs hl.1 (by simpa [←hl.2])
      simp [←wordProd_cons, Tinv_eq_inv_aux_reduced_word cs h2 _, inv_aux_cons, wordProd_cons]
      simp only [←hl.2, ←TsT_of_lt cs h1]
      simp only [←mul_assoc, mul_assoc cs _ _ (T cs (s i)), isLeftInv, mul_one]
      specialize ih (π l) (by simpa [←hl.2])
      simpa [Tinv_eq_inv_aux_reduced_word cs hl.1, ←hl.2] using ih

lemma Tinv_isRightInv (w : cs.Group) : T cs w * T⁻¹ w = 1 := by
  induction' w using WellFounded.induction with w ih
  · exact (Coxeter.wf cs).wf
  · simp only [rel_iff_length_lt] at ih
    by_cases w1 : w = 1
    · simp [w1, ←one_def]
    · obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one w1
      rw [←cs.simple_mul_simple_cancel_left (w:=w) i]
      obtain ⟨l, hl⟩ := cs.exists_reduced_word' (s i * w)
      simp [hl]
      have h1 : ℓ (s i * w) < ℓ (s i * (s i * w)) := by simpa
      have h2 : cs.IsReduced ([i] ++ l) := cons_reduced cs hl.1 (by simpa [←hl.2])
      simp [←wordProd_cons, Tinv_eq_inv_aux_reduced_word cs h2 _, inv_aux_cons, wordProd_cons]
      simp only [←hl.2, ←TsT_of_lt cs h1]
      simp only [←mul_assoc, mul_assoc cs _ _ (T cs (s i)), isLeftInv, mul_one]
      specialize ih (π l) (by simpa [←hl.2])
      simp [Tinv_eq_inv_aux_reduced_word cs hl.1, ←hl.2] at ih
      conv =>
        enter [1, 1]; simp [mul_assoc, ih]
      simp [isRightInv]

lemma Tinv_mul_simple {i : B} {u : cs.Group} (h : ℓ u < ℓ (u * s i)) :
    T⁻¹ (u * s i) = T⁻¹ (s i) * T⁻¹ u := by
  suffices T⁻¹ (u * s i) * T cs u * T cs (s i) = 1 by
    apply_fun (· * T⁻¹ (cs.simple i) * T⁻¹ u) at this
    simp at this
    conv at this =>
      enter [1, 1]; simp [mul_assoc, Tinv_simple, isRightInv]
    simpa [mul_assoc, Tinv_isRightInv] using this
  simp [mul_assoc, TTs_of_lt cs h, Tinv_isLeftInv]

lemma Tinv_simple_mul {i : B} {u : cs.Group} (h : ℓ u < ℓ (s i * u)) :
    T⁻¹ (s i * u) = T⁻¹ u * T⁻¹ (s i) := by
  suffices T⁻¹ (s i * u) * T cs (s i) * T cs u = 1 by
    apply_fun (· * T⁻¹ u * T⁻¹ (s i)) at this
    simp at this
    conv at this =>
      enter [1, 1]; simp [mul_assoc, Tinv_isRightInv]
    simpa [mul_assoc, Tinv_simple, isRightInv] using this
  simp [mul_assoc, TsT_of_lt cs h, Tinv_isLeftInv]

lemma Tinv_unique (w : cs.Group) : ∀ h, h * T cs w = 1 → h = T⁻¹ w := by
  intro h hh
  apply_fun ( · * T⁻¹ w) at hh
  simp [mul_assoc, Tinv_isRightInv cs] at hh
  exact hh

end HeckeInv


local notation : max "T⁻¹" => Tinv cs

noncomputable section involution

abbrev iotaT : cs.Group → cs.Hecke := fun w => T⁻¹ w⁻¹

abbrev iota : cs.Hecke → cs.Hecke :=
  fun h => finsum (fun x : cs.Group => invert (h x) • iotaT cs x)

local notation : max "ι" => iota cs

@[simp]
lemma iotaT_apply_one : iotaT cs 1 = 1 := by simp [iotaT]

open Classical in
lemma iota_apply_T (w : cs.Group) : ι (T cs w) = T⁻¹ w⁻¹ := by
  simp [iota]
  suffices ∑ᶠ (x : cs.Group), invert ((T cs w) x) • iotaT cs x = invert ((T cs w) w) • iotaT cs w by
    simp [this]
  apply finsum_eq_single
  simp [T, Finsupp.single_apply]
  tauto

@[simp]
lemma iot_apply_one : ι 1 = 1 := by simp [one_def, iota_apply_T]

lemma support_of_Hecke_apply_smul_fin (h : cs.Hecke) :
    (fun x ↦ invert (h x) • iotaT cs x).support.Finite := by
  suffices (fun x ↦ invert (h x) • iotaT cs x).support ⊆
  (fun x_1 ↦ LaurentPolynomial.invert (h x_1)).support by
    apply Set.Finite.subset _ this
    simp [Function.support]
    exact Finsupp.finite_support h
  simp [not_imp_not]
  intro w hw
  simp [hw, LaurentPolynomial.invert_C]

lemma map_smul' (r : LaurentPolynomial ℤ) (h : cs.Hecke) : ι (r • h) = invert r • ι h := by
  simp [iota, ←smul_smul]
  rw [←smul_finsum']
  exact support_of_Hecke_apply_smul_fin cs h

lemma map_add' (x y : cs.Hecke) : ι (x + y) = ι x + ι y := by
  simp [iota, add_smul]
  rw [finsum_add_distrib (support_of_Hecke_apply_smul_fin _ x)
  (support_of_Hecke_apply_smul_fin _ y)]

def iotaAddHom : AddMonoidHom cs.Hecke cs.Hecke where
  toFun := iota cs
  map_zero' := by simp [iota]
  map_add' := map_add' cs

lemma iota_apply_T_inv_simple (i : B) : ι (T⁻¹ (s i)) = T cs (s i) := by
  simp [Tinv_simple', sub_eq_add_neg, map_add', map_smul', ←neg_smul]
  simp only [iota_apply_T, inv_simple, Tinv_simple', smul_sub, smul_smul]
  simp only [mul_sub, ←T_add, sub_smul, add_smul, ←sub_eq_add_neg]
  simp

lemma map_one' : ι 1 = 1 := by simp [one_def, iota_apply_T]

lemma map_mul_TsT (i : B) (w : cs.Group) :
    ι (T cs (s i) * T cs w) = ι (T cs (s i)) * ι (T cs w) := by
  rcases cs.length_simple_mul w i with hlt | hgt
  · replace hlt : ℓ w < ℓ (s i * w) := by omega
    simp [TsT_of_lt cs hlt, iota_apply_T]
    rw [←Tinv_mul_simple]
    rw [show w⁻¹ * s i = ((s i) * w)⁻¹ by simp]
    simp only [length_inv, hlt]
  · replace hgt : ℓ (s i * w) < ℓ w := by omega
    simp [TsT_of_gt cs hgt, map_add', map_smul', iota_apply_T]
    nth_rw 1 [←cs.simple_mul_simple_cancel_right i (w := w⁻¹)]
    have l1 : ℓ (w⁻¹ * s i) < ℓ (w⁻¹ * s i * s i) := by
      nth_rw 1 [show w⁻¹ * s i = (s i * w)⁻¹ by simp, cs.length_inv]
      simp [hgt]
    rw [Tinv_mul_simple cs l1, Tinv_simple]
    conv => lhs; rw [←smul_mul_assoc]; congr; rfl; rw [←smul_one_mul]
    rw [←right_distrib]
    conv =>
      rhs
      rw [←cs.simple_mul_simple_cancel_right (w := w⁻¹) i, Tinv_mul_simple cs l1,
        Tinv_simple, ←mul_assoc]
    congr
    nth_rw 2 [T_simple_inv]
    rw [sub_mul,←Tinv_simple, smul_mul_assoc, Tinv_isRightInv cs]
    nth_rw 2 [sub_eq_add_neg, add_comm]
    congr
    simp [←neg_smul]

lemma map_mul_Ts (i : B) (h : cs.Hecke) :
    ι (T cs (s i) * h) = ι (T cs (s i)) * ι h := by
  have l1 (h1 : cs.Hecke) : ι h1 = iotaAddHom cs h1 := rfl
  rw [T_repr cs h, Finsupp.mul_sum, l1, map_finsupp_sum]
  simp_rw [←l1, mul_smul_comm, map_smul', map_mul_TsT, ←mul_smul_comm, ←Finsupp.mul_sum]
  simp_rw [l1, map_finsupp_sum, ←l1, map_smul']

lemma map_mul_TT (w w' : cs.Group) : ι (T cs w * T cs w') = ι (T cs w) * ι (T cs w') := by
  induction' w using WellFounded.induction with w ih
  · exact (Coxeter.wf cs).wf
  · simp at ih
    by_cases w1 : w = 1
    · simp [w1, ←one_def]
    · obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one w1
      have l1 :ℓ (s i * w) < ℓ (s i * (s i * w)) := by simp; exact hi
      rw [←cs.simple_mul_simple_cancel_left (w := w) i, ←TsT_of_lt cs l1]
      simp_rw [mul_assoc, map_mul_Ts, ih (s i * w) hi, mul_assoc]

lemma map_mul' (x y : cs.Hecke) : ι (x * y) = ι x * ι y := by
  rw [T_repr cs x, Finsupp.sum_mul y x, T_repr cs y]
  have l1 (h : cs.Hecke) : ι h = iotaAddHom cs h := rfl
  rw [l1, map_finsupp_sum]
  simp_rw [Finsupp.mul_sum, map_finsupp_sum, ←l1, mul_smul_comm, smul_mul_assoc, smul_smul,mul_comm]
  conv  =>
    lhs; congr; rfl; intro h1 r1; congr; rfl; intro h2 r2;
    rw [map_smul', map_mul_TT, map_mul, mul_smul_mul_comm]
  simp_rw [Finsupp.sum, ← Finset.sum_mul_sum, l1, map_sum, ←l1, map_smul']

lemma map_zero' : ι 0 = 0 := by simp [iota]

def iota' : RingHom cs.Hecke cs.Hecke where
  toFun := iota cs
  map_one':= map_one' cs
  map_mul':= map_mul' cs
  map_zero':= map_zero' cs
  map_add':= map_add' cs

def iotaA' : RingHom (LaurentPolynomial ℤ) (LaurentPolynomial ℤ) where
  toFun := invert
  map_one' := by simp
  map_mul' := by simp
  map_zero' := by simp
  map_add' := by simp

instance l2 : LinearMap iotaA' cs.Hecke cs.Hecke where
  toFun := iota cs
  map_add' := map_add' cs
  map_smul' := by simp [iotaA', map_smul']


lemma iota_sq_apply_T_simple (i : B) : ι^[2] (T cs (s i)) = T cs (s i):= by
  simp [iota_apply_T,iota_apply_T_inv_simple]

lemma iota_sq_apply_T (w : cs.Group) : ι^[2] (T cs w) = T cs w := by
  simp
  induction' w using WellFounded.induction with w ih
  · exact (Coxeter.wf cs).wf
  · simp at ih
    by_cases w1 : w = 1
    · simp [w1, ←one_def, map_one']
    · obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one w1
      nth_rw 1 [←cs.simple_mul_simple_cancel_left (w := w) i]
      have l1 : ℓ (s i * w) < ℓ (s i * (s i * w)) := by simp; exact hi
      have l2 (h1 : cs.Hecke) : ι (ι h1) = ι^[2] h1 := rfl
      rw [←TsT_of_lt cs l1, map_mul', map_mul', l2]
      simp [iota_sq_apply_T_simple, ih (s i * w) hi, TsT_of_lt cs l1]

lemma iota_sq_apply (h : cs.Hecke) : ι^[2] h = h := by
  rw [T_repr cs h]
  simp
  have l1 (h1 : cs.Hecke) : ι h1 = (iota' cs) h1 := rfl
  have l2 (h1 : cs.Hecke) : ι (ι h1) = ι^[2] h1 := rfl
  rw [l1, l1, map_finsupp_sum, map_finsupp_sum]
  simp_rw [←l1, map_smul', ]
  nth_rw 2 [←LaurentPolynomial.invert_symm]
  simp only [AlgEquiv.apply_symm_apply, l2, iota_sq_apply_T]

end involution


end Hecke
