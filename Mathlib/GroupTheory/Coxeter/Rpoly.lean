import Mathlib.GroupTheory.Coxeter.Hecke
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

variable {B : Type}
variable {W : Type} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable {l : List B} {t : W}

open CoxeterSystem Hecke Finsupp LaurentPolynomial Classical

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length
local prefix:100 "ris" => cs.rightInvSeq
local prefix:100 "lis" => cs.leftInvSeq

local notation : max "q" => @LaurentPolynomial.T ℤ _ (1)
local notation : max "q⁻¹" => @LaurentPolynomial.T ℤ _ (-1)
local notation : max "T₁" => T cs 1
local notation : max "Tₛ" => T_simple cs
local notation : max "T⁻¹" => Tinv cs

namespace CoxeterSystem

class Rpoly (R : cs.Group → cs.Group → LaurentPolynomial ℤ) where
  not_le : ∀ u v : cs.Group, ¬ (u ≤ v) → R u v = 0
  eq : ∀ u : cs.Group, R u u = 1
  mem_rD {u v : cs.Group} {i : B} (hui : cs.IsLeftDescent u i) (hvi : cs.IsLeftDescent v i) :
    R u v = R (s i * u) (s i * v)
  not_mem_rD {u v : cs.Group} {i : B} (hui : ¬cs.IsLeftDescent u i) (hvi : cs.IsLeftDescent v i) :
    R u v = q * R (s i * u) (s i * v) + (q - 1) * R u (s i * v)

noncomputable def R : cs.Group → cs.Group → ℤ[T;T⁻¹] := fun x w =>
  T⁻¹ w⁻¹ x * (-1)^(ℓ w + ℓ x) * q^ ℓ w

-- trans
lemma simple_mul_ne (i : B) (w : cs.Group) : s i * w ≠ w :=
  fun h => cs.length_simple_mul_ne w i (congrArg cs.length h)

lemma simple_ne_one (i : B) : s i ≠ 1 := by
  have := simple_mul_ne cs i 1; simp [-ne_eq] at this; exact this

lemma Ts_mul_apply_ne_zero {u : cs.Group} {i : B} (w : cs.Group)
    (h : (T cs (s i) * T cs w) u ≠ 0) : w = u ∨ w = s i * u := by
  by_cases h2 : ℓ (s i * w) < ℓ w
  · rw [TsT_of_gt cs h2, add_apply, smul_apply, smul_apply] at h
    contrapose! h
    simp [Hecke.T, single_apply, h.1]
    intro h3
    apply_fun (s i * · ) at h3
    simp at h3
    exact False.elim <| h.2 h3
  · replace h2 : ℓ (w) < ℓ (s i * w) := by
      have := cs.length_simple_mul_ne w i
      omega
    rw [TsT_of_lt cs h2] at h
    simp [Hecke.T, single_apply] at h
    apply_fun (s i * · ) at h
    simp at h
    exact Or.inr h

lemma Ts_mul_apply_gt_aux {u : cs.Group} {i : B} (h1 : ℓ (s i * u) < ℓ u) (w : cs.Group) :
    (T cs (s i) * T cs w) u ≠ 0 ↔ w = u ∨ w = s i * u := by
  constructor <;> intro h
  · exact Ts_mul_apply_ne_zero cs w h
  · rcases h with h | h
    · simp [h, TsT_of_gt cs h1]
      have l1 (i : B) (w : cs.Group) : s i * w ≠ w := simple_mul_ne cs i w
      simp [Hecke.T, single_apply, l1, ←LaurentPolynomial.T_zero]
      rw [LaurentPolynomial.T,LaurentPolynomial.T, sub_eq_zero, ←ne_eq]
      exact Finsupp.ne_iff.2 ⟨0, by simp only [single_apply]; tauto⟩
    · have h2 : ℓ (s i * u) < ℓ (s i * (s i * u)) := by simpa
      simp [h, TsT_of_lt cs h2]

lemma Ts_mul_apply_of_gt {u : cs.Group} {i : B} (h : cs.Hecke) (h1 : ℓ (s i * u) < ℓ u) :
    (T cs (s i) * h) u = h (s i * u) + (q - 1) * h u := by
  nth_rw 1 [T_repr cs h, mul_sum, sum_apply, sum]
  simp_rw [mul_smul_comm, smul_apply]
  -- nth_rw 1 [sum]
  let s1 :=  h.support ∩ {u, s i * u}
  let s2 := h.support \ s1
  have l1 : s1 ∪ s2 = h.support := by
    simp [s1, s2]
    rw [Finset.union_comm, Finset.sdiff_union_inter]
  have l2 : Disjoint s1 s2 := by
    simp [s2]
    exact Finset.disjoint_sdiff
  rw [←l1, Finset.sum_union l2]
  have l3 : ∑ x ∈ s2, h x • (Hecke.T cs (cs.simple i) * Hecke.T cs x) u = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp [s1, s2] at hx ⊢
    apply Or.inr
    have := (not_iff_not.2 <|Ts_mul_apply_gt_aux cs h1 x).2
    tauto
  have l4 : u ≠ s i * u := (simple_mul_ne cs i u).symm
  have h1' : ℓ (s i * u) < ℓ (s i * (s i * u)) := by simpa
  simp only [l3, add_zero, s1]
  rcases Classical.em (u ∈ h.support) with c1 | c1 <;>
  rcases Classical.em (s i * u ∈ h.support) with c2 | c2 <;> simp [c1, c2, l4]
  · simp [TsT_of_gt cs h1, TsT_of_lt cs h1']
    simp [Hecke.T, single_apply, simple_ne_one, mul_comm, add_comm]
  · simp only [TsT_of_gt cs h1, Finsupp.not_mem_support_iff.1 c2]
    simp [Hecke.T, single_apply, simple_ne_one, mul_comm]
  · simp [TsT_of_gt cs h1, TsT_of_lt cs h1', Finsupp.not_mem_support_iff.1 c1]
  · simp [Finsupp.not_mem_support_iff.1 c1, Finsupp.not_mem_support_iff.1 c2]

lemma Rpoly_aux {i : B} {w u : cs.Group} (hiw : cs.IsLeftDescent w i) (hiu : cs.IsLeftDescent u i) :
    (T⁻¹ w⁻¹) u = (T⁻¹ (s i * w)⁻¹) (s i * u) * q⁻¹ := by
  rw [← cs.simple_mul_simple_cancel_right i (w := w⁻¹)]
  have : ℓ (w⁻¹ * s i) < ℓ (w⁻¹ * s i * s i) := by
    convert cs.isRightDescent_inv_iff.2 hiw; simp [IsRightDescent]
  rw [Tinv_mul_simple cs this, Tinv_simple', sub_mul, sub_apply, smul_mul_assoc, smul_apply]
  rw [cs.Ts_mul_apply_of_gt _ hiu]
  simp [_root_.right_distrib, mul_right_comm, sub_mul]

lemma Ts_mul_apply_of_lt_aux {u : cs.Group} {i : B} (w : cs.Group) (h1 : ℓ u < ℓ (s i * u)) :
    (T cs (s i) * T cs w) u ≠ 0 ↔ w = s i * u := by
  constructor <;> intro h
  · by_cases h2 : ℓ (s i * w) < ℓ (w)
    · have h3 := Ts_mul_apply_ne_zero cs w h
      rcases h3 with h3 | h3
      · simp [h3] at h2; omega
      · exact h3
    · replace h2 : ℓ (w) < ℓ (s i * w) := by
        have := cs.length_simple_mul_ne w i
        omega
      rw [TsT_of_lt cs h2] at h
      simp [Hecke.T, single_apply] at h
      apply_fun (s i * · ) at h
      simp [←h]
  · have l1 : ℓ (s i * (s i * u)) < ℓ (s i * u):= by simpa
    simp  [h, TsT_of_gt cs l1]
    simp only [Hecke.T, single_apply, simple_mul_ne, ite_false, MulZeroClass.mul_zero, zero_add]
    rw [LaurentPolynomial.T, ←ne_eq]
    exact Finsupp.ne_iff.2 ⟨1, by simp only [single_apply]; tauto⟩

lemma Ts_mul_apply_of_lt {u : cs.Group} {i : B} (h : cs.Hecke)
    (h1 : ℓ u < ℓ (s i * u)) : (T cs (s i) * h) u = q * h (s i * u) := by
  nth_rw 1 [T_repr cs h, mul_sum, sum_apply]
  have : (h.sum fun a₁ b ↦ (Hecke.T cs (s i) * b • Hecke.T cs a₁) u) =
       (Hecke.T cs (s i) * h (s i * u) • Hecke.T cs (s i * u)) u := by
    apply Finsupp.sum_eq_single
    · intro b hb h2
      simp
      apply (or_iff_right hb).2
      contrapose! h2
      exact (Ts_mul_apply_of_lt_aux cs b h1).1 h2
    · simp [Hecke.mul_zero]
  have l1 : ℓ (s i * (s i * u)) < ℓ (s i * u) := by simpa
  rw [this]
  simp [mul_smul_comm, TsT_of_gt cs l1, -mul_eq_zero]
  simp only [Hecke.T, single_apply, simple_mul_ne, ite_false, MulZeroClass.mul_zero, zero_add]

lemma Rpoly_aux' {i : B} {w u : cs.Group} (hiw : cs.IsLeftDescent w i)
    (hiu : ¬cs.IsLeftDescent u i) :
    (T⁻¹ w⁻¹) u =  T⁻¹ (s i * w)⁻¹ (s i * u) - (1 - q⁻¹) * (T⁻¹ (s i * w)⁻¹) u := by
  rw [← cs.simple_mul_simple_cancel_right i (w := w⁻¹)]
  have : ℓ (w⁻¹ * s i) < ℓ (w⁻¹ * s i * s i) := by
    convert cs.isRightDescent_inv_iff.2 hiw; simp [IsRightDescent]
  rw [Tinv_mul_simple cs this, Tinv_simple', sub_mul, sub_apply, smul_mul_assoc, smul_apply]
  replace hiu : ℓ u < ℓ (s i * u) := by
    simp [IsLeftDescent] at hiu
    have := cs.length_simple_mul u i
    omega
  rw [cs.Ts_mul_apply_of_lt _ hiu]
  simp

lemma R_eq (u : cs.Group) : cs.R u u = 1 := by
  simp [R]
  induction' u using WellFounded.induction with u ih
  · exact (Coxeter.wf cs).wf
  · simp at ih
    by_cases u1 : u = 1
    · simp [u1]
    · obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one u1
      specialize ih (s i * u) hi
      rw [cs.Rpoly_aux hi hi, ←cs.isLeftDescent_iff.1 hi]
      simp at ih
      simp [ih]

lemma R_mem_rD {u v : cs.Group} {i : B} (hui : cs.IsLeftDescent u i)
    (hvi : cs.IsLeftDescent v i) : cs.R u v = cs.R (s i * u) (s i * v) := by
  simp only [R]
  suffices (T⁻¹ v⁻¹) u * q = (T⁻¹ (s i * v)⁻¹) (s i * u) by
    have lu := cs.isLeftDescent_iff.1 hui
    have lv := cs.isLeftDescent_iff.1 hvi
    simp [←lu, ←lv, show cs.length (s i * v) + 1 + (cs.length (s i * u) + 1)
      = cs.length (s i * v) + cs.length (s i * u) + 2 by ring]
    simp [pow_add]
    rw [T_add]
    calc
      _ = (T⁻¹ v⁻¹) u * q * (-1) ^ ℓ (s i * v) * (-1) ^ ℓ (s i * u) * (T (ℓ (s i * v))) := by
        ring_nf
      _ = (T⁻¹ (v⁻¹ * s i)) (s i * u) * (-1) ^ ℓ (s i * v) * (-1) ^ ℓ (s i * u) *
          (T (ℓ (s i * v))) := by simp at this; rw [this]
      _ = _ := by ring_nf
  simp [cs.Rpoly_aux hvi hui]

lemma R_not_mem_rD {u v : cs.Group} {i : B} (hui : ¬cs.IsLeftDescent u i)
    (hvi : cs.IsLeftDescent v i) :
    cs.R u v = q * cs.R (s i * u) (s i * v) + (q - 1) * cs.R u (s i * v) := by
  simp only [R]
  have h1 : q - 1 = q * (1 - q⁻¹) := by
    simp only [mul_sub,_root_.mul_one, ←T_add,add_neg_cancel, T_zero]
  conv =>
    lhs; rw [_root_.mul_assoc]
  conv in q * ?_ =>
    rw [←_root_.mul_assoc, mul_rotate, _root_.mul_assoc, T_pow, ←T_add]
    norm_cast
    rw [_root_.mul_one, cs.isLeftDescent_iff.1 hvi]
  conv in (q - 1) * ?_ =>
    rw [←_root_.mul_assoc, mul_rotate, _root_.mul_assoc]
    rw [h1, ←_root_.mul_assoc _ q, T_pow, ←T_add, _root_.mul_one]
    norm_cast
    rw [cs.isLeftDescent_iff.1 hvi, ← _root_.mul_assoc, ←mul_rotate]
    congr
  rw [←add_mul, T_pow, _root_.mul_one, ←_root_.mul_assoc]
  congr
  have lvpos : 0 < ℓ v := by
    have := cs.isLeftDescent_iff.1 hvi; omega
  have lu : ℓ (s i * u) = ℓ u + 1 := by
    have := cs.length_simple_mul u i
    simp [cs.isLeftDescent_iff] at hui
    omega
  have lv : ℓ (s i * v) = ℓ v - 1 := by
    have := cs.isLeftDescent_iff.1 hvi; omega
  have h2 : ℓ (s i * v) + ℓ (s i * u) = ℓ v + ℓ u := by
    simp [lu, lv]; omega
  have h3 : ℓ (s i * v) + ℓ u = ℓ v + ℓ u - 1 := by simp [lv]; omega
  have h4 : (-1)^ (ℓ (s i * v) + ℓ u) = - (-1)^ (ℓ v + ℓ u) := by
    nth_rw 2 [neg_eq_neg_one_mul, ←pow_one (-1)]; rw [h3, ←pow_add]
    rw [show 1 + (ℓ v + ℓ u) = (ℓ v + ℓ u) - 1 + 2 by omega]
    simp only [pow_add, even_two, Even.neg_pow, one_pow, _root_.mul_one]
  simp [-mul_inv_rev, h2, h4, ←sub_eq_add_neg, ←_root_.mul_assoc, ←sub_mul]
  congr
  exact Rpoly_aux' cs hvi hui

--trans
open Bruhat in
lemma simple_mul_le_simple_mul_iff {u v : cs.Group} {i : B} (hu : cs.IsLeftDescent u i)
    (hv : cs.IsLeftDescent v i) : toCoxeterGroup cs (s i) * u ≤ s i * v ↔ u ≤ v := by
  sorry

--trans
open Bruhat in
lemma le_of_IsLeftDescent {u : cs.Group} {i : B} (hu : cs.IsLeftDescent u i) :
    toCoxeterGroup cs (s i) * u ≤ u := sorry

lemma ge_of_not_IsLeftDescent {u : cs.Group} {i : B} (hu : ¬cs.IsLeftDescent u i) :
    u ≤ s i * u := by sorry

open Bruhat in
lemma R_not_le (u v : cs.Group) : ¬u ≤ v → cs.R u v = 0 := by
  intro h
  revert u
  induction' v using WellFounded.induction with v ih
  · exact (Coxeter.wf cs).wf
  · simp at ih
    intro u huv
    by_cases v1 : v = 1
    · have une1 : u ≠ 1 := by intro u1; simp [u1, v1] at huv
      simp [v1, R, one_def, Hecke.T, single_apply]
      tauto
    · obtain ⟨i, hiv⟩ := cs.exists_leftDescent_of_ne_one v1
      by_cases hiu : cs.IsLeftDescent u i
      · rw [R_mem_rD cs hiu hiv]
        have l1 : ¬ toCoxeterGroup cs (s i * u) ≤ toCoxeterGroup cs (s i * v) :=
          (not_iff_not.2 (simple_mul_le_simple_mul_iff cs hiu hiv)).2 huv
        exact ih (s i * v) hiv (s i * u) l1
      · rw [R_not_mem_rD cs hiu hiv]
        have l1 : ¬ u ≤ s i * v := by
          contrapose! huv
          exact huv.trans (le_of_IsLeftDescent cs hiv)
        have l2 : ¬ toCoxeterGroup cs (s i * u) ≤ s i * v := by
          contrapose! huv
          exact ((ge_of_not_IsLeftDescent cs hiu).trans huv).trans (le_of_IsLeftDescent cs hiv)
        simp only [ih (s i * v) hiv u l1, ih (s i * v) hiv (s i * u) l2,
          MulZeroClass.mul_zero, zero_add]

instance : cs.Rpoly cs.R where
  not_le := cs.R_not_le
  eq := cs.R_eq
  mem_rD := cs.R_mem_rD
  not_mem_rD := cs.R_not_mem_rD

theorem Unique_Rpoly {R' : cs.Group → cs.Group → LaurentPolynomial ℤ} :
    cs.Rpoly R' → R' = cs.R := by
  intro h
  funext u v
  revert u
  induction' v using WellFounded.induction with v ih
  · exact (Coxeter.wf cs).wf
  · intro u
    simp at ih
    by_cases v1 : v = 1
    · simp [v1]
      by_cases u1 : u = 1
      · simp [u1, Rpoly.eq]
      · simp [Rpoly.not_le u 1 (not_le_of_gt <| Bruhat.one_lt_of_ne_one cs u1)]
    · obtain ⟨i, hiv⟩ := cs.exists_leftDescent_of_ne_one v1
      by_cases hiu : cs.IsLeftDescent u i
      · simp [Rpoly.mem_rD hiu hiv]
        exact ih (s i * v) hiv (s i * u)
      · simp [Rpoly.not_mem_rD hiu hiv, ih (s i * v) hiv (s i * u), ih (s i * v) hiv u]

end CoxeterSystem

section property

variable {h : cs.Hecke}

lemma invert_Rpoly (x w : cs.Group) : (cs.R x w).invert =
    (-1)^( ℓ x + ℓ w) * q^(ℓ x - ℓ w) * (cs.R x w) := by sorry

--trans
instance {x w : cs.Group} : Fintype (Set.Icc x w) := sorry

lemma T_inv_eq (w : cs.Group) : T⁻¹ w⁻¹ = ∑ x : Set.Icc 1 w, q⁻¹ ^ (ℓ x) • Hecke.T cs x := by sorry

lemma Rpoly_concat (x w : cs.Group) (h : x < w) :
    ∑ y : Set.Icc x w, (-1)^(ℓ x + ℓ y) * cs.R x y * cs.R y w = 0 := sorry

end property
