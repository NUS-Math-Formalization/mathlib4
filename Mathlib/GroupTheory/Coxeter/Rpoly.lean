import Mathlib.GroupTheory.Coxeter.Hecke

variable {B : Type}
variable {W : Type} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable {l : List B} {t : W}

open CoxeterSystem Hecke Finsupp LaurentPolynomial

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length
local prefix:100 "ris" => cs.rightInvSeq
local prefix:100 "lis" => cs.leftInvSeq

local notation : max "q" => @LaurentPolynomial.T ℤ _ (1)
local notation : max "q⁻¹" => @LaurentPolynomial.T ℤ _ (-1)
local notation : max "T₁" => T cs 1
local notation : max "Tₛ" => T_simple cs
local notation : max "Tₛ⁻¹" => T_simple_inv cs
local notation : max "T⁻¹" => Tinv cs

namespace CoxeterSystem

class Rpoly (R : cs.Group → cs.Group → LaurentPolynomial ℤ) where
  not_le : ∀ u v : cs.Group, ¬ (u ≤ v) → R u v = 0
  eq : ∀ u : cs.Group, R u u = 1
  mem_rD {u v : cs.Group} {i : B} (hui : cs.IsLeftDescent u i) (hvi : cs.IsLeftDescent v i) :
    R u v = R (s i * u) (s i * v)
  not_mem_rD {u v : cs.Group} {i : B} (hui : ¬cs.IsLeftDescent u i) (hvi : cs.IsLeftDescent v i) :
    R u v = q * R (s i * u) (s i * v) + (q - 1) * R u (s i * v)

noncomputable def R : cs.Group → cs.Group → LaurentPolynomial ℤ := fun x w =>
  T⁻¹ w⁻¹ x * (-1)^(ℓ(w) + (ℓ(x))) * q^(ℓ(w))

#check MonoidAlgebra.mul_apply

-- def Hecke.MonoidAlgebra : cs.Hecke = MonoidAlgebra (LaurentPolynomial ℤ) cs.Group := rfl

lemma Tsimple_mul_apply_of_gt {u : cs.Group} {i : B} (h : cs.Hecke)
  (h1 : ℓ (s i * u) < ℓ u) : (T cs (s i) * h) u = h (s i * u) + (q - 1) * h u := by
    -- have := Basis.linearCombination_repr Finsupp.basisSingleOne h
    -- rw [Finsupp.linearCombination_apply] at this
    -- have := MonoidAlgebra.mul_apply (Tₛ i) h u
    sorry

lemma Rpoly_aux {i : B} {w u : cs.Group} (hiw : cs.IsLeftDescent w i) (hiu : cs.IsLeftDescent u i) :
    (T⁻¹ w⁻¹) u = (T⁻¹ (s i * w)⁻¹) (s i * u) * q⁻¹ := by
  rw [← cs.simple_mul_simple_cancel_right i (w := w⁻¹)]
  have : ℓ (w⁻¹ * s i) < ℓ (w⁻¹ * s i * s i) := by
    convert cs.isRightDescent_inv_iff.2 hiw; simp [IsRightDescent]
  rw [Tinv_mul_simple cs this, Tinv_simple, sub_mul, sub_apply, smul_mul_assoc, smul_apply]
  rw [cs.Tsimple_mul_apply_of_gt _ hiu]
  simp [_root_.right_distrib, mul_right_comm, sub_mul]

lemma Tsimple_mul_apply_of_lt {u : cs.Group} {i : B} (h : cs.Hecke)
    (h1 : ℓ u < ℓ (s i * u)) : (T cs (s i) * h) u = h (s i * u) := by

  sorry

lemma Rpoly_aux' {i : B} {w u : cs.Group} (hiw : cs.IsLeftDescent w i)
    (hiu : ¬cs.IsLeftDescent u i) :
    (T⁻¹ w⁻¹) u =  q⁻¹ * T⁻¹ (s i * w)⁻¹ (s i * u) - (1 - q⁻¹) * (T⁻¹ (s i * w)⁻¹) u := by
  rw [← cs.simple_mul_simple_cancel_right i (w := w⁻¹)]
  have : ℓ (w⁻¹ * s i) < ℓ (w⁻¹ * s i * s i) := by
    convert cs.isRightDescent_inv_iff.2 hiw; simp [IsRightDescent]
  rw [Tinv_mul_simple cs this, Tinv_simple, sub_mul, sub_apply, smul_mul_assoc, smul_apply]
  replace hiu : ℓ u < ℓ (s i * u) := by
    simp [IsLeftDescent] at hiu
    have := cs.length_simple_mul u i
    omega
  rw [cs.Tsimple_mul_apply_of_lt _ hiu]
  simp

lemma R_not_le (u v : cs.Group) : ¬u ≤ v → cs.R u v = 0 := by
  intro h
  sorry

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
  have h1 := cs.Rpoly_aux' hvi hui
  simp [h1]
  sorry

instance : cs.Rpoly cs.R where
  not_le := cs.R_not_le
  eq := cs.R_eq
  mem_rD := cs.R_mem_rD
  not_mem_rD := cs.R_not_mem_rD

lemma Unique_Rpoly {R' : cs.Group → cs.Group → LaurentPolynomial ℤ} : cs.Rpoly R' → R' = cs.R := by
  sorry

end CoxeterSystem
