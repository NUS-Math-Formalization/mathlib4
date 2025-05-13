import Mathlib.GroupTheory.Coxeter.Rpoly

variable {B : Type}
variable {W : Type} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable {l : List B} {t : W}

open CoxeterSystem Hecke Classical  AddMonoidAlgebra

open LaurentPolynomial hiding invert

local prefix:100 "s" => cs.simple
local prefix:100 "ℓ" => cs.length

local notation : max "q" => @LaurentPolynomial.T ℤ _ (1)
local notation : max "q⁻¹" => @LaurentPolynomial.T ℤ _ (-1)
local notation : max "T₁" => T cs 1
local notation : max "T⁻¹" => Tinv cs
local notation : max "ι" => iota cs

noncomputable section

instance embA : Coe (LaurentPolynomial ℤ) (AddMonoidAlgebra ℤ ℚ) where
  coe := AddMonoidAlgebra.mapDomain (Int.cast)

abbrev Hecke' := cs.Group →₀ AddMonoidAlgebra ℤ ℚ

instance : AddCommMonoid (Hecke' cs) := Finsupp.instAddCommMonoid

instance : Module (AddMonoidAlgebra ℤ ℚ) (Hecke' cs) := Finsupp.module _ _

def ofHecke : cs.Hecke → Hecke' cs := Finsupp.mapRange embA.coe (by simp [embA])

instance : Coe cs.Hecke (Hecke' cs) where
  coe := ofHecke cs

def AddMonoidAlgebra.invert : AddMonoidAlgebra ℤ ℚ ≃ₐ[ℤ] AddMonoidAlgebra ℤ ℚ :=
  AddMonoidAlgebra.domCongr ℤ ℤ (AddEquiv.neg ℚ)

def iota' : Hecke' cs → Hecke' cs :=
  fun h => finsum (fun x : cs.Group => invert (h x) • iotaT cs x)

def qsq : AddMonoidAlgebra ℤ ℚ := single (1 / 2) 1

def qsqinv : AddMonoidAlgebra ℤ ℚ := single (-1 / 2) 1

end

noncomputable def C_s (i : B) : Hecke' cs := qsqinv • (ofHecke cs (T cs (s i) - q • T₁))

lemma iota'_fix_Cs (i : B) : iota' cs (C_s cs i) = C_s cs i := by
  simp [_root_.iota']
  sorry

-- lemma Cs_mul (i j : B) : Cs cs i * Cs cs j =
--     q⁻¹ •  (T cs (s i * s j) - q • T cs (s i) - q • T cs (s j) + q^2 • T₁) := by sorry

-- lemma Cs_mul_comm (i j : B) : C_s cs i * C_s cs j = C_s cs j * C_s cs i := by sorry

def iota_fix (f : cs.Group → cs.Hecke) := ∀ w, ι (f w) = f w

structure KLpoly where
  P : cs.Group → cs.Group → LaurentPolynomial ℤ
  eq {u} : P u u = 1
  deg_le (u v : cs.Group) (hlt : u < v) : 2 * (P u v).degree ≤ Option.some (ℓ v - ℓ u - 1 : ℤ)
  rec_def (u v : cs.Group) (hle : u ≤ v) : LaurentPolynomial.T (ℓ v - ℓ u) * (P u v).invert =
    ∑ x : Set.Icc u v, cs.R u x * P x v

instance : Unique (KLpoly cs) := sorry

noncomputable def a (x w : cs.Group) :=
  (-1)^ ℓ w • (-1)^ ℓ x • (single (ℓ w / 2 : ℚ) (1 : ℤ))

structure iota_fixed_basis where
  C : cs.Group → cs.Hecke
  iota_fix (w) : ι (C w) = C w
  expr_T (w) : ∃ k : KLpoly cs, C w =
    ∑ x : Set.Icc 1 w, (a cs x w * invert (k.P x w)) • ofHecke cs (T cs x)

instance : Nonempty (iota_fixed_basis cs) := ⟨sorry⟩

instance : Unique (iota_fixed_basis cs) where
  default := sorry
  uniq := sorry
