import Mathlib.GroupTheory.Coxeter.Bruhat
import Mathlib.Algebra.Polynomial.Laurent


variable {B : Type}
variable {W : Type} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable {l : List B} {t : W}

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length
local prefix:100 "ris" => cs.rightInvSeq
local prefix:100 "lis" => cs.leftInvSeq

namespace CoxeterSystem

def Hecke := cs.Group →₀ (LaurentPolynomial ℤ)

end CoxeterSystem

namespace Hecke

open CoxeterSystem Bruhat

noncomputable section Hecke

instance : AddCommMonoid cs.Hecke := Finsupp.instAddCommMonoid

instance : Module (LaurentPolynomial ℤ) cs.Hecke := Finsupp.module _ _

instance : FunLike cs.Hecke cs.Group (LaurentPolynomial ℤ) := Finsupp.instFunLike

local notation : max "End_ε" => Module.End (LaurentPolynomial ℤ) cs.Hecke

def T : cs.Group → cs.Hecke := fun w => Finsupp.single w 1

noncomputable def q :=@LaurentPolynomial.T ℤ _ 1

local notation : max "q⁻¹" => @LaurentPolynomial.T ℤ _ (-1)

section HeckeMul

def simple_mul_T (i : B) (w : cs.Group) :=
  ite (ℓ w < ℓ (s i * w)) (T cs (s i * w)) ((q-1) • T cs w + q • T cs (s i * w))

def simple_mul (i : B) (h : cs.Hecke) : cs.Hecke :=
  finsum (fun w:cs.Group => h w • simple_mul_T cs i w)

def T_mul_simple (w : cs.Group) (i : B) :=
  ite (ℓ w < ℓ (w * s i)) (T cs (w * s i)) ((q-1) • T cs w + q • T cs (w * s i))

def mul_simple (h : cs.Hecke) (i : B) : cs.Hecke :=
  finsum (fun w:cs.Group => h w • T_mul_simple cs w i)

end HeckeMul

def opl (i : B) : End_ε where
  toFun := fun h => simple_mul cs i h
  map_add' := by
    intro x y
    simp [simple_mul]
    sorry
  map_smul' := sorry

def opr (i : B) : End_ε where
  toFun := fun h => mul_simple cs h i
  map_add' := by
    intro x y
    simp [simple_mul]
    sorry
  map_smul' := sorry

lemma opl_commute_opr : ∀ i j :B, LinearMap.comp (opr cs j) (opl cs i) =
  LinearMap.comp (opl cs i) (opr cs j) := by sorry

def generator_set := opl cs '' (Set.univ)

def generator_set' := opr cs '' (Set.univ)

def subalg := Algebra.adjoin (LaurentPolynomial ℤ) (generator_set cs)

def subalg' := Algebra.adjoin (LaurentPolynomial ℤ) (generator_set' cs)

def alg_hom : subalg cs → cs.Hecke := fun f => f.1 (T cs 1)

def alg_hom' : subalg' cs → cs.Hecke := fun f => f.1 (T cs 1)

instance subalg.Algebra: Algebra (LaurentPolynomial ℤ) (subalg cs) :=
  Subalgebra.algebra (subalg cs)

instance subalg'.Algebra: Algebra (LaurentPolynomial ℤ) (subalg' cs) :=
  Subalgebra.algebra (subalg' cs)


instance : IsLinearMap (LaurentPolynomial ℤ) (alg_hom cs) where
  map_add := sorry
  map_smul := sorry

lemma alg_hom_bijective : Function.Bijective (alg_hom cs) := sorry

def algEquiv : LinearEquiv (@RingHom.id (LaurentPolynomial ℤ) _)  (subalg cs) cs.Hecke where
  toFun := alg_hom cs
  map_add' := sorry
  map_smul' := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

def HeckeMul : cs.Hecke → cs.Hecke → cs.Hecke :=
  fun x y => (algEquiv cs).toFun ((algEquiv cs).invFun x * (algEquiv cs).invFun y)

lemma smul_assoc (r : LaurentPolynomial ℤ) (x y : cs.Hecke) :
  HeckeMul cs (r • x) y = r • (HeckeMul cs x y) := by sorry

lemma smul_comm (r : LaurentPolynomial ℤ) (x y : cs.Hecke) :
  HeckeMul cs x (r • y) = r • (HeckeMul cs x y) := by sorry

-- instance : Algebra (LaurentPolynomial ℤ) cs.Hecke := by
--   refine Algebra.ofModule ?_ ?_
-- #check @Module.toDistribMulAction
end Hecke

end Hecke
-- def Hecke (G : Type*) [CoxeterGroup G] := G →₀ (LaurentPolynomial ℤ)

-- namespace Hecke

-- noncomputable def TT : G → Hecke G:= fun w => Finsupp.single w 1
