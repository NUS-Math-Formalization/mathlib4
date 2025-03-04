import Mathlib.GroupTheory.Coxeter.Bruhat
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.Adjoin.Basic

variable {B : Type}
variable {W : Type} [Group W]
variable {M : CoxeterMatrix B} {cs : CoxeterSystem M W}
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

open CoxeterSystem Bruhat

noncomputable section Hecke

instance : AddCommMonoid cs.Hecke := Finsupp.instAddCommMonoid

instance moduleLaurent : Module (LaurentPolynomial ℤ) cs.Hecke := Finsupp.module _ _

instance : FunLike cs.Hecke cs.Group (LaurentPolynomial ℤ) := Finsupp.instFunLike

local notation : max "End_ε" => Module.End (LaurentPolynomial ℤ) cs.Hecke

def T : cs.Group → cs.Hecke := fun w => Finsupp.single w 1

noncomputable def q :=@LaurentPolynomial.T ℤ _ 1

local notation : max "q⁻¹" => @LaurentPolynomial.T ℤ _ (-1)
local notation : max "T₁" => T cs 1

instance : One (cs.Hecke) where
  one := T₁

instance : Basis W (LaurentPolynomial ℤ) cs.Hecke := Finsupp.basisSingleOne

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

lemma finsupp_smul (x : cs.Hecke) (i : B) :
  (Function.support fun w ↦ x w • simple_mul_T cs i w).Finite := by
    suffices (Function.support fun w ↦ x w • simple_mul_T cs i w) ⊆ x.support by
      apply Set.Finite.subset (by simp) this
    simp [not_imp_not]
    intro w hw
    simp [hw]

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

    all_goals sorry
  map_smul' := sorry

lemma opl_commute_opr : ∀ i j : B, LinearMap.comp (opr cs j) (opl cs i) =
  LinearMap.comp (opl cs i) (opr cs j) := by
    intro i j
    ext h
    simp [opl, opr]
    sorry

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
  -- apply CoxeterSystem.simple_induction_right cs w
  -- · use 1
  --   simp [alg_hom']
  -- · intro w i ⟨f, hf⟩
  --   use ⟨(opr cs i) ∘ₗ f.1, sorry⟩
  --   simp [alg_hom', opr, mul_simple]
  --   sorry
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

lemma alg_hom_bijective : Function.Bijective (alg_hom cs) := by
  constructor
  · intro ⟨f,hf⟩  ⟨g, hg⟩ h
    simp [alg_hom] at h
    have h2 : ∀ {f : subalg cs}, f.1 T₁ = 0 → f = 0 := by
      intro f h1
      exact inj_aux cs f h1
    suffices f - g = 0 by
      have : f = g := eq_of_sub_eq_zero this
      simpa
    -- have : f - g ∈ subalg cs := Subalgebra.sub_mem (subalg cs) hf hg
    have h3 : (⟨f - g, by sorry⟩ : subalg cs) = 0 := h2 (by simp [h])
    simp [←Subalgebra.coe_eq_zero] at h3
    exact h3
  · sorry

def algEquiv : LinearEquiv (@RingHom.id (LaurentPolynomial ℤ) _)  (subalg cs) cs.Hecke :=
  LinearEquiv.ofBijective (IsLinearMap.mk' (alg_hom cs) (isLinearMap cs)) (alg_hom_bijective cs)

def HeckeMul : cs.Hecke → cs.Hecke → cs.Hecke :=
  fun x y => (algEquiv cs).toFun ((algEquiv cs).invFun x * (algEquiv cs).invFun y)

lemma smul_assoc (r : LaurentPolynomial ℤ) (x y : cs.Hecke) :
  HeckeMul cs (r • x) y = r • (HeckeMul cs x y) := by sorry

lemma smul_comm (r : LaurentPolynomial ℤ) (x y : cs.Hecke) :
  HeckeMul cs x (r • y) = r • (HeckeMul cs x y) := by sorry

instance Hecke.Semiring : Semiring (cs.Hecke) := sorry

instance : Algebra (LaurentPolynomial ℤ) cs.Hecke := by
  refine' @Algebra.ofModule ..
-- #check @Module.toDistribMulAction
end Hecke

end Hecke
-- def Hecke (G : Type*) [CoxeterGroup G] := G →₀ (LaurentPolynomial ℤ)

-- namespace Hecke

-- noncomputable def TT : G → Hecke G:= fun w => Finsupp.single w 1
