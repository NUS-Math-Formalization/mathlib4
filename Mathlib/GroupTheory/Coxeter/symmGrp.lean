import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.GroupTheory.Coxeter.Basic

namespace CoxeterSystem

noncomputable section

open Equiv

variable (n : ℕ)

def M := CoxeterMatrix.Aₙ n

def cs := (M n).toCoxeterSystem

abbrev Cox (n : ℕ) := (M n).Group

abbrev S (n : ℕ) := Equiv.Perm (Fin n)

instance : Group (S (n + 1)) := Perm.permGroup

def f_simple : Fin n → S (n + 1) :=
  fun i => swap i.castSucc i.succ

lemma cycle_of_adjacent_swap (i j : Fin n) (hij : i ≠ j)
    (h1 : j.succ = i.castSucc ∨ i.succ = j.castSucc) :
    Perm.IsThreeCycle (swap i.castSucc i.succ * swap j.castSucc j.succ) := by
  rcases h1 with h1 | h1
  · rw[h1]
    rw[Equiv.swap_comm j.castSucc i.castSucc]
    apply Equiv.Perm.isThreeCycle_swap_mul_swap_same
    · rw[← h1]
      apply (Fin.succ_inj.ne).mpr hij.symm
    · apply (Fin.castSucc_inj.ne).mpr hij
    · intro h
      simp[Fin.ext_iff] at h
      simp[Fin.ext_iff] at h1
      rw[← h1] at h
      omega
  · rw[h1]
    rw[Equiv.swap_comm i.castSucc j.castSucc]
    apply Equiv.Perm.isThreeCycle_swap_mul_swap_same
    · apply (Fin.castSucc_inj.ne).mpr hij.symm
    · rw[← h1]
      apply (Fin.succ_inj.ne).mpr hij
    · intro h
      simp[Fin.ext_iff] at h
      simp[Fin.ext_iff] at h1
      rw[h] at h1
      omega

theorem f_liftable : (M n).IsLiftable (f_simple n) := by
  intro i j
  simp[M, CoxeterMatrix.Aₙ]
  by_cases heq : i = j
  · simp [heq, f_simple]
  · simp [f_simple]

    simp[heq]

    by_cases h1 : j.succ = i.castSucc ∨ i.succ = j.castSucc
    · have h1' :  (j.val + 1 = i.val ∨ i.val + 1 = j.val) := by
        simp[Fin.ext_iff] at h1
        tauto
      rw[if_pos h1']
      have hcycle := cycle_of_adjacent_swap n i j heq h1
      obtain ⟨ho , _ ⟩ := (orderOf_eq_iff (by omega)).mp (Equiv.Perm.IsThreeCycle.orderOf hcycle)
      exact ho
    · have h1' : ¬ (j.val + 1 = i.val ∨ i.val + 1 = j.val) := by
        simp[Fin.ext_iff] at h1
        simp[h1]

      rw[if_neg h1']
      apply Equiv.ext_iff.mpr
      intro k
      simp only [pow_succ]

      rcases not_or.mp h1 with ⟨ h1, h2 ⟩

      have h3 : ¬ (i.castSucc = j.castSucc) := by
        apply Fin.castSucc_inj.ne.mpr heq
      have h4 : ¬ (i.succ = j.succ) := by
        apply Fin.succ_inj.ne.mpr heq

      rw[← ne_eq] at h1 h2 h3 h4

      have h_disjoint : Equiv.Perm.Disjoint (Equiv.swap i.castSucc i.succ)
          (Equiv.swap j.castSucc j.succ) := by
        intro k
        apply or_iff_not_imp_left.mpr
        intro h
        rcases Equiv.eq_or_eq_of_swap_apply_ne_self h with h | h
        apply Equiv.swap_apply_of_ne_of_ne
        repeat
          simp[h, heq, h1, h2, h3, h4, h1.symm, h2.symm, h3.symm, h4.symm]
        apply Equiv.swap_apply_of_ne_of_ne h2 h4

      nth_rewrite 2 [Equiv.Perm.Disjoint.commute h_disjoint]
      simp

  def f := lift (cs n) ⟨ f_simple n, f_liftable n ⟩

theorem f_apply_simple (i : Fin n) : f n ((cs n).simple i) = Equiv.swap i.castSucc i.succ := by
  apply lift_apply_simple (cs n)

theorem f_surjective : Function.Surjective (f n) := by
  apply MonoidHom.mrange_eq_top.mp
  apply eq_top_iff.mpr
  have : Submonoid.closure (Set.range fun (i : Fin n) ↦ Equiv.swap i.castSucc i.succ) = ⊤ := by
    exact Equiv.Perm.mclosure_swap_castSucc_succ n
  simp [← this]
  intro p hp
  simp at hp ⊢
  rcases hp with ⟨ i, rfl ⟩
  use (cs n).simple i
  simp [f_apply_simple]

def f_equiv : (Cox n) ≃* S (n + 1) := by
  apply MulEquiv.ofBijective (f n)
  constructor
  · sorry
  · exact f_surjective n

theorem f_equiv_apply_simple (i : Fin n) :
    (f_equiv n) ((cs n).simple i) = Equiv.swap i.castSucc i.succ := by
  simp[f_equiv, f_apply_simple]

def S_cox : CoxeterSystem (M n) (S (n + 1)) := ⟨ (f_equiv n).symm ⟩

theorem S_cox_simple (i : Fin n) : (S_cox n).simple i = (Equiv.swap i.castSucc (i.succ)) := by
  rw[← f_equiv_apply_simple]
  rfl

end

end CoxeterSystem

instance Nat.Semigroup : Semigroup Nat where
  mul_assoc := Nat.mul_assoc

instance Nat.MulOneClass : MulOneClass Nat where
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one

instance : Monoid Nat where
  __ := Nat.Semigroup
  __ := Nat.MulOneClass
