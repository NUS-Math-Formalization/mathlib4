import Mathlib.GroupTheory.Coxeter.Bruhat
import Mathlib.GroupTheory.Coxeter.Hecke


variable {B : Type}
variable {W : Type} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable {l : List B} {t : W}

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length
local prefix:100 "ris" => cs.rightInvSeq
local prefix:100 "lis" => cs.leftInvSeq

open Classical CoxeterSystem Hecke

def Coxeter.wf : WellFoundedRelation cs.Group := measure cs.length

def adjl (u v : cs.Group) := ℓ u < ℓ v ∧ ∃ i : B, s i * u = v

lemma adjlIsWF : WellFounded (adjl cs) := by
  apply WellFounded.intro
  intro w
  apply CoxeterSystem.simple_induction_left cs w
  · refine Acc.intro 1 ?_
    intro y hy
    simp [adjl] at hy
  · intro w i hw
    sorry

#check WellFounded.fix

#check Hecke.T_simple_inv

noncomputable def Tinv.F (w : cs.Group) (h : ∀ u : cs.Group, adjl cs u w → cs.Hecke) : cs.Hecke := by
  by_cases w1 : w = 1
  · exact 1
  · let i := choose <| cs.exists_leftDescent_of_ne_one w1
    let hi := choose_spec <| cs.exists_leftDescent_of_ne_one w1
    have l1 : adjl cs (s i * w) w := by
      simp [CoxeterSystem.IsLeftDescent] at hi
      simp [adjl, i, hi]
      use i
      simp [i]
    exact h (s i * w) l1

noncomputable def inv : cs.Group → cs.Hecke := fun w => WellFounded.fix (adjlIsWF cs) (Tinv.F cs) w

lemma isLeftInv (w : cs.Group) : inv cs w * T cs w = 1 := by
  -- simp [inv]
  -- revert w
  -- let C : cs.Group → Prop := fun w => inv cs w * T cs w = 1
  -- apply WellFounded.induction (adjlIsWF cs) (C := C) w
  induction' w using WellFounded.induction with w ih
  · exact (Coxeter.wf cs).wf
  ·
   sorry

-- def inv_aux (l : List B) :

-- noncomputable def inv' (w : cs.Group) : cs.Hecke := sorry
