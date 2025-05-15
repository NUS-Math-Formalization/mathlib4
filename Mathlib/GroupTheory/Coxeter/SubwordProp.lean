import Mathlib.GroupTheory.Coxeter.Bruhat
import Mathlib.Order.Grade

variable {B : Type}
variable {W : Type} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable {l : List B} {t : W}
variable {u v : cs.Group}


open CoxeterSystem  List Relation
open Classical (choose choose_spec)

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length
local prefix:100 "ris" => cs.rightInvSeq
local prefix:100 "lis" => cs.leftInvSeq

set_option maxHeartbeats 250000
namespace Bruhat

section SubwordProp

variable {ω l l' : List B}

/-- If ` lt_adj W u v `, then exists reduced word of u is subword of reduced word of v. -/
lemma subword_of_lt_adj (veq : v = π ω) (h : lt_adj cs u v) :
  ∃ ω' : List B, (cs.IsReduced ω' ∧ u = π ω') ∧ ω'.Sublist ω := by
    obtain ⟨ ⟨t, vut⟩, llt⟩ := h
    have vtu : v * t = u := by rw [←IsReflection.inv vut.1, vut.2]; group
    rw [←vtu, veq] at llt
    obtain ⟨ l, ⟨h1, ⟨i, hi⟩ ⟩ ⟩ := StrongExchange cs vut.1 llt
    by_cases lred : IsReduced cs l
    · refine ⟨l, ⟨⟨lred, by rw [h1, ←veq, vtu]⟩, ?_ ⟩⟩
      rw [hi]; exact eraseIdx_sublist ω i.1
    · let ll      := choose <| DeletionExchange' cs lred
      let ll_spec := choose_spec <| DeletionExchange' cs lred
      refine  ⟨ll, ⟨?_ , ?_ ⟩⟩
      · exact ⟨ll_spec.2.2, by rw [←vtu, ll_spec.2.1, h1, ←veq]⟩
      · exact ll_spec.1.trans (by rw [hi]; exact eraseIdx_sublist ω i.1)

/-- If u < v, then exists reduced word of u is subword of reduced word of v. -/
lemma subword_of_lt (veq : v = π ω) (h : u < v)  : ∃ ω' : List B,
  (IsReduced cs ω' ∧ u = π ω') ∧ ω'.Sublist ω := by
    induction h  generalizing ω with
    | @single b hub => exact subword_of_lt_adj cs veq hub
    | @tail b c _ hbc ih =>
      have := subword_of_lt_adj cs veq hbc
      obtain ⟨l2, ⟨ll2, h2⟩ ⟩ := this
      obtain ⟨l1, ⟨ll1, h1⟩ ⟩ := ih  ll2.2
      exact ⟨l1, ⟨ll1, h1.trans h2⟩⟩

/-- If u ≤ v, then exists reduced word of u is subword of reduced word of v. -/
theorem subword_of_le (veq : v = π ω) (wred : cs.IsReduced ω) : u ≤ v →
  ∃ ω' : List B, (IsReduced cs ω' ∧ u = π ω') ∧ ω'.Sublist ω := by
    intro hle
    induction hle with
    | refl => exact ⟨ω, ⟨wred, veq⟩, by simp⟩
    | @tail b v hab hbc _ =>
      have : u < v := Relation.TransGen.tail' hab hbc
      exact subword_of_lt cs veq this

lemma le_of_subword (hl' : IsReduced cs l') (hsub : l <+ l') :
   toCoxeterGroup cs (π l) ≤ toCoxeterGroup cs (π l') := by
    simp [toCoxeterGroup]
    generalize h : l'.length = nl
    revert l l'
    induction' nl with n hn
    · intro l l' _ hsub h
      have : l = [] := by
        rw [List.length_eq_zero.1 h] at hsub
        exact eq_nil_of_sublist_nil hsub
      simp [this]
    · intro l l' hl' hsub hll'
      by_cases hlast : l.getLast? = l'.getLast?
      · have := hn (isReduced_dropLast cs hl')
          (List.dropLast_sublist_dropLast hsub) (by rw [length_dropLast, hll']; norm_num)
        have l'nnil : l' ≠ [] := ne_nil_of_length_eq_add_one hll'
        have lnnil : l ≠ [] := by
            by_contra lnil
            rw [List.getLast?_eq_getLast l' l'nnil, List.getLast?_eq_none_iff.2 lnil] at hlast
            tauto
        rcases (mul_simpleRefl_le_of_le cs (l'.getLast l'nnil) this) with hll | hrr <;>
          rw [List.getLast?_eq_getLast l' l'nnil, List.getLast?_eq_getLast l lnnil,
            Option.some_inj] at hlast
        · rw [←hlast, wordProd_dropLast cs lnnil] at hll
          simp at hll
          exact le_trans hll (dropLast_le cs hl')
        · nth_rw 1 [←hlast] at hrr
          rw [wordProd_dropLast cs lnnil, wordProd_dropLast cs l'nnil] at hrr
          simp at hrr
          assumption
      · have subdropLast := hn (isReduced_dropLast cs hl')
          (List.sublist_dropLast hsub hlast) (by rw [length_dropLast, hll']; norm_num)
        exact le_trans subdropLast (dropLast_le cs hl')

end SubwordProp


lemma inv_le_inv_of_le (hlt : u ≤ v) : u⁻¹ ≤ v⁻¹ := by
  rcases exists_reduced_word' cs v with ⟨lv, hlv⟩
  rcases subword_of_le cs hlv.2 hlv.1 hlt with ⟨lu, hlu⟩
  have := le_of_subword cs (IsReduced.reverse hlv.1) (reverse_sublist.2 hlu.2)
  simp [toCoxeterGroup] at this
  rwa [hlu.1.2, hlv.2]

lemma inv_le_inv_iff (u v : cs.Group) : u⁻¹ ≤ v⁻¹ ↔ u ≤ v := ⟨fun h => by
  convert inv_le_inv_of_le cs h <;> simp, fun h => inv_le_inv_of_le cs h⟩

lemma inv_lt_inv_iff (u v : cs.Group) : u⁻¹ < v⁻¹ ↔ u < v := by
  simp [lt_iff_le_and_ne, lt_iff_le_and_ne]
  exact fun _ => inv_le_inv_iff cs _ _

lemma mul_reflection {t : W} (u : cs.Group) (ht : cs.IsReflection t) : u < u * t ∨ u * t < u := by
  by_cases h : ℓ u < ℓ (u * t)
  · exact Or.inl <| (lt_reflection_mul_iff_length_lt cs _ ht).2 h
  · have := IsReflection.length_mul_left_ne ht u
    push_neg at h
    have isRis : cs.IsRightInversion u t := ⟨ht, Nat.lt_of_le_of_ne h this⟩
    exact Or.inr <| mul_lt_of_IsRightInversion cs isRis

lemma reflection_mul {t : W} (ht : cs.IsReflection t) : u < t * u ∨ u > t * u := by
  convert mul_reflection cs u⁻¹ ht using 1
  · convert (inv_lt_inv_iff cs u (t * u)).symm using 2; simp [IsReflection.inv ht]
  · have := (inv_lt_inv_iff cs (t * u) u)
    simp; rw [←this]; simp [IsReflection.inv ht]

lemma liftingProp {i : B} (hlt : u < v) (h1 : cs.IsRightDescent v i) (h2 : ¬ cs.IsRightDescent u i)
  : u ≤ v * s i ∧ u * s i ≤ v := by
    obtain ⟨l', hl'⟩ := (isRightDescent_iff_exist_reduced_word_getLast_eq cs).1 h1
    obtain ⟨l, hl⟩ := subword_of_lt cs hl'.2.1 hlt
    have := (not_isRightDescent_iff_reduced_word_getLast_not_eq cs).1 h2 l hl.1
    have : l <+ l'.dropLast := List.sublist_dropLast hl.2 <| hl'.2.2 ▸ this
    constructor
    · have := le_of_subword cs (isReduced_dropLast cs hl'.1) this
      rw [hl.1.2, hl'.2.1, ←dropLast_append_getLast? i hl'.2.2, wordProd_append]
      simpa
    · have : l ++ [i] <+ l' := by
        rw [←dropLast_append_getLast? i hl'.2.2]
        exact List.sublist_append_iff.2 ⟨l, [i], ⟨rfl, ⟨this, Sublist.refl [i]⟩⟩⟩
      have := le_of_subword cs hl'.1 this
      rwa [hl.1.2, ←wordProd_singleton, ←wordProd_append, hl'.2.1]

lemma liftingProp' {i : B} (hlt : u < v) (leq : ℓ u + 1 = ℓ v) (hllt : ¬ cs.IsRightDescent u i)
  (neq : u * s i ≠ v) : v < v * s i ∧ u * s i < v * s i := by
    have := mul_simpleRefl_le_of_le cs i (le_of_lt hlt)
    have lfalse : ¬ u * s i ≤ v := by
      rw [←cs.not_isRightDescent_iff.1 hllt] at leq
      exact fun h => neq (eq_of_le_of_length_ge cs h (by linarith))
    rw [or_iff_right lfalse] at this
    have lneq : ℓ (u * s i) ≠ ℓ (v * s i) := length_mul_simple_ne_of_parity_ne cs (s i)
      (fun h => (by rw [←Nat.ModEq, Nat.modEq_iff_dvd, ←leq] at h; simp at h; tauto))
    have right := lt_of_le_of_length_lt cs this (Nat.lt_of_le_of_ne (length_le_of_le cs this) lneq)
    have llt : ℓ v < ℓ (v * s i) := by calc
        _ = ℓ (u * s i) := by rw [←leq, cs.not_isRightDescent_iff.1 hllt]
        _ < _ := length_lt_of_lt cs right
    exact ⟨(lt_reflection_mul_iff_length_lt cs _ (cs.isReflection_simple i)).2 llt, right⟩

section chainProp

variable {l : List cs.Group}

@[simp]
def covby : cs.Group → cs.Group → Prop := fun u v => u < v ∧ ℓ u + 1 = ℓ v

lemma covby.WellFounded : WellFounded (covby cs) := by
  refine WellFounded.intro ?h
  intro a
  generalize ha : ℓ a = n
  revert a
  induction' n with n ih <;> intro a ha
  · apply Acc.intro
    intro y hy; simp [covby, ha] at hy;
  · exact Acc.intro (r := covby cs) a (fun y hy => ih y (by simp [covby, ha] at hy; exact hy.2))

lemma chainaux {i : B} (h : u < v) (h1 : cs.IsRightDescent v i) (h2 : ¬ cs.IsRightDescent u i) :
    u ≤ v * s i := by
      rcases (isRightDescent_iff_exist_reduced_word_getLast_eq cs).1 h1 with ⟨l, hl⟩
      obtain ⟨l', hl'⟩ := subword_of_le cs hl.2.1 hl.1 (_root_.le_of_lt h)
      have : l'.getLast? ≠ l.getLast? := by
        rw [hl.2.2]
        exact (not_isRightDescent_iff_reduced_word_getLast_not_eq cs).1 h2 l' hl'.1
      have hsub := List.sublist_dropLast hl'.2 this
      have := le_of_subword cs (isReduced_dropLast cs hl.1) hsub
      simp at this
      rwa [hl'.1.2, hl.2.1, ←wordProd_dropLast? cs hl.2.2]

def uvChain' {α : Type} (r : α → α → Prop) : α → α → List α → Prop :=
  fun u v l => (Chain' r l ∧ l.head? = some u ∧ l.getLast? = some v)

lemma Chain'_lt_of_Chain'_covby (h : Chain' (covby cs) l) : Chain' (· < ·) l :=
  List.Chain'.imp (fun _ _ h => h.1) h

lemma List.head?_getLast?_eq_some {α : Type} {a b : α} {l : List α} (h1 : l.head? = some a)
  (h2 : l.getLast? = some b) (h : a ≠ b): ∃ inl : List α, l = a :: inl.concat b:= by
    obtain ⟨tail, ih⟩ := List.head?_eq_some_iff.1 h1
    have : tail ≠ [] := by intro h3; simp [h3, ih] at *; exact h h2
    obtain ⟨inl, x, h3⟩ := (or_iff_right this).1 (List.eq_nil_or_concat tail)
    simp [h3] at ih
    simp [ih, List.getLast?_concat, List.getLast?_cons] at h2
    simp [h2] at ih
    exact ⟨inl, by convert ih; simp⟩

lemma chain_of_length_diff_eq_one (h : u < v) (h1 : ℓ u + 1 = ℓ v)
  (h2 : uvChain' (covby cs) u v l) : l = [u, v] := by
    obtain ⟨inl, h3⟩ := List.head?_getLast?_eq_some h2.2.1 h2.2.2 (ne_of_lt h)
    have h4 : inl = [] := by
      by_contra!
      obtain ⟨x, l', h5⟩ := List.exists_cons_of_ne_nil this
      simp [h5] at h3; simp [h3] at h2
      have h6 := Chain'_lt_of_Chain'_covby cs h2.1
      simp [List.chain'_iff_pairwise] at h6
      have h7 : u < x ∧ x < v := ⟨h6.1.1, by simp [h6.2.1]⟩
      have h8 : ℓ u < ℓ x ∧ ℓ x < ℓ v := ⟨length_lt_of_lt cs h7.1, length_lt_of_lt cs h7.2⟩
      have := Nat.add_one_le_of_lt h8.1
      simp [h1] at this
      exact not_le_of_lt h8.2 this
    simp [h4] at h3
    exact h3

end chainProp

lemma isRightDescent_iff' (i : B) : cs.IsRightDescent u i ↔ ¬ cs.IsRightDescent (u * s i) i := by
  simp [IsRightDescent]
  constructor <;> intro h
  · exact Nat.le_of_succ_le h
  · exact Nat.lt_of_le_of_ne h <| cs.length_mul_simple_ne u i

instance : IsDirected cs.Group (· ≤ ·) where
  directed := by
    intro a b
    generalize h : ℓ a + ℓ b = n
    revert a b
    induction' n with n ih <;> intro a b hn
    · have := Nat.add_eq_zero_iff.1 hn
      have ha : a = 1 := cs.length_eq_zero_iff.1 this.1
      have hb : b = 1 := cs.length_eq_zero_iff.1 this.2
      simp [ha, hb]
    · wlog h1 : (0 < ℓ a) generalizing a b
      · have h2 : 0 < ℓ b := by linarith
        have := this b a (by linarith) h2
        tauto
      · have ne1 : a ≠ 1 := cs.length_eq_zero_iff.not.1 (Nat.pos_iff_ne_zero.1 h1)
        obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one ne1
        have : ℓ (a * s i) + ℓ b = n := by
          have : ℓ (a * s i) + 1 = ℓ a := cs.isRightDescent_iff.1 hi
          linarith
        obtain ⟨c, hc⟩ := ih (a * s i) b this
        by_cases hci : cs.IsRightDescent c i
        · have : a * s i ≠ c := by
            contrapose! hci
            rw [←hci]
            exact (isRightDescent_iff' cs i).1 hi
          have := (liftingProp cs (lt_of_le_of_ne hc.1 this) hci ((isRightDescent_iff' cs i).1 hi))
          simp at this
          exact ⟨c, ⟨this.2, hc.2⟩ ⟩
        · have : a * s i < c * s i := lt_of_le_of_lt hc.1
            ((lt_simple_mul_iff cs i c).2 <| (cs.not_isRightDescent_iff.1 hci).symm)
          have hcii : cs.IsRightDescent (c * cs.simple i) i := by
            have := ((isRightDescent_iff' cs i).not.1 hci); tauto
          have naii : ¬cs.IsRightDescent (a * s i) i := (isRightDescent_iff' cs i).1 hi
          have := liftingProp cs this hcii naii
          simp at this
          have leci : c ≤ c * s i := by
            rw [not_isRightDescent_iff] at hci
            exact le_of_lt <| (lt_simple_mul_iff cs i c).2 hci.symm
          exact ⟨c * s i, ⟨this.2, hc.2.trans leci⟩ ⟩

end Bruhat
