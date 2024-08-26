import Mathlib.GroupTheory.Coxeter.inversion
import Mathlib.Order.Interval.Basic

open CoxeterSystem  List Relation
open Classical (choose choose_spec)


variable {B : Type*}
variable {W : Type} [Group W] [IsCoxeterGroup W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable {l : List B} {t : W}

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length
local prefix:100 "ris" => cs.rightInvSeq
local prefix:100 "lis" => cs.leftInvSeq

section StrongExchange

@[simp]
lemma nilIsReduced : cs.IsReduced [] := by simp [IsReduced]

@[simp]
lemma singletonIsReduced (h : l.length = 1) : cs.IsReduced l := by
  simp [IsReduced, h, length_eq_one_iff,List.length_eq_one]
  have := List.length_eq_one.1 h
  obtain ⟨a, ha⟩ := this
  exact ⟨a, by rw [ha]; simp⟩

lemma StrongExchange {l : List B} (ht : cs.IsReflection t) : ℓ (π l * t) < ℓ π l →
  ∃ l' : List B, π l' = π l * t ∧ ∃ i : Fin l.length, l' = l.eraseIdx i := by
    sorry

lemma StrongExchange' {l : List B} (ht : cs.IsReflection t) : ℓ (t * π l) < ℓ π l →
  t ∈ lis l := sorry

/-- If l is not a reduced word of w but a experssion, there exist a subword of l is also a
  expression of w. -/
lemma DeletionExchange {l : List B} (h : ¬IsReduced cs l) :
  ∃ i : Fin l.length, ∃ j : Fin i, π l = π (l.eraseIdx j).eraseIdx i := sorry

private lemma DeletionExchange_aux {l : List B} (h : ¬IsReduced cs l) :
  ∃ l', l' <+ l ∧ π l' = π l ∧ l'.length + 2 = l.length := sorry

/-- If l is not a reduced word of w but a experssion, there must exist a subword of l which
  is reduced word of w. -/
lemma DeletionExchange' {l : List B} (h : ¬IsReduced cs l) :
  ∃ l' : List B, l' <+ l ∧ π l' = π l ∧ IsReduced cs l' := by
  generalize hl : l.length = n
  revert l h
  induction' n using Nat.twoStepInduction with n h1 _ <;> intro l h llsucc
  · have : l = [] := List.eq_nil_of_length_eq_zero llsucc
    rw [this] at h
    exact (h <| nilIsReduced cs).elim
  · exact (h (singletonIsReduced cs llsucc)).elim
  · obtain ⟨ll, hll⟩ := DeletionExchange_aux cs h
    have lll : ll.length = n := by linarith
    by_cases hh : IsReduced cs ll
    · exact ⟨ll, ⟨hll.1, ⟨hll.2.1, hh⟩ ⟩⟩
    · obtain ⟨ll', hll'⟩ := h1 hh lll
      exact ⟨ll', ⟨hll'.1.trans hll.1, ⟨hll'.2.1.trans hll.2.1, hll'.2.2⟩ ⟩ ⟩

-- lemma llt_of_not_reduced {l : List B} {w : W} (hw : w = π l) (nred : ¬IsReduced cs l) :
--   ℓ w < l.length := sorry

end StrongExchange

abbrev CoxeterSystem.Group (_ : CoxeterSystem M W) := W

variable {u v : cs.Group}

namespace Bruhat

section definition


def lt_adj  : W → W → Prop := fun u v =>
  (∃ t, cs.IsReflection t ∧ v = u * t) ∧ ℓ u < ℓ v

def lt_adj' : W → W → Prop := fun u v =>
  (∃ t, cs.IsReflection t ∧ v = t * u) ∧ ℓ u < ℓ v

/-- `lt` is the transitive closure of `lt_adj` -/
def lt := Relation.TransGen <| lt_adj (cs := cs)

/-- `lt'` is the transitive closure of `lt_adj'` -/
def lt' := Relation.TransGen <| lt_adj' (cs := cs)

/-- The left Bruhat order is equivalent to the right Bruhat order since `lt_adj` is
  equivalent to ` lt_adj' `-/
lemma lt_adj_iff_lt_adj' : lt_adj cs u v ↔ lt_adj' cs u v := by
  constructor <;> rintro ⟨⟨t, vut⟩, llt⟩
  · have : cs.IsReflection (u * t * u⁻¹):=
      IsReflection.conj vut.1 u
    exact ⟨⟨u * t * u⁻¹, by simpa⟩, llt⟩
  · have subt : cs.IsReflection (u⁻¹ * t * u) := by
      have := IsReflection.conj vut.1 u⁻¹
      simp at this
      assumption
    exact ⟨⟨u⁻¹ * t * u, ⟨subt, by group; exact vut.2⟩⟩, llt⟩

/-- `le` is the reflexive transitive closure of `lt_adj ` -/
def le := Relation.ReflTransGen <| lt_adj cs

/-- `le'` is the reflexive transitive closure of `lt_adj' ` -/
def le' := Relation.ReflTransGen <| lt_adj' cs

lemma length_lt_of_lt (hlt : lt cs u v) : ℓ u < ℓ v :=
  Relation.TransGen.trans_induction_on hlt (fun h => h.2) (fun _ _ h1 h2 => h1.trans h2)

lemma length_le_of_le (hle : le cs u v) : ℓ u ≤ ℓ v := by
  induction hle with
  | refl           => rfl
  | tail _ bltv ih => exact le_of_lt (lt_of_le_of_lt ih bltv.2)

lemma le_of_lt (h : lt cs u v) : le cs u v := reflTransGen_iff_eq_or_transGen.2 (Or.inr h)

lemma eq_of_le_of_length_ge (hle : le cs u v) (lle : ℓ v ≤ ℓ u) : u = v := by
    have : ¬Relation.TransGen (lt_adj cs) u v := by
      contrapose! lle; exact length_lt_of_lt cs lle
    exact ((or_iff_left this).1 (Relation.reflTransGen_iff_eq_or_transGen.1 hle)).symm

/-- The Bruhat order is the partial order on Coxeter group. -/
instance : PartialOrder cs.Group where
  lt               := lt cs
  le               := le cs
  le_refl          := fun _             => id Relation.ReflTransGen.refl
  le_trans         := fun _ _ _ ha hb  => Relation.ReflTransGen.trans ha hb
  le_antisymm      := fun a b ha hb => eq_of_le_of_length_ge cs ha (length_le_of_le cs hb)
  lt_iff_le_not_le := by
    intro a b;
    constructor <;> intro h
    · exact ⟨TransGen.to_reflTransGen h, fun hh => by
        linarith [length_le_of_le cs hh, length_lt_of_lt cs h]⟩
    · exact Or.elim (reflTransGen_iff_eq_or_transGen.1 h.1) (right := fun a ↦ a)
        (fun hh => (False.elim <| h.2 <| reflTransGen_iff_eq_or_transGen.2 <| (Or.inl hh.symm)))

local infix : 100 "<ₗ" => lt' cs
local infix : 100 "≤ₗ" => le' cs

/-- Bruhat.lt is equivalent to Bruhat.lt' -/
lemma lt_iff_lt' : u < v ↔ u <ₗ v := by
  constructor <;> intro h
  · exact TransGen.mono (fun _ _ => (lt_adj_iff_lt_adj' cs).1) h
  · exact TransGen.mono (fun _ _ => (lt_adj_iff_lt_adj' cs).2) h

lemma le'_iff_lt'_or_eq : u ≤ₗ v ↔ u <ₗ v ∨ u = v := by
  have := @reflTransGen_iff_eq_or_transGen _ (lt_adj' cs) u v
  tauto

/-- Bruhat.le is equivalent to Bruhat.le' -/
lemma le_iff_le' : u ≤ v ↔ u ≤ₗ v := by
  constructor <;> intro h
  · have := le_iff_lt_or_eq.1 h
    rw [le'_iff_lt'_or_eq]
    exact Or.elim this (fun h1 => Or.inl <| (lt_iff_lt' cs).1 h1) (fun h2 => Or.inr h2)
  · exact Or.elim ((le'_iff_lt'_or_eq cs).1 h) (fun h1 => (le_of_lt cs) <| (lt_iff_lt' cs).2 h1)
      (fun h2 => reflTransGen_iff_eq_or_transGen.2 (Or.inl h2.symm))

lemma lt_of_le_of_length_lt : u ≤ v → ℓ u < ℓ v → u < v := fun h1 h2 =>
  (or_iff_right (by contrapose! h2; rw [h2])).1 <| reflTransGen_iff_eq_or_transGen.1 h1

/--If $t$ is the reflection of $W$, then $u < ut$ iff $\ell (u) < \ell (ut) $ -/
lemma lt_reflection_mul_iff_length_lt {t : W} (ht : cs.IsReflection t) :
  u < u * t ↔ ℓ u < ℓ (u * t) := by
    constructor <;> intro h
    · exact length_lt_of_lt cs h
    · exact (Relation.transGen_iff (lt_adj cs) u (u * t)).2 (Or.inl ⟨⟨t, ⟨ht, rfl⟩⟩, h⟩)

lemma mul_lt_of_IsRightInversion {t : W} (ht : cs.IsRightInversion u t) : u * t < u :=
  TransGen.single ⟨⟨t, ⟨ht.1, by rw [mul_assoc, IsReflection.mul_self ht.1, mul_one]⟩⟩, ht.2⟩

lemma mul_lt'_of_IsLeftInversion {t : W} (ht : cs.IsLeftInversion u t) : (t * u) <ₗ u :=
  TransGen.single ⟨⟨t, ⟨ht.1, by rw [←mul_assoc, IsReflection.mul_self ht.1, one_mul]⟩⟩, ht.2⟩

/-- $\forall u \in W$, if $ u \ne 1$, then $1 < u$ -/
lemma one_lt_of_ne_one (h : u ≠ 1) : 1 < u := by
  generalize h1 : ℓ u = n
  revert u
  induction' n with n ih
  · intro u h hu
    exact False.elim <| h <| cs.length_eq_zero_iff.1 <| hu
  · intro u h hu
    by_cases hh : n = 0
    · rw [hh] at hu
      obtain ⟨i, hi⟩ := (cs.length_eq_one_iff).1 hu
      exact TransGen.single ⟨ ⟨s i, ⟨cs.isReflection_simple i, by rw [hi,one_mul]⟩ ⟩,
      by simp;linarith⟩
    · obtain ⟨i, hi⟩ := exists_rightDescent_of_ne_one cs h
      have h1  : ℓ (u * s i) = n := by linarith [cs.isRightDescent_iff.1 hi]
      have ne1 : u * s i ≠ 1 := by
        have := cs.length_mul_ge_length_sub_length u (s i)
        simp only [length_simple] at this
        apply (Iff.not cs.length_eq_zero_iff).1
        intro h
        rw [h1] at h
        tauto
      have := mul_lt_of_IsRightInversion cs
        ((cs.isRightInversion_simple_iff_isRightDescent u i).2 hi)
      exact (ih ne1 h1).trans this

/-- $\forall u \in W, 1 \leq u$  -/
lemma one_le : 1 ≤ u := by
  by_cases h : u = 1
  · rw [h]
  · exact le_of_lt cs (one_lt_of_ne_one cs h)

end definition

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

lemma sublist_cases {α : Type} [DecidableEq α] {l l' : List α} : l <:+: l' ∨
  ∃ n : Nat, (n < l.length) ∧ l[n]? ≠ l'[n]? := by
    by_cases h : l <:+: l'
    · exact Or.inl h
    · right
      contrapose! h
      sorry --exact Or.inr (by contrapose! h; rw [List.ext_get? h]; exact infix_refl l')

noncomputable def first_deleted_index {α : Type} [DecidableEq α] {l l' : List α}
  (h : ¬l <:+: l') := Nat.find ((or_iff_right h).1 sublist_cases)

lemma first_deleted_index_lt_length {α : Type} [DecidableEq α] {l l' : List α} (h : ¬l <:+: l')
  : first_deleted_index h < l.length := (Nat.find_spec ((or_iff_right h).1 sublist_cases)).1

lemma le_of_infix (hl : IsReduced cs l) (hl' : IsReduced cs l')
  (h : l <:+: l') : π l ≤ π l' := by
    sorry

private def expSet (l l' : List (indexOf W)) :=
  {ll //  π ll = π l ∧ IsReduced (csOf W) ll ∧ ll <+ l'}

private def self_mem_expSet {l l' : List (indexOf W)} (hl : IsReduced (csOf W) l)
  (hsub : l <+ l') : expSet l l' := ⟨l, ⟨rfl, ⟨hl, hsub⟩⟩ ⟩

private instance (l l' : List (indexOf W)) : Fintype (expSet l l') := by
  sorry

lemma le_of_subword_aux (hl : IsReduced (csOf W) l) (hl' : IsReduced (csOf W) l') (hsub : l <+ l')
  (h : ∀ ll : expSet l l', ¬ll.1 <:+: l')
    : ∃ ll, IsReduced (csOf W) ll ∧ ll <+ l' ∧ π l < π ll ∧ ll.length = l.length + 1 := by
      classical
      let f (ll : expSet l l') : ℕ := first_deleted_index (h ll)
      have ne  :  (Finset.univ.image f).Nonempty := sorry
      let imax := ((Finset.univ).image f).max' ne
      let lmax := choose <| Finset.mem_image.1 <| (Finset.max'_mem _ ne)
      have lltl' : l.length < l'.length := by
        have := length_le_of_sublist hsub
        by_cases lt' : l.length < l'.length
        · exact lt'
        · have : l.length = l'.length := by linarith
          have hh := infix_refl l
          nth_rw 2 [Sublist.eq_of_length hsub this] at hh
          exact False.elim <| (h ⟨l, ⟨rfl, ⟨hl, hsub⟩ ⟩ ⟩) hh
      have imaxlt : imax < (lis l').length := by
        exact (Finset.max'_lt_iff _ _).2 (fun y hy => (by
        rw [CoxeterSystem.length_leftInvSeq]
        have : y < l.length := by
          obtain ⟨prey, hpre⟩ := Finset.mem_image.1 hy
          have := first_deleted_index_lt_length (h prey)
          rw [←hpre.2, ←hl]
          rw [←prey.2.2.1, prey.2.1] at this
          exact this
        exact this.trans lltl'))
      let t    := (lis l').get ⟨imax, imaxlt⟩
      have tisRefl := (csOf W).isLeftInversion_of_mem_leftInvSeq hl' (t := t) (get_mem _ _ _)
      have lttl : π lmax.1 < t * π lmax.1 := by
        by_contra! gttl
        have lle : ℓ (t * π lmax.1) ≤ ℓ (π lmax.1) := by
          contrapose! gttl
          sorry
          --exact (mul_lt'_of_IsLeftInversion tisRefl).2 gttl
        have llt : ℓ (t * π lmax.1) < ℓ (π lmax.1) := sorry
        sorry
        --have := StrongExchange' (csOf W) tisRefl llt
        --obtain ⟨i, hi⟩ := List.mem_iff_get.1 this
        -- by_cases ilt : i < imax
        -- · sorry
        -- · sorry
        --#check StrongExchange
        --have := le_of_not_lt gttl
      sorry

lemma le_of_subword  (hl : IsReduced (csOf W) l) (hl' : IsReduced (csOf W) l') (hsub : l <+ l') :
  π l ≤ π l' := by
    by_cases h : ∃ ll : expSet l l', ll.1 <:+: l'
    · obtain ⟨ll, hll⟩ := h
      exact ll.2.1 ▸ le_of_infix ll.2.2.1 hl' hll
    · push_neg at h
      generalize ldiff : l'.length - l.length = n
      induction' n with n ih generalizing l
      · rw [Sublist.eq_of_length hsub
        (Nat.eq_iff_le_and_ge.2 ⟨Sublist.length_le hsub, Nat.sub_eq_zero_iff_le.1 ldiff⟩)]
      · let ll := choose <| le_of_subword_aux hl hl' hsub h
        let ll_spec := choose_spec <| le_of_subword_aux hl hl' hsub h
        by_cases hll : ∀ lll : expSet ll l', ¬lll.1 <:+: l'
        · have llle := ih ll_spec.1 ll_spec.2.1 hll (by
            rw [ll_spec.2.2.2, Nat.sub_add_eq, ldiff, Nat.add_sub_self_right])
          exact le_of_lt (lt_of_lt_of_le ll_spec.2.2.1 llle)
        · push_neg at hll
          let ll := (choose <| hll)
          have := le_of_infix ll.2.2.1 hl' (choose_spec <| hll)
          exact le_of_lt (lt_of_lt_of_le (ll.2.1.symm ▸ ll_spec.2.2.1) this)

theorem SubwordProp : u ≤ v ↔ ∀ ω, v = π ω ∧ IsReduced (csOf W) ω → ∃ ω',
  v = π ω' ∧ IsReduced (csOf W) ω' ∧ ω' <+ ω := sorry


end SubwordProp

section otherProperty
#check Interval
/--Bruhat interval is finite because of Subword property. -/
-- lemma Interval.finite : sorry := sorry

abbrev BruhatInterval := NonemptyInterval W

def listInterval := {ω : List (indexOf W) | l <+ ω ∧ ω <+ l'}

instance BruhatInterval.finite (H : BruhatInterval) : Fintype H := by
  -- have := sorry
  have : 0 < Nat.card H := sorry

  sorry

lemma inv_le_iff_le : u⁻¹ ≤ v⁻¹ ↔ u ≤ v := by sorry

theorem chainProp (hlt : u < v) : ∃ l : List W, Chain (· ⋖ ·) u (l.concat v) := sorry

lemma liftingProp {i : indexOf W} (hlt : u < v) (hirv : (csOf W).IsRightDescent v i)
  (nhiru : ¬(csOf W).IsRightDescent u i) : u ≤ s i * v ∧ s i * u ≤ v := sorry

instance : IsDirected W (· ≤ ·) where
  directed := sorry

end otherProperty

end Bruhat
