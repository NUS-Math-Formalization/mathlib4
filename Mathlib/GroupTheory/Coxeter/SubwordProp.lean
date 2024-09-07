import Mathlib.GroupTheory.Coxeter.inversion
import Mathlib.Order.Interval.Basic
import Init.Data.List.Lemmas


open CoxeterSystem  List Relation
open Classical (choose choose_spec)


variable {B : Type}
variable {W : Type} [Group W]
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

lemma mul_simpleRefl_lt_adj {b v : cs.Group} (i : B) (h : lt_adj cs b v) :
  b * (s i) ≤ v ∨ b * (s i) ≤ v * (s i) := by
    rcases h.1 with ⟨t,h1⟩
    by_cases h2 : s i = t
    · rw [←h2] at h1; rw [h1.2]; exact Or.inl (le_refl _)
    · have blev := (le_of_lt cs (TransGen.single h))
      by_cases h3 : cs.IsRightInversion b (s i)
      · have h31 : b * cs.simple i < b := mul_lt_of_IsRightInversion cs h3
        exact Or.inl (le_trans (le_of_lt cs h31) blev)
      · right
        let t' : cs.Group := s i * t * s i
        have heq : b * s i * t' = b * t * s i := by
          simp [t']; rw [mul_assoc]; group; simp
        have IsReflt': cs.IsReflection t' := by
          have := (CoxeterSystem.isReflection_conj_iff cs (s i) t).2 h1.1
          rwa [inv_simple] at this
        have lbslvs : ℓ (b * s i) < ℓ (v * s i) := by
          by_contra! hh
          by_cases hlt : ℓ (v * s i) < ℓ (b * s i)
          · rw [h1.2, ←heq] at hlt
            let  redword_b := choose <| cs.exists_reduced_word' b
            have redword_bspec := choose_spec (cs.exists_reduced_word' b)
            let redword_bsi := redword_b ++ [i]
            have redword_bsieq : π redword_bsi = b * s i := by
              simp_rw [redword_bsi, wordProd_append, wordProd_singleton]; rw [redword_bspec.2]
            rw [←redword_bsieq] at hlt
            rcases StrongExchange cs IsReflt' hlt with ⟨ll', ⟨heq', ⟨i', hi'⟩ ⟩ ⟩
            rw [redword_bsieq, heq, ←h1.2] at heq'
            by_cases hdel_id : i' = redword_bsi.length - 1 <;> simp [redword_bsi] at *
            · have : ll' = redword_b := by
                rw [hi', hdel_id, eraseIdx_append_of_length_le (le_of_eq rfl)]
                simp
              rw [this, ←redword_bspec.2, h1.2, mul_assoc] at heq'
              have : s i = t := by
                nth_rw 1 [←mul_one b] at heq'
                have := mul_left_cancel heq'
                rw [←simple_sq cs i, pow_two] at this
                exact mul_right_cancel this
              exact h2 this
            · have hi'lt : i'.1 < redword_b.length := by
                push_neg at hdel_id
                have := Fin.is_lt i'
                simp [redword_bsi] at this
                have : i'.1 ≤ redword_b.length  := Nat.le_of_lt_succ this
                exact Nat.lt_of_le_of_ne this hdel_id
              rw [List.eraseIdx_append_of_lt_length hi'lt _] at hi'
              rw [hi', wordProd_append, wordProd_singleton] at heq'
              have : cs.wordProd (redword_b.eraseIdx ↑i') = v := by
                rw [←mul_one v, ←simple_sq cs i, pow_two, ←mul_assoc, ←heq']; simp
              have hcontra := cs.length_wordProd_le (redword_b.eraseIdx i')
              rw [this, length_eraseIdx hi'lt] at hcontra
              have hcontra' : ℓ b < ℓ v := h.2
              rw [←redword_bspec.1, ←redword_bspec.2] at hcontra
              have : ℓ v < ℓ v  := by
                calc
                  _ ≤ ℓ b - 1 := hcontra
                  _ ≤ ℓ v - 1 := Nat.sub_le_sub_right (_root_.le_of_lt h.2) 1
                  _ < ℓ v :=Nat.sub_one_lt_of_lt hcontra'
              linarith
          · have : ℓ (v * s i) = ℓ (b * s i) := by push_neg at hlt; linarith
            rw [h1.2, ←heq] at this
            exact CoxeterSystem.IsReflection.length_mul_left_ne IsReflt' (b * s i) this
        have : lt_adj cs (b * s i) (v * s i) := by
          rw [←h1.2] at heq
          exact ⟨⟨t', ⟨IsReflt', heq.symm⟩ ⟩, lbslvs⟩
        exact le_of_lt cs (TransGen.single this)

lemma mul_simpleRefl_le_of_le (i : B) (h : u ≤ v) : u * (s i) ≤ v ∨ u * (s i) ≤ v * (s i) := by
  induction h with
  | refl => exact Or.inr (le_refl _)
  | @tail b v hub hbv ih =>
    have blev := (le_of_lt cs (TransGen.single hbv ))
    cases mul_simpleRefl_lt_adj cs i hbv with
    | inl hl => cases ih with
      | inl hll => exact Or.inl (le_trans hll blev)
      | inr hrr => exact Or.inl (le_trans hrr hl)
    | inr hr => cases ih with
      | inl hll => exact Or.inl (le_trans hll blev)
      | inr hrr => exact Or.inr (le_trans hrr hr)

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

def toCoxeterGroup : W → cs.Group := id

lemma List.dropLast_sublist_dropLast {α : Type} {l l' : List α} (hsub : l <+ l')
  : l.dropLast <+ l'.dropLast := by
    revert l
    induction' l' with a ll' ih
    · intro _ hsub ; simp at *; rw [hsub]; simp
    · intro l hsub
      cases sublist_cons_iff.1 hsub with
      | inl hl =>
        by_cases ll'nil : ll' = []
        · simp [ll'nil] at *; simp [hl]
        · rw [List.dropLast_cons_of_ne_nil ll'nil]
          exact (ih hl).trans (sublist_cons_self a _)
      | inr hr =>
        rcases hr with ⟨r,hr⟩
        by_cases rnil : r = []
        · rw [rnil] at hr; rw [hr.1]; simp
        · have ll'nnil : ll' ≠ [] := by
            contrapose! rnil; rw [rnil] at hr; exact sublist_nil.1 hr.2
          have := ih hr.2
          rw [hr.1, dropLast_cons_of_ne_nil rnil, dropLast_cons_of_ne_nil ll'nnil]
          exact Sublist.cons₂ a this

lemma List.sublist_dropLast {α : Type} {l l' : List α} (hsub : l <+ l')
  (hlast : ¬l.getLast? = l'.getLast?) : l <+ l'.dropLast := by
    revert l
    induction' l' with a ll' hll' <;> intro l hsub hlast
    · simp; exact sublist_nil.1 hsub
    · by_cases ll'nil : ll' = []
      · simp [ll'nil] at *
        exact Or.elim hsub (fun hl => hl) (fun hr => by simp [hr] at hlast)
      · rw [getLast?_eq_getLast (a :: ll') (by simp), getLast_cons ll'nil,
          ←getLast?_eq_getLast _ ll'nil] at hlast
        cases sublist_cons_iff.1 hsub with
        | inl hl => exact (hll' hl hlast).trans (by simp [dropLast_cons_of_ne_nil ll'nil])
        | inr hr =>
          rcases hr with ⟨r, hr⟩
          by_cases rnil : r = []
          · simp [rnil] at *; rw [hr, dropLast_cons_of_ne_nil ll'nil]; simp
          · rw [hr.1, getLast?_eq_getLast (a :: r) (by simp), getLast_cons rnil,
              ←getLast?_eq_getLast _ rnil] at hlast;
            rw [hr.1, dropLast_cons_of_ne_nil ll'nil]
            exact Sublist.cons₂ a (hll' hr.2 hlast)

lemma isReduced_dropLast {ω : List B} (hω : cs.IsReduced ω) :
  cs.IsReduced ω.dropLast := by
  rw [dropLast_eq_take]
  exact isReduced_take cs hω (ω.length - 1)

lemma dropLast_le {l : List B} (h : cs.IsReduced l) :
  toCoxeterGroup cs (π l.dropLast) ≤ toCoxeterGroup cs (π l) := by
    simp [toCoxeterGroup]
    by_cases tri : l = []
    · simp [tri]
    · have : ℓ (π l.dropLast) < ℓ (π l) := by
        rw [h, dropLast_eq_take, cs.isReduced_take h, length_take]; simp; exact length_pos.2 tri
      nth_rw 2 [←dropLast_concat_getLast tri] at *
      rw [wordProd_append, wordProd_singleton] at *
      exact le_of_lt cs
        ((lt_reflection_mul_iff_length_lt cs (cs.isReflection_simple (l.getLast tri))).2 this)

lemma le_of_subword (hl : IsReduced cs l) (hl' : IsReduced cs l') (hsub : l <+ l') :
   toCoxeterGroup cs (π l) ≤ toCoxeterGroup cs (π l') := by
    simp [toCoxeterGroup]
    generalize h : l'.length = nl
    revert l l'
    induction' nl with n hn
    · intro l l' _ _ hsub h
      have : l.length = 0 := by have := List.Sublist.length_le hsub; linarith
      have : l = [] := length_eq_zero.mp this
      simp [this]
      exact one_le cs
    · intro l l' hl hl' hsub hll'
      by_cases hlast : l.getLast? = l'.getLast?
      · have := hn (isReduced_dropLast cs hl) (isReduced_dropLast cs hl')
          (List.dropLast_sublist_dropLast hsub) (by rw [length_dropLast, hll']; norm_num)
        have l'nnil : l' ≠ [] := ne_nil_of_length_eq_add_one hll'
        have lnnil : l ≠ [] := by
            by_contra lnil
            rw [List.getLast?_eq_getLast l' l'nnil, List.getLast?_eq_none_iff.2 lnil] at hlast
            tauto
        rcases (mul_simpleRefl_le_of_le cs (l'.getLast l'nnil) this) with hll | hrr <;>
          rw [List.getLast?_eq_getLast l' l'nnil, List.getLast?_eq_getLast l lnnil,
            Option.some_inj] at hlast
        · rw [←wordProd_singleton, ←wordProd_append,
            ←hlast, l.dropLast_append_getLast lnnil] at hll
          exact le_trans hll (dropLast_le cs hl')
        · nth_rw 1 [←hlast] at hrr
          rw [←wordProd_singleton, ←wordProd_append, ←wordProd_singleton, ←wordProd_append] at hrr
          rwa [l.dropLast_append_getLast lnnil, l'.dropLast_append_getLast l'nnil] at hrr
      · have subdropLast := hn hl (isReduced_dropLast cs hl')
          (List.sublist_dropLast hsub hlast) (by rw [length_dropLast, hll']; norm_num)
        exact le_trans subdropLast (dropLast_le cs hl')

end SubwordProp

section otherProperty
#check Interval
/--Bruhat interval is finite because of Subword property. -/
-- lemma Interval.finite : sorry := sorry

abbrev BruhatInterval := NonemptyInterval W

def listInterval := {ω : List B | l <+ ω ∧ ω <+ l'}

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
