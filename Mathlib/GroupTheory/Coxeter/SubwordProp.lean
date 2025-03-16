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

theorem chainProp (h : u < v) : ∃ p : List cs.Group,
  (Chain' (covby cs) p ∧ p.head? = some u ∧ p.getLast? = some v) := by
  generalize hn : ℓ u + ℓ v = n
  revert u v
  induction' n with n ih
  · intro u v h1 h2
    have : ℓ v = 0 := by linarith
    have h1 := length_lt_of_lt cs h1; rw [this] at h1; tauto
  · intro u v hlt h0
    have lvpos : 0 < ℓ v := Nat.zero_lt_of_lt (length_lt_of_lt cs hlt)
    rcases cs.exists_rightDescent_of_ne_one (ne_one_of_gt cs hlt) with ⟨i, hi⟩
    rcases (isRightDescent_iff_exist_reduced_word_getLast_eq cs).1 hi with ⟨l1, h1⟩
    rcases subword_of_le cs h1.2.1 h1.1 (le_of_lt hlt) with ⟨l2, h2⟩
    by_cases h : u < u * s i
    · have : ℓ (u * s i) = ℓ u + 1 := ((lt_simple_mul_iff cs i u).1 h).symm
      have := chainaux cs hlt hi (cs.not_isRightDescent_iff.2 this)
      by_cases h3 : u = v * s i
      · have llu : ℓ u + 1 = ℓ v := by rw [←cs.isRightDescent_iff.1 hi, h3]
        exact ⟨[u, v], by simp [covby]; exact ⟨hlt, llu⟩⟩
      · have ultvs : u < v * s i := lt_of_le_of_ne this h3
        have lcond : ℓ u + ℓ (v * s i) = n := by
          have := (cs.isRightDescent_iff).1 hi
          calc
            _ = ℓ u + (ℓ (v * s i) + 1 - 1) := rfl
            _ = ℓ u + ℓ v - 1 := by rw [this, Nat.add_sub_assoc lvpos]
            _ = _ := by rw [h0]; rfl
        obtain ⟨l3, hl3⟩ := ih ultvs lcond
        use (l3.concat v)
        simp [covby, List.chain'_append] at *
        exact ⟨⟨hl3.1, by
          intro x hx; simp [hl3.2.2] at hx; rw [←hx];
          exact ⟨(simple_mul_lt_iff cs i v).2 hi, cs.isRightDescent_iff.1 hi⟩⟩, by simp [hl3.2.1]⟩
    · sorry
    -- · replace h : u * s i < u :=
    --     (or_iff_right h ).1 <| mul_reflection cs u (cs.isReflection_simple i)
    --   have h3 : ℓ (u * s i) = ℓ u - 1 :=
    --     Nat.eq_sub_of_add_eq <| cs.isRightDescent_iff.1 ((simple_mul_lt_iff cs i u).1 h)
    --   have h4 : 1 ≤ ℓ u := Nat.one_le_of_lt (length_lt_of_lt cs h)
    --   have lcond : ℓ (u * s i) + ℓ v = n := by rw [h3, ←Nat.sub_add_comm h4, h0]; simp
    --   obtain ⟨l3, hl3⟩ := ih (h.trans hlt) lcond
    --   set p : Fin l3.length → Prop := fun ind => (l3[ind] * s i < l3[ind])
    --   classical
    --   obtain ⟨l4, hl4⟩ := List.getLast?_eq_some_iff.1 hl3.2.2
    --   have : l4.length < l3.length := by rw [hl4, length_append, length_singleton]; norm_num
    --   obtain ⟨l5, hl5⟩ := List.head?_eq_some_iff.1 hl3.2.1
    --   let ind := Fin.find p
    --   have h5 : ind.isSome := by
    --     rw [Fin.isSome_find_iff]
    --     use ⟨l4.length, this⟩
    --     simp [p]; rw [show l3[l4.length] = v by simp [hl4]]
    --     exact mul_lt_of_IsRightInversion cs ⟨cs.isReflection_simple i, hi⟩
    --   have h6 : (0 : ℕ) < ind.get h5 := by
    --     by_contra!
    --     have : (ind.get h5).1 = 0 := by linarith
    --     have tmp : ind = some ⟨0, by linarith⟩ :=
    --       Option.eq_some_iff_get_eq.2 ⟨h5, Fin.ext_iff.2 this⟩
    --     have : ¬p ⟨0, by linarith⟩ := by simp [p, hl5]; exact (simple_mul_iff cs i u).1 h
    --     exact this (Fin.find_eq_some_iff.1 tmp).1
    --   set ii := ind.get h5 with hii
    --   have hii' : ind = some ii := by simp [hii]
    --   have h7 : ∀ j, j < ii → l3[j] < l3[j] * s i := by
    --     intro j hj; by_contra!; replace this : l3[j] * s i < l3[j] :=
    --       (or_iff_left this).1 (simple_mul cs i l3[j])
    --     have :=  (Fin.find_eq_some_iff.1 hii').2 j this
    --     exact (not_le_of_lt hj) this
    --   have aux8 : ii - 1 < l3.length := (Nat.sub_one_lt (show ii.1 ≠ 0 by linarith)).trans ii.2
    --   have h8 : l3[ii] = l3[ii.1 - 1] * s i := by
    --     simp; have := List.chain'_iff_get.1 hl3.1 (ii - 1)
    --       (Nat.sub_lt_sub_right (Nat.add_one_le_of_lt h6) ii.is_lt )
    --     simp [covby, (Nat.add_one_le_of_lt h6)] at this
    --     by_contra! h8
    --     have h9 : l3[ii.1 - 1] < l3[ii.1 - 1] * s i := h7 ⟨ii - 1, aux8⟩ (by simp [Fin.lt_def, h6])
    --     have h10 := (liftingProp' cs this.1 this.2
    --       (cs.not_isRightDescent_iff.2 ((lt_simple_mul_iff cs i _).1 h9 ).symm) h8.symm).1
    --     have := (Fin.find_eq_some_iff.1 hii').1; simp [p] at this
    --     exact (simple_mul_iff cs i _).1 this h10
    --   have h9 : ∀ j < ii, 0 < j.1 → l3[j.1 - 1] * s i < l3[j] * s i := by
    --     intro j hj hj'
    --     have h1 : j.1 - 1 < l3.length - 1 := (lt_of_lt_of_le (show j.1 - 1 < ii.1 by
    --       exact lt_of_le_of_lt (Nat.sub_le j.1 1) (Fin.lt_def.1 hj)) (Nat.le_sub_one_of_lt ii.2))
    --     have := List.chain'_iff_get.1 hl3.1 (j.1 - 1) h1
    --     simp [covby, Nat.add_one_le_iff.2 hj'] at this
    --     have h3 := h7 ⟨j.1 - 1, h1.trans (Nat.sub_one_lt (Nat.not_eq_zero_of_lt aux8))⟩
    --         (Fin.lt_def.2 <| lt_of_le_of_lt (Nat.sub_le j.1 1) (Fin.lt_def.1 hj))
    --     have h2 : l3[j.1 - 1] * s i ≠ l3[j] := by
    --       intro h11; have := h7 j hj; simp [←h11] at this
    --       simp at h3; exact lt_asymm this h3
    --     have := liftingProp' cs this.1 this.2
    --       (by simp [IsRightDescent]; exact _root_.le_of_lt (length_lt_of_lt cs h3)) h2
    --     exact this.2
    --   use (l3.take ii.1).map (· * s i) ++ (l3.drop (ii.1 + 1))
    --   constructor
    --   · simp  [ List.chain'_iff_get]
    --     intro j hj
    --     replace hj : j < l3.length - 2 := by
    --       calc
    --         _ < ii + (l3.length - (ii + 1)) - 1 := hj
    --         _ = _ := by
    --           rw [←Nat.add_sub_assoc, Nat.add_comm, Nat.sub_add_eq]; simp [Nat.sub_sub]
    --           exact Nat.add_one_le_of_lt ii.2
    --     by_cases hjj : j + 1 < ii
    --     · have h1 : j + 1 < ((l3.map (· * s i)).take ii ).length := by simpa [length_take]
    --       have h2 : j < ((l3.map (· * s i)).take ii ).length :=
    --         (show j < j + 1 by linarith).trans h1
    --       rw [getElem_append_left h2, getElem_append_left h1, getElem_take', getElem_take']
    --       simp; have h3 := h9 ⟨j + 1, hjj.trans ii.2⟩ (Fin.lt_def.2 hjj); simp at h3
    --       have h4 := ((lt_simple_mul_iff cs i _).1 <| h7 ⟨j + 1, hjj.trans ii.2⟩ (Fin.lt_def.2 hjj))
    --       have h5 := ((lt_simple_mul_iff cs i _).1 <| h7 ⟨j, (show j < j + 1 by linarith).trans
    --         (hjj.trans ii.2)⟩ (Fin.lt_def.2 (by linarith)))
    --       simp at h4 h5
    --       have := List.chain'_iff_get.1 hl3.1 j (Nat.lt_sub_of_add_lt (hjj.trans ii.2))
    --       simp [covby] at this
    --       exact ⟨h3, by rw [←h4, ←h5, this.2] ⟩
    --     · by_cases hjj' : j + 1 = ii
    --       · have h1 : j < ((l3.map (· * s i)).take ii ).length := by
    --           simp [length_take]; rw [←hjj']; linarith
    --         rw [getElem_append_left h1, getElem_take']; simp [hjj']
    --         rw [List.getElem_append_right' (by simp [length_take]) ]; simp
    --         have h2 : l3[j] * s i = l3[j + 1] := by
    --           simp [Nat.eq_sub_of_add_eq hjj', Nat.sub_add_cancel (Nat.add_one_le_of_lt h6)]
    --           exact h8.symm
    --         have := List.chain'_iff_get.1 hl3.1 (j + 1)
    --           (by apply Nat.add_lt_of_lt_sub; simpa [Nat.sub_sub])
    --         simp [covby] at this; simp [←hjj',]; rwa [h2]
    --       · replace hjj' : ii.1 < j + 1 :=
    --           lt_of_le_of_ne (le_of_not_lt hjj) (by exact fun a ↦ hjj' (id a.symm))
    --         by_cases h1 : j = ii.1
    --         · simp [h1, List.getElem_append_right']
    --           have := List.chain'_iff_get.1 hl3.1 (ii.1 + 1)
    --             (by apply Nat.add_lt_of_lt_sub; simp [Nat.sub_sub]; rwa [←h1])
    --           simp [covby] at this; exact this
    --         · have h1 : ii.1 < j := lt_of_le_of_ne (Nat.le_of_lt_add_one hjj') (by simp [h1];tauto)
    --           rw [List.getElem_append_right' (by simp [length_take]; linarith)]
    --           rw [List.getElem_append_right' (by simp [length_take]; linarith)]
    --           have h2 : ii.1 + 1 + (j - ii.1) = j + 1 := by
    --             rw [←Nat.add_sub_assoc (_root_.le_of_lt h1), add_rotate, Nat.add_sub_cancel]; abel
    --           have h3 : ii.1 + 1 + (j + 1 - ii.1) = j + 2 := by
    --             rw [←Nat.add_sub_assoc (_root_.le_of_lt (h1.trans (by linarith))), add_rotate,
    --                Nat.add_sub_cancel]; ring
    --           simp [h2, h3]
    --           have := List.chain'_iff_get.1 hl3.1 (j + 1)
    --             (by apply Nat.add_lt_of_lt_sub; simpa [Nat.sub_sub])
    --           simp [covby] at this; exact this
    --   · constructor
    --     · have : map (· * s i) (take (ii.1) l3) ≠ [] := by
    --         intro h; rw [List.map_eq_nil, List.take_eq_nil_iff] at h; contrapose! h
    --         exact ⟨Nat.pos_iff_ne_zero.1 h6, by simp [hl4]⟩
    --       rw [List.head?_append_of_ne_nil ((l3.take ii.1).map (· * s i)) this]
    --       simp [List.head?_take, Nat.pos_iff_ne_zero.1 h6]
    --       exact ⟨u * s i, ⟨hl3.2.1, by simp⟩ ⟩
    --     · by_cases h1 : ii.1 + 1 = l3.length
    --       · simp [List.drop_eq_nil_iff_le, h1, List.getLast?_take, Nat.pos_iff_ne_zero.1 h6]
    --         left; use l3[ii.1 - 1]; simp
    --         have h2 : ii.1 = l3.length - 1 := Nat.eq_sub_of_add_eq h1
    --         have : l3[ii.1] = v := by simp [h2, hl4]
    --         rw [←this]; exact h8.symm
    --       · have : ii.1 + 1 < l3.length := lt_of_le_of_ne (Nat.add_one_le_iff.2 ii.2) (by simp [h1])
    --         simp; left; simp [List.getLast?_drop, not_le_of_lt this, hl3.2.2]

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

lemma covby_iff (u v : cs.Group): u ⋖ v ↔ covby cs u v := by
  simp [CovBy, covby]
  intro hlt
  constructor <;> intro h
  · contrapose! h
    obtain ⟨p, hp⟩ := chainProp cs hlt
    obtain ⟨inl, h1⟩ := List.head?_getLast?_eq_some hp.2.1 hp.2.2 (ne_of_lt hlt)
    have h2 : inl ≠ [] := by intro h2; simp [h2] at h1; simp [h1] at hp; exact h hp.2
    obtain ⟨x, l', h3⟩ := exists_cons_of_ne_nil h2
    rw [h3] at h1
    have h4 : Chain' (· < ·) p := Chain'_lt_of_Chain'_covby cs hp.1
    simp [h1, List.chain'_iff_pairwise] at h4
    exact ⟨x, ⟨h4.1.1, by simp [h4.2.1] ⟩ ⟩
  · intro c hc
    replace hc := h ▸ Nat.add_one_le_of_lt <| length_lt_of_lt cs hc
    exact fun h => (not_le_of_lt (length_lt_of_lt cs h) hc)

noncomputable instance : GradeOrder ℕ cs.Group where
  grade := cs.length
  grade_strictMono := fun _ _ h => length_lt_of_lt cs h
  covBy_grade := fun _ _ h => (by rw [covby_iff, covby ] at h; simp [←h.2])

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
