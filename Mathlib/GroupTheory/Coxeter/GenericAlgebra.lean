import Mathlib


variable {A B ε: Type} [CommRing A] [AddCommMonoid ε]
variable [Module A ε] [Module.Free A ε]
variable {W : Type} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable {l : List B} {t : W}

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length
local prefix:100 "ris" => cs.rightInvSeq
local prefix:100 "lis" => cs.leftInvSeq
#check Algebra


-- class GenAlg (A E : Type) [CommRing A] [AddCommMonoid E] [Module A E] [Module.Free A E] where
--   T : W ↪ E
--   a : B → A
--   b : B → A
--   Tmul : ∀ i : B, ∀ w : W, ℓ w < ℓ (s i * w) → T (s i) * T w = T (s i * w)
