import Mathlib.GroupTheory.Coxeter.Bruhat
import Mathlib.Algebra.Polynomial.Laurent


variable {B : Type}
variable {W : Type} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable {l : List B} {t : W}

namespace CoxeterSystem

def Hecke := cs.Group →₀ (LaurentPolynomial ℤ)

end CoxeterSystem


namespace Hecke

open CoxeterSystem Bruhat

noncomputable def T : cs.Group → cs.Hecke := fun w => Finsupp.single w 1

end Hecke
-- def Hecke (G : Type*) [CoxeterGroup G] := G →₀ (LaurentPolynomial ℤ)

-- namespace Hecke

-- noncomputable def TT : G → Hecke G:= fun w => Finsupp.single w 1
