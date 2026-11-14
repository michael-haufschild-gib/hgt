import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt.CompatibleTowers
import Mathlib.RingTheory.Artinian.Module

/-!
# Finite groups have zero Tate towers

Every coordinate of a compatible division tower lies both in the nilpotent
part and the stable image of multiplication by `p`. Fitting decomposition
makes their intersection zero when the underlying group is finite.
This separates finite primary torsion from the infinite divisible torsion
that supports nonzero Tate modules.
-/

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt

variable (p : ℕ) (A : Type*) [AddCommGroup A]

/-- Multiplication by `p` as an integral linear endomorphism. -/
def tateTransition : Module.End ℤ A := p • LinearMap.id

theorem tateTransition_pow_apply (r : ℕ) (x : A) :
    (tateTransition p A ^ r) x = p ^ r • x := by
  induction r with
  | zero => simp only [pow_zero, Module.End.one_apply, one_smul]
  | succ r ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      change p • (p ^ r • x) = p ^ (r + 1) • x
      rw [← mul_smul, ← pow_succ']

/-- A finite abelian group has no nonzero compatible tower of primary division points. -/
theorem finite_tateTower_eq_zero [Finite A] (x : tateTower p A) : x = 0 := by
  have hd := (isCompl_iff.mp
    (LinearMap.isCompl_iSup_ker_pow_iInf_range_pow (tateTransition p A))).1
  apply Subtype.ext
  funext n
  apply Submodule.disjoint_def.mp hd (x.1 n)
  · apply (le_iSup (fun r : ℕ => LinearMap.ker (tateTransition p A ^ r)) n)
    change (tateTransition p A ^ n) (x.1 n) = 0
    rw [tateTransition_pow_apply]
    exact x.2.2 n
  · apply (Submodule.mem_iInf _).mpr
    intro r
    refine ⟨x.1 (n + r), ?_⟩
    rw [tateTransition_pow_apply]
    exact tateTower_pow_smul p x r n

#print axioms finite_tateTower_eq_zero

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt
