import GaloisForLFunctions.HTGeometry.GomesFockTaylorGauge
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt.CompatibleTowers

/-!
# Compatible derivative and translation towers on finite jets

A finite jet has no nonzero tower of successive antiderivatives inside the
same jet space: the derivative is uniformly nilpotent. Taylor translation
has one backward tower through every jet, obtained by translating by `-nz`.
These are the nilpotent and invertible alternatives of the inverse-limit
argument used for Tate modules.
-/

noncomputable section
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

open ArithmeticHodgeTheoryOfDegenerations.HodgeWitt

theorem fockShiftLinear_pow_apply (N n : ℕ) (x : Fin N → ℂ) :
    (fockShiftLinear N ^ n) x = shiftOp^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, ih, Function.iterate_succ_apply]
      rfl

/-- Uniform nilpotence excludes every nonzero compatible antiderivative tower. -/
theorem fockDerivative_backwardOrbit_eq_zero (N : ℕ)
    (x : backwardOrbits (fockShiftLinear N)) : x = 0 := by
  apply (backwardOrbits_uniform_torsion_iff (fockShiftLinear N) x N).mp
  intro n
  rw [fockShiftLinear_pow_apply, shiftOp_iterate_eq_zero]

/-- The existing Taylor translation, bundled as a linear automorphism. -/
def fockTaylorEquiv (N : ℕ) (z : ℂ) : (Fin N → ℂ) ≃ₗ[ℂ] (Fin N → ℂ) :=
  LinearEquiv.ofLinear (Matrix.toLin' (fockTaylorMatrix N z))
    (Matrix.toLin' (fockTaylorMatrix N (-z)))
    (by
      apply LinearMap.ext
      intro x
      change fockTaylorMatrix N z *ᵥ (fockTaylorMatrix N (-z) *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, (fockTaylorMatrix_inverse N z).1, Matrix.one_mulVec])
    (by
      apply LinearMap.ext
      intro x
      change fockTaylorMatrix N (-z) *ᵥ (fockTaylorMatrix N z *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, (fockTaylorMatrix_inverse N z).2, Matrix.one_mulVec])

/-- Evaluation at zero classifies all compatible Taylor towers. -/
def fockTaylorTowerEquiv (N : ℕ) (z : ℂ) :
    backwardOrbits (fockTaylorEquiv N z).toLinearMap ≃ₗ[ℂ] (Fin N → ℂ) :=
  backwardOrbitsEquiv (fockTaylorEquiv N z)

theorem fockTaylorEquiv_pow_apply (N n : ℕ) (z : ℂ) (x : Fin N → ℂ) :
    ((fockTaylorEquiv N z).toLinearMap ^ n) x =
      fockTaylorMatrix N (n • z) *ᵥ x := by
  induction n with
  | zero => simp only [pow_zero, Module.End.one_apply, zero_smul,
      fockTaylorMatrix_zero, Matrix.one_mulVec]
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      change fockTaylorMatrix N z *ᵥ (fockTaylorMatrix N (n • z) *ᵥ x) = _
      rw [Matrix.mulVec_mulVec, ← fockTaylorMatrix_add, succ_nsmul']

/-- Every inverse translation orbit has the explicit parameter `-nz`. -/
theorem fockTaylor_backwardOrbit_formula (N : ℕ) (z : ℂ)
    (x : backwardOrbits (fockTaylorEquiv N z).toLinearMap) (n : ℕ) :
    x.1 n = fockTaylorMatrix N (-(n • z)) *ᵥ x.1 0 := by
  have h := congrArg (fun y : backwardOrbits (fockTaylorEquiv N z).toLinearMap => y.1 n)
    ((fockTaylorTowerEquiv N z).symm_apply_apply x)
  have hp : ((fockTaylorEquiv N (-z)).toLinearMap ^ n) (x.1 0) = x.1 n := h
  rw [fockTaylorEquiv_pow_apply, smul_neg] at hp
  exact hp.symm

#print axioms fockDerivative_backwardOrbit_eq_zero
#print axioms fockTaylorTowerEquiv
#print axioms fockTaylor_backwardOrbit_formula

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
