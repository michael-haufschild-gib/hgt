import GaloisForLFunctions.RHTower.DeningerWeightOnePolarization
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# On a complete carrier the polarized generator is bounded, so its spectrum cannot be the zeros

`DeningerWeightOnePolarization` takes `theta : Module.End ℂ H` — an **everywhere-defined** linear
endomorphism — and `shiftedTheta = theta - 1/2` is proved skew-symmetric for the Hodge metric
(`shiftedTheta_skewSymmetric`).  Multiplying a skew-symmetric operator by `I` produces a symmetric
one, and the Hellinger–Toeplitz theorem says an everywhere-defined symmetric operator on a
**complete** inner-product space is continuous.

Hence, whenever the carrier is complete:

* `theta` is continuous, so bounded;
* every eigenvalue of `theta` has modulus at most the operator norm.

The arithmetic realisation needs the eigenvalues of `theta` to be `1/2 + i·gamma` over **all** zeros
of zeta, whose imaginary parts are unbounded.  So no such realisation exists on a complete carrier.

This is not a defect of the package.  It is the reason the corpus's prescription *"nuclear cohomology
must be formed before Hilbert completion"* is not a matter of taste: on the completed space the
generator is forced bounded by a classical theorem, and the unbounded spectrum the arithmetic case
requires can only live on an **incomplete** pre-Hilbert carrier.  Completeness and the zeta spectrum
are incompatible, and the incompatibility is Hellinger–Toeplitz.
-/

noncomputable section

open scoped ComplexConjugate

namespace RHTower

namespace DeningerWeightOnePolarization

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `I · (theta - 1/2)` is symmetric: multiplying a skew-symmetric operator by `I` symmetrizes it. -/
theorem isSymmetric_I_smul_shiftedTheta (P : DeningerWeightOnePolarization H) :
    LinearMap.IsSymmetric ((Complex.I : ℂ) • P.shiftedTheta) := by
  intro x y
  have hskew := P.shiftedTheta_skewSymmetric x y
  show @inner ℂ H _ (Complex.I • P.shiftedTheta x) y
      = @inner ℂ H _ x (Complex.I • P.shiftedTheta y)
  rw [inner_smul_left, inner_smul_right, hskew, Complex.conj_I]
  ring

/-- **Hellinger–Toeplitz for the polarized generator.**  On a complete carrier `theta` is
continuous. -/
theorem theta_continuous [CompleteSpace H] (P : DeningerWeightOnePolarization H) :
    Continuous P.theta := by
  have hsym : Continuous ((Complex.I : ℂ) • P.shiftedTheta) :=
    (isSymmetric_I_smul_shiftedTheta P).continuous
  have hshift : Continuous (P.shiftedTheta : H → H) := by
    have h := hsym.const_smul (-(Complex.I : ℂ))
    refine h.congr fun x => ?_
    simp [LinearMap.smul_apply, smul_smul, Complex.I_mul_I]
  have hid : Continuous fun x : H => ((1 : ℂ) / 2) • x := continuous_const_smul _
  have := hshift.add hid
  refine this.congr fun x => ?_
  show P.shiftedTheta x + ((1 : ℂ) / 2) • x = P.theta x
  rw [shiftedTheta]
  simp

/-- **The spectrum of a polarized generator on a complete carrier is bounded.**  Every eigenvalue has
modulus at most the operator norm of `theta`. -/
theorem exists_eigenvalue_norm_bound [CompleteSpace H] (P : DeningerWeightOnePolarization H) :
    ∃ C : ℝ, ∀ (ρ : ℂ) (v : H), v ≠ 0 → P.theta v = ρ • v → ‖ρ‖ ≤ C := by
  have hcont := theta_continuous P
  set T : H →L[ℂ] H := ⟨P.theta, hcont⟩ with hT
  refine ⟨‖T‖, ?_⟩
  intro ρ v hv hev
  have hle : ‖T v‖ ≤ ‖T‖ * ‖v‖ := T.le_opNorm v
  have hTv : T v = ρ • v := hev
  rw [hTv, norm_smul] at hle
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  exact le_of_mul_le_mul_right (by linarith) hvpos

/-- **No complete carrier realises an unbounded spectrum.**  If the eigenvalues of `theta` are
unbounded in modulus then the carrier is not complete.  The zeta zeros have unbounded imaginary
part, so an arithmetic realisation must be pre-Hilbert. -/
theorem not_completeSpace_of_unbounded_spectrum
    (P : DeningerWeightOnePolarization H)
    (hunb : ∀ C : ℝ, ∃ (ρ : ℂ) (v : H), v ≠ 0 ∧ P.theta v = ρ • v ∧ C < ‖ρ‖) :
    ¬ CompleteSpace H := by
  intro hcomplete
  obtain ⟨C, hC⟩ := exists_eigenvalue_norm_bound P
  obtain ⟨ρ, v, hv, hev, hlt⟩ := hunb C
  exact absurd (hC ρ v hv hev) (not_le.mpr hlt)

end DeningerWeightOnePolarization

end RHTower
