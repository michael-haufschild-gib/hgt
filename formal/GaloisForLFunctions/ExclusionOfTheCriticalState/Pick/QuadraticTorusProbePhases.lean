import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeZeroPhaseSensitivity
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Quadratic-torus coordinates for the zero-reflection phase

The conjugation quotient of Braverman–Kazhdan, Lemma 2.2(2)
(arXiv:2604.11735), identifies complex units modulo real units with
the circle. Pullback of the actual zero-coordinate phase action yields
an exact projective overlap formula in the real determinant of two
complex representatives.
-/

noncomputable section
open scoped ComplexConjugate
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open ArithmeticCastelnuovoSeveri Zeta23

/-- The orientation conj(z)/z on the real quadratic torus. -/
def conjugationPhase : ℂˣ →* Circle where
  toFun z := Circle.ofConjDivSelf z z.ne_zero
  map_one' := Subtype.ext (by simp [Circle.ofConjDivSelf])
  map_mul' z w := Subtype.ext (by
    change conj ((z : ℂ) * w) / ((z : ℂ) * w) = (conj z / z) * (conj w / w)
    rw [map_mul, div_mul_div_comm])

/-- Every phase has an explicit lift: 1+conj(u) away from -1 and i at -1. -/
theorem conjugationPhase_surjective : Function.Surjective conjugationPhase := by
  intro u
  by_cases h : (u : ℂ) = -1
  · refine ⟨Units.mk0 Complex.I Complex.I_ne_zero, Subtype.ext ?_⟩
    change conj Complex.I / Complex.I = u
    rw [h, Complex.conj_I, neg_div, div_self Complex.I_ne_zero]
  · have hne : 1 + conj (u : ℂ) ≠ 0 := by
      intro hz
      apply h
      have he := congrArg (starRingEnd ℂ) hz
      simpa only [map_add, map_one, Complex.conj_conj, map_zero, add_eq_zero_iff_neg_eq] using he
    refine ⟨Units.mk0 _ hne, Subtype.ext ?_⟩
    change conj (1 + conj (u : ℂ)) / (1 + conj (u : ℂ)) = u
    rw [div_eq_iff hne, map_add, map_one, Complex.conj_conj, mul_add, mul_one,
      Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one, add_comm]

/-- The kernel consists exactly of embedded nonzero real scalars. -/
theorem conjugationPhase_kernel :
    conjugationPhase.ker = (Units.map Complex.ofRealHom.toMonoidHom).range := by
  ext z
  change conjugationPhase z = 1 ↔ ∃ r : ℝˣ, Units.map _ r = z
  constructor
  · intro h
    have he := congrArg (fun u : Circle => (u : ℂ)) h
    change conj (z : ℂ) / z = 1 at he
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp ((div_eq_one_iff_eq z.ne_zero).mp he)
    have hn : r ≠ 0 := fun h0 => z.ne_zero (by rw [hr, h0, Complex.ofReal_zero])
    exact ⟨Units.mk0 r hn, Units.ext hr.symm⟩
  · rintro ⟨r, rfl⟩
    apply Subtype.ext
    change conj ((r : ℝ) : ℂ) / ((r : ℝ) : ℂ) = 1
    rw [Complex.conj_ofReal, div_self (Complex.ofReal_ne_zero.mpr r.ne_zero)]

/-- Quotient by real units parametrizes the phase group without a branch of argument. -/
def realTorusPhaseEquiv : ℂˣ ⧸ (Units.map Complex.ofRealHom.toMonoidHom).range ≃* Circle :=
  (QuotientGroup.quotientMulEquivOfEq conjugationPhase_kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ conjugationPhase_surjective)

/-- Two representatives yield the same phase exactly on the same real projective line. -/
theorem conjugationPhase_eq_iff (z w : ℂˣ) :
    conjugationPhase z = conjugationPhase w ↔ ∃ r : ℝˣ, Units.map Complex.ofRealHom.toMonoidHom r * w = z := by
  rw [← div_eq_one, ← map_div]
  change z / w ∈ conjugationPhase.ker ↔ _
  rw [conjugationPhase_kernel]
  exact exists_congr fun r => (eq_div_iff_mul_eq)

/-- Homogeneous real determinant of the two representatives. -/
def phaseDeterminant (z w : ℂˣ) : ℝ :=
  (z : ℂ).re * (w : ℂ).im - (z : ℂ).im * (w : ℂ).re

private theorem conjugate_cross (z w : ℂˣ) :
    conj (z : ℂ) * w - conj (w : ℂ) * z = (2 * (phaseDeterminant z w : ℂ)) * Complex.I := by
  apply Complex.ext <;>
    simp only [phaseDeterminant, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat] <;> ring

/-- The phase chord length is twice the sine of the unoriented angle between representatives. -/
theorem conjugationPhase_chord (z w : ℂˣ) :
    ‖(conjugationPhase z : ℂ) - (conjugationPhase w : ℂ)‖ =
      2 * |phaseDeterminant z w| / (‖(z : ℂ)‖ * ‖(w : ℂ)‖) := by
  change ‖conj (z : ℂ) / z - conj (w : ℂ) / w‖ = _
  rw [div_sub_div _ _ z.ne_zero w.ne_zero, conjugate_cross, norm_div, norm_mul,
    norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  norm_num

/-- Pullback of the probe phase action to complex units. -/
def torusProbeAction : ℂˣ →* (ZeroSpace ≃ₗᵢ[ℂ] ZeroSpace) :=
  phaseRepresentation.comp conjugationPhase

/-- Pullback realizes every reflection phase on every vector simultaneously. -/
theorem torusProbeAction_range : torusProbeAction.range = phaseRepresentation.range := by
  ext T
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨conjugationPhase z, rfl⟩
  · rintro ⟨u, rfl⟩
    obtain ⟨z, rfl⟩ := conjugationPhase_surjective u
    exact ⟨z, rfl⟩

/-- All Hilbert-space projective losses factor through normalized real area and the two sector masses. -/
theorem torusProbe_projective_loss (z w : ℂˣ) (x : ZeroSpace) :
    ‖x‖ ^ 4 - ‖inner ℂ (torusProbeAction z x) (torusProbeAction w x)‖ ^ 2 =
      positiveMass x * negativeMass x *
        (2 * |phaseDeterminant z w| / (‖(z : ℂ)‖ * ‖(w : ℂ)‖))^2 := by
  rw [← conjugationPhase_chord]
  exact phaseRotate_projective_loss _ _ _

/-- An off-line zeta coordinate distinguishes exactly the real projective classes of lifts. -/
theorem zeroBasis_torus_indistinguishable_iff (ρ : zetaZeroConfig.carrier) (z w : ℂˣ) :
    1 - ‖inner ℂ (torusProbeAction z (zeroBasis ρ)) (torusProbeAction w (zeroBasis ρ))‖^2 = 0 ↔
      (ρ : ℂ).re = 1/2 ∨ ∃ r : ℝˣ, Units.map Complex.ofRealHom.toMonoidHom r * w = z :=
  (zeroBasis_projective_loss_zero_iff _ _ _).trans (or_congr_right' (conjugationPhase_eq_iff z w))

end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
