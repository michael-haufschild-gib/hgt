import GaloisForLFunctions.ArithmeticPolarization.HeckeInvarianceOfTheCollidedPolarizationIsRH
import GaloisForLFunctions.ArithmeticPolarization.TheCollidedFormIsAPolarization
import GaloisForLFunctions.ArithmeticPolarization.ThePolarizationLaw
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFrobeniusSpanDefectCountsTheOuterEigenvalues
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheSplineOrbitDecidesTheCriticalLine
import GaloisForLFunctions.HeckeKreinToeplitz.TheFiniteIndexStratumOfZetaIsLindelofDeep

/-!
# Frobenius at infinity

Two pairings act on the zero divisor: the **collided pairing** `(ρ, ρ̄)`, in which every zero
meets its conjugate and which gives the positive collided form, and the **reflection pairing**
`(ρ, 1 − ρ)` of the functional equation, which gives Weil's form. Their composite is the **defect
involution** `σ(ρ) = 1 − ρ̄` (`defectInvolution`). A correspondence acting as conjugation on the
divisor — Frobenius at infinity — would identify the two pairings, i.e. make `σ` trivial.

* **`σ` fixes exactly the critical line** (`defectInvolution_eq_self_iff`): `ρ̄ = 1 − ρ` iff
  `Re ρ = 1/2`.
* **Frobenius at infinity exists on `ζ` iff RH** (`riemannHypothesis_iff_defectInvolution_trivial`).
* **The Hodge defect counts the moved zeros** (`negIndex_zetaKernel_eq_encard_moved`): `κ(K_ζ)` is
  the number of zeros moved by `σ` on the right half of the strip, one per `σ`-orbit.
* **Over `𝔽_q` Frobenius is the circle reflection** (`circleReflect_eq_self_iff`,
  `hermNegIndex_spanGram_eq_card_moved`): on Frobenius eigenvalues `σ` becomes `β ↦ 1/β̄` (in units of
  `√q`), it fixes exactly the unit circle, and from window `2g` on the Hodge defect is the number of
  eigenvalues it moves outside the circle.
* **Frobenius at infinity as a Hecke similitude** (`frobeniusAtInfinity_iff`): RH holds iff every
  Hecke translation is a similitude of the collided polarization, iff it leaves the collided form
  invariant (ArithmeticPolarization). Over `𝔽_q` the Frobenius leaves the collided form invariant iff
  the eigenvalues are unitary (`ArithmeticPolarization.ReflSpectrum.collided_frob_invariant_iff_unitary`).

So Frobenius at infinity is not an additional symmetry that could be constructed first and used
afterwards: its existence, as an involution on the divisor or as a Hecke similitude, is RH, and its
failure is measured exactly by the Hodge defect.
-/

noncomputable section

open Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.EdgeHodgeTheory

open Zeta23

/-- **The defect involution** `ρ ↦ 1 − ρ̄`: conjugation composed with the functional-equation
reflection. -/
def defectInvolution (ρ : ℂ) : ℂ := 1 - conj ρ

theorem defectInvolution_involutive : Function.Involutive defectInvolution := fun ρ => by
  simp [defectInvolution]

theorem re_defectInvolution (ρ : ℂ) : (defectInvolution ρ).re = 1 - ρ.re := by
  simp [defectInvolution]

theorem im_defectInvolution (ρ : ℂ) : (defectInvolution ρ).im = ρ.im := by
  simp [defectInvolution]

/-- **`σ` fixes exactly the critical line.** -/
theorem defectInvolution_eq_self_iff (ρ : ℂ) : defectInvolution ρ = ρ ↔ ρ.re = 1 / 2 := by
  constructor
  · intro h
    have := congrArg Complex.re h
    rw [re_defectInvolution] at this
    linarith
  · intro h
    apply Complex.ext
    · rw [re_defectInvolution, h]; norm_num
    · rw [im_defectInvolution]

/-- The collided partner is the reflection partner exactly on the critical line. -/
theorem conj_eq_one_sub_iff (ρ : ℂ) : conj ρ = 1 - ρ ↔ ρ.re = 1 / 2 := by
  rw [← defectInvolution_eq_self_iff, defectInvolution]
  constructor
  · intro h; rw [h]; ring
  · intro h; linear_combination -h

/-- **Frobenius at infinity exists on `ζ` iff RH.** -/
theorem riemannHypothesis_iff_defectInvolution_trivial :
    RiemannHypothesis ↔ ∀ ρ ∈ zetaZeroConfig.carrier, defectInvolution ρ = ρ := by
  rw [SquareRootThreshold.riemannHypothesis_iff_zetaZeroConfig_onLine]
  exact forall₂_congr fun ρ _ => (defectInvolution_eq_self_iff ρ).symm

/-- **The Hodge defect counts the moved zeros**: `κ(K_ζ)` is the number of zeros right of the line
moved by `σ`. -/
theorem negIndex_zetaKernel_eq_encard_moved :
    HeckeKreinToeplitz.negIndex HeckeKreinToeplitz.zetaKernel =
      {ρ ∈ zetaZeroConfig.carrier | defectInvolution ρ ≠ ρ ∧ 1 / 2 < ρ.re}.encard := by
  rw [HeckeKreinToeplitz.negIndex_zetaKernel]
  congr 1
  ext ρ
  simp only [ArithmeticCastelnuovoSeveri.rightZeros, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => by rw [defectInvolution_eq_self_iff] at h; linarith, h2⟩
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1, h2⟩

/-! ### Over `𝔽_q` -/

open ArithmeticCastelnuovoSeveri in
/-- **Over `𝔽_q` the defect involution is the circle reflection**, which fixes exactly the unit
circle. -/
theorem circleReflect_eq_self_iff {z : ℂ} (hz : z ≠ 0) :
    circleReflect z = z ↔ ‖z‖ = 1 := by
  constructor
  · intro h
    have hn := congrArg norm h
    rw [norm_circleReflect] at hn
    have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have : ‖z‖ * ‖z‖ = 1 := by
      calc ‖z‖ * ‖z‖ = ‖z‖⁻¹ * ‖z‖ := by rw [hn]
        _ = 1 := inv_mul_cancel₀ hpos.ne'
    nlinarith
  · exact circleReflect_of_norm_one

open ArithmeticCastelnuovoSeveri in
/-- From window `2g` on, the Hodge defect of a curve datum is the number of Frobenius eigenvalues
moved by the circle reflection outside the unit circle. -/
theorem hermNegIndex_spanGram_eq_card_moved {ι : Type*} [Fintype ι] (D : CurveDatum ι) {n : ℕ}
    (hn : Fintype.card ι ≤ n) :
    HTGeometry.hermNegIndex (D.spanGram n) =
      (D.spectrum.filter fun z => circleReflect z ≠ z ∧ 1 < ‖z‖).card := by
  rw [D.pontryagin_law_curve.2 n hn, CurveDatum.outerSpectrum]
  congr 1
  refine Finset.filter_congr fun z _ => ?_
  constructor
  · intro h
    refine ⟨fun h' => ?_, h⟩
    have hz : z ≠ 0 := fun h0 => by rw [h0, norm_zero] at h; linarith
    rw [circleReflect_eq_self_iff hz] at h'
    linarith
  · exact fun h => h.2

/-! ### Frobenius at infinity as a Hecke similitude -/

/-- **Frobenius at infinity.** RH holds iff the defect involution is trivial on the zeros of `ζ`,
iff every Hecke translation is a similitude of the collided polarization, iff every Hecke translation
leaves the collided form invariant. -/
theorem frobeniusAtInfinity_iff {L : ℝ} (hL : L ≠ 0) :
    (RiemannHypothesis ↔ ∀ ρ ∈ zetaZeroConfig.carrier, defectInvolution ρ = ρ) ∧
    (RiemannHypothesis ↔ ∃ c : ℝ, ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
        ArithmeticPolarization.collidedForm zetaZeroConfig
            (ArithmeticPolarization.translate L (fun u => (g u : ℂ))) =
          c * ArithmeticPolarization.collidedForm zetaZeroConfig (fun u => (g u : ℂ))) ∧
    (RiemannHypothesis ↔ ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g → ∀ L : ℝ,
        ArithmeticPolarization.collidedForm zetaZeroConfig
            (ArithmeticPolarization.translate L (fun u => (g u : ℂ))) =
          ArithmeticPolarization.collidedForm zetaZeroConfig (fun u => (g u : ℂ))) :=
  ⟨riemannHypothesis_iff_defectInvolution_trivial,
    (ArithmeticPolarization.hecke_similitude_iff hL).symm,
    ArithmeticPolarization.riemannHypothesis_iff_collided_hecke_invariant⟩

end GaloisForLFunctions.EdgeHodgeTheory
