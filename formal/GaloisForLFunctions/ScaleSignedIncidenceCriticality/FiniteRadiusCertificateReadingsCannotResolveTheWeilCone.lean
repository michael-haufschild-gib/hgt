import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionLimitOfAReading
import GaloisForLFunctions.SquareRootThreshold.CertificateRadiusReadsAFinitePrimeWindow

/-!
# Finite-radius certificate readings cannot resolve the Weil cone

The datum is a prime weight `lam : ℕ → ℝ`, the property is membership in the full Weil cone of
`ζ`'s archimedean–polar datum (`RHTower.WeilPositiveFull`, which is RH together with `lam = Λ`),
and the reading is the radius-`R` certificate: the full Weil functional of `lam` on every `C²` test
supported in `[−R, R]`.

* The reading is a function of the finitely many primes below `e^{2R}`
  (`radiusReading_congr_of_agree_below`): it is finite data on the prime side, exactly as the
  truncated divisor is finite data on the zero side.
* At every radius a weight `lam ≥ Λ`, modified at one index above `e^{2R}`, has the reading of `Λ`
  and lies outside the cone (`exists_not_weilPositiveFull_radiusReading_eq`, from
  `SquareRootThreshold.exists_weight_not_weilPositiveFull_eq_zeta_W_on_aperture`).

Hence the prime-side gate: `not_riemannHypothesis_of_resolves_radiusReading` — a reading of the
radius-`R` certificate data resolves cone membership only if RH fails — and the same for every
quantity computed from that data (`not_riemannHypothesis_of_resolves_radiusDerived`). No finite
radius, however large, and no post-processing of the certificate, decides the cone.

This is the weight face of the trans-Nyquist gate: on the zero side a bounded aperture is blind to
every width, on the prime side a bounded radius is blind to the cone.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The certificate reading -/

/-- Tests of aperture `R`: `C²` and supported in `[−R, R]`. -/
def ApertureTest (R : ℝ) : Type := {f : ℝ → ℂ // ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-R) R}

/-- The radius-`R` certificate reading of a prime weight: its full Weil functional on every test of
aperture `R`. -/
noncomputable def radiusReading (R : ℝ) (lam : ℕ → ℝ) : ApertureTest R → ℂ :=
  fun f => weilFullFunctional lam (EF.weilTest f.1 f.1)

/-- **The reading is finite data**: it depends only on the primes below `e^{2R}`. -/
theorem radiusReading_congr_of_agree_below {R : ℝ} {lam lam' : ℕ → ℝ}
    (h : ∀ n : ℕ, 2 ≤ n → Real.log n < 2 * R → lam n = lam' n) :
    radiusReading R lam = radiusReading R lam' :=
  funext fun f => weilFullFunctional_weilTest_congr_of_agree_below h f.2.1 f.2.2

/-! ### 2. Every radius is mimicked from outside the cone -/

/-- **Mimicry at every radius.** Some weight outside the full Weil cone has the radius-`R` reading
of `Λ`. -/
theorem exists_not_weilPositiveFull_radiusReading_eq (R : ℝ) :
    ∃ lam : ℕ → ℝ, ¬ WeilPositiveFull lam ∧
      radiusReading R lam =
        radiusReading R (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) := by
  obtain ⟨lam, -, -, hW, hmim⟩ := exists_weight_not_weilPositiveFull_eq_zeta_W_on_aperture R
  refine ⟨lam, hW, funext fun f => ?_⟩
  obtain ⟨hf, hfs⟩ := f.2
  show weilFullFunctional lam (EF.weilTest f.1 f.1) = _
  rw [hmim f.1 hf hfs, zeta_W_eq_weilFullFunctional hf
    (hasCompactSupport_of_tsupport_subset_Icc hfs)]
  rfl

/-! ### 3. The prime-window gate -/

/-- **The prime-window gate.** A reading of the radius-`R` certificate data resolves membership in
the full Weil cone only if RH fails. -/
theorem not_riemannHypothesis_of_resolves_radiusReading {R : ℝ}
    (hres : Resolves (radiusReading R) WeilPositiveFull) : ¬ RiemannHypothesis := by
  intro hRH
  obtain ⟨lam, hW, heq⟩ := exists_not_weilPositiveFull_radiusReading_eq R
  have hpos : WeilPositiveFull (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) :=
    WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mpr ⟨hRH, fun _ _ => rfl⟩
  exact hW ((hres _ lam heq).mpr hpos)

/-- Nor does any quantity computed from the certificate data. -/
theorem not_riemannHypothesis_of_resolves_radiusDerived {R : ℝ} {O : Type*}
    (g : (ApertureTest R → ℂ) → O)
    (hres : Resolves (fun lam : ℕ → ℝ => g (radiusReading R lam)) WeilPositiveFull) :
    ¬ RiemannHypothesis :=
  not_riemannHypothesis_of_resolves_radiusReading
    (Resolves.of_refines (refines_of_comp (radiusReading R) (fun _ => rfl)) hres)

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
