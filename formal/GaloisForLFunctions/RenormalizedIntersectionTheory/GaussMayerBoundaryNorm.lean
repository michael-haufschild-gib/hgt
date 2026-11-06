import GaloisForLFunctions.RHTower.EisensteinLineRealness
import GaloisForLFunctions.RHTower.EisensteinLineTailParseval
import GaloisForLFunctions.CompletedArithmeticForms.BesselSpectralBand
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCofactorContinuation
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerEisensteinLift

/-!
# Boundary zero-freeness from the completed Mayer carrier

The actual Eisenstein lift maps to the Mayer period by its Cauchy transform.
A hypothetical boundary zeta zero annihilates both constant coefficients,
so the Maass–Selberg norm forces the entire field to vanish. Its first
Whittaker coefficient is nonzero in the Bessel spectral band, a contradiction.

Conjugation gives the full boundary. The completed scattering quotient has
unit modulus, and the actual Mayer determinant and pole cofactor have the
same zeros on the nonreal upper boundary.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.CompletedArithmeticForms
open RHTower

set_option autoImplicit false
noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerBoundaryNorm

private theorem boundary_coefficients_vanish {t : ℝ} (ht : 0 < t)
    (hz : riemannZeta (1 + 2 * ((t : ℂ) * Complex.I)) = 0) :
    msA ((t : ℂ) * Complex.I) = 0 ∧ msB ((t : ℂ) * Complex.I) = 0 := by
  have hA : msA ((t : ℂ) * Complex.I) = 0 := by
    unfold msA reflectedCompletedLambda
    rw [hz, mul_zero]
  have hB : msB ((t : ℂ) * Complex.I) = 0 := by
    rw [msB, reflectedCompletedLambda_two_mul_I_eq_conj ht.ne']
    change (starRingEnd ℂ) (msA ((t : ℂ) * Complex.I)) = 0
    rw [hA, map_zero]
  exact ⟨hA, hB⟩

private theorem truncated_eq_field_of_coefficients_zero {u : ℂ}
    (hA : msA u = 0) (hB : msB u = 0) (Y : ℝ) :
    truncatedLineModel u Y = eisensteinLineModel u := by
  funext z
  have hc : d4BMCompletedEisensteinCuspConstantPart .scalar u z.im = 0 := by
    rw [cuspConstantPart_eq_msAB, hA, hB]
    simp
  simp only [truncatedLineModel, hc, ite_self, sub_zero]

private theorem field_zero_of_zero_truncated_norm {u : ℂ}
    (hu : u ∈ eisensteinLineDomain) (hA : msA u = 0) (hB : msB u = 0)
    (hzero : ∫ z in fd, ‖truncatedLineModel u 1 z‖ ^ 2 = 0) :
    ∀ z : UpperHalfPlane, eisensteinLineModel u z = 0 := by
  have hint : IntegrableOn (fun z => ‖truncatedLineModel u 1 z‖ ^ 2) fd := by
    refine Measure.integrableOn_of_bounded volume_fd_ne_top
      ((measurable_truncatedLineModel u 1).norm.pow_const 2).aestronglyMeasurable
      (M := truncBound' u 1 ^ 2) ?_
    refine (ae_restrict_iff' isClosed_fd.measurableSet).mpr
      (Eventually.of_forall fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_truncatedLineModel_le_truncBound' u le_rfl hz) 2
  have hae : eisensteinLineModel u =ᵐ[volume.restrict fd] fun _ => 0 := by
    have h := (integral_eq_zero_iff_of_nonneg (fun z => by positivity) hint).mp hzero
    filter_upwards [h] with z hz
    rw [truncated_eq_field_of_coefficients_zero hA hB] at hz
    simpa using hz
  -- Continuity and modular invariance turn zero norm into global vanishing.
  have hfo : EqOn (eisensteinLineModel u) (fun _ => 0) fdo :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset fdo_subset_fd hae)
      isOpen_fdo (continuous_eisensteinLineModel u).continuousOn continuousOn_const
  have hfd : EqOn (eisensteinLineModel u) (fun _ => 0) fd :=
    hfo.of_subset_closure (continuous_eisensteinLineModel u).continuousOn continuousOn_const
      fdo_subset_fd (by rw [← fd_eq_closure_fdo])
  intro z
  obtain ⟨A, hAz⟩ := exists_smul_mem_fd z
  have hz := hfd hAz
  rw [eisensteinLineModel_smul hu] at hz
  exact hz

/-- A boundary zeta zero would annihilate the literal completed Eisenstein field. -/
theorem field_zero_of_boundary_zeta_zero {t : ℝ} (ht : 0 < t)
    (hz : riemannZeta (1 + 2 * ((t : ℂ) * Complex.I)) = 0) :
    ∀ z : UpperHalfPlane, eisensteinLineModel ((t : ℂ) * Complex.I) z = 0 := by
  obtain ⟨hA, hB⟩ := boundary_coefficients_vanish ht hz
  apply field_zero_of_zero_truncated_norm (by constructor; norm_num; simpa using ht) hA hB
  rw [integral_norm_sq_truncatedLineModel_line ht le_rfl]
  simp only [msLineValue, hA, hB, zero_pow (by decide : 2 ≠ 0), zero_mul,
    mul_zero, sub_zero, zero_div, add_zero, Complex.zero_re]

#print axioms field_zero_of_boundary_zeta_zero

/-- The first Fourier mode prevents the completed boundary carrier from vanishing. -/
theorem boundary_zeta_ne_zero {t : ℝ} (ht : 0 < t) :
    riemannZeta (1 + 2 * ((t : ℂ) * Complex.I)) ≠ 0 := by
  intro hz
  obtain ⟨hA, hB⟩ := boundary_coefficients_vanish ht hz
  have hfield := field_zero_of_boundary_zeta_zero ht hz
  let Y := |t| + 1
  have hY : 1 ≤ Y := le_add_of_nonneg_left (abs_nonneg t)
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have htail : eisensteinLineTailPart t Y = fun _ => 0 := by
    funext x
    let z : UpperHalfPlane := ⟨⟨x, Y⟩, hY0⟩
    have hc : d4BMCompletedEisensteinCuspConstantPart .scalar ((t : ℂ) * Complex.I) Y = 0 := by
      rw [cuspConstantPart_eq_msAB, hA, hB]
      simp
    have hh := hfield z
    change d4BMCompletedEisensteinCuspConstantPart .scalar ((t : ℂ) * Complex.I) Y +
      eisensteinLineTailPart t Y x = 0 at hh
    simpa only [hc, zero_add] using hh
  have hcoeff := fourierCoeffOn_eisensteinLineTailPart_pos t (Y := Y) (by linarith only [hY]) 0
  rw [htail] at hcoeff
  have hmode : eisensteinLineModeCoeff t Y 0 = 0 := by
    simpa only [fourierCoeffOn_eq_integral, Pi.zero_apply, mul_zero, smul_zero,
      intervalIntegral.integral_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] using hcoeff.symm
  have hmode_eq : eisensteinLineModeCoeff t Y 0 =
      (Real.sqrt Y : ℂ) * modifiedBesselKOrder (2 * Real.pi * Y) ((t : ℂ) * Complex.I) := by
    simp [eisensteinLineModeCoeff, d4BMCompletedEisensteinWhittakerCoefficient]
  have harg : |t| ≤ 2 * Real.pi * Y := by
    have hπY := mul_le_mul_of_nonneg_right Real.pi_gt_three.le hY0.le
    dsimp only [Y] at hπY ⊢
    nlinarith only [hπY, abs_nonneg t]
  have hK := modifiedBesselKOrder_ne_zero_on_band (by positivity : 0 < 2 * Real.pi * Y) harg
  have hroot : (Real.sqrt Y : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hY0).ne'
  exact (mul_ne_zero hroot hK) (hmode_eq.symm.trans hmode)

#print axioms boundary_zeta_ne_zero

/-- Boundary zero-freeness from the completed carrier norm and its first Fourier mode. -/
theorem riemannZeta_ne_zero_of_re_eq_one {w : ℂ} (hw : w.re = 1) :
    riemannZeta w ≠ 0 := by
  have hupper : ∀ v : ℂ, v.re = 1 → 0 < v.im → riemannZeta v ≠ 0 := by
    intro v hv hvi
    have he : v = 1 + 2 * (((v.im / 2 : ℝ) : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp [hv]
      ring
    rw [he]
    exact boundary_zeta_ne_zero (by positivity)
  rcases lt_trichotomy w.im 0 with hneg | hzero | hpos
  · intro hz
    have hn := hupper ((starRingEnd ℂ) w) (by simpa using hw) (by simpa using neg_pos.mpr hneg)
    apply hn
    rw [riemannZeta_conj, hz, map_zero]
  · -- The pole's assigned value is handled separately.
    have he : w = 1 := by apply Complex.ext <;> simp [hw, hzero]
    rw [he]
    exact riemannZeta_one_ne_zero
  · exact hupper w hw hpos

/-- The scattering denominator is nonzero on the actual Mayer boundary. -/
theorem mayer_boundary_denominator_ne_zero {s : ℂ} (hs : (2 * s).re = 1) :
    riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_re_eq_one hs

/-- The completed constant coefficient is nonzero on the upper unitary boundary. -/
theorem boundary_constant_coefficient_ne_zero {t : ℝ} (ht : 0 < t) :
    msA ((t : ℂ) * Complex.I) ≠ 0 := by
  unfold msA reflectedCompletedLambda
  exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by simp))
    (boundary_zeta_ne_zero ht)

/-- The actual completed scattering quotient has unit modulus on the boundary. -/
theorem boundary_scattering_norm_one {t : ℝ} (ht : 0 < t) :
    ‖msB ((t : ℂ) * Complex.I) / msA ((t : ℂ) * Complex.I)‖ = 1 := by
  have hB : msB ((t : ℂ) * Complex.I) = (starRingEnd ℂ) (msA ((t : ℂ) * Complex.I)) := by
    rw [msB, reflectedCompletedLambda_two_mul_I_eq_conj ht.ne']
    rfl
  rw [hB, norm_div, Complex.norm_conj,
    div_self (norm_ne_zero_iff.mpr (boundary_constant_coefficient_ne_zero ht))]

#print axioms riemannZeta_ne_zero_of_re_eq_one
#print axioms mayer_boundary_denominator_ne_zero
#print axioms boundary_scattering_norm_one

/-- Boundary nonvanishing resolves the actual Mayer pole cofactor without dividing by its determinant. -/
theorem boundary_mayer_polePart_eq {w : ℂ} (hw : w.re = 1) (hw1 : w ≠ 1) :
    MayerPole.polePart w 1 = -2 * MayerParameter.sourceDeterminant w 1 *
      (riemannZeta (w - 1) / riemannZeta w) := by
  have hw0 : 0 < w.re := by rw [hw]; norm_num
  have hw2 : w ≠ 2 := by
    intro he
    have hh := congrArg Complex.re he
    simp only [hw, Complex.re_ofNat] at hh
    norm_num at hh
  have h := MayerCofactorContinuation.zeta_cofactor_identity hw0 hw1 hw2
  have hz := riemannZeta_ne_zero_of_re_eq_one hw
  field_simp [hz]
  linear_combination h

#print axioms boundary_mayer_polePart_eq

/-- The reflected zeta coefficient is also nonzero on the nonreal upper boundary. -/
theorem boundary_shifted_zeta_ne_zero {t : ℝ} (ht : 0 < t) :
    riemannZeta (2 * ((t : ℂ) * Complex.I)) ≠ 0 := by
  have hB : msB ((t : ℂ) * Complex.I) ≠ 0 := by
    rw [msB, reflectedCompletedLambda_two_mul_I_eq_conj ht.ne']
    intro hz
    have hnorm := congrArg norm hz
    rw [Complex.norm_conj, norm_zero] at hnorm
    exact boundary_constant_coefficient_ne_zero ht (norm_eq_zero.mp hnorm)
  intro hz
  apply hB
  unfold msB reflectedCompletedLambda
  rw [hz, mul_zero]

/-- The actual Mayer determinant and pole cofactor have exactly the same zeros on the upper boundary. -/
theorem boundary_mayer_polePart_zero_iff {t : ℝ} (ht : 0 < t) :
    MayerPole.polePart (1 + 2 * ((t : ℂ) * Complex.I)) 1 = 0 ↔
      MayerParameter.sourceDeterminant (1 + 2 * ((t : ℂ) * Complex.I)) 1 = 0 := by
  have hw : (1 + 2 * ((t : ℂ) * Complex.I)).re = 1 := by simp
  have hw1 : 1 + 2 * ((t : ℂ) * Complex.I) ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    simp at hi
    exact ht.ne' hi
  have hs : riemannZeta ((1 + 2 * ((t : ℂ) * Complex.I)) - 1) ≠ 0 := by
    rw [show (1 + 2 * ((t : ℂ) * Complex.I)) - 1 = 2 * ((t : ℂ) * Complex.I) by ring]
    exact boundary_shifted_zeta_ne_zero ht
  have hr := div_ne_zero hs (boundary_zeta_ne_zero ht)
  rw [boundary_mayer_polePart_eq hw hw1]
  have htwo : (-2 : ℂ) ≠ 0 := by norm_num
  simp only [mul_eq_zero, hr, htwo, or_false, false_or]

#print axioms boundary_mayer_polePart_zero_iff

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerBoundaryNorm
