import GaloisForLFunctions.RHTower.SuzukiTaCoalescingCovarianceTangent
import GaloisForLFunctions.RHTower.SuzukiTaV2LivsicCharacteristic

/-!
# Actual Suzuki v2 finite-aperture defect jet

This module identifies the first disk jet of Suzuki's literal finite-aperture Livšic function
with the normalized imbalance of the actual completed prime--polar--Gamma covariance energies.

The coefficient bridge is exact.  Reflection makes the cross-deficiency pairing real; Hilbert
polarization identifies its sum and difference with the coalescing even/odd energies; endpoint
Fourier evaluation then removes the common deficiency normalization.  Thus no fitted gauge,
abstract parity surrogate, limiting hypothesis, or Riemann-hypothesis premise enters the result.

Combined with whole-upper-half-plane cofinal compactness, the theorem exposes the remaining
arithmetic problem sharply: identify the cofinal limit of this literal covariance-energy ratio.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct

noncomputable section
namespace RHTower

open GaloisForLFunctions.RHTower

attribute [local instance] Measure.Subtype.measureSpace

theorem spectralExponential_negI_eq (a : SuzukiPositiveAperture) :
    suzukiTaSpectralExponentialL2 a (-I) = suzukiTaExponentialL2 a (-1) := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
      (suzukiTaSpectralExponentialContinuous a (-I)),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
      (suzukiTaExponentialContinuous a (-1))] with x hx hy
  change
    (((ContinuousMap.toLp 2 volume ℂ)
      (suzukiTaSpectralExponentialContinuous a (-I)) :
        SuzukiApertureInterval a.1 → ℂ) x) =
    (((ContinuousMap.toLp 2 volume ℂ)
      (suzukiTaExponentialContinuous a (-1)) :
        SuzukiApertureInterval a.1 → ℂ) x)
  rw [hx, hy]
  simp only [suzukiTaSpectralExponentialContinuous, suzukiTaExponentialContinuous]
  change Complex.exp (-I * -I * (((x : ℝ) : ℂ))) =
    ((Real.exp ((-1 : ℝ) * (x : ℝ)) : ℝ) : ℂ)
  rw [Complex.ofReal_exp]
  congr 1
  rw [show -I * -I = (-1 : ℂ) by rw [neg_mul_neg, Complex.I_mul_I]]
  norm_cast

theorem spectralExponential_I_eq (a : SuzukiPositiveAperture) :
    suzukiTaSpectralExponentialL2 a I = suzukiTaExponentialL2 a 1 := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
      (suzukiTaSpectralExponentialContinuous a I),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
      (suzukiTaExponentialContinuous a 1)] with x hx hy
  change
    (((ContinuousMap.toLp 2 volume ℂ)
      (suzukiTaSpectralExponentialContinuous a I) :
        SuzukiApertureInterval a.1 → ℂ) x) =
    (((ContinuousMap.toLp 2 volume ℂ)
      (suzukiTaExponentialContinuous a 1) :
        SuzukiApertureInterval a.1 → ℂ) x)
  rw [hx, hy]
  simp only [suzukiTaSpectralExponentialContinuous, suzukiTaExponentialContinuous]
  change Complex.exp (-I * I * (((x : ℝ) : ℂ))) =
    ((Real.exp ((1 : ℝ) * (x : ℝ)) : ℝ) : ℂ)
  rw [Complex.ofReal_exp]
  congr 1
  rw [show -I * I = (1 : ℂ) by rw [neg_mul, Complex.I_mul_I, neg_neg]]
  norm_cast

theorem physicalFourier_I_eq_moment_neg_one
    (a : SuzukiPositiveAperture) (x : SuzukiTaHilbert a) :
    suzukiTaPhysicalFourier a x I = suzukiTaMoment a (-1) x := by
  rw [← suzukiTaSpectralMoment_star_eq_physicalFourier]
  have hstar : star (I : ℂ) = -I := Complex.conj_I
  rw [hstar]
  rw [suzukiTaSpectralMoment, suzukiTaMoment, spectralExponential_negI_eq]

theorem physicalFourier_negI_eq_moment_one
    (a : SuzukiPositiveAperture) (x : SuzukiTaHilbert a) :
    suzukiTaPhysicalFourier a x (-I) = suzukiTaMoment a 1 x := by
  rw [← suzukiTaSpectralMoment_star_eq_physicalFourier]
  have hstar : star (-I : ℂ) = I := by
    calc
      (starRingEnd ℂ) (-I) = -(starRingEnd ℂ) I := map_neg _ _
      _ = -(-I) := congrArg Neg.neg Complex.conj_I
      _ = I := neg_neg I
  rw [hstar]
  rw [suzukiTaSpectralMoment, suzukiTaMoment, spectralExponential_I_eq]

theorem inner_rawDeficiency_neg_eq_swap
    (a : SuzukiPositiveAperture) (c : ℝ) :
    inner ℂ (suzukiTaRawDeficiency a (-c)) (suzukiTaRawDeficiency a c) =
      inner ℂ (suzukiTaRawDeficiency a c) (suzukiTaRawDeficiency a (-c)) := by
  rw [suzukiTaRawDeficiency_inner, suzukiTaRawDeficiency_inner]
  change inner ℂ (suzukiTaExponentialL2 a (-c))
      (suzukiTaPhysicalEmbedding a (suzukiTaRawDeficiency a c)) =
    inner ℂ (suzukiTaExponentialL2 a c)
      (suzukiTaPhysicalEmbedding a (suzukiTaRawDeficiency a (-c)))
  rw [← suzukiWeilIntervalReflection_exponential a c,
    suzukiTaPhysicalEmbedding_rawDeficiency_reflection a c]
  simpa using (suzukiWeilIntervalReflection a).inner_map_map
    (suzukiTaExponentialL2 a c)
    (suzukiWeilIntervalReflection a
      (suzukiTaPhysicalEmbedding a (suzukiTaRawDeficiency a c)))

theorem suzukiTaCoalescingEnergy_add_eq_norm_sq
    (a : SuzukiPositiveAperture) (c : ℝ) :
    suzukiTaCoalescingEvenEnergy a c + suzukiTaCoalescingOddEnergy a c =
      ‖suzukiTaRawDeficiency a c‖ ^ 2 := by
  rw [suzukiTaCoalescingEvenEnergy_eq_norm_sq,
    suzukiTaCoalescingOddEnergy_eq_norm_sq,
    suzukiTaRawCoalescingEven, suzukiTaRawCoalescingOdd,
    norm_smul, norm_smul]
  norm_num
  ring_nf
  rw [norm_add_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ),
    norm_suzukiTaRawDeficiency_neg_eq]
  ring_nf

theorem suzukiTaCoalescingEnergy_sub_eq_inner_re
    (a : SuzukiPositiveAperture) (c : ℝ) :
    suzukiTaCoalescingEvenEnergy a c - suzukiTaCoalescingOddEnergy a c =
      (inner ℂ (suzukiTaRawDeficiency a c)
        (suzukiTaRawDeficiency a (-c))).re := by
  rw [suzukiTaCoalescingEvenEnergy_eq_norm_sq,
    suzukiTaCoalescingOddEnergy_eq_norm_sq,
    suzukiTaRawCoalescingEven, suzukiTaRawCoalescingOdd,
    norm_smul, norm_smul]
  norm_num
  ring_nf
  rw [norm_add_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ)]
  ring_nf
  rfl

theorem inner_rawDeficiency_neg_eq_energy_sub
    (a : SuzukiPositiveAperture) (c : ℝ) :
    inner ℂ (suzukiTaRawDeficiency a (-c)) (suzukiTaRawDeficiency a c) =
      ((suzukiTaCoalescingEvenEnergy a c -
        suzukiTaCoalescingOddEnergy a c : ℝ) : ℂ) := by
  have hswap := inner_rawDeficiency_neg_eq_swap a c
  have hconj :
      (starRingEnd ℂ)
          (inner ℂ (suzukiTaRawDeficiency a (-c))
            (suzukiTaRawDeficiency a c)) =
        inner ℂ (suzukiTaRawDeficiency a (-c))
          (suzukiTaRawDeficiency a c) := by
    calc
      (starRingEnd ℂ)
          (inner ℂ (suzukiTaRawDeficiency a (-c))
            (suzukiTaRawDeficiency a c)) =
          inner ℂ (suzukiTaRawDeficiency a c)
            (suzukiTaRawDeficiency a (-c)) :=
              inner_conj_symm (suzukiTaRawDeficiency a c)
                (suzukiTaRawDeficiency a (-c))
      _ = inner ℂ (suzukiTaRawDeficiency a (-c))
            (suzukiTaRawDeficiency a c) := hswap.symm
  have hreal := (Complex.conj_eq_iff_re.mp hconj).symm
  calc
    inner ℂ (suzukiTaRawDeficiency a (-c))
        (suzukiTaRawDeficiency a c) =
      ((inner ℂ (suzukiTaRawDeficiency a (-c))
        (suzukiTaRawDeficiency a c)).re : ℂ) := hreal
    _ = ((inner ℂ (suzukiTaRawDeficiency a c)
        (suzukiTaRawDeficiency a (-c))).re : ℂ) := by rw [hswap]
    _ = ((suzukiTaCoalescingEvenEnergy a c -
        suzukiTaCoalescingOddEnergy a c : ℝ) : ℂ) := by
          rw [suzukiTaCoalescingEnergy_sub_eq_inner_re]

theorem physicalFourier_plus_I_eq_scaled_energy_sub
    (a : SuzukiPositiveAperture) :
    suzukiTaPhysicalFourier a (suzukiTaPlusDeficiency a) I =
      ((‖suzukiTaRawDeficiency a 1‖ *
        (suzukiTaCoalescingEvenEnergy a 1 -
          suzukiTaCoalescingOddEnergy a 1) : ℝ) : ℂ) := by
  rw [physicalFourier_I_eq_moment_neg_one, ← suzukiTaRawDeficiency_inner,
    suzukiTaPlusDeficiency, inner_smul_right,
    inner_rawDeficiency_neg_eq_energy_sub]
  rw [norm_suzukiTaRawDeficiency_neg_eq a 1]
  norm_cast

theorem physicalFourier_plus_negI_eq_scaled_energy_add
    (a : SuzukiPositiveAperture) :
    suzukiTaPhysicalFourier a (suzukiTaPlusDeficiency a) (-I) =
      ((‖suzukiTaRawDeficiency a 1‖ *
        (suzukiTaCoalescingEvenEnergy a 1 +
          suzukiTaCoalescingOddEnergy a 1) : ℝ) : ℂ) := by
  rw [physicalFourier_negI_eq_moment_one, ← suzukiTaRawDeficiency_inner,
    suzukiTaPlusDeficiency, inner_smul_right,
    inner_self_eq_norm_sq_to_K,
    norm_suzukiTaRawDeficiency_neg_eq a 1,
    suzukiTaCoalescingEnergy_add_eq_norm_sq]
  push_cast
  rfl

theorem deriv_suzukiTaV2Livsic_disk_zero_eq_coalescingDefectAngle
    (a : SuzukiPositiveAperture) :
    deriv (fun w => suzukiTaV2Livsic a (suzukiUpperCayleyInv w)) 0 =
      (suzukiDefectAngle
        (suzukiTaCoalescingEvenEnergy a 1)
        (suzukiTaCoalescingOddEnergy a 1) : ℂ) := by
  let F : ℂ → ℂ := suzukiTaPhysicalFourier a (suzukiTaPlusDeficiency a)
  have hplus : ‖suzukiTaRawDeficiency a 1‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (suzukiTaRawDeficiency_ne_zero a 1)
  have hsum :
      ‖suzukiTaRawDeficiency a 1‖ *
        suzukiTaCoalescingEvenEnergy a 1 +
      ‖suzukiTaRawDeficiency a 1‖ *
        suzukiTaCoalescingOddEnergy a 1 ≠ 0 := by
    rw [← mul_add, suzukiTaCoalescingEnergy_add_eq_norm_sq]
    exact mul_ne_zero hplus (pow_ne_zero 2 hplus)
  have hfourier := deriv_suzukiFourierLivsic_disk_zero_eq_defectAngle
    (F := F)
    (evenEnergy := ‖suzukiTaRawDeficiency a 1‖ *
      suzukiTaCoalescingEvenEnergy a 1)
    (oddEnergy := ‖suzukiTaRawDeficiency a 1‖ *
      suzukiTaCoalescingOddEnergy a 1)
    (differentiable_suzukiTaPhysicalFourier a
      (suzukiTaPlusDeficiency a) I)
    (differentiable_suzukiTaPhysicalFourier a
      (suzukiTaPlusDeficiency a) (-I))
    hsum
    (by simpa [F, mul_sub] using physicalFourier_plus_I_eq_scaled_energy_sub a)
    (by simpa [F, mul_add] using physicalFourier_plus_negI_eq_scaled_energy_add a)
  have hquot : suzukiTaV2Livsic a =
      suzukiLivsicQuotient (suzukiFourierNumerator F)
        (suzukiFourierDenominator F) := by
    funext z
    change
      ((z - I) * F z) /
          ((z + I) * suzukiTaPhysicalFourier a
            (suzukiTaMinusDeficiency a) z) =
        ((z - I) * F z) / ((z + I) * F (-z))
    rw [suzukiTaPhysicalFourier_minusDeficiency_reflection]
  rw [hquot]
  have hscale :
      suzukiDefectAngle
          (‖suzukiTaRawDeficiency a 1‖ *
            suzukiTaCoalescingEvenEnergy a 1)
          (‖suzukiTaRawDeficiency a 1‖ *
            suzukiTaCoalescingOddEnergy a 1) =
        suzukiDefectAngle
          (suzukiTaCoalescingEvenEnergy a 1)
          (suzukiTaCoalescingOddEnergy a 1) := by
    rw [suzukiDefectAngle, suzukiDefectAngle]
    field_simp [hplus]
  rw [hscale] at hfourier
  exact hfourier

/-- The literal covariance defect angle is the first upper-half-plane jet at the anchor, with
the exact Cayley Jacobian and no asymptotic normalization. -/
theorem suzukiTaV2_coalescingDefectAngle_eq_two_I_mul_deriv
    (a : SuzukiPositiveAperture) :
    (suzukiDefectAngle
      (suzukiTaCoalescingEvenEnergy a 1)
      (suzukiTaCoalescingOddEnergy a 1) : ℂ) =
      2 * I * deriv (suzukiTaV2Livsic a) I := by
  let U : Set ℂ := {z : ℂ | 0 < z.im}
  have hdiffOn : DifferentiableOn ℂ (suzukiTaV2Livsic a) U :=
    differentiableOn_suzukiLivsicQuotient_upperHalfPlane
      (differentiable_suzukiTaV2CharacteristicA a)
      (differentiable_suzukiTaV2CharacteristicE a)
      (suzukiTaV2CharacteristicA_I a)
      (suzukiTaV2_allAngleRealZeros a)
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hI : I ∈ U := by simp [U]
  have hdiff : DifferentiableAt ℂ (suzukiTaV2Livsic a) I :=
    hdiffOn.differentiableAt (hUopen.mem_nhds hI)
  have hadd : HasDerivAt (fun w : ℂ => 1 + w) 1 0 := by
    simpa using! (hasDerivAt_const 0 (1 : ℂ)).add (hasDerivAt_id 0)
  have hsub : HasDerivAt (fun w : ℂ => 1 - w) (-1) 0 := by
    simpa using! (hasDerivAt_const 0 (1 : ℂ)).sub (hasDerivAt_id 0)
  have hinv : HasDerivAt suzukiUpperCayleyInv (2 * I) 0 := by
    have h := (hadd.div hsub (by norm_num : (1 : ℂ) - 0 ≠ 0)).const_mul I
    convert! h using 1
    ring
  have hcomp : HasDerivAt
      (fun w => suzukiTaV2Livsic a (suzukiUpperCayleyInv w))
      (deriv (suzukiTaV2Livsic a) I * (2 * I)) 0 := by
    have hdiff' : HasDerivAt (suzukiTaV2Livsic a)
        (deriv (suzukiTaV2Livsic a) I) (suzukiUpperCayleyInv 0) := by
      simpa [suzukiUpperCayleyInv] using hdiff.hasDerivAt
    simpa [Function.comp_def] using hdiff'.comp 0 hinv
  calc
    (suzukiDefectAngle
        (suzukiTaCoalescingEvenEnergy a 1)
        (suzukiTaCoalescingOddEnergy a 1) : ℂ) =
      deriv (fun w => suzukiTaV2Livsic a (suzukiUpperCayleyInv w)) 0 :=
        (deriv_suzukiTaV2Livsic_disk_zero_eq_coalescingDefectAngle a).symm
    _ = deriv (suzukiTaV2Livsic a) I * (2 * I) := hcomp.deriv
    _ = 2 * I * deriv (suzukiTaV2Livsic a) I := by ring

end RHTower
