import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolMatrixCompleteColligation
import GaloisForLFunctions.RHTower.XiWardCubicPrimitiveTailRateNoGo
import GaloisForLFunctions.RHTower.FrankensteinPrimitiveXiMixedBurnolSchurGap

/-!
# Route P constant-channel aperture landing no-go

P-G194's exact matrix colligation is local in radial aperture.  This module
tests whether a fixed finite mixing of its three literal channels can itself
be the missing completed-Xi boundary restriction.
-/

open Complex Matrix Set Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

def routePPrimitiveBurnolApertureRawChannel
    (c : ℝ) (channel : Fin 3) (pe : Nat.Primes × ℕ)
    (kappa L : ℝ) : ℂ :=
  match channel with
  | 0 => routePBurnolForwardDampingShift c
      (routePPrimitiveBurnolWindowFeature pe kappa) L
  | 1 => routePBurnolApertureBoundaryDefect c
      (routePPrimitiveBurnolWindowFeature pe kappa) L
  | 2 => routePBurnolApertureTailDefect c
      (routePPrimitiveBurnolWindowFeature pe kappa) L

def routePPrimitiveBurnolApertureConstantMixer
    (c : ℝ) (z : Fin 3 → ℂ) (pe : Nat.Primes × ℕ)
    (kappa L : ℝ) : ℂ :=
  ∑ channel : Fin 3,
    z channel *
      routePPrimitiveBurnolApertureRawChannel c channel pe kappa L

theorem norm_routePPrimitiveBurnolWindowFeature
    (pe : Nat.Primes × ℕ) (kappa : ℝ) {L : ℝ} (hL : 0 < L) :
    ‖routePPrimitiveBurnolWindowFeature pe kappa L‖ =
      ‖finiteVonMangoldtDepthOneAmplitude
          (xiGammaEulerValuationNat pe)‖ * L *
        Real.exp (-(xiGammaEulerPrimitiveLogFrequency pe * L)) := by
  rw [routePPrimitiveBurnolWindowFeature,
    xiWardCubicBurnolWindowConormalFeature_eq,
    routePXiBaseConormalResidueFeature,
    norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hL, Complex.norm_exp]
  simp [routePPrimitiveBurnolSpectralPoint, Complex.mul_re]
  ring

theorem norm_routePStrictRightBaseConormalResidueFeature
    (q : XiRightZeroCopy) {L : ℝ} (hL : 0 < L) :
    ‖routePXiBaseConormalResidueFeature (q.1.1 : ℂ) L‖ =
      L * Real.exp (-((xiRightCenteredZero q).re * L)) := by
  rw [routePXiBaseConormalResidueFeature, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL,
    Complex.norm_exp]
  rw [← xiRightCenteredZero_eq_support_sub_half]
  simp [Complex.mul_re]

theorem norm_routePBurnolApertureTailDefect_le
    {c L : ℝ} (hc : 0 ≤ c) (f : ℝ → ℂ) :
    ‖routePBurnolApertureTailDefect c f L‖ ≤ ‖f L‖ := by
  by_cases hLc : L ∈ Ioi c
  · have hcL := mem_Ioi.mp hLc
    rw [routePBurnolApertureTailDefect, Set.indicator_of_mem hLc,
      norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (Real.sqrt_le_one.mpr
        (routePBurnolApertureTailDefectWeight_le_one hc hcL))
  · simp [routePBurnolApertureTailDefect, hLc]

theorem norm_routePPrimitiveBurnolApertureRawChannel_le
    {c L : ℝ} (hc : 0 ≤ c) (hLc : c < L)
    (channel : Fin 3) (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    ‖routePPrimitiveBurnolApertureRawChannel c channel pe kappa L‖ ≤
      ‖routePPrimitiveBurnolWindowFeature pe kappa L‖ := by
  fin_cases channel
  · rw [routePPrimitiveBurnolApertureRawChannel.eq_def,
      routePBurnolForwardDampingShift_primitiveFeature hc
        (lt_of_le_of_lt hc hLc)]
    rw [norm_mul, Complex.norm_exp]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [Real.exp_le_one_iff]
    simp [Complex.mul_re]
    exact mul_nonneg hc
      (xiGammaEulerPrimitiveLogFrequency_pos pe).le
  · have hnot : L ∉ Ioc (0 : ℝ) c := by
      intro hmem
      exact (not_lt_of_ge hmem.2) hLc
    simp [routePPrimitiveBurnolApertureRawChannel.eq_def,
      routePBurnolApertureBoundaryDefect, hnot]
  · simpa [routePPrimitiveBurnolApertureRawChannel.eq_def] using
      norm_routePBurnolApertureTailDefect_le hc
        (routePPrimitiveBurnolWindowFeature pe kappa)

theorem norm_routePPrimitiveBurnolApertureConstantMixer_le
    {c L : ℝ} (hc : 0 ≤ c) (hLc : c < L)
    (z : Fin 3 → ℂ) (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    ‖routePPrimitiveBurnolApertureConstantMixer c z pe kappa L‖ ≤
      (∑ channel : Fin 3, ‖z channel‖) *
        ‖routePPrimitiveBurnolWindowFeature pe kappa L‖ := by
  rw [routePPrimitiveBurnolApertureConstantMixer]
  calc
    ‖∑ channel : Fin 3,
        z channel * routePPrimitiveBurnolApertureRawChannel
          c channel pe kappa L‖ ≤
        ∑ channel : Fin 3,
          ‖z channel * routePPrimitiveBurnolApertureRawChannel
          c channel pe kappa L‖ := by
      simpa using norm_sum_le Finset.univ
        (fun channel : Fin 3 =>
          z channel * routePPrimitiveBurnolApertureRawChannel
            c channel pe kappa L)
    _ ≤ ∑ channel : Fin 3,
        ‖z channel‖ * ‖routePPrimitiveBurnolWindowFeature pe kappa L‖ := by
      apply Finset.sum_le_sum
      intro channel _hchannel
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_routePPrimitiveBurnolApertureRawChannel_le
          hc hLc channel pe kappa)
        (norm_nonneg _)
    _ = (∑ channel : Fin 3, ‖z channel‖) *
        ‖routePPrimitiveBurnolWindowFeature pe kappa L‖ := by
      rw [Finset.sum_mul]

/-- No fixed scalar mixing of the three literal P-G194 channels of one
primitive column can equal even one strict-right completed-Xi conormal.  The
source-local colligation preserves the primitive exponential floor. -/
theorem not_exists_routePPrimitiveBurnolApertureConstantMixer_eq_strictRightConormal
    (q : XiRightZeroCopy) {c : ℝ} (hc : 0 ≤ c)
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    ¬ ∃ z : Fin 3 → ℂ, ∀ L : ℝ, 0 < L →
      routePPrimitiveBurnolApertureConstantMixer c z pe kappa L =
        routePXiBaseConormalResidueFeature (q.1.1 : ℂ) L := by
  rintro ⟨z, hz⟩
  let C : ℝ :=
    (∑ channel : Fin 3, ‖z channel‖) *
      ‖finiteVonMangoldtDepthOneAmplitude
        (xiGammaEulerValuationNat pe)‖
  have hC : 0 ≤ C := by
    exact mul_nonneg (Finset.sum_nonneg fun channel _ => norm_nonneg _)
      (norm_nonneg _)
  have hgap :
      (xiRightCenteredZero q).re <
        xiGammaEulerPrimitiveLogFrequency pe :=
    xiRightCenteredZero_re_lt_primitiveBurnolLogFrequency pe q
  have hratio :=
    xiWardCubicConormalExponentialTail_ratio_tendsto_atTop hgap
  have hlarge := hratio.eventually_ge_atTop (C ^ (2 : ℕ) + 1)
  have hthreshold : ∀ᶠ L : ℝ in atTop, max c 0 + 1 ≤ L :=
    Filter.eventually_ge_atTop (max c 0 + 1)
  obtain ⟨L, hlargeL, hthresholdL⟩ := (hlarge.and hthreshold).exists
  have hL : 0 < L := by
    have hzero : 0 ≤ max c 0 := le_max_right c 0
    linarith
  have hcL : c < L := by
    have hcle : c ≤ max c 0 := le_max_left c 0
    linarith
  have hmix :=
    norm_routePPrimitiveBurnolApertureConstantMixer_le
      hc hcL z pe kappa
  have hbound :
      L * Real.exp (-((xiRightCenteredZero q).re * L)) ≤
        C *
          (L * Real.exp
            (-(xiGammaEulerPrimitiveLogFrequency pe * L))) := by
    calc
      L * Real.exp (-((xiRightCenteredZero q).re * L)) =
          ‖routePXiBaseConormalResidueFeature (q.1.1 : ℂ) L‖ := by
        symm
        exact norm_routePStrictRightBaseConormalResidueFeature q hL
      _ = ‖routePPrimitiveBurnolApertureConstantMixer c z pe kappa L‖ := by
        exact congrArg norm (hz L hL).symm
      _ ≤ (∑ channel : Fin 3, ‖z channel‖) *
          ‖routePPrimitiveBurnolWindowFeature pe kappa L‖ := hmix
      _ = C *
          (L * Real.exp
            (-(xiGammaEulerPrimitiveLogFrequency pe * L))) := by
        rw [norm_routePPrimitiveBurnolWindowFeature pe kappa hL]
        dsimp [C]
        ring
  have hexpBound :
      Real.exp (-((xiRightCenteredZero q).re * L)) ≤
        C * Real.exp
          (-(xiGammaEulerPrimitiveLogFrequency pe * L)) := by
    apply (mul_le_mul_iff_left₀ hL).mp
    simpa [mul_assoc, mul_comm, mul_left_comm] using hbound
  have hsq :
      Real.exp (-((xiRightCenteredZero q).re * L)) ^ (2 : ℕ) ≤
        C ^ (2 : ℕ) *
          Real.exp
            (-(xiGammaEulerPrimitiveLogFrequency pe * L)) ^ (2 : ℕ) := by
    have hleft : 0 ≤ Real.exp (-((xiRightCenteredZero q).re * L)) :=
      (Real.exp_pos _).le
    have hright : 0 ≤ C * Real.exp
        (-(xiGammaEulerPrimitiveLogFrequency pe * L)) :=
      mul_nonneg hC (Real.exp_pos _).le
    nlinarith
  have htailBound :
      xiWardCubicConormalExponentialTail (xiRightCenteredZero q).re L ≤
        C ^ (2 : ℕ) *
          xiWardCubicConormalExponentialTail
            (xiGammaEulerPrimitiveLogFrequency pe) L := by
    rw [xiWardCubicConormalExponentialTail,
      xiWardCubicConormalExponentialTail]
    rw [show Real.exp (-2 * (xiRightCenteredZero q).re * L) =
        Real.exp (-((xiRightCenteredZero q).re * L)) ^ (2 : ℕ) by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring,
      show Real.exp (-2 * xiGammaEulerPrimitiveLogFrequency pe * L) =
        Real.exp (-(xiGammaEulerPrimitiveLogFrequency pe * L)) ^ (2 : ℕ) by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring]
    exact hsq
  have hden : 0 < xiWardCubicConormalExponentialTail
      (xiGammaEulerPrimitiveLogFrequency pe) L :=
    Real.exp_pos _
  have hquot :
      xiWardCubicConormalExponentialTail (xiRightCenteredZero q).re L /
          xiWardCubicConormalExponentialTail
            (xiGammaEulerPrimitiveLogFrequency pe) L ≤ C ^ (2 : ℕ) := by
    exact (div_le_iff₀ hden).2 htailBound
  linarith

end

end RHTower
