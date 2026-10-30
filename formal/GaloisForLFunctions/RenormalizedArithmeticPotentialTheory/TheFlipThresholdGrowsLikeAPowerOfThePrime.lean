import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.NoFixedOverlapSeesEveryFlip
import GaloisForLFunctions.RHTower.LebesgueAtomWeilPositivity
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import GaloisForLFunctions.BiScaleUncertainty.SplineProbeFiniteShiftBounds
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheTiltedSplineHasAPolynomialConductorFloor

/-!
# The flip threshold grows like a power of the prime

Write `M = ‖φ‖²`, `T(y) = ∫_y^∞ |φ̂(2πt)|² dt` and `E_m(c)` for the completed conductor energies.

* **Plancherel** (`setIntegral_Ioi_shellSpectrum_le`): `T(0) ≤ M/2`.
* **Conductor bounds** (`completedConductorEnergy_le_one`, `completedShellEnergy_le_log`,
  `completedShellEnergy_le_pow`): `E_m(c) ≤ (m/φ(m)) E_1(c/m)`, and if `T(y) ≤ B y⁻⁷` then
  `E_1(y) ≤ 1 + log⁺(1/y) + 4B/M` and, for `y ≥ 1`, `E_1(y) ≤ (4B/M) y⁻⁷`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Real

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis CompletedShell

section Generic

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
include hφ hsupp

/-- **Plancherel for the shell spectrum**: `∫ |φ̂(2πt)|² dt = ‖φ‖²`. -/
theorem integral_shellSpectrum_eq : ∫ t, shellSpectrum φ t = ∫ u, φ u ^ 2 := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hsupp u hu
  have hfc : HasCompactSupport (fun u => (φ u : ℂ)) := hφc.comp_left Complex.ofReal_zero
  have hf : ContDiff ℝ 2 (fun u => (φ u : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
  have h := RHTower.LebesgueAtomWeil.integral_norm_sq_paperFT_eq hf hfc
  have hscale := Measure.integral_comp_mul_left
    (fun r : ℝ => ‖Zeta23.paperFT (fun u => (φ u : ℂ)) (r : ℂ)‖ ^ 2) (2 * π)
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  have hpi : |(2 * π)⁻¹| = 1 / (2 * π) := by
    rw [abs_of_pos (inv_pos.mpr Real.two_pi_pos), one_div]
  unfold shellSpectrum
  rw [hscale, hpi, smul_eq_mul, h]

/-- **The tail of the shell spectrum is at most half the mass.** -/
theorem setIntegral_Ioi_shellSpectrum_le {y : ℝ} (hy : 0 ≤ y) :
    ∫ t in Ioi y, shellSpectrum φ t ≤ (∫ u, φ u ^ 2) / 2 := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hsupp u hu
  have hint : Integrable (shellSpectrum φ) := by
    have h0 := CriticalArithmeticCorrelationTheory.integrableOn_shellSpectrum_Ioi hφ hφc 0
    have h1 : IntegrableOn (shellSpectrum φ) (Iic 0) := by
      have h := h0.comp_neg
      simp only [shellSpectrum_neg, Set.neg_Ioi, neg_zero] at h
      exact (integrableOn_Iic_iff_integrableOn_Iio).mpr h
    have := h1.union h0
    rwa [Iic_union_Ioi, integrableOn_univ] at this
  have hsym : ∫ t in Ioi 0, shellSpectrum φ t = ∫ t in Iic 0, shellSpectrum φ t := by
    have := integral_comp_neg_Ioi 0 (shellSpectrum φ)
    simp only [shellSpectrum_neg, neg_zero] at this
    exact this
  have hsplit : ∫ t, shellSpectrum φ t =
      (∫ t in Iic 0, shellSpectrum φ t) + ∫ t in Ioi 0, shellSpectrum φ t := by
    rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hint.integrableOn
      hint.integrableOn, Iic_union_Ioi, setIntegral_univ]
  have hmono : ∫ t in Ioi y, shellSpectrum φ t ≤ ∫ t in Ioi 0, shellSpectrum φ t :=
    setIntegral_mono_set hint.integrableOn (ae_of_all _ fun t => shellSpectrum_nonneg t)
      (Eventually.of_forall (Ioi_subset_Ioi hy))
  rw [integral_shellSpectrum_eq hφ hsupp] at hsplit
  linarith

omit hφ hsupp in
/-- A polynomial decay of the shell spectrum gives a polynomial tail. -/
theorem setIntegral_Ioi_shellSpectrum_le_pow {A : ℝ}
    (hA : ∀ t : ℝ, 0 < t → shellSpectrum φ t ≤ A * t ^ (-8 : ℝ)) {y : ℝ} (hy : 0 < y) :
    ∫ t in Ioi y, shellSpectrum φ t ≤ A / 7 * y ^ (-7 : ℝ) := by
  have hmaj : IntegrableOn (fun t : ℝ => A * t ^ (-8 : ℝ)) (Ioi y) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hy).const_mul A
  have hval : ∫ t in Ioi y, A * t ^ (-8 : ℝ) = A / 7 * y ^ (-7 : ℝ) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hy]
    norm_num
    ring
  have hA0 : 0 ≤ A := by
    have h1 := hA 1 one_pos
    rw [Real.one_rpow, mul_one] at h1
    exact (shellSpectrum_nonneg 1).trans h1
  by_cases hint : IntegrableOn (shellSpectrum φ) (Ioi y)
  · rw [← hval]
    exact setIntegral_mono_on hint hmaj measurableSet_Ioi fun t ht => hA t (hy.trans ht)
  · rw [integral_undef hint]
    exact mul_nonneg (by positivity) (Real.rpow_pos_of_pos hy _).le

end Generic

/-! ### Harmonic sums -/

theorem sum_range_inv_succ_le_one_add_log (F : ℕ) :
    ∑ n ∈ Finset.range F, 1 / ((n : ℝ) + 1) ≤ 1 + Real.log F := by
  have h := harmonic_le_one_add_log F
  have e : ((harmonic F : ℚ) : ℝ) = ∑ n ∈ Finset.range F, 1 / ((n : ℝ) + 1) := by
    simp [harmonic, one_div]
  rwa [e] at h

/-- The head of the pole series: indices with `(n + 1) y < 1` carry at most `1 + log⁺(1/y)`. -/
theorem sum_range_head_le {y : ℝ} (hy : 0 < y) (K : ℕ) :
    ∑ n ∈ Finset.range K, (if ((n : ℝ) + 1) * y < 1 then 1 / ((n : ℝ) + 1) else 0) ≤
      1 + max 0 (Real.log (1 / y)) := by
  set F := ⌊1 / y⌋₊
  rw [← Finset.sum_filter]
  have hsub : (Finset.range K).filter (fun n : ℕ => ((n : ℝ) + 1) * y < 1) ⊆ Finset.range F := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [Finset.mem_range, Nat.lt_iff_add_one_le]
    refine Nat.le_floor ?_
    push_cast
    rw [le_div_iff₀ hy]
    exact hn.2.le
  calc _ ≤ ∑ n ∈ Finset.range F, 1 / ((n : ℝ) + 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity
    _ ≤ 1 + Real.log F := sum_range_inv_succ_le_one_add_log F
    _ ≤ 1 + max 0 (Real.log (1 / y)) := by
        rcases Nat.eq_zero_or_pos F with h0 | hpos
        · rw [h0, Nat.cast_zero, Real.log_zero]; linarith [le_max_left 0 (Real.log (1 / y))]
        · have := Real.log_le_log (by exact_mod_cast hpos) (Nat.floor_le (by positivity))
          linarith [le_max_right 0 (Real.log (1 / y))]

/-- The tail of the pole series telescopes: `Σ_{(n+1)y ≥ 1} 1/((n+1)² y) ≤ 2`. -/
theorem sum_range_tail_le {y : ℝ} (hy : 0 < y) (K : ℕ) :
    ∑ n ∈ Finset.range K, (if 1 ≤ ((n : ℝ) + 1) * y then 1 / (((n : ℝ) + 1) ^ 2 * y) else 0) ≤
      if 1 ≤ (K : ℝ) * y then 2 - 1 / (y * ((K : ℝ) + 1 / 2)) else 0 := by
  induction K with
  | zero => simp; norm_num
  | succ K ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have hK0 : (0 : ℝ) ≤ K := K.cast_nonneg
    by_cases h1 : 1 ≤ ((K : ℝ) + 1) * y
    · rw [if_pos h1, if_pos h1]
      have hstep : 1 / (((K : ℝ) + 1) ^ 2 * y) ≤
          1 / (y * ((K : ℝ) + 1 / 2)) - 1 / (y * ((K : ℝ) + 1 + 1 / 2)) := by
        rw [div_sub_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hy, hK0, mul_pos hy hy]
      by_cases h0 : 1 ≤ (K : ℝ) * y
      · rw [if_pos h0] at ih
        linarith
      · rw [if_neg h0] at ih
        have ha : 1 / (((K : ℝ) + 1) ^ 2 * y) ≤ 1 / ((K : ℝ) + 1) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
        have hb : 1 / (y * ((K : ℝ) + 1 + 1 / 2)) ≤ 1 := by
          rw [div_le_one (by positivity)]; nlinarith
        have hc : 1 / ((K : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
        linarith
    · rw [if_neg h1, if_neg h1, add_zero]
      have h0 : ¬ 1 ≤ (K : ℝ) * y := fun h => h1 (by nlinarith)
      rwa [if_neg h0] at ih

theorem sum_range_tail_le_two {y : ℝ} (hy : 0 < y) (K : ℕ) :
    ∑ n ∈ Finset.range K, (if 1 ≤ ((n : ℝ) + 1) * y then 1 / (((n : ℝ) + 1) ^ 2 * y) else 0) ≤
      2 := by
  refine (sum_range_tail_le hy K).trans ?_
  split_ifs
  · have : 0 ≤ 1 / (y * ((K : ℝ) + 1 / 2)) := by positivity
    linarith
  · norm_num

theorem sum_range_inv_succ_sq_le_two (K : ℕ) :
    ∑ n ∈ Finset.range K, 1 / ((n : ℝ) + 1) ^ 2 ≤ 2 := by
  have h := sum_range_tail_le_two one_pos K
  simpa only [mul_one, show ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 from fun n => by
    linarith [n.cast_nonneg (α := ℝ)], if_true] using h

/-! ### Upper bounds for the completed conductor energies -/

section Series

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
  (hM : 0 < ∫ u, φ u ^ 2)
include hφ hsupp hM

/-- The pole energy as its coprime-tail series. -/
theorem hasSum_completedShellEnergy {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => 2 / (∫ u, φ u ^ 2) * (1 / ((n : ℝ) + 1)) *
      ∫ t in Ioi (((n : ℝ) + 1) * y), shellSpectrum φ t) (completedShellEnergy φ y) := by
  have h := hasSum_completedConductorEnergy hφ hsupp hM hy one_pos
  rw [completedConductorEnergy_one] at h
  convert h using 1
  funext n
  simp

/-- **Conductor comparison**: `E_m(c) ≤ (m/φ(m)) E_1(c/m)`. -/
theorem completedConductorEnergy_le_one {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    completedConductorEnergy φ c m ≤ ((m : ℝ) / m.totient) * completedShellEnergy φ (c / m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have htot : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have h1 := hasSum_completedConductorEnergy hφ hsupp hM hc hm
  have h2 := (hasSum_completedShellEnergy hφ hsupp hM (div_pos hc hm0)).mul_left
    ((m : ℝ) / m.totient)
  refine hasSum_le (fun n => ?_) h1 h2
  have hT : 0 ≤ ∫ t in Ioi (((n : ℝ) + 1) * (c / m)), shellSpectrum φ t :=
    setIntegral_nonneg measurableSet_Ioi fun t _ => shellSpectrum_nonneg t
  rw [show ((n : ℝ) + 1) * c / m = ((n : ℝ) + 1) * (c / m) by ring]
  split_ifs
  · apply le_of_eq
    field_simp
  · positivity

/-- Partial sums control the pole energy. -/
theorem completedShellEnergy_le_of_partial {y b : ℝ} (hy : 0 < y)
    (hb : ∀ K : ℕ, ∑ n ∈ Finset.range K, 2 / (∫ u, φ u ^ 2) * (1 / ((n : ℝ) + 1)) *
      ∫ t in Ioi (((n : ℝ) + 1) * y), shellSpectrum φ t ≤ b) :
    completedShellEnergy φ y ≤ b :=
  le_of_tendsto' (hasSum_completedShellEnergy hφ hsupp hM hy).tendsto_sum_nat hb

/-- **The pole energy at large overlap** decays like the Fourier tail:
`E_1(y) ≤ (4B/M) y⁻⁷` for `y ≥ 1` when `T(z) ≤ B z⁻⁷`. -/
theorem completedShellEnergy_le_pow {B : ℝ} (hB : 0 ≤ B)
    (hT : ∀ z : ℝ, 0 < z → ∫ t in Ioi z, shellSpectrum φ t ≤ B * z ^ (-7 : ℝ)) {y : ℝ}
    (hy : 1 ≤ y) :
    completedShellEnergy φ y ≤ 4 * B / (∫ u, φ u ^ 2) * y ^ (-7 : ℝ) := by
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  refine completedShellEnergy_le_of_partial hφ hsupp hM hy0 fun K => ?_
  have hterm : ∀ n ∈ Finset.range K, 2 / (∫ u, φ u ^ 2) * (1 / ((n : ℝ) + 1)) *
      ∫ t in Ioi (((n : ℝ) + 1) * y), shellSpectrum φ t ≤
        (2 * B / (∫ u, φ u ^ 2) * y ^ (-7 : ℝ)) * (1 / ((n : ℝ) + 1) ^ 2) := by
    intro n _
    have ha : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [n.cast_nonneg (α := ℝ)]
    have ha0 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have h := hT (((n : ℝ) + 1) * y) (mul_pos ha0 hy0)
    rw [Real.mul_rpow ha0.le hy0.le] at h
    have hpow : ((n : ℝ) + 1) ^ (-7 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by
      rw [one_div, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le ha (by norm_num)
    have hy7 : 0 ≤ y ^ (-7 : ℝ) := (Real.rpow_pos_of_pos hy0 _).le
    have hcoef : 0 ≤ 2 / (∫ u, φ u ^ 2) * (1 / ((n : ℝ) + 1)) := by positivity
    calc _ ≤ 2 / (∫ u, φ u ^ 2) * (1 / ((n : ℝ) + 1)) *
          (B * (((n : ℝ) + 1) ^ (-7 : ℝ) * y ^ (-7 : ℝ))) := mul_le_mul_of_nonneg_left h hcoef
      _ ≤ 2 / (∫ u, φ u ^ 2) * (1 / ((n : ℝ) + 1)) *
          (B * (1 / ((n : ℝ) + 1) * y ^ (-7 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hpow hy7) hB) hcoef
      _ = _ := by field_simp
  calc _ ≤ ∑ n ∈ Finset.range K, (2 * B / (∫ u, φ u ^ 2) * y ^ (-7 : ℝ)) *
        (1 / ((n : ℝ) + 1) ^ 2) := Finset.sum_le_sum hterm
    _ = (2 * B / (∫ u, φ u ^ 2) * y ^ (-7 : ℝ)) *
        ∑ n ∈ Finset.range K, 1 / ((n : ℝ) + 1) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (2 * B / (∫ u, φ u ^ 2) * y ^ (-7 : ℝ)) * 2 :=
        mul_le_mul_of_nonneg_left (sum_range_inv_succ_sq_le_two K)
          (mul_nonneg (by positivity) (Real.rpow_pos_of_pos (zero_lt_one.trans_le hy) _).le)
    _ = _ := by ring

/-- **The pole energy at every overlap**: `E_1(y) ≤ 1 + log⁺(1/y) + 4B/M`. The head `(n+1)y < 1`
uses `T ≤ M/2` (Plancherel), the tail uses the decay. -/
theorem completedShellEnergy_le_log {B : ℝ} (hB : 0 ≤ B)
    (hT : ∀ z : ℝ, 0 < z → ∫ t in Ioi z, shellSpectrum φ t ≤ B * z ^ (-7 : ℝ)) {y : ℝ}
    (hy : 0 < y) :
    completedShellEnergy φ y ≤ 1 + max 0 (Real.log (1 / y)) + 4 * B / (∫ u, φ u ^ 2) := by
  refine completedShellEnergy_le_of_partial hφ hsupp hM hy fun K => ?_
  have hterm : ∀ n ∈ Finset.range K, 2 / (∫ u, φ u ^ 2) * (1 / ((n : ℝ) + 1)) *
      ∫ t in Ioi (((n : ℝ) + 1) * y), shellSpectrum φ t ≤
        (if ((n : ℝ) + 1) * y < 1 then 1 / ((n : ℝ) + 1) else 0) +
          2 * B / (∫ u, φ u ^ 2) *
            (if 1 ≤ ((n : ℝ) + 1) * y then 1 / (((n : ℝ) + 1) ^ 2 * y) else 0) := by
    intro n _
    have ha0 : (0 : ℝ) < (n : ℝ) + 1 := by linarith [n.cast_nonneg (α := ℝ)]
    have hz : 0 < ((n : ℝ) + 1) * y := mul_pos ha0 hy
    have hcoef : 0 ≤ 2 / (∫ u, φ u ^ 2) * (1 / ((n : ℝ) + 1)) := by positivity
    by_cases h1 : ((n : ℝ) + 1) * y < 1
    · rw [if_pos h1, if_neg (not_le.mpr h1), mul_zero, add_zero]
      have hhalf := setIntegral_Ioi_shellSpectrum_le hφ hsupp hz.le
      calc _ ≤ 2 / (∫ u, φ u ^ 2) * (1 / ((n : ℝ) + 1)) * ((∫ u, φ u ^ 2) / 2) :=
            mul_le_mul_of_nonneg_left hhalf hcoef
        _ = _ := by field_simp
    · rw [if_neg h1, if_pos (not_lt.mp h1), zero_add]
      have h := hT _ hz
      have hpow : (((n : ℝ) + 1) * y) ^ (-7 : ℝ) ≤ 1 / (((n : ℝ) + 1) * y) := by
        rw [one_div, ← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le (not_lt.mp h1) (by norm_num)
      calc _ ≤ 2 / (∫ u, φ u ^ 2) * (1 / ((n : ℝ) + 1)) *
            (B * (1 / (((n : ℝ) + 1) * y))) :=
            mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left hpow hB)) hcoef
        _ = _ := by field_simp
  calc _ ≤ ∑ n ∈ Finset.range K, ((if ((n : ℝ) + 1) * y < 1 then 1 / ((n : ℝ) + 1) else 0) +
          2 * B / (∫ u, φ u ^ 2) *
            (if 1 ≤ ((n : ℝ) + 1) * y then 1 / (((n : ℝ) + 1) ^ 2 * y) else 0)) :=
        Finset.sum_le_sum hterm
    _ = (∑ n ∈ Finset.range K, (if ((n : ℝ) + 1) * y < 1 then 1 / ((n : ℝ) + 1) else 0)) +
          2 * B / (∫ u, φ u ^ 2) * ∑ n ∈ Finset.range K,
            (if 1 ≤ ((n : ℝ) + 1) * y then 1 / (((n : ℝ) + 1) ^ 2 * y) else 0) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (1 + max 0 (Real.log (1 / y))) + 2 * B / (∫ u, φ u ^ 2) * 2 :=
        add_le_add (sum_range_head_le hy K)
          (mul_le_mul_of_nonneg_left (sum_range_tail_le_two hy K) (by positivity))
    _ = _ := by ring

end Series

/-! ### The tilted spline: decay and the upper threshold -/

section Spline

open ArithmeticCastelnuovoSeveri BiScaleUncertainty.ChebyshevGauge

/-- The decay constant of the tilted spline's shell spectrum. -/
def splineDecayConstant : ℝ := Real.cosh 1 ^ 8 * 4 ^ 8 / (64 * π ^ 8)

theorem splineDecayConstant_pos : 0 < splineDecayConstant := by
  unfold splineDecayConstant; positivity

theorem norm_paperFT_tiltedUnitSpline_eq (r : ℝ) :
    ‖Zeta23.paperFT (cx tiltedUnitSpline) (r : ℂ)‖ =
      (1 / 8 : ℝ) * ‖Zeta23.paperFT (cx splineProbe) ((r / 8 : ℝ) : ℂ)‖ := by
  have heq : cx tiltedUnitSpline =
      ArithmeticCastelnuovoSeveri.translate (1 / 2) (cx (atomDilate splineProbe (1 / 8))) := rfl
  rw [heq, paperFT_translate, paperFT_atomDilate (by norm_num : (0 : ℝ) < 1 / 8),
    norm_mul, norm_mul, Complex.norm_exp]
  have hz : ((1 / 8 : ℝ) : ℂ) * (r : ℂ) = ((r / 8 : ℝ) : ℂ) := by push_cast; ring
  rw [hz]
  norm_num [Complex.mul_re, Complex.mul_im]

/-- **The tilted spline's shell spectrum decays like `t⁻⁸`.** -/
theorem shellSpectrum_tiltedUnitSpline_le {t : ℝ} (ht : 0 < t) :
    shellSpectrum tiltedUnitSpline t ≤ splineDecayConstant * t ^ (-8 : ℝ) := by
  set x := π * t / 4 with hx
  have hx0 : 0 < x := by positivity
  have hn : ‖Zeta23.paperFT (cx tiltedUnitSpline) ((2 * π * t : ℝ) : ℂ)‖ ≤
      (1 / 8) * (Real.cosh 1 ^ 4 / x ^ 4) := by
    rw [norm_paperFT_tiltedUnitSpline_eq]
    refine mul_le_mul_of_nonneg_left ((norm_paperFT_splineProbe_ofReal_le _).trans ?_)
      (by norm_num)
    rw [show 2 * π * t / 8 = x by rw [hx]; ring]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    nlinarith [sq_nonneg x, pow_pos hx0 2, pow_pos hx0 4]
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hrpow : t ^ (-8 : ℝ) = 1 / t ^ 8 := by
    rw [Real.rpow_neg ht.le, one_div]; norm_cast
  change ‖Zeta23.paperFT (fun u => (tiltedUnitSpline u : ℂ)) ((2 * π * t : ℝ) : ℂ)‖ ^ 2 ≤ _
  refine hsq.trans (le_of_eq ?_)
  rw [hrpow, hx]
  unfold splineDecayConstant
  field_simp
  ring

/-- The Fourier tail of the tilted spline: `T(z) ≤ (A/7) z⁻⁷`. -/
theorem shellTail_tiltedUnitSpline_le {z : ℝ} (hz : 0 < z) :
    ∫ t in Ioi z, shellSpectrum tiltedUnitSpline t ≤ splineDecayConstant / 7 * z ^ (-7 : ℝ) :=
  setIntegral_Ioi_shellSpectrum_le_pow (fun _ ht => shellSpectrum_tiltedUnitSpline_le ht) hz

/-- The constant `K₀ = 4B/M` of the pole-energy bounds for the tilted spline. -/
def splineEnergyConstant : ℝ :=
  4 * (splineDecayConstant / 7) / ∫ u, tiltedUnitSpline u ^ 2

theorem splineEnergyConstant_pos : 0 < splineEnergyConstant := by
  unfold splineEnergyConstant
  have := splineDecayConstant_pos
  have := integral_tiltedUnitSpline_sq_pos
  positivity

theorem tiltedUnitSpline_completedShellEnergy_le_pow {y : ℝ} (hy : 1 ≤ y) :
    completedShellEnergy tiltedUnitSpline y ≤ splineEnergyConstant * y ^ (-7 : ℝ) :=
  completedShellEnergy_le_pow contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
    integral_tiltedUnitSpline_sq_pos (by have := splineDecayConstant_pos; positivity)
    (fun _ hz => shellTail_tiltedUnitSpline_le hz) hy

theorem tiltedUnitSpline_completedShellEnergy_le_log {y : ℝ} (hy : 0 < y) :
    completedShellEnergy tiltedUnitSpline y ≤
      1 + max 0 (Real.log (1 / y)) + splineEnergyConstant :=
  completedShellEnergy_le_log contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
    integral_tiltedUnitSpline_sq_pos (by have := splineDecayConstant_pos; positivity)
    (fun _ hz => shellTail_tiltedUnitSpline_le hz) hy

end Spline

/-! ### The upper threshold: `c*(p) = O(p^{1/7})` -/

/-- The algebraic core: after the exact cancellation of the `log p/p` terms, the trial energy
plus the flip gain is `((q² − 1)(q² + 4X(q² − q + 1)) + 4L(4q² − q − 2))/(q³(q² − 1))`. -/
theorem flipTrial_bound_neg {q L X : ℝ} (hq : 11 ≤ q) (hLq : L < q) (hX : X ≤ -1) :
    1 / q + 4 * (q - 1) ^ 2 / q ^ 3 * (X + L) + 4 / q ^ 2 * (X + 2 * L) +
      (4 * L / q * (-1 + 2 / q ^ 2) + 2 * (2 * L / (q * (q ^ 2 - 1))) * (1 - 1 / q + 1 / q ^ 2))
      < 0 := by
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q ^ 2 - 1 := by nlinarith
  have hq2 : 0 < q ^ 2 - q + 1 := by nlinarith
  have hq3 : 0 < 4 * q ^ 2 - q - 2 := by nlinarith
  have heq : 1 / q + 4 * (q - 1) ^ 2 / q ^ 3 * (X + L) + 4 / q ^ 2 * (X + 2 * L) +
      (4 * L / q * (-1 + 2 / q ^ 2) + 2 * (2 * L / (q * (q ^ 2 - 1))) * (1 - 1 / q + 1 / q ^ 2)) =
      ((q ^ 2 - 1) * (q ^ 2 + 4 * X * (q ^ 2 - q + 1)) + 4 * L * (4 * q ^ 2 - q - 2)) /
        (q ^ 3 * (q ^ 2 - 1)) := by
    field_simp
    ring
  rw [heq]
  refine div_neg_of_neg_of_pos ?_ (by positivity)
  have h1 : (q ^ 2 - 1) * (4 * X * (q ^ 2 - q + 1)) ≤ (q ^ 2 - 1) * (-4 * (q ^ 2 - q + 1)) := by
    apply mul_le_mul_of_nonneg_left _ hq1.le; nlinarith
  have h2 : L * (4 * q ^ 2 - q - 2) ≤ q * (4 * q ^ 2 - q - 2) :=
    mul_le_mul_of_nonneg_right hLq.le hq3.le
  have h3 : q ^ 3 * (20 - 3 * q) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  nlinarith

theorem max_zero_log_sub_eq (L ℓ : ℝ) : max 0 (L - ℓ) = L - min ℓ L := by
  rcases le_total ℓ L with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]
  · rw [min_eq_right h, max_eq_left (by linarith)]; ring

theorem max_zero_two_log_sub_le (L ℓ : ℝ) (hL : 0 ≤ L) : max 0 (2 * L - ℓ) ≤ 2 * L - min ℓ L := by
  rcases le_total ℓ L with h | h
  · rw [min_eq_left h]; exact max_le (by linarith) le_rfl
  · rw [min_eq_right h]; exact max_le (by linarith) (by linarith)

section Upper

open TransMetzlerWeilPositivity.BoundedOverlap ArithmeticElectrostatics

/-- The prime-square trial energy in its three conductors. -/
theorem flipTrialEnergy_eq (φ : ℝ → ℝ) (c : ℝ) {p : ℕ} (hp : p.Prime) :
    flipTrialEnergy φ c p =
      (1 - 2 / (p : ℝ) + 2 / (p : ℝ) ^ 2) ^ 2 * completedConductorEnergy φ c 1 +
        (-2 / (p : ℝ) + 2 / (p : ℝ) ^ 2) ^ 2 * ((p : ℝ) - 1) * completedConductorEnergy φ c p +
        (2 / (p : ℝ) ^ 2) ^ 2 * ((p : ℝ) * ((p : ℝ) - 1)) *
          completedConductorEnergy φ c (p ^ 2) := by
  have hp1 : p ≠ 1 := hp.one_lt.ne'
  have hp2 : p ^ 2 ≠ 1 := fun h => hp1 (by
    have := (Nat.pow_eq_one.mp h); omega)
  have hpp : p ^ 2 ≠ p := by
    have := hp.two_le
    nlinarith
  have h1 : 1 ∉ ({p, p ^ 2} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hp1.symm, hp2.symm⟩
  have h2 : p ∉ ({p ^ 2} : Finset ℕ) := by
    simp only [Finset.mem_singleton]; exact fun h => hpp h.symm
  have htp : ((p.totient : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  have htp2 : (((p ^ 2).totient : ℕ) : ℝ) = (p : ℝ) * ((p : ℝ) - 1) := by
    rw [Nat.totient_prime_pow hp two_pos]
    push_cast [Nat.cast_sub hp.one_le]
    ring
  have hc1 : flipTrialCoeff p 1 = 1 - 2 / (p : ℝ) + 2 / (p : ℝ) ^ 2 := by
    simp [flipTrialCoeff]
  have hcp : flipTrialCoeff p p = (-2 / (p : ℝ) + 2 / (p : ℝ) ^ 2) * Real.sqrt (p.totient : ℝ) := by
    rw [flipTrialCoeff, if_neg hp1, if_pos rfl]
  have hcp2 : flipTrialCoeff p (p ^ 2) = (2 / (p : ℝ) ^ 2) * Real.sqrt ((p ^ 2).totient : ℝ) := by
    rw [flipTrialCoeff, if_neg hp2, if_neg hpp]
  unfold flipTrialEnergy flipTrialConductors
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton, hc1, hcp, hcp2,
    mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _), htp, htp2]
  ring

/-- **Every prime is seen by overlap `O(p^{1/7})`.** For the tilted unit spline there is `K` such
that for every prime `p ≥ K` and every overlap `c ≥ K` with `c⁷ ≥ Kp`, the `p`-flipped complete
form is eventually negative on the prime-square trial. The `log p/p` excitation of the trial
cancels exactly against the flip gain (Plancherel `T(0) = M/2`), leaving
`E_1(c) − (1/p)(log c − O(1))`, and `E_1(c) = O(c⁻⁷)`. -/
theorem tiltedUnitSpline_flip_negative_of_large_overlap :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ p : ℕ, p.Prime → K ≤ p → ∀ c : ℝ, K ≤ c → K * p ≤ c ^ 7 →
      ∀ᶠ N : ℕ in atTop, weilQuadTw (ArithmeticCountingPositivity.primeFlipWeight p)
        (atomicTest N (fun n => primeSquareTrial p n / Real.sqrt n)
          (atomDilate tiltedUnitSpline (c / N))) < 0 := by
  set K₀ := splineEnergyConstant with hK₀
  have hK₀0 : 0 < K₀ := splineEnergyConstant_pos
  set K := max (max 11 (Real.exp (2 + K₀))) K₀ with hKdef
  have hK11 : (11 : ℝ) ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hKe : Real.exp (2 + K₀) ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have hKK₀ : K₀ ≤ K := le_max_right _ _
  refine ⟨K, by linarith, fun p hp hpK c hcK hc7 => ?_⟩
  set q : ℝ := (p : ℝ) with hqdef
  have hq11 : 11 ≤ q := hK11.trans hpK
  have hq0 : 0 < q := by linarith
  have hc0 : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  have hlogc : 2 + K₀ ≤ Real.log c := by
    rw [Real.le_log_iff_exp_le hc0]; exact hKe.trans hcK
  have hlogp : 2 + K₀ ≤ Real.log q := by
    rw [Real.le_log_iff_exp_le hq0]; exact hKe.trans hpK
  have hLq : Real.log q < q := by
    have := Real.log_le_sub_one_of_pos hq0; linarith
  have hL0 : 0 ≤ Real.log q := by linarith
  have hφ := contDiff_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_eq_zero
  have hM := integral_tiltedUnitSpline_sq_pos
  -- the three conductor energies
  have hE1 : completedConductorEnergy tiltedUnitSpline c 1 ≤ 1 / q := by
    rw [completedConductorEnergy_one]
    refine (tiltedUnitSpline_completedShellEnergy_le_pow hc1).trans ?_
    rw [Real.rpow_neg hc0.le, show (c ^ (7 : ℝ)) = c ^ 7 by norm_cast, ← div_eq_mul_inv,
      div_le_div_iff₀ (by positivity) hq0]
    nlinarith [mul_le_mul_of_nonneg_right hKK₀ hq0.le]
  have hE1nn : 0 ≤ completedConductorEnergy tiltedUnitSpline c 1 :=
    completedConductorEnergy_nonneg hφ hsupp hM hc0 one_pos
  have htp : ((p.totient : ℕ) : ℝ) = q - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  have htp2 : (((p ^ 2).totient : ℕ) : ℝ) = q * (q - 1) := by
    rw [Nat.totient_prime_pow hp two_pos]
    push_cast [Nat.cast_sub hp.one_le]
    ring
  have hq1 : 0 < q - 1 := by linarith
  have hEp : completedConductorEnergy tiltedUnitSpline c p ≤
      q / (q - 1) * (1 + K₀ + Real.log q - min (Real.log c) (Real.log q)) := by
    refine (completedConductorEnergy_le_one hφ hsupp hM hc0 hp.pos).trans ?_
    rw [htp]
    refine mul_le_mul_of_nonneg_left ((tiltedUnitSpline_completedShellEnergy_le_log
      (div_pos hc0 hq0)).trans (le_of_eq ?_)) (by positivity)
    rw [one_div_div, Real.log_div hq0.ne' hc0.ne', max_zero_log_sub_eq]
    ring
  have hEp2 : completedConductorEnergy tiltedUnitSpline c (p ^ 2) ≤
      q / (q - 1) * (1 + K₀ + 2 * Real.log q - min (Real.log c) (Real.log q)) := by
    refine (completedConductorEnergy_le_one hφ hsupp hM hc0 (pow_pos hp.pos 2)).trans ?_
    rw [htp2]
    have hcq : 0 < c / ((p ^ 2 : ℕ) : ℝ) := div_pos hc0 (by positivity)
    have hlog := tiltedUnitSpline_completedShellEnergy_le_log hcq
    rw [one_div_div, Real.log_div (by positivity) hc0.ne'] at hlog
    push_cast at hlog
    rw [Real.log_pow, Nat.cast_ofNat] at hlog
    have hmax := max_zero_two_log_sub_le (Real.log q) (Real.log c) hL0
    push_cast
    calc q ^ 2 / (q * (q - 1)) * completedShellEnergy tiltedUnitSpline (c / q ^ 2)
        = q / (q - 1) * completedShellEnergy tiltedUnitSpline (c / q ^ 2) := by
          congr 1; field_simp
      _ ≤ q / (q - 1) * (1 + max 0 (2 * Real.log q - Real.log c) + K₀) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  -- the trial energy plus the flip gain is negative
  have ha1 : 0 ≤ 1 - 2 / q + 2 / q ^ 2 := by
    have : 2 / q ≤ 1 := by rw [div_le_one hq0]; linarith
    have : 0 ≤ 2 / q ^ 2 := by positivity
    linarith
  have ha1' : 1 - 2 / q + 2 / q ^ 2 ≤ 1 := by
    have : 2 / q ^ 2 ≤ 2 / q := div_le_div_of_nonneg_left (by norm_num) hq0 (by nlinarith)
    linarith
  have hsq1 : (1 - 2 / q + 2 / q ^ 2) ^ 2 ≤ 1 := pow_le_one₀ ha1 ha1'
  have hneg : flipTrialEnergy tiltedUnitSpline c p + flipGain p < 0 := by
    rw [flipTrialEnergy_eq _ _ hp]
    set X := 1 + K₀ - min (Real.log c) (Real.log q)
    have hX : X ≤ -1 := by
      have : 2 + K₀ ≤ min (Real.log c) (Real.log q) := le_min hlogc hlogp
      linarith
    have hcore := flipTrial_bound_neg hq11 hLq hX
    have hT1 : (1 - 2 / q + 2 / q ^ 2) ^ 2 * completedConductorEnergy tiltedUnitSpline c 1 ≤ 1 / q :=
      (mul_le_of_le_one_left hE1nn hsq1).trans hE1
    have hT2 : (-2 / q + 2 / q ^ 2) ^ 2 * (q - 1) * completedConductorEnergy tiltedUnitSpline c p ≤
        4 * (q - 1) ^ 2 / q ^ 3 * (X + Real.log q) := by
      calc _ ≤ (-2 / q + 2 / q ^ 2) ^ 2 * (q - 1) *
            (q / (q - 1) * (1 + K₀ + Real.log q - min (Real.log c) (Real.log q))) :=
            mul_le_mul_of_nonneg_left hEp (by positivity)
        _ = _ := by field_simp; ring
    have hT3 : (2 / q ^ 2) ^ 2 * (q * (q - 1)) *
        completedConductorEnergy tiltedUnitSpline c (p ^ 2) ≤ 4 / q ^ 2 * (X + 2 * Real.log q) := by
      calc _ ≤ (2 / q ^ 2) ^ 2 * (q * (q - 1)) *
            (q / (q - 1) * (1 + K₀ + 2 * Real.log q - min (Real.log c) (Real.log q))) :=
            mul_le_mul_of_nonneg_left hEp2 (by positivity)
        _ = _ := by field_simp; ring
    have hgain : flipGain p = 4 * Real.log q / q * (-1 + 2 / q ^ 2) +
        2 * (2 * Real.log q / (q * (q ^ 2 - 1))) * (1 - 1 / q + 1 / q ^ 2) := rfl
    rw [hgain]
    linarith
  exact eventually_flip_negative_of_energy hφ hsupp hM hp hc0 hneg

end Upper

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
