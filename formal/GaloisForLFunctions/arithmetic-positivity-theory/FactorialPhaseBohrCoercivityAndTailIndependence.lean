import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialPhaseWindowAndPhysicalRieszBounds
import GaloisForLFunctions.RHTower.ArithmeticLogarithmicResponseHeight
import GaloisForLFunctions.HTGeometry.BohrParseval
import GaloisForLFunctions.HTGeometry.BohrMeanTriangle
import GaloisForLFunctions.HTGeometry.BohrMultiFejerOperator

/-! Bohr coercivity of the factorial correction phases and linear independence of the tails.

The clamped kernel `C(u) = {u}(1 - {u})/2` is continuous and `1`-periodic, so each dilated dyadic
filter `v ↦ P(c v)` (`c > 0`) is continuous and periodic, hence Bohr almost periodic. Finite
combinations, norms and products preserve almost periodicity, so `‖B_b‖²` with
`B_b = ∑_{n ∈ S} b_n Φ_{n+1}` has a Bohr mean `lim_{L → ∞} (1/L) ∫_0^L ‖B_b‖²`.

On each window `[0, L]` the harmonic expansion `-(π²/2) B_b = ∑_k w_k H_k`, the Montgomery–Vaughan
layer bounds `(L ∓ K) ∑‖b_n‖²`, and the pointwise dominance with `θ = 3/4` give
`(π⁴/4) ∫_0^L ‖B_b‖² ≥ (L/16 - 7K/16) ∑ ‖b_n‖²`. Dividing by `L` and letting `L → ∞`, the Bohr
mean is at least `∑‖b_n‖² / (4π⁴) ≥ ∑‖b_n‖² / (8π⁴)`. If a finite combination of the literal
tails vanishes, its phase combination vanishes on `[1, ∞)`, its Bohr mean is zero, and every
coefficient vanishes: the correction tails are linearly independent over `ℂ`. -/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

theorem continuous_periodicClampedKernel : Continuous periodicClampedKernel := by
  have h := RHTower.DeletionMixedRefinement.continuous_centeredBernoulliKernel
  have he : periodicClampedKernel = fun x => -(RHTower.bernoulliPeriodic x + 1 / 12) + 1 / 12 := by
    funext x
    simp [periodicClampedKernel]
  rw [he]
  exact h.neg.add continuous_const

theorem periodicClampedKernel_add_nat (x : ℝ) (m : ℕ) :
    periodicClampedKernel (x + m) = periodicClampedKernel x := by
  rw [periodicClampedKernel_eq_fract, periodicClampedKernel_eq_fract, Int.fract_add_natCast]

theorem continuous_dyadicBernoulliFilter : Continuous dyadicBernoulliFilter := by
  have h := continuous_periodicClampedKernel
  unfold dyadicBernoulliFilter
  fun_prop

theorem dyadicBernoulliFilter_periodic : Function.Periodic dyadicBernoulliFilter 1 := by
  intro u
  unfold dyadicBernoulliFilter
  rw [show 4 * (u + 1) = 4 * u + ((4 : ℕ) : ℝ) by push_cast; ring,
    show 2 * (u + 1) = 2 * u + ((2 : ℕ) : ℝ) by push_cast; ring,
    show u + 1 = u + ((1 : ℕ) : ℝ) by push_cast; ring,
    periodicClampedKernel_add_nat, periodicClampedKernel_add_nat, periodicClampedKernel_add_nat]

/-- Every dilated dyadic filter `v ↦ P(c v)`, `c > 0`, is Bohr almost periodic. -/
theorem isBohrAlmostPeriodic_dyadicBernoulliFilter_mul {c : ℝ} (hc : 0 < c) :
    _root_.HTGeometry.IsBohrAlmostPeriodic fun v : ℝ => ((dyadicBernoulliFilter (c * v) : ℝ) : ℂ) := by
  refine isBohrAlmostPeriodic_of_periodic (p := 1 / c) (by positivity) fun v => ?_
  rw [show c * (v + 1 / c) = c * v + 1 by field_simp, dyadicBernoulliFilter_periodic]

theorem continuous_factorialPhaseProfile (N : ℕ) : Continuous (factorialPhaseProfile N) := by
  have h := continuous_dyadicBernoulliFilter
  unfold factorialPhaseProfile
  fun_prop

/-- A finite phase combination is Bohr almost periodic. -/
theorem isBohrAlmostPeriodic_factorialPhaseCombination (S : Finset ℕ) (b : ℕ → ℂ) :
    _root_.HTGeometry.IsBohrAlmostPeriodic (factorialPhaseCombination S b) := by
  have hcP := continuous_dyadicBernoulliFilter
  have hterm (n : ℕ) : _root_.HTGeometry.IsBohrAlmostPeriodic
      fun v => b n * ((factorialPhaseProfile (n + 1) v : ℝ) : ℂ) := by
    refine isBohrAlmostPeriodic_const_mul (b n) ?_
    have h1 := isBohrAlmostPeriodic_dyadicBernoulliFilter_mul
      (factorialShiftedFreq_pos (N := n + 1) (by omega))
    have h2 := isBohrAlmostPeriodic_dyadicBernoulliFilter_mul
      (c := ((n + 1 : ℕ) : ℝ)) (by positivity)
    have hs := isBohrAlmostPeriodic_sub (by fun_prop) h1 (by fun_prop) h2
    simp only [← Complex.ofReal_sub] at hs
    exact hs
  exact isBohrAlmostPeriodic_sum S (F := fun n v => b n * ((factorialPhaseProfile (n + 1) v :
    ℝ) : ℂ)) (fun n _ => continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_factorialPhaseProfile (n + 1)))) fun n _ => hterm n

/-- **Existence of the Bohr square mean** of every finite phase combination. -/
theorem exists_tendsto_bohrMeanSq_factorialPhaseCombination (S : Finset ℕ) (b : ℕ → ℂ) :
    ∃ ℓ : ℝ, Tendsto (fun L : ℝ => (1 / L) *
      ∫ v in (0 : ℝ)..L, ‖factorialPhaseCombination S b v‖ ^ 2) atTop (𝓝 ℓ) := by
  set B := factorialPhaseCombination S b with hB
  have hBc : Continuous B := continuous_factorialPhaseCombination S b
  have hBa : _root_.HTGeometry.IsBohrAlmostPeriodic B :=
    isBohrAlmostPeriodic_factorialPhaseCombination S b
  have hg := isBohrAlmostPeriodic_norm hBa
  have hgc : Continuous fun u => ((‖B u‖ : ℝ) : ℂ) := by fun_prop
  have hgg := isBohrAlmostPeriodic_mul hgc hg hgc hg
  have hsq : _root_.HTGeometry.IsBohrAlmostPeriodic fun u => ‖B u‖ ^ 2 := by
    refine isBohrAlmostPeriodic_of_ofReal ?_
    simpa only [Complex.ofReal_pow, sq, Complex.ofReal_mul] using hgg
  obtain ⟨M, hM⟩ := exists_tendsto_windowAverage (hBc.norm.pow 2) hsq
  refine ⟨M, hM.congr fun L => ?_⟩
  simp only [windowAverage, smul_eq_mul, one_div, Pi.pow_apply]

/-- Window form of the first-harmonic dominance on `[0, L]`:
`(π⁴/4) ∫_0^L ‖B_b‖² ≥ (L/16 - 7K/16) ∑‖b_n‖²`. -/
theorem factorialPhaseCombination_initial_window_lower (S : Finset ℕ) (b : ℕ → ℂ) {L : ℝ}
    (hL : 0 ≤ L) :
    (L / 16 - 7 * factorialWindowGapConstant / 16) * ∑ n ∈ S, ‖b n‖ ^ 2 ≤
      Real.pi ^ 4 / 4 * ∫ v in (0 : ℝ)..L, ‖factorialPhaseCombination S b v‖ ^ 2 := by
  set K := factorialWindowGapConstant with hKdef
  set Sb := ∑ n ∈ S, ‖b n‖ ^ 2 with hSb
  have hK : 0 < K := factorialWindowGapConstant_pos
  have hSb0 : 0 ≤ Sb := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [intervalIntegral.integral_of_le hL]
  have hI (k : ℕ) : (∫ v in (0 : ℝ)..0 + L, ‖factorialHarmonicLayer S b k v‖ ^ 2) =
      ∫ v in Ioc 0 L, ‖factorialHarmonicLayer S b k v‖ ^ 2 := by
    rw [zero_add, intervalIntegral.integral_of_le hL]
  have h1 : (L - K) * Sb ≤ ∫ v in Ioc 0 L, ‖factorialHarmonicLayer S b 1 v‖ ^ 2 := by
    have h := (factorialHarmonicLayer_interval_bounds S b (k := 1) le_rfl (r := 1) le_rfl 0 L).1
    simp only [one_mul, Nat.cast_one, div_one] at h
    rwa [hI] at h
  have hk : ∀ k, 2 ≤ k →
      ∫ v in Ioc 0 L, ‖factorialHarmonicLayer S b k v‖ ^ 2 ≤ (L + K) * Sb := by
    intro k hk2
    have h := (factorialHarmonicLayer_interval_bounds S b (k := k) (by omega) (r := 1) le_rfl
      0 L).2
    simp only [one_mul] at h
    rw [hI] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hSb0)
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have : K / k ≤ K := div_le_self hK.le hk1
    linarith
  have hdom := integral_norm_sq_ge_of_first_harmonic
    (μ := volume.restrict (Ioc 0 L))
    (F := fun v => -((Real.pi ^ 2 / 2 : ℝ) : ℂ) * factorialPhaseCombination S b v)
    (factorialPhaseCombination_hasSum S b) summable_abs_dyadicHarmonicWeight
    dyadicHarmonicWeight_zero dyadicHarmonicWeight_one tsum_abs_dyadicHarmonicWeight_tail_le
    (continuous_factorialHarmonicLayer S b) (norm_factorialHarmonicLayer_le S b) h1 hk
    (θ := 3 / 4) (by norm_num) (by norm_num)
  simp only [norm_neg_pi_sq_half_mul_sq, integral_const_mul] at hdom
  nlinarith

/-- **Bohr coercivity of the actual factorial correction phases.** For every finite complex
family `b`, the Bohr square mean of `B_b = ∑_{n ∈ S} b_n Φ_{n+1}` exists and satisfies
`lim_{L → ∞} (1/L) ∫_0^L ‖B_b‖² ≥ (1/(8π⁴)) ∑ ‖b_n‖²`. -/
theorem factorialPhaseCombination_bohr_coercivity (S : Finset ℕ) (b : ℕ → ℂ) :
    ∃ ℓ : ℝ, Tendsto (fun L : ℝ => (1 / L) *
        ∫ v in (0 : ℝ)..L, ‖factorialPhaseCombination S b v‖ ^ 2) atTop (𝓝 ℓ) ∧
      factorialBohrCoercivityConstant * ∑ n ∈ S, ‖b n‖ ^ 2 ≤ ℓ := by
  obtain ⟨ℓ, hℓ⟩ := exists_tendsto_bohrMeanSq_factorialPhaseCombination S b
  refine ⟨ℓ, hℓ, ?_⟩
  set K := factorialWindowGapConstant with hKdef
  set Sb := ∑ n ∈ S, ‖b n‖ ^ 2 with hSb
  have hSb0 : 0 ≤ Sb := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpi : 0 < Real.pi ^ 4 := by positivity
  have hlow : Tendsto (fun L : ℝ => 4 / Real.pi ^ 4 * (1 / 16 - 7 * K / 16 * L⁻¹) * Sb) atTop
      (𝓝 (4 / Real.pi ^ 4 * (1 / 16 - 7 * K / 16 * 0) * Sb)) :=
    (((tendsto_inv_atTop_zero.const_mul (7 * K / 16)).const_sub (1 / 16)).const_mul
      (4 / Real.pi ^ 4)).mul_const Sb
  have hle := le_of_tendsto_of_tendsto hlow hℓ (by
    filter_upwards [eventually_gt_atTop 0] with L hL
    have h := factorialPhaseCombination_initial_window_lower S b hL.le
    set I := ∫ v in (0 : ℝ)..L, ‖factorialPhaseCombination S b v‖ ^ 2
    have he : 4 / Real.pi ^ 4 * (1 / 16 - 7 * K / 16 * L⁻¹) * Sb =
        (4 / Real.pi ^ 4) * (1 / L) * ((L / 16 - 7 * K / 16) * Sb) := by
      field_simp
    rw [he]
    have hI : 1 / L * I = (4 / Real.pi ^ 4) * (1 / L) * (Real.pi ^ 4 / 4 * I) := by
      field_simp
    rw [hI]
    exact mul_le_mul_of_nonneg_left h (by positivity))
  have hc : factorialBohrCoercivityConstant * Sb ≤
      4 / Real.pi ^ 4 * (1 / 16 - 7 * K / 16 * 0) * Sb := by
    unfold factorialBohrCoercivityConstant
    rw [mul_zero, sub_zero]
    have : 1 / (8 * Real.pi ^ 4) ≤ 4 / Real.pi ^ 4 * (1 / 16) := by
      rw [show 4 / Real.pi ^ 4 * (1 / 16) = 1 / (4 * Real.pi ^ 4) by field_simp; ring]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    exact mul_le_mul_of_nonneg_right this hSb0
  exact hc.trans hle

/-- **Linear independence of the factorial correction tails.** The literal tails
`T_n = factorialMuntzCorrectedTail n` are linearly independent over `ℂ`. -/
theorem linearIndependent_factorialMuntzCorrectedTail :
    LinearIndependent ℂ (fun n : ℕ => fun x : ℝ => (factorialMuntzCorrectedTail n x : ℂ)) := by
  rw [linearIndependent_iff']
  intro s g hg
  set b : ℕ → ℂ := fun n => g n * (factorialTailAmplitude n : ℂ) with hb
  have hpt : ∀ x, ∑ n ∈ s, g n * (factorialMuntzCorrectedTail n x : ℂ) = 0 := by
    intro x
    have h := congrFun hg x
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h
  have hB : ∀ v, 1 ≤ v → factorialPhaseCombination s b v = 0 := by
    intro v hv
    have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
    have h := hpt (-Real.log v)
    rw [sum_factorialMuntzCorrectedTail_eq, indicator_of_mem
      (show -Real.log v ∈ Iic 0 from neg_nonpos.mpr (Real.log_nonneg hv)),
      neg_neg, Real.exp_log hv0] at h
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast (Real.exp_pos _).ne')
  obtain ⟨ℓ, hℓ, hcoer⟩ := factorialPhaseCombination_bohr_coercivity s b
  set C := ∫ v in (0 : ℝ)..1, ‖factorialPhaseCombination s b v‖ ^ 2 with hC
  have hzero : Tendsto (fun L : ℝ => (1 / L) *
      ∫ v in (0 : ℝ)..L, ‖factorialPhaseCombination s b v‖ ^ 2) atTop (𝓝 0) := by
    have hlim : Tendsto (fun L : ℝ => L⁻¹ * C) atTop (𝓝 (0 * C)) :=
      tendsto_inv_atTop_zero.mul_const C
    rw [zero_mul] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with L hL
    have hcont : Continuous fun v => ‖factorialPhaseCombination s b v‖ ^ 2 :=
      (continuous_factorialPhaseCombination s b).norm.pow 2
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1)
      (hcont.intervalIntegrable 0 1) (hcont.intervalIntegrable 1 L)]
    have h0 : (∫ v in (1 : ℝ)..L, ‖factorialPhaseCombination s b v‖ ^ 2) = 0 := by
      rw [intervalIntegral.integral_of_le hL]
      refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => ?_
      rw [hB v hv.1.le, norm_zero]
      norm_num
    rw [h0, add_zero, one_div]
  have hℓ0 : ℓ = 0 := tendsto_nhds_unique hℓ hzero
  exact factorialTail_linear_independent_of_bohr_coercive s g hℓ0 hcoer

/-- **The normalized correction tails form a Riesz sequence.** For every finite complex family
`c`, `144 A ∑ |c_n|² ≤ ∫_ℝ |∑ c_n √(n+1) T_n|² ≤ 225 B ∑ |c_n|²`. -/
theorem factorialTail_normalized_riesz_bounds (S : Finset ℕ) (c : ℕ → ℂ) :
    144 * factorialWeightedPhaseLower * ∑ n ∈ S, ‖c n‖ ^ 2 ≤
      ∫ x, ‖∑ n ∈ S, c n * ((Real.sqrt ((n + 1 : ℕ) : ℝ) * factorialMuntzCorrectedTail n x :
        ℝ) : ℂ)‖ ^ 2 ∧
    (∫ x, ‖∑ n ∈ S, c n * ((Real.sqrt ((n + 1 : ℕ) : ℝ) * factorialMuntzCorrectedTail n x :
        ℝ) : ℂ)‖ ^ 2) ≤ 225 * factorialWeightedPhaseUpper * ∑ n ∈ S, ‖c n‖ ^ 2 := by
  set c' : ℕ → ℂ := fun n => c n * (Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ) with hc'
  obtain ⟨-, hlo, hhi⟩ := factorialTail_physical_riesz_bounds S c'
  have hsum : (∑ n ∈ S, ‖c' n‖ ^ 2 / ((n + 1 : ℕ) : ℝ)) = ∑ n ∈ S, ‖c n‖ ^ 2 := by
    refine Finset.sum_congr rfl fun n _ => ?_
    have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [hc', norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt hN.le]
    field_simp
  have hint : (fun x => ‖∑ n ∈ S, c' n * (factorialMuntzCorrectedTail n x : ℂ)‖ ^ 2) =
      fun x => ‖∑ n ∈ S, c n * ((Real.sqrt ((n + 1 : ℕ) : ℝ) * factorialMuntzCorrectedTail n x :
        ℝ) : ℂ)‖ ^ 2 := by
    funext x
    congr 2
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hc']
    push_cast
    ring
  rw [hsum, hint] at hlo hhi
  exact ⟨hlo, hhi⟩

end

end GaloisForLFunctions.ArithmeticPositivityTheory
