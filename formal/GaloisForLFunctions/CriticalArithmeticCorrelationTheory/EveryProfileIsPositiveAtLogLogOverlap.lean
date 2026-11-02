import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ExponentialFloorsControlRelativeConductorWeights
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.RelativeQuasimodesControlFiniteFrames
import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandTopTailBounds
import GaloisForLFunctions.RHTower.Sieve.TwoRangeLimits

/-!
# Arbitrary compact profiles at log-log overlap

Individual exponential conductor floors separate the overlap cost from the growing-span cost.
The relative residual budget then tends to zero below the half-power logarithmic conductor
cutoff, uniformly on a fixed positive multiple of the log-log overlap scale.
-/

noncomputable section

open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis

set_option autoImplicit false

private theorem conductor_analysis_frame_lower {Q N : ℕ} (hQ : 2 ≤ Q)
    (hQN : Q * Q ≤ N) (hlog : 18 * (1 + Real.log Q) ≤ Real.log N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) (hx : x ∈ conductorSubspace Q N) :
    (1 / 2 : ℝ) * ‖x‖ ^ 2 ≤
      ∑ m ∈ Icc 1 Q, ⟪normalizedRamanujanHorizonVector m N, x⟫ ^ 2 := by
  by_cases hx0 : x = 0
  · simp only [hx0, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
      inner_zero_right, sum_const_zero, le_refl]
  have hxpos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  obtain ⟨a, -, hax⟩ := (mem_conductorSubspace_iff (M := Q) (N := N) (x := x)).mp hx
  have hcoef := (half_and_three_halves_riesz_of_log_le hQ hQN hlog a).1
  rw [← hax] at hcoef
  have hnorm : ‖x‖ ^ 2 = ∑ m ∈ Icc 1 Q,
      a m * ⟪normalizedRamanujanHorizonVector m N, x⟫ := by
    calc
      _ = ⟪x, x⟫ := (real_inner_self_eq_norm_sq x).symm
      _ = ⟪∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N, x⟫ :=
        congrArg (fun y => ⟪y, x⟫) hax
      _ = _ := by rw [sum_inner]; simp only [real_inner_smul_left]
  have hcs := sum_mul_sq_le_sq_mul_sq (Icc 1 Q) a
    (fun m => ⟪normalizedRamanujanHorizonVector m N, x⟫)
  rw [← hnorm] at hcs
  have hmul := mul_le_mul_of_nonneg_right
    (show (∑ m ∈ Icc 1 Q, a m ^ 2) ≤ 2 * ‖x‖ ^ 2 by linarith only [hcoef])
    (sum_nonneg (s := Icc 1 Q) fun m _ => sq_nonneg ⟪normalizedRamanujanHorizonVector m N, x⟫)
  have hprod : ‖x‖ ^ 2 * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 *
      (2 * ∑ m ∈ Icc 1 Q, ⟪normalizedRamanujanHorizonVector m N, x⟫ ^ 2) := by
    calc
      _ = (‖x‖ ^ 2) ^ 2 := (sq _).symm
      _ ≤ _ := hcs.trans hmul
      _ = _ := by ring
  have hh := (mul_le_mul_iff_right₀ hxpos).mp hprod
  linarith only [hh]

private theorem conductor_span_coercive_of_relative_budget {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q * Q ≤ N) (hlog : 18 * (1 + Real.log Q) ≤ Real.log N)
    {A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ} (hA : A.IsHermitian)
    (E : ℕ → ℝ) {e : ℝ} (he : 0 < e) (hfloor : ∀ m ∈ Icc 1 Q, e ≤ E m)
    (hbudget : (∑ m ∈ Icc 1 Q,
      ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N) -
        E m • normalizedRamanujanHorizonVector m N‖ ^ 2 / E m ^ 2) ≤ 1 / 16) :
    ∀ x ∈ conductorSubspace Q N, e / 2 * ‖x‖ ^ 2 ≤ ⟪Matrix.toEuclideanLin A x, x⟫ := by
  classical
  let I := ↥(Icc 1 Q)
  let V := conductorSubspace Q N
  let v : I → V := fun m => ⟨conductorBasisFamily Q N m, Submodule.subset_span ⟨m, rfl⟩⟩
  have hframe (x : V) : (1 / 2 : ℝ) * ‖x‖ ^ 2 ≤ ∑ m : I, ⟪v m, x⟫ ^ 2 := by
    change (1 / 2 : ℝ) * ‖(x : EuclideanSpace ℝ (PrimeHorizonIndex N))‖ ^ 2 ≤
      ∑ m : ↥(Icc 1 Q), ⟪normalizedRamanujanHorizonVector m.1 N,
        (x : EuclideanSpace ℝ (PrimeHorizonIndex N))⟫ ^ 2
    rw [sum_coe_sort (Icc 1 Q) (fun m : ℕ =>
      ⟪normalizedRamanujanHorizonVector m N, (x : EuclideanSpace ℝ (PrimeHorizonIndex N))⟫ ^ 2)]
    exact conductor_analysis_frame_lower hQ hQN hlog x x.property
  have hsmall : (∑ m : I,
      ‖Matrix.toEuclideanLin A (v m : EuclideanSpace ℝ (PrimeHorizonIndex N)) -
        E m.1 • (v m : EuclideanSpace ℝ (PrimeHorizonIndex N))‖ ^ 2 / E m.1 ^ 2) ≤
        (1 / 2 : ℝ) / 8 := by
    change (∑ m : ↥(Icc 1 Q),
      ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m.1 N) -
        E m.1 • normalizedRamanujanHorizonVector m.1 N‖ ^ 2 / E m.1 ^ 2) ≤ (1 / 2 : ℝ) / 8
    rw [sum_coe_sort (Icc 1 Q) (fun m : ℕ =>
      ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N) -
        E m • normalizedRamanujanHorizonVector m N‖ ^ 2 / E m ^ 2)]
    convert hbudget using 1; norm_num
  have hbound := inner_ge_half_floor_on_subspace_of_relative_frame_budget
    (Matrix.toEuclideanLin A) (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    V v (fun m : I => E m.1) (by norm_num : (0 : ℝ) < 1 / 2) he hframe
    (fun m => hfloor m.1 m.property) hsmall
  intro x hx
  exact hbound ⟨x, hx⟩

private theorem overlap_polynomial_envelopes {c α t : ℝ} (hc : 1 ≤ c) (hct : c ≤ α * t) :
    (c + 1) ^ 2 ≤ 4 * α ^ 2 * t ^ 2 ∧
      c ^ 2 * (1 + Real.log c) ^ 3 ≤ α ^ 5 * t ^ 5 ∧
      c ^ 10 ≤ α ^ 10 * t ^ 10 := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hlogc : 0 ≤ 1 + Real.log c := by linarith only [Real.log_nonneg hc]
  have hlogle : 1 + Real.log c ≤ c := by linarith only [Real.log_le_sub_one_of_pos hc0]
  constructor
  · calc
      _ ≤ (2 * c) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith only [hc]) 2
      _ = 4 * c ^ 2 := by ring
      _ ≤ 4 * (α * t) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc0.le hct 2) (by norm_num)
      _ = _ := by ring
  constructor
  · calc
      _ ≤ c ^ 2 * c ^ 3 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hlogc hlogle 3) (sq_nonneg c)
      _ = c ^ 5 := by ring
      _ ≤ (α * t) ^ 5 := pow_le_pow_left₀ hc0.le hct 5
      _ = _ := mul_pow _ _ _
  · exact (pow_le_pow_left₀ hc0.le hct 10).trans_eq (mul_pow _ _ _)

private theorem exponential_relative_rate_envelope {K B A α θ L n c : ℝ}
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hA : 0 ≤ A) (_hα : 0 ≤ α)
    (hθB : 2 * B * α ≤ θ) (hθA : 2 * A ≤ θ) (hθ1 : θ ≤ 1)
    (hL1 : 1 ≤ L) (ht1 : 1 ≤ Real.log L) {Q : ℕ} (hQ1 : 1 ≤ Q)
    (hQ : (Q : ℝ) ≤ L ^ A) (hc : 1 ≤ c) (hct : c ≤ α * Real.log L) (k : ℕ) :
    K * ((c + 1) ^ 2 * Real.exp (2 * B * c) + (Q : ℝ) ^ 2) * (1 + Real.log Q) ^ 2 *
        (c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / (k : ℝ)) / L + c ^ 10 * (L / n) ^ 2) ≤
      (K * (4 * α ^ 2 + 1) * (1 + A) ^ 2 * α ^ 5) *
        (L ^ (θ + 1 / (k : ℝ) - 1) * (Real.log L) ^ 9) +
      (K * (4 * α ^ 2 + 1) * (1 + A) ^ 2 * α ^ 10) * (L ^ 17 / n ^ 2) := by
  let t := Real.log L
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have ht0 : 0 ≤ t := zero_le_one.trans ht1
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ1
  obtain ⟨hplus, hnear, htail⟩ := overlap_polynomial_envelopes hc hct
  have hexp : Real.exp (2 * B * c) ≤ L ^ θ := by
    calc
      _ ≤ Real.exp (2 * B * (α * t)) := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hct (mul_nonneg zero_le_two hB))
      _ = L ^ (2 * B * α) := by rw [Real.rpow_def_of_pos hL]; dsimp only [t]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 hθB
  have hQsq : (Q : ℝ) ^ 2 ≤ L ^ θ := by
    calc
      _ ≤ (L ^ A) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hQ 2
      _ = L ^ (2 * A) := by
        simpa only [Real.rpow_two, mul_comm A (2 : ℝ)] using
          (Real.rpow_mul hL.le A (2 : ℝ)).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 hθA
  have hQsq' : (Q : ℝ) ^ 2 ≤ t ^ 2 * L ^ θ := hQsq.trans
    (le_mul_of_one_le_left (Real.rpow_nonneg hL.le _) (one_le_pow₀ ht1))
  have hS : (c + 1) ^ 2 * Real.exp (2 * B * c) + (Q : ℝ) ^ 2 ≤
      (4 * α ^ 2 + 1) * t ^ 2 * L ^ θ := by
    have hh := mul_le_mul hplus hexp (Real.exp_pos _).le (by positivity)
    nlinarith only [hh, hQsq']
  have hlogQ : Real.log (Q : ℝ) ≤ A * t := by
    have hh := Real.log_le_log hQ0 hQ
    rwa [Real.log_rpow hL] at hh
  have hlogSq : (1 + Real.log (Q : ℝ)) ^ 2 ≤ (1 + A) ^ 2 * t ^ 2 := by
    calc
      _ ≤ ((1 + A) * t) ^ 2 := pow_le_pow_left₀ (by positivity)
        (by nlinarith only [hlogQ, ht1]) 2
      _ = _ := mul_pow _ _ _
  have hrate : c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / (k : ℝ)) / L +
      c ^ 10 * (L / n) ^ 2 ≤
        α ^ 5 * t ^ 5 * L ^ (1 / (k : ℝ)) / L + α ^ 10 * t ^ 10 * (L / n) ^ 2 :=
    add_le_add (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hnear (Real.rpow_nonneg hL.le _)) hL.le)
      (mul_le_mul_of_nonneg_right htail (sq_nonneg _))
  have hrate0 : 0 ≤ c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / (k : ℝ)) / L +
      c ^ 10 * (L / n) ^ 2 := by
    have hlogc : 0 ≤ 1 + Real.log c := by linarith only [Real.log_nonneg hc]
    positivity
  have hcoef := mul_le_mul
    (mul_le_mul_of_nonneg_left hS hK) hlogSq (sq_nonneg _) (by positivity)
  have hbig := mul_le_mul hcoef hrate hrate0 (by positivity)
  have htL : t ≤ L := by dsimp only [t]; linarith only [Real.log_le_sub_one_of_pos hL]
  have hLthree : L ^ (θ + 2) ≤ L ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num; linarith only [hθ1])
  have htailPower : t ^ 14 * L ^ (θ + 2) ≤ L ^ (17 : ℕ) := by
    calc
      _ ≤ L ^ (14 : ℕ) * L ^ (3 : ℕ) := mul_le_mul
        (pow_le_pow_left₀ ht0 htL 14) hLthree (Real.rpow_nonneg hL.le _) (by positivity)
      _ = _ := by ring
  have hC2 : 0 ≤ K * (4 * α ^ 2 + 1) * (1 + A) ^ 2 * α ^ 10 := by positivity
  calc
    _ ≤ K * ((4 * α ^ 2 + 1) * t ^ 2 * L ^ θ) * ((1 + A) ^ 2 * t ^ 2) *
        (α ^ 5 * t ^ 5 * L ^ (1 / (k : ℝ)) / L + α ^ 10 * t ^ 10 * (L / n) ^ 2) := hbig
    _ = (K * (4 * α ^ 2 + 1) * (1 + A) ^ 2 * α ^ 5) *
        (L ^ (θ + 1 / (k : ℝ) - 1) * t ^ 9) +
        (K * (4 * α ^ 2 + 1) * (1 + A) ^ 2 * α ^ 10) *
          (t ^ 14 * L ^ (θ + 2) / n ^ 2) := by
      rw [Real.rpow_sub hL, Real.rpow_add hL, Real.rpow_one,
        Real.rpow_add hL, Real.rpow_two, div_pow]
      ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right htailPower (sq_nonneg n)) hC2)

private theorem exists_small_loglog_relative_rate {K B A α ε : ℝ}
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hA : 0 ≤ A) (hα : 0 ≤ α)
    (hBA : 2 * B * α < 1) (hAhalf : 2 * A < 1) (hε : 0 < ε) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ᶠ N : ℕ in atTop,
      ∀ c : ℝ, 1 ≤ c → c ≤ α * Real.log (Real.log (N : ℝ)) →
      ∀ Q : ℕ, 1 ≤ Q → (Q : ℝ) ≤ Real.log (N : ℝ) ^ A →
        K * ((c + 1) ^ 2 * Real.exp (2 * B * c) + (Q : ℝ) ^ 2) * (1 + Real.log Q) ^ 2 *
          (c ^ 2 * (1 + Real.log c) ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
            c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) ≤ ε := by
  let θ := max (2 * B * α) (2 * A)
  have hθ : θ < 1 := max_lt hBA hAhalf
  have hδ : 0 < 1 - θ := sub_pos.mpr hθ
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (1 - θ))
  have hkR : (0 : ℝ) < k := (div_pos zero_lt_one hδ).trans hk
  have hk1 : 1 ≤ k := by exact_mod_cast hkR
  have hrate : 1 / (k : ℝ) < 1 - θ := by
    apply (div_lt_iff₀ hkR).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hk
  have he : θ + 1 / (k : ℝ) - 1 < 0 := by linarith only [hrate]
  let C₁ := K * (4 * α ^ 2 + 1) * (1 + A) ^ 2 * α ^ 5
  let C₂ := K * (4 * α ^ 2 + 1) * (1 + A) ^ 2 * α ^ 10
  have hfirst : Tendsto (fun N : ℕ => C₁ *
      (Real.log (N : ℝ) ^ (θ + 1 / (k : ℝ) - 1) *
        (Real.log (Real.log (N : ℝ))) ^ 9)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((_root_.RHTower.Sieve.tendsto_logRpow_mul_logLogPow he 9).const_mul C₁).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have htail : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (17 : ℕ) / (N : ℝ) ^ 2)
      atTop (𝓝 0) := by
    have hpow17 (x : ℝ) : x ^ (17 : ℝ) = x ^ (17 : ℕ) := Real.rpow_natCast x 17
    simpa only [Function.comp_def, hpow17, Real.rpow_two] using
      ((isLittleO_log_rpow_rpow_atTop (17 : ℝ) (s := 2) (by norm_num)).tendsto_div_nhds_zero).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hlim : Tendsto (fun N : ℕ =>
      C₁ * (Real.log (N : ℝ) ^ (θ + 1 / (k : ℝ) - 1) *
        (Real.log (Real.log (N : ℝ))) ^ 9) +
      C₂ * (Real.log (N : ℝ) ^ (17 : ℕ) / (N : ℝ) ^ 2)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using hfirst.add (htail.const_mul C₂)
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htlim := Real.tendsto_log_atTop.comp hLlim
  refine ⟨k, hk1, ?_⟩
  filter_upwards [hlim.eventually (ge_mem_nhds hε), hLlim.eventually_ge_atTop 1,
    htlim.eventually_ge_atTop 1] with N hsmall hL1 ht1
  intro c hc hct Q hQ1 hQ
  exact (exponential_relative_rate_envelope hK hB hA hα (le_max_left _ _) (le_max_right _ _)
    hθ.le hL1 ht1 hQ1 hQ hc hct (n := (N : ℝ)) k).trans hsmall

private theorem eventually_loglog_frame_horizon {A α : ℝ} (hA : 0 < A) (hα : 0 ≤ α) :
    ∀ᶠ N : ℕ in atTop,
      let Q := ⌊Real.log (N : ℝ) ^ A⌋₊
      2 ≤ Q ∧ Q * Q ≤ N ∧ 18 * (1 + Real.log Q) ≤ Real.log N ∧
      ∀ c : ℝ, 1 ≤ c → c ≤ α * Real.log (Real.log (N : ℝ)) →
        4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) := by
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow := (tendsto_rpow_atTop hA).comp hLlim
  have hcut : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (2 * A) / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_one] using
      ((isLittleO_log_rpow_rpow_atTop (2 * A) (s := 1) zero_lt_one).tendsto_div_nhds_zero).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hsq : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (2 : ℕ) / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_two, Real.rpow_one] using
      ((isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 1) zero_lt_one).tendsto_div_nhds_zero).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hinv : Tendsto (fun N : ℕ => (Real.log (N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hLlim
  have hlogratio : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) / Real.log N)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_one] using
      ((isLittleO_log_rpow_atTop (r := 1) zero_lt_one).tendsto_div_nhds_zero).comp hLlim
  have hgram : Tendsto (fun N : ℕ => 18 * (1 + A * Real.log (Real.log (N : ℝ))) / Real.log N)
      atTop (𝓝 0) := by
    have hh : Tendsto (fun N : ℕ => 18 * ((Real.log (N : ℝ))⁻¹ +
        A * (Real.log (Real.log (N : ℝ)) / Real.log N))) atTop (𝓝 0) := by
      simpa only [mul_zero, add_zero] using (hinv.add (hlogratio.const_mul A)).const_mul (18 : ℝ)
    apply hh.congr
    intro N
    ring
  let Cw := 4 * (Real.exp 1 + 3) ^ 2 * α ^ 2
  have hwidth : Tendsto (fun N : ℕ => Cw * (Real.log (N : ℝ) ^ (2 : ℕ) / (N : ℝ)))
      atTop (𝓝 0) := by simpa only [mul_zero] using hsq.const_mul Cw
  filter_upwards [hpow.eventually_ge_atTop 2, hcut.eventually (ge_mem_nhds zero_lt_one),
    hgram.eventually (ge_mem_nhds zero_lt_one), hwidth.eventually (ge_mem_nhds zero_lt_one),
    eventually_ge_atTop 2] with N hpowN hcutN hgramN hwidthN hN
  let Q := ⌊Real.log (N : ℝ) ^ A⌋₊
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hQ2 : 2 ≤ Q := Nat.le_floor hpowN
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hQpow : (Q : ℝ) ≤ Real.log (N : ℝ) ^ A :=
    Nat.floor_le (Real.rpow_nonneg (Real.log_natCast_nonneg N) A)
  have hQsq : (Q : ℝ) ^ 2 ≤ Real.log (N : ℝ) ^ (2 * A) := by
    calc
      _ ≤ (Real.log (N : ℝ) ^ A) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hQpow 2
      _ = _ := by simpa only [Real.rpow_two, mul_comm A (2 : ℝ)] using
          (Real.rpow_mul hL.le A (2 : ℝ)).symm
  have hQN : Q * Q ≤ N := by
    have hh := hQsq.trans ((div_le_one hN0).mp hcutN)
    exact_mod_cast (show (Q : ℝ) * (Q : ℝ) ≤ N by simpa only [sq] using hh)
  have hlogQ : Real.log (Q : ℝ) ≤ A * Real.log (Real.log (N : ℝ)) := by
    have hh := Real.log_le_log hQ0 hQpow
    rwa [Real.log_rpow hL] at hh
  have hgramQ : 18 * (1 + Real.log Q) ≤ Real.log N := by
    have hh := (div_le_one hL).mp hgramN
    linarith only [hh, hlogQ]
  refine ⟨hQ2, hQN, hgramQ, ?_⟩
  intro c hc hct
  have htL : Real.log (Real.log (N : ℝ)) ≤ Real.log N := by
    linarith only [Real.log_le_sub_one_of_pos hL]
  have hcL : c ≤ α * Real.log N := hct.trans (mul_le_mul_of_nonneg_left htL hα)
  have hcSq : c ^ 2 ≤ α ^ 2 * Real.log (N : ℝ) ^ 2 :=
    (pow_le_pow_left₀ (zero_le_one.trans hc) hcL 2).trans_eq (mul_pow _ _ _)
  have hwNum : Cw * Real.log (N : ℝ) ^ 2 ≤ (N : ℝ) := by
    apply (div_le_one hN0).mp
    convert hwidthN using 1; ring
  calc
    _ ≤ 4 * (Real.exp 1 + 3) ^ 2 * (α ^ 2 * Real.log (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hcSq (by positivity)
    _ = Cw * Real.log (N : ℝ) ^ 2 := by dsimp only [Cw]; ring
    _ ≤ _ := hwNum

/-- Every nonzero compact `C²` profile is coercive on each logarithmic conductor span below
the half-power cutoff, uniformly up to a universal positive multiple of log-log overlap.
The profile-dependent prefactor is independent of the cutoff and overlap exponents. -/
theorem exists_universal_loglog_overlap_coercivity :
    ∃ B : ℝ, 0 < B ∧ ∀ φ : ℝ → ℝ, ContDiff ℝ 2 φ →
      (∀ x : ℝ, x ∉ Set.Icc 0 1 → φ x = 0) → (0 < ∫ x, φ x ^ 2) →
      ∃ a : ℝ, 0 < a ∧ ∀ A : ℝ, 0 < A → A < 1 / 2 →
      ∀ α : ℝ, 0 < α → 2 * B * α < 1 →
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ α * Real.log (Real.log (N : ℝ)) →
      ∀ x ∈ conductorSubspace ⌊Real.log (N : ℝ) ^ A⌋₊ N,
        a * Real.exp (-B * c) * ‖x‖ ^ 2 ≤ completeWeilEnergy φ c N x := by
  obtain ⟨b₀, hb₀, hfloor⟩ := exists_universal_exponential_completedConductor_floor
  obtain ⟨b₁, hb₁, hresidual⟩ := exists_universal_exponential_relative_residual_budget
  let B := max b₀ b₁
  have hB₀ : b₀ ≤ B := le_max_left _ _
  have hB₁ : b₁ ≤ B := le_max_right _ _
  refine ⟨B, hb₀.trans_le hB₀, ?_⟩
  intro φ hφ hsupp hM
  obtain ⟨a₀, ha₀, hE⟩ := hfloor φ hφ hsupp hM
  obtain ⟨K, hK, hres⟩ := hresidual φ hφ hsupp hM
  refine ⟨a₀ / 2, div_pos ha₀ zero_lt_two, ?_⟩
  intro A hA hAhalf α hα hαB
  have hαb : 2 * b₁ * α < 1 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB₁ zero_le_two) hα.le).trans_lt hαB
  obtain ⟨k, hk, hsmall⟩ := exists_small_loglog_relative_rate hK.le hb₁.le hA.le hα.le
    hαb (by linarith only [hAhalf]) (by norm_num : (0 : ℝ) < 1 / 16)
  filter_upwards [hres A hA.le k hk, hsmall, eventually_loglog_frame_horizon hA hα.le]
    with N hresN hsmallN hframeN
  intro c hc hct x hx
  let Q := ⌊Real.log (N : ℝ) ^ A⌋₊
  obtain ⟨hQ2, hQN, hlog, hwidth⟩ := hframeN
  have hQpow : (Q : ℝ) ≤ Real.log (N : ℝ) ^ A :=
    Nat.floor_le (Real.rpow_nonneg (Real.log_natCast_nonneg N) A)
  have hbudget := (hresN c hc (hwidth c hc hct) Q hQpow).trans
    (hsmallN c hc hct Q (by omega) hQpow)
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hδ : 0 < a₀ * Real.exp (-B * c) := mul_pos ha₀ (Real.exp_pos _)
  have hEfloor (m : ℕ) (hm : m ∈ Icc 1 Q) :
      a₀ * Real.exp (-B * c) ≤ completedConductorEnergy φ c m := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (mem_Icc.mp hm).1
    have hcm : c / m ≤ c := div_le_self hc0.le hm1
    have hprod : b₀ * (c / m) ≤ B * c :=
      (mul_le_mul_of_nonneg_left hcm hb₀.le).trans
        (mul_le_mul_of_nonneg_right hB₀ hc0.le)
    have he : Real.exp (-B * c) ≤ Real.exp (-b₀ * (c / m)) :=
      Real.exp_le_exp.mpr (by linarith only [hprod])
    exact (mul_le_mul_of_nonneg_left he ha₀.le).trans (hE c hc0 m (mem_Icc.mp hm).1)
  have hbound := conductor_span_coercive_of_relative_budget hQ2 hQN hlog
    (completeWeilMatrix_isHermitian φ c N) (completedConductorEnergy φ c) hδ hEfloor hbudget x hx
  change _ ≤ ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) x, x⟫
  convert hbound using 1; ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
