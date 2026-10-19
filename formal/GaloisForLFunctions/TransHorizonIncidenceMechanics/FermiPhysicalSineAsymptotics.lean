import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiNonnegativeCosinePhysicalTraceLowerBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Sharp asymptotic bounds for the physical Fermi trace

The exact weighted ray estimate and nonnegative dyadic cosine packets identify
`4 / Real.pi^2` as the sharp quadratic leading coefficient at dyadic horizons.
The upper bound is uniform over every coefficient input; the lower family has
nonnegative entries. Both signed and nonnegative asymptotic inverse estimates
admit a leading coefficient exactly when it is at least `4 / Real.pi^2`.
-/

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

open Filter Topology

private theorem cosine_gap_half_angle (x : ℝ) :
    2 - 2 * Real.cos x = 4 * Real.sin (x / 2)^2 := by
  have h := Real.sin_sq_eq_half_sub (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  linarith

private theorem mixed_gap_scaled_limit :
    Tendsto (fun n : ℕ => (n : ℝ)^2 *
      (2 - 2 * Real.cos (Real.pi / (2 * (n : ℝ) + 1)))) atTop (𝓝 (Real.pi^2 / 4)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  let z := fun n : ℕ => 1 / ((n : ℝ) + 1)
  let a := fun n : ℕ => Real.pi / (4 + 2 * z n)
  have hz : Tendsto z atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hden : Tendsto (fun n => 4 + 2 * z n) atTop (𝓝 (4 : ℝ)) := by
    simpa using (hz.const_mul 2).const_add 4
  have ha : Tendsto a atTop (𝓝 (Real.pi / 4)) :=
    tendsto_const_nhds.div hden (by norm_num)
  have ht : Tendsto (fun n => a n * z n) atTop (𝓝 0) := by
    simpa using ha.mul hz
  have hs : Tendsto (fun n => Real.sinc (a n * z n)) atTop (𝓝 1) := by
    simpa only [Real.sinc_zero, Function.comp_def] using (Real.continuous_sinc.tendsto 0).comp ht
  have hlim : Tendsto (fun n => 4 * (a n)^2 * (Real.sinc (a n * z n))^2)
      atTop (𝓝 (Real.pi^2 / 4)) := by
    have h := ((ha.pow 2).mul (hs.pow 2)).const_mul 4
    rw [show 4 * ((Real.pi / 4)^2 * (1 : ℝ)^2) = Real.pi^2 / 4 by ring] at h
    simpa only [mul_assoc] using h
  have heq : (fun n : ℕ => ((n + 1 : ℕ) : ℝ)^2 *
      (2 - 2 * Real.cos (Real.pi / (2 * ((n + 1 : ℕ) : ℝ) + 1)))) =
      fun n : ℕ => 4 * (a n)^2 * (Real.sinc (a n * z n))^2 := by
    funext n
    have hn : (0 : ℝ) < n + 1 := by positivity
    have hdn : 0 < 4 + 2 * z n := by dsimp [z]; positivity
    have ha0 : 0 < a n := div_pos Real.pi_pos hdn
    have hz0 : 0 < z n := by dsimp [z]; positivity
    rw [Nat.cast_add, Nat.cast_one, cosine_gap_half_angle,
      Real.sinc_of_ne_zero (ne_of_gt (mul_pos ha0 hz0))]
    have hangle : Real.pi / (2 * ((n : ℝ) + 1) + 1) / 2 = a n * z n := by
      dsimp [a, z]
      field_simp
      ring
    rw [hangle]
    dsimp [a, z]
    field_simp
  rw [heq]
  exact hlim

private noncomputable def mixedGap (n : ℕ) : ℝ :=
  2 - 2 * Real.cos (Real.pi / (2 * (n : ℝ) + 1))

private theorem shifted_reciprocal_limit :
    Tendsto (fun m : ℕ => 1 / ((m + 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
  (tendsto_add_atTop_iff_nat 2).2 tendsto_one_div_atTop_nhds_zero_nat

private theorem shifted_ratio_limit (K : ℕ) :
    Tendsto (fun m : ℕ => ((m + K : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ)) atTop (𝓝 1) := by
  have h := (shifted_reciprocal_limit.const_mul ((K : ℝ) - 2)).const_add 1
  have heq : (fun m : ℕ => ((m + K : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ)) =
      fun m : ℕ => 1 + ((K : ℝ) - 2) * (1 / ((m + 2 : ℕ) : ℝ)) := by
    funext m
    push_cast
    field_simp
    ring
  rw [heq]
  simpa using h

private theorem shifted_gap_limits (K : ℕ) :
    Tendsto (fun m : ℕ => mixedGap (m + 2)) atTop (𝓝 0) ∧
    Tendsto (fun m : ℕ => ((m + K : ℕ) : ℝ) * mixedGap (m + 2)) atTop (𝓝 0) ∧
    Tendsto (fun m : ℕ => ((m + K : ℕ) : ℝ)^2 * mixedGap (m + 2))
      atTop (𝓝 (Real.pi^2 / 4)) := by
  have hg : Tendsto (fun m : ℕ => ((m + 2 : ℕ) : ℝ)^2 * mixedGap (m + 2))
      atTop (𝓝 (Real.pi^2 / 4)) :=
    (tendsto_add_atTop_iff_nat 2).2 mixed_gap_scaled_limit
  have hi := shifted_reciprocal_limit
  have hr := shifted_ratio_limit K
  constructor
  · have heq : (fun m : ℕ => mixedGap (m + 2)) =
        fun m : ℕ => (((m + 2 : ℕ) : ℝ)^2 * mixedGap (m + 2)) *
          (1 / ((m + 2 : ℕ) : ℝ))^2 := by
      funext m
      have hm : (0 : ℝ) < (m + 2 : ℕ) := by positivity
      field_simp
    rw [heq]
    simpa using hg.mul (hi.pow 2)
  constructor
  · have heq : (fun m : ℕ => ((m + K : ℕ) : ℝ) * mixedGap (m + 2)) =
        fun m : ℕ => ((((m + 2 : ℕ) : ℝ)^2 * mixedGap (m + 2)) *
          (1 / ((m + 2 : ℕ) : ℝ))) *
          (((m + K : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ)) := by
      funext m
      have hm : (0 : ℝ) < (m + 2 : ℕ) := by positivity
      field_simp
    rw [heq]
    simpa using (hg.mul hi).mul hr
  · have heq : (fun m : ℕ => ((m + K : ℕ) : ℝ)^2 * mixedGap (m + 2)) =
        fun m : ℕ => (((m + 2 : ℕ) : ℝ)^2 * mixedGap (m + 2)) *
          (((m + K : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ))^2 := by
      funext m
      have hm : (0 : ℝ) < (m + 2 : ℕ) := by positivity
      field_simp
    rw [heq]
    simpa using hg.mul (hr.pow 2)

private noncomputable def scaledSineDenominator (K : ℕ) (M : ℝ) (m : ℕ) : ℝ :=
  M * mixedGap (m + 2) * ((m + K : ℕ) : ℝ)^2

private noncomputable def sineNumerator (K : ℕ) (M : ℝ) (m : ℕ) : ℝ :=
  (1 + 1 / (2 : ℝ)^(K + 1)) *
    ((M + 1) + M * (M + 1) * mixedGap (m + 2) * (m + 2 : ℕ) +
      (4 / 3 : ℝ) * M * mixedGap (m + 2)) +
    (5 / 2 : ℝ) * (K - 1 : ℕ) * (((m + K : ℕ) : ℝ) + 2) * M * mixedGap (m + 2)

private theorem sine_coefficient_limits (K : ℕ) (M : ℝ) :
    Tendsto (scaledSineDenominator K M) atTop (𝓝 (M * (Real.pi^2 / 4))) ∧
    Tendsto (sineNumerator K M) atTop (𝓝 ((1 + 1 / (2 : ℝ)^(K + 1)) * (M + 1))) := by
  constructor
  · have heq : scaledSineDenominator K M =
        fun m : ℕ => M * (((m + K : ℕ) : ℝ)^2 * mixedGap (m + 2)) := by
      funext m
      dsimp [scaledSineDenominator]
      ring
    rw [heq]
    exact (shifted_gap_limits K).2.2.const_mul M
  · let G := fun m : ℕ => (M + 1) + M * (M + 1) * mixedGap (m + 2) * (m + 2 : ℕ) +
      (4 / 3 : ℝ) * M * mixedGap (m + 2)
    have hg : Tendsto G atTop (𝓝 (M + 1)) := by
      have h := ((tendsto_const_nhds (x := M + 1)).add
        ((shifted_gap_limits 2).2.1.const_mul (M * (M + 1)))).add
        ((shifted_gap_limits 0).1.const_mul ((4 / 3 : ℝ) * M))
      simpa only [mul_zero, zero_mul, add_zero, mul_assoc, mul_left_comm, mul_comm, G] using h
    have heq : sineNumerator K M = fun m : ℕ =>
        (1 + 1 / (2 : ℝ)^(K + 1)) * G m +
          ((5 / 2 : ℝ) * (K - 1 : ℕ) * M) *
            (((m + (K + 2) : ℕ) : ℝ) * mixedGap (m + 2)) := by
      funext m
      dsimp [sineNumerator, G]
      push_cast
      ring
    rw [heq]
    have h := (hg.const_mul (1 + 1 / (2 : ℝ)^(K + 1))).add
      ((shifted_gap_limits (K + 2)).2.1.const_mul ((5 / 2 : ℝ) * (K - 1 : ℕ) * M))
    simpa only [mul_zero, add_zero] using h

private theorem physical_eventual_bound_fixed (K : ℕ) (hK : 1 ≤ K)
    (M : ℝ) (hM : 0 < M) (C : ℝ)
    (hC : (1 + 1 / (2 : ℝ)^(K + 1)) * (M + 1) < C * (M * (Real.pi^2 / 4))) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → ∀ c : ℕ → ℝ,
      sieveTotalPronicEnergy (2^r) c ≤
        C * (r : ℝ)^2 * fermiSelectedTotalPronicEnergy (2^r) c := by
  obtain ⟨hA, hB⟩ := sine_coefficient_limits K M
  have hpos := hA.eventually_const_lt (show (0 : ℝ) < M * (Real.pi^2 / 4) by positivity)
  have hneg := (hB.sub (hA.const_mul C)).eventually_lt_const
    (show (1 + 1 / (2 : ℝ)^(K + 1)) * (M + 1) - C * (M * (Real.pi^2 / 4)) < 0 by linarith)
  obtain ⟨R, hR⟩ := eventually_atTop.mp (hpos.and hneg)
  refine ⟨R + K, ?_⟩
  intro r hr c
  let m := r - K
  have hm : R ≤ m := by dsimp [m]; omega
  have hrm : m + K = r := by dsimp [m]; omega
  obtain ⟨hα, hβ⟩ := hR m hm
  have hKD : K ≤ Nat.log 2 (2^(m + K)) + 1 := by
    rw [Nat.log_pow (by decide : 1 < (2 : ℕ))]
    omega
  have hbase : M * mixedGap (m + 2) * sieveTotalPronicEnergy (2^(m + K)) c ≤
      sineNumerator K M m * fermiSelectedTotalPronicEnergy (2^(m + K)) c := by
    have h := sieveTotalPronicEnergy_scaled_sine_bound (2^(m + K)) c K hK hKD M hM.le
    dsimp only at h
    simp only [Nat.log_pow (by decide : 1 < (2 : ℕ))] at h
    rw [show m + K + 1 + 1 - K = m + 2 by omega] at h
    dsimp only [mixedGap, sineNumerator]
    push_cast at h ⊢
    nlinarith only [h]
  have hQ : 0 ≤ fermiSelectedTotalPronicEnergy (2^(m + K)) c := by
    unfold fermiSelectedTotalPronicEnergy
    apply tsum_nonneg
    intro j
    unfold fermiSelectedPronicEnergy
    exact Finset.sum_nonneg fun _ _ => by positivity
  have hscale := mul_le_mul_of_nonneg_right
    (show sineNumerator K M m ≤ C * scaledSineDenominator K M m by linarith only [hβ]) hQ
  have hrpos : (0 : ℝ) < (m + K : ℕ) := by exact_mod_cast (show 0 < m + K by omega)
  have hML : 0 < M * mixedGap (m + 2) :=
    (mul_pos_iff_of_pos_right (sq_pos_of_pos hrpos)).mp hα
  have hfinal : sieveTotalPronicEnergy (2^(m + K)) c ≤
      C * ((m + K : ℕ) : ℝ)^2 * fermiSelectedTotalPronicEnergy (2^(m + K)) c := by
    dsimp only [scaledSineDenominator] at hscale
    nlinarith only [hML, hbase, hscale]
  simpa only [hrm] using hfinal

private theorem sine_upper_parameter_limit :
    Tendsto (fun j : ℕ => (1 + 1 / (2 : ℝ)^(j + 2)) *
      (1 + 1 / ((j : ℝ) + 1)) * (4 / Real.pi^2)) atTop (𝓝 (4 / Real.pi^2)) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hi : Tendsto (fun j : ℕ => 1 / (2 : ℝ)^(j + 2)) atTop (𝓝 0) := by
    have heq : (fun j : ℕ => 1 / (2 : ℝ)^(j + 2)) =
        fun j : ℕ => (1 / 4 : ℝ) * (1 / 2 : ℝ)^j := by
      funext j
      rw [pow_add, div_pow, one_pow]
      norm_num
    rw [heq]
    simpa using hp.const_mul (1 / 4 : ℝ)
  have hr : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa using ((hi.const_add 1).mul (hr.const_add 1)).mul_const (4 / Real.pi^2)

/-- Every coefficient input at a sufficiently large dyadic horizon obeys the
physical trace inverse estimate with coefficient `4 / Real.pi^2 + ε`. -/
theorem sieveTotalPronicEnergy_asymptotic_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → ∀ c : ℕ → ℝ,
      sieveTotalPronicEnergy (2^r) c ≤
        (4 / Real.pi^2 + ε) * (r : ℝ)^2 * fermiSelectedTotalPronicEnergy (2^r) c := by
  obtain ⟨j, hj⟩ := eventually_atTop.mp
    (sine_upper_parameter_limit.eventually_lt_const (lt_add_of_pos_right _ hε))
  have hjj := hj j le_rfl
  have hα : 0 < ((j : ℝ) + 1) * (Real.pi^2 / 4) := by positivity
  have h := mul_lt_mul_of_pos_right hjj hα
  have heq : ((1 + 1 / (2 : ℝ)^(j + 2)) *
      (1 + 1 / ((j : ℝ) + 1)) * (4 / Real.pi^2)) *
      (((j : ℝ) + 1) * (Real.pi^2 / 4)) =
      (1 + 1 / (2 : ℝ)^(j + 2)) * (((j : ℝ) + 1) + 1) := by
    field_simp
  rw [heq] at h
  exact physical_eventual_bound_fixed (j + 1) (by omega) ((j : ℝ) + 1)
    (by positivity) (4 / Real.pi^2 + ε) (by simpa only [Nat.add_assoc] using h)

private noncomputable def cosineScaledLowerCoefficient (L : ℕ) : ℝ :=
  (1 - 4 / (2 * ((L + 1 : ℕ) : ℝ) + 1)) /
    (((L + 1 : ℕ) : ℝ)^2 * mixedGap (L + 1))

private theorem cosine_scaled_lower_limit :
    Tendsto cosineScaledLowerCoefficient atTop (𝓝 (4 / Real.pi^2)) := by
  have hr : Tendsto (fun L : ℕ => 1 / ((L + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h : Tendsto (fun L : ℕ => 1 / ((L : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h
  have hf : Tendsto (fun L : ℕ => 4 / (2 * ((L + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) := by
    have heq : (fun L : ℕ => 4 / (2 * ((L + 1 : ℕ) : ℝ) + 1)) =
        fun L : ℕ => (4 * (1 / ((L + 1 : ℕ) : ℝ))) / (2 + 1 / ((L + 1 : ℕ) : ℝ)) := by
      funext L
      have hL : (0 : ℝ) < (L + 1 : ℕ) := by positivity
      field_simp
    rw [heq]
    have h := (hr.const_mul 4).div (hr.const_add 2) (by norm_num : (2 : ℝ) + 0 ≠ 0)
    rw [show (4 : ℝ) * 0 / (2 + 0) = 0 by norm_num] at h
    exact h.congr (fun L => rfl)
  have hg : Tendsto (fun L : ℕ => ((L + 1 : ℕ) : ℝ)^2 * mixedGap (L + 1))
      atTop (𝓝 (Real.pi^2 / 4)) :=
    (tendsto_add_atTop_iff_nat 1).2 mixed_gap_scaled_limit
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hf).div hg (by positivity)
  rw [show ((1 : ℝ) - 0) / (Real.pi^2 / 4) = 4 / Real.pi^2 by field_simp; norm_num] at h
  exact h.congr (fun L => rfl)

/-- The nonnegative cosine family asymptotically attains the physical inverse
coefficient `4 / Real.pi^2`, with every positive epsilon slack. -/
theorem fermiDyadicCosine_asymptotic_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ L : ℕ, R ≤ L →
      (4 / Real.pi^2 - ε) * ((L + 1 : ℕ) : ℝ)^2 *
          fermiSelectedTotalPronicEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) ≤
        sieveTotalPronicEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) := by
  have hc := cosine_scaled_lower_limit.eventually_const_lt
    (show 4 / Real.pi^2 - ε < 4 / Real.pi^2 by linarith)
  have hg : Tendsto (fun L : ℕ => ((L + 1 : ℕ) : ℝ)^2 * mixedGap (L + 1))
      atTop (𝓝 (Real.pi^2 / 4)) :=
    (tendsto_add_atTop_iff_nat 1).2 mixed_gap_scaled_limit
  have hd := hg.eventually_const_lt (show (0 : ℝ) < Real.pi^2 / 4 by positivity)
  obtain ⟨R, hR⟩ := eventually_atTop.mp (hc.and hd)
  refine ⟨max R 1, ?_⟩
  intro L hL
  have hLR : R ≤ L := le_trans (le_max_left R 1) hL
  have hL1 : 1 ≤ L := le_trans (le_max_right R 1) hL
  obtain ⟨hcoef, hden⟩ := hR L hLR
  let r : ℝ := ((L + 1 : ℕ) : ℝ)
  let S : ℝ := (2 * r + 1) / 4
  let g : ℝ := mixedGap (L + 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hS : 0 < S := by dsimp [S]; positivity
  have hgpos : 0 < g := (mul_pos_iff_of_pos_left (sq_pos_of_pos hr)).mp hden
  have hQ := fermiDyadicCosine_selected_pos L
  have hbase := fermiDyadicCosine_physical_ratio L hL1
  change (S - 1) * fermiSelectedTotalPronicEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) ≤
    g * S * sieveTotalPronicEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) at hbase
  have halg : cosineScaledLowerCoefficient L * (r^2 * g) * S = S - 1 := by
    change ((1 - 4 / (2 * r + 1)) / (r^2 * g)) * (r^2 * g) * S = S - 1
    rw [div_mul_cancel₀ _ (ne_of_gt hden)]
    dsimp only [S]
    field_simp
  have hm := mul_lt_mul_of_pos_right hcoef (mul_pos hden hS)
  have hcoeff : (4 / Real.pi^2 - ε) * (r^2 * g) * S ≤ S - 1 := by
    nlinarith only [hm, halg]
  apply le_of_mul_le_mul_left (a := g * S) ?_ (mul_pos hgpos hS)
  calc
    _ = ((4 / Real.pi^2 - ε) * (r^2 * g) * S) *
        fermiSelectedTotalPronicEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) := by ring
    _ ≤ (S - 1) * fermiSelectedTotalPronicEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) :=
      mul_le_mul_of_nonneg_right hcoeff hQ.le
    _ ≤ _ := hbase

/-- The sharp quadratic leading coefficient of the physical inverse estimate
on nonnegative inputs at dyadic horizons is `4 / Real.pi^2`. -/
theorem fermiPhysicalTrace_asymptotic_nonnegative_constant_iff (C : ℝ) :
    (∀ ε : ℝ, 0 < ε → ∃ R : ℕ, ∀ r : ℕ, R ≤ r → ∀ c : ℕ → ℝ,
      (∀ d : ℕ, 0 ≤ c d) → sieveTotalPronicEnergy (2^r) c ≤
        (C + ε) * (r : ℝ)^2 * fermiSelectedTotalPronicEnergy (2^r) c) ↔
      4 / Real.pi^2 ≤ C := by
  constructor
  · intro h
    by_contra hC
    have hC' : C < 4 / Real.pi^2 := lt_of_not_ge hC
    let ε := (4 / Real.pi^2 - C) / 3
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨RU, hU⟩ := h ε hε
    obtain ⟨RL, hLow⟩ := fermiDyadicCosine_asymptotic_lower ε hε
    let L := max RU RL
    have hRU : RU ≤ L + 1 := by dsimp [L]; omega
    have hRL : RL ≤ L := by dsimp [L]; omega
    have hu := hU (L + 1) hRU (fermiDyadicCosineWeight L) (fermiDyadicCosineWeight_nonneg L)
    have hl := hLow L hRL
    have hz : 0 < ((L + 1 : ℕ) : ℝ)^2 *
        fermiSelectedTotalPronicEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) :=
      mul_pos (sq_pos_of_pos (by positivity)) (fermiDyadicCosine_selected_pos L)
    have he : C + ε < 4 / Real.pi^2 - ε := by dsimp [ε]; linarith
    have hs := mul_lt_mul_of_pos_right he hz
    nlinarith only [hu, hl, hs]
  · intro hC ε hε
    obtain ⟨R, hR⟩ := sieveTotalPronicEnergy_asymptotic_upper
      (C + ε - 4 / Real.pi^2) (by linarith)
    rw [show 4 / Real.pi^2 + (C + ε - 4 / Real.pi^2) = C + ε by ring] at hR
    exact ⟨R, fun r hr c _ => hR r hr c⟩

/-- Allowing arbitrary signed inputs preserves the sharp dyadic physical
inverse coefficient `4 / Real.pi^2`. -/
theorem fermiPhysicalTrace_asymptotic_constant_iff (C : ℝ) :
    (∀ ε : ℝ, 0 < ε → ∃ R : ℕ, ∀ r : ℕ, R ≤ r → ∀ c : ℕ → ℝ,
      sieveTotalPronicEnergy (2^r) c ≤
        (C + ε) * (r : ℝ)^2 * fermiSelectedTotalPronicEnergy (2^r) c) ↔
      4 / Real.pi^2 ≤ C := by
  constructor
  · intro h
    apply (fermiPhysicalTrace_asymptotic_nonnegative_constant_iff C).1
    intro ε hε
    obtain ⟨R, hR⟩ := h ε hε
    exact ⟨R, fun r hr c _ => hR r hr c⟩
  · intro hC ε hε
    obtain ⟨R, hR⟩ := sieveTotalPronicEnergy_asymptotic_upper
      (C + ε - 4 / Real.pi^2) (by linarith)
    rw [show 4 / Real.pi^2 + (C + ε - 4 / Real.pi^2) = C + ε by ring] at hR
    exact ⟨R, hR⟩

end GaloisForLFunctions.TransHorizonIncidenceMechanics

