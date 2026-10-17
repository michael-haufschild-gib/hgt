import GaloisForLFunctions.BiScaleUncertainty.ArithmeticMultiplierCollisionControl

/-!
# Uniform dyadic frames for odd-source hyperbolic multipliers

Hyperbolic decay bounds the arithmetic collision energy independently of chain
length. Original-source variance supplies a uniform sine-multiplier frame radius.
Explicit source errors preserve an unconditional full secant/plastic receiver.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.DyadicMultiplierFrame
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open CenteredHyperbolicGram ProjectedHyperbolicGram ArithmeticMultiplierCollisions
noncomputable section

def weightEnergy (N : ℕ) (w : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range (N + 1), w i ^ 2

theorem weightEnergy_nonneg (N : ℕ) (w : ℕ → ℝ) : 0 ≤ weightEnergy N w :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem pair_bounds {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ pairSet N) :
    p.1 ≤ N ∧ p.2 ≤ N ∧ p.1 ≠ p.2 := by
  simpa only [pairSet, Finset.mem_offDiag, Finset.mem_range, Nat.lt_succ_iff] using hp

/-- Positive and negative lag packets have equal amplitudes, for arbitrary signed weights. -/
theorem lagAmplitude_reflect (N : ℕ) (α δ : ℝ) (w : ℕ → ℝ) (r : ℕ) (hr : r ≤ 2 * N) :
    lagAmplitude N α δ w (2 * N - r) = lagAmplitude N α δ w r := by
  unfold lagAmplitude
  apply Finset.sum_bij (fun p _ => (p.2, p.1))
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hb := pair_bounds hp'.1
    have hs := hp'.2
    unfold lagSlot at hs
    simp only [lagPairs, Finset.mem_filter, pairSet, Finset.mem_offDiag,
      Finset.mem_range, lagSlot]
    omega
  · intro p _ q _ hpq
    exact Prod.ext (congrArg Prod.snd hpq) (congrArg Prod.fst hpq)
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hb := pair_bounds hp'.1
    have hs := hp'.2
    unfold lagSlot at hs
    refine ⟨(p.2, p.1), ?_, rfl⟩
    simp only [lagPairs, Finset.mem_filter, pairSet, Finset.mem_offDiag,
      Finset.mem_range, lagSlot]
    omega
  · intro p _
    unfold differenceWeight differenceNode chainNode
    rw [show α * ((p.1 : ℝ) * δ - (p.2 : ℝ) * δ) =
      -(α * ((p.2 : ℝ) * δ - (p.1 : ℝ) * δ)) by ring, Real.cosh_neg]
    ring

theorem collisionEnergy_eq_two_positive (N : ℕ) (α δ : ℝ) (w : ℕ → ℝ) :
    collisionEnergy N α δ w =
      2 * ∑ k ∈ Finset.range N, lagAmplitude N α δ w (N + (k + 1)) ^ 2 := by
  have hrev : (∑ r ∈ Finset.range N, lagAmplitude N α δ w r ^ 2) =
      ∑ k ∈ Finset.range N, lagAmplitude N α δ w (N + (k + 1)) ^ 2 := by
    rw [← Finset.sum_range_reflect (fun r => lagAmplitude N α δ w r ^ 2) N]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have h := lagAmplitude_reflect N α δ w (N - 1 - k) (by omega)
    rw [show 2 * N - (N - 1 - k) = N + (k + 1) by omega] at h
    rw [h]
  have hsum := Finset.sum_range_add (fun r => lagAmplitude N α δ w r ^ 2) N (N + 1)
  have ht : (∑ r ∈ Finset.range (N + 1), lagAmplitude N α δ w (N + r) ^ 2) =
      ∑ k ∈ Finset.range N, lagAmplitude N α δ w (N + (k + 1)) ^ 2 := by
    rw [Finset.sum_range_succ']
    simp [lagAmplitude_center]
  rw [show N + (N + 1) = 2 * N + 1 by omega, ht] at hsum
  unfold collisionEnergy
  rw [hsum, hrev]
  ring

private theorem aperiodic_sq_le (N k : ℕ) (w : ℕ → ℝ) (hk : k ≤ N) :
    (∑ i ∈ Finset.range (N + 1 - k), w i * w (i + k)) ^ 2 ≤ weightEnergy N w ^ 2 := by
  let M := N + 1 - k
  have hMk : M + k = N + 1 := by dsimp [M]; omega
  have hkM : k + M = N + 1 := by omega
  have hL : (∑ i ∈ Finset.range M, w i ^ 2) ≤ weightEnergy N w := by
    have h := Finset.sum_range_add (fun i => w i ^ 2) M k
    rw [hMk] at h
    have hn : 0 ≤ ∑ i ∈ Finset.range k, w (M + i) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    unfold weightEnergy
    linarith
  have hR : (∑ i ∈ Finset.range M, w (i + k) ^ 2) ≤ weightEnergy N w := by
    have h := Finset.sum_range_add (fun i => w i ^ 2) k M
    rw [hkM] at h
    have he : (∑ i ∈ Finset.range M, w (k + i) ^ 2) =
        ∑ i ∈ Finset.range M, w (i + k) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm]
    rw [he] at h
    have hn : 0 ≤ ∑ i ∈ Finset.range k, w i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    unfold weightEnergy
    linarith
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range M) w (fun i => w (i + k))
  have hprod := mul_le_mul hL hR (Finset.sum_nonneg fun _ _ => sq_nonneg _) (weightEnergy_nonneg N w)
  change (∑ i ∈ Finset.range M, w i * w (i + k)) ^ 2 ≤ _
  nlinarith only [h, hprod]

private theorem dyadic_cosh_sq_ge (k : ℕ) :
    (2 : ℝ) ^ k ≤ (2 * Real.cosh ((1 / 2 : ℝ) * ((k : ℝ) * Real.log 2))) ^ 2 := by
  let t := (1 / 2 : ℝ) * ((k : ℝ) * Real.log 2)
  have h : Real.exp t ≤ 2 * Real.cosh t := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-t)]
  have he : Real.exp t ^ 2 = (2 : ℝ) ^ k := by
    rw [sq, ← Real.exp_add, show t + t = (k : ℝ) * Real.log 2 by dsimp [t]; ring,
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  change _ ≤ (2 * Real.cosh t) ^ 2
  rw [← he]
  nlinarith [Real.exp_pos t, Real.cosh_pos t]

theorem dyadic_lag_sq_le (N k : ℕ) (w : ℕ → ℝ) (hk : 1 ≤ k) (hkN : k ≤ N) :
    lagAmplitude N (1 / 2) (Real.log 2) w (N + k) ^ 2 ≤ weightEnergy N w ^ 2 / (2 : ℝ) ^ k := by
  rw [lagAmplitude_positive N k (1 / 2) (Real.log 2) w hk hkN, div_pow]
  exact div_le_div₀ (sq_nonneg _) (aperiodic_sq_le N k w hkN) (by positivity) (dyadic_cosh_sq_ge k)

private theorem dyadic_sum_le_one (N : ℕ) :
    (∑ k ∈ Finset.range N, 1 / (2 : ℝ) ^ (k + 1)) ≤ 1 := by
  have he : ∀ n : ℕ, (∑ k ∈ Finset.range n, 1 / (2 : ℝ) ^ (k + 1)) + 1 / (2 : ℝ) ^ n = 1 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      have hh : 1 / (2 : ℝ) ^ (n + 1) + 1 / (2 : ℝ) ^ (n + 1) = 1 / (2 : ℝ) ^ n := by
        rw [pow_succ]
        field_simp
        ring
      rw [Finset.sum_range_succ, add_assoc, hh]
      exact ih
  have hn : 0 ≤ 1 / (2 : ℝ) ^ N := by positivity
  linarith [he N]

/-- Hyperbolic decay makes the dyadic collision constant independent of chain length. -/
theorem dyadic_collisionEnergy_le (N : ℕ) (w : ℕ → ℝ) :
    collisionEnergy N (1 / 2) (Real.log 2) w ≤ 2 * weightEnergy N w ^ 2 := by
  rw [collisionEnergy_eq_two_positive]
  have h : (∑ k ∈ Finset.range N, lagAmplitude N (1 / 2) (Real.log 2) w (N + (k + 1)) ^ 2) ≤
      ∑ k ∈ Finset.range N, weightEnergy N w ^ 2 / (2 : ℝ) ^ (k + 1) :=
    Finset.sum_le_sum fun k hk => dyadic_lag_sq_le N (k + 1) w (by omega)
      (by have := Finset.mem_range.mp hk; omega)
  have he : (∑ k ∈ Finset.range N, weightEnergy N w ^ 2 / (2 : ℝ) ^ (k + 1)) =
      weightEnergy N w ^ 2 * ∑ k ∈ Finset.range N, 1 / (2 : ℝ) ^ (k + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [he] at h
  have hb := mul_le_mul_of_nonneg_left (dyadic_sum_le_one N) (sq_nonneg (weightEnergy N w))
  nlinarith only [h, hb]

/-- A source-variance radius independent of the dyadic chain length. -/
def frameRadius (f : C_c(ℝ, ℝ)) : ℝ := Real.sqrt (2 * sourceVariance f (1 / 2))

theorem sqrt_variance_collision_le (f : C_c(ℝ, ℝ)) (N : ℕ) (w : ℕ → ℝ) :
    Real.sqrt (sourceVariance f (1 / 2) * collisionEnergy N (1 / 2) (Real.log 2) w) ≤
      frameRadius f * weightEnergy N w := by
  have hV := sourceVariance_nonneg f (1 / 2)
  have hW := weightEnergy_nonneg N w
  have h := mul_le_mul_of_nonneg_left (dyadic_collisionEnergy_le N w) hV
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) hW, ?_⟩
  unfold frameRadius
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * sourceVariance f (1 / 2))]
  nlinarith only [h]

/-- The original doubled zero range gives a uniform multiplier frame radius. -/
theorem odd_defect_abs_le_frame_of_double_zeros (f : C_c(ℝ, ℝ)) (N : ℕ) (w : ℕ → ℝ)
    (hz : ∀ m : ℕ, 1 ≤ m → m ≤ 2 * N →
      autocorr (oddCompactSource f) ((m : ℝ) * Real.log 2) = 0) :
    |sinhCliqueGramDefect (oddCompactSource f) (1 / 2)
      (Finset.range (N + 1)) w (chainNode (Real.log 2))| ≤
        frameRadius (oddCompactSource f) * weightEnergy N w :=
  (odd_defect_abs_le_variance_collision f N (1 / 2) (Real.log 2) w hz).trans
    (sqrt_variance_collision_le _ N w)

/-- Full source logarithmic blindness also yields the same chain-independent radius. -/
theorem odd_logGrid_defect_abs_le_frame (f : C_c(ℝ, ℝ)) (N : ℕ) (w : ℕ → ℝ)
    (hz : ∀ n : ℕ, 2 ≤ n → autocorr (oddCompactSource f) (Real.log (n : ℝ)) = 0) :
    |sinhCliqueGramDefect (oddCompactSource f) (1 / 2)
      (Finset.range (N + 1)) w (chainNode (Real.log 2))| ≤
        frameRadius (oddCompactSource f) * weightEnergy N w :=
  (odd_logGrid_defect_abs_le_variance_collision f N (1 / 2) w hz).trans
    (sqrt_variance_collision_le _ N w)

/-- An actual multiplier frame inequality; no multiplier zeros are assumed. -/
theorem odd_sinhGram_le_frame_of_double_zeros (f : C_c(ℝ, ℝ)) (N : ℕ) (w : ℕ → ℝ)
    (hz : ∀ m : ℕ, 1 ≤ m → m ≤ 2 * N →
      autocorr (oddCompactSource f) ((m : ℝ) * Real.log 2) = 0) :
    translationGramEnergy (sinhCompact (1 / 2) (oddCompactSource f))
      (Finset.range (N + 1)) w (chainNode (Real.log 2)) ≤
        (autocorr (sinhCompact (1 / 2) (oddCompactSource f)) 0 +
          frameRadius (oddCompactSource f)) * weightEnergy N w := by
  have h := (le_abs_self _).trans (odd_defect_abs_le_frame_of_double_zeros f N w hz)
  rw [sinhGram_eq_diagonal_add_defect]
  change _ * weightEnergy N w + _ ≤ _
  nlinarith only [h]

/-- Source-error term retained away from exact source grids. -/
def frameSourceError (f : C_c(ℝ, ℝ)) (N : ℕ) (w : ℕ → ℝ) : ℝ :=
  lagCorrection f N (1 / 2) (sourceMean f (1 / 2)) (Real.log 2) w +
    Real.sqrt (autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0 *
      max (crossLagError f N (1 / 2) (Real.log 2) w) 0)

/-- Uniform diagonal frame term together with all necessary original-source errors. -/
def frameGramUpper (f : C_c(ℝ, ℝ)) (N : ℕ) (w : ℕ → ℝ) : ℝ :=
  (autocorr (sinhCompact (1 / 2) f) 0 + frameRadius f) * weightEnergy N w +
    frameSourceError f N w

theorem frameSourceError_eq_zero_of_double_zeros (f : C_c(ℝ, ℝ)) (N : ℕ) (w : ℕ → ℝ)
    (hz : ∀ m : ℕ, 1 ≤ m → m ≤ 2 * N → autocorr f ((m : ℝ) * Real.log 2) = 0) :
    frameSourceError f N w = 0 := by
  have ho := arithmetic_progression_pairwise_orth (f := (f : ℝ → ℝ)) 0 (Real.log 2) N
    (fun m hm hmn => hz m hm (by omega))
  have he : lagCorrection f N (1 / 2) (sourceMean f (1 / 2)) (Real.log 2) w = 0 := by
    rw [← sourceCorrection_eq_lags]
    apply Finset.sum_eq_zero
    intro p hp
    have hp' := Finset.mem_offDiag.mp hp
    have hh := ho p.2 hp'.2.1 p.1 hp'.1 (Ne.symm hp'.2.2)
    simp only [zero_add] at hh
    change _ * autocorr f ((p.2 : ℝ) * Real.log 2 - (p.1 : ℝ) * Real.log 2) = 0
    rw [hh, mul_zero]
  unfold frameSourceError
  rw [he, crossLagError_eq_zero_of_double_zeros f N (1 / 2) (Real.log 2) w hz]
  norm_num

theorem frameGramUpper_of_double_zeros (f : C_c(ℝ, ℝ)) (N : ℕ) (w : ℕ → ℝ)
    (hz : ∀ m : ℕ, 1 ≤ m → m ≤ 2 * N → autocorr f ((m : ℝ) * Real.log 2) = 0) :
    frameGramUpper f N w =
      (autocorr (sinhCompact (1 / 2) f) 0 + frameRadius f) * weightEnergy N w := by
  rw [frameGramUpper, frameSourceError_eq_zero_of_double_zeros f N w hz, add_zero]

theorem sourceDefectUpper_le_frame (f : C_c(ℝ, ℝ)) (N : ℕ) (w : ℕ → ℝ) :
    sourceDefectUpper f (1 / 2) (sourceMean f (1 / 2))
      (Finset.range (N + 1)) w (chainNode (Real.log 2)) ≤
        frameRadius f * weightEnergy N w + frameSourceError f N w := by
  let Q := autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0
  let R := autocorr f 0
  let V := sourceVariance f (1 / 2)
  let A := collisionEnergy N (1 / 2) (Real.log 2) w
  let Z := crossLagError f N (1 / 2) (Real.log 2) w
  let W := weightEnergy N w
  have hQ : 0 ≤ Q := autocorr_zero_nonneg _
  have hV : 0 ≤ V := sourceVariance_nonneg _ _
  have hW : 0 ≤ W := weightEnergy_nonneg N w
  have hqr : Q * R = V := mean_energy_mul_source_eq_variance f (1 / 2)
  have hA : A ≤ 2 * W ^ 2 := dyadic_collisionEnergy_le N w
  have hprod : Q * (R * A + Z) ≤ 2 * V * W ^ 2 + Q * max Z 0 := by
    calc
      Q * (R * A + Z) = V * A + Q * Z := by rw [mul_add, ← mul_assoc, hqr]
      _ ≤ V * (2 * W ^ 2) + Q * max Z 0 :=
        add_le_add (mul_le_mul_of_nonneg_left hA hV)
          (mul_le_mul_of_nonneg_left (le_max_left Z 0) hQ)
      _ = _ := by ring
  have hr : Real.sqrt (Q * (R * A + Z)) ≤
      Real.sqrt (2 * V) * W + Real.sqrt (Q * max Z 0) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hs : (Real.sqrt (2 * V) * W) ^ 2 = 2 * V * W ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * V)]
    have he := Real.sq_sqrt (mul_nonneg hQ (le_max_right Z 0))
    have hc : 0 ≤ (Real.sqrt (2 * V) * W) * Real.sqrt (Q * max Z 0) := by positivity
    nlinarith only [hprod, hs, he, hc]
  unfold sourceDefectUpper frameSourceError frameRadius
  rw [sourceCorrection_eq_lags,
    show (Finset.range (N + 1)).offDiag = pairSet N from rfl,
    differenceGram_eq_collision_add_error]
  change _ + Real.sqrt (Q * (R * A + Z)) ≤ Real.sqrt (2 * V) * W +
    (_ + Real.sqrt (Q * max Z 0))
  linarith only [hr]

/-- Unconditional source-error-aware frame bound for the actual odd multiplier. -/
theorem odd_sinhGram_le_frameGramUpper (f : C_c(ℝ, ℝ)) (N : ℕ) (w : ℕ → ℝ) :
    translationGramEnergy (sinhCompact (1 / 2) (oddCompactSource f))
      (Finset.range (N + 1)) w (chainNode (Real.log 2)) ≤
        frameGramUpper (oddCompactSource f) N w := by
  have h := (odd_defect_le_sourceDefectUpper f (1 / 2)
    (sourceMean (oddCompactSource f) (1 / 2)) (Finset.range (N + 1)) w
    (chainNode (Real.log 2))).trans (sourceDefectUpper_le_frame _ N w)
  rw [sinhGram_eq_diagonal_add_defect]
  unfold frameGramUpper
  change _ * weightEnergy N w + _ ≤ _
  nlinarith only [h]

/-- Dyadic jump lower bound obtained from the uniform frame envelope. -/
def frameJumpBound (f : C_c(ℝ, ℝ)) (N : ℕ) (b : ℕ → ℝ) (y : ℝ) : ℝ :=
  autocorr (sinhCompact (1 / 2) f) 0 *
      (∑ i ∈ Finset.range (N + 1), sinhJumpTransferWeights f b (chainNode (Real.log 2)) y i *
        Real.cosh ((chainNode (Real.log 2) i - y) / 2)) -
    Real.sqrt (autocorr (sinhCompact (1 / 2) f) 0 *
      max (frameGramUpper f N (sinhJumpTransferWeights f b (chainNode (Real.log 2)) y)) 0)

/-- Exact source-grid specialization removes both explicit source errors. -/
theorem frameJumpBound_of_double_zeros (f : C_c(ℝ, ℝ)) (N : ℕ) (b : ℕ → ℝ) (y : ℝ)
    (hz : ∀ m : ℕ, 1 ≤ m → m ≤ 2 * N → autocorr f ((m : ℝ) * Real.log 2) = 0) :
    frameJumpBound f N b y =
      autocorr (sinhCompact (1 / 2) f) 0 *
        (∑ i ∈ Finset.range (N + 1), sinhJumpTransferWeights f b (chainNode (Real.log 2)) y i *
          Real.cosh ((chainNode (Real.log 2) i - y) / 2)) -
      Real.sqrt (autocorr (sinhCompact (1 / 2) f) 0 *
        ((autocorr (sinhCompact (1 / 2) f) 0 + frameRadius f) *
          weightEnergy N (sinhJumpTransferWeights f b (chainNode (Real.log 2)) y))) := by
  unfold frameJumpBound
  rw [frameGramUpper_of_double_zeros f N _ hz, max_eq_left]
  exact mul_nonneg (add_nonneg (autocorr_zero_nonneg _) (Real.sqrt_nonneg _))
    (weightEnergy_nonneg _ _)

theorem odd_frameJumpBound_le_gram (f : C_c(ℝ, ℝ)) (N : ℕ) (b : ℕ → ℝ) (y : ℝ) :
    frameJumpBound (oddCompactSource f) N b y ≤
      sinhJumpGramBound (oddCompactSource f) (Finset.range (N + 1)) b (chainNode (Real.log 2)) y := by
  have h := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
    ((odd_sinhGram_le_frameGramUpper f N
      (sinhJumpTransferWeights (oddCompactSource f) b (chainNode (Real.log 2)) y)).trans
      (le_max_left _ 0)) (autocorr_zero_nonneg (sinhCompact (1 / 2) (oddCompactSource f))))
  unfold frameJumpBound sinhJumpGramBound
  linarith only [h]

theorem odd_secantJumpCollar_ge_frame (f : C_c(ℝ, ℝ)) (N : ℕ) (b : ℕ → ℝ) (y : ℝ) :
    frameJumpBound (oddCompactSource f) N b y ≤
      secantJumpCollar (oddCompactSource f) (Finset.range (N + 1)) b (chainNode (Real.log 2)) y :=
  (odd_frameJumpBound_le_gram f N b y).trans (secantJumpCollar_ge_gram _ _ _ _ _)

theorem continuous_frameJumpBound (f : C_c(ℝ, ℝ)) (N : ℕ) (b : ℕ → ℝ) :
    Continuous (frameJumpBound f N b) := by
  let t := chainNode (Real.log 2)
  let v := sinhJumpTransferWeights f b t
  have hv := continuous_sinhJumpTransferWeights f b t
  have ha (r : ℕ) : Continuous (fun y => lagAmplitude N (1 / 2) (Real.log 2) (v y) r) := by
    unfold lagAmplitude differenceWeight
    exact continuous_finsetSum _ fun p _ => ((hv p.1).mul (hv p.2)).div_const _
  have he : Continuous (fun y => lagCorrection f N (1 / 2) (sourceMean f (1 / 2))
      (Real.log 2) (v y)) := by
    unfold lagCorrection
    exact continuous_finsetSum _ fun r _ => ((ha r).mul continuous_const).mul continuous_const
  have hz : Continuous (fun y => crossLagError f N (1 / 2) (Real.log 2) (v y)) := by
    unfold crossLagError
    exact continuous_finsetSum _ fun p _ => ((ha p.1).mul (ha p.2)).mul continuous_const
  have hw : Continuous (fun y => weightEnergy N (v y)) :=
    continuous_finsetSum _ fun i _ => (hv i).pow 2
  have hu : Continuous (fun y => frameGramUpper f N (v y)) := by
    unfold frameGramUpper frameSourceError
    exact (continuous_const.mul hw).add (he.add
      (Real.continuous_sqrt.comp (continuous_const.mul (hz.max continuous_const))))
  unfold frameJumpBound
  exact (continuous_const.mul (continuous_finsetSum _ fun i _ =>
    (hv i).mul (by fun_prop))).sub
      (Real.continuous_sqrt.comp (continuous_const.mul (hu.max continuous_const)))

/-- Full secant energy receives the uniform dyadic frame bound without source-zero assumptions. -/
theorem odd_secantEnergy_ge_frame (f : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ y in (0 : ℝ)..Real.log 2, frameJumpBound (oddCompactSource f) N (fun _ => 1) (-y)) ≤
      biScaleSecantEnergy (oddCompactSource f) := by
  have hd : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have h := biScaleSecantEnergy_ge_sinhJumpGram (oddCompactSource f) (Real.log 2) (N + 1)
  rw [abs_of_nonneg hd] at h
  refine le_trans ?_ h
  exact intervalIntegral.integral_mono_on (μ := volume) hd
    (((continuous_frameJumpBound _ _ _).comp continuous_neg).intervalIntegrable _ _)
    (((continuous_sinhJumpGramBound _ _ _ _).comp continuous_neg).intervalIntegrable _ _)
    (fun y _ => odd_frameJumpBound_le_gram f N (fun _ => 1) (-y))

/-- Unconditional actual plastic receiver, retaining the positive remainder and odd moment. -/
theorem odd_plasticCrossover_ge_frame (f : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ y in (0 : ℝ)..Real.log 2, frameJumpBound (oddCompactSource f) N (fun _ => 1) (-y)) +
      plasticRemainderEnergy (oddCompactSource f) -
        2 * (∫ u, oddCompactSource f u * Real.sinh (u / 2)) ^ 2 ≤
      plasticCrossover (oddCompactSource f) := by
  have h := odd_secantEnergy_ge_frame f N
  rw [plasticCrossover_eq_secant_add_remainder_add_moment, hyperbolicMomentEnergy_oddSource]
  linarith

end
end GaloisForLFunctions.BiScaleUncertainty.DyadicMultiplierFrame
