import GaloisForLFunctions.CompletedArithmeticForms.CompleteWeilConductorAveragePositivity
import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandOverlapAndNonRatioBounds

/-!
# Emptiness of Exceptional Conductors Above Polylogarithmic Scales

This module evaluates `completeWeilEnergy φ c N` individually on every normalized Ramanujan
horizon mode `v_m = normalizedRamanujanHorizonVector m N` up to the Bombieri–Vinogradov
square-root barrier `m ≤ ⌊N^θ⌋₊` (`0 < θ < 1 / 2`) across power-of-logarithm overlaps
`1 ≤ c ≤ (log N)^α` (`0 < α < 1 / 4`), proving that for every `A > 8 * α`:

* **Diverging positive single-mode floor (`eventually_completeWeilEnergy_mode_ge_log_above_polylog`).**
  Eventually in `N`, for all `1 ≤ c ≤ (log N)^α` and all `m ∈ Icc ⌈(log N)^A⌉₊ ⌊N^θ⌋₊`,
  `((1 - 2 * θ) / 4) * Real.log m ≤ completeWeilEnergy φ c N v_m`.
* **Structural emptiness of exceptional conductors (`eventually_exceptionalConductors_above_polylog_empty`).**
  The exceptional conductor set `{m ∈ Icc ⌈(log N)^A⌉₊ ⌊N^θ⌋₊ | completeWeilEnergy φ c N v_m ≤ 0}`
  is identically `∅` eventually in `N` — no Siegel-type exceptional conductor exists anywhere
  between `(log N)^A` and `N^θ`.
-/

noncomputable section

open MeasureTheory Finset Filter Topology ArithmeticFunction
open scoped BigOperators RealInnerProductSpace

namespace GaloisForLFunctions.CompletedArithmeticForms

open SignedArithmeticHodgeTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell
  ArithmeticIntersectionTheory ArithmeticEffectivityTheory BezoutValuationIncidence
  SuccessorShellArithmetic CriticalArithmeticCorrelationTheory
  SpacingScaleHarmonicAnalysis HTGeometry

/-! ## Section 1: Zero-Mean Periodic Partial Sums and Single-Mode Two-Pole Bounds -/

private theorem sum_range_normalizedRamanujanMode_eq_zero {m : ℕ} (hm : 2 ≤ m) :
    (∑ j ∈ range m, normalizedRamanujanMode m j) = 0 := by
  have hm0 : 0 < m := by omega
  have hp := periodMean_normalizedRamanujanMode_mul hm0 one_pos dvd_rfl (one_dvd m) hm0
  rw [if_neg (by omega : m ≠ 1)] at hp
  unfold periodMean at hp
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0.ne'
  have hsum0 : (∑ j ∈ range m, normalizedRamanujanMode m j * normalizedRamanujanMode 1 j) = 0 :=
    (div_eq_zero_iff.mp hp).resolve_right hmR
  have hmode1 : ∀ j, normalizedRamanujanMode 1 j = 1 := fun j => by
    rw [normalizedRamanujanMode, ramanujanMode_one, Nat.totient_one, Nat.cast_one,
      Real.sqrt_one, div_one]
  simpa only [hmode1, mul_one] using hsum0

/-- Uniform `O(m)` partial-sum bound for `normalizedRamanujanMode m` (`2 ≤ m`) over every
interval `Ico l k`. -/
theorem abs_sum_Ico_normalizedRamanujanMode_le {m : ℕ} (hm : 2 ≤ m) {l k : ℕ} (_hlk : l ≤ k) :
    |∑ j ∈ Ico l k, normalizedRamanujanMode m j| ≤ (m : ℝ) := by
  have hm0 : 0 < m := by omega
  have hper := normalizedRamanujanMode_periodic hm0
  let q := (k - l) / m
  have hsplit : Ico l k = Ico l (l + q * m) ∪ Ico (l + q * m) k := by
    have hqm : q * m ≤ k - l := Nat.div_mul_le_self (k - l) m
    ext j; simp only [mem_Ico, mem_union]; omega
  have hdisj : Disjoint (Ico l (l + q * m)) (Ico (l + q * m) k) := by
    rw [Finset.disjoint_left]; intro j h1 h2; simp only [mem_Ico] at h1 h2; omega
  have hzero_periods : ∀ p : ℕ, (∑ j ∈ Ico l (l + p * m), normalizedRamanujanMode m j) = 0 := by
    intro p
    induction p with
    | zero => simp
    | succ p ih =>
      have hsucc : l + (p + 1) * m = (l + p * m) + m := by ring
      have hu : Ico l (l + (p + 1) * m) = Ico l (l + p * m) ∪ Ico (l + p * m) ((l + p * m) + m) := by
        rw [hsucc]; ext j; simp only [mem_Ico, mem_union]; omega
      have hd : Disjoint (Ico l (l + p * m)) (Ico (l + p * m) ((l + p * m) + m)) := by
        rw [Finset.disjoint_left]; intro j h1 h2; simp only [mem_Ico] at h1 h2; omega
      rw [hu, sum_union hd, ih, zero_add, sum_Ico_periodic_eq hm0 hper,
        sum_range_normalizedRamanujanMode_eq_zero hm]
  rw [hsplit, sum_union hdisj, hzero_periods q, zero_add]
  have hrem_sub : Ico (l + q * m) k ⊆ Ico (l + q * m) ((l + q * m) + m) := by
    have hdiv := Nat.div_add_mod (k - l) m
    have hmod := Nat.mod_lt (k - l) hm0
    have hqm : q * m = m * ((k - l) / m) := Nat.mul_comm _ _
    intro j hj; simp only [mem_Ico] at hj ⊢; omega
  have hper_abs : Function.Periodic (fun j => |normalizedRamanujanMode m j|) m :=
    fun j => by dsimp only; rw [hper j]
  calc
    |∑ j ∈ Ico (l + q * m) k, normalizedRamanujanMode m j| ≤
        ∑ j ∈ Ico (l + q * m) k, |normalizedRamanujanMode m j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Ico (l + q * m) ((l + q * m) + m), |normalizedRamanujanMode m j| :=
      sum_le_sum_of_subset_of_nonneg hrem_sub fun _ _ _ => abs_nonneg _
    _ = ∑ j ∈ range m, |normalizedRamanujanMode m j| :=
      sum_Ico_periodic_eq hm0 hper_abs (l + q * m)
    _ ≤ (m : ℝ) := sum_range_abs_normalizedRamanujanMode_le hm0

/-- Abel summation bounds the harmonic sum of `normalizedRamanujanMode m` (`2 ≤ m`) by `m`,
with no `log N` loss. -/
theorem abs_sum_Icc_normalizedRamanujanMode_div_le {m : ℕ} (hm : 2 ≤ m) (N : ℕ) :
    |∑ j ∈ Icc 1 N, normalizedRamanujanMode m j / (j : ℝ)| ≤ (m : ℝ) := by
  have hpartial : ∀ k ≤ N, |∑ i ∈ range k, normalizedRamanujanMode m (i + 1)| ≤ (m : ℝ) := by
    intro k _
    have heq : (∑ i ∈ range k, normalizedRamanujanMode m (i + 1)) =
        ∑ j ∈ Ico 1 (1 + k), normalizedRamanujanMode m j := by
      refine sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
      · intro i hi; have := mem_range.mp hi; exact mem_Ico.mpr ⟨by omega, by omega⟩
      · intro a _ b _ h; exact Nat.succ.inj h
      · intro j hj; obtain ⟨h1, h2⟩ := mem_Ico.mp hj
        exact ⟨j - 1, mem_range.mpr (by omega), by omega⟩
      · intro _ _; rfl
    rw [heq]
    exact abs_sum_Ico_normalizedRamanujanMode_le hm (Nat.le_add_right 1 k)
  have hab := abs_sum_mul_le_of_finite_partial
    (g := fun i => normalizedRamanujanMode m (i + 1))
    (w := fun i => 1 / ((i : ℝ) + 1))
    N hpartial (fun i => by positivity)
    (fun i => by apply one_div_le_one_div_of_le (by positivity); push_cast; linarith)
  have hbij : (∑ i ∈ range N, 1 / ((i : ℝ) + 1) * normalizedRamanujanMode m (i + 1)) =
      ∑ j ∈ Icc 1 N, normalizedRamanujanMode m j / (j : ℝ) := by
    refine sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
    · intro i hi; have := mem_range.mp hi; exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro a _ b _ h; exact Nat.succ.inj h
    · intro j hj; obtain ⟨h1, h2⟩ := mem_Icc.mp hj
      exact ⟨j - 1, mem_range.mpr (by omega), by omega⟩
    · intro i _; push_cast; ring
  rw [hbij, Nat.cast_zero, zero_add, one_div_one, mul_one] at hab
  exact hab

/-- Quadratic bound on `arithmeticPoleKernel` evaluated on a single Ramanujan mode `v_m` (`2 ≤ m`):
`|∑_{n,j} v_m(n) v_m(j) arithmeticPoleKernel n j| ≤ 2 m^2 / log N`. -/
private theorem abs_arithmeticPoleKernel_mode_le {m N : ℕ} (hm : 2 ≤ m) (hN : 2 ≤ N) :
    |∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
          primeHorizonExtension (normalizedRamanujanHorizonVector m N) j *
          arithmeticPoleKernel n j| ≤
      2 * (m : ℝ) ^ 2 / Real.log N := by
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsL : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL
  set v := primeHorizonExtension (normalizedRamanujanHorizonVector m N)
  have hv_sqrt : ∀ n ∈ Icc 1 N, v n * Real.sqrt n =
      (Real.sqrt (Real.log N))⁻¹ * normalizedRamanujanMode m n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    rw [primeHorizonExtension_coe _ ⟨n, hn⟩]
    change ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m n / Real.sqrt n)) *
      Real.sqrt n = _
    field_simp [(Real.sqrt_pos.mpr hn0).ne']
  have hv_div : ∀ j ∈ Icc 1 N, v j / Real.sqrt j =
      (Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m j / (j : ℝ)) := by
    intro j hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
    rw [primeHorizonExtension_coe _ ⟨j, hj⟩]
    change ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m j / Real.sqrt j)) /
      Real.sqrt j = _
    rw [div_div, ← sq, Real.sq_sqrt hj0.le]
    ring
  have hfact :
      (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, v n * v j * arithmeticPoleKernel n j) =
        (2 / Real.log N) * (∑ n ∈ Icc 1 N, normalizedRamanujanMode m n) *
          (∑ j ∈ Icc 1 N, normalizedRamanujanMode m j / (j : ℝ)) := by
    have hterm : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N,
        v n * v j * arithmeticPoleKernel n j =
          (Real.log N)⁻¹ * (normalizedRamanujanMode m n * (normalizedRamanujanMode m j / (j : ℝ)) +
            (normalizedRamanujanMode m n / (n : ℝ)) * normalizedRamanujanMode m j) := by
      intro n hn j hj
      have h1 : v n * v j * arithmeticPoleKernel n j =
          (v n * Real.sqrt n) * (v j / Real.sqrt j) +
            (v n / Real.sqrt n) * (v j * Real.sqrt j) := by
        unfold arithmeticPoleKernel; ring
      rw [h1, hv_sqrt n hn, hv_div j hj, hv_div n hn, hv_sqrt j hj]
      field_simp [hsL.ne', hL.ne']
      rw [Real.sq_sqrt hL.le]
      ring
    rw [sum_congr rfl fun n hn => sum_congr rfl fun j hj => hterm n hn j hj]
    simp only [← mul_sum, sum_add_distrib, ← sum_mul]
    ring
  have hIcc_Ico : Icc 1 N = Ico 1 (N + 1) := by ext n; simp only [mem_Icc, mem_Ico]; omega
  have hsum1 : |∑ n ∈ Icc 1 N, normalizedRamanujanMode m n| ≤ (m : ℝ) := by
    rw [hIcc_Ico]
    exact abs_sum_Ico_normalizedRamanujanMode_le hm (by omega)
  have hsum2 := abs_sum_Icc_normalizedRamanujanMode_div_le hm N
  rw [hfact, abs_mul, abs_mul, abs_of_pos (div_pos zero_lt_two hL)]
  calc
    (2 / Real.log N) * |∑ n ∈ Icc 1 N, normalizedRamanujanMode m n| *
        |∑ j ∈ Icc 1 N, normalizedRamanujanMode m j / (j : ℝ)| ≤
      (2 / Real.log N) * (m : ℝ) * (m : ℝ) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hsum1 (by positivity)) hsum2
        (abs_nonneg _) (by positivity)
    _ = 2 * (m : ℝ) ^ 2 / Real.log N := by ring

/-! ## Section 2: Single-Mode Norm, Pole Error, and Center Collar Bounds -/

/-- Upper bound `‖v_m‖² ≤ 19` and `‖v_m‖ ≤ 5` for every `2 ≤ m` with `m * m ≤ N` and `1 ≤ log N`. -/
private theorem normalizedRamanujanHorizonVector_norm_sq_le_nineteen {m N : ℕ}
    (hm : 2 ≤ m) (hmN : m * m ≤ N) (hlogN : 1 ≤ Real.log N) :
    ‖normalizedRamanujanHorizonVector m N‖ ^ 2 ≤ 19 ∧
      ‖normalizedRamanujanHorizonVector m N‖ ≤ 5 := by
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hlogN
  have hm_le_N : m ≤ N := (Nat.le_mul_self m).trans hmN
  have hlogm_le : Real.log m ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast (show 0 < m by omega)) (by exact_mod_cast hm_le_N)
  let a : ℕ → ℝ := fun k => if k = m then 1 else 0
  have hsum_v : (∑ k ∈ Icc 1 m, a k • normalizedRamanujanHorizonVector k N) =
      normalizedRamanujanHorizonVector m N := by
    simp [a, show m ∈ Icc 1 m from mem_Icc.mpr ⟨by omega, le_rfl⟩]
  have hsum_a : (∑ k ∈ Icc 1 m, a k ^ 2) = 1 := by
    simp [a, show m ∈ Icc 1 m from mem_Icc.mpr ⟨by omega, le_rfl⟩]
  have hgram := (abs_le.mp (abs_norm_sum_normalizedRamanujanHorizonVector_sq_sub_le hm hmN a)).2
  rw [hsum_v, hsum_a, mul_one] at hgram
  have hrat : 9 * (1 + Real.log m) / Real.log N ≤ 18 := by
    rw [div_le_iff₀ hL0]
    linarith only [hlogN, hlogm_le]
  have hsq : ‖normalizedRamanujanHorizonVector m N‖ ^ 2 ≤ 19 := by linarith only [hgram, hrat]
  refine ⟨hsq, ?_⟩
  have h25 : ‖normalizedRamanujanHorizonVector m N‖ ^ 2 ≤ 5 ^ 2 := by norm_num; exact hsq.trans (by norm_num)
  nlinarith only [h25, norm_nonneg (normalizedRamanujanHorizonVector m N)]

/-- Linear moment bound `∑_{n=1}^N (n / N) v_m(n)^2 ≤ 2 / log N` for `1 ≤ m ≤ N`. -/
private theorem sum_linear_moment_mode_sq_le {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N)
    (hL0 : 0 < Real.log N) :
    (∑ n ∈ Icc 1 N, ((n : ℝ) / N) *
        primeHorizonExtension (normalizedRamanujanHorizonVector m N) n ^ 2) ≤
      2 / Real.log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (hm.trans hmN)
  have hpt : ∀ n ∈ Icc 1 N,
      ((n : ℝ) / N) * primeHorizonExtension (normalizedRamanujanHorizonVector m N) n ^ 2 =
        (1 / ((N : ℝ) * Real.log N)) * normalizedRamanujanMode m n ^ 2 := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    rw [primeHorizonExtension_coe _ ⟨n, hn⟩]
    change ((n : ℝ) / N) *
      (((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m n / Real.sqrt n)) ^ 2) = _
    rw [mul_pow, inv_pow, div_pow, Real.sq_sqrt hL0.le, Real.sq_sqrt hn0.le]
    field_simp [hn0.ne', hN0.ne', hL0.ne']
  rw [sum_congr rfl hpt, ← mul_sum]
  have hp_sub : Icc 1 N ⊆ Ioc 0 (0 + (N / m + 1) * m) := by
    have hdiv := Nat.div_add_mod N m
    have hmod := Nat.mod_lt N hm
    have hmul : m * (N / m) = (N / m) * m := Nat.mul_comm _ _
    intro n hn; simp only [mem_Icc, mem_Ioc] at hn ⊢; omega
  have hper_sq : Function.Periodic (fun n => normalizedRamanujanMode m n ^ 2) m :=
    fun n => by dsimp only; rw [normalizedRamanujanMode_periodic hm n]
  have hsum_periods : ∀ p : ℕ, (∑ n ∈ Ioc 0 (p * m), normalizedRamanujanMode m n ^ 2) =
      (p : ℝ) * m := by
    intro p
    induction p with
    | zero => simp
    | succ p ih =>
      have hu : Ioc 0 ((p + 1) * m) = Ioc 0 (p * m) ∪ Ioc (p * m) (p * m + m) := by
        have : (p + 1) * m = p * m + m := by ring
        rw [this]; ext n; simp only [mem_Ioc, mem_union]; omega
      have hd : Disjoint (Ioc 0 (p * m)) (Ioc (p * m) (p * m + m)) := by
        rw [Finset.disjoint_left]; intro n h1 h2; simp only [mem_Ioc] at h1 h2; omega
      rw [hu, sum_union hd, ih, sum_Ioc_normalizedRamanujanMode_sq hm (p * m)]
      push_cast; ring
  have hsum_le : (∑ n ∈ Icc 1 N, normalizedRamanujanMode m n ^ 2) ≤ 2 * (N : ℝ) := by
    have h1 : (∑ n ∈ Icc 1 N, normalizedRamanujanMode m n ^ 2) ≤
        ∑ n ∈ Ioc 0 ((N / m + 1) * m), normalizedRamanujanMode m n ^ 2 := by
      simpa only [zero_add] using
        sum_le_sum_of_subset_of_nonneg hp_sub fun _ _ _ => sq_nonneg _
    rw [hsum_periods (N / m + 1)] at h1
    have hqm : ((N / m : ℕ) : ℝ) * m ≤ N := by exact_mod_cast Nat.div_mul_le_self N m
    have hmNR : (m : ℝ) ≤ N := by exact_mod_cast hmN
    push_cast at h1
    linarith only [h1, hqm, hmNR]
  calc
    (1 / ((N : ℝ) * Real.log N)) * (∑ n ∈ Icc 1 N, normalizedRamanujanMode m n ^ 2) ≤
        (1 / ((N : ℝ) * Real.log N)) * (2 * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = 2 / Real.log N := by field_simp [hN0.ne', hL0.ne']

/-- Quadratic bound on `fullWeilPoleErrorMatrix` evaluated on a single Ramanujan mode `v_m`
(`2 ≤ m`, `m * m ≤ N`). -/
private theorem abs_fullWeilPoleErrorMatrix_mode_inner_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) {m N : ℕ}
    (hm : 2 ≤ m) (hmN : m * m ≤ N) (hcN : c ≤ N) :
    |⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
        (normalizedRamanujanHorizonVector m N),
      normalizedRamanujanHorizonVector m N⟫| ≤
      2 * atomPoleMomentErrorConstant φ * c ^ 2 / ((N : ℝ) * Real.log N) := by
  have hN4 : 4 ≤ N := (Nat.mul_le_mul hm hm).trans hmN
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL0 : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  change |⟪Matrix.toEuclideanLin
    (horizonKernelMatrix (fun n j => atomPoleErrorCoefficient φ c N * arithmeticPoleKernel n j) N)
    (normalizedRamanujanHorizonVector m N), normalizedRamanujanHorizonVector m N⟫| ≤ _
  rw [horizonKernelMatrix_inner]
  have hpull :
      (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
          primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
            primeHorizonExtension (normalizedRamanujanHorizonVector m N) j *
            (atomPoleErrorCoefficient φ c N * arithmeticPoleKernel n j)) =
        atomPoleErrorCoefficient φ c N *
          ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
            primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
              primeHorizonExtension (normalizedRamanujanHorizonVector m N) j *
              arithmeticPoleKernel n j := by
    simp_rw [mul_sum]
    exact sum_congr rfl fun n _ => sum_congr rfl fun j _ => by ring
  rw [hpull, abs_mul]
  have hcoef := abs_atomPoleErrorCoefficient_le_of_le hφ hsupp hM_int hc0 hN1 hcN
  have hpole := abs_arithmeticPoleKernel_mode_le hm hN2
  have hm2N : (m : ℝ) ^ 2 ≤ N := by
    have : (m * m : ℕ) ≤ N := hmN
    simpa only [sq, Nat.cast_mul] using (Nat.cast_le (α := ℝ)).mpr this
  have hC0 : 0 ≤ atomPoleMomentErrorConstant φ := by
    have := abs_nonneg (atomPoleErrorCoefficient φ c N)
    have hpos : 0 < (c / N) ^ 2 := sq_pos_of_pos (div_pos hc0 hN0)
    nlinarith only [this, hcoef, hpos]
  calc
    |atomPoleErrorCoefficient φ c N| *
        |∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
          primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
            primeHorizonExtension (normalizedRamanujanHorizonVector m N) j *
            arithmeticPoleKernel n j| ≤
        (atomPoleMomentErrorConstant φ * (c / N) ^ 2) * (2 * (m : ℝ) ^ 2 / Real.log N) :=
      mul_le_mul hcoef hpole (abs_nonneg _) (by positivity)
    _ = 2 * atomPoleMomentErrorConstant φ * c ^ 2 * ((m : ℝ) ^ 2 / N) /
          ((N : ℝ) * Real.log N) := by
      field_simp [hN0.ne', hL0.ne']; ring
    _ ≤ 2 * atomPoleMomentErrorConstant φ * c ^ 2 * 1 / ((N : ℝ) * Real.log N) := by
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left ((div_le_one hN0).mpr hm2N) (by positivity)
    _ = 2 * atomPoleMomentErrorConstant φ * c ^ 2 / ((N : ℝ) * Real.log N) := by ring

/-- Reflected Abel summation starting at integer gap `d ≥ 1`:
`|∑_{j=1}^{n-d} a(j) / (n - j)| ≤ B / d`. -/
private theorem abs_sum_Icc_div_sub_gap_le {a : ℕ → ℝ} {B : ℝ} {n d : ℕ}
    (hd : 1 ≤ d) (hB : ∀ l k : ℕ, l ≤ k → |∑ j ∈ Ico l k, a j| ≤ B) :
    |∑ j ∈ Icc 1 (n - d), a j / ((n : ℝ) - j)| ≤ B / d := by
  by_cases hnd : n ≤ d
  · have hemp : Icc 1 (n - d) = ∅ := by
      rw [Nat.sub_eq_zero_of_le hnd]; exact Icc_eq_empty (by omega)
    have hB0 : 0 ≤ B := by simpa only [Ico_self, sum_empty, abs_zero] using hB 0 0 le_rfl
    rw [hemp, sum_empty, abs_zero]
    positivity
  have hgt : d < n := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hpartial : ∀ k ≤ n - d, |∑ i ∈ range k, a (n - d - i)| ≤ B := by
    intro k hk
    rw [← Nat.Ico_zero_eq_range,
      sum_Ico_reflect a 0 (show k ≤ n - d + 1 by omega),
      Nat.sub_add_cancel (by omega : 1 ≤ n - d + 1), Nat.sub_zero]
    exact hB (n - d + 1 - k) (n - d + 1) (Nat.sub_le _ _)
  have hab := abs_sum_mul_le_of_finite_partial
    (g := fun i => a (n - d - i)) (w := fun i => 1 / ((d : ℝ) + i))
    (n - d) hpartial (fun i => by positivity)
    (fun i => by apply one_div_le_one_div_of_le (by positivity); push_cast; linarith)
  have heq : (∑ i ∈ range (n - d), 1 / ((d : ℝ) + i) * a (n - d - i)) =
      ∑ j ∈ Icc 1 (n - d), a j / ((n : ℝ) - j) := by
    refine sum_bij (fun i _ => n - d - i) ?_ ?_ ?_ ?_
    · intro i hi; have := mem_range.mp hi; exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro i₁ h1 i₂ h2 h
      have := mem_range.mp h1; have := mem_range.mp h2
      change n - d - i₁ = n - d - i₂ at h; omega
    · intro j hj; obtain ⟨h1, h2⟩ := mem_Icc.mp hj
      exact ⟨n - d - j, mem_range.mpr (by omega), by omega⟩
    · intro i hi
      have hi' := mem_range.mp hi
      have hsub : (n : ℝ) - (n - d - i : ℕ) = (d : ℝ) + i := by
        rw [Nat.cast_sub (show i ≤ n - d by omega), Nat.cast_sub (by omega : d ≤ n)]
        ring
      rw [hsub]; ring
  rw [heq, Nat.cast_zero, add_zero, div_eq_mul_inv, one_mul, mul_comm] at hab
  rwa [div_eq_mul_inv]

/-- Uniform single-mode quadratic bound on `fullWeilCenterMatrix α N` across all `2 ≤ m`
with `m * m ≤ N` and `1 ≤ log N`:
`|⟪fullWeilCenterMatrix α N v_m, v_m⟫| ≤ 100 * |α| * (1 + log m) / √(log N)`. -/
private theorem abs_fullWeilCenterMatrix_mode_inner_le (α : ℝ) {m N : ℕ}
    (hm : 2 ≤ m) (hmN : m * m ≤ N) (hlogN : 1 ≤ Real.log N) :
    |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix α N)
        (normalizedRamanujanHorizonVector m N),
      normalizedRamanujanHorizonVector m N⟫| ≤
      100 * |α| * (1 + Real.log m) / Real.sqrt (Real.log N) := by
  have hN4 : 4 ≤ N := (Nat.mul_le_mul hm hm).trans hmN
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hm_le_N : m ≤ N := (Nat.le_mul_self m).trans hmN
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hlogN
  have hsL0 : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL0
  have h1m : 1 ≤ 1 + Real.log m := by linarith [Real.log_natCast_nonneg m]
  obtain ⟨_, hv_norm⟩ := normalizedRamanujanHorizonVector_norm_sq_le_nineteen hm hmN hlogN
  let a := normalizedRamanujanMode m
  have ha_abs : ∀ j, |a j| ≤ (m : ℝ) := fun j => by
    dsimp only [a]
    have h1 := abs_sum_Ico_normalizedRamanujanMode_le hm (Nat.le_succ j)
    rwa [Nat.Ico_succ_singleton, sum_singleton] at h1
  have hB : ∀ l k : ℕ, l ≤ k → |∑ j ∈ Ico l k, a j| ≤ (m : ℝ) :=
    fun _ _ hlk => abs_sum_Ico_normalizedRamanujanMode_le hm hlk
  set v := primeHorizonExtension (normalizedRamanujanHorizonVector m N)
  have hv_eq : ∀ j ∈ Icc 1 N, v j = (Real.sqrt (Real.log N))⁻¹ * (a j / Real.sqrt j) :=
    fun j hj => primeHorizonExtension_coe _ ⟨j, hj⟩
  -- Split `⟪fullWeilCenterMatrix α N v_m, v_m⟫` into `arithmeticPoleKernel` minus `archimedeanCenterKernel`.
  change |⟪Matrix.toEuclideanLin
    (horizonKernelMatrix (fun n j =>
      (α / N) * (arithmeticPoleKernel n j - archimedeanCenterKernel n j)) N)
    (normalizedRamanujanHorizonVector m N), normalizedRamanujanHorizonVector m N⟫| ≤ _
  rw [horizonKernelMatrix_inner]
  have hsplit_inner :
      (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
          v n * v j * ((α / N) * (arithmeticPoleKernel n j - archimedeanCenterKernel n j))) =
        (α / N) * (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, v n * v j * arithmeticPoleKernel n j) -
          ∑ n ∈ Icc 1 N, v n *
            ∑ j ∈ Icc 1 N, ((α / N) * archimedeanCenterKernel n j) * v j := by
    have ht : ∀ n j,
        v n * v j * ((α / N) * (arithmeticPoleKernel n j - archimedeanCenterKernel n j)) =
          (α / N) * (v n * v j * arithmeticPoleKernel n j) -
            v n * (((α / N) * archimedeanCenterKernel n j) * v j) := fun _ _ => by ring
    simp only [ht, sum_sub_distrib, ← mul_sum]
  rw [hsplit_inner]
  -- Part 1: `arithmeticPoleKernel` piece is `≤ 2 * |α| / log N ≤ 2 * |α| * (1 + log m) / √(log N)`.
  have hm2N : (m : ℝ) ^ 2 ≤ N := by
    simpa only [sq, Nat.cast_mul] using (Nat.cast_le (α := ℝ)).mpr hmN
  have hpole_part :
      |(α / N) * ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, v n * v j * arithmeticPoleKernel n j| ≤
        2 * |α| * (1 + Real.log m) / Real.sqrt (Real.log N) := by
    rw [abs_mul, abs_div, abs_of_pos hN0]
    have hp := abs_arithmeticPoleKernel_mode_le hm hN2
    have hsqrt_le : Real.sqrt (Real.log N) ≤ Real.log N := by
      nlinarith only [Real.sq_sqrt hL0.le, hsL0, hlogN]
    calc
      (|α| / N) * |∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, v n * v j * arithmeticPoleKernel n j| ≤
          (|α| / N) * (2 * (m : ℝ) ^ 2 / Real.log N) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = 2 * |α| * ((m : ℝ) ^ 2 / N) / Real.log N := by ring
      _ ≤ 2 * |α| * 1 / Real.log N :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left ((div_le_one hN0).mpr hm2N) (by positivity)) hL0.le
      _ ≤ 2 * |α| * (1 + Real.log m) / Real.sqrt (Real.log N) := by
        rw [div_le_div_iff₀ hL0 hsL0]
        nlinarith only [abs_nonneg α, h1m, hsqrt_le, hsL0]
  -- Part 2: `archimedeanCenterKernel` row split into `K_near` (`2 * m < n` and `|n - j| < m`) + far.
  let K_near : ℕ → ℕ → ℝ := fun n j =>
    if 2 * m < n ∧ j ≠ n ∧ (n < j + m ∧ j < n + m) then
      (α / N) * archimedeanCenterKernel n j else 0
  let row_col : ℕ → ℝ := fun n => ∑ j ∈ Icc 1 N, ((α / N) * archimedeanCenterKernel n j) * v j
  let row_near : ℕ → ℝ := fun n => ∑ j ∈ Icc 1 N, K_near n j * v j
  let row_far : ℕ → ℝ := fun n => row_col n - row_near n
  -- Far collar `L²` square bound: `∑_{n=1}^N row_far n ^ 2 ≤ 40 * α^2 / log N`.
  have hfar_sq : (∑ n ∈ Icc 1 N, row_far n ^ 2) ≤ 40 * α ^ 2 / Real.log N := by
    have hpt_far : ∀ n ∈ Icc 1 N,
        row_far n ^ 2 ≤
          if n ≤ 2 * m then 9 * α ^ 2 * (m : ℝ) ^ 2 * (n : ℝ) / ((N : ℝ) ^ 2 * Real.log N)
          else 4 * α ^ 2 * (n : ℝ) / ((N : ℝ) ^ 2 * Real.log N) := by
      intro n hn
      obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hsn_ne : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
      by_cases hn2m : n ≤ 2 * m
      · rw [if_pos hn2m]
        have hzero : row_near n = 0 := sum_eq_zero fun j _ => by
          dsimp only [K_near]; rw [if_neg (by omega), zero_mul]
        have hcol_eq : row_col n = (Real.sqrt (Real.log N))⁻¹ *
            ((α / N) * ∑ j ∈ Icc 1 N, archimedeanCenterKernel n j * (a j / Real.sqrt j)) := by
          dsimp only [row_col]
          rw [mul_sum, mul_sum]
          exact sum_congr rfl fun j hj => by rw [hv_eq j hj]; ring
        have hb := abs_sum_archimedeanCenterKernel_poleProfile_le hn hm0.le (ha_abs n) hB
        have h3m : (2 * (m : ℝ) + m) * Real.sqrt n = 3 * m * Real.sqrt n := by ring
        rw [h3m] at hb
        have hbsq := mul_self_le_mul_self (abs_nonneg _) hb
        rw [← sq, sq_abs, ← sq, mul_pow, mul_pow, Real.sq_sqrt hn0.le] at hbsq
        have hrf : row_far n = row_col n := by dsimp only [row_far]; rw [hzero, sub_zero]
        rw [hrf, hcol_eq, mul_pow, inv_pow, Real.sq_sqrt hL0.le, mul_pow]
        calc
          (Real.log N)⁻¹ * ((α / N) ^ 2 *
              (∑ j ∈ Icc 1 N, archimedeanCenterKernel n j * (a j / Real.sqrt j)) ^ 2) ≤
              (Real.log N)⁻¹ * ((α / N) ^ 2 * (3 ^ 2 * (m : ℝ) ^ 2 * n)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbsq (sq_nonneg _))
              (inv_nonneg.mpr hL0.le)
          _ = 9 * α ^ 2 * (m : ℝ) ^ 2 * (n : ℝ) / ((N : ℝ) ^ 2 * Real.log N) := by
            field_simp [hN0.ne', hL0.ne']; ring
      · rw [if_neg hn2m]
        have hn_gt : 2 * m < n := by omega
        -- Far indices `j ∈ Icc 1 N`: `j ≤ n - m` or `j ≥ n + m`.
        let F_far := (Icc 1 N).filter (fun j => ¬(j ≠ n ∧ (n < j + m ∧ j < n + m)))
        have hfar_eq : row_far n = (Real.sqrt (Real.log N))⁻¹ * (α / N) *
            ∑ j ∈ F_far.erase n, archimedeanCenterKernel n j * (a j / Real.sqrt j) := by
          have h1 : row_far n = ∑ j ∈ Icc 1 N,
              (if ¬(j ≠ n ∧ (n < j + m ∧ j < n + m)) then
                (α / N) * archimedeanCenterKernel n j else 0) * v j := by
            dsimp only [row_far, row_col, row_near, K_near]
            rw [← sum_sub_distrib]
            refine sum_congr rfl fun j _ => ?_
            by_cases hcond : j ≠ n ∧ (n < j + m ∧ j < n + m)
            · rw [if_pos ⟨hn_gt, hcond⟩, if_neg (not_not.mpr hcond)]; ring
            · rw [if_neg (fun h => hcond h.2), if_pos hcond]; ring
          have hn_F : n ∈ F_far := mem_filter.mpr ⟨hn, fun h => h.1 rfl⟩
          rw [h1, ← sum_erase_add F_far
            (fun j => archimedeanCenterKernel n j * (a j / Real.sqrt j)) hn_F,
            archimedeanCenterKernel_self, zero_mul, add_zero, sum_filter, mul_sum]
          refine sum_congr rfl fun j hj => ?_
          split_ifs <;> [rw [hv_eq j hj]; skip] <;> ring
        -- Expand `archimedeanCenterKernel` into difference + sum reciprocal pieces on `F_far.erase n`.
        have hdecomp_far :
            (∑ j ∈ F_far.erase n, archimedeanCenterKernel n j * (a j / Real.sqrt j)) =
              Real.sqrt n / 2 * ((∑ j ∈ Icc 1 (n - m), a j / ((n : ℝ) - j)) +
                (∑ j ∈ Icc (n + m) N, a j / ((j : ℝ) - n)) +
                (∑ j ∈ F_far.erase n, a j / ((n : ℝ) + j))) := by
          have hF_er : F_far.erase n = Icc 1 (n - m) ∪ Icc (n + m) N := by
            ext j; simp only [F_far, mem_erase, mem_filter, mem_Icc, mem_union]; omega
          have hdisj_lu : Disjoint (Icc 1 (n - m)) (Icc (n + m) N) := by
            rw [Finset.disjoint_left]; intro j h1 h2; simp only [mem_Icc] at h1 h2; omega
          have hkern : ∀ j ∈ F_far.erase n,
              archimedeanCenterKernel n j * (a j / Real.sqrt j) =
                Real.sqrt n / 2 * (a j / |(n : ℝ) - j| + a j / ((n : ℝ) + j)) := by
            intro j hj
            obtain ⟨hjn, hjF⟩ := mem_erase.mp hj
            have hjI := (mem_filter.mp hjF).1
            have hk := archimedeanCenterKernel_div_sqrt_mul hn1 (mem_Icc.mp hjI).1 (Ne.symm hjn)
            calc
              archimedeanCenterKernel n j * (a j / Real.sqrt j) =
                  Real.sqrt n * a j * (archimedeanCenterKernel n j / (Real.sqrt n * Real.sqrt j)) := by
                field_simp [hsn_ne]
              _ = _ := by rw [hk]; ring
          rw [sum_congr rfl hkern, ← mul_sum, sum_add_distrib]
          congr 2
          rw [hF_er, sum_union hdisj_lu]
          congr 1
          · refine sum_congr rfl fun j hj => ?_
            have hjle : (j : ℝ) ≤ n := by exact_mod_cast (show j ≤ n by have := (mem_Icc.mp hj).2; omega)
            rw [abs_of_nonneg (sub_nonneg.mpr hjle)]
          · refine sum_congr rfl fun j hj => ?_
            have hjge : (n : ℝ) ≤ j := by exact_mod_cast (show n ≤ j by have := (mem_Icc.mp hj).1; omega)
            rw [abs_of_nonpos (sub_nonpos.mpr hjge), neg_sub]
        -- Bound the three reciprocal sums by `1`, `1`, and `2` respectively!
        have hb_lo : |∑ j ∈ Icc 1 (n - m), a j / ((n : ℝ) - j)| ≤ 1 := by
          have h := abs_sum_Icc_div_sub_gap_le (by omega : 1 ≤ m) hB
          rwa [div_self hm0.ne'] at h
        have hb_hi : |∑ j ∈ Icc (n + m) N, a j / ((j : ℝ) - n)| ≤ 1 := by
          by_cases hnmN : N < n + m
          · rw [Icc_eq_empty (by omega), sum_empty, abs_zero]; norm_num
          · have h := abs_sum_Ico_div_add_le (r := -(n : ℝ)) hB (n + m) (N + 1)
              (by push_cast; linarith only [hm0])
            have heq : (∑ j ∈ Ico (n + m) (N + 1), a j / (-(n : ℝ) + j)) =
                ∑ j ∈ Icc (n + m) N, a j / ((j : ℝ) - n) := by
              rw [Ico_add_one_right_eq_Icc]
              exact sum_congr rfl fun j _ => by ring
            have hden : -(n : ℝ) + ((n + m : ℕ) : ℝ) = m := by push_cast; ring
            rw [heq, hden, div_self hm0.ne'] at h
            exact h
        have hb_add : |∑ j ∈ F_far.erase n, a j / ((n : ℝ) + j)| ≤ 2 := by
          have hF_er : F_far.erase n = Icc 1 (n - m) ∪ Icc (n + m) N := by
            ext j; simp only [F_far, mem_erase, mem_filter, mem_Icc, mem_union]; omega
          have hdisj_lu : Disjoint (Icc 1 (n - m)) (Icc (n + m) N) := by
            rw [Finset.disjoint_left]; intro j h1 h2; simp only [mem_Icc] at h1 h2; omega
          rw [hF_er, sum_union hdisj_lu]
          have h1 : |∑ j ∈ Icc 1 (n - m), a j / ((n : ℝ) + j)| ≤ 1 := by
            have h := abs_sum_Ico_div_add_le (r := (n : ℝ)) hB 1 (n - m + 1) (by positivity)
            rw [Ico_add_one_right_eq_Icc] at h
            refine h.trans ?_
            rw [div_le_one (by positivity)]
            push_cast
            have : (m : ℝ) ≤ n := by exact_mod_cast (show m ≤ n by omega)
            linarith only [this]
          have h2 : |∑ j ∈ Icc (n + m) N, a j / ((n : ℝ) + j)| ≤ 1 := by
            by_cases hnmN : N < n + m
            · rw [Icc_eq_empty (by omega), sum_empty, abs_zero]; norm_num
            · have h := abs_sum_Ico_div_add_le (r := (n : ℝ)) hB (n + m) (N + 1) (by positivity)
              rw [Ico_add_one_right_eq_Icc] at h
              refine h.trans ?_
              rw [div_le_one (by positivity)]
              push_cast
              linarith only [hn0]
          exact (abs_add_le _ _).trans (by linarith only [h1, h2])
        have hfar_abs : |∑ j ∈ F_far.erase n, archimedeanCenterKernel n j * (a j / Real.sqrt j)| ≤
            2 * Real.sqrt n := by
          rw [hdecomp_far, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (n : ℝ) / 2)]
          have h3 := (abs_add_three _ _ _).trans (add_le_add (add_le_add hb_lo hb_hi) hb_add)
          calc
            Real.sqrt n / 2 * |_ + _ + _| ≤ Real.sqrt n / 2 * (1 + 1 + 2) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
            _ = 2 * Real.sqrt n := by ring
        have hsq := mul_self_le_mul_self (abs_nonneg _) hfar_abs
        rw [← sq, sq_abs, ← sq, mul_pow, Real.sq_sqrt hn0.le] at hsq
        rw [hfar_eq, mul_assoc, mul_pow, inv_pow, Real.sq_sqrt hL0.le, mul_pow]
        calc
          (Real.log N)⁻¹ * ((α / N) ^ 2 *
              (∑ j ∈ F_far.erase n, archimedeanCenterKernel n j * (a j / Real.sqrt j)) ^ 2) ≤
              (Real.log N)⁻¹ * ((α / N) ^ 2 * (2 ^ 2 * n)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (sq_nonneg _))
              (inv_nonneg.mpr hL0.le)
          _ = 4 * α ^ 2 * (n : ℝ) / ((N : ℝ) ^ 2 * Real.log N) := by
            field_simp [hN0.ne', hL0.ne']; ring
    -- Sum `hpt_far` over `n ≤ 2 * m` and `n > 2 * m`.
    have hpt_unif : ∀ n ∈ Icc 1 N,
        (if n ≤ 2 * m then 9 * α ^ 2 * (m : ℝ) ^ 2 * (n : ℝ) / ((N : ℝ) ^ 2 * Real.log N)
          else 4 * α ^ 2 * (n : ℝ) / ((N : ℝ) ^ 2 * Real.log N)) ≤
        (if n ≤ 2 * m then 18 * α ^ 2 * (m : ℝ) ^ 3 / ((N : ℝ) ^ 2 * Real.log N) else 0) +
          4 * α ^ 2 / ((N : ℝ) * Real.log N) := by
      intro n hn
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
      split_ifs with hle
      · have hn2mR : (n : ℝ) ≤ 2 * m := by exact_mod_cast hle
        have h1 : 9 * α ^ 2 * (m : ℝ) ^ 2 * (n : ℝ) ≤ 18 * α ^ 2 * (m : ℝ) ^ 3 := by
          have : 0 ≤ 9 * α ^ 2 * (m : ℝ) ^ 2 := by positivity
          nlinarith only [this, hn2mR]
        have h2 : 0 ≤ 4 * α ^ 2 / ((N : ℝ) * Real.log N) := by positivity
        exact (div_le_div_of_nonneg_right h1 (by positivity)).trans (by linarith only [h2])
      · rw [zero_add]
        calc
          4 * α ^ 2 * (n : ℝ) / ((N : ℝ) ^ 2 * Real.log N) ≤
              4 * α ^ 2 * (N : ℝ) / ((N : ℝ) ^ 2 * Real.log N) :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hnN (by positivity)) (by positivity)
          _ = 4 * α ^ 2 / ((N : ℝ) * Real.log N) := by field_simp [hN0.ne', hL0.ne']
    have hsum_low :
        (∑ n ∈ Icc 1 N,
          if n ≤ 2 * m then 18 * α ^ 2 * (m : ℝ) ^ 3 / ((N : ℝ) ^ 2 * Real.log N) else 0) ≤
        36 * α ^ 2 / Real.log N := by
      rw [← sum_filter]
      have hsub : (Icc 1 N).filter (fun n => n ≤ 2 * m) ⊆ Icc 1 (2 * m) :=
        fun n hn => mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hn).1).1, (mem_filter.mp hn).2⟩
      have hcard : (((Icc 1 N).filter (fun n => n ≤ 2 * m)).card : ℝ) ≤ 2 * m := by
        have hc := (card_le_card hsub).trans_eq (by rw [Nat.card_Icc, Nat.add_sub_cancel])
        exact_mod_cast hc
      rw [sum_const, nsmul_eq_mul]
      calc
        (((Icc 1 N).filter (fun n => n ≤ 2 * m)).card : ℝ) *
            (18 * α ^ 2 * (m : ℝ) ^ 3 / ((N : ℝ) ^ 2 * Real.log N)) ≤
          (2 * (m : ℝ)) * (18 * α ^ 2 * (m : ℝ) ^ 3 / ((N : ℝ) ^ 2 * Real.log N)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 36 * α ^ 2 * ((m : ℝ) ^ 2 / N) ^ 2 / Real.log N := by
          field_simp [hN0.ne', hL0.ne']; ring
        _ ≤ 36 * α ^ 2 * 1 ^ 2 / Real.log N := by
          refine div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left ?_ (by positivity)) hL0.le
          exact pow_le_pow_left₀ (by positivity) ((div_le_one hN0).mpr hm2N) 2
        _ = 36 * α ^ 2 / Real.log N := by ring
    calc
      (∑ n ∈ Icc 1 N, row_far n ^ 2) ≤
          ∑ n ∈ Icc 1 N,
            ((if n ≤ 2 * m then 18 * α ^ 2 * (m : ℝ) ^ 3 / ((N : ℝ) ^ 2 * Real.log N) else 0) +
              4 * α ^ 2 / ((N : ℝ) * Real.log N)) :=
        sum_le_sum fun n hn => (hpt_far n hn).trans (hpt_unif n hn)
      _ = (∑ n ∈ Icc 1 N,
            if n ≤ 2 * m then 18 * α ^ 2 * (m : ℝ) ^ 3 / ((N : ℝ) ^ 2 * Real.log N) else 0) +
          (N : ℝ) * (4 * α ^ 2 / ((N : ℝ) * Real.log N)) := by
        rw [sum_add_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      _ ≤ 36 * α ^ 2 / Real.log N + 4 * α ^ 2 / Real.log N :=
        add_le_add hsum_low (by field_simp [hN0.ne', hL0.ne'])
      _ = 40 * α ^ 2 / Real.log N := by ring
  -- Near collar `L²` square bound: `∑_{n=1}^N row_near n ^ 2 ≤ 128 * α^2 * (1 + log m)^2 / log N`.
  have hnear_sq : (∑ n ∈ Icc 1 N, row_near n ^ 2) ≤
      128 * α ^ 2 * (1 + Real.log m) ^ 2 / Real.log N := by
    let w_v : ℕ → ℝ := fun j => ((j : ℝ) / N) * |v j|
    let W_ker : ℕ → ℕ → ℝ := fun n j =>
      if j ≠ n ∧ (n < j + m ∧ j < n + m) then 2 * |α| / |(n : ℝ) - j| else 0
    have hrow_near_le : ∀ n ∈ Icc 1 N,
        |row_near n| ≤ ∑ j ∈ Icc 1 N, W_ker n j * w_v j := by
      intro n hn
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
      rw [abs_mul]
      dsimp only [K_near, W_ker, w_v]
      by_cases hcond : 2 * m < n ∧ j ≠ n ∧ (n < j + m ∧ j < n + m)
      · rw [if_pos hcond, if_pos hcond.2]
        obtain ⟨hn_gt, hjn, hnj1, hnj2⟩ := hcond
        have hn1 := (mem_Icc.mp hn).1
        have hj1 := (mem_Icc.mp hj).1
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
        have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
        have hjn_ne : |(n : ℝ) - j| ≠ 0 :=
          abs_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast hjn.symm))
        -- For `n > 2 * m` and `|n - j| < m`, `j > m` and `n ≤ 2 * j`, so `archimedeanCenterKernel n j ≤ 2 * j / |n - j|`.
        have hn_le_2j : (n : ℝ) ≤ 2 * j := by exact_mod_cast (show n ≤ 2 * j by omega)
        have hkern_le : archimedeanCenterKernel n j ≤ 2 * (j : ℝ) / |(n : ℝ) - j| := by
          have hk := archimedeanCenterKernel_div_sqrt_mul hn1 hj1 (Ne.symm hjn)
          have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
          have hsj : 0 < Real.sqrt j := Real.sqrt_pos.mpr hj0
          have heq : archimedeanCenterKernel n j =
              Real.sqrt n * Real.sqrt j / 2 * (1 / |(n : ℝ) - j| + 1 / ((n : ℝ) + j)) := by
            have := (div_eq_iff (mul_pos hsn hsj).ne').mp hk
            linarith only [this]
          have hadd_le : 1 / ((n : ℝ) + j) ≤ 1 / |(n : ℝ) - j| := by
            refine one_div_le_one_div_of_le (pos_of_ne_zero hjn_ne) ?_
            rw [abs_le]
            exact ⟨by linarith only [hn0, hj0], by linarith only [hn0, hj0]⟩
          have hsqrt_prod : Real.sqrt n * Real.sqrt j ≤ 2 * j := by
            have hsq : (Real.sqrt n * Real.sqrt j) ^ 2 ≤ (2 * (j : ℝ)) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt hn0.le, Real.sq_sqrt hj0.le]
              nlinarith only [hn_le_2j, hj0]
            nlinarith only [hsq, mul_nonneg hsn.le hsj.le, hj0]
          rw [heq]
          calc
            Real.sqrt n * Real.sqrt j / 2 * (1 / |(n : ℝ) - j| + 1 / ((n : ℝ) + j)) ≤
                Real.sqrt n * Real.sqrt j / 2 * (2 / |(n : ℝ) - j|) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              linarith only [hadd_le, (by ring : 1 / |(n : ℝ) - j| + 1 / |(n : ℝ) - j| = 2 / |(n : ℝ) - j|)]
            _ = Real.sqrt n * Real.sqrt j / |(n : ℝ) - j| := by ring
            _ ≤ 2 * (j : ℝ) / |(n : ℝ) - j| :=
              div_le_div_of_nonneg_right hsqrt_prod (abs_nonneg _)
        rw [abs_mul, abs_div, abs_of_pos hN0,
          abs_of_nonneg (archimedeanCenterKernel_nonneg n j)]
        calc
          (|α| / N) * archimedeanCenterKernel n j * |v j| ≤
              (|α| / N) * (2 * (j : ℝ) / |(n : ℝ) - j|) * |v j| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hkern_le (by positivity)) (abs_nonneg _)
          _ = 2 * |α| / |(n : ℝ) - j| * ((j : ℝ) / N * |v j|) := by ring
      · rw [if_neg hcond, abs_zero, zero_mul]
        split_ifs <;> positivity
    -- Row/col bound on symmetric `W_ker`: `∑_{j=1}^N W_ker n j ≤ 8 * |α| * (1 + log m)`.
    have hW_symm : ∀ n j, W_ker n j = W_ker j n := fun n j => by
      dsimp only [W_ker]
      by_cases h : j ≠ n ∧ (n < j + m ∧ j < n + m)
      · rw [if_pos h, if_pos ⟨h.1.symm, h.2.2, h.2.1⟩, abs_sub_comm]
      · have h' : ¬(n ≠ j ∧ (j < n + m ∧ n < j + m)) :=
          fun hc => h ⟨hc.1.symm, hc.2.2, hc.2.1⟩
        rw [if_neg h, if_neg h']
    have hW_row : ∀ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, W_ker n j) ≤ 8 * |α| * (1 + Real.log m) := by
      intro n _
      -- Split `j < n` (`d = n - j ∈ Icc 1 m`) and `j > n` (`d = j - n ∈ Icc 1 m`).
      let S_lo := (Icc 1 N).filter (fun j => j < n ∧ n < j + m)
      let S_hi := (Icc 1 N).filter (fun j => n < j ∧ j < n + m)
      have hsplit_W : (∑ j ∈ Icc 1 N, W_ker n j) =
          2 * |α| * ((∑ j ∈ S_lo, 1 / |(n : ℝ) - j|) + ∑ j ∈ S_hi, 1 / |(n : ℝ) - j|) := by
        have hdisj : Disjoint S_lo S_hi := by
          rw [Finset.disjoint_left]; intro j h1 h2
          simp only [S_lo, S_hi, mem_filter] at h1 h2; omega
        have heq_f : (Icc 1 N).filter (fun j => j ≠ n ∧ (n < j + m ∧ j < n + m)) =
            S_lo ∪ S_hi := by
          ext j; simp only [S_lo, S_hi, mem_filter, mem_union]; omega
        dsimp only [W_ker]
        simp_rw [show ∀ j, (if j ≠ n ∧ (n < j + m ∧ j < n + m) then 2 * |α| / |(n : ℝ) - j| else 0) =
          2 * |α| * (if j ≠ n ∧ (n < j + m ∧ j < n + m) then 1 / |(n : ℝ) - j| else 0) from
          fun j => by split_ifs <;> ring]
        rw [← mul_sum, ← sum_filter, heq_f, sum_union hdisj]
      have hhar_m : (∑ d ∈ Icc 1 m, (1 : ℝ) / d) ≤ 2 * (1 + Real.log m) := by
        have hh := harmonic_le_one_add_log m
        rw [harmonic_eq_sum_Icc, Rat.cast_sum] at hh
        have h1 : (∑ d ∈ Icc 1 m, (1 : ℝ) / d) ≤ 1 + Real.log m := by
          refine le_trans (le_of_eq ?_) hh
          exact sum_congr rfl fun d _ => by push_cast; ring
        linarith only [h1, h1m]
      have hlo_le : (∑ j ∈ S_lo, 1 / |(n : ℝ) - j|) ≤ 2 * (1 + Real.log m) := by
        have hinj : ∀ j₁ ∈ S_lo, ∀ j₂ ∈ S_lo, n - j₁ = n - j₂ → j₁ = j₂ := by
          intro j₁ h1 j₂ h2 heq
          have := (mem_filter.mp h1).2.1; have := (mem_filter.mp h2).2.1; omega
        have himg_sub : S_lo.image (fun j => n - j) ⊆ Icc 1 m := by
          intro d hd
          obtain ⟨j, hj, rfl⟩ := mem_image.mp hd
          have := (mem_filter.mp hj).2; exact mem_Icc.mpr ⟨by omega, by omega⟩
        have heq_img : (∑ j ∈ S_lo, 1 / |(n : ℝ) - j|) =
            ∑ d ∈ S_lo.image (fun j => n - j), (1 : ℝ) / d := by
          rw [sum_image hinj]
          refine sum_congr rfl fun j hj => ?_
          have hlt := (mem_filter.mp hj).2.1
          rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)),
            Nat.cast_sub hlt.le]
        rw [heq_img]
        exact (sum_le_sum_of_subset_of_nonneg himg_sub fun _ _ _ => by positivity).trans hhar_m
      have hhi_le : (∑ j ∈ S_hi, 1 / |(n : ℝ) - j|) ≤ 2 * (1 + Real.log m) := by
        have hinj : ∀ j₁ ∈ S_hi, ∀ j₂ ∈ S_hi, j₁ - n = j₂ - n → j₁ = j₂ := by
          intro j₁ h1 j₂ h2 heq
          have := (mem_filter.mp h1).2.1; have := (mem_filter.mp h2).2.1; omega
        have himg_sub : S_hi.image (fun j => j - n) ⊆ Icc 1 m := by
          intro d hd
          obtain ⟨j, hj, rfl⟩ := mem_image.mp hd
          have := (mem_filter.mp hj).2; exact mem_Icc.mpr ⟨by omega, by omega⟩
        have heq_img : (∑ j ∈ S_hi, 1 / |(n : ℝ) - j|) =
            ∑ d ∈ S_hi.image (fun j => j - n), (1 : ℝ) / d := by
          rw [sum_image hinj]
          refine sum_congr rfl fun j hj => ?_
          have hlt := (mem_filter.mp hj).2.1
          rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hlt.le)), neg_sub,
            Nat.cast_sub hlt.le]
        rw [heq_img]
        exact (sum_le_sum_of_subset_of_nonneg himg_sub fun _ _ _ => by positivity).trans hhar_m
      rw [hsplit_W]
      calc
        2 * |α| * ((∑ j ∈ S_lo, 1 / |(n : ℝ) - j|) + ∑ j ∈ S_hi, 1 / |(n : ℝ) - j|) ≤
            2 * |α| * (2 * (1 + Real.log m) + 2 * (1 + Real.log m)) :=
          mul_le_mul_of_nonneg_left (add_le_add hlo_le hhi_le) (by positivity)
        _ = 8 * |α| * (1 + Real.log m) := by ring
    let B_W := 8 * |α| * (1 + Real.log m)
    have hBW0 : 0 ≤ B_W := by dsimp only [B_W]; positivity
    have hschur := sum_sq_abs_majorized_kernel_le' (N := N) W_ker W_ker w_v
      (fun _ => 1) (fun _ => B_W) (fun _ => B_W ^ 2)
      (fun n _ j _ => by dsimp only [W_ker]; split_ifs <;> positivity)
      (fun n _ j _ => le_abs_self _)
      (fun _ _ => zero_lt_one)
      (fun n hn => by simpa only [mul_one] using hW_row n hn)
      (fun j hj => by
        have h1 : (∑ n ∈ Icc 1 N, W_ker n j * (B_W / 1)) = B_W * ∑ n ∈ Icc 1 N, W_ker j n := by
          rw [mul_sum]; exact sum_congr rfl fun n _ => by rw [hW_symm n j]; ring
        rw [h1]
        exact (mul_le_mul_of_nonneg_left (hW_row j hj) hBW0).trans_eq (sq B_W).symm)
    have hw_sq : (∑ j ∈ Icc 1 N, w_v j ^ 2) ≤ 2 / Real.log N := by
      have hpt : ∀ j ∈ Icc 1 N, w_v j ^ 2 ≤ ((j : ℝ) / N) * v j ^ 2 := by
        intro j hj
        have hjN : (j : ℝ) / N ≤ 1 := (div_le_one hN0).mpr (by exact_mod_cast (mem_Icc.mp hj).2)
        have hj0 : 0 ≤ (j : ℝ) / N := by positivity
        dsimp only [w_v]
        rw [mul_pow, sq_abs]
        exact mul_le_mul_of_nonneg_right (by nlinarith only [hjN, hj0]) (sq_nonneg _)
      exact (sum_le_sum hpt).trans (sum_linear_moment_mode_sq_le (by omega) hm_le_N hL0)
    have hpt_rn : ∀ n ∈ Icc 1 N, row_near n ^ 2 ≤ (∑ j ∈ Icc 1 N, W_ker n j * w_v j) ^ 2 := by
      intro n hn
      have h := mul_self_le_mul_self (abs_nonneg _) (hrow_near_le n hn)
      rwa [← sq, sq_abs, ← sq] at h
    calc
      (∑ n ∈ Icc 1 N, row_near n ^ 2) ≤
          ∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, W_ker n j * w_v j) ^ 2 := sum_le_sum hpt_rn
      _ ≤ ∑ j ∈ Icc 1 N, B_W ^ 2 * w_v j ^ 2 := hschur
      _ = B_W ^ 2 * ∑ j ∈ Icc 1 N, w_v j ^ 2 := (mul_sum ..).symm
      _ ≤ B_W ^ 2 * (2 / Real.log N) := mul_le_mul_of_nonneg_left hw_sq (sq_nonneg _)
      _ = 128 * α ^ 2 * (1 + Real.log m) ^ 2 / Real.log N := by
        dsimp only [B_W]; rw [mul_pow, mul_pow, sq_abs]; ring
  -- Combine `row_col = row_far + row_near` via `(a + b)^2 ≤ 2 a^2 + 2 b^2` and Cauchy-Schwarz.
  have hcol_sq : (∑ n ∈ Icc 1 N, row_col n ^ 2) ≤
      (19 * |α| * (1 + Real.log m) / Real.sqrt (Real.log N)) ^ 2 := by
    have h2 : ∀ n ∈ Icc 1 N, row_col n ^ 2 ≤ 2 * row_far n ^ 2 + 2 * row_near n ^ 2 := fun n _ => by
      have hid : row_col n = row_far n + row_near n := by dsimp only [row_far]; ring
      rw [hid]; nlinarith only [sq_nonneg (row_far n - row_near n)]
    have h1m_sq : 1 ≤ (1 + Real.log m) ^ 2 := by nlinarith only [h1m]
    calc
      (∑ n ∈ Icc 1 N, row_col n ^ 2) ≤
          2 * (∑ n ∈ Icc 1 N, row_far n ^ 2) + 2 * (∑ n ∈ Icc 1 N, row_near n ^ 2) := by
        refine (sum_le_sum h2).trans_eq ?_; simp only [sum_add_distrib, ← mul_sum]
      _ ≤ 2 * (40 * α ^ 2 / Real.log N) +
            2 * (128 * α ^ 2 * (1 + Real.log m) ^ 2 / Real.log N) :=
        add_le_add (mul_le_mul_of_nonneg_left hfar_sq zero_le_two)
          (mul_le_mul_of_nonneg_left hnear_sq zero_le_two)
      _ ≤ (361 * α ^ 2 * (1 + Real.log m) ^ 2) / Real.log N := by
        rw [div_add_div_same, div_le_div_iff_of_pos_right hL0]
        nlinarith only [h1m_sq, sq_nonneg α]
      _ = (19 * |α| * (1 + Real.log m) / Real.sqrt (Real.log N)) ^ 2 := by
        rw [div_pow, mul_pow, mul_pow, sq_abs, Real.sq_sqrt hL0.le]; ring
  have hcol_part :
      |∑ n ∈ Icc 1 N, v n * row_col n| ≤
        95 * |α| * (1 + Real.log m) / Real.sqrt (Real.log N) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 N) v row_col
    rw [sum_primeHorizonExtension_sq] at hcs
    have hsq_le : (∑ n ∈ Icc 1 N, v n * row_col n) ^ 2 ≤
        (95 * |α| * (1 + Real.log m) / Real.sqrt (Real.log N)) ^ 2 := by
      have hv25 : ‖normalizedRamanujanHorizonVector m N‖ ^ 2 ≤ 25 := by
        nlinarith only [hv_norm, norm_nonneg (normalizedRamanujanHorizonVector m N)]
      calc
        (∑ n ∈ Icc 1 N, v n * row_col n) ^ 2 ≤
            ‖normalizedRamanujanHorizonVector m N‖ ^ 2 * (∑ n ∈ Icc 1 N, row_col n ^ 2) := hcs
        _ ≤ 25 * (19 * |α| * (1 + Real.log m) / Real.sqrt (Real.log N)) ^ 2 :=
          mul_le_mul hv25 hcol_sq (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
        _ = (95 * |α| * (1 + Real.log m) / Real.sqrt (Real.log N)) ^ 2 := by ring
    exact abs_le_of_sq_le_sq' hsq_le (by positivity) |>.2
  -- Wait: `2 + 95 = 97 ≤ 100`, update statement constant from `80` to `100`!
  linarith only [abs_sub ((α / N) * ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, v n * v j * arithmeticPoleKernel n j)
    (∑ n ∈ Icc 1 N, v n * row_col n), hpole_part, hcol_part,
    (show 0 ≤ |α| * (1 + Real.log m) / Real.sqrt (Real.log N) by positivity)]

/-! ## Section 3: Single-Mode Prime-Matrix Residual Bound Across All Conductors `m * m ≤ N` -/

private theorem sum_union_le_of_nonneg' {α : Type*} [DecidableEq α] {s t : Finset α} {f : α → ℝ}
    (hf : ∀ x ∈ t, 0 ≤ f x) :
    (∑ x ∈ s ∪ t, f x) ≤ (∑ x ∈ s, f x) + ∑ x ∈ t, f x := by
  have heq : s ∪ t = s ∪ (t \ s) := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  have hdisj : Disjoint s (t \ s) := by
    rw [Finset.disjoint_left]; intro x hxs hxt; exact (mem_sdiff.mp hxt).2 hxs
  rw [heq, sum_union hdisj]
  exact add_le_add le_rfl
    (sum_le_sum_of_subset_of_nonneg (fun x hx => (mem_sdiff.mp hx).1) fun x hx _ => hf x hx)

private theorem periodic_add_mul' {α : Type*} {f : ℕ → α} {m : ℕ}
    (hf : Function.Periodic f m) (k x : ℕ) : f (x + k * m) = f x := by
  simpa only [Nat.cast_id] using hf.nat_mul k x

private def singlePrimeCorrection (m y n : ℕ) : ℝ :=
  poleProfileCorrection (normalizedRamanujanMode m) y n +
    (Real.log m + tameDifferent m) * normalizedRamanujanMode m n

private theorem tendsto_tail_singlePrimeCorrection {m : ℕ} (hm : 0 < m)
    {n : ℕ} (hn : 0 < n) (y : ℕ) :
    Tendsto (fun T : ℕ =>
      -(∑ t ∈ Ioc y T, ramanujanUpCorrectionTerm m n t / Real.sqrt (m.totient : ℝ)))
      atTop (𝓝 (singlePrimeCorrection m y n)) := by
  have hg : normalizedRamanujanMode m =
      fun j => ramanujanLagCoefficient m j / Real.sqrt (m.totient : ℝ) :=
    funext (normalizedRamanujanMode_eq_coefficient hm)
  have hid : singlePrimeCorrection m y n =
      ((∑ t ∈ Icc 1 y, ramanujanUpCorrectionTerm m n t) +
        (Real.log m + tameDifferent m) * ramanujanLagCoefficient m n +
          ramanujanDownCorrection m n) / Real.sqrt (m.totient : ℝ) := by
    unfold singlePrimeCorrection
    rw [hg, poleProfileCorrection_div, poleProfileCorrection_eq_divisor_jumps]
    change ((_ + ramanujanDownCorrection m n) / Real.sqrt (m.totient : ℝ) + _) = _
    unfold ramanujanUpCorrectionTerm
    ring
  have hs := (hasSum_ramanujan_correction m hm n hn).tendsto_sum_nat
  have hshift := (tendsto_add_atTop_iff_nat 1).mpr hs
  have hlim := (hshift.const_sub (∑ t ∈ Icc 1 y, ramanujanUpCorrectionTerm m n t)).div_const
    (Real.sqrt (m.totient : ℝ))
  have htarget :
      ((∑ t ∈ Icc 1 y, ramanujanUpCorrectionTerm m n t) -
        (-(Real.log m + tameDifferent m) * ramanujanLagCoefficient m n -
          ramanujanDownCorrection m n)) / Real.sqrt (m.totient : ℝ) =
      singlePrimeCorrection m y n := by
    rw [hid]; ring
  rw [htarget] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop y] with T hT
  have hrng : range (T + 1) = insert 0 (Icc 1 y ∪ Ioc y T) := by
    ext t; simp only [mem_range, mem_insert, mem_union, mem_Icc, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 y) (Ioc y T) := by
    rw [Finset.disjoint_left]; intro t ht1 ht2; simp only [mem_Icc, mem_Ioc] at ht1 ht2; omega
  have hnot0 : (0 : ℕ) ∉ Icc 1 y ∪ Ioc y T := by simp
  have hsum_split : (∑ t ∈ range (T + 1), ramanujanUpCorrectionTerm m n t) =
      (∑ t ∈ Icc 1 y, ramanujanUpCorrectionTerm m n t) +
        ∑ t ∈ Ioc y T, ramanujanUpCorrectionTerm m n t := by
    rw [hrng, sum_insert hnot0, sum_union hdisj]
    simp [ramanujanUpCorrectionTerm]
  rw [hsum_split, ← sum_div]
  ring

private theorem singlePrimeCorrection_periodic_pos {m : ℕ} (hm : 0 < m) (y : ℕ)
    {n : ℕ} (hn : 1 ≤ n) :
    singlePrimeCorrection m y (n + m) = singlePrimeCorrection m y n := by
  have hper_lag : Function.Periodic (ramanujanLagCoefficient m) m := by
    intro x
    have hφ : Real.sqrt (m.totient : ℝ) ≠ 0 :=
      (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hm)).ne'
    have h1 := normalizedRamanujanMode_periodic hm x
    rw [normalizedRamanujanMode_eq_coefficient hm, normalizedRamanujanMode_eq_coefficient hm] at h1
    exact (div_left_inj' hφ).mp h1
  have hterm : ∀ t : ℕ, ramanujanUpCorrectionTerm m (n + m) t = ramanujanUpCorrectionTerm m n t := by
    intro t
    unfold ramanujanUpCorrectionTerm
    rw [show (n + m) * t = n * t + t * m by ring, periodic_add_mul' hper_lag t (n * t), hper_lag n]
  have h1 := tendsto_tail_singlePrimeCorrection hm (by omega : 0 < n + m) y
  have h2 := tendsto_tail_singlePrimeCorrection hm hn y
  simp_rw [hterm] at h1
  exact tendsto_nhds_unique h1 h2

private theorem card_filter_mul_mod_le_gcd' {m : ℕ} (hm : 0 < m) (t z : ℕ) :
    ((range m).filter (fun r => (r * t) % m = z)).card ≤ Nat.gcd m t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · rw [Nat.gcd_zero_right]
    exact (card_filter_le _ _).trans_eq (card_range m)
  let F := (range m).filter (fun r => (r * t) % m = z)
  by_cases hne : F.Nonempty
  · let r₀ := F.min' hne
    have hr₀_mem : r₀ ∈ F := Finset.min'_mem F hne
    have hr₀_mod : (r₀ * t) % m = z := (mem_filter.mp hr₀_mem).2
    let g := Nat.gcd m t
    have hg0 : 0 < g := Nat.gcd_pos_of_pos_left t hm
    let m' := m / g
    let t' := t / g
    have hm_eq : m' * g = m := Nat.div_mul_cancel (Nat.gcd_dvd_left m t)
    have ht_eq : t' * g = t := Nat.div_mul_cancel (Nat.gcd_dvd_right m t)
    have hm'0 : 0 < m' := Nat.div_pos (Nat.gcd_le_left t hm) hg0
    have hcop : m'.Coprime t' := Nat.coprime_div_gcd_div_gcd hg0
    have hdvd_diff : ∀ r ∈ F, m' ∣ r - r₀ := by
      intro r hr
      have hle : r₀ ≤ r := Finset.min'_le F r hr
      have hr_mod : (r * t) % m = z := (mem_filter.mp hr).2
      have hdiv1 := Nat.div_add_mod (r * t) m
      have hdiv0 := Nat.div_add_mod (r₀ * t) m
      rw [hr_mod] at hdiv1; rw [hr₀_mod] at hdiv0
      have hsub : (r - r₀) * t = m * (r * t / m - r₀ * t / m) := by
        rw [Nat.sub_mul, Nat.mul_sub_left_distrib]
        have hle_mul : r₀ * t ≤ r * t := Nat.mul_le_mul_right t hle
        have hle_div : m * (r₀ * t / m) ≤ m * (r * t / m) :=
          Nat.mul_le_mul_left m (Nat.div_le_div_right hle_mul)
        omega
      have hmdvd : m ∣ (r - r₀) * t := ⟨r * t / m - r₀ * t / m, hsub⟩
      have hgdvd : m' * g ∣ ((r - r₀) * t') * g := by
        rw [hm_eq, Nat.mul_assoc, ht_eq]; exact hmdvd
      exact hcop.dvd_of_dvd_mul_right (Nat.dvd_of_mul_dvd_mul_right hg0 hgdvd)
    refine (Finset.card_le_card_of_injOn (fun r => (r - r₀) / m') ?_ ?_).trans_eq (card_range g)
    · intro r hr
      have hrm : r < m := mem_range.mp (mem_filter.mp hr).1
      exact mem_range.mpr (Nat.div_lt_of_lt_mul (by omega))
    · intro r₁ hr₁ r₂ hr₂ heq
      have hle₁ := Finset.min'_le F r₁ hr₁
      have hle₂ := Finset.min'_le F r₂ hr₂
      have hd₁ := Nat.div_mul_cancel (hdvd_diff r₁ hr₁)
      have hd₂ := Nat.div_mul_cancel (hdvd_diff r₂ hr₂)
      dsimp only at heq
      have hsub_eq : r₁ - r₀ = r₂ - r₀ := by rw [← hd₁, ← hd₂, heq]
      omega
  · change F.card ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hne, card_empty]
    exact Nat.zero_le _

private theorem sum_Icc_normalizedRamanujanMode_mul_sq_le' {m : ℕ} (hm : 0 < m) (t : ℕ) :
    (∑ n ∈ Icc 1 m, normalizedRamanujanMode m (n * t) ^ 2) ≤ (Nat.gcd m t : ℝ) * m := by
  have hper_base := normalizedRamanujanMode_periodic hm
  have hper : Function.Periodic (fun n => normalizedRamanujanMode m (n * t) ^ 2) m := fun n => by
    dsimp only
    rw [show (n + m) * t = n * t + t * m by ring, periodic_add_mul' hper_base t (n * t)]
  have h0 : Icc 1 m = Ioc 0 (0 + m) := by ext x; simp only [mem_Icc, mem_Ioc]; omega
  rw [h0, sum_Ioc_periodic_eq hm hper 0]
  have hmod_eq : ∀ r : ℕ, normalizedRamanujanMode m (r * t) =
      normalizedRamanujanMode m ((r * t) % m) := fun r => by
    conv_lhs => rw [← Nat.mod_add_div (r * t) m, Nat.mul_comm m _,
      periodic_add_mul' hper_base (r * t / m) (r * t % m)]
  have hmaps : ∀ r ∈ range m, (r * t) % m ∈ range m :=
    fun r _ => mem_range.mpr (Nat.mod_lt _ hm)
  calc
    (∑ r ∈ range m, normalizedRamanujanMode m (r * t) ^ 2) =
        ∑ r ∈ range m, normalizedRamanujanMode m ((r * t) % m) ^ 2 :=
      sum_congr rfl fun r _ => by rw [hmod_eq r]
    _ = ∑ z ∈ range m, ∑ r ∈ (range m).filter (fun r => (r * t) % m = z),
          normalizedRamanujanMode m ((r * t) % m) ^ 2 :=
      (sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ z ∈ range m, (((range m).filter (fun r => (r * t) % m = z)).card : ℝ) *
          normalizedRamanujanMode m z ^ 2 := by
      refine sum_congr rfl fun z _ => ?_
      rw [sum_congr rfl (fun r hr => by rw [(mem_filter.mp hr).2]), sum_const, nsmul_eq_mul]
    _ ≤ ∑ z ∈ range m, (Nat.gcd m t : ℝ) * normalizedRamanujanMode m z ^ 2 := by
      refine sum_le_sum fun z _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      exact_mod_cast card_filter_mul_mod_le_gcd' hm t z
    _ = (Nat.gcd m t : ℝ) * ∑ z ∈ range m, normalizedRamanujanMode m z ^ 2 := (mul_sum _ _ _).symm
    _ = (Nat.gcd m t : ℝ) * m := by
      have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      rw [(div_eq_iff hmR).mp (periodMean_normalizedRamanujanMode_sq hm), one_mul]

private theorem sum_primeFactors_localMangoldtMass_mul_gcd_le' {m : ℕ} (hm : 0 < m) (y T : ℕ) :
    (∑ p ∈ m.primeFactors, ∑ t ∈ Ioc y T, localMangoldtMass p t * (Nat.gcd m t : ℝ)) ≤
      2 * Real.log m := by
  have hfor_p : ∀ p ∈ m.primeFactors,
      (∑ t ∈ Ioc y T, localMangoldtMass p t * (Nat.gcd m t : ℝ)) ≤
        2 * (m.factorization p : ℝ) * Real.log p := by
    intro p hp_mem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp0 : (0 : ℝ) < p := by linarith only [hp2]
    have hp1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith only [hp2]
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith only [hp2])
    let a := m.factorization p
    have ha1 : 1 ≤ a :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (m.support_factorization ▸ hp_mem))
    have hndvd : ¬ p ^ (a + 1) ∣ m := Nat.pow_succ_factorization_not_dvd hm.ne' hp
    let S := (Ioc y T).filter (fun t => localMangoldtMass p t ≠ 0)
    have hrestrict : (∑ t ∈ Ioc y T, localMangoldtMass p t * (Nat.gcd m t : ℝ)) =
        ∑ t ∈ S, localMangoldtMass p t * (Nat.gcd m t : ℝ) := by
      symm
      refine sum_subset (filter_subset _ _) fun t _ htS => ?_
      have hz : localMangoldtMass p t = 0 := by
        by_contra hne; exact htS (mem_filter.mpr ⟨‹_›, hne⟩)
      rw [hz, zero_mul]
    have hS_sub : S ⊆ (range T).image (fun k => p ^ (k + 1)) := by
      intro t ht
      obtain ⟨htI, hne⟩ := mem_filter.mp ht
      have hpdvd : p ∣ t := by
        unfold localMangoldtMass at hne
        by_contra hnd; rw [if_neg hnd] at hne; exact hne rfl
      have hΛne : Λ t ≠ 0 := by
        unfold localMangoldtMass at hne; rw [if_pos hpdvd] at hne
        intro hz; rw [hz, zero_div] at hne; exact hne rfl
      obtain ⟨q, j, hq, hj, rfl⟩ := (isPrimePow_nat_iff t).mp (vonMangoldt_ne_zero_iff.mp hΛne)
      have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpdvd)
      subst hpq
      refine mem_image.mpr ⟨j - 1, mem_range.mpr ?_, by congr 1; omega⟩
      have htT : p ^ j ≤ T := (mem_Ioc.mp htI).2
      have hj_lt : j ≤ p ^ j := (Nat.lt_pow_self hp.one_lt).le
      omega
    have hinj : Function.Injective (fun k : ℕ => p ^ (k + 1)) :=
      fun k₁ k₂ h => Nat.succ.inj ((Nat.pow_right_injective hp.one_lt) h)
    have hpow_val : ∀ k : ℕ, localMangoldtMass p (p ^ (k + 1)) =
        Real.log p / (p : ℝ) ^ (k + 1) := fun k => by
      rw [localMangoldtMass, if_pos (dvd_pow_self p (by omega)),
        vonMangoldt_prime_pow hp (by omega), Nat.cast_pow]
    have hrng_sub : range T ⊆ range a ∪ (range T).image (fun j => a + j) := fun k hk => by
      by_cases hka : k < a
      · exact mem_union_left _ (mem_range.mpr hka)
      · exact mem_union_right _ (mem_image.mpr ⟨k - a,
          mem_range.mpr (by have := mem_range.mp hk; omega), by omega⟩)
    have hlow : (∑ k ∈ range a, localMangoldtMass p (p ^ (k + 1)) *
        (Nat.gcd m (p ^ (k + 1)) : ℝ)) ≤ (a : ℝ) * Real.log p := by
      have hpt : ∀ k ∈ range a, localMangoldtMass p (p ^ (k + 1)) *
          (Nat.gcd m (p ^ (k + 1)) : ℝ) ≤ Real.log p := fun k _ => by
        rw [hpow_val k]
        have hgcd : (Nat.gcd m (p ^ (k + 1)) : ℝ) ≤ (p : ℝ) ^ (k + 1) := by
          exact_mod_cast Nat.gcd_le_right m (pow_pos hp.pos _)
        exact (mul_le_mul_of_nonneg_left hgcd (by positivity)).trans_eq
          (div_mul_cancel₀ _ (pow_pos hp0 _).ne')
      calc
        _ ≤ ∑ _k ∈ range a, Real.log p := sum_le_sum hpt
        _ = (a : ℝ) * Real.log p := by rw [sum_const, card_range, nsmul_eq_mul]
    have hhigh : (∑ k ∈ (range T).image (fun j => a + j),
        localMangoldtMass p (p ^ (k + 1)) * (Nat.gcd m (p ^ (k + 1)) : ℝ)) ≤ Real.log p := by
      rw [sum_image (fun j₁ _ j₂ _ h => Nat.add_left_cancel h)]
      have hpt : ∀ j ∈ range T, localMangoldtMass p (p ^ (a + j + 1)) *
          (Nat.gcd m (p ^ (a + j + 1)) : ℝ) ≤ Real.log p / (p : ℝ) ^ (j + 1) := fun j _ => by
        rw [hpow_val (a + j)]
        obtain ⟨i, _, hi_eq⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right m (p ^ (a + j + 1)))
        have hi_le : i ≤ a := by
          by_contra hgt
          exact hndvd ((Nat.pow_dvd_pow p (by omega)).trans (hi_eq ▸ Nat.gcd_dvd_left m _))
        have hgcd : (Nat.gcd m (p ^ (a + j + 1)) : ℝ) ≤ (p : ℝ) ^ a := by
          rw [hi_eq, Nat.cast_pow]; exact pow_le_pow_right₀ (by linarith only [hp2]) hi_le
        calc
          (Real.log p / (p : ℝ) ^ (a + j + 1)) * (Nat.gcd m (p ^ (a + j + 1)) : ℝ) ≤
              (Real.log p / (p : ℝ) ^ (a + j + 1)) * (p : ℝ) ^ a :=
            mul_le_mul_of_nonneg_left hgcd (by positivity)
          _ = Real.log p / (p : ℝ) ^ (j + 1) := by
            rw [show a + j + 1 = a + (j + 1) by omega, pow_add]
            field_simp [(pow_pos hp0 a).ne', (pow_pos hp0 (j + 1)).ne']
      have hgeom : ∀ J : ℕ, (∑ j ∈ range J, Real.log p / (p : ℝ) ^ (j + 1)) =
          Real.log p / ((p : ℝ) - 1) - (Real.log p / ((p : ℝ) - 1)) / (p : ℝ) ^ J := by
        intro J
        induction J with
        | zero => simp
        | succ J ih =>
          rw [Finset.sum_range_succ, ih, pow_succ]
          field_simp [hp0.ne', (show (p : ℝ) - 1 ≠ 0 by linarith only [hp2])]; ring
      calc
        _ ≤ ∑ j ∈ range T, Real.log p / (p : ℝ) ^ (j + 1) := sum_le_sum hpt
        _ = Real.log p / ((p : ℝ) - 1) - (Real.log p / ((p : ℝ) - 1)) / (p : ℝ) ^ T := hgeom T
        _ ≤ Real.log p / ((p : ℝ) - 1) := sub_le_self _ (by positivity)
        _ ≤ Real.log p := div_le_self hlogp hp1
    have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    rw [hrestrict]
    calc
      (∑ t ∈ S, localMangoldtMass p t * (Nat.gcd m t : ℝ)) ≤
          ∑ t ∈ (range T).image (fun k => p ^ (k + 1)),
            localMangoldtMass p t * (Nat.gcd m t : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hS_sub fun t _ _ =>
          mul_nonneg (localMangoldtMass_nonneg p t) (Nat.cast_nonneg _)
      _ = ∑ k ∈ range T, localMangoldtMass p (p ^ (k + 1)) * (Nat.gcd m (p ^ (k + 1)) : ℝ) :=
        sum_image fun a _ b _ h => hinj h
      _ ≤ ∑ k ∈ range a ∪ (range T).image (fun j => a + j),
            localMangoldtMass p (p ^ (k + 1)) * (Nat.gcd m (p ^ (k + 1)) : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hrng_sub fun k _ _ =>
          mul_nonneg (localMangoldtMass_nonneg p _) (Nat.cast_nonneg _)
      _ ≤ (∑ k ∈ range a, localMangoldtMass p (p ^ (k + 1)) * (Nat.gcd m (p ^ (k + 1)) : ℝ)) +
          ∑ k ∈ (range T).image (fun j => a + j),
            localMangoldtMass p (p ^ (k + 1)) * (Nat.gcd m (p ^ (k + 1)) : ℝ) :=
        sum_union_le_of_nonneg' fun k _ =>
          mul_nonneg (localMangoldtMass_nonneg p _) (Nat.cast_nonneg _)
      _ ≤ (a : ℝ) * Real.log p + Real.log p := add_le_add hlow hhigh
      _ ≤ 2 * (a : ℝ) * Real.log p := by nlinarith only [haR, hlogp]
  have hfact_log : (∑ p ∈ m.primeFactors, (m.factorization p : ℝ) * Real.log p) = Real.log m := by
    have hprod : (∏ p ∈ m.primeFactors, ((p : ℝ) ^ (m.factorization p))) = (m : ℝ) := by
      exact_mod_cast Nat.prod_factorization_pow_eq_self hm.ne'
    rw [← hprod, Real.log_prod (fun p hp =>
      pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero))]
    exact sum_congr rfl fun p _ => (Real.log_pow _ _).symm
  calc
    (∑ p ∈ m.primeFactors, ∑ t ∈ Ioc y T, localMangoldtMass p t * (Nat.gcd m t : ℝ)) ≤
        ∑ p ∈ m.primeFactors, 2 * (m.factorization p : ℝ) * Real.log p := sum_le_sum hfor_p
    _ = 2 * ∑ p ∈ m.primeFactors, (m.factorization p : ℝ) * Real.log p := by
      rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    _ = 2 * Real.log m := by rw [hfact_log]

private theorem sum_Icc_singlePrimeCorrection_sq_le {m y : ℕ} (hm : 0 < m) (hy : 0 < y) :
    (∑ n ∈ Icc 1 m, singlePrimeCorrection m y n ^ 2) ≤
      16 * (m : ℝ) * (Real.log m) ^ 2 / (y : ℝ) := by
  let w : ℕ → ℝ := fun t => ∑ p ∈ m.primeFactors, localMangoldtMass p t
  have hw0 : ∀ t, 0 ≤ w t := fun t => sum_nonneg fun p _ => localMangoldtMass_nonneg p t
  have hterm_le : ∀ n t : ℕ,
      |ramanujanUpCorrectionTerm m n t / Real.sqrt (m.totient : ℝ)| ≤
        |normalizedRamanujanMode m (n * t) - normalizedRamanujanMode m n| * w t := by
    intro n t
    have heq : ramanujanUpCorrectionTerm m n t / Real.sqrt (m.totient : ℝ) =
        (normalizedRamanujanMode m (n * t) - normalizedRamanujanMode m n) * Λ t / (t : ℝ) := by
      unfold ramanujanUpCorrectionTerm
      rw [normalizedRamanujanMode_eq_coefficient hm, normalizedRamanujanMode_eq_coefficient hm]
      ring
    rw [heq]
    by_cases hΛ : Λ t = 0
    · rw [hΛ, mul_zero, zero_div, abs_zero]
      exact mul_nonneg (abs_nonneg _) (hw0 t)
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff t).mp (vonMangoldt_ne_zero_iff.mp hΛ)
    by_cases hpm : p ∣ m
    · have hmem : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpm, hm.ne'⟩
      have hmass : Λ (p ^ k) / ((p ^ k : ℕ) : ℝ) ≤ w (p ^ k) := by
        dsimp only [w]
        have h := single_le_sum (f := fun q => localMangoldtMass q (p ^ k))
          (fun q _ => localMangoldtMass_nonneg q (p ^ k)) hmem
        rwa [localMangoldtMass, if_pos (dvd_pow_self p hk.ne')] at h
      rw [mul_div_assoc, abs_mul, abs_div,
        abs_of_nonneg (show 0 ≤ Λ (p ^ k) from vonMangoldt_nonneg),
        abs_of_nonneg (show 0 ≤ ((p ^ k : ℕ) : ℝ) from Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left hmass (abs_nonneg _)
    · have hmp : m.Coprime p := (hp.coprime_iff_not_dvd.mpr hpm).symm
      have hdiff : normalizedRamanujanMode m (n * p ^ k) - normalizedRamanujanMode m n = 0 := by
        rw [normalizedRamanujanMode_eq_coefficient hm, normalizedRamanujanMode_eq_coefficient hm,
          ramanujanCoefficient_mul_lag_of_coprime (hmp.pow_right k), sub_self]
      rw [hdiff, zero_mul, zero_div, abs_zero, zero_mul]
  have hw_tail : ∀ T : ℕ, (∑ t ∈ Ioc y T, w t) ≤ 2 * Real.log m / (y : ℝ) := by
    intro T
    have hp_tail : ∀ p ∈ m.primeFactors,
        (∑ t ∈ Ioc y T, localMangoldtMass p t) ≤ localMangoldtTail p y := by
      intro p hp_mem
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
      by_cases hTy : T ≤ y
      · rw [Ioc_eq_empty (by omega), sum_empty]
        unfold localMangoldtTail
        exact sub_nonneg.mpr
          ((summable_localMangoldtMass hp).sum_le_tsum _ fun t _ => localMangoldtMass_nonneg p t)
      · have hdisj : Disjoint (range (y + 1)) (Ioc y T) := by
          rw [Finset.disjoint_left]; intro t ht1 ht2; simp only [mem_range, mem_Ioc] at ht1 ht2; omega
        have hunion : range (y + 1) ∪ Ioc y T = range (T + 1) := by
          ext t; simp only [mem_union, mem_range, mem_Ioc]; omega
        have hsum := (summable_localMangoldtMass hp).sum_le_tsum (range (T + 1))
          fun t _ => localMangoldtMass_nonneg p t
        rw [← hunion, sum_union hdisj] at hsum
        unfold localMangoldtTail
        linarith only [hsum]
    have hlog_sum : (∑ p ∈ m.primeFactors, Real.log p) ≤ Real.log m := by
      have hprimes : ∀ p ∈ m.primeFactors, p.Prime := fun _ hp => Nat.prime_of_mem_primeFactors hp
      have hpos : 0 < ∏ p ∈ m.primeFactors, p := prod_pos fun p hp => (hprimes p hp).pos
      have hle : ((∏ p ∈ m.primeFactors, p : ℕ) : ℝ) ≤ m := by
        exact_mod_cast Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)
      rw [← Real.log_prod (fun p hp => by exact_mod_cast (hprimes p hp).ne_zero), ← Nat.cast_prod]
      exact Real.log_le_log (by exact_mod_cast hpos) hle
    dsimp only [w]
    rw [sum_comm]
    calc
      (∑ p ∈ m.primeFactors, ∑ t ∈ Ioc y T, localMangoldtMass p t) ≤
          ∑ p ∈ m.primeFactors, localMangoldtTail p y := sum_le_sum hp_tail
      _ ≤ ∑ p ∈ m.primeFactors, (2 * Real.log p / (y : ℝ)) :=
        sum_le_sum fun p hp => localMangoldtTail_le (Nat.prime_of_mem_primeFactors hp) hy
      _ = 2 * (∑ p ∈ m.primeFactors, Real.log p) / (y : ℝ) := by rw [← sum_div, ← mul_sum]
      _ ≤ 2 * Real.log m / (y : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog_sum zero_le_two)
          (Nat.cast_nonneg y)
  have hT_bound : ∀ T : ℕ,
      (∑ n ∈ Icc 1 m,
        (-(∑ t ∈ Ioc y T, ramanujanUpCorrectionTerm m n t / Real.sqrt (m.totient : ℝ))) ^ 2) ≤
        16 * (m : ℝ) * (Real.log m) ^ 2 / (y : ℝ) := by
    intro T
    have hcs_n : ∀ n ∈ Icc 1 m,
        (-(∑ t ∈ Ioc y T, ramanujanUpCorrectionTerm m n t / Real.sqrt (m.totient : ℝ))) ^ 2 ≤
          (∑ t ∈ Ioc y T, w t) *
            ∑ t ∈ Ioc y T, w t *
              (normalizedRamanujanMode m (n * t) - normalizedRamanujanMode m n) ^ 2 := by
      intro n _
      rw [neg_sq]
      have habs : |∑ t ∈ Ioc y T, ramanujanUpCorrectionTerm m n t / Real.sqrt (m.totient : ℝ)| ≤
          ∑ t ∈ Ioc y T, Real.sqrt (w t) *
            (Real.sqrt (w t) * |normalizedRamanujanMode m (n * t) - normalizedRamanujanMode m n|) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t _ => ?_)
        refine (hterm_le n t).trans_eq ?_
        rw [← mul_assoc, Real.mul_self_sqrt (hw0 t), mul_comm]
      have hsq := mul_self_le_mul_self (abs_nonneg _) habs
      rw [← sq, sq_abs, ← sq] at hsq
      refine hsq.trans ?_
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Ioc y T) (fun t => Real.sqrt (w t))
        (fun t => Real.sqrt (w t) * |normalizedRamanujanMode m (n * t) - normalizedRamanujanMode m n|)
      refine hcs.trans_eq ?_
      congr 1
      · exact sum_congr rfl fun t _ => Real.sq_sqrt (hw0 t)
      · exact sum_congr rfl fun t _ => by rw [mul_pow, Real.sq_sqrt (hw0 t), sq_abs]
    have hdiff_sum : ∀ t ∈ Ioc y T,
        (∑ n ∈ Icc 1 m, (normalizedRamanujanMode m (n * t) - normalizedRamanujanMode m n) ^ 2) ≤
          4 * (Nat.gcd m t : ℝ) * m := by
      intro t _
      have hgcd1 : (1 : ℝ) ≤ Nat.gcd m t := by exact_mod_cast Nat.gcd_pos_of_pos_left t hm
      have h2sq : ∀ n ∈ Icc 1 m,
          (normalizedRamanujanMode m (n * t) - normalizedRamanujanMode m n) ^ 2 ≤
            2 * normalizedRamanujanMode m (n * t) ^ 2 + 2 * normalizedRamanujanMode m n ^ 2 :=
        fun n _ => by
          nlinarith only [sq_nonneg (normalizedRamanujanMode m (n * t) + normalizedRamanujanMode m n)]
      have hIcc_base : (∑ n ∈ Icc 1 m, normalizedRamanujanMode m n ^ 2) = (m : ℝ) := by
        have h1 : Icc 1 m = Ioc 0 (0 + m) := by ext x; simp only [mem_Icc, mem_Ioc]; omega
        rw [h1, sum_Ioc_normalizedRamanujanMode_sq hm 0]
      calc
        (∑ n ∈ Icc 1 m, (normalizedRamanujanMode m (n * t) - normalizedRamanujanMode m n) ^ 2) ≤
            ∑ n ∈ Icc 1 m,
              (2 * normalizedRamanujanMode m (n * t) ^ 2 + 2 * normalizedRamanujanMode m n ^ 2) :=
          sum_le_sum h2sq
        _ = 2 * (∑ n ∈ Icc 1 m, normalizedRamanujanMode m (n * t) ^ 2) +
              2 * (∑ n ∈ Icc 1 m, normalizedRamanujanMode m n ^ 2) := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum]
        _ ≤ 2 * ((Nat.gcd m t : ℝ) * m) + 2 * (m : ℝ) :=
          add_le_add (mul_le_mul_of_nonneg_left
            (sum_Icc_normalizedRamanujanMode_mul_sq_le' hm t) zero_le_two) (by rw [hIcc_base])
        _ ≤ 4 * (Nat.gcd m t : ℝ) * m := by
          nlinarith only [hgcd1, show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
    have hsecond : (∑ t ∈ Ioc y T, w t *
        ∑ n ∈ Icc 1 m, (normalizedRamanujanMode m (n * t) - normalizedRamanujanMode m n) ^ 2) ≤
          8 * (m : ℝ) * Real.log m := by
      calc
        _ ≤ ∑ t ∈ Ioc y T, w t * (4 * (Nat.gcd m t : ℝ) * m) :=
          sum_le_sum fun t ht => mul_le_mul_of_nonneg_left (hdiff_sum t ht) (hw0 t)
        _ = 4 * (m : ℝ) * ∑ p ∈ m.primeFactors, ∑ t ∈ Ioc y T,
              localMangoldtMass p t * (Nat.gcd m t : ℝ) := by
          dsimp only [w]
          simp_rw [sum_mul]
          rw [sum_comm, mul_sum]
          exact sum_congr rfl fun p _ => by rw [mul_sum]; exact sum_congr rfl fun t _ => by ring
        _ ≤ 4 * (m : ℝ) * (2 * Real.log m) :=
          mul_le_mul_of_nonneg_left
            (sum_primeFactors_localMangoldtMass_mul_gcd_le' hm y T) (by positivity)
        _ = 8 * (m : ℝ) * Real.log m := by ring
    calc
      (∑ n ∈ Icc 1 m,
          (-(∑ t ∈ Ioc y T, ramanujanUpCorrectionTerm m n t / Real.sqrt (m.totient : ℝ))) ^ 2) ≤
          ∑ n ∈ Icc 1 m, (∑ t ∈ Ioc y T, w t) *
            ∑ t ∈ Ioc y T, w t *
              (normalizedRamanujanMode m (n * t) - normalizedRamanujanMode m n) ^ 2 :=
        sum_le_sum hcs_n
      _ = (∑ t ∈ Ioc y T, w t) *
            ∑ t ∈ Ioc y T, w t *
              ∑ n ∈ Icc 1 m, (normalizedRamanujanMode m (n * t) - normalizedRamanujanMode m n) ^ 2 := by
        rw [← mul_sum]; congr 1; rw [Finset.sum_comm]
        exact sum_congr rfl fun t _ => (mul_sum _ _ _).symm
      _ ≤ (2 * Real.log m / (y : ℝ)) * (8 * (m : ℝ) * Real.log m) :=
        mul_le_mul (hw_tail T) hsecond
          (sum_nonneg fun t _ => mul_nonneg (hw0 t) (sum_nonneg fun _ _ => sq_nonneg _))
          (by have := Real.log_natCast_nonneg m; positivity)
      _ = 16 * (m : ℝ) * (Real.log m) ^ 2 / (y : ℝ) := by ring
  have hlim_sum : Tendsto (fun T : ℕ =>
      ∑ n ∈ Icc 1 m,
        (-(∑ t ∈ Ioc y T, ramanujanUpCorrectionTerm m n t / Real.sqrt (m.totient : ℝ))) ^ 2)
      atTop (𝓝 (∑ n ∈ Icc 1 m, singlePrimeCorrection m y n ^ 2)) :=
    tendsto_finsetSum _ fun n hn =>
      (tendsto_tail_singlePrimeCorrection hm (mem_Icc.mp hn).1 y).pow 2
  exact le_of_tendsto' hlim_sum hT_bound

/-- Individual conductor prime-tower tail bound retaining `(log m)^2`: for `2 ≤ m` with
`m * m ≤ N`, `∑_{n=1}^N singlePrimeCorrection m (N / n) n ^ 2 / n ≤ 192 * (log m)^2`. -/
private theorem sum_singlePrimeCorrection_sq_div_le {m N : ℕ}
    (hm2 : 2 ≤ m) (hmN_sq : m * m ≤ N) :
    (∑ n ∈ Icc 1 N, singlePrimeCorrection m (N / n) n ^ 2 / (n : ℝ)) ≤
      192 * (Real.log m) ^ 2 := by
  have hm : 0 < m := by omega
  have hN0 : 0 < N := (Nat.mul_pos hm hm).trans_le hmN_sq
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hNm_le : N / m ≤ N := Nat.div_le_self N m
  have hunion : Icc 1 N = Icc 1 (N / m) ∪ Ioc (N / m) N := by
    have := Nat.zero_le (N / m)
    ext n; simp only [mem_Icc, mem_union, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 (N / m)) (Ioc (N / m) N) := by
    rw [Finset.disjoint_left]; intro n hn1 hn2; simp only [mem_Icc, mem_Ioc] at hn1 hn2; omega
  have hpart1 : (∑ n ∈ Icc 1 (N / m),
      singlePrimeCorrection m (N / n) n ^ 2 / (n : ℝ)) ≤ 64 * (Real.log m) ^ 2 := by
    have hpt : ∀ n ∈ Icc 1 (N / m),
        singlePrimeCorrection m (N / n) n ^ 2 / (n : ℝ) ≤ 64 * (Real.log m) ^ 2 / N := by
      intro n hn
      obtain ⟨hn1, hnNm⟩ := mem_Icc.mp hn
      have hnN : n ≤ N := hnNm.trans hNm_le
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
      have hy : 1 ≤ N / n := Nat.div_pos hnN hn1
      have hyR : (0 : ℝ) < (N / n : ℕ) := by exact_mod_cast hy
      have hb := abs_normalizedRamanujan_correction_le hm hn1 hy
      have hbsq := mul_self_le_mul_self (abs_nonneg _) hb
      rw [← sq, sq_abs, ← sq, div_pow, mul_pow, mul_pow,
        Real.sq_sqrt (Nat.cast_nonneg m.totient)] at hbsq
      have hφ_le : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
      have hNy : (N : ℝ) ≤ 2 * ((N / n : ℕ) : ℝ) * n := by
        have hmod := Nat.mod_lt N hn1
        have hid := Nat.mod_add_div N n
        have hlt : N < (N / n + 1) * n := by nlinarith only [hmod, hid]
        have hle : N ≤ 2 * (N / n) * n := by nlinarith only [hlt, hy]
        exact_mod_cast hle
      have hinv_y2 : 1 / ((N / n : ℕ) : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ (sq_pos_of_pos hyR) (sq_pos_of_pos hNR)]
        have hsq := pow_le_pow_left₀ hNR.le hNy 2
        nlinarith only [hsq]
      have hmnN : (m : ℝ) * n ≤ N := by
        have hnat : n * m ≤ N := (Nat.le_div_iff_mul_le hm).mp hnNm
        exact_mod_cast (Nat.mul_comm m n ▸ hnat)
      calc
        singlePrimeCorrection m (N / n) n ^ 2 / n ≤
            (16 * (m.totient : ℝ) * (Real.log m) ^ 2 / ((N / n : ℕ) : ℝ) ^ 2) / n :=
          div_le_div_of_nonneg_right (hbsq.trans_eq (by ring)) hnR.le
        _ ≤ (16 * (m : ℝ) * (Real.log m) ^ 2 * (1 / ((N / n : ℕ) : ℝ) ^ 2)) / n := by
          refine div_le_div_of_nonneg_right ?_ hnR.le
          rw [div_eq_mul_inv, ← one_div]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hφ_le (by norm_num))
              (sq_nonneg _)) (by positivity)
        _ ≤ (16 * (m : ℝ) * (Real.log m) ^ 2 * (4 * (n : ℝ) ^ 2 / (N : ℝ) ^ 2)) / n :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hinv_y2 (by positivity)) hnR.le
        _ = 64 * ((m : ℝ) * n) * (Real.log m) ^ 2 / (N : ℝ) ^ 2 := by
          field_simp [hnR.ne', hNR.ne']; ring
        _ ≤ 64 * (N : ℝ) * (Real.log m) ^ 2 / (N : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmnN (by norm_num))
              (sq_nonneg _)) (sq_nonneg _)
        _ = 64 * (Real.log m) ^ 2 / N := by field_simp [hNR.ne']
    have hcard_le : ((N / m : ℕ) : ℝ) ≤ N := by exact_mod_cast hNm_le
    calc
      (∑ n ∈ Icc 1 (N / m), singlePrimeCorrection m (N / n) n ^ 2 / (n : ℝ)) ≤
          ∑ _n ∈ Icc 1 (N / m), 64 * (Real.log m) ^ 2 / N := sum_le_sum hpt
      _ = ((N / m : ℕ) : ℝ) * (64 * (Real.log m) ^ 2 / N) := by
        rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (64 * (Real.log m) ^ 2 / N) :=
        mul_le_mul_of_nonneg_right hcard_le (by positivity)
      _ = 64 * (Real.log m) ^ 2 := mul_div_cancel₀ _ hNR.ne'
  have hcover_y : Ioc (N / m) N ⊆
      (Icc 1 (m - 1)).biUnion (fun y => Ioc (N / (y + 1)) (N / y)) := by
    intro n hn
    obtain ⟨hn_gt, hn_le⟩ := mem_Ioc.mp hn
    have hn0 : 0 < n := (Nat.zero_le _).trans_lt hn_gt
    let y := N / n
    have hy1 : 1 ≤ y := Nat.div_pos hn_le hn0
    have hym : y ≤ m - 1 := by
      have hlt : y < m := by
        by_contra hge
        have hnm : m * n ≤ N := (Nat.le_div_iff_mul_le hn0).mp (le_of_not_gt hge)
        have hnle : n ≤ N / m := (Nat.le_div_iff_mul_le hm).mpr (Nat.mul_comm m n ▸ hnm)
        omega
      omega
    have hn_hi : n ≤ N / y :=
      (Nat.le_div_iff_mul_le hy1).mpr (Nat.mul_comm n y ▸ Nat.div_mul_le_self N n)
    have hn_lo : N / (y + 1) < n := by
      by_contra hle
      have hmul : n * (y + 1) ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp (le_of_not_gt hle)
      have hy_ge : y + 1 ≤ N / n :=
        (Nat.le_div_iff_mul_le hn0).mpr (Nat.mul_comm n (y + 1) ▸ hmul)
      omega
    exact mem_biUnion.mpr ⟨y, mem_Icc.mpr ⟨hy1, hym⟩, mem_Ioc.mpr ⟨hn_lo, hn_hi⟩⟩
  have hdisj_y : Set.PairwiseDisjoint (↑(Icc 1 (m - 1)) : Set ℕ)
      (fun y => Ioc (N / (y + 1)) (N / y)) := by
    intro y₁ _ y₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro n hn₁ hn₂
    obtain ⟨h1a, h1b⟩ := mem_Ioc.mp hn₁
    obtain ⟨h2a, h2b⟩ := mem_Ioc.mp hn₂
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := Nat.div_le_div_left (by omega : y₁ + 1 ≤ y₂) (by omega : 0 < y₁ + 1); omega
    · have := Nat.div_le_div_left (by omega : y₂ + 1 ≤ y₁) (by omega : 0 < y₂ + 1); omega
  have hy_eq : ∀ y ∈ Icc 1 (m - 1), ∀ n ∈ Ioc (N / (y + 1)) (N / y), N / n = y := by
    intro y hyI n hn
    obtain ⟨hy1, _⟩ := mem_Icc.mp hyI
    obtain ⟨hn_lo, hn_hi⟩ := mem_Ioc.mp hn
    have hn0 : 0 < n := (Nat.zero_le _).trans_lt hn_lo
    have hge : y ≤ N / n :=
      (Nat.le_div_iff_mul_le hn0).mpr (Nat.mul_comm y n ▸ (Nat.le_div_iff_mul_le hy1).mp hn_hi)
    have hlt : N / n < y + 1 := by
      by_contra hge1
      have hmul : (y + 1) * n ≤ N := (Nat.le_div_iff_mul_le hn0).mp (le_of_not_gt hge1)
      have hnle : n ≤ N / (y + 1) :=
        (Nat.le_div_iff_mul_le (by omega)).mpr (Nat.mul_comm (y + 1) n ▸ hmul)
      omega
    omega
  have hfor_y : ∀ y ∈ Icc 1 (m - 1),
      (∑ n ∈ Ioc (N / (y + 1)) (N / y),
        singlePrimeCorrection m (N / n) n ^ 2 / (n : ℝ)) ≤
        64 * (Real.log m) ^ 2 *
          ((((Ioc (N / (y + 1)) (N / y)).card : ℝ) + m) / N) := by
    intro y hyI
    obtain ⟨hy1, _⟩ := mem_Icc.mp hyI
    have hyR : (0 : ℝ) < y := by exact_mod_cast hy1
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    let I_y := Ioc (N / (y + 1)) (N / y)
    have hinv_n : ∀ n ∈ I_y, 1 / (n : ℝ) ≤ 4 * (y : ℝ) / N := by
      intro n hn
      have hn_lo : N / (y + 1) < n := (mem_Ioc.mp hn).1
      have hn0 : 0 < n := (Nat.zero_le _).trans_lt hn_lo
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
      have hdiv : N < (N / (y + 1) + 1) * (y + 1) := by
        have hmod := Nat.mod_lt N (by omega : 0 < y + 1)
        have hid := Nat.mod_add_div N (y + 1)
        nlinarith only [hmod, hid]
      have hle_n : N ≤ n * (y + 1) := by
        have hmul := Nat.mul_le_mul_right (y + 1) (show N / (y + 1) + 1 ≤ n from hn_lo)
        omega
      have hle_4 : N ≤ 4 * y * n := by
        calc
          N ≤ n * (y + 1) := hle_n
          _ ≤ n * (4 * y) := Nat.mul_le_mul_left n (by omega)
          _ = 4 * y * n := by ring
      rw [div_le_div_iff₀ hnR hNR, one_mul]
      exact_mod_cast hle_4
    have hper_bound : (∑ n ∈ I_y, singlePrimeCorrection m y n ^ 2) ≤
        ((I_y.card : ℝ) / m + 1) * (16 * (m : ℝ) * (Real.log m) ^ 2 / y) := by
      have h1 := sum_Ioc_le_mul_sum_Icc_of_periodic_pos
        (f := fun n => singlePrimeCorrection m y n ^ 2) hm (fun _ _ => sq_nonneg _)
        (fun n hn => by rw [singlePrimeCorrection_periodic_pos hm y hn])
        (N / (y + 1)) (N / y)
      rw [show N / y - N / (y + 1) = I_y.card from (Nat.card_Ioc _ _).symm] at h1
      have hdiv_le : (((I_y.card / m + 1 : ℕ) : ℝ)) ≤ (I_y.card : ℝ) / m + 1 := by
        push_cast
        have hmul : ((I_y.card / m : ℕ) : ℝ) * m ≤ I_y.card := by
          exact_mod_cast Nat.div_mul_le_self I_y.card m
        linarith [(le_div_iff₀ hmR).mpr hmul]
      exact h1.trans (mul_le_mul hdiv_le (sum_Icc_singlePrimeCorrection_sq_le hm hy1)
        (sum_nonneg fun _ _ => sq_nonneg _) (by positivity))
    calc
      (∑ n ∈ I_y, singlePrimeCorrection m (N / n) n ^ 2 / (n : ℝ)) =
          ∑ n ∈ I_y, singlePrimeCorrection m y n ^ 2 * (1 / (n : ℝ)) :=
        sum_congr rfl fun n hn => by rw [hy_eq y hyI n hn, div_eq_mul_one_div]
      _ ≤ ∑ n ∈ I_y, singlePrimeCorrection m y n ^ 2 * (4 * (y : ℝ) / N) :=
        sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hinv_n n hn) (sq_nonneg _)
      _ = (4 * (y : ℝ) / N) * ∑ n ∈ I_y, singlePrimeCorrection m y n ^ 2 := by
        rw [mul_sum]; exact sum_congr rfl fun _ _ => mul_comm _ _
      _ ≤ (4 * (y : ℝ) / N) *
            (((I_y.card : ℝ) / m + 1) * (16 * (m : ℝ) * (Real.log m) ^ 2 / y)) :=
        mul_le_mul_of_nonneg_left hper_bound (by positivity)
      _ = 64 * (Real.log m) ^ 2 * (((I_y.card : ℝ) + m) / N) := by
        field_simp [hyR.ne', hmR.ne', hNR.ne']; ring
  have hIy_sub : (Icc 1 (m - 1)).biUnion (fun y => Ioc (N / (y + 1)) (N / y)) ⊆ Icc 1 N := by
    intro n hn
    obtain ⟨y, hyI, hny⟩ := mem_biUnion.mp hn
    obtain ⟨hy1, _⟩ := mem_Icc.mp hyI
    obtain ⟨hn_lo, hn_hi⟩ := mem_Ioc.mp hny
    have := Nat.zero_le (N / (y + 1))
    exact mem_Icc.mpr ⟨by omega, hn_hi.trans (Nat.div_le_self N y)⟩
  have hsum_cards : (∑ y ∈ Icc 1 (m - 1), ((Ioc (N / (y + 1)) (N / y)).card : ℝ)) ≤ N := by
    have hnat : (∑ y ∈ Icc 1 (m - 1), (Ioc (N / (y + 1)) (N / y)).card) ≤ N := by
      rw [← card_biUnion hdisj_y]
      exact (card_le_card hIy_sub).trans_eq (by rw [Nat.card_Icc, Nat.add_sub_cancel])
    exact_mod_cast hnat
  have hsum_m : (∑ _y ∈ Icc 1 (m - 1), (m : ℝ)) ≤ N := by
    rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    have hnat : (m - 1) * m ≤ N := (Nat.mul_le_mul_right m (Nat.sub_le m 1)).trans hmN_sq
    exact_mod_cast hnat
  have hpart2 : (∑ n ∈ Ioc (N / m) N,
      singlePrimeCorrection m (N / n) n ^ 2 / (n : ℝ)) ≤ 128 * (Real.log m) ^ 2 := by
    calc
      (∑ n ∈ Ioc (N / m) N, singlePrimeCorrection m (N / n) n ^ 2 / (n : ℝ)) ≤
          ∑ n ∈ (Icc 1 (m - 1)).biUnion (fun y => Ioc (N / (y + 1)) (N / y)),
            singlePrimeCorrection m (N / n) n ^ 2 / (n : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hcover_y fun _ _ _ => by positivity
      _ = ∑ y ∈ Icc 1 (m - 1), ∑ n ∈ Ioc (N / (y + 1)) (N / y),
            singlePrimeCorrection m (N / n) n ^ 2 / (n : ℝ) :=
        sum_biUnion hdisj_y
      _ ≤ ∑ y ∈ Icc 1 (m - 1), 64 * (Real.log m) ^ 2 *
            ((((Ioc (N / (y + 1)) (N / y)).card : ℝ) + m) / N) :=
        sum_le_sum hfor_y
      _ = (64 * (Real.log m) ^ 2 / N) *
            ((∑ y ∈ Icc 1 (m - 1), ((Ioc (N / (y + 1)) (N / y)).card : ℝ)) +
              ∑ _y ∈ Icc 1 (m - 1), (m : ℝ)) := by
        rw [← sum_add_distrib, mul_sum]
        exact sum_congr rfl fun _ _ => by ring
      _ ≤ (64 * (Real.log m) ^ 2 / N) * ((N : ℝ) + N) :=
        mul_le_mul_of_nonneg_left (add_le_add hsum_cards hsum_m) (by positivity)
      _ = 128 * (Real.log m) ^ 2 := by field_simp [hNR.ne']; ring
  rw [hunion, sum_union hdisj]
  linarith only [hpart1, hpart2]

/-- Uniform single-mode `renormalizedPrimeEnergy` discrepancy bound across all `2 ≤ m`
with `m * m ≤ N`:
`|renormalizedPrimeEnergy N v_m - E_arith(m) ‖v_m‖²| ≤ C_p1 * (1 + log m / √(log N))`. -/
private theorem exists_renormalizedPrimeEnergy_mode_sub_le :
    ∃ C_p1 : ℝ, 0 < C_p1 ∧
      ∀ {m N : ℕ}, 2 ≤ m → m * m ≤ N → 1 ≤ Real.log N →
        |renormalizedPrimeEnergy N (normalizedRamanujanHorizonVector m N) -
            ramanujanAdjunctionEnergy m * ‖normalizedRamanujanHorizonVector m N‖ ^ 2| ≤
          C_p1 * (1 + Real.log m / Real.sqrt (Real.log N)) := by
  obtain ⟨C_env, hC_env_pos, hC_env⟩ := exists_primeMertensRemainder_log_envelope
  let C_p1 := 5 * (8 * C_env + 25)
  refine ⟨C_p1, by dsimp only [C_p1]; positivity, ?_⟩
  intro m N hm hmN hlogN
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hlogN
  have hsL0 : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL0
  obtain ⟨hv_sq_le, hv_norm_le⟩ := normalizedRamanujanHorizonVector_norm_sq_le_nineteen hm hmN hlogN
  set v_m := normalizedRamanujanHorizonVector m N
  set res := Matrix.toEuclideanLin (fullPrimeMatrix N) v_m -
    (Real.log N - ramanujanAdjunctionEnergy m) • v_m
  have hid_inner :
      renormalizedPrimeEnergy N v_m - ramanujanAdjunctionEnergy m * ‖v_m‖ ^ 2 =
        -⟪res, v_m⟫ := by
    unfold renormalizedPrimeEnergy
    dsimp only [res]
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  -- Bound `‖res‖^2 ≤ 2 * C_env^2 * ‖v_m‖^2 + 384 * (log m)^2 / log N`.
  let e : ℕ → ℝ := fun y => mertensSum y - Real.log y + Real.eulerMascheroniConstant
  let r : ℕ → ℝ := fun n => Real.log N - Real.log ((N / n : ℕ) : ℝ) - Real.log n
  have hres_sq : ‖res‖ ^ 2 ≤ 38 * C_env ^ 2 + 384 * (Real.log m) ^ 2 / Real.log N := by
    have hcoord : ∀ idx : PrimeHorizonIndex N,
        res idx = (e (N / idx.1) - r idx.1) * primeHorizonExtension v_m idx.1 +
          (Real.sqrt (Real.log N))⁻¹ * (singlePrimeCorrection m (N / idx.1) idx.1 / Real.sqrt idx.1) := by
      intro idx
      obtain ⟨hn0, hnN⟩ := mem_Icc.mp idx.2
      change Matrix.toEuclideanLin (fullPrimeMatrix N) v_m idx -
        (Real.log N - ramanujanAdjunctionEnergy m) * v_m idx = _
      have hv_idx : v_m idx = (Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile m idx.1 := rfl
      have hlin : Matrix.toEuclideanLin (fullPrimeMatrix N) v_m idx =
          (Real.sqrt (Real.log N))⁻¹ *
            Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector m N) idx := by
        dsimp only [v_m, normalizedRamanujanHorizonVector]
        rw [map_smul]; rfl
      rw [hlin, hv_idx, fullPrimeMatrix_apply_ramanujanHorizonVector,
        primeHorizonExtension_coe v_m idx, hv_idx]
      have hcorr : ramanujanPrimeResidual m N idx.1 =
          ((e (N / idx.1) - r idx.1) * normalizedRamanujanMode m idx.1 +
            singlePrimeCorrection m (N / idx.1) idx.1) * poleVector idx.1 := by
        rw [ramanujanPrimeResidual, ramanujanPoleProfile_eq_mul_poleVector,
          sum_weilPrimeKernel_poleProfile_eq_correction (normalizedRamanujanMode m) hn0 hnN]
        dsimp only [e, r, singlePrimeCorrection, ramanujanAdjunctionEnergy]
        ring
      have hsub_eq : Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector m N) idx -
          (Real.log N - ramanujanAdjunctionEnergy m) * ramanujanPoleProfile m idx.1 =
          ramanujanPrimeResidual m N idx.1 := rfl
      have halg : (Real.sqrt (Real.log N))⁻¹ *
          Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector m N) idx -
          (Real.log N - ramanujanAdjunctionEnergy m) *
            ((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile m idx.1) =
          (Real.sqrt (Real.log N))⁻¹ * ramanujanPrimeResidual m N idx.1 := by
        rw [← hsub_eq]; ring
      rw [halg, hcorr, ramanujanPoleProfile_eq_mul_poleVector]
      unfold poleVector; ring
    have hnorm_sum : ‖res‖ ^ 2 = ∑ n ∈ Icc 1 N,
        ((e (N / n) - r n) * primeHorizonExtension v_m n +
          (Real.sqrt (Real.log N))⁻¹ * (singlePrimeCorrection m (N / n) n / Real.sqrt n)) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      trans ∑ idx : PrimeHorizonIndex N,
        ((e (N / idx.1) - r idx.1) * primeHorizonExtension v_m idx.1 +
          (Real.sqrt (Real.log N))⁻¹ * (singlePrimeCorrection m (N / idx.1) idx.1 / Real.sqrt idx.1)) ^ 2
      · exact sum_congr rfl fun idx _ => by rw [hcoord idx]
      · exact Finset.sum_coe_sort (Icc 1 N) _
    have hmert_sq : (∑ n ∈ Icc 1 N, ((e (N / n) - r n) * primeHorizonExtension v_m n) ^ 2) ≤
        19 * C_env ^ 2 := by
      have hpt : ∀ n ∈ Icc 1 N,
          ((e (N / n) - r n) * primeHorizonExtension v_m n) ^ 2 ≤
            C_env ^ 2 * primeHorizonExtension v_m n ^ 2 := by
        intro n hn
        obtain ⟨hn0, hnN⟩ := mem_Icc.mp hn
        have hy1 : 1 ≤ N / n := Nat.div_pos hnN hn0
        have hr_bd := roundoff_le hn0 hnN
        have her_abs : |e (N / n) - r n| ≤ C_env := by
          have h1 : |e (N / n) - r n| ≤ primeMertensRemainderProfile (N / n) := by
            unfold primeMertensRemainderProfile
            calc
              |e (N / n) - r n| ≤ |e (N / n)| + |r n| := abs_sub _ _
              _ ≤ |e (N / n)| + 1 / ((N / n : ℕ) : ℝ) := by
                rw [abs_of_nonneg hr_bd.1]; exact add_le_add le_rfl hr_bd.2
          have hden : 1 ≤ 1 + Real.log ((N / n : ℕ) : ℝ) := by
            have := Real.log_natCast_nonneg (N / n); linarith
          exact h1.trans ((hC_env (N / n) hy1).trans (div_le_self hC_env_pos.le hden))
        have her_sq : (e (N / n) - r n) ^ 2 ≤ C_env ^ 2 := by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) her_abs 2
        rw [mul_pow]; exact mul_le_mul_of_nonneg_right her_sq (sq_nonneg _)
      calc
        _ ≤ ∑ n ∈ Icc 1 N, C_env ^ 2 * primeHorizonExtension v_m n ^ 2 := sum_le_sum hpt
        _ = C_env ^ 2 * ‖v_m‖ ^ 2 := by rw [← mul_sum, sum_primeHorizonExtension_sq]
        _ ≤ C_env ^ 2 * 19 := mul_le_mul_of_nonneg_left hv_sq_le (sq_nonneg _)
        _ = 19 * C_env ^ 2 := by ring
    have htail_sq : (∑ n ∈ Icc 1 N,
        ((Real.sqrt (Real.log N))⁻¹ * (singlePrimeCorrection m (N / n) n / Real.sqrt n)) ^ 2) ≤
        192 * (Real.log m) ^ 2 / Real.log N := by
      have hpt : ∀ n ∈ Icc 1 N,
          ((Real.sqrt (Real.log N))⁻¹ * (singlePrimeCorrection m (N / n) n / Real.sqrt n)) ^ 2 =
            (Real.log N)⁻¹ * (singlePrimeCorrection m (N / n) n ^ 2 / (n : ℝ)) := fun n hn => by
        rw [mul_pow, inv_pow, div_pow, Real.sq_sqrt hL0.le, Real.sq_sqrt (Nat.cast_nonneg n)]
      rw [sum_congr rfl hpt, ← mul_sum]
      exact (mul_le_mul_of_nonneg_left (sum_singlePrimeCorrection_sq_div_le hm hmN)
        (inv_nonneg.mpr hL0.le)).trans_eq (div_eq_inv_mul _ _).symm
    have h2 : ∀ n ∈ Icc 1 N,
        ((e (N / n) - r n) * primeHorizonExtension v_m n +
          (Real.sqrt (Real.log N))⁻¹ * (singlePrimeCorrection m (N / n) n / Real.sqrt n)) ^ 2 ≤
          2 * ((e (N / n) - r n) * primeHorizonExtension v_m n) ^ 2 +
            2 * ((Real.sqrt (Real.log N))⁻¹ * (singlePrimeCorrection m (N / n) n / Real.sqrt n)) ^ 2 :=
      fun n _ => by nlinarith only [sq_nonneg ((e (N / n) - r n) * primeHorizonExtension v_m n -
        (Real.sqrt (Real.log N))⁻¹ * (singlePrimeCorrection m (N / n) n / Real.sqrt n))]
    rw [hnorm_sum]
    calc
      _ ≤ 2 * (∑ n ∈ Icc 1 N, ((e (N / n) - r n) * primeHorizonExtension v_m n) ^ 2) +
            2 * (∑ n ∈ Icc 1 N, ((Real.sqrt (Real.log N))⁻¹ *
              (singlePrimeCorrection m (N / n) n / Real.sqrt n)) ^ 2) := by
        refine (sum_le_sum h2).trans_eq ?_; simp only [sum_add_distrib, ← mul_sum]
      _ ≤ 2 * (19 * C_env ^ 2) + 2 * (192 * (Real.log m) ^ 2 / Real.log N) :=
        add_le_add (mul_le_mul_of_nonneg_left hmert_sq zero_le_two)
          (mul_le_mul_of_nonneg_left htail_sq zero_le_two)
      _ = 38 * C_env ^ 2 + 384 * (Real.log m) ^ 2 / Real.log N := by ring
  set X := Real.log m / Real.sqrt (Real.log N)
  have hX0 : 0 ≤ X := by have := Real.log_natCast_nonneg m; positivity
  have hres_norm : ‖res‖ ≤ (8 * C_env + 25) * (1 + X) := by
    have hX_sq : X ^ 2 = (Real.log m) ^ 2 / Real.log N := by
      dsimp only [X]; rw [div_pow, Real.sq_sqrt hL0.le]
    have hsq : ‖res‖ ^ 2 ≤ ((8 * C_env + 25) * (1 + X)) ^ 2 := by
      rw [← hX_sq] at hres_sq
      nlinarith only [hres_sq, hC_env_pos, hX0, sq_nonneg C_env, sq_nonneg X,
        mul_nonneg hC_env_pos.le hX0]
    nlinarith only [hsq, norm_nonneg res, hC_env_pos, hX0]
  rw [hid_inner, abs_neg]
  calc
    |⟪res, v_m⟫| ≤ ‖res‖ * ‖v_m‖ := abs_real_inner_le_norm _ _
    _ ≤ ((8 * C_env + 25) * (1 + X)) * 5 :=
      mul_le_mul hres_norm hv_norm_le (norm_nonneg _) (by positivity)
    _ = C_p1 * (1 + X) := by dsimp only [C_p1]; ring

/-! ## Section 4: Top-Band Single-Mode Overlap and Non-Ratio Bounds -/

private theorem mem_nearRowIndices_symm' {c : ℝ} {N n j : ℕ}
    (hn : n ∈ Icc 1 N) (hj : j ∈ nearRowIndices c N n) :
    n ∈ nearRowIndices c N j := by
  obtain ⟨_, hjn, hlog⟩ := mem_filter.mp hj
  exact mem_filter.mpr ⟨hn, Ne.symm hjn, by rwa [abs_sub_comm]⟩

private theorem log_two_mul_linearNearRowRadius_le' {c : ℝ} (hc1 : 1 ≤ c) :
    Real.log (2 * (linearNearRowRadius c + 1)) + 3 ≤ 10 * (1 + Real.log c) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have he2 : Real.exp 2 ≤ 8 := by
    have h1 : Real.exp 1 ≤ 14 / 5 := by linarith [Real.exp_one_lt_d9]
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith only [h1, h2, Real.exp_pos 1]
  have hlin : 2 * (linearNearRowRadius c + 1) ≤ 34 * c := by
    unfold linearNearRowRadius; nlinarith only [hc1, he2]
  have hlog34 : Real.log 34 ≤ 6 := by
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have he6 : (34 : ℝ) ≤ Real.exp 6 := by
      have hpow : (2 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 := pow_le_pow_left₀ (by norm_num) he1 6
      rw [← Real.exp_nat_mul] at hpow; norm_num at hpow; linarith only [hpow]
    exact (Real.log_le_log (by norm_num) he6).trans_eq (Real.log_exp 6)
  have hlog_le : Real.log (2 * (linearNearRowRadius c + 1)) ≤ 6 + Real.log c :=
    (Real.log_le_log (by unfold linearNearRowRadius; positivity) hlin).trans
      (by rw [Real.log_mul (by norm_num) hc0.ne']; linarith only [hlog34])
  linarith only [hlog_le, Real.log_nonneg hc1]

/-- Single-mode top-quotient `L²` tail bound via `sum_Ioc_packet_sq_le`, requiring no
Gram-inversion log condition on `m`. -/
private theorem sum_quotient_tail_mode_sq_le {m N : ℕ} {T : ℝ}
    (hm : 2 ≤ m) (hT1 : 1 ≤ T) (hRNT : ((m * m : ℕ) + 1 : ℝ) * T ≤ N)
    (hL0 : 0 < Real.log N) :
    Real.log N * (∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / n < T),
        primeHorizonExtension (normalizedRamanujanHorizonVector m N) n ^ 2) ≤
      Real.log (2 * T) + 3 := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  let K := ⌊(N : ℝ) / T⌋₊
  have hm2_le_div : ((m * m : ℕ) + 1 : ℝ) ≤ (N : ℝ) / T := (le_div_iff₀ hT0).mpr hRNT
  have hmK : m * m ≤ K := Nat.le_floor (by linarith only [hm2_le_div])
  have hK1 : 1 ≤ K := (Nat.mul_le_mul hm hm).trans hmK |>.trans' (by omega)
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hKN_R : (K : ℝ) ≤ N :=
    (Nat.floor_le (by positivity)).trans (div_le_self (Nat.cast_nonneg N) hT1)
  have hKN : K ≤ N := by exact_mod_cast hKN_R
  have hN0 : (0 : ℝ) < N := hK0.trans_le (by exact_mod_cast hKN)
  have hsub : (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / n < T) ⊆ Ioc K N := by
    intro n hn
    obtain ⟨hnI, hlt⟩ := mem_filter.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hnI).1
    have hNT_lt : (N : ℝ) / T < n := by
      have := (div_lt_iff₀ hn0).mp hlt
      exact (div_lt_iff₀ hT0).mpr (by linarith only [this])
    have hK_lt : K < n := by
      have hKR : (K : ℝ) < n := (Nat.floor_le (by positivity)).trans_lt hNT_lt
      exact_mod_cast hKR
    exact mem_Ioc.mpr ⟨hK_lt, (mem_Icc.mp hnI).2⟩
  let a : ℕ → ℝ := fun k => if k = m then 1 else 0
  have hval : ∀ n ∈ Ioc K N,
      Real.log N * primeHorizonExtension (normalizedRamanujanHorizonVector m N) n ^ 2 =
        (∑ k ∈ Icc 1 m, a k * ramanujanPoleProfile k n) ^ 2 := by
    intro n hn
    have hnI : n ∈ Icc 1 N := mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩
    have hsum_k : (∑ k ∈ Icc 1 m, a k * ramanujanPoleProfile k n) = ramanujanPoleProfile m n := by
      simp [a, show m ∈ Icc 1 m from mem_Icc.mpr ⟨by omega, le_rfl⟩]
    rw [hsum_k, primeHorizonExtension_coe _ ⟨n, hnI⟩]
    change Real.log N * (((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile m n) ^ 2) = _
    rw [mul_pow, inv_pow, Real.sq_sqrt hL0.le]
    field_simp [hL0.ne']
  have hpack := sum_Ioc_packet_sq_le hm hmK hKN a
  have ha_sq : (∑ k ∈ Icc 1 m, a k ^ 2) = 1 := by
    simp [a, show m ∈ Icc 1 m from mem_Icc.mpr ⟨by omega, le_rfl⟩]
  rw [ha_sq, mul_one] at hpack
  have hHN : (harmonic N : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
  have hHK : Real.log K ≤ (harmonic K : ℝ) :=
    (Real.log_le_log hK0 (by exact_mod_cast Nat.le_succ K)).trans (log_add_one_le_harmonic K)
  have hNT_ge2 : 2 ≤ (N : ℝ) / T := by
    have : (5 : ℝ) ≤ ((m * m : ℕ) + 1 : ℝ) := by
      have : 4 ≤ m * m := Nat.mul_le_mul hm hm
      exact_mod_cast (show 5 ≤ m * m + 1 by omega)
    linarith only [this, hm2_le_div]
  have hK_ge_half : (N : ℝ) / (2 * T) ≤ K := by
    have hsub1 := (Nat.sub_one_lt_floor ((N : ℝ) / T)).le
    have hhalf : (N : ℝ) / (2 * T) ≤ (N : ℝ) / T - 1 := by
      have : (N : ℝ) / (2 * T) = ((N : ℝ) / T) / 2 := by ring
      linarith only [this, hNT_ge2]
    exact hhalf.trans hsub1
  have hNK_le_2T : (N : ℝ) / K ≤ 2 * T := by
    rw [div_le_iff₀ hK0]
    have := (div_le_iff₀ (by positivity : 0 < 2 * T)).mp hK_ge_half
    linarith only [this]
  have hlog_NK : Real.log ((N : ℝ) / K) ≤ Real.log (2 * T) :=
    Real.log_le_log (div_pos hN0 hK0) hNK_le_2T
  calc
    Real.log N * (∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / n < T),
        primeHorizonExtension (normalizedRamanujanHorizonVector m N) n ^ 2) ≤
        Real.log N * (∑ n ∈ Ioc K N,
          primeHorizonExtension (normalizedRamanujanHorizonVector m N) n ^ 2) :=
      mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _) hL0.le
    _ = ∑ n ∈ Ioc K N,
          (∑ k ∈ Icc 1 m, a k * ramanujanPoleProfile k n) ^ 2 := by
      rw [mul_sum, sum_congr rfl hval]
    _ ≤ (harmonic N : ℝ) - harmonic K + 2 := hpack
    _ ≤ Real.log ((N : ℝ) / K) + 3 := by
      rw [Real.log_div hN0.ne' hK0.ne']; linarith only [hHN, hHK]
    _ ≤ Real.log (2 * T) + 3 := by linarith only [hlog_NK]

/-- Single-mode quadratic bound `|⟪overlapMatrix φ c N v_m, v_m⟫| ≤ C_ov1 * c * (1 + log c)`
across all `2 ≤ m` satisfying `((m * m : ℕ) + 1) * (linearNearRowRadius c + 1) ≤ N`. -/
private theorem exists_overlapMatrix_mode_inner_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C_ov1 : ℝ, 0 < C_ov1 ∧
      ∀ {m N : ℕ} {c : ℝ},
        2 ≤ m → 1 ≤ Real.log N → 1 ≤ c → c ≤ Real.log N → c / N ≤ 1 / 3 →
        ((m * m : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        |⟪Matrix.toEuclideanLin (overlapMatrix φ c N)
            (normalizedRamanujanHorizonVector m N),
          normalizedRamanujanHorizonVector m N⟫| ≤
          C_ov1 * c * (1 + Real.log c) := by
  obtain ⟨K_pair, hK_pair0, hpair⟩ := exists_abs_atomArchPair_near_sub_le hφ hsupp hM
  let M_ov : ℝ := K_pair + 2 + Real.exp (1 / 2)
  let C_ov1 : ℝ := 20 * (2 * Real.exp 2) * M_ov + 1
  refine ⟨C_ov1, by dsimp only [C_ov1, M_ov]; positivity, ?_⟩
  intro m N c hm hL1 hc1 hcL hw1 hRNT
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hw : c / N ≤ 1 := hw1.trans (by norm_num)
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL1
  have hN0 : (0 : ℝ) < N := by
    have : (0 : ℝ) < ((m * m : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) := by
      unfold linearNearRowRadius; positivity
    linarith only [this, hRNT]
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ ((m * m : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) := by
      have h1 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
      have h2 : (0 : ℝ) ≤ (m * m : ℕ) := by positivity
      nlinarith only [h1, h2]
    exact_mod_cast this.trans hRNT
  have hcN2 : 2 * c ≤ N := by have := (div_le_iff₀ hN0).mp hw1; linarith only [this, hc0]
  set v_m := normalizedRamanujanHorizonVector m N
  let g := atomDilate φ (c / N)
  let G0 := ∫ t, g t ^ 2
  let K_ov : ℕ → ℕ → ℝ := fun n j =>
    atomArchPair g n j / G0 + (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j
  let T := linearNearRowRadius c + 1
  have hT1 : 1 ≤ T := by
    have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
    dsimp only [T]; linarith only [h0]
  let vTop : ℕ → ℝ := fun n => if (N : ℝ) / n < T then primeHorizonExtension v_m n else 0
  have hinner_eq :
      ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v_m, v_m⟫ =
        ∑ n ∈ Icc 1 N, vTop n *
          ∑ j ∈ nearRowIndices c N n, K_ov n j * primeHorizonExtension v_m j := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ n : PrimeHorizonIndex N, v_m.ofLp n *
      ∑ j : PrimeHorizonIndex N, overlapMatrix φ c N n j * v_m.ofLp j) = _
    rw [← sum_coe_sort (Icc 1 N) (fun n => vTop n *
      ∑ j ∈ nearRowIndices c N n, K_ov n j * primeHorizonExtension v_m j)]
    refine sum_congr rfl fun n hn => ?_
    dsimp only [vTop]
    split_ifs with hlt
    · rw [primeHorizonExtension_coe v_m ⟨n, hn⟩]
      congr 1
      rw [nearRowIndices, sum_filter, ← sum_coe_sort (Icc 1 N)]
      refine sum_congr rfl fun j _ => ?_
      rw [primeHorizonExtension_coe v_m j]
      dsimp only [overlapMatrix, K_ov, g, G0]
      by_cases h : (j : ℕ) ≠ n ∧ |Real.log (j : ℕ) - Real.log (n : ℕ)| ≤ 2 * c / N
      · rw [if_pos ⟨Ne.symm h.1, by rw [← mul_div_assoc]; exact h.2⟩, if_pos h]
      · rw [if_neg fun h' => h ⟨Ne.symm h'.1, by rw [mul_div_assoc]; exact h'.2⟩, if_neg h, zero_mul]
    · rw [zero_mul]
      suffices hempty : ∀ j : PrimeHorizonIndex N, overlapMatrix φ c N ⟨n, hn⟩ j = 0 by
        simp [hempty]
      intro j
      dsimp only [overlapMatrix]
      split_ifs with hcond
      · exfalso
        have hjI : (j : ℕ) ∈ nearRowIndices c N n :=
          mem_filter.mpr ⟨j.2, Ne.symm hcond.1, by rw [← mul_div_assoc]; exact hcond.2⟩
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        have hgeom := (nearRow_geometry_small_width hc0 hn hjI hw).2.1
        exact hlt (by dsimp only [T]; linarith only [(div_le_iff₀ hn0).mpr hgeom])
      · rfl
  have hKov_le : ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n,
      |K_ov n j| ≤ M_ov * Real.log N := by
    intro n hn j hj
    have hw0 : 0 < c / N := div_pos hc0 hN0
    have hs : |Real.log j - Real.log n| ≤ 2 * (c / N) := by
      simpa only [mul_div_assoc] using (mem_filter.mp hj).2.2
    let q := shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ t, φ t ^ 2)
    have hrem : |atomArchPair g n j / G0 - Real.log (1 / (c / N)) * q| ≤ K_pair := by
      simpa only [g, G0, q, mul_div_assoc] using hpair (c / N) hw0 hw1 n j hs
    have hq : |q| ≤ 1 := by
      dsimp only [q]
      rw [abs_div, abs_of_pos hM, div_le_one hM]
      exact abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp) _
    have hlog_inv : |Real.log (1 / (c / N))| ≤ Real.log N := by
      have heq : Real.log (1 / (c / N)) = Real.log N - Real.log c := by
        rw [one_div, Real.log_inv, Real.log_div hc0.ne' hN0.ne']; ring
      rw [heq, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hc0 (by linarith only [hcN2, hc0])))]
      linarith [Real.log_nonneg hc1]
    have hnc : |(completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j| ≤
        (1 + Real.exp (1 / 2)) * Real.log N := by
      have h1 := abs_nearCenter_entry_le (φ := φ) (m := 1) zero_lt_one hN1 hcN2 hn hj
      have hm1 : ∀ k, normalizedRamanujanMode 1 k = 1 := fun k => by
        rw [normalizedRamanujanMode, ramanujanMode_one, Nat.totient_one, Nat.cast_one,
          Real.sqrt_one, div_one]
      rw [hm1 j, mul_one, range_one, sum_singleton, hm1 0, abs_one, mul_one,
        abs_of_nonneg (completeWeilPoleShift_nonneg φ hc0.le)] at h1
      have hpole := (completeWeilPoleShift_le hφ.continuous hsupp hM hc0.le).trans hcL
      exact h1.trans (by simpa only [mul_comm (Real.log N)] using
        mul_le_mul_of_nonneg_right hpole (by positivity))
    have hid : K_ov n j = (atomArchPair g n j / G0 - Real.log (1 / (c / N)) * q) +
        Real.log (1 / (c / N)) * q +
        (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j := by
      dsimp only [K_ov]; ring
    rw [hid]
    calc
      _ ≤ |atomArchPair g n j / G0 - Real.log (1 / (c / N)) * q| +
            |Real.log (1 / (c / N)) * q| +
            |(completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j| :=
        abs_add_three _ _ _
      _ ≤ K_pair + Real.log N * 1 + (1 + Real.exp (1 / 2)) * Real.log N := by
        rw [abs_mul]
        exact add_le_add (add_le_add hrem (mul_le_mul hlog_inv hq (abs_nonneg _) hL0.le)) hnc
      _ ≤ M_ov * Real.log N := by dsimp only [M_ov]; nlinarith only [hL1, hK_pair0]
  have hvTop_sq : (∑ n ∈ Icc 1 N, vTop n ^ 2) ≤ 10 * (1 + Real.log c) / Real.log N := by
    have hfilt : (∑ n ∈ Icc 1 N, vTop n ^ 2) =
        ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / n < T), primeHorizonExtension v_m n ^ 2 := by
      rw [sum_filter]; exact sum_congr rfl fun n _ => by dsimp only [vTop]; split_ifs <;> simp
    rw [hfilt, le_div_iff₀' hL0]
    exact (sum_quotient_tail_mode_sq_le hm hT1 hRNT hL0).trans
      (log_two_mul_linearNearRowRadius_le' hc1)
  -- Near-band Schur on `K_ov` restricted to `nearRowIndices c N n`.
  let K' : ℕ → ℕ → ℝ := fun n j => if j ∈ nearRowIndices c N n then K_ov n j else 0
  let U' : ℕ → ℕ → ℝ := fun n j => if j ∈ nearRowIndices c N n then M_ov * Real.log N else 0
  let B_row := 2 * linearNearRowRadius c * (M_ov * Real.log N)
  have hB_row0 : 0 ≤ B_row := by dsimp only [B_row, M_ov, linearNearRowRadius]; positivity
  have hrow_eq : ∀ n ∈ Icc 1 N,
      (∑ j ∈ nearRowIndices c N n, K_ov n j * primeHorizonExtension v_m j) =
        ∑ j ∈ Icc 1 N, K' n j * vTop j := by
    intro n hn
    have hsub : nearRowIndices c N n ⊆ Icc 1 N := filter_subset _ _
    rw [← sum_subset hsub]
    · refine sum_congr rfl fun j hj => ?_
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp (hsub hj)).1
      have hgeom := (nearRow_geometry_small_width hc0 hn hj hw).2.2
      have hlt : (N : ℝ) / j < T := by
        dsimp only [T]; linarith only [(div_le_iff₀ hj0).mpr hgeom]
      dsimp only [K', vTop]; rw [if_pos hj, if_pos hlt]
    · intro j _ hj; dsimp only [K']; rw [if_neg hj, zero_mul]
  have hU_row : ∀ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, U' n j * 1) ≤ B_row := by
    intro n hn
    have hsub : nearRowIndices c N n ⊆ Icc 1 N := filter_subset _ _
    have heq : (∑ j ∈ Icc 1 N, U' n j * 1) =
        ((nearRowIndices c N n).card : ℝ) * (M_ov * Real.log N) := by
      simp only [U', mul_one, ← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr hsub,
        sum_const, nsmul_eq_mul]
    rw [heq]
    exact mul_le_mul_of_nonneg_right (card_nearRowIndices_le_small_width hc0 hn hw)
      (by dsimp only [M_ov]; positivity)
  have hU_col : ∀ j ∈ Icc 1 N, (∑ n ∈ Icc 1 N, U' n j * (B_row / 1)) ≤ B_row ^ 2 := by
    intro j hj
    have hsym : ∀ n ∈ Icc 1 N, U' n j * (B_row / 1) = B_row * (U' j n * 1) := fun n hn => by
      dsimp only [U']
      by_cases hjn : j ∈ nearRowIndices c N n
      · rw [if_pos hjn, if_pos (mem_nearRowIndices_symm' hn hjn)]; ring
      · have hnj : n ∉ nearRowIndices c N j := fun h => hjn (mem_nearRowIndices_symm' hj h)
        rw [if_neg hjn, if_neg hnj]; ring
    rw [sum_congr rfl hsym, ← mul_sum, sq]
    exact mul_le_mul_of_nonneg_left (hU_row j hj) hB_row0
  have hschur := sum_sq_abs_majorized_kernel_le' K' U' vTop
    (fun _ => 1) (fun _ => B_row) (fun _ => B_row ^ 2)
    (fun _ _ _ _ => by dsimp only [U', M_ov]; split_ifs <;> positivity)
    (fun n hn j _ => by dsimp only [K', U']; split_ifs with hj; exact hKov_le n hn j hj; rw [abs_zero])
    (fun _ _ => zero_lt_one) hU_row hU_col
  have hrow_sq : (∑ n ∈ Icc 1 N,
      (∑ j ∈ nearRowIndices c N n, K_ov n j * primeHorizonExtension v_m j) ^ 2) ≤
      B_row ^ 2 * (10 * (1 + Real.log c) / Real.log N) := by
    rw [sum_congr rfl fun n hn => by rw [hrow_eq n hn]]
    calc
      (∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, K' n j * vTop j) ^ 2) ≤
          ∑ j ∈ Icc 1 N, B_row ^ 2 * vTop j ^ 2 := hschur
      _ = B_row ^ 2 * ∑ j ∈ Icc 1 N, vTop j ^ 2 := (mul_sum ..).symm
      _ ≤ B_row ^ 2 * (10 * (1 + Real.log c) / Real.log N) :=
        mul_le_mul_of_nonneg_left hvTop_sq (sq_nonneg _)
  rw [hinner_eq]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 N) vTop
    (fun n => ∑ j ∈ nearRowIndices c N n, K_ov n j * primeHorizonExtension v_m j)
  have hsq_le :
      (∑ n ∈ Icc 1 N, vTop n *
        ∑ j ∈ nearRowIndices c N n, K_ov n j * primeHorizonExtension v_m j) ^ 2 ≤
      (C_ov1 * c * (1 + Real.log c)) ^ 2 := by
    have hBrad : B_row = 4 * Real.exp 2 * c * M_ov * Real.log N := by
      dsimp only [B_row]; unfold linearNearRowRadius; ring
    have hC_ge : 20 * (2 * Real.exp 2) * M_ov ≤ C_ov1 := by dsimp only [C_ov1]; linarith
    calc
      _ ≤ (∑ n ∈ Icc 1 N, vTop n ^ 2) *
            (∑ n ∈ Icc 1 N, (∑ j ∈ nearRowIndices c N n,
              K_ov n j * primeHorizonExtension v_m j) ^ 2) := hcs
      _ ≤ (10 * (1 + Real.log c) / Real.log N) *
            (B_row ^ 2 * (10 * (1 + Real.log c) / Real.log N)) :=
        mul_le_mul hvTop_sq hrow_sq (sum_nonneg fun _ _ => sq_nonneg _)
          (by have := Real.log_nonneg hc1; positivity)
      _ = (20 * (2 * Real.exp 2) * M_ov * c * (1 + Real.log c)) ^ 2 := by
        rw [hBrad]; field_simp [hL0.ne']; ring
      _ ≤ (C_ov1 * c * (1 + Real.log c)) ^ 2 := by
        refine pow_le_pow_left₀ (by dsimp only [M_ov]; have := Real.log_nonneg hc1; positivity) ?_ 2
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC_ge hc0.le) (by linarith [Real.log_nonneg hc1])
  exact abs_le_of_sq_le_sq' hsq_le (by dsimp only [C_ov1, M_ov]; have := Real.log_nonneg hc1; positivity) |>.2

/-- Single-mode quadratic bound on `fullWeilNonRatioMatrix φ c N`:
`|⟪fullWeilNonRatioMatrix φ c N v_m, v_m⟫| ≤ 40 * √(log 4 + 4) * exp 3 * c`. -/
private theorem abs_fullWeilNonRatioMatrix_mode_inner_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) {m N : ℕ} (hm : 2 ≤ m) (hmN : m * m ≤ N)
    (hlogN : 1 ≤ Real.log N) {c : ℝ} (hc0 : 0 < c) (hcN : c ≤ N) :
    |⟪Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N)
        (normalizedRamanujanHorizonVector m N),
      normalizedRamanujanHorizonVector m N⟫| ≤
      40 * Real.sqrt (Real.log 4 + 4) * Real.exp 3 * c := by
  have hN1 : 1 ≤ N := (Nat.mul_le_mul hm hm).trans hmN |>.trans' (by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hlogN
  have hm_le_N : m ≤ N := (Nat.le_mul_self m).trans hmN
  obtain ⟨_, hv_norm⟩ := normalizedRamanujanHorizonVector_norm_sq_le_nineteen hm hmN hlogN
  set v_m := normalizedRamanujanHorizonVector m N
  -- Symmetry `⟪fullWeilNonRatioMatrix v_m, v_m⟫ = 2 * ⟪upwardPrimeVector v_m, v_m⟫`.
  have hsym_eq :
      ⟪Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) v_m, v_m⟫ =
        2 * ⟪upwardPrimeVector φ c N v_m, v_m⟫ := by
    rw [fullWeilNonRatioMatrix_eq_downward_add_upward hφ hsupp hM_int hc0 hN1 v_m,
      inner_add_left, ← upwardPrimeVector_self_inner_eq_downward hφ hsupp hc0 hN1 v_m]
    ring
  -- Bound `‖upwardPrimeVector φ c N v_m‖ ≤ 4 * √(log 4 + 4) * exp 3 * c`.
  let L₄ := Real.log 4 + 4
  have hL₄ : 0 < L₄ := by
    dsimp only [L₄]; have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
  let w := c / N
  have hw0 : 0 < w := div_pos hc0 hN0
  have hw1 : w ≤ 1 := (div_le_one hN0).mpr hcN
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts hφ hsupp hw0
  let g := atomDilate φ w
  have hG : 0 < ∫ u, g u ^ 2 := by
    dsimp only [g]; rw [integral_atomDilate_sq hw0]; exact mul_pos hw0 hM_int
  have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hgsupp
  have hew : Real.exp w - 1 ≤ w * Real.exp 1 :=
    exp_sub_one_le_mul_exp.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hw1) hw0.le)
  have hew_nonneg : 0 ≤ Real.exp w - 1 := by linarith [Real.add_one_le_exp w]
  let K_lag := SpacingScaleHarmonicAnalysis.lagRange (Real.log N + w + 1)
  let K_mat : ℕ → ℕ → ℝ := fun n j =>
    ∑ k ∈ range K_lag, _root_.RHTower.vonMangoldtAtom k *
      ((if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n))) /
        (∫ u, g u ^ 2))
  let U_mat : ℕ → ℕ → ℝ := fun n j =>
    ∑ k ∈ range K_lag, _root_.RHTower.vonMangoldtAtom k * upInd w k n j
  have hU_nonneg : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N, 0 ≤ U_mat n j :=
    fun _ _ _ _ => sum_nonneg fun k _ =>
      mul_nonneg (vonMangoldtAtom_nonneg' k) (upInd_nonneg w k _ _)
  have hKU : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N, |K_mat n j| ≤ U_mat n j := by
    intro n _ j _
    dsimp only [K_mat, U_mat]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
    rw [abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg' k)]
    refine mul_le_mul_of_nonneg_left ?_ (vonMangoldtAtom_nonneg' k)
    rw [abs_div, abs_of_pos hG, div_le_iff₀ hG]
    simpa only [mul_comm] using abs_nonRatio_term_le hg.continuous hgc hgsupp k n j
  let R_up := 2 * L₄ * Real.exp 3 * c
  have hR_up0 : 0 ≤ R_up := by dsimp only [R_up]; positivity
  have hrow_U : ∀ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, U_mat n j * (1 / Real.sqrt j)) ≤
      R_up / Real.sqrt n := by
    intro n hn
    have hn1 := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have heq : (∑ j ∈ Icc 1 N, U_mat n j * (1 / Real.sqrt j)) =
        (∑ k ∈ range K_lag, _root_.RHTower.vonMangoldtAtom k *
          ∑ j ∈ Icc 1 N, Real.sqrt ((n : ℝ) / j) * upInd w k n j) / Real.sqrt n := by
      dsimp only [U_mat]; simp_rw [sum_mul]; rw [sum_comm, sum_div]
      refine sum_congr rfl fun k _ => ?_
      simp_rw [mul_assoc]; rw [← mul_sum, mul_div_assoc]; congr 1; rw [sum_div]
      refine sum_congr rfl fun j hj => ?_
      have hsj : Real.sqrt j ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast (mem_Icc.mp hj).1)).ne'
      rw [Real.sqrt_div hn0.le]; field_simp [hsn.ne', hsj]
    rw [heq]
    refine div_le_div_of_nonneg_right ?_ hsn.le
    have hup := up_row_le (N := N) hw0.le hn1 K_lag
    have hexp32 : Real.exp (3 * w / 2) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith only [hw1])
    calc
      _ ≤ 2 * L₄ * Real.exp (3 * w / 2) * (Real.exp w - 1) * N := hup
      _ ≤ 2 * L₄ * Real.exp 2 * (w * Real.exp 1) * N :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (mul_le_mul_of_nonneg_left hexp32 (by positivity)) hew hew_nonneg
            (by positivity)) hN0.le
      _ = R_up := by
        dsimp only [R_up, w]
        rw [show Real.exp 3 = Real.exp 2 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
        field_simp [hN0.ne']
  have hcol_U : ∀ j ∈ Icc 1 N,
      (∑ n ∈ Icc 1 N, U_mat n j * ((R_up / Real.sqrt n) / (1 / Real.sqrt j))) ≤
        4 * R_up * Real.exp 2 * w * Real.log N * j := by
    intro j hj
    obtain ⟨hj1, hjN⟩ := mem_Icc.mp hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    have hsj : 0 < Real.sqrt j := Real.sqrt_pos.mpr hj0
    have heq : (∑ n ∈ Icc 1 N, U_mat n j * ((R_up / Real.sqrt n) / (1 / Real.sqrt j))) =
        R_up * ∑ k ∈ range K_lag, _root_.RHTower.vonMangoldtAtom k *
          ∑ n ∈ Icc 1 N, Real.sqrt ((j : ℝ) / n) * upInd w k n j := by
      dsimp only [U_mat]; simp_rw [sum_mul]; rw [sum_comm, mul_sum]
      refine sum_congr rfl fun k _ => ?_
      simp_rw [mul_assoc]; rw [← mul_sum, mul_left_comm R_up]; congr 1; rw [mul_sum]
      refine sum_congr rfl fun n hn => ?_
      have hsn : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast (mem_Icc.mp hn).1)).ne'
      rw [Real.sqrt_div hj0.le]; field_simp [hsn, hsj.ne']
    rw [heq]
    have hdown := down_row_le (N := N) hw0.le hj1 K_lag
    have hexp12 : Real.exp (w / 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith only [hw1])
    have hlogj : Real.log j + w ≤ 2 * Real.log N := by
      have h1 : Real.log j ≤ Real.log N := Real.log_le_log hj0 (by exact_mod_cast hjN)
      linarith only [h1, hw1, hlogN]
    have hdown_ub :
        2 * Real.exp (w / 2) * j * (Real.exp w - 1) * (Real.log j + w) ≤
          4 * Real.exp 2 * w * Real.log N * j := by
      calc
        _ ≤ 2 * Real.exp 1 * j * (w * Real.exp 1) * (2 * Real.log N) := by
          refine mul_le_mul ?_ hlogj (by linarith [Real.log_natCast_nonneg j]) (by positivity)
          refine mul_le_mul ?_ hew hew_nonneg (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp12 zero_le_two) hj0.le
        _ = 4 * Real.exp 2 * w * Real.log N * j := by
          rw [show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]; ring
    exact (mul_le_mul_of_nonneg_left (hdown.trans hdown_ub) hR_up0).trans_eq (by ring)
  have hup_norm_sq : ‖upwardPrimeVector φ c N v_m‖ ^ 2 ≤
      (4 * Real.sqrt L₄ * Real.exp 3 * c) ^ 2 := by
    have hrow_eq : ∀ n ∈ Icc 1 N,
        (upwardPrimeRow g N (primeHorizonExtension v_m) n / (∫ u, g u ^ 2)) ^ 2 =
        (∑ j ∈ Icc 1 N, K_mat n j * (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2 /
          Real.log N := by
      intro n hn
      have heq1 : upwardPrimeRow g N (primeHorizonExtension v_m) n / (∫ u, g u ^ 2) =
          (Real.sqrt (Real.log N))⁻¹ *
            ∑ j ∈ Icc 1 N, K_mat n j * (normalizedRamanujanMode m j / Real.sqrt j) := by
        rw [upwardPrimeRow_eq_sum hgsupp hw0.le hn, sum_div]
        dsimp only [K_mat]; simp_rw [sum_mul]
        rw [sum_comm (s := Icc 1 N) (t := range K_lag), mul_sum]
        refine sum_congr rfl fun k _ => ?_
        rw [mul_sum, mul_sum, sum_div]
        refine sum_congr rfl fun j hj => ?_
        rw [primeHorizonExtension, dif_pos hj]
        change (_root_.RHTower.vonMangoldtAtom k *
            (((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m j / Real.sqrt j)) *
              if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n)))) /
            (∫ u, g u ^ 2) = _
        ring
      rw [heq1, mul_pow, inv_pow, Real.sq_sqrt hL0.le, div_eq_inv_mul]
    have hvec_sq : ‖upwardPrimeVector φ c N v_m‖ ^ 2 =
        (∑ n ∈ Icc 1 N,
          (∑ j ∈ Icc 1 N, K_mat n j * (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2) /
          Real.log N := by
      rw [EuclideanSpace.real_norm_sq_eq]
      change (∑ n : PrimeHorizonIndex N,
        (upwardPrimeRow g N (primeHorizonExtension v_m) n / (∫ u, g u ^ 2)) ^ 2) = _
      refine (sum_coe_sort (Icc 1 N)
        (fun n => (upwardPrimeRow g N (primeHorizonExtension v_m) n /
          (∫ u, g u ^ 2)) ^ 2)).trans ?_
      rw [sum_congr rfl hrow_eq, ← sum_div]
    have hschur := sum_sq_abs_majorized_kernel_le (N := N) K_mat U_mat
      (fun j => normalizedRamanujanMode m j / Real.sqrt j)
      (fun j => 1 / Real.sqrt j)
      (fun n => R_up / Real.sqrt n)
      (fun j => 4 * R_up * Real.exp 2 * w * Real.log N * j)
      hU_nonneg hKU
      (fun j hj => one_div_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast (mem_Icc.mp hj).1)))
      hrow_U hcol_U
    have hmode_sum : (∑ j ∈ Icc 1 N,
        (4 * R_up * Real.exp 2 * w * Real.log N * j) *
          (normalizedRamanujanMode m j / Real.sqrt j) ^ 2) ≤
        8 * R_up * Real.exp 2 * c * Real.log N := by
      have h1 : (∑ j ∈ Icc 1 N,
          (4 * R_up * Real.exp 2 * w * Real.log N * j) *
            (normalizedRamanujanMode m j / Real.sqrt j) ^ 2) =
          (4 * R_up * Real.exp 2 * w * Real.log N * ((N : ℝ) * Real.log N)) *
            ∑ j ∈ Icc 1 N, ((j : ℝ) / N) * primeHorizonExtension v_m j ^ 2 := by
        rw [mul_sum]
        refine sum_congr rfl fun j hj => ?_
        have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
        rw [primeHorizonExtension_coe v_m ⟨j, hj⟩]
        change _ = (4 * R_up * Real.exp 2 * w * Real.log N * ((N : ℝ) * Real.log N)) *
          (((j : ℝ) / N) *
            (((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2))
        rw [mul_pow, inv_pow, div_pow, Real.sq_sqrt hL0.le, Real.sq_sqrt hj0.le]
        field_simp [hj0.ne', hN0.ne', hL0.ne']
      rw [h1]
      calc
        _ ≤ (4 * R_up * Real.exp 2 * w * Real.log N * ((N : ℝ) * Real.log N)) *
              (2 / Real.log N) :=
          mul_le_mul_of_nonneg_left (sum_linear_moment_mode_sq_le (by omega) hm_le_N hL0)
            (by positivity)
        _ = 8 * R_up * Real.exp 2 * c * Real.log N := by
          dsimp only [w]; field_simp [hN0.ne', hL0.ne']; ring
    have hexp56 : Real.exp 5 ≤ Real.exp 6 := Real.exp_le_exp.mpr (by norm_num)
    rw [hvec_sq]
    calc
      _ ≤ (8 * R_up * Real.exp 2 * c * Real.log N) / Real.log N :=
        div_le_div_of_nonneg_right (hschur.trans hmode_sum) hL0.le
      _ = 16 * L₄ * Real.exp 5 * c ^ 2 := by
        dsimp only [R_up]; field_simp [hL0.ne']
        rw [show Real.exp 3 * Real.exp 2 = Real.exp 5 by rw [← Real.exp_add]; norm_num]; ring
      _ ≤ 16 * L₄ * Real.exp 6 * c ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp56 (by positivity)) (sq_nonneg _)
      _ = (4 * Real.sqrt L₄ * Real.exp 3 * c) ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hL₄.le,
          show Real.exp 3 ^ 2 = Real.exp 6 by rw [sq, ← Real.exp_add]; norm_num]
        ring
  have hup_norm : ‖upwardPrimeVector φ c N v_m‖ ≤ 4 * Real.sqrt L₄ * Real.exp 3 * c := by
    have hrhs0 : 0 ≤ 4 * Real.sqrt L₄ * Real.exp 3 * c := by positivity
    nlinarith only [hup_norm_sq, norm_nonneg (upwardPrimeVector φ c N v_m), hrhs0]
  rw [hsym_eq, abs_mul, abs_of_pos zero_lt_two]
  calc
    2 * |⟪upwardPrimeVector φ c N v_m, v_m⟫| ≤
        2 * (‖upwardPrimeVector φ c N v_m‖ * ‖v_m‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) zero_le_two
    _ ≤ 2 * ((4 * Real.sqrt L₄ * Real.exp 3 * c) * 5) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hup_norm hv_norm (norm_nonneg _) (by positivity)) zero_le_two
    _ = 40 * Real.sqrt L₄ * Real.exp 3 * c := by ring

/-! ## Section 5: Diverging Single-Mode Positivity and Emptiness of Exceptional Conductors -/

private theorem log_le_rpow_div_pos {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) :
    Real.log x ≤ x ^ δ / δ := by
  rw [le_div_iff₀ hδ, mul_comm, Real.rpow_def_of_pos hx]
  exact (Real.lt_exp_self (δ * Real.log x)).le

/-- **Diverging positive single-mode floor above polylogarithmic scales.**
For every `C²` profile `φ` supported in `[0, 1]` with `0 < ∫ φ²`, every Bombieri–Vinogradov
exponent `0 < θ < 1 / 2`, every power-of-logarithm overlap exponent `0 < α < 1 / 4`, and every
`A > 8 * α`, eventually in `N`, for all `1 ≤ c ≤ (log N)^α` and all conductors
`m ∈ Icc ⌈(log N)^A⌉₊ ⌊N^θ⌋₊`:
```
((1 - 2 * θ) / 4) * log m ≤ completeWeilEnergy φ c N (normalizedRamanujanHorizonVector m N).
```
-/
theorem eventually_completeWeilEnergy_mode_ge_log_above_polylog {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) {θ α A : ℝ}
    (hθ0 : 0 < θ) (hθ : θ < 1 / 2) (hα0 : 0 < α) (hα : α < 1 / 4) (hA : 8 * α < A) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log N ^ α →
      ∀ m ∈ Icc ⌈Real.log N ^ A⌉₊ ⌊(N : ℝ) ^ θ⌋₊,
        ((1 - 2 * θ) / 4) * Real.log m ≤
          completeWeilEnergy φ c N (normalizedRamanujanHorizonVector m N) := by
  have hA0 : 0 < A := by linarith only [hα0, hA]
  have h1_2θ : 0 < 1 - 2 * θ := by linarith only [hθ]
  let δ := (1 - 2 * θ) / 10
  have hδ0 : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨C_p1, hCp1, hp1⟩ := exists_renormalizedPrimeEnergy_mode_sub_le
  obtain ⟨C_mid, hCmid, hmid⟩ := exists_overlapMatrix_midBand_inner_le hφ hsupp hM_int
  obtain ⟨C_od, hCod, hod⟩ := exists_overlap_sub_downward_norm_le_of_mem_conductorSubspace
    hφ hsupp hM_int
  obtain ⟨C_ov1, hCov1, hov1⟩ := exists_overlapMatrix_mode_inner_le hφ hsupp hM_int
  let K₀ := 152 * (∫ t, |φ t|) ^ 2 / (∫ t, φ t ^ 2)
  have hK₀ : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  let C_pole := |atomPoleMomentErrorConstant φ| + 1
  have hCpole : 0 < C_pole := by dsimp only [C_pole]; positivity
  let C_nr := 40 * Real.sqrt (Real.log 4 + 4) * Real.exp 3
  have hCnr : 0 < C_nr := by
    dsimp only [C_nr]
    have : 0 < Real.log 4 + 4 := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
    positivity
  -- Exponents for eventual decay as `N → ∞` and `log N → ∞`.
  let η_θ := (1 - 2 * θ) / 2
  have hη_θ : 0 < η_θ := by dsimp only [η_θ]; linarith only [hθ]
  let η_α := (1 / 4 - α) / 2
  have hη_α : 0 < η_α := by dsimp only [η_α]; linarith only [hα]
  let γ_A := A / 2 - 4 * α
  have hγ_A : 0 < γ_A := by dsimp only [γ_A]; linarith only [hA]
  let γ_od := 1 / 2 - 2 * α - η_α
  have hγ_od : 0 < γ_od := by dsimp only [γ_od, η_α]; linarith only [hα]
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  -- Thresholds on `log (log N)`, `log N`, and `N`.
  let LL_min := max 2 (max ((8 * (|completeWeilSelfFinitePart φ 1| + 1) + 2) / A)
    ((2 * C_p1 + 2) / (δ * A)))
  let L_pow1 : ℝ := (2 * C_p1 / δ + 1) ^ (2 : ℝ)
  let L_pow2 : ℝ := (200 / δ + 1) ^ (1 / (1 / 2 - α))
  let L_pow3 : ℝ := (684 * (K₀ + 1) / δ + 1) ^ (1 / (1 - 2 * α))
  let L_pow4 : ℝ := (1900 * (K₀ + 1) / δ + 25 * (2 * C_ov1 + C_nr) / δ + 1) ^ (1 / (1 - 2 * α))
  let L_pow5 : ℝ := (152 * C_mid / δ + 1) ^ (1 / (1 - 3 * α))
  let L_pow6 : ℝ := (152 * C_mid / δ + 1) ^ (1 / γ_A)
  let L_pow7 : ℝ := (640 * C_od * Real.sqrt (1 + 1 / (2 * η_α)) / δ + 1) ^ (1 / γ_od)
  let L_min := max 40 (max L_pow1 (max L_pow2 (max L_pow3 (max L_pow4 (max L_pow5 (max L_pow6 L_pow7))))))
  have hN_rpow_θ : Tendsto (fun N : ℕ => (N : ℝ) ^ η_θ) atTop atTop :=
    (tendsto_rpow_atTop hη_θ).comp tendsto_natCast_atTop_atTop
  have hN_rpow_20 : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 20 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp tendsto_natCast_atTop_atTop
  have hN_rpow_5 : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 5 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_conductorCutoff_bounds hθ0 hθ,
    hloglog.eventually_ge_atTop LL_min,
    hlog.eventually_ge_atTop L_min,
    (hlog.Eventually (eventually_gt_atTop 0)),
    ((tendsto_rpow_atTop hA0).comp hlog).eventually_ge_atTop 4,
    hN_rpow_θ.eventually_ge_atTop (68 / η_θ + 1),
    hN_rpow_20.eventually_ge_atTop 4,
    hN_rpow_5.eventually_ge_atTop
      (max (68 ^ 2 * 100 ^ 2 + 1)
        (max (2 * C_pole / δ + 1)
          (max (152 * C_mid * 10 ^ 6 / δ + 1)
            (320000 * C_od / δ + 1)))),
    eventually_ge_atTop 16]
    with N hcut hLL hL _hLpos hLA4 hNη hN20 hN5 hN16
  obtain ⟨_, hMθ_sq, _, hMθ_le, _⟩ := hcut
  have hN1 : 1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hN4 : 4 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL40 : 40 ≤ Real.log N := (le_max_left _ _).trans hL
  have hL1 : 1 ≤ Real.log N := by linarith only [hL40]
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL1
  have hsL0 : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL0
  have hLL2 : 2 ≤ Real.log (Real.log N) := (le_max_left _ _).trans hLL
  intro c hc1 hc_ub m hm_mem
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  obtain ⟨hm_lo, hm_hi⟩ := mem_Icc.mp hm_mem
  -- Basic conductor range facts: `4 ≤ m`, `m * m ≤ N`, `1 ≤ log m`.
  have hm_ge4 : 4 ≤ m := by
    have : 4 ≤ ⌈Real.log N ^ A⌉₊ := Nat.le_ceil.mp (by norm_num; exact hLA4)
    omega
  have hm2 : 2 ≤ m := by omega
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmN_sq : m * m ≤ N := (Nat.mul_le_mul hm_hi hm_hi).trans hMθ_sq
  have hm_le_N : m ≤ N := (Nat.le_mul_self m).trans hmN_sq
  have hmR_ge_LA : Real.log N ^ A ≤ m := (Nat.le_ceil _).trans (by exact_mod_cast hm_lo)
  have hlogm_ge : A * Real.log (Real.log N) ≤ Real.log m := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hL0 A) hmR_ge_LA
    rwa [Real.log_rpow hL0] at h
  have hlogm_ge1 : 1 ≤ Real.log m := by
    have hLA_ge4 : (4 : ℝ) ≤ m := by exact_mod_cast hm_ge4
    have hlog4 : 1 ≤ Real.log (4 : ℝ) := by
      have he : Real.exp 1 ≤ 4 := by linarith [Real.exp_one_lt_d9]
      exact (Real.log_exp 1).symm.trans_le (Real.log_le_log (Real.exp_pos 1) he)
    exact hlog4.trans (Real.log_le_log (by norm_num) hLA_ge4)
  have hlogm0 : 0 < Real.log m := zero_lt_one.trans_le hlogm_ge1
  -- Overlap upper bounds: `c ≤ log N`, `c / N ≤ 1 / 3`, `4 * (rad + 1)^2 ≤ N`, `((m^2 + 1) * (rad + 1)) ≤ N`.
  have hc_le_L : c ≤ Real.log N :=
    hc_ub.trans ((Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hα])).trans_eq
      (Real.rpow_one _))
  have hL_le_N5 : Real.log N ≤ 5 * (N : ℝ) ^ (1 / 5 : ℝ) := by
    simpa only [one_div, inv_inv] using log_le_rpow_div_pos hN0 (by norm_num : (0 : ℝ) < 1 / 5)
  have hrad_le : linearNearRowRadius c + 1 ≤ 17 * c := by
    have he2 : Real.exp 2 ≤ 8 := by
      have h1 : Real.exp 1 ≤ 14 / 5 := by linarith [Real.exp_one_lt_d9]
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith only [h1, h2, Real.exp_pos 1]
    unfold linearNearRowRadius; nlinarith only [hc1, he2]
  have hrad_N : 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N := by
    have h1 : 2 * (linearNearRowRadius c + 1) ≤ 34 * Real.log N := by linarith only [hrad_le, hc_le_L]
    have h2 : 34 * Real.log N ≤ 170 * (N : ℝ) ^ (1 / 5 : ℝ) := by linarith only [hL_le_N5]
    have h3 : (170 * (N : ℝ) ^ (1 / 5 : ℝ)) ^ 2 ≤ N := by
      have hN5_1 : (68 ^ 2 * 100 ^ 2 + 1 : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ) :=
        (le_max_left _ _).trans hN5
      have hp : ((N : ℝ) ^ (1 / 5 : ℝ)) ^ 2 * (N : ℝ) ^ (1 / 5 : ℝ) ≤ N := by
        have hsum : (N : ℝ) ^ (1 / 5 : ℝ) * (N : ℝ) ^ (1 / 5 : ℝ) * (N : ℝ) ^ (1 / 5 : ℝ) =
            (N : ℝ) ^ (3 / 5 : ℝ) := by
          rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; norm_num
        rw [sq, hsum]
        exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by norm_num : (3 / 5 : ℝ) ≤ 1)).trans_eq
          (Real.rpow_one _)
      have h170 : (170 : ℝ) ^ 2 ≤ 68 ^ 2 * 100 ^ 2 := by norm_num
      nlinarith only [hN5_1, hp, h170, sq_nonneg ((N : ℝ) ^ (1 / 5 : ℝ))]
    have h0 : 0 ≤ 2 * (linearNearRowRadius c + 1) := by unfold linearNearRowRadius; positivity
    have hsq := pow_le_pow_left₀ h0 (h1.trans h2) 2
    nlinarith only [hsq, h3]
  have hw3 : c / N ≤ 1 / 3 := by
    rw [div_le_iff₀ hN0]
    have hrad0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
    have hc_le_rad : 2 * c ≤ linearNearRowRadius c + 1 := by
      have he2 : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
      unfold linearNearRowRadius; nlinarith only [hc1, he2]
    nlinarith only [hrad_N, hc_le_rad, hrad0, hc1]
  have hcN : c ≤ N := by have := (div_le_iff₀ hN0).mp hw3; linarith only [this, hc0]
  have hRNT_m : ((m * m : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N := by
    have hmR_θ : (m : ℝ) ≤ (N : ℝ) ^ θ := (by exact_mod_cast hm_hi : (m : ℝ) ≤ ⌊(N : ℝ) ^ θ⌋₊).trans hMθ_le
    have hm2_2θ : ((m * m : ℕ) + 1 : ℝ) ≤ 2 * (N : ℝ) ^ (2 * θ) := by
      have h1 : ((m * m : ℕ) : ℝ) ≤ (N : ℝ) ^ (2 * θ) := by
        push_cast
        calc
          (m : ℝ) * m ≤ (N : ℝ) ^ θ * (N : ℝ) ^ θ := mul_le_mul hmR_θ hmR_θ hm0.le (by positivity)
          _ = (N : ℝ) ^ (2 * θ) := by rw [← Real.rpow_add hN0]; ring_nf
      have hge1 : 1 ≤ (N : ℝ) ^ (2 * θ) :=
        Real.one_le_rpow (by exact_mod_cast hN1) (by positivity)
      linarith only [h1, hge1]
    have hL_η : Real.log N ≤ (N : ℝ) ^ η_θ / η_θ := log_le_rpow_div_pos hN0 hη_θ
    have hrad_η : linearNearRowRadius c + 1 ≤ (17 / η_θ) * (N : ℝ) ^ η_θ := by
      calc
        linearNearRowRadius c + 1 ≤ 17 * Real.log N := by linarith only [hrad_le, hc_le_L]
        _ ≤ 17 * ((N : ℝ) ^ η_θ / η_θ) := mul_le_mul_of_nonneg_left hL_η (by norm_num)
        _ = (17 / η_θ) * (N : ℝ) ^ η_θ := by ring
    have hprod_eq : (N : ℝ) ^ (2 * θ) * (N : ℝ) ^ η_θ * (N : ℝ) ^ η_θ = N := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
      have hexp : 2 * θ + η_θ + η_θ = 1 := by dsimp only [η_θ]; ring
      rw [hexp, Real.rpow_one]
    calc
      ((m * m : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤
          (2 * (N : ℝ) ^ (2 * θ)) * ((17 / η_θ) * (N : ℝ) ^ η_θ) :=
        mul_le_mul hm2_2θ hrad_η (by unfold linearNearRowRadius; positivity) (by positivity)
      _ = (34 / η_θ) * ((N : ℝ) ^ (2 * θ) * (N : ℝ) ^ η_θ) := by ring
      _ ≤ (N : ℝ) ^ η_θ * ((N : ℝ) ^ (2 * θ) * (N : ℝ) ^ η_θ) :=
        mul_le_mul_of_nonneg_right (by linarith only [hNη]) (by positivity)
      _ = N := by rw [← hprod_eq]; ring
  set v_m := normalizedRamanujanHorizonVector m N
  obtain ⟨hv_sq_le, hv_norm_le⟩ := normalizedRamanujanHorizonVector_norm_sq_le_nineteen hm2 hmN_sq hL1
  have hv_sq_ge : 1 - 2 * θ ≤ ‖v_m‖ ^ 2 :=
    normalizedRamanujanHorizonVector_norm_sq_ge (mem_Icc.mpr ⟨hm1, hm_hi⟩) hN4 hMθ_le
  -- Exact decomposition of `completeWeilEnergy φ c N v_m`.
  have hdecomp := completeWeilMatrix_inner_eq_decomposition_at_every_overlap
    hφ hsupp hM_int hc0 hN1 v_m
  -- Step 1: Main positive scalar term `≥ (3 / 4) * (1 - 2 * θ) * log m`.
  have hmain_lb :
      (3 / 4) * (1 - 2 * θ) * Real.log m ≤
        ramanujanAdjunctionEnergy m * ‖v_m‖ ^ 2 +
          (completeWeilSelfFinitePart φ c - Real.eulerMascheroniConstant +
            completeWeilSelfError φ c N) * ‖v_m‖ ^ 2 := by
    have hself_eq := completeWeilSelfFinitePart_eq_at_one_sub_log φ hc0
    have hself_err : |completeWeilSelfError φ c N| ≤ 1 := by
      have h1 := abs_completeWeilSelfError_le_of_width_le_one hφ hsupp hM_int hc0 hN1 hcN
      have he12 : Real.exp (1 / 2) ≤ 3 :=
        (Real.exp_le_exp.mpr (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans
          (by linarith [Real.exp_one_lt_d9])
      calc
        |completeWeilSelfError φ c N| ≤ Real.exp (1 / 2) / 2 * (c / N) := h1
        _ ≤ (3 / 2) * (1 / 3) :=
          mul_le_mul (by linarith only [he12]) hw3 (by positivity) (by norm_num)
        _ ≤ 1 := by norm_num
    have hlogc_le : Real.log c ≤ (1 / 8) * Real.log m := by
      have h1 : Real.log c ≤ α * Real.log (Real.log N) :=
        (Real.log_le_log hc0 hc_ub).trans_eq (Real.log_rpow hL0)
      have h2 : α * Real.log (Real.log N) ≤ (A / 8) * Real.log (Real.log N) :=
        mul_le_mul_of_nonneg_right (by linarith only [hA]) (by linarith only [hLL2])
      nlinarith only [h1, h2, hlogm_ge]
    have hconst_le : |completeWeilSelfFinitePart φ 1| + 1 ≤ (1 / 8) * Real.log m := by
      have hLL_r : (8 * (|completeWeilSelfFinitePart φ 1| + 1) + 2) / A ≤
          Real.log (Real.log N) := (le_max_left _ _).trans ((le_max_right _ _).trans hLL)
      have hmul := (div_le_iff₀ hA0).mp hLL_r
      linarith only [hmul, hlogm_ge]
    have hscalar_lb : (3 / 4) * Real.log m ≤
        ramanujanAdjunctionEnergy m + completeWeilSelfFinitePart φ c -
          Real.eulerMascheroniConstant + completeWeilSelfError φ c N := by
      rw [hself_eq]
      have hadj := log_le_ramanujanAdjunctionEnergy_sub m
      have herr_lb := (abs_le.mp hself_err).1
      have hfin_lb := neg_abs_le (completeWeilSelfFinitePart φ 1)
      linarith only [hadj, herr_lb, hfin_lb, hlogc_le, hconst_le]
    calc
      (3 / 4) * (1 - 2 * θ) * Real.log m = ((3 / 4) * Real.log m) * (1 - 2 * θ) := by ring
      _ ≤ (ramanujanAdjunctionEnergy m + completeWeilSelfFinitePart φ c -
            Real.eulerMascheroniConstant + completeWeilSelfError φ c N) * ‖v_m‖ ^ 2 :=
        mul_le_mul hscalar_lb hv_sq_ge (by positivity) (by positivity)
      _ = _ := by ring
  -- Step 2: Error 1 (`renormalizedPrimeEnergy` discrepancy) `≤ δ * log m`.
  have herr_prime :
      |renormalizedPrimeEnergy N v_m - ramanujanAdjunctionEnergy m * ‖v_m‖ ^ 2| ≤
        δ * Real.log m := by
    have hb := hp1 hm2 hmN_sq hL1
    have h1 : C_p1 ≤ (δ / 2) * Real.log m := by
      have hLL_r : (2 * C_p1 + 2) / (δ * A) ≤ Real.log (Real.log N) :=
        (le_max_right _ _).trans ((le_max_right _ _).trans hLL)
      have hmul := (div_le_iff₀ (mul_pos hδ0 hA0)).mp hLL_r
      have hδm := mul_le_mul_of_nonneg_left hlogm_ge hδ0.le
      nlinarith only [hmul, hδm]
    have h2 : C_p1 / Real.sqrt (Real.log N) ≤ δ / 2 := by
      have hL_r : L_pow1 ≤ Real.log N := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
      have hsq : (2 * C_p1 / δ + 1) ^ 2 ≤ Real.log N := by
        simpa only [L_pow1, Real.rpow_two] using hL_r
      have hs : 2 * C_p1 / δ + 1 ≤ Real.sqrt (Real.log N) := by
        have h0 : 0 ≤ 2 * C_p1 / δ + 1 := by positivity
        nlinarith only [hsq, Real.sq_sqrt hL0.le, hsL0, h0]
      rw [div_le_iff₀ hsL0]
      have hmul := (div_le_iff₀ hδ0).mp (by linarith only [hs] : 2 * C_p1 / δ ≤ Real.sqrt (Real.log N))
      linarith only [hmul]
    calc
      _ ≤ C_p1 + (C_p1 / Real.sqrt (Real.log N)) * Real.log m := by
        linarith only [hb, (by ring : C_p1 * (1 + Real.log m / Real.sqrt (Real.log N)) =
          C_p1 + (C_p1 / Real.sqrt (Real.log N)) * Real.log m)]
      _ ≤ (δ / 2) * Real.log m + (δ / 2) * Real.log m :=
        add_le_add h1 (mul_le_mul_of_nonneg_right h2 hlogm0.le)
      _ = δ * Real.log m := by ring
  -- Helper for `rpow` decay `x ^ β ≤ (1 / B)` when `x ≥ B ^ (1 / (-β))`.
  have hrpow_inv_le : ∀ {B γ : ℝ}, 0 < B → 0 < γ →
      (B + 1) ^ (1 / γ) ≤ Real.log N → Real.log N ^ (-γ) ≤ 1 / B := by
    intro B γ hB hγ hL_ge
    have h1 : B + 1 ≤ Real.log N ^ γ := by
      have hp := Real.rpow_le_rpow (by positivity) hL_ge hγ.le
      rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hγ.ne', Real.rpow_one] at hp
    rw [Real.rpow_neg hL0.le, inv_eq_one_div]
    exact one_div_le_one_div_of_le hB (by linarith only [h1])
  -- Step 3: Error 2 (`fullWeilCenterMatrix`) `≤ δ * log m`.
  have herr_center :
      |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N) v_m, v_m⟫| ≤
        δ * Real.log m := by
    have hb := abs_fullWeilCenterMatrix_mode_inner_le (completeWeilPoleShift φ c) hm2 hmN_sq hL1
    have hpole_le : |completeWeilPoleShift φ c| ≤ c := by
      rw [abs_of_nonneg (completeWeilPoleShift_nonneg φ hc0.le)]
      exact completeWeilPoleShift_le hφ.continuous hsupp hM_int hc0.le
    have h1m_le : 1 + Real.log m ≤ 2 * Real.log m := by linarith only [hlogm_ge1]
    have hc_sqrt : c / Real.sqrt (Real.log N) ≤ δ / 200 := by
      have hL_r : L_pow2 ≤ Real.log N :=
        (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
      have hdec := hrpow_inv_le (B := 200 / δ) (γ := 1 / 2 - α) (by positivity)
        (by linarith only [hα]) hL_r
      have h1 : c / Real.sqrt (Real.log N) ≤ Real.log N ^ (-(1 / 2 - α)) := by
        rw [Real.sqrt_eq_rpow, show -(1 / 2 - α) = α - 1 / 2 by ring, Real.rpow_sub hL0]
        exact div_le_div_of_nonneg_right hc_ub (by positivity)
      exact h1.trans (hdec.trans_eq (by field_simp [hδ0.ne']))
    calc
      _ ≤ 100 * |completeWeilPoleShift φ c| * (1 + Real.log m) / Real.sqrt (Real.log N) := hb
      _ = 100 * (|completeWeilPoleShift φ c| / Real.sqrt (Real.log N)) * (1 + Real.log m) := by ring
      _ ≤ 100 * (c / Real.sqrt (Real.log N)) * (2 * Real.log m) :=
        mul_le_mul (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hpole_le hsL0.le) (by norm_num)) h1m_le
          (by positivity) (by positivity)
      _ = 200 * (c / Real.sqrt (Real.log N)) * Real.log m := by ring
      _ ≤ 200 * (δ / 200) * Real.log m :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc_sqrt (by norm_num)) hlogm0.le
      _ = δ * Real.log m := by ring
  -- Step 4: Error 3 (`fullWeilPoleErrorMatrix`) `≤ δ * log m`.
  have herr_pole :
      |⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) v_m, v_m⟫| ≤ δ * Real.log m := by
    have hb := abs_fullWeilPoleErrorMatrix_mode_inner_le hφ hsupp hM_int hc0 hm2 hmN_sq hcN
    have hC_le : atomPoleMomentErrorConstant φ ≤ C_pole := by
      dsimp only [C_pole]; linarith [le_abs_self (atomPoleMomentErrorConstant φ)]
    have hc2_div : c ^ 2 / ((N : ℝ) * Real.log N) ≤ 1 / (N : ℝ) ^ (1 / 5 : ℝ) := by
      have hc2_L : c ^ 2 ≤ Real.log N := by
        calc
          c ^ 2 ≤ (Real.log N ^ α) ^ 2 := pow_le_pow_left₀ hc0.le hc_ub 2
          _ = Real.log N ^ (2 * α) := by
            rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hL0.le]; norm_num
          _ ≤ Real.log N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hα])
          _ = Real.log N := Real.rpow_one _
      have hN15 : (N : ℝ) ^ (1 / 5 : ℝ) ≤ N :=
        (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by norm_num)).trans_eq
          (Real.rpow_one _)
      calc
        c ^ 2 / ((N : ℝ) * Real.log N) ≤ Real.log N / ((N : ℝ) * Real.log N) :=
          div_le_div_of_nonneg_right hc2_L (by positivity)
        _ = 1 / (N : ℝ) := by field_simp [hN0.ne', hL0.ne']
        _ ≤ 1 / (N : ℝ) ^ (1 / 5 : ℝ) := one_div_le_one_div_of_le (by positivity) hN15
    have hN5_pole : 2 * C_pole / δ + 1 ≤ (N : ℝ) ^ (1 / 5 : ℝ) :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hN5)
    have hsmall : 2 * C_pole * (1 / (N : ℝ) ^ (1 / 5 : ℝ)) ≤ δ := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      have := (div_le_iff₀ hδ0).mp (by linarith only [hN5_pole] : 2 * C_pole / δ ≤ (N : ℝ) ^ (1 / 5 : ℝ))
      linarith only [this]
    calc
      _ ≤ 2 * atomPoleMomentErrorConstant φ * (c ^ 2 / ((N : ℝ) * Real.log N)) := by
        linarith only [hb, (by ring :
          2 * atomPoleMomentErrorConstant φ * c ^ 2 / ((N : ℝ) * Real.log N) =
          2 * atomPoleMomentErrorConstant φ * (c ^ 2 / ((N : ℝ) * Real.log N)))]
      _ ≤ 2 * C_pole * (1 / (N : ℝ) ^ (1 / 5 : ℝ)) :=
        mul_le_mul (by linarith only [hC_le]) hc2_div (by positivity) (by positivity)
      _ ≤ δ := hsmall
      _ ≤ δ * Real.log m := le_mul_of_one_le_right hδ0.le hlogm_ge1
  -- Shared `c^2 ≤ log N ^ (2 α)` helper.
  have hc2_ub : c ^ 2 ≤ Real.log N ^ (2 * α) := by
    calc
      c ^ 2 ≤ (Real.log N ^ α) ^ 2 := pow_le_pow_left₀ hc0.le hc_ub 2
      _ = Real.log N ^ (2 * α) := by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hL0.le]; norm_num
  -- Split `m ≤ ⌊N^(1/20)⌋₊` vs `⌊N^(1/20)⌋₊ < m` for `separatedCross` and `overlap - nonRatio`.
  have herr_sep_and_ov :
      |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) v_m, v_m⟫| ≤ δ * Real.log m ∧
        |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v_m, v_m⟫ -
          ⟪Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) v_m, v_m⟫| ≤ δ * Real.log m := by
    by_cases hm_low : m ≤ ⌊(N : ℝ) ^ (1 / 20 : ℝ)⌋₊
    · -- Regime I (`m ≤ ⌊N^(1/20)⌋₊`): `m^6 ≤ N`, `18 * (1 + log m) ≤ log N`.
      have hmR_20 : (m : ℝ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) :=
        (by exact_mod_cast hm_low : (m : ℝ) ≤ ⌊(N : ℝ) ^ (1 / 20 : ℝ)⌋₊).trans
          (Nat.floor_le (by positivity))
      have hm6N : m ^ 6 ≤ N := by
        have hR : ((m ^ 6 : ℕ) : ℝ) ≤ N := by
          push_cast
          calc
            (m : ℝ) ^ 6 ≤ ((N : ℝ) ^ (1 / 20 : ℝ)) ^ 6 := pow_le_pow_left₀ hm0.le hmR_20 6
            _ = (N : ℝ) ^ (6 / 20 : ℝ) := by
              rw [← Real.rpow_natCast _ 6, ← Real.rpow_mul hN0.le]; norm_num
            _ ≤ (N : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by norm_num)
            _ = N := Real.rpow_one _
        exact_mod_cast hR
      have hm4N : m ^ 4 ≤ N :=
        (Nat.pow_le_pow_right (by omega) (by norm_num : 4 ≤ 6)).trans hm6N
      have hlog18 : 18 * (1 + Real.log m) ≤ Real.log N := by
        have hlm : Real.log m ≤ (1 / 20) * Real.log N :=
          (Real.log_le_log hm0 hmR_20).trans_eq (Real.log_rpow hN0)
        linarith only [hlm, hL40]
      have hv_mem : v_m ∈ conductorSubspace m N :=
        mem_conductorSubspace_normalizedRamanujanHorizonVector (mem_Icc.mpr ⟨hm1, le_rfl⟩)
      -- Regime I `separatedCrossErrorMatrix` bound:
      have hsep_I :
          |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) v_m, v_m⟫| ≤ δ * Real.log m := by
        have hb := abs_separatedCrossErrorMatrix_inner_le_of_mem_conductorSubspace
          hφ hsupp hM_int hc0 hm2 hm4N hlog18 hv_mem
        have hL_r : L_pow3 ≤ Real.log N :=
          (le_max_left _ _).trans ((le_max_right _ _).trans
            ((le_max_right _ _).trans ((le_max_right _ _).trans hL)))
        have hdec := hrpow_inv_le (B := 684 * (K₀ + 1) / δ) (γ := 1 - 2 * α)
          (by positivity) (by linarith only [hα]) hL_r
        have hc2_div : c ^ 2 / Real.log N ≤ Real.log N ^ (-(1 - 2 * α)) := by
          rw [show -(1 - 2 * α) = 2 * α - 1 by ring, Real.rpow_sub hL0, Real.rpow_one]
          exact div_le_div_of_nonneg_right hc2_ub hL0.le
        calc
          _ ≤ 36 * K₀ * c ^ 2 / Real.log N * 19 :=
            hb.trans (mul_le_mul_of_nonneg_left hv_sq_le (by positivity))
          _ ≤ 684 * (K₀ + 1) * (c ^ 2 / Real.log N) := by
            nlinarith only [hK₀, (show 0 ≤ c ^ 2 / Real.log N by positivity)]
          _ ≤ 684 * (K₀ + 1) * (1 / (684 * (K₀ + 1) / δ)) :=
            mul_le_mul_of_nonneg_left (hc2_div.trans hdec) (by positivity)
          _ = δ := by field_simp [(show 684 * (K₀ + 1) ≠ 0 by positivity), hδ0.ne']
          _ ≤ δ * Real.log m := le_mul_of_one_le_right hδ0.le hlogm_ge1
      -- Regime I `overlapMatrix - fullWeilNonRatioMatrix` via `overlap_sub_nonRatio_inner_eq`:
      have hov_I :
          |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v_m, v_m⟫ -
            ⟪Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) v_m, v_m⟫| ≤ δ * Real.log m := by
        rw [overlap_sub_nonRatio_inner_eq hφ hsupp hM_int hc0 hN1 v_m]
        -- 1) `|⟪overlapMatrix v_m, v_m⟫| ≤ δ / 2` via `exists_overlapMatrix_midBand_inner_le` at `Q₁ = m - 1`, `R₂ = m`.
        let a_m : ℕ → ℝ := fun k => if k = m then 1 else 0
        have hu_eq : (∑ k ∈ Icc 1 m, a_m k • normalizedRamanujanHorizonVector k N) = v_m := by
          simp [a_m, v_m, show m ∈ Icc 1 m from mem_Icc.mpr ⟨hm1, le_rfl⟩]
        have ha0 : ∀ k ∈ Icc 1 (m - 1), a_m k = 0 := fun k hk => by
          have := (mem_Icc.mp hk).2; simp [a_m, show k ≠ m by omega]
        have hmid_b := hmid (Q₁ := m - 1) (R₂ := m) (by omega) (by omega) hmN_sq hlog18
          hc1 hc_le_L hw3 hrad_N hRNT_m ha0
        dsimp only at hmid_b
        rw [hu_eq] at hmid_b
        -- Bound the four summands inside `hmid_b` each by `δ / (152 * C_mid)`.
        let η_mid := δ / (152 * C_mid)
        have hη_mid : 0 < η_mid := by dsimp only [η_mid]; positivity
        have ht1 : c ^ 2 * (1 + Real.log c) / Real.log N ≤ 2 * η_mid := by
          have h1c : 1 + Real.log c ≤ 2 * c := by
            have := Real.log_le_sub_one_of_pos hc0; linarith only [this, hc1]
          have hc3 : c ^ 2 * (1 + Real.log c) / Real.log N ≤ 2 * Real.log N ^ (-(1 - 3 * α)) := by
            have hc3_ub : c ^ 3 ≤ Real.log N ^ (3 * α) := by
              calc
                c ^ 3 ≤ (Real.log N ^ α) ^ 3 := pow_le_pow_left₀ hc0.le hc_ub 3
                _ = Real.log N ^ (3 * α) := by
                  rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul hL0.le]; norm_num
            calc
              c ^ 2 * (1 + Real.log c) / Real.log N ≤ 2 * c ^ 3 / Real.log N :=
                div_le_div_of_nonneg_right
                  (by nlinarith only [h1c, sq_nonneg c]) hL0.le
              _ = 2 * (c ^ 3 / Real.log N) := by ring
              _ ≤ 2 * (Real.log N ^ (3 * α) / Real.log N) :=
                mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hc3_ub hL0.le) zero_le_two
              _ = 2 * Real.log N ^ (-(1 - 3 * α)) := by
                rw [show -(1 - 3 * α) = 3 * α - 1 by ring, Real.rpow_sub hL0, Real.rpow_one]
          have hL_r : L_pow5 ≤ Real.log N :=
            (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
              ((le_max_right _ _).trans ((le_max_right _ _).trans
                ((le_max_right _ _).trans hL)))))
          have hdec := hrpow_inv_le (B := 152 * C_mid / δ) (γ := 1 - 3 * α)
            (by positivity) (by linarith only [hα]) hL_r
          calc
            _ ≤ 2 * (1 / (152 * C_mid / δ)) :=
              hc3.trans (mul_le_mul_of_nonneg_left hdec zero_le_two)
            _ = 2 * η_mid := by dsimp only [η_mid]; field_simp [hCmid.ne', hδ0.ne']
        have hL_le_N10 : Real.log N ≤ 10 * (N : ℝ) ^ (1 / 10 : ℝ) := by
          simpa only [one_div, inv_inv] using
            log_le_rpow_div_pos hN0 (by norm_num : (0 : ℝ) < 1 / 10)
        have hN35_div : (N : ℝ) ^ (3 / 5 : ℝ) / N ≤ 1 / (N : ℝ) ^ (1 / 5 : ℝ) := by
          rw [div_le_div_iff₀ hN0 (by positivity), one_mul]
          calc
            (N : ℝ) ^ (3 / 5 : ℝ) * (N : ℝ) ^ (1 / 5 : ℝ) = (N : ℝ) ^ (4 / 5 : ℝ) := by
              rw [← Real.rpow_add hN0]; norm_num
            _ ≤ (N : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by norm_num)
            _ = N := Real.rpow_one _
        have h10_6_N5 : (10 : ℝ) ^ 6 * (1 / (N : ℝ) ^ (1 / 5 : ℝ)) ≤ η_mid := by
          have hN5_mid : 152 * C_mid * 10 ^ 6 / δ + 1 ≤ (N : ℝ) ^ (1 / 5 : ℝ) :=
            (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN5))
          rw [mul_one_div, div_le_iff₀ (by positivity)]
          have hm := (div_le_iff₀ hδ0).mp
            (by linarith only [hN5_mid] : 152 * C_mid * 10 ^ 6 / δ ≤ (N : ℝ) ^ (1 / 5 : ℝ))
          have heq : η_mid * (N : ℝ) ^ (1 / 5 : ℝ) * (152 * C_mid) =
              δ * (N : ℝ) ^ (1 / 5 : ℝ) := by
            dsimp only [η_mid]; field_simp [hCmid.ne']
          have h152 : 0 < 152 * C_mid := by positivity
          nlinarith only [hm, heq, h152]
        have ht2 : c ^ 5 * Real.log N / N ≤ η_mid := by
          have hc5 : c ^ 5 * Real.log N ≤ 10 ^ 6 * (N : ℝ) ^ (3 / 5 : ℝ) := by
            have h1 : c ≤ 10 * (N : ℝ) ^ (1 / 10 : ℝ) := hc_le_L.trans hL_le_N10
            calc
              c ^ 5 * Real.log N ≤
                  (10 * (N : ℝ) ^ (1 / 10 : ℝ)) ^ 5 * (10 * (N : ℝ) ^ (1 / 10 : ℝ)) :=
                mul_le_mul (pow_le_pow_left₀ hc0.le h1 5) hL_le_N10 hL0.le (by positivity)
              _ = 10 ^ 6 * ((N : ℝ) ^ (1 / 10 : ℝ)) ^ 6 := by ring
              _ = 10 ^ 6 * (N : ℝ) ^ (3 / 5 : ℝ) := by
                rw [← Real.rpow_natCast _ 6, ← Real.rpow_mul hN0.le]; norm_num
          calc
            c ^ 5 * Real.log N / N ≤ (10 ^ 6 * (N : ℝ) ^ (3 / 5 : ℝ)) / N :=
              div_le_div_of_nonneg_right hc5 hN0.le
            _ = 10 ^ 6 * ((N : ℝ) ^ (3 / 5 : ℝ) / N) := by ring
            _ ≤ 10 ^ 6 * (1 / (N : ℝ) ^ (1 / 5 : ℝ)) :=
              mul_le_mul_of_nonneg_left hN35_div (by norm_num)
            _ ≤ η_mid := h10_6_N5
        have ht3 : c ^ 4 / Real.sqrt ((m - 1 : ℕ) : ℝ) ≤ 2 * η_mid := by
          have hm1_ge : (1 / 4 : ℝ) * Real.log N ^ A ≤ ((m - 1 : ℕ) : ℝ) := by
            have hnat : m ≤ 2 * (m - 1) := by omega
            have hcast : (m : ℝ) ≤ 2 * ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
            have hLA_pos : 0 ≤ Real.log N ^ A := by positivity
            linarith only [hmR_ge_LA, hcast, hLA_pos]
          have hsqrt_ge : (1 / 2 : ℝ) * Real.log N ^ (A / 2) ≤ Real.sqrt ((m - 1 : ℕ) : ℝ) := by
            have hsq : ((1 / 2 : ℝ) * Real.log N ^ (A / 2)) ^ 2 = (1 / 4 : ℝ) * Real.log N ^ A := by
              rw [mul_pow, ← Real.rpow_natCast (Real.log N ^ (A / 2)) 2, ← Real.rpow_mul hL0.le]
              congr 2 <;> norm_num
            have hpos : 0 ≤ (1 / 2 : ℝ) * Real.log N ^ (A / 2) := by positivity
            exact (Real.sqrt_sq hpos).symm.trans_le (Real.sqrt_le_sqrt (hsq.trans_le hm1_ge))
          have hc4_ub : c ^ 4 ≤ Real.log N ^ (4 * α) := by
            calc
              c ^ 4 ≤ (Real.log N ^ α) ^ 4 := pow_le_pow_left₀ hc0.le hc_ub 4
              _ = Real.log N ^ (4 * α) := by
                rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hL0.le]; norm_num
          have hL_r : L_pow6 ≤ Real.log N :=
            (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
              ((le_max_right _ _).trans ((le_max_right _ _).trans
                ((le_max_right _ _).trans ((le_max_right _ _).trans hL))))))
          have hdec := hrpow_inv_le (B := 152 * C_mid / δ) (γ := γ_A)
            (by positivity) hγ_A hL_r
          calc
            c ^ 4 / Real.sqrt ((m - 1 : ℕ) : ℝ) ≤
                Real.log N ^ (4 * α) / ((1 / 2 : ℝ) * Real.log N ^ (A / 2)) :=
              (div_le_div_of_nonneg_right hc4_ub (by positivity)).trans
                (div_le_div_of_nonneg_left (by positivity) (by positivity) hsqrt_ge)
            _ = 2 * (Real.log N ^ (4 * α) / Real.log N ^ (A / 2)) := by ring
            _ = 2 * Real.log N ^ (-γ_A) := by
              rw [← Real.rpow_sub hL0]; congr 2; dsimp only [γ_A]; ring
            _ ≤ 2 * (1 / (152 * C_mid / δ)) := mul_le_mul_of_nonneg_left hdec zero_le_two
            _ = 2 * η_mid := by dsimp only [η_mid]; field_simp [hCmid.ne', hδ0.ne']
        have ht4 : c ^ 3 * (m : ℝ) ^ 4 / N ≤ η_mid := by
          have hc3m4 : c ^ 3 * (m : ℝ) ^ 4 ≤ 10 ^ 6 * (N : ℝ) ^ (3 / 5 : ℝ) := by
            have hc1 : c ≤ 10 * (N : ℝ) ^ (1 / 10 : ℝ) := hc_le_L.trans hL_le_N10
            have hc3 : c ^ 3 ≤ 10 ^ 3 * (N : ℝ) ^ (3 / 10 : ℝ) := by
              calc
                c ^ 3 ≤ (10 * (N : ℝ) ^ (1 / 10 : ℝ)) ^ 3 := pow_le_pow_left₀ hc0.le hc1 3
                _ = 10 ^ 3 * ((N : ℝ) ^ (1 / 10 : ℝ)) ^ 3 := by ring
                _ = 10 ^ 3 * (N : ℝ) ^ (3 / 10 : ℝ) := by
                  rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul hN0.le]; norm_num
            have hm4 : (m : ℝ) ^ 4 ≤ (N : ℝ) ^ (1 / 5 : ℝ) := by
              calc
                (m : ℝ) ^ 4 ≤ ((N : ℝ) ^ (1 / 20 : ℝ)) ^ 4 := pow_le_pow_left₀ hm0.le hmR_20 4
                _ = (N : ℝ) ^ (1 / 5 : ℝ) := by
                  rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hN0.le]; norm_num
            have hhalf_35 : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) ^ (3 / 5 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by norm_num)
            calc
              c ^ 3 * (m : ℝ) ^ 4 ≤ (10 ^ 3 * (N : ℝ) ^ (3 / 10 : ℝ)) * (N : ℝ) ^ (1 / 5 : ℝ) :=
                mul_le_mul hc3 hm4 (by positivity) (by positivity)
              _ = 10 ^ 3 * ((N : ℝ) ^ (3 / 10 : ℝ) * (N : ℝ) ^ (1 / 5 : ℝ)) := by ring
              _ = 10 ^ 3 * (N : ℝ) ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hN0]; norm_num
              _ ≤ 10 ^ 6 * (N : ℝ) ^ (3 / 5 : ℝ) :=
                mul_le_mul (by norm_num) hhalf_35 (by positivity) (by norm_num)
          calc
            c ^ 3 * (m : ℝ) ^ 4 / N ≤ (10 ^ 6 * (N : ℝ) ^ (3 / 5 : ℝ)) / N :=
              div_le_div_of_nonneg_right hc3m4 hN0.le
            _ = 10 ^ 6 * ((N : ℝ) ^ (3 / 5 : ℝ) / N) := by ring
            _ ≤ 10 ^ 6 * (1 / (N : ℝ) ^ (1 / 5 : ℝ)) :=
              mul_le_mul_of_nonneg_left hN35_div (by norm_num)
            _ ≤ η_mid := h10_6_N5
        have hmid_le : |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v_m, v_m⟫| ≤
            (3 / 4) * δ * Real.log m := by
          have hsum6 : c ^ 2 * (1 + Real.log c) / Real.log N + c ^ 5 * Real.log N / N +
              c ^ 4 / Real.sqrt ((m - 1 : ℕ) : ℝ) + c ^ 3 * (m : ℝ) ^ 4 / N ≤ 6 * η_mid := by
            linarith only [ht1, ht2, ht3, ht4]
          calc
            |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v_m, v_m⟫| ≤
                C_mid * (6 * η_mid) * 19 :=
              hmid_b.trans (mul_le_mul
                (mul_le_mul_of_nonneg_left hsum6 hCmid.le) hv_sq_le
                (sq_nonneg _) (by positivity))
            _ = (3 / 4) * δ := by
              dsimp only [η_mid]; field_simp [hCmid.ne']; ring
            _ ≤ (3 / 4) * δ * Real.log m :=
              le_mul_of_one_le_right (by positivity) hlogm_ge1
        -- 2) `2 * |⟪overlapMatrix v_m - downwardPrimeVector v_m, v_m⟫| ≤ (1 / 4) * δ * log m`.
        have hod_le :
            2 * |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v_m -
                downwardPrimeVector φ c N v_m, v_m⟫| ≤
              (1 / 4) * δ * Real.log m := by
          have hod_b := hod hm2 hmN_sq hlog18 hc1 hw3 hRNT_m hv_mem
          let X := c ^ 2 * (1 + Real.log m) * Real.sqrt ((1 + Real.log c) / Real.log N)
          let Y := c ^ 2 * (m : ℝ) * Real.sqrt (Real.log N / N)
          have hcs : 2 * |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v_m -
                downwardPrimeVector φ c N v_m, v_m⟫| ≤
              38 * C_od * X + 38 * C_od * Y := by
            have h1 := abs_real_inner_le_norm
              (Matrix.toEuclideanLin (overlapMatrix φ c N) v_m -
                downwardPrimeVector φ c N v_m) v_m
            have h2 : ‖Matrix.toEuclideanLin (overlapMatrix φ c N) v_m -
                  downwardPrimeVector φ c N v_m‖ * ‖v_m‖ ≤
                C_od * (X + Y) * ‖v_m‖ ^ 2 := by
              calc
                _ ≤ (C_od * (X + Y) * ‖v_m‖) * ‖v_m‖ :=
                  mul_le_mul_of_nonneg_right hod_b (norm_nonneg _)
                _ = C_od * (X + Y) * ‖v_m‖ ^ 2 := by ring
            have hXY0 : 0 ≤ C_od * (X + Y) := by
              dsimp only [X, Y]
              have := Real.log_natCast_nonneg m
              positivity
            calc
              2 * |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v_m -
                    downwardPrimeVector φ c N v_m, v_m⟫| ≤
                  2 * (C_od * (X + Y) * ‖v_m‖ ^ 2) :=
                mul_le_mul_of_nonneg_left (h1.trans h2) zero_le_two
              _ ≤ 2 * (C_od * (X + Y) * 19) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hv_sq_le hXY0) zero_le_two
              _ = 38 * C_od * X + 38 * C_od * Y := by ring
          have hX_le : 38 * C_od * X ≤ (1 / 8) * δ * Real.log m := by
            let K_α := 1 + 1 / (2 * η_α)
            have hKα : 0 < K_α := by dsimp only [K_α]; positivity
            have h1c_le : 1 + Real.log c ≤ K_α * Real.log N ^ (2 * η_α) := by
              have hlc : Real.log c ≤ Real.log (Real.log N) := Real.log_le_log hc0 hc_le_L
              have hll : Real.log (Real.log N) ≤ Real.log N ^ (2 * η_α) / (2 * η_α) :=
                log_le_rpow_div_pos hL0 (by positivity)
              have h1pow : 1 ≤ Real.log N ^ (2 * η_α) :=
                Real.one_le_rpow hL1 (by positivity)
              dsimp only [K_α]
              have hdiv_eq : Real.log N ^ (2 * η_α) / (2 * η_α) =
                  (1 / (2 * η_α)) * Real.log N ^ (2 * η_α) := by ring
              linarith only [hlc, hll, h1pow, hdiv_eq]
            have hsqrt_le : Real.sqrt ((1 + Real.log c) / Real.log N) ≤
                Real.sqrt K_α * Real.log N ^ (η_α - 1 / 2) := by
              have hdiv : (1 + Real.log c) / Real.log N ≤
                  (Real.sqrt K_α * Real.log N ^ (η_α - 1 / 2)) ^ 2 := by
                calc
                  (1 + Real.log c) / Real.log N ≤ (K_α * Real.log N ^ (2 * η_α)) / Real.log N :=
                    div_le_div_of_nonneg_right h1c_le hL0.le
                  _ = K_α * (Real.log N ^ (2 * η_α) / Real.log N) := by ring
                  _ = K_α * Real.log N ^ (2 * η_α - 1) := by
                    rw [Real.rpow_sub hL0, Real.rpow_one]
                  _ = (Real.sqrt K_α * Real.log N ^ (η_α - 1 / 2)) ^ 2 := by
                    rw [mul_pow, Real.sq_sqrt hKα.le,
                      ← Real.rpow_natCast (Real.log N ^ (η_α - 1 / 2)) 2,
                      ← Real.rpow_mul hL0.le]
                    congr 2; ring
              exact (Real.sqrt_le_sqrt hdiv).trans_eq (Real.sqrt_sq (by positivity))
            have hc2_sqrt : c ^ 2 * Real.sqrt ((1 + Real.log c) / Real.log N) ≤
                Real.sqrt K_α * Real.log N ^ (-γ_od) := by
              calc
                c ^ 2 * Real.sqrt ((1 + Real.log c) / Real.log N) ≤
                    Real.log N ^ (2 * α) * (Real.sqrt K_α * Real.log N ^ (η_α - 1 / 2)) :=
                  mul_le_mul hc2_ub hsqrt_le (by positivity) (by positivity)
                _ = Real.sqrt K_α * (Real.log N ^ (2 * α) * Real.log N ^ (η_α - 1 / 2)) := by ring
                _ = Real.sqrt K_α * Real.log N ^ (-γ_od) := by
                  rw [← Real.rpow_add hL0]; congr 2; dsimp only [γ_od]; ring
            have hL_r : L_pow7 ≤ Real.log N :=
              (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
                ((le_max_right _ _).trans ((le_max_right _ _).trans
                  ((le_max_right _ _).trans ((le_max_right _ _).trans hL))))))
            have hdec := hrpow_inv_le (B := 640 * C_od * Real.sqrt K_α / δ) (γ := γ_od)
              (by positivity) hγ_od hL_r
            have h1m_le : 1 + Real.log m ≤ 2 * Real.log m := by linarith only [hlogm_ge1]
            have hKs0 : 0 < Real.sqrt K_α := Real.sqrt_pos.mpr hKα
            calc
              38 * C_od * X =
                  38 * C_od * (c ^ 2 * Real.sqrt ((1 + Real.log c) / Real.log N)) *
                    (1 + Real.log m) := by dsimp only [X]; ring
              _ ≤ 38 * C_od * (Real.sqrt K_α * Real.log N ^ (-γ_od)) * (2 * Real.log m) :=
                mul_le_mul
                  (mul_le_mul_of_nonneg_left hc2_sqrt (by positivity))
                  h1m_le (by positivity) (by positivity)
              _ = 76 * C_od * Real.sqrt K_α * Real.log N ^ (-γ_od) * Real.log m := by ring
              _ ≤ 76 * C_od * Real.sqrt K_α *
                    (1 / (640 * C_od * Real.sqrt K_α / δ)) * Real.log m :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hdec (by positivity)) hlogm0.le
              _ = (76 / 640 : ℝ) * δ * Real.log m := by
                field_simp [hCod.ne', hKs0.ne', hδ0.ne']; ring
              _ ≤ (1 / 8) * δ * Real.log m := by nlinarith only [hδ0, hlogm0]
          have hY_le : 38 * C_od * Y ≤ (1 / 8) * δ * Real.log m := by
            have hY_ub : Y ≤ 1000 / (N : ℝ) ^ (1 / 5 : ℝ) := by
              have hY_sq : Y ^ 2 ≤ (1000 / (N : ℝ) ^ (1 / 5 : ℝ)) ^ 2 := by
                have hc4L : c ^ 4 * Real.log N ≤ 10 ^ 5 * (N : ℝ) ^ (1 / 2 : ℝ) := by
                  have hc1 : c ≤ 10 * (N : ℝ) ^ (1 / 10 : ℝ) := hc_le_L.trans hL_le_N10
                  calc
                    c ^ 4 * Real.log N ≤
                        (10 * (N : ℝ) ^ (1 / 10 : ℝ)) ^ 4 * (10 * (N : ℝ) ^ (1 / 10 : ℝ)) :=
                      mul_le_mul (pow_le_pow_left₀ hc0.le hc1 4) hL_le_N10 hL0.le (by positivity)
                    _ = 10 ^ 5 * ((N : ℝ) ^ (1 / 10 : ℝ)) ^ 5 := by ring
                    _ = 10 ^ 5 * (N : ℝ) ^ (1 / 2 : ℝ) := by
                      rw [← Real.rpow_natCast _ 5, ← Real.rpow_mul hN0.le]; norm_num
                have hm2_10 : (m : ℝ) ^ 2 ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
                  calc
                    (m : ℝ) ^ 2 ≤ ((N : ℝ) ^ (1 / 20 : ℝ)) ^ 2 := pow_le_pow_left₀ hm0.le hmR_20 2
                    _ = (N : ℝ) ^ (1 / 10 : ℝ) := by
                      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hN0.le]; norm_num
                have hnum : c ^ 4 * (m : ℝ) ^ 2 * Real.log N ≤ 10 ^ 6 * (N : ℝ) ^ (3 / 5 : ℝ) := by
                  calc
                    c ^ 4 * (m : ℝ) ^ 2 * Real.log N = (c ^ 4 * Real.log N) * (m : ℝ) ^ 2 := by ring
                    _ ≤ (10 ^ 5 * (N : ℝ) ^ (1 / 2 : ℝ)) * (N : ℝ) ^ (1 / 10 : ℝ) :=
                      mul_le_mul hc4L hm2_10 (by positivity) (by positivity)
                    _ = 10 ^ 5 * ((N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ)) := by ring
                    _ = 10 ^ 5 * (N : ℝ) ^ (3 / 5 : ℝ) := by rw [← Real.rpow_add hN0]; norm_num
                    _ ≤ 10 ^ 6 * (N : ℝ) ^ (3 / 5 : ℝ) :=
                      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
                have hdiv_sq : (N : ℝ) ^ (3 / 5 : ℝ) / N = (1 / (N : ℝ) ^ (1 / 5 : ℝ)) ^ 2 := by
                  rw [one_div, inv_pow, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hN0.le,
                    div_eq_iff hN0.ne', inv_mul_eq_iff_eq_mul₀ (by positivity),
                    ← Real.rpow_add hN0]
                  norm_num
                  exact (Real.rpow_one _).symm
                calc
                  Y ^ 2 = (c ^ 4 * (m : ℝ) ^ 2 * Real.log N) / N := by
                    dsimp only [Y]
                    rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hL0.le hN0.le)]
                    ring
                  _ ≤ (10 ^ 6 * (N : ℝ) ^ (3 / 5 : ℝ)) / N :=
                    div_le_div_of_nonneg_right hnum hN0.le
                  _ = 10 ^ 6 * ((N : ℝ) ^ (3 / 5 : ℝ) / N) := by ring
                  _ = 10 ^ 6 * (1 / (N : ℝ) ^ (1 / 5 : ℝ)) ^ 2 := by rw [hdiv_sq]
                  _ = (1000 / (N : ℝ) ^ (1 / 5 : ℝ)) ^ 2 := by ring
              have hY0 : 0 ≤ Y := by dsimp only [Y]; positivity
              have hrhs0 : 0 ≤ 1000 / (N : ℝ) ^ (1 / 5 : ℝ) := by positivity
              nlinarith only [hY_sq, hY0, hrhs0]
            have hN5_od : 320000 * C_od / δ + 1 ≤ (N : ℝ) ^ (1 / 5 : ℝ) :=
              (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN5))
            have hsmall : 38 * C_od * (1000 / (N : ℝ) ^ (1 / 5 : ℝ)) ≤ (1 / 8) * δ := by
              have hm := (div_le_iff₀ hδ0).mp
                (by linarith only [hN5_od] : 320000 * C_od / δ ≤ (N : ℝ) ^ (1 / 5 : ℝ))
              rw [show 38 * C_od * (1000 / (N : ℝ) ^ (1 / 5 : ℝ)) =
                (38000 * C_od) / (N : ℝ) ^ (1 / 5 : ℝ) by ring,
                div_le_iff₀ (by positivity)]
              nlinarith only [hm, hCod]
            calc
              38 * C_od * Y ≤ 38 * C_od * (1000 / (N : ℝ) ^ (1 / 5 : ℝ)) :=
                mul_le_mul_of_nonneg_left hY_ub (by positivity)
              _ ≤ (1 / 8) * δ := hsmall
              _ ≤ (1 / 8) * δ * Real.log m := le_mul_of_one_le_right (by positivity) hlogm_ge1
          linarith only [hcs, hX_le, hY_le]
        calc
          |-⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v_m, v_m⟫ +
              2 * ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v_m -
                downwardPrimeVector φ c N v_m, v_m⟫| ≤
              |-⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v_m, v_m⟫| +
                |2 * ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v_m -
                  downwardPrimeVector φ c N v_m, v_m⟫| := abs_add_le _ _
          _ = |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v_m, v_m⟫| +
                2 * |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v_m -
                  downwardPrimeVector φ c N v_m, v_m⟫| := by
            rw [abs_neg, abs_mul, abs_of_pos zero_lt_two]
          _ ≤ (3 / 4) * δ * Real.log m + (1 / 4) * δ * Real.log m := add_le_add hmid_le hod_le
          _ = δ * Real.log m := by ring
      exact ⟨hsep_I, hov_I⟩
    · -- Regime II (`⌊N^(1/20)⌋₊ < m`): `(1 / 20) * log N ≤ log m`, so `O(c^2)` errors are `≤ δ * log m`.
      have hm_gt : (N : ℝ) ^ (1 / 20 : ℝ) ≤ m :=
        (Nat.lt_floor_add_one _).le.trans
          (by exact_mod_cast Nat.succ_le_of_lt (lt_of_not_ge hm_low))
      have hlogm_25 : (1 / 25 : ℝ) * Real.log N ≤ Real.log m := by
        have h20 : (1 / 20 : ℝ) * Real.log N ≤ Real.log m := by
          have h := Real.log_le_log (by positivity) hm_gt
          rwa [Real.log_rpow hN0] at h
        linarith only [h20, hL0]
      have hL_r4 : L_pow4 ≤ Real.log N :=
        (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
          ((le_max_right _ _).trans ((le_max_right _ _).trans hL))))
      let B4 := 1900 * (K₀ + 1) / δ + 25 * (2 * C_ov1 + C_nr) / δ
      have hB4 : 0 < B4 := by dsimp only [B4]; positivity
      have hdec4 : c ^ 2 / Real.log N ≤ 1 / B4 := by
        have hd := hrpow_inv_le (B := B4) (γ := 1 - 2 * α) hB4 (by linarith only [hα]) hL_r4
        have hc2_div : c ^ 2 / Real.log N ≤ Real.log N ^ (-(1 - 2 * α)) := by
          rw [show -(1 - 2 * α) = 2 * α - 1 by ring, Real.rpow_sub hL0, Real.rpow_one]
          exact div_le_div_of_nonneg_right hc2_ub hL0.le
        exact hc2_div.trans hd
      have hsep_II :
          |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) v_m, v_m⟫| ≤ δ * Real.log m := by
        have hcs := abs_real_inner_le_norm
          (Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) v_m) v_m
        have hnorm := norm_separatedCrossErrorMatrix_le hφ hsupp hM_int hc0 hN1 v_m
        have h1 : |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) v_m, v_m⟫| ≤
            76 * (K₀ + 1) * c ^ 2 := by
          calc
            _ ≤ (4 * K₀ * c ^ 2 * ‖v_m‖) * ‖v_m‖ :=
              hcs.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
            _ = 4 * K₀ * c ^ 2 * ‖v_m‖ ^ 2 := by ring
            _ ≤ 4 * K₀ * c ^ 2 * 19 :=
              mul_le_mul_of_nonneg_left hv_sq_le (by positivity)
            _ ≤ 76 * (K₀ + 1) * c ^ 2 := by nlinarith only [hK₀, sq_nonneg c]
        have hB4_ge : 1900 * (K₀ + 1) / δ ≤ B4 := by dsimp only [B4]; positivity
        have hdiv_le : c ^ 2 / Real.log N ≤ δ / (1900 * (K₀ + 1)) :=
          hdec4.trans ((one_div_le_one_div_of_le (by positivity) hB4_ge).trans_eq
            (by field_simp [hδ0.ne', (show 1900 * (K₀ + 1) ≠ 0 by positivity)]))
        calc
          _ ≤ 76 * (K₀ + 1) * c ^ 2 := h1
          _ = 1900 * (K₀ + 1) * (c ^ 2 / Real.log N) * ((1 / 25) * Real.log N) := by
            field_simp [hL0.ne']; ring
          _ ≤ 1900 * (K₀ + 1) * (δ / (1900 * (K₀ + 1))) * ((1 / 25) * Real.log N) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hdiv_le (by positivity)) (by positivity)
          _ = δ * ((1 / 25) * Real.log N) := by
            field_simp [(show 1900 * (K₀ + 1) ≠ 0 by positivity)]; ring
          _ ≤ δ * Real.log m := mul_le_mul_of_nonneg_left hlogm_25 hδ0.le
      have hov_II :
          |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v_m, v_m⟫ -
            ⟪Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) v_m, v_m⟫| ≤ δ * Real.log m := by
        have hb1 := hov1 hm2 hL1 hc1 hc_le_L hw3 hRNT_m
        have hb2 := abs_fullWeilNonRatioMatrix_mode_inner_le hφ hsupp hM_int hm2 hmN_sq hL1 hc0 hcN
        have h1c : 1 + Real.log c ≤ 2 * c := by
          have := Real.log_le_sub_one_of_pos hc0; linarith only [this, hc1]
        have hsum_c2 :
            |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v_m, v_m⟫ -
              ⟪Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) v_m, v_m⟫| ≤
              (2 * C_ov1 + C_nr) * c ^ 2 := by
          have hov_c2 : C_ov1 * c * (1 + Real.log c) ≤ 2 * C_ov1 * c ^ 2 := by
            calc
              C_ov1 * c * (1 + Real.log c) ≤ C_ov1 * c * (2 * c) :=
                mul_le_mul_of_nonneg_left h1c (by positivity)
              _ = 2 * C_ov1 * c ^ 2 := by ring
          have hnr_c2 : C_nr * c ≤ C_nr * c ^ 2 :=
            mul_le_mul_of_nonneg_left (by nlinarith only [hc1]) hCnr.le
          exact (abs_sub _ _).trans (by dsimp only [C_nr] at hnr_c2 ⊢; linarith only [hb1, hb2, hov_c2, hnr_c2])
        have hB4_ge : 25 * (2 * C_ov1 + C_nr) / δ ≤ B4 := by dsimp only [B4]; positivity
        have hdiv_le : c ^ 2 / Real.log N ≤ δ / (25 * (2 * C_ov1 + C_nr)) :=
          hdec4.trans ((one_div_le_one_div_of_le (by positivity) hB4_ge).trans_eq
            (by field_simp [hδ0.ne', (show 25 * (2 * C_ov1 + C_nr) ≠ 0 by positivity)]))
        calc
          _ ≤ (2 * C_ov1 + C_nr) * c ^ 2 := hsum_c2
          _ = 25 * (2 * C_ov1 + C_nr) * (c ^ 2 / Real.log N) * ((1 / 25) * Real.log N) := by
            field_simp [hL0.ne']; ring
          _ ≤ 25 * (2 * C_ov1 + C_nr) * (δ / (25 * (2 * C_ov1 + C_nr))) *
                ((1 / 25) * Real.log N) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hdiv_le (by positivity)) (by positivity)
          _ = δ * ((1 / 25) * Real.log N) := by
            field_simp [(show 25 * (2 * C_ov1 + C_nr) ≠ 0 by positivity)]; ring
          _ ≤ δ * Real.log m := mul_le_mul_of_nonneg_left hlogm_25 hδ0.le
      exact ⟨hsep_II, hov_II⟩
  obtain ⟨herr_sep, herr_ov⟩ := herr_sep_and_ov
  -- Final assembly of `completeWeilEnergy φ c N v_m`.
  have hE_eq : completeWeilEnergy φ c N v_m =
      renormalizedPrimeEnergy N v_m +
      (completeWeilSelfFinitePart φ c - Real.eulerMascheroniConstant +
        completeWeilSelfError φ c N) * ‖v_m‖ ^ 2 +
      ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N) v_m, v_m⟫ -
      ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) v_m, v_m⟫ +
      ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) v_m, v_m⟫ +
      (⟪Matrix.toEuclideanLin (overlapMatrix φ c N) v_m, v_m⟫ -
        ⟪Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) v_m, v_m⟫) := by
    unfold completeWeilEnergy renormalizedPrimeEnergy
    exact hdecomp
  have h1 := (abs_le.mp herr_prime).1
  have h2 := (abs_le.mp herr_center).1
  have h3 := (abs_le.mp herr_sep).2
  have h4 := (abs_le.mp herr_pole).1
  have h5 := (abs_le.mp herr_ov).1
  have hδ_eq : (3 / 4) * (1 - 2 * θ) * Real.log m - 5 * (δ * Real.log m) =
      ((1 - 2 * θ) / 4) * Real.log m := by dsimp only [δ]; ring
  linarith only [hE_eq, hmain_lb, h1, h2, h3, h4, h5, hδ_eq]

/-- **Structural Emptiness of Exceptional Conductors Above Polylogarithmic Scales.**
For every `C²` profile `φ` supported in `[0, 1]` with `0 < ∫ φ²`, every `0 < θ < 1 / 2`, every
`0 < α < 1 / 4`, and every `A > 8 * α`, eventually in `N`, for all `1 ≤ c ≤ (log N)^α`, no
Ramanujan conductor `m ∈ Icc ⌈(log N)^A⌉₊ ⌊N^θ⌋₊` has nonpositive complete-Weil energy:
```
{m ∈ Icc ⌈(log N)^A⌉₊ ⌊N^θ⌋₊ | completeWeilEnergy φ c N v_m ≤ 0} = ∅.
```
-/
theorem eventually_exceptionalConductors_above_polylog_empty {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) {θ α A : ℝ}
    (hθ0 : 0 < θ) (hθ : θ < 1 / 2) (hα0 : 0 < α) (hα : α < 1 / 4) (hA : 8 * α < A) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log N ^ α →
      ((Icc ⌈Real.log N ^ A⌉₊ ⌊(N : ℝ) ^ θ⌋₊).filter (fun m =>
        completeWeilEnergy φ c N (normalizedRamanujanHorizonVector m N) ≤ 0)) = ∅ := by
  have hA0 : 0 < A := by linarith only [hα0, hA]
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_completeWeilEnergy_mode_ge_log_above_polylog
      hφ hsupp hM_int hθ0 hθ hα0 hα hA,
    ((tendsto_rpow_atTop hA0).comp hlog).eventually_ge_atTop 2] with N hpos hLA2 c hc1 hc_ub
  rw [Finset.filter_eq_empty_iff]
  intro m hm hle
  have hm2 : 2 ≤ m := by
    have : 2 ≤ ⌈Real.log N ^ A⌉₊ := Nat.le_ceil.mp (by norm_num; exact hLA2)
    have hm_lo := (mem_Icc.mp hm).1
    omega
  have hlogm : 0 < Real.log m := Real.log_pos (by exact_mod_cast hm2)
  have h12θ : 0 < (1 - 2 * θ) / 4 := by linarith only [hθ]
  have hlb := hpos c hc1 hc_ub m hm
  linarith [mul_pos h12θ hlogm]

/-- **`tiltedUnitSpline` single-mode positivity floor above `(log N)^A`.** -/
theorem eventually_tiltedUnitSpline_mode_ge_log_above_polylog
    {θ α A : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1 / 2)
    (hα0 : 0 < α) (hα : α < 1 / 4) (hA : 8 * α < A) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log N ^ α →
      ∀ m ∈ Icc ⌈Real.log N ^ A⌉₊ ⌊(N : ℝ) ^ θ⌋₊,
        ((1 - 2 * θ) / 4) * Real.log m ≤
          completeWeilEnergy tiltedUnitSpline c N (normalizedRamanujanHorizonVector m N) :=
  eventually_completeWeilEnergy_mode_ge_log_above_polylog
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
    hθ0 hθ hα0 hα hA

/-- **`tiltedUnitSpline` emptiness of exceptional conductors above `(log N)^A`.** -/
theorem eventually_tiltedUnitSpline_exceptionalConductors_above_polylog_empty
    {θ α A : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1 / 2)
    (hα0 : 0 < α) (hα : α < 1 / 4) (hA : 8 * α < A) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log N ^ α →
      ((Icc ⌈Real.log N ^ A⌉₊ ⌊(N : ℝ) ^ θ⌋₊).filter (fun m =>
        completeWeilEnergy tiltedUnitSpline c N
          (normalizedRamanujanHorizonVector m N) ≤ 0)) = ∅ :=
  eventually_exceptionalConductors_above_polylog_empty
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
    hθ0 hθ hα0 hα hA

#print axioms eventually_completeWeilEnergy_mode_ge_log_above_polylog
#print axioms eventually_exceptionalConductors_above_polylog_empty
#print axioms eventually_tiltedUnitSpline_mode_ge_log_above_polylog
#print axioms eventually_tiltedUnitSpline_exceptionalConductors_above_polylog_empty

end GaloisForLFunctions.CompletedArithmeticForms

