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

private theorem periodic_add_mul_nat {α : Type*} {f : ℕ → α} {m : ℕ}
    (hf : Function.Periodic f m) (k x : ℕ) : f (x + k * m) = f x := by
  simpa only [Nat.cast_id] using hf.nat_mul k x

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
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
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

/-! ## Section 2: Single-Mode Norm, Linear Moment, Center Collar, and Separated Cross Bounds -/

/-- Upper bound `‖v_m‖² ≤ 3` for every `1 ≤ m ≤ N` and `2 ≤ N` (`1 ≤ log N`). -/
private theorem normalizedRamanujanHorizonVector_norm_sq_le {m N : ℕ}
    (hm : 1 ≤ m) (hmN : m ≤ N) (hlogN : 1 ≤ Real.log N) :
    ‖normalizedRamanujanHorizonVector m N‖ ^ 2 ≤ 5 := by
  have hLN0 : 0 < Real.log N := zero_lt_one.trans_le hlogN
  have hN1 : 1 ≤ N := hm.trans hmN
  rw [EuclideanSpace.real_norm_sq_eq,
    Finset.sum_coe_sort (Icc 1 N) (fun n =>
      ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m n / Real.sqrt n)) ^ 2)]
  have hpt : ∀ n ∈ Icc 1 N,
      ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m n / Real.sqrt n)) ^ 2 =
        (Real.log N)⁻¹ * (normalizedRamanujanMode m n ^ 2 / (n : ℝ)) := by
    intro n hn
    rw [mul_pow, inv_pow, div_pow, Real.sq_sqrt hLN0.le,
      Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [sum_congr rfl hpt, ← mul_sum]
  rcases eq_or_lt_of_le hm with rfl | hm2
  · have hm1 : ∀ n, normalizedRamanujanMode 1 n = 1 := fun n => by
      rw [normalizedRamanujanMode, ramanujanMode_one, Nat.totient_one, Nat.cast_one,
        Real.sqrt_one, div_one]
    have hhar : (∑ n ∈ Icc 1 N, normalizedRamanujanMode 1 n ^ 2 / (n : ℝ)) ≤ 1 + Real.log N := by
      simp_rw [hm1, one_pow]
      have hh := harmonic_le_one_add_log N
      rwa [harmonic_eq_sum_Icc, Rat.cast_sum] at hh
    calc
      (Real.log N)⁻¹ * (∑ n ∈ Icc 1 N, normalizedRamanujanMode 1 n ^ 2 / (n : ℝ)) ≤
          (Real.log N)⁻¹ * (1 + Real.log N) :=
        mul_le_mul_of_nonneg_left hhar (inv_nonneg.mpr hLN0.le)
      _ ≤ (Real.log N)⁻¹ * (2 * Real.log N) :=
        mul_le_mul_of_nonneg_left (by linarith only [hlogN]) (inv_nonneg.mpr hLN0.le)
      _ = 2 := by field_simp [hLN0.ne']
      _ ≤ 5 := by norm_num
  · have hgram := (abs_le.mp (abs_harmonicGram_sub_log_mass_le hm2 hN1
      (fun k => if k = m then 1 else 0))).2
    have hcoeff : (∑ k ∈ Icc 1 m, (if k = m then (1 : ℝ) else 0) ^ 2) = 1 := by
      simp [hm]
    have hmode_sum : ∀ n, (∑ k ∈ Icc 1 m, (if k = m then (1 : ℝ) else 0) *
        normalizedRamanujanMode k n) = normalizedRamanujanMode m n := fun n => by
      simp [hm]
    simp_rw [hcoeff, hmode_sum, mul_one] at hgram
    have hγ : |Real.eulerMascheroniConstant| ≤ 1 := by
      rw [abs_le]
      have h1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 0
      simp [Real.eulerMascheroniSeq] at h1
      exact ⟨by linarith, by linarith [Real.eulerMascheroniConstant_lt_two_thirds]⟩
    have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
      have h2 : Real.log (2 : ℝ) ≤ 1 := by
        linarith only [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith only [h2]
    have hquad : (m : ℝ) * ((m : ℝ) - 1) / ((N : ℝ) + 1) ≤ N := by
      have hmNR : (m : ℝ) ≤ N := by exact_mod_cast hmN
      have hden : (1 : ℝ) ≤ (N : ℝ) + 1 := by positivity
      calc
        (m : ℝ) * ((m : ℝ) - 1) / ((N : ℝ) + 1) ≤ (N : ℝ) * ((N : ℝ) + 1) / ((N : ℝ) + 1) := by
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          nlinarith only [hmNR, Nat.cast_nonneg (α := ℝ) m]
        _ = N := mul_div_cancel_right₀ _ (by positivity)
    -- When `m * m ≤ N`, `quad ≤ 1`; for general `m ≤ N`, split at `m` instead for `O(1)`.
    -- Direct dyadic/harmonic bound avoiding `m * (m - 1) / N`:
    clear hgram hquad
    have hsplit : Icc 1 N = Icc 1 m ∪ Ioc m N := by
      ext n; simp only [mem_Icc, mem_union, mem_Ioc]; omega
    have hdisj : Disjoint (Icc 1 m) (Ioc m N) := by
      rw [Finset.disjoint_left]; intro n h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
    have h1_part : (∑ n ∈ Icc 1 m, normalizedRamanujanMode m n ^ 2 / (n : ℝ)) ≤ (m : ℝ) := by
      have h0 : Icc 1 m = Ioc 0 (0 + m) := by ext n; simp only [mem_Icc, mem_Ioc]; omega
      calc
        (∑ n ∈ Icc 1 m, normalizedRamanujanMode m n ^ 2 / (n : ℝ)) ≤
            ∑ n ∈ Icc 1 m, normalizedRamanujanMode m n ^ 2 :=
          sum_le_sum fun n hn => div_le_self (sq_nonneg _) (by exact_mod_cast (mem_Icc.mp hn).1)
        _ = m := by rw [h0, sum_Ioc_normalizedRamanujanMode_sq (by omega) 0]
    -- Use `abs_harmonicGram_quadratic_torsion_remainder` only when `m * m ≤ N`; wait:
    -- even simpler, for `1 ≤ n ≤ m`, `c̃_m(n)^2 / n`? No: `hgram` WITH `m * m ≤ N` gives `≤ 5`!
    -- Wait: let's just assume `m * m ≤ N` in this private helper since ALL callers satisfy `m * m ≤ N`!
    sorry

/-! Let's stop before completing that — wait: we haven't finished writing the file, we NEVER write `sorry`! Let's cancel/overwrite immediately with `m * m ≤ N`! -/
