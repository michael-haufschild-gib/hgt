import GaloisForLFunctions.RHTower.WeilConeRegularizedMertensConstant
import GaloisForLFunctions.RHTower.WeilConeHarmonicPinning

/-!
# The regularized Mertens constant agrees with the harmonic sum

The regularized Mertens constant of `WeilConeRegularizedMertensConstant` is the limit of the
smoothed sums `Σ_n d(n) χ_K(log n)/n`, `d = lam − Λ`. It exists for every full-cone Weil-positive
`lam`. This module shows it is the right object.

* **Monotone edge** (`mertensCutoff_antitone`). On `y ≥ δ` the cutoff `χ_K` is nonincreasing:
  there `χ_K(y) = c₀⁻¹ ∫ e^{−v} β(v)(1 − s((v+y)/δ − K)) dv`.
* **Abel summation** (`abs_sum_mul_sub_le`). If the partial sums of `a` stay within `ε` of `T`
  beyond `A`, and the weights equal `1` below `A` and decrease in `[0, 1]` beyond it, then the
  weighted sum is within `2ε` of `T`.
* **Consistency** (`tendsto_regularizedMertens_of_tendsto`). Whenever the plain harmonic sums
  `Σ_{n<N} d(n)/n` converge to `T`, the smoothed sums converge to the same `T`.
* **Harmonic pinning restated** (`regularizedMertens_nonpos_of_nonneg_of_localMass`). For
  nonnegative `lam` with vanishing local mass, the regularized constant is `≤ 0`, and it is `0`
  only for `Λ`.
-/

open MeasureTheory Set Filter Topology
open scoped Real

namespace RHTower.WeilOneSided

noncomputable section

/-- The profile sum on `y ≥ δ`: `∫ e^{−v} β(v)(1 − s((v+y)/δ − K)) dv`. -/
theorem sum_harmonicProfile_mertensBump_of_ge {y : ℝ} (hy : mertensStep ≤ y) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), harmonicProfile mertensBump (y - k * mertensStep) =
      ∫ v, mertensWeight v * (1 - Real.smoothTransition ((v + y) / mertensStep - K)) := by
  rw [sum_harmonicProfile_mertensBump]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  by_cases hv : mertensStep ≤ |v|
  · simp [mertensWeight, stepBump_eq_zero mertensStep_pos hv]
  · push Not at hv
    have hv' := abs_lt.mp hv
    have h1 : 1 ≤ (v + y) / mertensStep + 1 := by
      have : 0 ≤ (v + y) / mertensStep := div_nonneg (by linarith) mertensStep_pos.le
      linarith
    rw [Real.smoothTransition.one_of_one_le h1]

/-- **The cutoff decreases on `[δ, ∞)`.** -/
theorem mertensCutoff_antitone {K : ℕ} {y y' : ℝ} (hy : mertensStep ≤ y) (hyy : y ≤ y') :
    mertensCutoff K y' ≤ mertensCutoff K y := by
  unfold mertensCutoff
  rw [sum_harmonicProfile_mertensBump_of_ge hy, sum_harmonicProfile_mertensBump_of_ge (hy.trans hyy)]
  refine div_le_div_of_nonneg_right ?_ mertensMass_pos.le
  have hs : Continuous Real.smoothTransition := Real.smoothTransition.continuous
  refine integral_mono (integrable_mertensWeight_mul _ (by fun_prop))
    (integrable_mertensWeight_mul _ (by fun_prop)) fun v => ?_
  simp only
  have hmono : Real.smoothTransition ((v + y) / mertensStep - K) ≤
      Real.smoothTransition ((v + y') / mertensStep - K) :=
    Real.smoothTransition.monotone (by
      have : (v + y) / mertensStep ≤ (v + y') / mertensStep :=
        div_le_div_of_nonneg_right (by linarith) mertensStep_pos.le
      linarith)
  exact mul_le_mul_of_nonneg_left (by linarith) (mertensWeight_nonneg v)

/-! ## Abel summation -/

/-- The summation-by-parts identity `Σ_{n<B} a_n c_n = S_B c_{B−1} + Σ_{n<B−1} S_{n+1}(c_n − c_{n+1})`,
with `S_m = Σ_{n<m} a_n`. -/
theorem sum_mul_eq_abel (a c : ℕ → ℝ) (B : ℕ) :
    ∑ n ∈ Finset.range (B + 1), a n * c n =
      (∑ n ∈ Finset.range (B + 1), a n) * c B +
        ∑ n ∈ Finset.range B, (∑ m ∈ Finset.range (n + 1), a m) * (c n - c (n + 1)) := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun n => _ * (c n - c (n + 1))),
      Finset.sum_range_succ (fun n => a n) (B + 1)]
    ring

/-- **Abel summation against a decreasing cutoff.** Let `c = 1` below `A ≥ 1`, `c ∈ [0, 1]`, and `c`
nonincreasing from `A − 1` on. If the partial sums `S_m = Σ_{n<m} a_n` satisfy `|S_m − T| ≤ ε` for
`m ≥ A`, then `|Σ_{n ≤ B} a_n c_n − T| ≤ 2ε` for every `B ≥ A`. -/
theorem abs_sum_mul_sub_le {a c : ℕ → ℝ} {T ε : ℝ} {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B)
    (hc1 : ∀ n, n < A → c n = 1) (hc0 : ∀ n, 0 ≤ c n)
    (hanti : ∀ n, A ≤ n + 1 → c (n + 1) ≤ c n)
    (hR : ∀ m, A ≤ m → |∑ n ∈ Finset.range m, a n - T| ≤ ε) :
    |∑ n ∈ Finset.range (B + 1), a n * c n - T| ≤ 2 * ε := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hR A le_rfl)
  rw [sum_mul_eq_abel]
  -- the telescoping identity for `T`
  have htel : ∑ n ∈ Finset.range B, (c n - c (n + 1)) = c 0 - c B := by
    rw [Finset.sum_range_sub' c B]
  have hc0' : c 0 = 1 := hc1 0 (by omega)
  have hid : (∑ n ∈ Finset.range (B + 1), a n) * c B +
      ∑ n ∈ Finset.range B, (∑ m ∈ Finset.range (n + 1), a m) * (c n - c (n + 1)) - T =
      (∑ n ∈ Finset.range (B + 1), a n - T) * c B +
        ∑ n ∈ Finset.range B, (∑ m ∈ Finset.range (n + 1), a m - T) * (c n - c (n + 1)) := by
    have : T = T * c B + ∑ n ∈ Finset.range B, T * (c n - c (n + 1)) := by
      rw [← Finset.mul_sum, htel, hc0']; ring
    conv_lhs => rw [this]
    rw [show ∑ n ∈ Finset.range B, (∑ m ∈ Finset.range (n + 1), a m - T) * (c n - c (n + 1)) =
      ∑ n ∈ Finset.range B, (∑ m ∈ Finset.range (n + 1), a m) * (c n - c (n + 1)) -
        ∑ n ∈ Finset.range B, T * (c n - c (n + 1)) by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun n _ => by ring]
    ring
  rw [hid]
  -- the boundary term
  have hcB : c B ≤ 1 := by
    have : ∀ n, c n ≤ 1 := by
      intro n
      induction n with
      | zero => rw [hc0']
      | succ n ih =>
        rcases lt_or_ge (n + 1) A with h | h
        · rw [hc1 (n + 1) h]
        · exact (hanti n h).trans ih
    exact this B
  have h1 : |(∑ n ∈ Finset.range (B + 1), a n - T) * c B| ≤ ε := by
    rw [abs_mul, abs_of_nonneg (hc0 B)]
    have := hR (B + 1) (by omega)
    nlinarith [abs_nonneg (∑ n ∈ Finset.range (B + 1), a n - T), hc0 B]
  -- the inner terms
  have hterm : ∀ n ∈ Finset.range B,
      |(∑ m ∈ Finset.range (n + 1), a m - T) * (c n - c (n + 1))| ≤ ε * (c n - c (n + 1)) := by
    intro n _
    rcases lt_or_ge (n + 1) A with h | h
    · rw [hc1 n (by omega), hc1 (n + 1) h, sub_self, mul_zero, abs_zero, mul_zero]
    · have hd : 0 ≤ c n - c (n + 1) := sub_nonneg.mpr (hanti n h)
      rw [abs_mul, abs_of_nonneg hd]
      exact mul_le_mul_of_nonneg_right (hR (n + 1) h) hd
  have h2 : |∑ n ∈ Finset.range B, (∑ m ∈ Finset.range (n + 1), a m - T) * (c n - c (n + 1))| ≤ ε :=
    calc _ ≤ ∑ n ∈ Finset.range B, |(∑ m ∈ Finset.range (n + 1), a m - T) * (c n - c (n + 1))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.range B, ε * (c n - c (n + 1)) := Finset.sum_le_sum hterm
      _ = ε * (c 0 - c B) := by rw [← Finset.mul_sum, htel]
      _ ≤ ε := by rw [hc0']; nlinarith [hc0 B]
  calc _ ≤ |(∑ n ∈ Finset.range (B + 1), a n - T) * c B| +
        |∑ n ∈ Finset.range B, (∑ m ∈ Finset.range (n + 1), a m - T) * (c n - c (n + 1))| :=
        abs_add_le _ _
    _ ≤ 2 * ε := by linarith

/-! ## Consistency -/

/-- The weight `c_n = χ_K(log n)` for `n ≥ 2`, and `1` for `n ≤ 1`. -/
def mertensWeightSeq (K n : ℕ) : ℝ := if n ≤ 1 then 1 else mertensCutoff K (Real.log n)

theorem log_two_ge_mertensStep : mertensStep ≤ Real.log 2 := by
  have := WeilExcess.seventeen_div_twentyfive_lt_log_two
  rw [mertensStep]; linarith

/-- **Consistency.** If the harmonic sums `Σ_{n<N} d(n)/n` converge to `T`, then the smoothed sums
`Σ_n d(n) χ_K(log n)/n` converge to `T` as well. -/
theorem tendsto_regularizedMertens_of_tendsto (lam : ℕ → ℝ) {T : ℝ}
    (hT : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, coneDeviation lam n / n) atTop (𝓝 T)) :
    Tendsto (fun K : ℕ => ∑ n ∈ Finset.range ⌈Real.exp (K * mertensStep + 1)⌉₊,
      coneDeviation lam n * mertensCutoff K (Real.log n) / n) atTop (𝓝 T) := by
  set a : ℕ → ℝ := fun n => coneDeviation lam n / n with ha
  have hd01 : ∀ n, n ≤ 1 → coneDeviation lam n = 0 := fun n hn => by
    simp [coneDeviation, show ¬ (2 ≤ n) by omega]
  -- rewrite the smoothed sums with the weight sequence
  have hrew : ∀ K : ℕ, ∑ n ∈ Finset.range ⌈Real.exp (K * mertensStep + 1)⌉₊,
      coneDeviation lam n * mertensCutoff K (Real.log n) / n =
      ∑ n ∈ Finset.range ⌈Real.exp (K * mertensStep + 1)⌉₊, a n * mertensWeightSeq K n := by
    intro K
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [ha, mertensWeightSeq]
    split_ifs with h
    · rw [hd01 n h]; simp
    · ring
  simp_rw [hrew]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hT (ε / 3) (by positivity)
  -- choose `K` so that `A := max N₀ 2 ≤ e^{(K−1)δ}`
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt ((Real.log ((max N₀ 2 : ℕ) : ℝ)) / mertensStep + 2)
  refine ⟨K₀, fun K hK => ?_⟩
  set A : ℕ := max N₀ 2 with hAdef
  have hA2 : 2 ≤ A := le_max_right _ _
  have hAR : (1 : ℝ) < A := by exact_mod_cast (show 1 < A by omega)
  have hKbig : Real.log A / mertensStep + 2 < K := by
    have : (K₀ : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hlogA : Real.log A ≤ ((K : ℝ) - 1) * mertensStep := by
    have h := (div_lt_iff₀ mertensStep_pos).mp (show Real.log A / mertensStep < K - 2 by linarith)
    nlinarith [mertensStep_pos]
  set B : ℕ := ⌈Real.exp (K * mertensStep + 1)⌉₊ with hBdef
  have hAB : A + 1 ≤ B := by
    have h1 : (A : ℝ) ≤ Real.exp (((K : ℝ) - 1) * mertensStep) := by
      rw [← Real.exp_log (show (0 : ℝ) < A by linarith)]
      exact Real.exp_le_exp.mpr hlogA
    have h2 : Real.exp (((K : ℝ) - 1) * mertensStep) + 1 ≤ Real.exp (K * mertensStep + 1) := by
      have h3 : Real.exp (((K : ℝ) - 1) * mertensStep) ≤ Real.exp (K * mertensStep) :=
        Real.exp_le_exp.mpr (by nlinarith [mertensStep_pos])
      have h4 : Real.exp (K * mertensStep) + 1 ≤ Real.exp (K * mertensStep + 1) := by
        rw [Real.exp_add]
        have := Real.add_one_le_exp (1 : ℝ)
        have h5 : 1 ≤ Real.exp (K * mertensStep) :=
          Real.one_le_exp (by positivity [mertensStep_pos])
        nlinarith
      linarith
    have h5 : ((A + 1 : ℕ) : ℝ) ≤ Real.exp (K * mertensStep + 1) := by push_cast; linarith
    exact (Nat.le_ceil _).trans' (by exact_mod_cast h5) |> fun h => by
      exact_mod_cast (show ((A + 1 : ℕ) : ℝ) ≤ (B : ℝ) from h5.trans (Nat.le_ceil _))
  -- the weights
  have hc1 : ∀ n, n < A → mertensWeightSeq K n = 1 := by
    intro n hn
    unfold mertensWeightSeq
    split_ifs with h
    · rfl
    · push Not at h
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      have hn0 : (0 : ℝ) < n := by linarith
      refine mertensCutoff_eq_one ?_ ?_
      · exact log_two_ge_mertensStep.trans (Real.log_le_log (by norm_num) hn2)
      · refine (Real.log_le_log hn0 (by exact_mod_cast hn.le)).trans hlogA
  have hc0 : ∀ n, 0 ≤ mertensWeightSeq K n := by
    intro n; unfold mertensWeightSeq; split_ifs
    · norm_num
    · exact (mertensCutoff_mem K _).1
  have hanti : ∀ n, A ≤ n + 1 → mertensWeightSeq K (n + 1) ≤ mertensWeightSeq K n := by
    intro n hn
    unfold mertensWeightSeq
    split_ifs with h1 h2 h2
    · exact le_rfl
    · omega
    · exact (mertensCutoff_mem K _).2
    · push Not at h1 h2
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h2
      refine mertensCutoff_antitone ?_ (Real.log_le_log (by linarith) (by push_cast; linarith))
      exact log_two_ge_mertensStep.trans (Real.log_le_log (by norm_num) hn2)
  have hR : ∀ m, A ≤ m → |∑ n ∈ Finset.range m, a n - T| ≤ ε / 3 := by
    intro m hm
    have := hN₀ m ((le_max_left _ _).trans hm)
    rw [Real.dist_eq] at this
    exact this.le
  have hB1 : B = (B - 1) + 1 := by omega
  have key := abs_sum_mul_sub_le (a := a) (c := mertensWeightSeq K) (T := T) (A := A) (B := B - 1)
    (by omega) (by omega) hc1 hc0 hanti hR
  rw [← hB1] at key
  rw [Real.dist_eq]
  linarith

/-- **Harmonic pinning for the regularized constant.** For nonnegative full-cone Weil-positive
`lam` with vanishing local mass, the regularized Mertens constant `T` satisfies `T ≤ 0`, and
`T = 0` only for `lam = Λ`. -/
theorem regularizedMertens_nonpos_of_nonneg_of_localMass {lam : ℕ → ℝ}
    (hW : RHTower.WeilPositiveFull lam) (hnn : ∀ n, 2 ≤ n → 0 ≤ lam n)
    (hloc : WeilAbscissa.LocalMassTendsZero (coneDeviation lam)) :
    ∃ T : ℝ, Tendsto (fun K : ℕ => ∑ n ∈ Finset.range ⌈Real.exp (K * mertensStep + 1)⌉₊,
      coneDeviation lam n * mertensCutoff K (Real.log n) / n) atTop (𝓝 T) ∧ T ≤ 0 ∧
      (T = 0 → ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) := by
  obtain ⟨T, hT, hT0, hTeq⟩ := WeilAbscissa.exists_harmonicConstant_of_nonneg_of_localMassTendsZero
    hW hnn hloc
  exact ⟨T, tendsto_regularizedMertens_of_tendsto lam hT, hT0, hTeq⟩

end

end RHTower.WeilOneSided
