import GaloisForLFunctions.RHTower.SignedArithmeticAbscissaRH

/-!
# Pole-regularized `log ζ` and prime zeta series

`log ζ(s) = Σ_{n ≥ 2} (Λ(n)/log n) n^{-s}` and `Σ_p p^{-s}` have nonnegative coefficients, so both
diverge at every `s` with `Re s < 1` (`not_dirichletConvergesAt_logZetaShiftedCoeff`,
`not_dirichletConvergesAt_primeIndicator`).  Subtracting the pole series `Σ_{n ≥ 2} n^{-s}/log n`,
whose sum is `-log(s − 1)` plus a function analytic near `s = 1`, gives the signed series

  `Σ_{n ≥ 2} ((Λ(n) − 1)/log n) n^{-s}`   and   `Σ_{n ≥ 2} (1_P(n) − 1/log n) n^{-s}`.

For every `α ≥ 0` each of them converges at every real `σ > ½ + α` iff every zero of `ξ` has
`Re ρ ≤ ½ + α` (`xiZeroHalfPlaneBound_iff_logZetaRegCoeff_converges`,
`xiZeroHalfPlaneBound_iff_primeRegCoeff_converges`); at `α = 0` both are RH.

**Proof.**  For real coefficients and `θ ≥ 0`, convergence at every real `σ > θ` is equivalent to
partial sums `O(N^{θ+δ})` for every `δ > 0` (`partialSumPowerBound_iff_convergesRightOf`).  Summation
by parts shows that this growth class is stable under the weights `log n` and `1/log n`, which have
logarithmic and bounded variation respectively.  This carries the `Λ − 1` abscissa law
(`xiZeroHalfPlaneBound_iff_vonMangoldtMinusOne_converges`) to `(Λ − 1)/log n`.  The prime series
differs from it by the nonnegative prime-power series `Σ_{p^k, k ≥ 2} (1/k) p^{-ks}`, whose
partial sums are at most `(ψ − θ)/log 2 = O(√N log N)`.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-! ## Growth classes of partial sums -/

/-- Partial sums `Σ_{n<N} g n = O(N^{θ+δ})` for every `δ > 0`. -/
def PartialSumPowerBound (g : ℕ → ℝ) (θ : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    |∑ n ∈ Finset.range N, g n| ≤ C * ((N : ℝ) + 1) ^ (θ + δ)

/-- `Σ g n (n+1)^{-σ}` converges at every real `σ > θ`. -/
def ConvergesRightOf (g : ℕ → ℝ) (θ : ℝ) : Prop :=
  ∀ σ : ℝ, θ < σ → ∃ L : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N,
    ((g n : ℝ) : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-(σ : ℂ))) atTop (𝓝 L)

/-- **Abscissa of convergence as a growth class.** -/
theorem partialSumPowerBound_iff_convergesRightOf (g : ℕ → ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    PartialSumPowerBound g θ ↔ ConvergesRightOf g θ := by
  constructor
  · intro h σ hσ
    obtain ⟨C, hC0, hC⟩ := h ((σ - θ) / 2) (by linarith)
    refine GaloisForLFunctions.RHTower.tendsto_dirichlet_partialSum_of_poly_bounded
      (α := θ + (σ - θ) / 2) hC0 (by linarith) (fun N => ?_)
      (by rw [Complex.ofReal_re]; linarith)
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    exact hC N
  · intro h δ hδ
    obtain ⟨C, hC0, hC⟩ := exists_abs_sum_range_le_of_converges g
      (by linarith : (0 : ℝ) < θ + δ) (h (θ + δ) (by linarith))
    refine ⟨C, hC0, fun N => (hC N).trans (mul_le_mul_of_nonneg_left ?_ hC0)⟩
    exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)

theorem PartialSumPowerBound.mono {g : ℕ → ℝ} {θ θ' : ℝ} (h : PartialSumPowerBound g θ)
    (hθ : θ ≤ θ') : PartialSumPowerBound g θ' := by
  intro δ hδ
  obtain ⟨C, hC0, hC⟩ := h δ hδ
  refine ⟨C, hC0, fun N => (hC N).trans (mul_le_mul_of_nonneg_left ?_ hC0)⟩
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [N.cast_nonneg (α := ℝ)]) (by linarith)

theorem PartialSumPowerBound.add {g h : ℕ → ℝ} {θ : ℝ} (hg : PartialSumPowerBound g θ)
    (hh : PartialSumPowerBound h θ) : PartialSumPowerBound (fun n => g n + h n) θ := by
  intro δ hδ
  obtain ⟨C, hC0, hC⟩ := hg δ hδ
  obtain ⟨D, hD0, hD⟩ := hh δ hδ
  refine ⟨C + D, by positivity, fun N => ?_⟩
  rw [Finset.sum_add_distrib]
  calc _ ≤ |∑ n ∈ Finset.range N, g n| + |∑ n ∈ Finset.range N, h n| := abs_add_le _ _
    _ ≤ C * ((N : ℝ) + 1) ^ (θ + δ) + D * ((N : ℝ) + 1) ^ (θ + δ) := add_le_add (hC N) (hD N)
    _ = (C + D) * ((N : ℝ) + 1) ^ (θ + δ) := by ring

theorem PartialSumPowerBound.neg {g : ℕ → ℝ} {θ : ℝ} (hg : PartialSumPowerBound g θ) :
    PartialSumPowerBound (fun n => -g n) θ := by
  intro δ hδ
  obtain ⟨C, hC0, hC⟩ := hg δ hδ
  exact ⟨C, hC0, fun N => by rw [Finset.sum_neg_distrib, abs_neg]; exact hC N⟩

theorem PartialSumPowerBound.sub {g h : ℕ → ℝ} {θ : ℝ} (hg : PartialSumPowerBound g θ)
    (hh : PartialSumPowerBound h θ) : PartialSumPowerBound (fun n => g n - h n) θ := by
  simpa only [sub_eq_add_neg] using hg.add hh.neg

theorem partialSumPowerBound_of_abs_le {g : ℕ → ℝ} {θ B : ℝ} (hθ : 0 ≤ θ)
    (h : ∀ N : ℕ, |∑ n ∈ Finset.range N, g n| ≤ B) : PartialSumPowerBound g θ := by
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (h 0)
  refine fun δ hδ => ⟨B, hB, fun N => (h N).trans ?_⟩
  exact le_mul_of_one_le_right hB
    (Real.one_le_rpow (by linarith [N.cast_nonneg (α := ℝ)]) (by linarith))

/-! ## Summation by parts against weights -/

theorem abs_sum_range_mul_le_of_partial (g w : ℕ → ℝ) (N : ℕ) {B : ℝ}
    (hB : ∀ k, k ≤ N → |∑ j ∈ Finset.range k, g j| ≤ B) :
    |∑ i ∈ Finset.range N, w i * g i| ≤
      B * (|w (N - 1)| + ∑ i ∈ Finset.range (N - 1), |w (i + 1) - w i|) := by
  have h := Finset.sum_range_by_parts w g N
  simp only [smul_eq_mul] at h
  rw [h]
  calc _ ≤ |w (N - 1) * ∑ i ∈ Finset.range N, g i| + |∑ i ∈ Finset.range (N - 1),
        (w (i + 1) - w i) * ∑ j ∈ Finset.range (i + 1), g j| := abs_sub _ _
    _ ≤ |w (N - 1)| * B + ∑ i ∈ Finset.range (N - 1), |w (i + 1) - w i| * B := by
        refine add_le_add ?_ ?_
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB N le_rfl) (abs_nonneg _)
        · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_left (hB (i + 1) ?_) (abs_nonneg _)
          have := Finset.mem_range.mp hi
          omega
    _ = B * (|w (N - 1)| + ∑ i ∈ Finset.range (N - 1), |w (i + 1) - w i|) := by
        rw [← Finset.sum_mul]; ring

theorem abs_sum_range_le_of_partialSumPowerBound {g : ℕ → ℝ} {a C : ℝ} (ha : 0 ≤ a)
    (hC : ∀ N : ℕ, |∑ n ∈ Finset.range N, g n| ≤ C * ((N : ℝ) + 1) ^ a) (hC0 : 0 ≤ C)
    (N : ℕ) : ∀ k, k ≤ N → |∑ j ∈ Finset.range k, g j| ≤ C * ((N : ℝ) + 1) ^ a := by
  intro k hk
  refine (hC k).trans (mul_le_mul_of_nonneg_left ?_ hC0)
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1) ha

/-- The weight `log(n+1)`. -/
theorem PartialSumPowerBound.log_weight {g : ℕ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ)
    (hg : PartialSumPowerBound g θ) :
    PartialSumPowerBound (fun n => Real.log ((n : ℝ) + 1) * g n) θ := by
  intro δ hδ
  obtain ⟨C, hC0, hC⟩ := hg (δ / 2) (by linarith)
  refine ⟨4 * C / δ, by positivity, fun N => ?_⟩
  set w : ℕ → ℝ := fun n => Real.log ((n : ℝ) + 1) with hw
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [N.cast_nonneg (α := ℝ)]
  have hwmono : ∀ i, w i ≤ w (i + 1) := fun i => by
    simp only [hw]
    exact Real.log_le_log (by positivity) (by push_cast; linarith)
  have hwlast : |w (N - 1)| ≤ Real.log ((N : ℝ) + 1) := by
    simp only [hw]
    rw [abs_of_nonneg (Real.log_nonneg (by linarith [(N - 1 : ℕ).cast_nonneg (α := ℝ)]))]
    exact Real.log_le_log (by positivity)
      (by have : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
          linarith)
  have hvar : ∑ i ∈ Finset.range (N - 1), |w (i + 1) - w i| ≤ Real.log ((N : ℝ) + 1) := by
    rw [Finset.sum_congr rfl fun i _ => abs_of_nonneg (sub_nonneg.mpr (hwmono i)),
      Finset.sum_range_sub (fun i => w i) (N - 1)]
    have : w 0 = 0 := by simp [hw]
    rw [this, sub_zero]
    exact le_trans (le_abs_self _) hwlast
  have hlog : Real.log ((N : ℝ) + 1) ≤ ((N : ℝ) + 1) ^ (δ / 2) / (δ / 2) :=
    Real.log_le_rpow_div (by positivity) (by linarith)
  have hab := abs_sum_range_mul_le_of_partial g w N
    (abs_sum_range_le_of_partialSumPowerBound (by linarith) hC hC0 N)
  have hP : 0 ≤ C * ((N : ℝ) + 1) ^ (θ + δ / 2) := by positivity
  calc |∑ n ∈ Finset.range N, Real.log ((n : ℝ) + 1) * g n|
      ≤ C * ((N : ℝ) + 1) ^ (θ + δ / 2) * (|w (N - 1)| +
          ∑ i ∈ Finset.range (N - 1), |w (i + 1) - w i|) := hab
    _ ≤ C * ((N : ℝ) + 1) ^ (θ + δ / 2) * (2 * (((N : ℝ) + 1) ^ (δ / 2) / (δ / 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ hP
        linarith
    _ = 4 * C / δ * (((N : ℝ) + 1) ^ (θ + δ / 2) * ((N : ℝ) + 1) ^ (δ / 2)) := by
        field_simp
        ring
    _ = 4 * C / δ * ((N : ℝ) + 1) ^ (θ + δ) := by
        rw [← Real.rpow_add (by positivity)]
        ring_nf

/-- `Σ_{i<M} |1/log(i+2) − 1/log(i+1)| ≤ 2/log 2` (with `1/log 1 = 0`). -/
theorem sum_range_abs_inv_log_sub_le (M : ℕ) :
    ∑ i ∈ Finset.range M, |(Real.log (((i + 1 : ℕ) : ℝ) + 1))⁻¹ - (Real.log ((i : ℝ) + 1))⁻¹|
      ≤ 2 * (Real.log 2)⁻¹ := by
  set v : ℕ → ℝ := fun n => (Real.log ((n : ℝ) + 1))⁻¹ with hv
  have hv0 : ∀ n, 0 ≤ v n := fun n => by
    simp only [hv]; exact inv_nonneg.mpr (Real.log_nonneg (by linarith [n.cast_nonneg (α := ℝ)]))
  have hv1 : v 1 = (Real.log 2)⁻¹ := by simp only [hv]; norm_num
  have hanti : ∀ n, 1 ≤ n → v (n + 1) ≤ v n := fun n hn => by
    simp only [hv]
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact inv_anti₀ (Real.log_pos (by linarith)) (Real.log_le_log (by linarith) (by push_cast; linarith))
  have key : ∀ M, 1 ≤ M → ∑ i ∈ Finset.range M, |v (i + 1) - v i| = 2 * v 1 - v M := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base =>
      have h0 : v 0 = 0 := by simp [hv]
      simp [h0, abs_of_nonneg (hv0 1)]
      ring
    | succ n hn ih =>
      rw [Finset.sum_range_succ, ih, abs_of_nonpos (sub_nonpos.mpr (hanti n hn))]
      ring
  change ∑ i ∈ Finset.range M, |v (i + 1) - v i| ≤ 2 * (Real.log 2)⁻¹
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp only [Finset.range_zero, Finset.sum_empty]
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr (Real.log_nonneg (by norm_num)))
  · rw [key M hM, hv1]
    linarith [hv0 M]

theorem inv_log_two_le : (Real.log 2)⁻¹ ≤ 3 / 2 := by
  rw [inv_le_comm₀ (Real.log_pos (by norm_num)) (by norm_num)]
  linarith [Real.log_two_gt_d9]

/-- The weight `1/log(n+1)` (with `1/log 1 = 0`). -/
theorem PartialSumPowerBound.inv_log_weight {g : ℕ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ)
    (hg : PartialSumPowerBound g θ) :
    PartialSumPowerBound (fun n => (Real.log ((n : ℝ) + 1))⁻¹ * g n) θ := by
  intro δ hδ
  obtain ⟨C, hC0, hC⟩ := hg δ hδ
  refine ⟨5 * C, by positivity, fun N => ?_⟩
  set w : ℕ → ℝ := fun n => (Real.log ((n : ℝ) + 1))⁻¹ with hw
  have hwle : ∀ n, |w n| ≤ 2 := fun n => by
    simp only [hw]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [abs_of_nonneg (inv_nonneg.mpr (Real.log_nonneg (by linarith)))]
      calc (Real.log ((n : ℝ) + 1))⁻¹ ≤ (Real.log 2)⁻¹ :=
            inv_anti₀ (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) (by linarith))
        _ ≤ 2 := by linarith [inv_log_two_le]
  have hvar : ∑ i ∈ Finset.range (N - 1), |w (i + 1) - w i| ≤ 3 := by
    have := sum_range_abs_inv_log_sub_le (N - 1)
    linarith [inv_log_two_le]
  have hab := abs_sum_range_mul_le_of_partial g w N
    (abs_sum_range_le_of_partialSumPowerBound (by linarith) hC hC0 N)
  have hP : 0 ≤ C * ((N : ℝ) + 1) ^ (θ + δ) := by positivity
  calc |∑ n ∈ Finset.range N, (Real.log ((n : ℝ) + 1))⁻¹ * g n|
      ≤ C * ((N : ℝ) + 1) ^ (θ + δ) * (|w (N - 1)| +
          ∑ i ∈ Finset.range (N - 1), |w (i + 1) - w i|) := hab
    _ ≤ C * ((N : ℝ) + 1) ^ (θ + δ) * 5 := by
        refine mul_le_mul_of_nonneg_left ?_ hP
        linarith [hwle (N - 1)]
    _ = 5 * C * ((N : ℝ) + 1) ^ (θ + δ) := by ring

/-! ## The regularized coefficients -/

/-- `(Λ(n+1) − 1)/log(n+1)`, the pole-regularized coefficients of `log ζ` (the entry `n = 0`
is `0`). -/
def logZetaRegCoeff (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt (n + 1) - 1) / Real.log ((n : ℝ) + 1)

/-- `1_P(n+1) − 1/log(n+1)`, the pole-regularized prime zeta coefficients (the entry `n = 0`
is `0`). -/
def primeRegCoeff (n : ℕ) : ℝ :=
  (if (n + 1).Prime then 1 else 0) - (Real.log ((n : ℝ) + 1))⁻¹

theorem logZetaRegCoeff_eq (n : ℕ) :
    logZetaRegCoeff n = (Real.log ((n : ℝ) + 1))⁻¹ * vonMangoldtMinusOne n := by
  rw [logZetaRegCoeff, vonMangoldtMinusOne, div_eq_inv_mul]

theorem vonMangoldtMinusOne_eq_log_mul (n : ℕ) :
    vonMangoldtMinusOne n =
      Real.log ((n : ℝ) + 1) * logZetaRegCoeff n + (if n = 0 then -1 else 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [vonMangoldtMinusOne, logZetaRegCoeff, ArithmeticFunction.vonMangoldt_apply_one]
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : Real.log ((n : ℝ) + 1) ≠ 0 := (Real.log_pos (by linarith)).ne'
    rw [if_neg hn.ne', add_zero, logZetaRegCoeff, vonMangoldtMinusOne]
    field_simp

theorem partialSumPowerBound_vonMangoldtMinusOne_iff {θ : ℝ} (hθ : 0 ≤ θ) :
    PartialSumPowerBound vonMangoldtMinusOne θ ↔ PartialSumPowerBound logZetaRegCoeff θ := by
  constructor
  · intro h
    have h1 := h.inv_log_weight hθ
    simp only [← logZetaRegCoeff_eq] at h1
    exact h1
  · intro h
    have h2 : PartialSumPowerBound (fun n : ℕ => if n = 0 then (-1 : ℝ) else 0) θ := by
      refine partialSumPowerBound_of_abs_le (B := 1) hθ fun N => ?_
      rw [Finset.sum_ite_eq' (Finset.range N) 0 (fun _ => (-1 : ℝ))]
      split_ifs <;> norm_num
    have := (h.log_weight hθ).add h2
    simp only [← vonMangoldtMinusOne_eq_log_mul] at this
    exact this

/-! ## The prime-power defect -/

/-- `Λ(n+1)/log(n+1) − 1_P(n+1)`: equal to `1/k` at `n + 1 = p^k`, `k ≥ 2`, and `0` otherwise. -/
def logPrimePowerDefect (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt (n + 1) / Real.log ((n : ℝ) + 1) - (if (n + 1).Prime then 1 else 0)

theorem logZetaRegCoeff_sub_primeRegCoeff (n : ℕ) :
    logZetaRegCoeff n - primeRegCoeff n = logPrimePowerDefect n := by
  unfold logZetaRegCoeff primeRegCoeff logPrimePowerDefect
  ring

theorem sum_range_succ_eq_sum_Ioc (f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, f (n + 1) = ∑ m ∈ Finset.Ioc 0 N, f m := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, Finset.sum_Ioc_succ_top (Nat.zero_le N)]

theorem logPrimePowerDefect_nonneg_le (n : ℕ) :
    0 ≤ logPrimePowerDefect n ∧ logPrimePowerDefect n ≤ (Real.log 2)⁻¹ *
      (ArithmeticFunction.vonMangoldt (n + 1) -
        (if (n + 1).Prime then Real.log (((n + 1 : ℕ) : ℝ)) else 0)) := by
  unfold logPrimePowerDefect
  by_cases hp : (n + 1).Prime
  · have hl : Real.log ((n : ℝ) + 1) ≠ 0 := by
      have : (1 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hp.one_lt
      push_cast at this
      exact (Real.log_pos this).ne'
    rw [if_pos hp, if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    push_cast
    rw [div_self hl]
    simp
  · rw [if_neg hp, if_neg hp, sub_zero, sub_zero]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ArithmeticFunction.vonMangoldt_apply_one]
    · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hΛ := (ArithmeticFunction.vonMangoldt_nonneg (n := n + 1))
      have hl2 : Real.log 2 ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by norm_num) (by linarith)
      have hl2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
      refine ⟨div_nonneg hΛ (by linarith), ?_⟩
      rw [inv_mul_eq_div]
      exact div_le_div_of_nonneg_left hΛ hl2p hl2

theorem sum_range_logPrimePowerDefect_le (N : ℕ) :
    0 ≤ ∑ n ∈ Finset.range N, logPrimePowerDefect n ∧
      ∑ n ∈ Finset.range N, logPrimePowerDefect n ≤
        (Real.log 2)⁻¹ * (Chebyshev.psi N - Chebyshev.theta N) := by
  refine ⟨Finset.sum_nonneg fun n _ => (logPrimePowerDefect_nonneg_le n).1, ?_⟩
  refine (Finset.sum_le_sum fun n _ => (logPrimePowerDefect_nonneg_le n).2).trans (le_of_eq ?_)
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_sub_distrib, Chebyshev.psi, Chebyshev.theta, Nat.floor_natCast,
    Finset.sum_filter]
  rw [sum_range_succ_eq_sum_Ioc (fun m => ArithmeticFunction.vonMangoldt m) N,
    sum_range_succ_eq_sum_Ioc (fun m => if m.Prime then Real.log (m : ℝ) else 0) N]

theorem partialSumPowerBound_logPrimePowerDefect : PartialSumPowerBound logPrimePowerDefect (1 / 2) := by
  intro δ hδ
  refine ⟨3 / δ, by positivity, fun N => ?_⟩
  obtain ⟨h0, h1⟩ := sum_range_logPrimePowerDefect_le N
  rw [abs_of_nonneg h0]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Finset.range_zero, Finset.sum_empty]; positivity
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpt := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hN'
  have hsqrt : Real.sqrt N ≤ ((N : ℝ) + 1) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have hlog : Real.log N ≤ ((N : ℝ) + 1) ^ δ / δ :=
    (Real.log_le_log (by linarith) (by linarith)).trans
      (Real.log_le_rpow_div (by positivity) hδ)
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN'
  have hinv := inv_log_two_le
  have hinv0 : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr (Real.log_nonneg (by norm_num))
  calc ∑ n ∈ Finset.range N, logPrimePowerDefect n
      ≤ (Real.log 2)⁻¹ * (Chebyshev.psi N - Chebyshev.theta N) := h1
    _ ≤ (Real.log 2)⁻¹ * (2 * Real.sqrt N * Real.log N) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans hpt) hinv0
    _ ≤ 3 / 2 * (2 * (((N : ℝ) + 1) ^ (1 / 2 : ℝ) * (((N : ℝ) + 1) ^ δ / δ))) := by
        rw [mul_assoc 2]
        refine mul_le_mul hinv (mul_le_mul_of_nonneg_left
          (mul_le_mul hsqrt hlog hlog0 (by positivity)) (by norm_num)) (by positivity)
          (by norm_num)
    _ = 3 / δ * (((N : ℝ) + 1) ^ (1 / 2 : ℝ) * ((N : ℝ) + 1) ^ δ) := by
        field_simp
    _ = 3 / δ * ((N : ℝ) + 1) ^ (1 / 2 + δ) := by rw [← Real.rpow_add (by positivity)]

theorem partialSumPowerBound_primeRegCoeff_iff {θ : ℝ} (hθ : 1 / 2 ≤ θ) :
    PartialSumPowerBound primeRegCoeff θ ↔ PartialSumPowerBound logZetaRegCoeff θ := by
  have hd := partialSumPowerBound_logPrimePowerDefect.mono hθ
  constructor
  · intro h
    have := h.add hd
    convert this using 1
    funext n
    rw [← logZetaRegCoeff_sub_primeRegCoeff]
    ring
  · intro h
    have := h.sub hd
    convert this using 1
    funext n
    rw [← logZetaRegCoeff_sub_primeRegCoeff]
    ring

/-! ## The abscissa laws -/

/-- **The regularized `log ζ` series.**  For `α ≥ 0`, every zero of `ξ` has `Re ρ ≤ ½ + α` iff
`Σ_{n ≥ 2} ((Λ(n) − 1)/log n) n^{-σ}` converges at every real `σ > ½ + α`. -/
theorem xiZeroHalfPlaneBound_iff_logZetaRegCoeff_converges {α : ℝ} (hα : 0 ≤ α) :
    XiZeroHalfPlaneBound α ↔ ConvergesRightOf logZetaRegCoeff (1 / 2 + α) := by
  have hθ : (0 : ℝ) ≤ 1 / 2 + α := by linarith
  exact (xiZeroHalfPlaneBound_iff_vonMangoldtMinusOne_converges hα).trans
    ((partialSumPowerBound_iff_convergesRightOf _ hθ).symm.trans
      ((partialSumPowerBound_vonMangoldtMinusOne_iff hθ).trans
        (partialSumPowerBound_iff_convergesRightOf _ hθ)))

/-- **The regularized prime zeta series.**  For `α ≥ 0`, every zero of `ξ` has `Re ρ ≤ ½ + α`
iff `Σ_{n ≥ 2} (1_P(n) − 1/log n) n^{-σ}` converges at every real `σ > ½ + α`. -/
theorem xiZeroHalfPlaneBound_iff_primeRegCoeff_converges {α : ℝ} (hα : 0 ≤ α) :
    XiZeroHalfPlaneBound α ↔ ConvergesRightOf primeRegCoeff (1 / 2 + α) := by
  have hθ : (0 : ℝ) ≤ 1 / 2 + α := by linarith
  rw [xiZeroHalfPlaneBound_iff_logZetaRegCoeff_converges hα,
    ← partialSumPowerBound_iff_convergesRightOf _ hθ,
    ← partialSumPowerBound_iff_convergesRightOf _ hθ,
    partialSumPowerBound_primeRegCoeff_iff (by linarith)]

theorem riemannHypothesis_iff_logZetaRegCoeff_converges :
    RiemannHypothesis ↔ ConvergesRightOf logZetaRegCoeff (1 / 2) := by
  rw [riemannHypothesis_iff_xiZeroHalfPlaneBound_zero,
    xiZeroHalfPlaneBound_iff_logZetaRegCoeff_converges le_rfl, add_zero]

theorem riemannHypothesis_iff_primeRegCoeff_converges :
    RiemannHypothesis ↔ ConvergesRightOf primeRegCoeff (1 / 2) := by
  rw [riemannHypothesis_iff_xiZeroHalfPlaneBound_zero,
    xiZeroHalfPlaneBound_iff_primeRegCoeff_converges le_rfl, add_zero]

end

end RHTower
