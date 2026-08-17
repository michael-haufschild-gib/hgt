import GaloisForLFunctions.HTGeometry.PolydiscAnalytic

/-!
# Vanishing Cauchy coefficients and the multi-index Schwarz estimate

The count of a Siegel-type argument produces vanishing of the *multi-index* Cauchy coefficients up
to a total degree, not of the tuple-indexed iterated derivatives — the difference matters, since
the number of multi-indices of degree below `N` in `n` variables grows like `N^n` whereas the
number of derivative tuples grows like `n^N`.

* **`polydiscSeries_eq_zero_of_coeff_vanish`** — vanishing coefficients of a degree kill that term
  of the series;
* **`norm_le_of_polydiscCoeff_vanish`** — hence the function is smaller than its torus bound by the
  factor `(N+1)^n·(r/R)^N` on the smaller polydisc.
-/

open MeasureTheory Complex Set
open scoped Real

namespace GaloisForLFunctions.HTGeometry

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Vanishing coefficients of one degree kill that term of the series.** -/
theorem polydiscSeries_eq_zero_of_coeff_vanish {f : (Fin n → ℂ) → E} (c : Fin n → ℂ) (R : ℝ)
    {k : ℕ} (h : ∀ m : Fin n → ℕ, ∑ i, m i = k → polydiscCoeff f c R m = 0) :
    polydiscSeries f c R k = 0 := by
  rw [polydiscSeries]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [h m.1 (Finset.Nat.mem_antidiagonalTuple.1 m.2)]
  ext v
  simp

/-- **The multi-index Schwarz estimate, from the polydisc expansion.**  Vanishing of every Cauchy
coefficient of total degree below `N` makes the function smaller than its torus bound by the factor
`(N+1)^n·(r/R)^N` on the smaller polydisc.  The expansion of the function into its polydisc series
is taken as a hypothesis, so the estimate applies to a function holomorphic only near the polydisc
as well as to a globally holomorphic one. -/
theorem norm_le_of_polydiscCoeff_vanish_of_hasSum [CompleteSpace E] {N : ℕ}
    {f : (Fin n → ℂ) → E}
    (c : Fin n → ℂ) {R r M : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (hM : ∀ θ : Fin n → ℝ, ‖f (torusMap c (fun _ => R) θ)‖ ≤ M)
    (hvan : ∀ m : Fin n → ℕ, ∑ i, m i < N → polydiscCoeff f c R m = 0)
    {y : Fin n → ℂ} (hy : ‖y‖ ≤ r)
    (hsum : HasSum (fun k => polydiscSeries f c R k fun _ => y) (f (c + y))) :
    ‖f (c + y)‖ ≤ M * (((N + 1) ^ n : ℕ) : ℝ) * (r / R) ^ N *
      ∑' j : ℕ, (((j + 1) ^ n : ℕ) : ℝ) * (r / R) ^ j := by
  classical
  set q : ℝ := r / R with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hqdef, div_lt_one hR]; exact hrR
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM fun _ => 0)
  have hbound : ∀ k : ℕ, ‖polydiscSeries f c R k fun _ => y‖
      ≤ (((k + 1) ^ n : ℕ) : ℝ) * M * q ^ k := by
    intro k
    have h1 : ‖polydiscSeries f c R k fun _ => y‖
        ≤ ‖polydiscSeries f c R k‖ * ‖y‖ ^ k := by
      have := (polydiscSeries f c R k).le_opNorm (fun _ : Fin k => y)
      simpa using this
    have h2 : ‖polydiscSeries f c R k‖ ≤ (((k + 1) ^ n : ℕ) : ℝ) * (M / R ^ k) :=
      norm_polydiscSeries_le c hR hM k
    have h3 : ‖y‖ ^ k ≤ r ^ k := pow_le_pow_left₀ (norm_nonneg y) hy k
    calc ‖polydiscSeries f c R k fun _ => y‖
        ≤ ‖polydiscSeries f c R k‖ * ‖y‖ ^ k := h1
      _ ≤ ((((k + 1) ^ n : ℕ) : ℝ) * (M / R ^ k)) * r ^ k := by
          refine mul_le_mul h2 h3 (by positivity) (by positivity)
      _ = (((k + 1) ^ n : ℕ) : ℝ) * M * q ^ k := by
          rw [hqdef, div_pow]
          field_simp
  have hmaj : Summable fun k : ℕ => (((k + 1) ^ n : ℕ) : ℝ) * M * q ^ k := by
    have := (summable_succ_pow_mul_geometric n hq0 hq1).mul_right M
    refine this.congr fun k => ?_
    ring
  have hsummable : Summable fun k : ℕ => ‖polydiscSeries f c R k fun _ => y‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hbound hmaj
  have hzeroterm : ∀ k, k < N → (polydiscSeries f c R k fun _ => y) = 0 := by
    intro k hk
    have := polydiscSeries_eq_zero_of_coeff_vanish (f := f) c R
      (k := k) (fun m hm => hvan m (by rw [hm]; exact hk))
    rw [this]
    simp
  have hsplit := hsummable.sum_add_tsum_nat_add N
  have hfin : ∑ i ∈ Finset.range N, ‖polydiscSeries f c R i fun _ => y‖ = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [hzeroterm i (Finset.mem_range.mp hi)]
    simp
  have htailbound : ∀ j : ℕ, ‖polydiscSeries f c R (j + N) fun _ => y‖
      ≤ (M * (((N + 1) ^ n : ℕ) : ℝ) * q ^ N) * ((((j + 1) ^ n : ℕ) : ℝ) * q ^ j) := by
    intro j
    refine (hbound (j + N)).trans ?_
    have hcard : (((j + N + 1) ^ n : ℕ) : ℝ)
        ≤ (((N + 1) ^ n : ℕ) : ℝ) * (((j + 1) ^ n : ℕ) : ℝ) := by
      have hnat : (j + N + 1) ^ n ≤ (N + 1) ^ n * (j + 1) ^ n := by
        rw [← Nat.mul_pow]
        exact Nat.pow_le_pow_left (by nlinarith) n
      exact_mod_cast hnat
    have hpow : q ^ (j + N) = q ^ N * q ^ j := by rw [pow_add]; ring
    calc (((j + N + 1) ^ n : ℕ) : ℝ) * M * q ^ (j + N)
        ≤ ((((N + 1) ^ n : ℕ) : ℝ) * (((j + 1) ^ n : ℕ) : ℝ)) * M * (q ^ N * q ^ j) := by
          rw [hpow]
          gcongr
      _ = (M * (((N + 1) ^ n : ℕ) : ℝ) * q ^ N) * ((((j + 1) ^ n : ℕ) : ℝ) * q ^ j) := by ring
  have hshiftsum : Summable fun j : ℕ => ‖polydiscSeries f c R (j + N) fun _ => y‖ :=
    hsummable.comp_injective (add_left_injective N)
  have hmaj2 : Summable fun j : ℕ =>
      (M * (((N + 1) ^ n : ℕ) : ℝ) * q ^ N) * ((((j + 1) ^ n : ℕ) : ℝ) * q ^ j) :=
    (summable_succ_pow_mul_geometric n hq0 hq1).mul_left _
  calc ‖f (c + y)‖ = ‖∑' k : ℕ, (polydiscSeries f c R k fun _ => y)‖ := by rw [hsum.tsum_eq]
    _ ≤ ∑' k : ℕ, ‖polydiscSeries f c R k fun _ => y‖ := norm_tsum_le_tsum_norm hsummable
    _ = ∑' j : ℕ, ‖polydiscSeries f c R (j + N) fun _ => y‖ := by
        rw [← hsplit, hfin, zero_add]
    _ ≤ ∑' j : ℕ, (M * (((N + 1) ^ n : ℕ) : ℝ) * q ^ N) * ((((j + 1) ^ n : ℕ) : ℝ) * q ^ j) :=
        Summable.tsum_le_tsum htailbound hshiftsum hmaj2
    _ = M * (((N + 1) ^ n : ℕ) : ℝ) * q ^ N *
          ∑' j : ℕ, (((j + 1) ^ n : ℕ) : ℝ) * q ^ j := by
        rw [tsum_mul_left]

/-- **The multi-index Schwarz estimate** for a globally holomorphic function. -/
theorem norm_le_of_polydiscCoeff_vanish [CompleteSpace E] {N : ℕ} {f : (Fin n → ℂ) → E}
    (hf : Differentiable ℂ f) (c : Fin n → ℂ) {R r M : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (hM : ∀ θ : Fin n → ℝ, ‖f (torusMap c (fun _ => R) θ)‖ ≤ M)
    (hvan : ∀ m : Fin n → ℕ, ∑ i, m i < N → polydiscCoeff f c R m = 0)
    {y : Fin n → ℂ} (hy : ‖y‖ ≤ r) :
    ‖f (c + y)‖ ≤ M * (((N + 1) ^ n : ℕ) : ℝ) * (r / R) ^ N *
      ∑' j : ℕ, (((j + 1) ^ n : ℕ) : ℝ) * (r / R) ^ j :=
  norm_le_of_polydiscCoeff_vanish_of_hasSum c hR hr hrR hM hvan hy
    (polydiscSeries_hasSum hf c hR hM (lt_of_le_of_lt hy hrR))

/-- **The Cauchy coefficient is linear in the function.**  A finite linear combination of functions
has the corresponding combination of coefficients, so a coefficient of a prescribed multi-index is a
linear functional of the coefficient vector — which is what the counting step needs. -/
theorem polydiscCoeff_sum_smul [CompleteSpace E] {ι : Type*} (s : Finset ι)
    (g : ι → (Fin n → ℂ) → E) (a : ι → ℂ) (c : Fin n → ℂ) {R : ℝ} (hR : 0 < R)
    (hg : ∀ j ∈ s, Continuous fun θ : Fin n → ℝ => g j (torusMap c (fun _ => R) θ))
    (m : Fin n → ℕ) :
    polydiscCoeff (fun z => ∑ j ∈ s, a j • g j z) c R m
      = ∑ j ∈ s, a j • polydiscCoeff (g j) c R m := by
  classical
  have hfun : ∀ ζ : Fin n → ℂ,
      (∏ i, (ζ i - c i) ^ (m i + 1))⁻¹ • (∑ j ∈ s, a j • g j ζ)
        = ∑ j ∈ s, a j • ((∏ i, (ζ i - c i) ^ (m i + 1))⁻¹ • g j ζ) := by
    intro ζ
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_comm]
  have hint : ∀ j ∈ s, TorusIntegrable
      (fun ζ => a j • ((∏ i, (ζ i - c i) ^ (m i + 1))⁻¹ • g j ζ)) c (fun _ => R) :=
    fun j hj => (polydiscCoeff_integrable (hg j hj) hR m).smul (a j)
  rw [polydiscCoeff]
  simp_rw [hfun]
  rw [torusIntegral_finsetSum s _ hint, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [polydiscCoeff, torusIntegral_smul, smul_comm]

end GaloisForLFunctions.HTGeometry
