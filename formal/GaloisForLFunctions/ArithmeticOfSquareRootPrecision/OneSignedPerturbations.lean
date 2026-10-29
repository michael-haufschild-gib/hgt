import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheGaugeStabilizerOfTheCount

/-!
# One-signed perturbations: majorants, minorants and abscissas

**Majorants and minorants.** The upper half of the count is antitone and the lower half monotone
in the weight. Since each half for `Λ` is RH:

* an upper count for any **majorant** `b ≥ Λ` proves RH (`riemannHypothesis_of_majorant`), and a
  lower count for any **minorant** `a ≤ Λ` proves RH (`riemannHypothesis_of_minorant`);
* for a weight above `Λ`, the count is RH together with `b − Λ ∈ 𝒬`
  (`count_iff_of_vonMangoldt_le`).

A sieve majorant of the primes carries information at square-root precision only if it is RH.

**Precision exponents are abscissas.** For a nonnegative perturbation `δ`:
* partial sums `O(x^θ)`, `θ ≥ 0`, give absolute convergence of `Σ δ(n) n^{−s}` on `Re s > θ`
  (`abscissaOfAbsConv_le_of_partialSum_isBigO`);
* absolute convergence at `σ ≥ 0` gives partial sums `≤ x^σ Σ δ(n) n^{−σ}`
  (`partialSum_isBigO_of_abscissaOfAbsConv_lt`).

So the square-root class meets the cone of nonnegative perturbations between the half-planes
`Re s > ½` (`mem_sqrtClass_of_abscissaOfAbsConv_lt_half`,
`abscissaOfAbsConv_le_half_of_mem_sqrtClass`): a one-signed perturbation is invisible to the count
when its Dirichlet series converges absolutely beyond `½`, and visible when its abscissa exceeds `½`
(`not_count_add_of_half_lt_abscissaOfAbsConv`).
-/

noncomputable section

open Filter Asymptotics Real Finset

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

/-! ### Majorants and minorants -/

/-- **The upper half is antitone in the weight.** -/
theorem upperCount_anti {a b : ℕ → ℝ} (hab : ∀ n, a n ≤ b n) (hb : UpperCount b) :
    UpperCount a := by
  obtain ⟨C, hC⟩ := hb
  refine ⟨C, hC.mono fun x hx => le_trans ?_ hx⟩
  have : partialSum a x ≤ partialSum b x := sum_le_sum fun n _ => hab n
  linarith

/-- **An upper count for a majorant of `Λ` is RH.** -/
theorem riemannHypothesis_of_majorant {b : ℕ → ℝ} (hb : ∀ n, vonMangoldtWeight n ≤ b n)
    (h : UpperCount b) : RiemannHypothesis :=
  upperCount_vonMangoldt_iff.mp (upperCount_anti hb h)

/-- **A lower count for a minorant of `Λ` is RH.** -/
theorem riemannHypothesis_of_minorant {a : ℕ → ℝ} (ha : ∀ n, a n ≤ vonMangoldtWeight n)
    (h : LowerCount a) : RiemannHypothesis :=
  lowerCount_vonMangoldt_iff.mp (lowerCount_mono ha h)

/-- **Weights above `Λ`**: the count is RH together with `b − Λ ∈ 𝒬`. -/
theorem count_iff_of_vonMangoldt_le {b : ℕ → ℝ} (hb : ∀ n, vonMangoldtWeight n ≤ b n) :
    Count b ↔ RiemannHypothesis ∧ b - vonMangoldtWeight ∈ sqrtClass := by
  constructor
  · intro h
    have hRH := riemannHypothesis_of_majorant hb (count_iff_upperCount_and_lowerCount.mp h).1
    exact ⟨hRH, sub_mem_sqrtClass_of_count (count_vonMangoldt_iff.mpr hRH) h⟩
  · rintro ⟨hRH, hδ⟩
    have := (count_add_iff_mem_sqrtClass (count_vonMangoldt_iff.mpr hRH) _).mpr hδ
    simpa using this

/-! ### Precision exponents are abscissas -/

theorem partialSum_natCast_eq_sum_Icc (δ : ℕ → ℝ) (n : ℕ) :
    partialSum δ n = ∑ k ∈ Icc 1 n, δ k := by
  unfold partialSum
  rw [Nat.floor_natCast]
  congr 1

/-- **Partial sums `O(x^θ)` give absolute convergence beyond `θ`.** -/
theorem abscissaOfAbsConv_le_of_partialSum_isBigO {δ : ℕ → ℝ} (hδ : ∀ n, 0 ≤ δ n) {θ : ℝ}
    (hθ : 0 ≤ θ) (h : partialSum δ =O[atTop] fun x => x ^ θ) :
    LSeries.abscissaOfAbsConv (fun n => (δ n : ℂ)) ≤ θ := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  have hnat : (fun n : ℕ => ∑ k ∈ Icc 1 n, δ k) =O[atTop] fun n : ℕ => (n : ℝ) ^ θ := by
    have := h.comp_tendsto tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, partialSum_natCast_eq_sum_Icc] using this
  exact LSeriesSummable_of_sum_norm_bigO_and_nonneg hnat hδ hθ (by simpa using hy)

/-- **Absolute convergence at `σ ≥ 0` bounds the partial sums by `x^σ`.** -/
theorem partialSum_isBigO_of_abscissaOfAbsConv_lt {δ : ℕ → ℝ} (hδ : ∀ n, 0 ≤ δ n) {σ : ℝ}
    (hσ : 0 ≤ σ) (h : LSeries.abscissaOfAbsConv (fun n => (δ n : ℂ)) < σ) :
    partialSum δ =O[atTop] fun x => x ^ σ := by
  have hsum := LSeries.summable_real_of_abscissaOfAbsConv_lt (f := δ) h
  refine IsBigO.of_bound (∑' n, δ n / (n : ℝ) ^ σ) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  rw [Real.norm_of_nonneg (partialSum_nonneg hδ x), Real.norm_of_nonneg (Real.rpow_nonneg hx0.le σ)]
  have hterm : ∀ n ∈ Ioc 0 ⌊x⌋₊, δ n ≤ x ^ σ * (δ n / (n : ℝ) ^ σ) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.mp hn).1
    have hnx : (n : ℝ) ≤ x := (Nat.cast_le.mpr (mem_Ioc.mp hn).2).trans (Nat.floor_le hx0.le)
    have hpow : (n : ℝ) ^ σ ≤ x ^ σ := Real.rpow_le_rpow hn0.le hnx hσ
    have hnσ : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hn0 σ
    rw [mul_div_assoc', le_div_iff₀ hnσ]
    calc δ n * (n : ℝ) ^ σ ≤ δ n * x ^ σ := mul_le_mul_of_nonneg_left hpow (hδ n)
      _ = x ^ σ * δ n := mul_comm _ _
  calc partialSum δ x ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, x ^ σ * (δ n / (n : ℝ) ^ σ) := sum_le_sum hterm
    _ = x ^ σ * ∑ n ∈ Ioc 0 ⌊x⌋₊, δ n / (n : ℝ) ^ σ := by rw [mul_sum]
    _ ≤ x ^ σ * ∑' n, δ n / (n : ℝ) ^ σ := by
        refine mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ fun n _ => ?_)
          (Real.rpow_nonneg hx0.le σ)
        exact div_nonneg (hδ n) (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
    _ = (∑' n, δ n / (n : ℝ) ^ σ) * x ^ σ := mul_comm _ _

/-- A nonnegative perturbation whose Dirichlet series converges absolutely beyond `½` lies in `𝒬`. -/
theorem mem_sqrtClass_of_abscissaOfAbsConv_lt_half {δ : ℕ → ℝ} (hδ : ∀ n, 0 ≤ δ n)
    (h : LSeries.abscissaOfAbsConv (fun n => (δ n : ℂ)) < (1 / 2 : ℝ)) : δ ∈ sqrtClass := by
  refine (partialSum_isBigO_of_abscissaOfAbsConv_lt hδ (by norm_num) h).trans
    (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_ge_atTop (exp 1)] with x hx
  have hx0 : 0 ≤ x := le_trans (exp_pos 1).le hx
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0 _), Real.norm_of_nonneg (sqrtScale_nonneg x),
    one_mul, ← Real.sqrt_eq_rpow]
  exact sqrt_le_sqrtScale hx

/-- A nonnegative perturbation in `𝒬` has abscissa of absolute convergence at most `½`. -/
theorem abscissaOfAbsConv_le_half_of_mem_sqrtClass {δ : ℕ → ℝ} (hδ : ∀ n, 0 ≤ δ n)
    (h : δ ∈ sqrtClass) : LSeries.abscissaOfAbsConv (fun n => (δ n : ℂ)) ≤ (1 / 2 : ℝ) := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  have hθ : partialSum δ =O[atTop] fun x => x ^ ((1 / 2 + y) / 2) :=
    (h : partialSum δ =O[atTop] sqrtScale).trans
      (sqrtScale_isLittleO_rpow (η := 1 - (1 / 2 + y) / 2) (by linarith)).isBigO |>.congr_right
        fun x => by rw [sub_sub_cancel]
  exact LSeriesSummable_of_abscissaOfAbsConv_lt_re
    ((abscissaOfAbsConv_le_of_partialSum_isBigO hδ (by linarith) hθ).trans_lt
      (by simp only [Complex.ofReal_re]; exact_mod_cast (by linarith : (1 / 2 + y) / 2 < y)))

/-- **Visibility by abscissa**: if `a` satisfies the count and `δ ≥ 0` has abscissa of absolute
convergence beyond `½`, then `a + δ` fails the count. -/
theorem not_count_add_of_half_lt_abscissaOfAbsConv {a δ : ℕ → ℝ} (ha : Count a)
    (hδ : ∀ n, 0 ≤ δ n) (h : ((1 / 2 : ℝ) : EReal) < LSeries.abscissaOfAbsConv (fun n => (δ n : ℂ))) :
    ¬ Count (a + δ) := fun h' =>
  not_le.mpr h (abscissaOfAbsConv_le_half_of_mem_sqrtClass hδ
    ((count_add_iff_mem_sqrtClass ha δ).mp h'))

/-- **Invisibility by abscissa**: a nonnegative perturbation converging absolutely beyond `½`
preserves the count. -/
theorem count_add_of_abscissaOfAbsConv_lt_half {a δ : ℕ → ℝ} (ha : Count a) (hδ : ∀ n, 0 ≤ δ n)
    (h : LSeries.abscissaOfAbsConv (fun n => (δ n : ℂ)) < (1 / 2 : ℝ)) : Count (a + δ) :=
  (count_add_iff_mem_sqrtClass ha δ).mpr (mem_sqrtClass_of_abscissaOfAbsConv_lt_half hδ h)

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
