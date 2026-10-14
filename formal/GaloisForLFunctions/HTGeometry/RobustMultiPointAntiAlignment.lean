import GaloisForLFunctions.HTGeometry.PowerSumTuranWeightedLowerBound
import GaloisForLFunctions.HTGeometry.PositiveExponentialSumPowerSums

/-!
# Robust anti-alignment of finitely many points at polynomial cost

Let `ζ_1, …, ζ_n` lie in the closed unit disc, one of them on the unit circle, and let the weights
`w_i` have a uniform angle, `Re w_i ≥ c |w_i|`.  Then the exponential sum `Σ_i w_i e^{u ζ_i}` has
real part `< −m` somewhere on the circle `|u| = R`, as soon as

`2 ν! (Re Σ_i w_i + m) < c |w_{i₀}| R^ν / D(n, M)` for every `ν ∈ [M+1, M+n]`,

where `D(n, M) = 2e n (6(n+1)(M+2n+2))^n` is Turán's constant
(`exists_norm_re_caratheodoryExpSum_lt`).  Otherwise the real part would stay `≥ −m` on the circle,
and Carathéodory's inequality would bound all power sums `Σ w_i ζ_i^ν` by `2ν!(Re Σ w + m)/R^ν`,
against Turán's lower bound `c |w_{i₀}|/D(n, M)` for some `ν` in the window.

**Robustness.**  The same `u` keeps the real part negative under any perturbation of the exponents by
`|e_i| ≤ ε ≤ 1` with `2 ε e^R Σ |w_i| ≤ m` (`exists_re_sum_mul_cexp_add_lt_zero`).

**Cost.**  With `R ≥ 2e(M + n)` the window condition holds once
`2 (Re Σ w + m) D(n, M) < c |w_{i₀}| 2^{M+1}` (`exists_re_sum_mul_cexp_add_lt_zero_of_large`), so
`M ≈ n log(nM) + log(Σ|w|/|w_{i₀}|)` and `R ≈ C (n log n + log(Σ|w|/|w_{i₀}|))`: polynomial in `n`.
The price is the error tolerance `ε ≈ m e^{−R}/Σ|w|`, exponentially small in `R`.  This trades the
doubly exponential ladder of the band pigeonhole for an exponentially small tolerance.
-/

open Complex Metric

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **Anti-alignment through Carathéodory and Turán.** -/
theorem exists_norm_re_caratheodoryExpSum_lt {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (w ζ : ι → ℂ) {c R m : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hcw : ∀ i ∈ s, c * ‖w i‖ ≤ (w i).re)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hζ₀ : 1 ≤ ‖ζ i₀‖) (hw₀ : w i₀ ≠ 0) (M : ℕ)
    (hbig : ∀ ν : ℕ, M + 1 ≤ ν → ν ≤ M + s.card →
      2 * ν.factorial * ((∑ i ∈ s, w i).re + m) <
        c * ‖w i₀‖ * R ^ ν / (2 * (Real.exp 1 * s.card *
          (6 * (s.card + 1) * ((M : ℝ) + 2 * s.card + 2)) ^ s.card))) :
    ∃ u : ℂ, ‖u‖ = R ∧ (caratheodoryExpSum s w ζ u).re < -m := by
  classical
  by_contra hcon
  push Not at hcon
  -- Carathéodory for the family with one constant term `m`
  let w' : Option ι → ℂ := fun o => o.elim (m : ℂ) w
  let S' : Option ι → ℂ := fun o => o.elim 0 ζ
  have hpos' : ∀ u ∈ sphere (0 : ℂ) R, 0 ≤ (caratheodoryExpSum (Finset.insertNone s) w' S' u).re := by
    intro u hu
    have hu' : ‖u‖ = R := by simpa using hu
    have hsplit : caratheodoryExpSum (Finset.insertNone s) w' S' u =
        (m : ℂ) + caratheodoryExpSum s w ζ u := by
      simp [caratheodoryExpSum, w', S', Finset.sum_insertNone]
    rw [hsplit, Complex.add_re, Complex.ofReal_re]
    linarith [hcon u hu']
  have hcar : ∀ ν : ℕ, 1 ≤ ν →
      ‖∑ i ∈ s, w i * ζ i ^ ν‖ * R ^ ν ≤ 2 * ν.factorial * ((∑ i ∈ s, w i).re + m) := by
    intro ν hν
    have h := norm_sum_mul_pow_mul_pow_le (Finset.insertNone s) w' S' hR hpos' hν
    have hn0 : (0 : ℂ) ^ ν = 0 := zero_pow (by omega)
    have e1 : ∑ i ∈ Finset.insertNone s, w' i * S' i ^ ν = ∑ i ∈ s, w i * ζ i ^ ν := by
      simp [w', S', Finset.sum_insertNone, hn0]
    have e2 : (∑ i ∈ Finset.insertNone s, w' i).re = m + (∑ i ∈ s, w i).re := by
      simp [w', Finset.sum_insertNone, Complex.re_sum]
    rw [e1, e2] at h
    linarith
  -- Turán for the family
  have hβ0 : 0 < c * ‖w i₀‖ := mul_pos hc (norm_pos_iff.mpr hw₀)
  have hβ : ∀ t : ℝ, 1 - 1 / ((M : ℝ) + 2 * s.card + 2) ≤ t → t ≤ 1 →
      c * ‖w i₀‖ ≤ ‖∑ i ∈ s.filter (fun i => t ≤ ‖ζ i‖), w i‖ := by
    intro t _ ht1
    have hmem : i₀ ∈ s.filter (fun i => t ≤ ‖ζ i‖) :=
      Finset.mem_filter.mpr ⟨hi₀, ht1.trans hζ₀⟩
    have h1 : c * ∑ i ∈ s.filter (fun i => t ≤ ‖ζ i‖), ‖w i‖ ≤
        (∑ i ∈ s.filter (fun i => t ≤ ‖ζ i‖), w i).re := by
      rw [Complex.re_sum, Finset.mul_sum]
      exact Finset.sum_le_sum fun i hi => hcw i (Finset.mem_filter.mp hi).1
    have h2 : ‖w i₀‖ ≤ ∑ i ∈ s.filter (fun i => t ≤ ‖ζ i‖), ‖w i‖ :=
      Finset.single_le_sum (f := fun i => ‖w i‖) (fun i _ => norm_nonneg _) hmem
    have h3 := Complex.re_le_norm (∑ i ∈ s.filter (fun i => t ≤ ‖ζ i‖), w i)
    have h4 := mul_le_mul_of_nonneg_left h2 hc.le
    linarith
  obtain ⟨ν, hν1, hν2, hν⟩ := exists_norm_weightedPowerSum_ge s ζ w ⟨i₀, hi₀, hζ₀⟩ M hβ0 hβ
  have hD : 0 < 2 * (Real.exp 1 * s.card *
      (6 * (s.card + 1) * ((M : ℝ) + 2 * s.card + 2)) ^ s.card) := by
    have : 0 < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨i₀, hi₀⟩
    positivity
  have hRν : 0 < R ^ ν := pow_pos hR ν
  have h1 := mul_le_mul_of_nonneg_right hν hRν.le
  have h2 := hcar ν (by omega)
  have h3 := hbig ν hν1 hν2
  rw [div_mul_eq_mul_div] at h1
  linarith

/-- **Robust anti-alignment.**  Under the window condition, one `u` with `|u| = R` keeps
`Re Σ_i w_i e^{u ζ_i + e_i} < 0` for every perturbation `|e_i| ≤ ε ≤ 1`, as soon as
`2 ε e^R Σ_i |w_i| ≤ m` and `|ζ_i| ≤ 1`. -/
theorem exists_re_sum_mul_cexp_add_lt_zero {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (w ζ : ι → ℂ) {c R m ε : ℝ} (hc : 0 < c) (hR : 0 < R) (hε1 : ε ≤ 1)
    (hcw : ∀ i ∈ s, c * ‖w i‖ ≤ (w i).re) (hζ : ∀ i ∈ s, ‖ζ i‖ ≤ 1)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hζ₀ : 1 ≤ ‖ζ i₀‖) (hw₀ : w i₀ ≠ 0) (M : ℕ)
    (hm : 2 * ε * Real.exp R * ∑ i ∈ s, ‖w i‖ ≤ m)
    (hbig : ∀ ν : ℕ, M + 1 ≤ ν → ν ≤ M + s.card →
      2 * ν.factorial * ((∑ i ∈ s, w i).re + m) <
        c * ‖w i₀‖ * R ^ ν / (2 * (Real.exp 1 * s.card *
          (6 * (s.card + 1) * ((M : ℝ) + 2 * s.card + 2)) ^ s.card))) :
    ∃ u : ℂ, ‖u‖ = R ∧ ∀ e : ι → ℂ, (∀ i ∈ s, ‖e i‖ ≤ ε) →
      (∑ i ∈ s, w i * cexp (u * ζ i + e i)).re < 0 := by
  obtain ⟨u, hu, hneg⟩ := exists_norm_re_caratheodoryExpSum_lt s w ζ hc hR hcw hi₀ hζ₀ hw₀ M
    hbig
  refine ⟨u, hu, fun e he => ?_⟩
  have hsplit : ∑ i ∈ s, w i * cexp (u * ζ i + e i) = caratheodoryExpSum s w ζ u +
      ∑ i ∈ s, w i * cexp (ζ i * u) * (cexp (e i) - 1) := by
    rw [caratheodoryExpSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.exp_add, mul_comm (ζ i) u]; ring
  have hpert : ‖∑ i ∈ s, w i * cexp (ζ i * u) * (cexp (e i) - 1)‖ ≤
      2 * ε * Real.exp R * ∑ i ∈ s, ‖w i‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖cexp (ζ i * u)‖ ≤ Real.exp R := by
      rw [Complex.norm_exp]
      refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ?_)
      rw [norm_mul, hu]
      exact mul_le_of_le_one_left hR.le (hζ i hi)
    have h2 : ‖cexp (e i) - 1‖ ≤ 2 * ε :=
      (Complex.norm_exp_sub_one_le ((he i hi).trans hε1)).trans
        (by linarith [he i hi])
    have h3 : ‖w i‖ * ‖cexp (ζ i * u)‖ * ‖cexp (e i) - 1‖ ≤ ‖w i‖ * Real.exp R * (2 * ε) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) h2 (norm_nonneg _)
        (by positivity)
    linarith
  rw [hsplit, Complex.add_re]
  have := Complex.re_le_norm (∑ i ∈ s, w i * cexp (ζ i * u) * (cexp (e i) - 1))
  linarith

/-- **Polynomial cost.**  If `R ≥ 2e(M + n)` and `2 (Re Σ w + m) D(n, M) < c |w_{i₀}| 2^{M+1}`, the
window condition holds, so some `u` with `|u| = R` makes the perturbed sum negative. -/
theorem exists_re_sum_mul_cexp_add_lt_zero_of_large {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (w ζ : ι → ℂ) {c R m ε : ℝ} (hc : 0 < c) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hcw : ∀ i ∈ s, c * ‖w i‖ ≤ (w i).re) (hζ : ∀ i ∈ s, ‖ζ i‖ ≤ 1)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hζ₀ : 1 ≤ ‖ζ i₀‖) (hw₀ : w i₀ ≠ 0) (M : ℕ)
    (hm : 2 * ε * Real.exp R * ∑ i ∈ s, ‖w i‖ ≤ m)
    (hRlarge : 2 * Real.exp 1 * ((M : ℝ) + s.card) ≤ R)
    (hM : 2 * ((∑ i ∈ s, w i).re + m) * (2 * (Real.exp 1 * s.card *
          (6 * (s.card + 1) * ((M : ℝ) + 2 * s.card + 2)) ^ s.card)) <
        c * ‖w i₀‖ * 2 ^ (M + 1)) :
    ∃ u : ℂ, ‖u‖ = R ∧ ∀ e : ι → ℂ, (∀ i ∈ s, ‖e i‖ ≤ ε) →
      (∑ i ∈ s, w i * cexp (u * ζ i + e i)).re < 0 := by
  have he := Real.exp_pos 1
  have he1 : 1 < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hn1 : (1 : ℝ) ≤ s.card := by exact_mod_cast Finset.card_pos.mpr ⟨i₀, hi₀⟩
  have hR : 0 < R := lt_of_lt_of_le (by positivity) hRlarge
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 2 * (Real.exp 1 * s.card *
      (6 * (s.card + 1) * ((M : ℝ) + 2 * s.card + 2)) ^ s.card) := ⟨_, rfl⟩
  rw [← hD] at hM
  have hD0 : 0 < D := by rw [hD]; positivity
  refine exists_re_sum_mul_cexp_add_lt_zero s w ζ hc hR hε1 hcw hζ hi₀ hζ₀ hw₀ M hm ?_
  intro ν hν1 hν2
  rw [← hD]
  have hν0 : (0 : ℝ) < ν := by exact_mod_cast (show 0 < ν by omega)
  -- `R^ν ≥ ν^ν 2^ν ≥ ν! 2^{M+1}`
  have hRν : 2 * (ν : ℝ) ≤ R := by
    have : (ν : ℝ) ≤ M + s.card := by exact_mod_cast hν2
    nlinarith
  have hpow1 : (2 * (ν : ℝ)) ^ ν ≤ R ^ ν := pow_le_pow_left₀ (by positivity) hRν ν
  have hfac : (ν.factorial : ℝ) ≤ (ν : ℝ) ^ ν := by exact_mod_cast Nat.factorial_le_pow ν
  have h2 : (2 : ℝ) ^ (M + 1) ≤ 2 ^ ν := pow_le_pow_right₀ (by norm_num) hν1
  have hkey : (ν.factorial : ℝ) * 2 ^ (M + 1) ≤ R ^ ν := by
    calc (ν.factorial : ℝ) * 2 ^ (M + 1) ≤ (ν : ℝ) ^ ν * 2 ^ ν :=
          mul_le_mul hfac h2 (by positivity) (by positivity)
      _ = (2 * (ν : ℝ)) ^ ν := by rw [mul_pow]; ring
      _ ≤ R ^ ν := hpow1
  have hS : 0 ≤ (∑ i ∈ s, w i).re + m := by
    have : 0 ≤ (∑ i ∈ s, w i).re := by
      rw [Complex.re_sum]
      exact Finset.sum_nonneg fun i hi => (mul_nonneg hc.le (norm_nonneg _)).trans (hcw i hi)
    have hm0 : 0 ≤ m := le_trans (by positivity) hm
    linarith
  rw [lt_div_iff₀ hD0]
  have hw0 : 0 < c * ‖w i₀‖ := mul_pos hc (norm_pos_iff.mpr hw₀)
  have h3 : c * ‖w i₀‖ * 2 ^ (M + 1) * ν.factorial ≤ c * ‖w i₀‖ * R ^ ν := by
    have := mul_le_mul_of_nonneg_left hkey hw0.le
    linarith
  have hfac0 : (0 : ℝ) < ν.factorial := by exact_mod_cast ν.factorial_pos
  have h4 := mul_lt_mul_of_pos_right hM hfac0
  nlinarith

/-! ## Sharpness: the roots of unity cannot be anti-aligned cheaply -/

/-- The power sums of a primitive `n`-th root of unity vanish below order `n`. -/
theorem sum_range_primitiveRoot_pow_eq {n m : ℕ} {ω : ℂ} (hprim : IsPrimitiveRoot ω n)
    (hm : m < n) : ∑ k ∈ Finset.range n, (ω ^ m) ^ k = if m = 0 then (n : ℂ) else 0 := by
  split_ifs with h0
  · subst h0; simp
  · have hne : ω ^ m ≠ 1 := hprim.pow_ne_one_of_pos_of_lt h0 hm
    have hpow : (ω ^ m) ^ n = 1 := by
      rw [← pow_mul, mul_comm m n, pow_mul, hprim.pow_eq_one, one_pow]
    rw [geom_sum_eq hne, hpow, sub_self, zero_div]

/-- **Equal weights at the roots of unity.**  For `|u| ≤ (n+1)/2`,
`|Σ_{k<n} e^{u ω^k} − n| ≤ 2n |u|^n/n!`, with `ω = e^{2πi/n}`. -/
theorem norm_sum_cexp_rootOfUnity_sub_le {n : ℕ} (hn : 2 ≤ n) {u : ℂ}
    (hu : ‖u‖ ≤ ((n : ℝ) + 1) / 2) :
    ‖∑ k ∈ Finset.range n, cexp (u * cexp (2 * Real.pi * I / n) ^ k) - n‖ ≤
      2 * n * (‖u‖ ^ n / n.factorial) := by
  obtain ⟨ω, hω⟩ : ∃ ω : ℂ, ω = cexp (2 * Real.pi * I / n) := ⟨_, rfl⟩
  rw [← hω]
  have hprim : IsPrimitiveRoot ω n := hω ▸ Complex.isPrimitiveRoot_exp n (by omega)
  have hωn : ‖ω‖ = 1 := hprim.norm'_eq_one (by omega)
  -- the truncated exponential series sum to `n`
  have htrunc : ∑ k ∈ Finset.range n, ∑ m ∈ Finset.range n, (u * ω ^ k) ^ m / m.factorial =
      (n : ℂ) := by
    rw [Finset.sum_comm]
    have : ∀ m ∈ Finset.range n, ∑ k ∈ Finset.range n, (u * ω ^ k) ^ m / m.factorial =
        u ^ m / m.factorial * (if m = 0 then (n : ℂ) else 0) := by
      intro m hm
      rw [← sum_range_primitiveRoot_pow_eq hprim (Finset.mem_range.mp hm), Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k m]
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_eq_single 0]
    · simp
    · intro m _ hm0; simp [hm0]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hsplit : ∑ k ∈ Finset.range n, cexp (u * ω ^ k) - n =
      ∑ k ∈ Finset.range n, (cexp (u * ω ^ k) -
        ∑ m ∈ Finset.range n, (u * ω ^ k) ^ m / m.factorial) := by
    rw [Finset.sum_sub_distrib, htrunc]
  rw [hsplit]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ k ∈ Finset.range n, ‖cexp (u * ω ^ k) -
      ∑ m ∈ Finset.range n, (u * ω ^ k) ^ m / m.factorial‖ ≤ ‖u‖ ^ n / n.factorial * 2 := by
    intro k _
    have hnorm : ‖u * ω ^ k‖ = ‖u‖ := by rw [norm_mul, norm_pow, hωn, one_pow, mul_one]
    have hcond : ‖u * ω ^ k‖ / (n.succ : ℝ) ≤ 1 / 2 := by
      rw [hnorm, div_le_iff₀ (by positivity)]
      push_cast
      linarith
    have := Complex.exp_bound' hcond
    rwa [hnorm] at this
  calc ∑ k ∈ Finset.range n, ‖cexp (u * ω ^ k) -
        ∑ m ∈ Finset.range n, (u * ω ^ k) ^ m / m.factorial‖
      ≤ ∑ k ∈ Finset.range n, ‖u‖ ^ n / n.factorial * 2 := Finset.sum_le_sum hterm
    _ = 2 * n * (‖u‖ ^ n / n.factorial) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **No cheap anti-alignment at the roots of unity.**  With equal weights at the `n`-th roots of
unity, `Re Σ_k e^{u ω^k} > 0` for every `u` with `|u| ≤ (n+1)/2` and `2|u|^n < n!`.  So the radius
of any anti-aligning `u` is at least `min((n+1)/2, (n!/2)^{1/n}) ≈ n/e`: the polynomial cost of
`exists_re_sum_mul_cexp_add_lt_zero_of_large` is sharp up to the logarithm. -/
theorem re_sum_cexp_rootOfUnity_pos {n : ℕ} (hn : 2 ≤ n) {u : ℂ}
    (hu : ‖u‖ ≤ ((n : ℝ) + 1) / 2) (hsmall : 2 * ‖u‖ ^ n < n.factorial) :
    0 < (∑ k ∈ Finset.range n, cexp (u * cexp (2 * Real.pi * I / n) ^ k)).re := by
  have h := norm_sum_cexp_rootOfUnity_sub_le hn hu
  have hre := Complex.abs_re_le_norm
    (∑ k ∈ Finset.range n, cexp (u * cexp (2 * Real.pi * I / n) ^ k) - n)
  rw [Complex.sub_re, Complex.natCast_re] at hre
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h2 : 2 * (n : ℝ) * (‖u‖ ^ n / n.factorial) < n := by
    rw [mul_div_assoc', div_lt_iff₀ hfac]
    nlinarith
  have := (abs_le.mp (hre.trans h)).1
  linarith

end GaloisForLFunctions.HTGeometry
