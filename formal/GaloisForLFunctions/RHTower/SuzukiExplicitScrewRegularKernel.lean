import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Suzuki's explicit screw function and its exact regular convolution kernel

Suzuki's screw function for the completed Riemann zeta function (arXiv:2606.09096, eq. (1.3)) is,
for `t > 0`,

```text
g t = -4 (e^(t/2) + e^(-t/2) - 2)
      + ∑_{n ≤ e^t} Λ n * n^(-1/2) * (t - log n)
      - (t/2) (ψ(1/4) - log π)
      - (1/4) (Φ(1,2,1/4) - e^(-t/2) Φ(e^(-2t),2,1/4)).
```

The convolution kernel of the restricted Weil form is `K = -g''` in the distributional sense.  This
module builds `g` as an honest real function and computes its **classical** second derivative at
every point of `(0, ∞)` which is not a prime-power atom `log n`, `n ≥ 2`.  The answer is the exact
regular kernel

```text
K t = e^(t/2) - e^(-5t/2) / (1 - e^(-2t)),
```

and its sign is decided by the plastic number: `K t > 0` iff `e^(3t) - e^t - 1 > 0` iff `t > log ρ`,
where `ρ` is the unique real root of `ρ^3 - ρ - 1 = 0`.

## Structure of the computation

* the four archimedean exponentials contribute `-(e^(t/2) + e^(-t/2))` to `g''`;
* the prime-power hinge sum is **locally affine** off the atoms — this is
  `exists_locallyAffine_screwPrimeSum`, proved by showing that the index set `{n : log n ≤ t}` is
  locally constant — so it contributes nothing;
* the Lerch tail is the series `∑_k e^(-λ k t) / (λ k)^2` with `λ k = 2k + 1/2 = 2(k + 1/4)`; since
  `(λ k)^2` is exactly the square of the exponent, differentiating twice termwise collapses all
  weights to `1` and leaves the geometric series `∑_k e^(-λ k t) = e^(-t/2) / (1 - e^(-2t))`.  This
  is the identity `(8)`–`(9)` of the card; termwise differentiation is justified on every ray
  `(δ, ∞)` by `hasDerivAt_tsum_of_isPreconnected`.

Everything here is unconditional.  The two archimedean constants `ψ(1/4) - log π` and
`(1/4) Φ(1,2,1/4)` enter `g` only through a linear and a constant term, so the second-derivative
theorem is stated for an arbitrary pair of real constants and then instantiated at the true Suzuki
values `screwLinearCoeff` and `screwLerchConst`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology Set

/-! ## The archimedean Lerch tail -/

/-- The exponents of the archimedean Lerch tail of Suzuki's screw function:
`lerchExp k = 2k + 1/2 = 2 (k + 1/4)`.  The point of the normalisation is that the Lerch weight
`1/(4 (k + 1/4)^2)` is exactly the reciprocal square of the exponent, so two termwise
differentiations cancel it. -/
def lerchExp (k : ℕ) : ℝ := 2 * k + 1 / 2

theorem lerchExp_pos (k : ℕ) : 0 < lerchExp k := by
  have h : (0 : ℝ) ≤ 2 * (k : ℝ) := by positivity
  simp only [lerchExp]
  linarith

theorem lerchExp_ne_zero (k : ℕ) : lerchExp k ≠ 0 := (lerchExp_pos k).ne'

theorem half_le_lerchExp (k : ℕ) : (1 : ℝ) / 2 ≤ lerchExp k := by
  have h : (0 : ℝ) ≤ 2 * (k : ℝ) := by positivity
  simp only [lerchExp]
  linarith

theorem quarter_le_lerchExp_sq (k : ℕ) : (1 : ℝ) / 4 ≤ (lerchExp k) ^ 2 := by
  have h := half_le_lerchExp k
  nlinarith

/-- `(lerchExp k)^2 = 4 (k + 1/4)^2`: the Lerch weight is the reciprocal square of the exponent. -/
theorem lerchExp_sq (k : ℕ) : (lerchExp k) ^ 2 = 4 * ((k : ℝ) + 1 / 4) ^ 2 := by
  simp only [lerchExp]; ring

/-- Every Lerch exponential splits off the geometric ratio `e^(-2t)`. -/
theorem exp_neg_lerchExp_mul (k : ℕ) (t : ℝ) :
    Real.exp (-(lerchExp k * t)) = Real.exp (-(t / 2)) * Real.exp (-(2 * t)) ^ k := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  simp only [lerchExp]
  ring

/-- The Lerch exponentials are summable on every ray `t > 0`. -/
theorem summable_exp_neg_lerchExp {t : ℝ} (ht : 0 < t) :
    Summable fun k : ℕ => Real.exp (-(lerchExp k * t)) := by
  have hr : Real.exp (-(2 * t)) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hgeom : Summable fun k : ℕ => Real.exp (-(2 * t)) ^ k :=
    summable_geometric_of_lt_one (Real.exp_nonneg _) hr
  simpa [exp_neg_lerchExp_mul] using hgeom.mul_left (Real.exp (-(t / 2)))

/-- The Lerch tail `(1/4) e^(-t/2) Φ(e^(-2t), 2, 1/4) = ∑_k e^(-λ k t) / (λ k)^2`. -/
def screwLerchTail (t : ℝ) : ℝ := ∑' k : ℕ, Real.exp (-(lerchExp k * t)) / (lerchExp k) ^ 2

/-- The termwise first derivative of the Lerch tail. -/
def screwLerchTail₁ (t : ℝ) : ℝ := ∑' k : ℕ, -(Real.exp (-(lerchExp k * t)) / lerchExp k)

/-- The termwise second derivative of the Lerch tail: all weights have collapsed to `1`. -/
def screwLerchTail₂ (t : ℝ) : ℝ := ∑' k : ℕ, Real.exp (-(lerchExp k * t))

/-- **Equation (9).**  The twice-differentiated Lerch tail is the geometric series
`e^(-t/2) / (1 - e^(-2t))`. -/
theorem screwLerchTail₂_eq {t : ℝ} (ht : 0 < t) :
    screwLerchTail₂ t = Real.exp (-(t / 2)) / (1 - Real.exp (-(2 * t))) := by
  have hr : Real.exp (-(2 * t)) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  calc screwLerchTail₂ t
      = ∑' k : ℕ, Real.exp (-(t / 2)) * Real.exp (-(2 * t)) ^ k := by
        simp only [screwLerchTail₂, exp_neg_lerchExp_mul]
    _ = Real.exp (-(t / 2)) * ∑' k : ℕ, Real.exp (-(2 * t)) ^ k := tsum_mul_left
    _ = Real.exp (-(t / 2)) * (1 - Real.exp (-(2 * t)))⁻¹ := by
        rw [tsum_geometric_of_lt_one (Real.exp_nonneg _) hr]
    _ = Real.exp (-(t / 2)) / (1 - Real.exp (-(2 * t))) := by ring

/-- The linear inner function of one Lerch term. -/
theorem hasDerivAt_neg_lerchExp_mul (k : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => -(lerchExp k * s)) (-(lerchExp k)) t := by
  simpa using ((hasDerivAt_id t).const_mul (lerchExp k)).fun_neg

/-- Termwise derivative of one Lerch term. -/
theorem hasDerivAt_screwLerchTerm (k : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-(lerchExp k * s)) / (lerchExp k) ^ 2)
      (-(Real.exp (-(lerchExp k * t)) / lerchExp k)) t := by
  have hne : lerchExp k ≠ 0 := lerchExp_ne_zero k
  have h2 := ((hasDerivAt_neg_lerchExp_mul k t).exp).div_const ((lerchExp k) ^ 2)
  have hval : Real.exp (-(lerchExp k * t)) * -(lerchExp k) / (lerchExp k) ^ 2
      = -(Real.exp (-(lerchExp k * t)) / lerchExp k) := by
    field_simp
  rw [hval] at h2
  exact h2

/-- Termwise derivative of one differentiated Lerch term. -/
theorem hasDerivAt_screwLerchTerm₁ (k : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => -(Real.exp (-(lerchExp k * s)) / lerchExp k))
      (Real.exp (-(lerchExp k * t))) t := by
  have hne : lerchExp k ≠ 0 := lerchExp_ne_zero k
  have h2 := (((hasDerivAt_neg_lerchExp_mul k t).exp).div_const (lerchExp k)).fun_neg
  have hval : -(Real.exp (-(lerchExp k * t)) * -(lerchExp k) / lerchExp k)
      = Real.exp (-(lerchExp k * t)) := by
    field_simp
  rw [hval] at h2
  exact h2

theorem div_lerchExp_le {k : ℕ} {y : ℝ} :
    Real.exp (-(lerchExp k * y)) / lerchExp k ≤ 2 * Real.exp (-(lerchExp k * y)) := by
  have hpos := lerchExp_pos k
  have h2 : (1 : ℝ) / 2 ≤ lerchExp k := half_le_lerchExp k
  rw [div_le_iff₀ hpos]
  nlinarith [Real.exp_pos (-(lerchExp k * y))]

theorem div_lerchExp_sq_le {k : ℕ} {y : ℝ} :
    Real.exp (-(lerchExp k * y)) / (lerchExp k) ^ 2 ≤ 4 * Real.exp (-(lerchExp k * y)) := by
  have h4 : (1 : ℝ) / 4 ≤ (lerchExp k) ^ 2 := quarter_le_lerchExp_sq k
  rw [div_le_iff₀ (by positivity)]
  nlinarith [Real.exp_pos (-(lerchExp k * y))]

theorem exp_neg_lerchExp_antitone {k : ℕ} {a y : ℝ} (h : a ≤ y) :
    Real.exp (-(lerchExp k * y)) ≤ Real.exp (-(lerchExp k * a)) := by
  have hpos := lerchExp_pos k
  rw [Real.exp_le_exp]
  have : lerchExp k * a ≤ lerchExp k * y := mul_le_mul_of_nonneg_left h hpos.le
  linarith

theorem summable_screwLerchTerm {t : ℝ} (ht : 0 < t) :
    Summable fun k : ℕ => Real.exp (-(lerchExp k * t)) / (lerchExp k) ^ 2 :=
  Summable.of_nonneg_of_le (fun k => div_nonneg (Real.exp_nonneg _) (by positivity))
    (fun _ => div_lerchExp_sq_le) ((summable_exp_neg_lerchExp ht).mul_left 4)

theorem summable_screwLerchTerm₁ {t : ℝ} (ht : 0 < t) :
    Summable fun k : ℕ => -(Real.exp (-(lerchExp k * t)) / lerchExp k) :=
  (Summable.of_nonneg_of_le
    (fun k => div_nonneg (Real.exp_nonneg _) (lerchExp_pos k).le)
    (fun _ => div_lerchExp_le) ((summable_exp_neg_lerchExp ht).mul_left 2)).neg

/-- The Lerch tail is differentiable on `(0, ∞)`, with the termwise derivative. -/
theorem hasDerivAt_screwLerchTail {t : ℝ} (ht : 0 < t) :
    HasDerivAt screwLerchTail (screwLerchTail₁ t) t := by
  have hhalf : 0 < t / 2 := by linarith
  have hsum : Summable fun k : ℕ => 2 * Real.exp (-(lerchExp k * (t / 2))) :=
    (summable_exp_neg_lerchExp hhalf).mul_left 2
  have hmem : t ∈ Ioi (t / 2) := by simp only [mem_Ioi]; linarith
  have hbound : ∀ (k : ℕ), ∀ y ∈ Ioi (t / 2),
      ‖-(Real.exp (-(lerchExp k * y)) / lerchExp k)‖
        ≤ 2 * Real.exp (-(lerchExp k * (t / 2))) := by
    intro k y hy
    have hy' : t / 2 ≤ y := le_of_lt hy
    have hnorm : ‖-(Real.exp (-(lerchExp k * y)) / lerchExp k)‖
        = Real.exp (-(lerchExp k * y)) / lerchExp k := by
      rw [norm_neg, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (Real.exp_nonneg _) (lerchExp_pos k).le)]
    rw [hnorm]
    calc Real.exp (-(lerchExp k * y)) / lerchExp k
        ≤ 2 * Real.exp (-(lerchExp k * y)) := div_lerchExp_le
      _ ≤ 2 * Real.exp (-(lerchExp k * (t / 2))) := by
          have := exp_neg_lerchExp_antitone (k := k) hy'
          linarith
  exact hasDerivAt_tsum_of_isPreconnected hsum isOpen_Ioi isPreconnected_Ioi
    (fun k y _ => hasDerivAt_screwLerchTerm k y) hbound hmem (summable_screwLerchTerm ht) hmem

/-- The differentiated Lerch tail is again differentiable on `(0, ∞)`, with termwise derivative. -/
theorem hasDerivAt_screwLerchTail₁ {t : ℝ} (ht : 0 < t) :
    HasDerivAt screwLerchTail₁ (screwLerchTail₂ t) t := by
  have hhalf : 0 < t / 2 := by linarith
  have hsum : Summable fun k : ℕ => Real.exp (-(lerchExp k * (t / 2))) :=
    summable_exp_neg_lerchExp hhalf
  have hmem : t ∈ Ioi (t / 2) := by simp only [mem_Ioi]; linarith
  have hbound : ∀ (k : ℕ), ∀ y ∈ Ioi (t / 2),
      ‖Real.exp (-(lerchExp k * y))‖ ≤ Real.exp (-(lerchExp k * (t / 2))) := by
    intro k y hy
    have hy' : t / 2 ≤ y := le_of_lt hy
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact exp_neg_lerchExp_antitone hy'
  exact hasDerivAt_tsum_of_isPreconnected hsum isOpen_Ioi isPreconnected_Ioi
    (fun k y _ => hasDerivAt_screwLerchTerm₁ k y) hbound hmem (summable_screwLerchTerm₁ ht) hmem

/-! ## The prime-power hinge sum -/

/-- The von Mangoldt weight `Λ n * n^(-1/2)` of Suzuki's screw function. -/
def screwPrimeWeight (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n / Real.sqrt n

/-- The prime-power hinge sum `∑_{2 ≤ n ≤ e^t} Λ n * n^(-1/2) * (t - log n)`. -/
def screwPrimeSum (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊, screwPrimeWeight n * (t - Real.log n)

/-- The hinge sum is the positive-part sum over any sufficiently long index range. -/
theorem screwPrimeSum_eq_sum_max {t : ℝ} {N : ℕ} (hN : ⌊Real.exp t⌋₊ ≤ N) :
    screwPrimeSum t = ∑ n ∈ Finset.Icc 2 N, screwPrimeWeight n * max 0 (t - Real.log n) := by
  have hsub : Finset.Icc 2 ⌊Real.exp t⌋₊ ⊆ Finset.Icc 2 N := by
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans hN⟩
  have hinner : ∀ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
      screwPrimeWeight n * (t - Real.log n) = screwPrimeWeight n * max 0 (t - Real.log n) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hle : (n : ℝ) ≤ Real.exp t := by
      calc (n : ℝ) ≤ (⌊Real.exp t⌋₊ : ℝ) := by exact_mod_cast hn.2
        _ ≤ Real.exp t := Nat.floor_le (Real.exp_pos t).le
    have hlog : Real.log n ≤ t := (Real.log_le_iff_le_exp hnpos).mpr hle
    rw [max_eq_right (by linarith)]
  have houter : ∀ n ∈ Finset.Icc 2 N, n ∉ Finset.Icc 2 ⌊Real.exp t⌋₊ →
      screwPrimeWeight n * max 0 (t - Real.log n) = 0 := by
    intro n hn hnot
    simp only [Finset.mem_Icc] at hn
    have hgt : ⌊Real.exp t⌋₊ < n := by
      by_contra hle
      exact hnot (Finset.mem_Icc.mpr ⟨hn.1, by omega⟩)
    have hexp : Real.exp t < (n : ℝ) := (Nat.floor_lt (Real.exp_pos t).le).mp hgt
    have hnpos : (0 : ℝ) < (n : ℝ) := (Real.exp_pos t).trans hexp
    have hlog : t < Real.log n := (Real.lt_log_iff_exp_lt hnpos).mpr hexp
    rw [max_eq_left (by linarith), mul_zero]
  rw [screwPrimeSum, Finset.sum_congr rfl hinner, Finset.sum_subset hsub houter]

/-- **Off the prime-power atoms the hinge sum is locally affine.**  This is the reason the
arithmetic part of Suzuki's screw function contributes nothing to the regular kernel. -/
theorem exists_locallyAffine_screwPrimeSum {t : ℝ} (ht : 0 < t)
    (hatom : ∀ n : ℕ, 2 ≤ n → t ≠ Real.log n) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ t / 2 ∧ ∃ A B : ℝ,
      ∀ s ∈ Ioo (t - δ) (t + δ), screwPrimeSum s = A * s - B := by
  classical
  set N : ℕ := ⌊Real.exp (t + 1)⌋₊ with hNdef
  set T : Set ℝ := (fun n : ℕ => Real.log n) '' (Finset.Icc 2 N : Set ℕ) with hTdef
  have hTfin : T.Finite := Set.Finite.image _ (Finset.finite_toSet _)
  have htT : t ∉ T := by
    rintro ⟨n, hn, hlog⟩
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    exact hatom n hn2 hlog.symm
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hTfin.isClosed.isOpen_compl t htT
  have hsep : ∀ n ∈ Finset.Icc 2 N, ε ≤ |Real.log n - t| := by
    intro n hn
    by_contra hlt
    rw [not_le] at hlt
    have hmem : Real.log n ∈ Metric.ball t ε := by
      simp only [Metric.mem_ball, Real.dist_eq]
      exact hlt
    exact (hball hmem) ⟨n, hn, rfl⟩
  have hδpos : 0 < min ε (min 1 (t / 2)) := lt_min hε (lt_min one_pos (by linarith))
  refine ⟨min ε (min 1 (t / 2)), hδpos,
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  set δ : ℝ := min ε (min 1 (t / 2)) with hδdef
  have hδε : δ ≤ ε := min_le_left _ _
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hδt : δ ≤ t / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set S : Finset ℕ := Finset.Icc 2 ⌊Real.exp t⌋₊ with hSdef
  refine ⟨∑ n ∈ S, screwPrimeWeight n, ∑ n ∈ S, screwPrimeWeight n * Real.log n, ?_⟩
  intro s hs
  obtain ⟨hs1, hs2⟩ := hs
  have hsN : ⌊Real.exp s⌋₊ ≤ N := by
    rw [hNdef]
    exact Nat.floor_mono (Real.exp_le_exp.mpr (by linarith))
  have htN : ⌊Real.exp t⌋₊ ≤ N := by
    rw [hNdef]
    exact Nat.floor_mono (Real.exp_le_exp.mpr (by linarith))
  have hSsub : S ⊆ Finset.Icc 2 N := by
    intro n hn
    rw [hSdef, Finset.mem_Icc] at hn
    exact Finset.mem_Icc.mpr ⟨hn.1, hn.2.trans htN⟩
  have hin : ∀ n ∈ S, screwPrimeWeight n * max 0 (s - Real.log n)
      = screwPrimeWeight n * (s - Real.log n) := by
    intro n hn
    have hnS := hn
    rw [hSdef, Finset.mem_Icc] at hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hle : (n : ℝ) ≤ Real.exp t := by
      calc (n : ℝ) ≤ (⌊Real.exp t⌋₊ : ℝ) := by exact_mod_cast hn.2
        _ ≤ Real.exp t := Nat.floor_le (Real.exp_pos t).le
    have hlog : Real.log n ≤ t := (Real.log_le_iff_le_exp hnpos).mpr hle
    have hne : Real.log n ≠ t := fun h => hatom n hn.1 h.symm
    have hsepn : ε ≤ |Real.log n - t| := hsep n (hSsub hnS)
    have habs : |Real.log n - t| = t - Real.log n := by
      rw [abs_of_nonpos (by linarith [lt_of_le_of_ne hlog hne])]
      ring
    have hgap : δ ≤ t - Real.log n := by rw [← habs]; linarith
    rw [max_eq_right (by linarith)]
  have hout : ∀ n ∈ Finset.Icc 2 N, n ∉ S → screwPrimeWeight n * max 0 (s - Real.log n) = 0 := by
    intro n hn hnot
    have hnN := hn
    simp only [Finset.mem_Icc] at hn
    have hgt : ⌊Real.exp t⌋₊ < n := by
      by_contra hle
      exact hnot (by rw [hSdef]; exact Finset.mem_Icc.mpr ⟨hn.1, by omega⟩)
    have hexp : Real.exp t < (n : ℝ) := (Nat.floor_lt (Real.exp_pos t).le).mp hgt
    have hnpos : (0 : ℝ) < (n : ℝ) := (Real.exp_pos t).trans hexp
    have hlog : t < Real.log n := (Real.lt_log_iff_exp_lt hnpos).mpr hexp
    have hsepn : ε ≤ |Real.log n - t| := hsep n hnN
    have habs : |Real.log n - t| = Real.log n - t := abs_of_nonneg (by linarith)
    have hgap : δ ≤ Real.log n - t := by rw [habs] at hsepn; linarith
    rw [max_eq_left (by linarith), mul_zero]
  calc screwPrimeSum s
      = ∑ n ∈ Finset.Icc 2 N, screwPrimeWeight n * max 0 (s - Real.log n) :=
        screwPrimeSum_eq_sum_max hsN
    _ = ∑ n ∈ S, screwPrimeWeight n * max 0 (s - Real.log n) :=
        (Finset.sum_subset hSsub hout).symm
    _ = ∑ n ∈ S, screwPrimeWeight n * (s - Real.log n) := Finset.sum_congr rfl hin
    _ = (∑ n ∈ S, screwPrimeWeight n) * s - ∑ n ∈ S, screwPrimeWeight n * Real.log n := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun n _ => by ring

/-! ## Suzuki's explicit screw function -/

/-- The archimedean linear coefficient `ψ(1/4) - log π` of Suzuki's screw function. -/
def screwLinearCoeff : ℝ := (Complex.digamma (1 / 4)).re - Real.log Real.pi

/-- The archimedean constant `(1/4) Φ(1,2,1/4) = ∑_k (lerchExp k)⁻¹ ^ 2`. -/
def screwLerchConst : ℝ := screwLerchTail 0

/-- **Suzuki's explicit screw function**, equation `(3)`, with the two archimedean constants kept
as parameters `c₁` (the linear coefficient) and `c₀` (the additive constant).  The published
function is `screwFn screwLinearCoeff screwLerchConst`. -/
def screwFn (c₁ c₀ : ℝ) (t : ℝ) : ℝ :=
  -4 * (Real.exp (t / 2) + Real.exp (-(t / 2)) - 2)
    + screwPrimeSum t - c₁ / 2 * t - c₀ + screwLerchTail t

/-- The exact regular screw kernel `K t = e^(t/2) - e^(-5t/2) / (1 - e^(-2t))`, equation `(6)`. -/
def screwRegularKernel (t : ℝ) : ℝ :=
  Real.exp (t / 2) - Real.exp (-(5 * t / 2)) / (1 - Real.exp (-(2 * t)))

theorem one_sub_exp_neg_two_mul_pos {t : ℝ} (ht : 0 < t) : 0 < 1 - Real.exp (-(2 * t)) := by
  have : Real.exp (-(2 * t)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  linarith

/-- The regular kernel in the form produced by the second derivative. -/
theorem screwRegularKernel_eq_tailForm {t : ℝ} (ht : 0 < t) :
    screwRegularKernel t
      = Real.exp (t / 2) + Real.exp (-(t / 2))
        - Real.exp (-(t / 2)) / (1 - Real.exp (-(2 * t))) := by
  have h2 : (1 : ℝ) - Real.exp (-(2 * t)) ≠ 0 := ne_of_gt (one_sub_exp_neg_two_mul_pos ht)
  have hE : Real.exp (-(5 * t / 2)) = Real.exp (-(t / 2)) * Real.exp (-(2 * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hcancel : Real.exp (-(t / 2)) / (1 - Real.exp (-(2 * t)))
        - Real.exp (-(t / 2)) * Real.exp (-(2 * t)) / (1 - Real.exp (-(2 * t)))
      = Real.exp (-(t / 2)) := by
    rw [div_sub_div_same,
      show Real.exp (-(t / 2)) - Real.exp (-(t / 2)) * Real.exp (-(2 * t))
        = Real.exp (-(t / 2)) * (1 - Real.exp (-(2 * t))) from by ring,
      mul_div_assoc, div_self h2, mul_one]
  rw [screwRegularKernel, hE]
  linarith [hcancel]

/-! ## Basic derivative helpers -/

theorem hasDerivAt_half (t : ℝ) : HasDerivAt (fun r : ℝ => r / 2) (1 / 2 : ℝ) t := by
  simpa using (hasDerivAt_id t).div_const 2

theorem hasDerivAt_neg_half (t : ℝ) : HasDerivAt (fun r : ℝ => -(r / 2)) (-(1 / 2) : ℝ) t := by
  simpa using ((hasDerivAt_id t).div_const 2).fun_neg

theorem hasDerivAt_exp_half (t : ℝ) :
    HasDerivAt (fun r : ℝ => Real.exp (r / 2)) (Real.exp (t / 2) * (1 / 2)) t :=
  (hasDerivAt_half t).exp

theorem hasDerivAt_exp_neg_half (t : ℝ) :
    HasDerivAt (fun r : ℝ => Real.exp (-(r / 2))) (Real.exp (-(t / 2)) * (-(1 / 2))) t :=
  (hasDerivAt_neg_half t).exp

/-- The archimedean exponential block of `screwFn` and its derivative. -/
theorem hasDerivAt_screwExpBlock (t : ℝ) :
    HasDerivAt (fun r : ℝ => -4 * (Real.exp (r / 2) + Real.exp (-(r / 2)) - 2))
      (-2 * Real.exp (t / 2) + 2 * Real.exp (-(t / 2))) t := by
  have h := (((hasDerivAt_exp_half t).fun_add (hasDerivAt_exp_neg_half t)).sub_const
    (2 : ℝ)).const_mul (-4 : ℝ)
  have hval : (-4 : ℝ) * (Real.exp (t / 2) * (1 / 2) + Real.exp (-(t / 2)) * (-(1 / 2)))
      = -2 * Real.exp (t / 2) + 2 * Real.exp (-(t / 2)) := by ring
  rw [hval] at h
  exact h

/-! ## The second derivative -/

/-- The explicit derivative of `screwFn` on a neighbourhood where the hinge sum is affine. -/
theorem hasDerivAt_screwFn_of_affine (c₁ c₀ A B : ℝ) {δ t s : ℝ} (ht : 0 < t) (hδ : δ ≤ t / 2)
    (haff : ∀ r ∈ Ioo (t - δ) (t + δ), screwPrimeSum r = A * r - B)
    (hs : s ∈ Ioo (t - δ) (t + δ)) :
    HasDerivAt (screwFn c₁ c₀)
      (-2 * Real.exp (s / 2) + 2 * Real.exp (-(s / 2)) + A - c₁ / 2 + screwLerchTail₁ s) s := by
  have hspos : 0 < s := by
    have h1 := hs.1
    linarith
  have hIoo : Ioo (t - δ) (t + δ) ∈ 𝓝 s := isOpen_Ioo.mem_nhds hs
  have hhinge : HasDerivAt screwPrimeSum A s := by
    have haffs : HasDerivAt (fun r : ℝ => A * r - B) A s := by
      simpa using ((hasDerivAt_id s).const_mul A).sub_const B
    exact haffs.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem hIoo fun r hr => haff r hr)
  have hlin : HasDerivAt (fun r : ℝ => c₁ / 2 * r) (c₁ / 2) s := by
    simpa using (hasDerivAt_id s).const_mul (c₁ / 2)
  have htail : HasDerivAt screwLerchTail (screwLerchTail₁ s) s := hasDerivAt_screwLerchTail hspos
  exact ((((hasDerivAt_screwExpBlock s).fun_add hhinge).fun_sub hlin).sub_const c₀).fun_add htail

/-- **The exact second derivative of Suzuki's screw function off the prime-power atoms**, in the
form produced by the computation. -/
theorem iteratedDeriv_two_screwFn_tailForm (c₁ c₀ : ℝ) {t : ℝ} (ht : 0 < t)
    (hatom : ∀ n : ℕ, 2 ≤ n → t ≠ Real.log n) :
    iteratedDeriv 2 (screwFn c₁ c₀) t
      = -(Real.exp (t / 2) + Real.exp (-(t / 2))) + screwLerchTail₂ t := by
  obtain ⟨δ, hδpos, hδt, A, B, haff⟩ := exists_locallyAffine_screwPrimeSum ht hatom
  have hmemt : t ∈ Ioo (t - δ) (t + δ) := ⟨by linarith, by linarith⟩
  have hIoo : Ioo (t - δ) (t + δ) ∈ 𝓝 t := isOpen_Ioo.mem_nhds hmemt
  have hderiv : ∀ s ∈ Ioo (t - δ) (t + δ), deriv (screwFn c₁ c₀) s
      = -2 * Real.exp (s / 2) + 2 * Real.exp (-(s / 2)) + A - c₁ / 2 + screwLerchTail₁ s :=
    fun s hs => (hasDerivAt_screwFn_of_affine c₁ c₀ A B ht hδt haff hs).deriv
  have hEq : deriv (screwFn c₁ c₀) =ᶠ[𝓝 t]
      fun s => -2 * Real.exp (s / 2) + 2 * Real.exp (-(s / 2)) + A - c₁ / 2 + screwLerchTail₁ s :=
    Filter.eventuallyEq_of_mem hIoo hderiv
  have hD : HasDerivAt
      (fun s : ℝ => -2 * Real.exp (s / 2) + 2 * Real.exp (-(s / 2)) + A - c₁ / 2
        + screwLerchTail₁ s)
      (-(Real.exp (t / 2) + Real.exp (-(t / 2))) + screwLerchTail₂ t) t := by
    have h := (((((hasDerivAt_exp_half t).const_mul (-2 : ℝ)).fun_add
      ((hasDerivAt_exp_neg_half t).const_mul (2 : ℝ))).add_const A).sub_const
      (c₁ / 2)).fun_add (hasDerivAt_screwLerchTail₁ ht)
    have hval : (-2 : ℝ) * (Real.exp (t / 2) * (1 / 2))
          + 2 * (Real.exp (-(t / 2)) * (-(1 / 2))) + screwLerchTail₂ t
        = -(Real.exp (t / 2) + Real.exp (-(t / 2))) + screwLerchTail₂ t := by ring
    rw [hval] at h
    exact h
  rw [iteratedDeriv_succ, iteratedDeriv_one, hEq.deriv_eq, hD.deriv]

/-- **Equation (6).**  Away from the prime-power atoms the restricted Weil kernel `K = -g''`
of Suzuki's screw function is exactly `e^(t/2) - e^(-5t/2)/(1 - e^(-2t))`. -/
theorem iteratedDeriv_two_screwFn (c₁ c₀ : ℝ) {t : ℝ} (ht : 0 < t)
    (hatom : ∀ n : ℕ, 2 ≤ n → t ≠ Real.log n) :
    iteratedDeriv 2 (screwFn c₁ c₀) t = -screwRegularKernel t := by
  rw [iteratedDeriv_two_screwFn_tailForm c₁ c₀ ht hatom, screwRegularKernel_eq_tailForm ht,
    screwLerchTail₂_eq ht]
  ring

/-- The same statement for the published Suzuki constants. -/
theorem iteratedDeriv_two_screwFn_suzuki {t : ℝ} (ht : 0 < t)
    (hatom : ∀ n : ℕ, 2 ≤ n → t ≠ Real.log n) :
    iteratedDeriv 2 (screwFn screwLinearCoeff screwLerchConst) t = -screwRegularKernel t :=
  iteratedDeriv_two_screwFn _ _ ht hatom

/-! ## The sign threshold: the plastic number -/

theorem exists_plasticRoot : ∃ x, x ∈ Ioo (1 : ℝ) 2 ∧ x ^ 3 - x - 1 = 0 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3 - x - 1) (Icc 1 2) := by fun_prop
  have h := intermediate_value_Ioo (by norm_num : (1 : ℝ) ≤ 2) hcont
  have h0 : (0 : ℝ) ∈ Ioo ((1 : ℝ) ^ 3 - 1 - 1) ((2 : ℝ) ^ 3 - 2 - 1) := by norm_num
  obtain ⟨x, hx, hx0⟩ := h h0
  exact ⟨x, hx, hx0⟩

/-- The plastic number: the unique real root of `x^3 - x - 1`. -/
def plasticRoot : ℝ := exists_plasticRoot.choose

theorem plasticRoot_mem_Ioo : plasticRoot ∈ Ioo (1 : ℝ) 2 := exists_plasticRoot.choose_spec.1

theorem plasticRoot_cubic : plasticRoot ^ 3 - plasticRoot - 1 = 0 :=
  exists_plasticRoot.choose_spec.2

theorem one_lt_plasticRoot : 1 < plasticRoot := plasticRoot_mem_Ioo.1

theorem plasticRoot_pos : 0 < plasticRoot := by linarith [one_lt_plasticRoot]

/-- `x^3 - x - 1` is strictly positive exactly beyond the plastic number, on `x ≥ 1`. -/
theorem cubic_pos_iff_plasticRoot_lt {x : ℝ} (hx : 1 ≤ x) :
    0 < x ^ 3 - x - 1 ↔ plasticRoot < x := by
  have hρ : 1 < plasticRoot := one_lt_plasticRoot
  constructor
  · intro h
    by_contra hle
    rw [not_lt] at hle
    have hfac : 0 ≤ (plasticRoot - x) * (plasticRoot ^ 2 + plasticRoot * x + x ^ 2 - 1) := by
      refine mul_nonneg (by linarith) ?_
      nlinarith
    nlinarith [plasticRoot_cubic]
  · intro h
    have hfac : 0 < (x - plasticRoot) * (x ^ 2 + x * plasticRoot + plasticRoot ^ 2 - 1) := by
      refine mul_pos (by linarith) ?_
      nlinarith
    nlinarith [plasticRoot_cubic]

theorem cubic_neg_of_lt_plasticRoot {x : ℝ} (hx : 1 ≤ x) (h : x < plasticRoot) :
    x ^ 3 - x - 1 < 0 := by
  have hρ : 1 < plasticRoot := one_lt_plasticRoot
  have hfac : 0 < (plasticRoot - x) * (plasticRoot ^ 2 + plasticRoot * x + x ^ 2 - 1) := by
    refine mul_pos (by linarith) ?_
    nlinarith
  nlinarith [plasticRoot_cubic]

/-- The sign threshold `t_* = log ρ` of the regular screw kernel. -/
def screwSignThreshold : ℝ := Real.log plasticRoot

theorem screwSignThreshold_pos : 0 < screwSignThreshold := Real.log_pos one_lt_plasticRoot

/-- The exponential identities used to clear the kernel's denominator. -/
theorem exp_half_mul_exp_five_half (t : ℝ) :
    Real.exp (t / 2) * Real.exp (5 * t / 2) = Real.exp t ^ 3 := by
  rw [← Real.exp_add, show t / 2 + 5 * t / 2 = ((3 : ℕ) : ℝ) * t by push_cast; ring,
    Real.exp_nat_mul]

theorem exp_neg_five_half_mul_exp_five_half (t : ℝ) :
    Real.exp (-(5 * t / 2)) * Real.exp (5 * t / 2) = 1 := by
  rw [← Real.exp_add]; simp

theorem exp_cube_mul_exp_neg_two (t : ℝ) :
    Real.exp t ^ 3 * Real.exp (-(2 * t)) = Real.exp t := by
  rw [show Real.exp t ^ 3 = Real.exp (((3 : ℕ) : ℝ) * t) by rw [Real.exp_nat_mul],
    ← Real.exp_add, show ((3 : ℕ) : ℝ) * t + -(2 * t) = t by push_cast; ring]

/-- The exact sign carrier: multiplying the kernel by an explicit positive factor produces the
cubic `e^(3t) - e^t - 1`. -/
theorem screwRegularKernel_mul_eq_cubic {t : ℝ} (ht : 0 < t) :
    screwRegularKernel t * (Real.exp (5 * t / 2) * (1 - Real.exp (-(2 * t))))
      = Real.exp t ^ 3 - Real.exp t - 1 := by
  have h2 : (1 : ℝ) - Real.exp (-(2 * t)) ≠ 0 := ne_of_gt (one_sub_exp_neg_two_mul_pos ht)
  have hd : Real.exp (-(5 * t / 2)) / (1 - Real.exp (-(2 * t))) * (1 - Real.exp (-(2 * t)))
      = Real.exp (-(5 * t / 2)) := by
    rw [div_mul_eq_mul_div, mul_div_assoc, div_self h2, mul_one]
  have hK : screwRegularKernel t * (1 - Real.exp (-(2 * t)))
      = Real.exp (t / 2) * (1 - Real.exp (-(2 * t))) - Real.exp (-(5 * t / 2)) := by
    rw [screwRegularKernel, sub_mul, hd]
  have hstep : screwRegularKernel t * (Real.exp (5 * t / 2) * (1 - Real.exp (-(2 * t))))
      = (screwRegularKernel t * (1 - Real.exp (-(2 * t)))) * Real.exp (5 * t / 2) := by ring
  rw [hstep, hK]
  linear_combination exp_half_mul_exp_five_half t
    - Real.exp (-(2 * t)) * exp_half_mul_exp_five_half t
    - exp_neg_five_half_mul_exp_five_half t - exp_cube_mul_exp_neg_two t

theorem screwKernelSignFactor_pos {t : ℝ} (ht : 0 < t) :
    0 < Real.exp (5 * t / 2) * (1 - Real.exp (-(2 * t))) :=
  mul_pos (Real.exp_pos _) (one_sub_exp_neg_two_mul_pos ht)

/-- **Equation (7), algebraic form.** -/
theorem screwRegularKernel_pos_iff_cubic {t : ℝ} (ht : 0 < t) :
    0 < screwRegularKernel t ↔ 0 < Real.exp t ^ 3 - Real.exp t - 1 := by
  have hP := screwKernelSignFactor_pos ht
  rw [← screwRegularKernel_mul_eq_cubic ht]
  constructor
  · intro h
    exact mul_pos h hP
  · intro h
    by_contra hc
    rw [not_lt] at hc
    nlinarith [mul_nonneg (neg_nonneg.mpr hc) hP.le]

theorem screwRegularKernel_neg_iff_cubic {t : ℝ} (ht : 0 < t) :
    screwRegularKernel t < 0 ↔ Real.exp t ^ 3 - Real.exp t - 1 < 0 := by
  have hP := screwKernelSignFactor_pos ht
  rw [← screwRegularKernel_mul_eq_cubic ht]
  constructor
  · intro h
    nlinarith [mul_pos (neg_pos.mpr h) hP]
  · intro h
    by_contra hc
    rw [not_lt] at hc
    nlinarith [mul_nonneg hc hP.le]

/-- **Equation (7).**  The regular screw kernel is positive exactly beyond `t_* = log ρ`. -/
theorem screwRegularKernel_pos_iff {t : ℝ} (ht : 0 < t) :
    0 < screwRegularKernel t ↔ screwSignThreshold < t := by
  rw [screwRegularKernel_pos_iff_cubic ht,
    cubic_pos_iff_plasticRoot_lt (Real.one_le_exp ht.le), screwSignThreshold]
  exact (Real.log_lt_iff_lt_exp plasticRoot_pos).symm

/-- Below the threshold the kernel is strictly negative. -/
theorem screwRegularKernel_neg_of_lt_threshold {t : ℝ} (ht : 0 < t)
    (hlt : t < screwSignThreshold) : screwRegularKernel t < 0 := by
  have hx : 1 ≤ Real.exp t := Real.one_le_exp ht.le
  have hxlt : Real.exp t < plasticRoot := by
    rw [screwSignThreshold] at hlt
    exact (Real.lt_log_iff_exp_lt plasticRoot_pos).mp hlt
  exact (screwRegularKernel_neg_iff_cubic ht).mpr (cubic_neg_of_lt_plasticRoot hx hxlt)

end GaloisForLFunctions.RHTower

end
