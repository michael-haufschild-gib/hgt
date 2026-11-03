import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheWeilFloorOfACurveIsItsZeroWidth
import GaloisForLFunctions.SquareRootThreshold.LagFamilyMeetsTheCrystalAtTheThreshold
import GaloisForLFunctions.RHTower.PrimeBlindPoleCurvatureFloor

/-!
# The monodromy rate of a curve is its zero width

Along the dilation of its tests, Weil's form of a curve datum degenerates polynomially when the
curve is pure and exponentially when it is not (`DegenerationSelectsThePureCurves`). This file
computes the exponential rate exactly. Let `L = log q`, `N = 2g`, `R = max_i |β_i|` (the spectral
radius of the normalized Frobenius) and `δ = log R / L`, the **zero width**
`max |Re s − ½|` of the zeros of the zeta function of the curve.

* **Ceiling and floor** (`norm_W_curveConfig_le_of_length`, `norm_W_curveConfig_le_exp`): a test
  vanishing outside an interval of length `ℓ` has `|W(f, f)| ≤ (2ℓ + L) N e^{δℓ} ‖f‖²`. Only the
  lags `|m| ≤ ℓ/L` meet the autocorrelation, which is bounded by `‖f‖²`, and `|t_m| ≤ N R^{|m|}`.
* **Sharpness in both directions** (`exists_lagTests_two_sided`): Turán's lower bound for power
  sums puts a lag `ν` in every window `[M + 1, M + N]` with `|t_ν| ≥ R^ν / C_M`, `C_M` polynomial
  in `M`; the two lag tests `g ± g(· − νL)` read `L(N ∓ |t_ν|)‖f‖²`.
* **The rate** (`curve_monodromy_rate`): for an impure curve (`R > 1`) and every `ε > 0`, on all
  long enough lengths `ℓ`, every test has `|W(f, f)| ≤ e^{(δ+ε)ℓ}‖f‖²`, and some tests have
  `Re W ≤ −e^{(δ−ε)ℓ}‖f‖²` and `Re W ≥ e^{(δ−ε)ℓ}‖f‖²`. The degeneration of the family has
  exponential monodromy at exactly the zero width, in both signs.
* **Pure curves** (`norm_W_curveConfig_le_of_pure`): `R = 1` gives the linear bound
  `(2ℓ + L) N ‖f‖²`, rate `0`.

For the golden fake (`β = φ^{±1}` over `𝔽₅`) the rate is `log φ / log 5`.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open ArithmeticCastelnuovoSeveri

/-- The autocorrelation of a test vanishing outside an interval of length `ℓ` vanishes beyond
`ℓ`. -/
theorem weilTest_self_eq_zero_of_length {f : ℝ → ℂ} {x ℓ y : ℝ}
    (hsupp : ∀ u ∉ Set.Icc x (x + ℓ), f u = 0) (hy : ℓ < |y|) : EF.weilTest f f y = 0 := by
  have h : ∀ t, f t * conj (f (t - y)) = 0 := fun t => by
    by_cases ht : t ∈ Set.Icc x (x + ℓ)
    · have hty : t - y ∉ Set.Icc x (x + ℓ) := fun hm => by
        have : |y| ≤ ℓ := abs_le.mpr ⟨by linarith [ht.1, hm.2], by linarith [ht.2, hm.1]⟩
        linarith
      rw [hsupp _ hty, map_zero, mul_zero]
    · rw [hsupp _ ht, zero_mul]
  rw [show EF.weilTest f f y = ∫ t, f t * conj (f (t - y)) by
    simp only [EF.weilTest, convolution_def, ContinuousLinearMap.mul_apply', EF.tilde, neg_sub]]
  simp only [h, integral_zero]

/-- Polynomials lose against exponentials: if `0 ≤ P ℓ ≤ k ℓ` for `ℓ ≥ 1` and `b > 0`, then
`A P(ℓ)^n ≤ e^{bℓ}` for all large `ℓ`. -/
theorem eventually_mul_pow_le_exp {P : ℝ → ℝ} {k A b : ℝ} (n : ℕ) (hA : 0 ≤ A) (hb : 0 < b)
    (hP : ∀ ℓ, 1 ≤ ℓ → 0 ≤ P ℓ ∧ P ℓ ≤ k * ℓ) :
    ∀ᶠ ℓ in atTop, A * P ℓ ^ n ≤ Real.exp (b * ℓ) := by
  have ht := tendsto_exp_mul_div_rpow_atTop (n : ℝ) b hb
  filter_upwards [ht.eventually_ge_atTop (A * |k| ^ n), eventually_ge_atTop 1] with ℓ hℓ h1
  obtain ⟨hP0, hPk⟩ := hP ℓ h1
  have hℓ0 : 0 < ℓ := by linarith
  rw [Real.rpow_natCast, le_div_iff₀ (pow_pos hℓ0 n)] at hℓ
  calc A * P ℓ ^ n ≤ A * (|k| * ℓ) ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hP0
          (hPk.trans (mul_le_mul_of_nonneg_right (le_abs_self k) hℓ0.le)) n) hA
    _ = A * |k| ^ n * ℓ ^ n := by ring
    _ ≤ _ := hℓ

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι) (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq)

/-- **Ceiling and floor on tests of length `ℓ`**: `|W(f, f)| ≤ L (2n + 1) N R^n ‖f‖²` with
`n = ⌊ℓ/L⌋`. Only the lags `|m| ≤ n` meet the autocorrelation, which is bounded by `‖f‖²`, and
`|t_m| ≤ N R^{|m|}`. -/
theorem norm_W_curveConfig_le_of_length {R : ℝ} (hR1 : 1 ≤ R) (hR : ∀ i, ‖D.β i‖ ≤ R)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {x ℓ : ℝ}
    (hsupp : ∀ u ∉ Set.Icc x (x + ℓ), f u = 0) :
    ‖(D.curveConfig hD).W f f‖ ≤ Real.log D.q * (2 * ⌊ℓ / Real.log D.q⌋₊ + 1) *
      Fintype.card ι * R ^ ⌊ℓ / Real.log D.q⌋₊ * ∫ u, ‖f u‖ ^ 2 := by
  have hL := D.log_q_pos
  set n : ℕ := ⌊ℓ / Real.log D.q⌋₊ with hn
  have hN0 : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hI : 0 ≤ ∫ u, ‖f u‖ ^ 2 := integral_nonneg fun _ => by positivity
  have hzero : ∀ m ∉ Finset.Icc (-(n : ℤ)) n,
      EF.weilTest f f (m * Real.log D.q) * (D.trace m.natAbs : ℂ) = 0 := by
    intro m hm
    have hm1 : (n : ℝ) + 1 ≤ |(m : ℝ)| := by
      rw [Finset.mem_Icc, not_and_or] at hm
      rcases hm with h | h
      · have h' : (m : ℝ) ≤ -(n : ℝ) - 1 := by exact_mod_cast (show m ≤ -(n : ℤ) - 1 by omega)
        rw [abs_of_neg (by linarith [Nat.cast_nonneg (α := ℝ) n])]
        linarith
      · have h' : (n : ℝ) + 1 ≤ m := by exact_mod_cast (show (n : ℤ) + 1 ≤ m by omega)
        rw [abs_of_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])]
        exact h'
    have hlt : ℓ < |(m : ℝ) * Real.log D.q| := by
      rw [abs_mul, abs_of_pos hL]
      have h2 : ℓ / Real.log D.q < |(m : ℝ)| := by
        have := Nat.lt_floor_add_one (ℓ / Real.log D.q)
        rw [← hn] at this
        linarith
      rwa [div_lt_iff₀ hL] at h2
    rw [weilTest_self_eq_zero_of_length hsupp hlt, zero_mul]
  have hterm : ∀ m ∈ Finset.Icc (-(n : ℤ)) n,
      ‖EF.weilTest f f (m * Real.log D.q) * (D.trace m.natAbs : ℂ)‖ ≤
        (∫ u, ‖f u‖ ^ 2) * (Fintype.card ι * R ^ n) := by
    intro m hm
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul (RHTower.WeilOneSided.norm_weilTest_self_le_testMass ⟨f, hf, hfc⟩ _) ?_
      (abs_nonneg _) hI
    refine (D.abs_trace_le hR _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR1 ?_) hN0)
    have := Finset.mem_Icc.mp hm
    rcases Int.natAbs_eq m with h | h <;> omega
  have hcard : ((Finset.Icc (-(n : ℤ)) n).card : ℝ) = 2 * n + 1 := by
    rw [Int.card_Icc]
    have : ((n : ℤ) + 1 - -(n : ℤ)).toNat = 2 * n + 1 := by omega
    rw [this]
    push_cast
    ring
  rw [D.W_curveConfig_lagFormula hD hf hfc, tsum_eq_sum hzero, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hL]
  calc Real.log D.q * ‖∑ m ∈ Finset.Icc (-(n : ℤ)) n,
        EF.weilTest f f (m * Real.log D.q) * (D.trace m.natAbs : ℂ)‖
      ≤ Real.log D.q * (((Finset.Icc (-(n : ℤ)) n).card : ℝ) *
          ((∫ u, ‖f u‖ ^ 2) * (Fintype.card ι * R ^ n))) := by
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) hL.le
        have := Finset.sum_le_card_nsmul _ _ _ hterm
        rwa [nsmul_eq_mul] at this
    _ = _ := by rw [hcard]; ring

/-- **The exponential form**: `|W(f, f)| ≤ (2ℓ + L) N e^{δℓ} ‖f‖²`, `δ = log R / L`. -/
theorem norm_W_curveConfig_le_exp {R : ℝ} (hR1 : 1 ≤ R) (hR : ∀ i, ‖D.β i‖ ≤ R)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {x ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hsupp : ∀ u ∉ Set.Icc x (x + ℓ), f u = 0) :
    ‖(D.curveConfig hD).W f f‖ ≤ (2 * ℓ + Real.log D.q) * Fintype.card ι *
      Real.exp (Real.log R / Real.log D.q * ℓ) * ∫ u, ‖f u‖ ^ 2 := by
  have hL := D.log_q_pos
  set n : ℕ := ⌊ℓ / Real.log D.q⌋₊ with hn
  have hnl : (n : ℝ) ≤ ℓ / Real.log D.q := Nat.floor_le (div_nonneg hℓ hL.le)
  have h1 : Real.log D.q * (2 * n + 1) ≤ 2 * ℓ + Real.log D.q := by
    have := (le_div_iff₀ hL).mp hnl
    nlinarith
  have h2 : R ^ n ≤ Real.exp (Real.log R / Real.log D.q * ℓ) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith), Real.exp_le_exp]
    calc Real.log R * n ≤ Real.log R * (ℓ / Real.log D.q) :=
          mul_le_mul_of_nonneg_left hnl (Real.log_nonneg hR1)
      _ = Real.log R / Real.log D.q * ℓ := by ring
  have hI : 0 ≤ ∫ u, ‖f u‖ ^ 2 := integral_nonneg fun _ => by positivity
  have hN0 : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hRn : 0 ≤ R ^ n := pow_nonneg (by linarith) n
  refine (norm_W_curveConfig_le_of_length D hD hR1 hR hf hfc hsupp).trans ?_
  rw [← hn]
  calc Real.log D.q * (2 * n + 1) * Fintype.card ι * R ^ n * ∫ u, ‖f u‖ ^ 2
      = (Real.log D.q * (2 * n + 1)) * (Fintype.card ι * R ^ n * ∫ u, ‖f u‖ ^ 2) := by ring
    _ ≤ (2 * ℓ + Real.log D.q) * (Fintype.card ι *
          Real.exp (Real.log R / Real.log D.q * ℓ) * ∫ u, ‖f u‖ ^ 2) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hN0) hI)
          (by positivity) (by nlinarith)
    _ = _ := by ring

/-- **Pure curves degenerate polynomially**: with all `|β_i| ≤ 1`,
`|W(f, f)| ≤ (2ℓ + L) N ‖f‖²` on tests of length `ℓ`. -/
theorem norm_W_curveConfig_le_of_pure (hpure : ∀ i, ‖D.β i‖ ≤ 1) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {x ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hsupp : ∀ u ∉ Set.Icc x (x + ℓ), f u = 0) :
    ‖(D.curveConfig hD).W f f‖ ≤ (2 * ℓ + Real.log D.q) * Fintype.card ι * ∫ u, ‖f u‖ ^ 2 := by
  have h := norm_W_curveConfig_le_exp D hD le_rfl hpure hf hfc hℓ hsupp
  rwa [Real.log_one, zero_div, zero_mul, Real.exp_zero, mul_one] at h

/-- Turán's constant `C_M = 2e N (6(N + 1)(M + 2N + 2))^N`. -/
def turanConst (N M : ℕ) : ℝ :=
  2 * (Real.exp 1 * N * (6 * ((N : ℝ) + 1) * ((M : ℝ) + 2 * N + 2)) ^ N)

open _root_.RHTower SquareRootThreshold in
/-- **Sharpness in both directions.** If `|β_{i₀}| = R > 1`, then for every `M` some lag
`ν ∈ [M + 1, M + N]` carries two nonzero lag tests `g ± g(· − νL)`, vanishing outside an interval
of length `(ν + ½)L`, with `Re W(fm, fm) ≤ L (N − R^ν/C_M) ‖fm‖²` and
`L (N + R^ν/C_M) ‖fp‖² ≤ Re W(fp, fp)`. -/
theorem exists_lagTests_two_sided {i₀ : ι} (hR : 1 < ‖D.β i₀‖) (M : ℕ) :
    ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + Fintype.card ι ∧
      (∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧
        (∀ u ∉ Set.Icc (-(Real.log D.q / 4))
          (-(Real.log D.q / 4) + (ν + 1 / 2) * Real.log D.q), f u = 0) ∧
        0 < ∫ u, ‖f u‖ ^ 2 ∧
        ((D.curveConfig hD).W f f).re ≤ Real.log D.q *
          (Fintype.card ι - ‖D.β i₀‖ ^ ν / turanConst (Fintype.card ι) M) * ∫ u, ‖f u‖ ^ 2) ∧
      (∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧
        (∀ u ∉ Set.Icc (-(Real.log D.q / 4))
          (-(Real.log D.q / 4) + (ν + 1 / 2) * Real.log D.q), f u = 0) ∧
        0 < ∫ u, ‖f u‖ ^ 2 ∧
        Real.log D.q * (Fintype.card ι + ‖D.β i₀‖ ^ ν / turanConst (Fintype.card ι) M) *
          ∫ u, ‖f u‖ ^ 2 ≤ ((D.curveConfig hD).W f f).re) := by
  have hL := D.log_q_pos
  have hR0 : 0 < ‖D.β i₀‖ := by linarith
  obtain ⟨ν, hν1, hν2, hνT⟩ := HTGeometry.exists_norm_powerSum_ge_scaled Finset.univ
    (fun i => D.β i) hR0 ⟨i₀, Finset.mem_univ _, le_rfl⟩ M
  simp only [Finset.card_univ] at hν2 hνT
  have hT : ‖D.β i₀‖ ^ ν / turanConst (Fintype.card ι) M ≤ |D.trace ν| := by
    rw [D.abs_trace_eq_norm_powerSum]; exact hνT
  refine ⟨ν, hν1, hν2, ?_⟩
  have hw0 : 0 < Real.log D.q / 4 := by positivity
  set g := modScaledBump (Real.log D.q / 4) 0 with hg
  have hg2 : ContDiff ℝ 2 g := contDiff_modScaledBump_two _ 0
  have hgc : HasCompactSupport g := hasCompactSupport_modScaledBump hw0 0
  have hgs : tsupport g ⊆ Set.Icc (-(Real.log D.q / 2 / 2)) (Real.log D.q / 2 / 2) :=
    fun u hu => by
      have := tsupport_modScaledBump_subset hw0 0 hu
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
      have h1 := neg_abs_le u
      have h2 := le_abs_self u
      exact ⟨by linarith, by linarith⟩
  have hwL : Real.log D.q / 2 < Real.log D.q := by linarith
  have hgpos : 0 < ∫ u, ‖g u‖ ^ 2 := integral_norm_sq_modScaledBump_pos hw0
  have hν1' : (1 : ℝ) ≤ ν := by exact_mod_cast (show 1 ≤ ν by omega)
  have hνL : Real.log D.q ≤ ν * Real.log D.q := by nlinarith
  have hvw : Real.log D.q / 2 < ν * Real.log D.q := by linarith
  -- the value of a lag test of sign `s = ±1`
  have hnorm : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      ∫ u, ‖lagTest g s (ν * Real.log D.q) u‖ ^ 2 = 2 * ∫ u, ‖g u‖ ^ 2 := fun s hs =>
    CurveDatum.integral_norm_sq_lagTest hg2.continuous hgs hs hvw
  have hval : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      ((D.curveConfig hD).W (lagTest g s (ν * Real.log D.q))
        (lagTest g s (ν * Real.log D.q))).re =
        Real.log D.q * (Fintype.card ι + s * D.trace ν) *
          ∫ u, ‖lagTest g s (ν * Real.log D.q) u‖ ^ 2 := by
    intro s hs
    rw [D.re_W_curveConfig_lagTest hD hg2 hgs hwL s ν, hnorm s hs, D.trace_zero]
    rcases hs with rfl | rfl <;> ring
  have hsupp : ∀ s : ℝ, ∀ u ∉ Set.Icc (-(Real.log D.q / 4))
      (-(Real.log D.q / 4) + (ν + 1 / 2) * Real.log D.q),
      lagTest g s (ν * Real.log D.q) u = 0 := by
    intro s u hu
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
    have hz : ∀ v : ℝ, Real.log D.q / 4 < |v| → g v = 0 := fun v hv =>
      modScaledBump_eq_zero hw0 hv.le
    simp only [lagTest]
    rcases hu with h | h
    · rw [hz u (by rw [abs_of_neg (by linarith)]; linarith),
        hz (u - ν * Real.log D.q) (by rw [abs_of_neg (by linarith)]; linarith), mul_zero,
        add_zero]
    · rw [hz u (by rw [abs_of_pos (by linarith)]; linarith),
        hz (u - ν * Real.log D.q) (by rw [abs_of_pos (by linarith)]; linarith), mul_zero,
        add_zero]
  have hI0 : ∀ s : ℝ, (s = 1 ∨ s = -1) → 0 < ∫ u, ‖lagTest g s (ν * Real.log D.q) u‖ ^ 2 :=
    fun s hs => by rw [hnorm s hs]; linarith
  have htest : ∀ s : ℝ, ContDiff ℝ 2 (lagTest g s (ν * Real.log D.q)) ∧
      HasCompactSupport (lagTest g s (ν * Real.log D.q)) := fun s =>
    ⟨lagTest_contDiff hg2 _ _, lagTest_hasCompactSupport hgc _ _⟩
  -- the sign `σ` with `σ t_ν = |t_ν|`
  obtain ⟨σ, hσ, hσt⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ σ * D.trace ν = |D.trace ν| := by
    rcases le_or_gt 0 (D.trace ν) with h | h
    · exact ⟨1, Or.inl rfl, by rw [one_mul, abs_of_nonneg h]⟩
    · exact ⟨-1, Or.inr rfl, by rw [abs_of_neg h]; ring⟩
  have hσ' : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
  refine ⟨⟨lagTest g (-σ : ℝ) (ν * Real.log D.q), (htest _).1, (htest _).2, hsupp _, hI0 _ hσ', ?_⟩,
    ⟨lagTest g σ (ν * Real.log D.q), (htest _).1, (htest _).2, hsupp _, hI0 _ hσ, ?_⟩⟩
  · rw [hval _ hσ', neg_mul, hσt]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hL.le) (hI0 _ hσ').le
    linarith
  · rw [hval _ hσ, hσt]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hL.le) (hI0 _ hσ).le
    linarith

/-- **The monodromy rate of an impure curve is its zero width.** Let `R = |β_{i₀}| = max_i |β_i|`
be `> 1` and `δ = log R / log q`. For every `ε > 0` and all large lengths `ℓ`: every test
vanishing outside an interval of length `ℓ` has `|W(f, f)| ≤ e^{(δ+ε)ℓ} ‖f‖²`, and there are
nonzero tests vanishing outside an interval of length `ℓ` with `Re W(f, f) ≤ −e^{(δ−ε)ℓ} ‖f‖²`
and with `e^{(δ−ε)ℓ} ‖f‖² ≤ Re W(f, f)`. -/
theorem curve_monodromy_rate {i₀ : ι} (hmax : ∀ i, ‖D.β i‖ ≤ ‖D.β i₀‖) (hR : 1 < ‖D.β i₀‖)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ ℓ : ℝ in atTop,
      (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f → ∀ x : ℝ,
        (∀ u ∉ Set.Icc x (x + ℓ), f u = 0) →
        ‖(D.curveConfig hD).W f f‖ ≤
          Real.exp ((Real.log ‖D.β i₀‖ / Real.log D.q + ε) * ℓ) * ∫ u, ‖f u‖ ^ 2) ∧
      (∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧
        (∃ x : ℝ, ∀ u ∉ Set.Icc x (x + ℓ), f u = 0) ∧ 0 < ∫ u, ‖f u‖ ^ 2 ∧
        ((D.curveConfig hD).W f f).re ≤
          -(Real.exp ((Real.log ‖D.β i₀‖ / Real.log D.q - ε) * ℓ) * ∫ u, ‖f u‖ ^ 2)) ∧
      (∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧
        (∃ x : ℝ, ∀ u ∉ Set.Icc x (x + ℓ), f u = 0) ∧ 0 < ∫ u, ‖f u‖ ^ 2 ∧
        Real.exp ((Real.log ‖D.β i₀‖ / Real.log D.q - ε) * ℓ) * ∫ u, ‖f u‖ ^ 2 ≤
          ((D.curveConfig hD).W f f).re) := by
  have hL := D.log_q_pos
  set R := ‖D.β i₀‖ with hRdef
  set δ := Real.log R / Real.log D.q with hδ
  set N : ℕ := Fintype.card ι with hNdef
  have hR0 : 0 < R := by linarith
  have hδ0 : 0 < δ := div_pos (Real.log_pos hR) hL
  have hN1 : 1 ≤ N := Fintype.card_pos_iff.mpr ⟨i₀⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  -- the polynomial factor of Turán's constant along `M ≤ ℓ/L`
  set P : ℝ → ℝ := fun ℓ => 6 * ((N : ℝ) + 1) * (ℓ / Real.log D.q + 2 * N + 2) with hP
  have hPk : ∀ ℓ, 1 ≤ ℓ → 0 ≤ P ℓ ∧
      P ℓ ≤ (6 * ((N : ℝ) + 1) * (1 / Real.log D.q + 2 * N + 2)) * ℓ := fun ℓ h1 => by
    have h0 : 0 ≤ ℓ / Real.log D.q := div_nonneg (by linarith) hL.le
    refine ⟨by positivity, ?_⟩
    have e : (6 * ((N : ℝ) + 1) * (1 / Real.log D.q + 2 * N + 2)) * ℓ =
        6 * ((N : ℝ) + 1) * (ℓ / Real.log D.q + (2 * N + 2) * ℓ) := by ring
    rw [e]
    have : (2 * (N : ℝ) + 2) ≤ (2 * N + 2) * ℓ := by nlinarith
    show 6 * ((N : ℝ) + 1) * (ℓ / Real.log D.q + 2 * N + 2) ≤ _
    have h6 : 0 ≤ 6 * ((N : ℝ) + 1) := by positivity
    nlinarith
  set Ac : ℝ := 2 * (Real.exp 1 * N) with hAc
  have hAc0 : 0 < Ac := by positivity
  have hPpos : ∀ ℓ, 0 ≤ ℓ → 0 < P ℓ := fun ℓ hℓ => by
    have : 0 ≤ ℓ / Real.log D.q := div_nonneg hℓ hL.le
    show 0 < 6 * ((N : ℝ) + 1) * (ℓ / Real.log D.q + 2 * N + 2)
    positivity
  have E1 := eventually_mul_pow_le_exp (P := fun ℓ => (2 * ℓ + Real.log D.q) * N)
    (k := (2 + Real.log D.q) * N) (A := 1) 1 zero_le_one hε fun ℓ h1 =>
      ⟨by positivity, by
        have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hL.le hN0.le)
        nlinarith⟩
  have E2 := eventually_mul_pow_le_exp (P := P) N
    (A := 2 * N * R ^ (N + 1) * Ac) (by positivity) hδ0 hPk
  have E3 := eventually_mul_pow_le_exp (P := P) N
    (A := 2 * R ^ (N + 1) * Ac / Real.log D.q) (by positivity) hε hPk
  filter_upwards [E1, E2, E3, eventually_ge_atTop ((N + 2) * Real.log D.q),
    eventually_ge_atTop 1] with ℓ h1 h2 h3 h4 h5
  have hℓ0 : 0 ≤ ℓ := by linarith
  refine ⟨fun f hf hfc x hsupp => ?_, ?_⟩
  · -- the ceiling
    have hb := norm_W_curveConfig_le_exp D hD hR.le hmax hf hfc hℓ0 hsupp
    simp only [pow_one, one_mul] at h1
    have hI : 0 ≤ ∫ u, ‖f u‖ ^ 2 := integral_nonneg fun _ => by positivity
    refine hb.trans ?_
    rw [show (δ + ε) * ℓ = δ * ℓ + ε * ℓ by ring, Real.exp_add]
    calc (2 * ℓ + Real.log D.q) * N * Real.exp (δ * ℓ) * ∫ u, ‖f u‖ ^ 2
        = ((2 * ℓ + Real.log D.q) * N) * (Real.exp (δ * ℓ) * ∫ u, ‖f u‖ ^ 2) := by ring
      _ ≤ Real.exp (ε * ℓ) * (Real.exp (δ * ℓ) * ∫ u, ‖f u‖ ^ 2) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by ring
  -- the lag window below `ℓ/L`
  set m : ℕ := ⌊ℓ / Real.log D.q⌋₊ with hm
  have hmN : N + 2 ≤ m := Nat.le_floor (by
    rw [le_div_iff₀ hL]; push_cast; linarith)
  have hmle : (m : ℝ) ≤ ℓ / Real.log D.q := Nat.floor_le (div_nonneg hℓ0 hL.le)
  have hmlt : ℓ / Real.log D.q < m + 1 := Nat.lt_floor_add_one _
  obtain ⟨ν, hν1, hν2, ⟨fm, hfm, hfcm, hsm, hIm, hWm⟩, ⟨fp, hfp, hfcp, hsp, hIp, hWp⟩⟩ :=
    exists_lagTests_two_sided D hD hR (m - (N + 1))
  -- the support fits in length `ℓ`
  have hνm : ν + 1 ≤ m := by omega
  have hfit : (ν + 1 / 2 : ℝ) * Real.log D.q ≤ ℓ := by
    have : ((ν + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hνm
    push_cast at this
    have := (le_div_iff₀ hL).mp (this.trans hmle)
    nlinarith
  have hsub : ∀ u ∉ Set.Icc (-(Real.log D.q / 4)) (-(Real.log D.q / 4) + ℓ),
      u ∉ Set.Icc (-(Real.log D.q / 4)) (-(Real.log D.q / 4) + (ν + 1 / 2) * Real.log D.q) :=
    fun u hu hu' => hu ⟨hu'.1, by linarith [hu'.2]⟩
  -- Turán's bound against `e^{δℓ}`
  have hνlow : ℓ / Real.log D.q ≤ ((ν + N + 1 : ℕ) : ℝ) := by
    have : m ≤ ν + N := by omega
    have : ((m + 1 : ℕ) : ℝ) ≤ ((ν + N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    push_cast at this ⊢
    linarith
  have hRν : Real.exp (δ * ℓ) / R ^ (N + 1) ≤ R ^ ν := by
    rw [div_le_iff₀ (pow_pos hR0 _), ← pow_add, ← Real.rpow_natCast, Real.rpow_def_of_pos hR0,
      Real.exp_le_exp]
    calc δ * ℓ = Real.log R * (ℓ / Real.log D.q) := by rw [hδ]; ring
      _ ≤ Real.log R * ((ν + N + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hνlow (Real.log_nonneg hR.le)
      _ = _ := by push_cast; ring
  have hMle : ((m - (N + 1) : ℕ) : ℝ) ≤ ℓ / Real.log D.q :=
    le_trans (by exact_mod_cast Nat.sub_le m (N + 1)) hmle
  have hbase : 6 * ((N : ℝ) + 1) * (((m - (N + 1) : ℕ) : ℝ) + 2 * N + 2) ≤ P ℓ := by
    show _ ≤ 6 * ((N : ℝ) + 1) * (ℓ / Real.log D.q + 2 * N + 2)
    gcongr
  have hC : turanConst N (m - (N + 1)) ≤ Ac * P ℓ ^ N := by
    calc turanConst N (m - (N + 1)) =
          Ac * (6 * ((N : ℝ) + 1) * (((m - (N + 1) : ℕ) : ℝ) + 2 * N + 2)) ^ N := by
          unfold turanConst; rw [hAc]; ring
      _ ≤ Ac * P ℓ ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase N) hAc0.le
  have hCpos : 0 < turanConst N (m - (N + 1)) := by unfold turanConst; positivity
  set D₀ := R ^ (N + 1) * (Ac * P ℓ ^ N) with hD₀
  have hD₀pos : 0 < D₀ := by have := hPpos ℓ hℓ0; positivity
  set X := Real.exp (δ * ℓ) / D₀ with hX
  have hY : X ≤ R ^ ν / turanConst N (m - (N + 1)) := by
    rw [hX, hD₀, ← div_div]
    exact div_le_div₀ (pow_nonneg hR0.le _) hRν hCpos hC
  have hX2 : 2 * N ≤ X := by
    rw [hX, le_div_iff₀ hD₀pos]
    calc 2 * (N : ℝ) * D₀ = 2 * N * R ^ (N + 1) * Ac * P ℓ ^ N := by rw [hD₀]; ring
      _ ≤ _ := h2
  have hX3 : Real.exp ((δ - ε) * ℓ) ≤ Real.log D.q * X / 2 := by
    rw [sub_mul, Real.exp_sub, hX, div_le_iff₀ (Real.exp_pos _)]
    have hA3 : 2 * D₀ / Real.log D.q ≤ Real.exp (ε * ℓ) := by
      calc 2 * D₀ / Real.log D.q = 2 * R ^ (N + 1) * Ac / Real.log D.q * P ℓ ^ N := by
            rw [hD₀]; ring
        _ ≤ _ := h3
    have hE : 0 ≤ Real.exp (δ * ℓ) := (Real.exp_pos _).le
    calc Real.exp (δ * ℓ) = Real.log D.q * (Real.exp (δ * ℓ) / D₀) / 2 * (2 * D₀ / Real.log D.q) := by
          field_simp
      _ ≤ Real.log D.q * (Real.exp (δ * ℓ) / D₀) / 2 * Real.exp (ε * ℓ) :=
          mul_le_mul_of_nonneg_left hA3 (by positivity)
  refine ⟨⟨fm, hfm, hfcm, ⟨_, fun u hu => hsm u (hsub u hu)⟩, hIm, hWm.trans ?_⟩,
    ⟨fp, hfp, hfcp, ⟨_, fun u hu => hsp u (hsub u hu)⟩, hIp, le_trans ?_ hWp⟩⟩
  · rw [neg_mul_eq_neg_mul]
    refine mul_le_mul_of_nonneg_right ?_ hIm.le
    have hY' : (N : ℝ) - R ^ ν / turanConst N (m - (N + 1)) ≤ -(X / 2) := by linarith
    calc Real.log D.q * ((N : ℝ) - R ^ ν / turanConst N (m - (N + 1)))
        ≤ Real.log D.q * (-(X / 2)) := mul_le_mul_of_nonneg_left hY' hL.le
      _ = -(Real.log D.q * X / 2) := by ring
      _ ≤ _ := neg_le_neg hX3
  · refine mul_le_mul_of_nonneg_right ?_ hIp.le
    have hX0 : 0 ≤ X := by positivity
    have hY' : X / 2 ≤ (N : ℝ) + R ^ ν / turanConst N (m - (N + 1)) := by linarith
    calc Real.exp ((δ - ε) * ℓ) ≤ Real.log D.q * X / 2 := hX3
      _ = Real.log D.q * (X / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hY' hL.le

end CurveDatum

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
