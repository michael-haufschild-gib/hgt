import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheDegreeFiltrationOfACurveIsItsWindowFiltration
import GaloisForLFunctions.HTGeometry.PowerSumTuranLowerBound
import GaloisForLFunctions.RHTower.JointAncestryShellPowerSumCriterion

/-!
# The first negative lag of a curve

Square-Root Threshold detects an attained off-line top of `ζ` by a *lag test*: two narrow bumps at
distance `v`, whose Weil form turns negative at an explicit lag
(`SquareRootThreshold.zeta_attained_top_first_negative_lag`). This file calibrates that law over
`𝔽_q`, on the scaling surface of a curve datum.

* **The lag test reads one point count** (`re_W_curveConfig_lagTest`). For a narrow bump `g` and
  `L = log q`, the test `g + s·g(· − nL)`, `s ∈ ℝ`, has
  `Re W = L‖g‖² ((1 + s²) t₀ + 2s tₙ)` with `tₙ = Σ_i β_i^n` and `t₀ = 2g`: the lag `nL` sees the
  `n`-th point count `N_n = q^n + 1 − q^{n/2} tₙ` and nothing else, so `s = ∓1` tests the two
  Hasse–Weil inequalities `|tₙ| ≤ 2g` for `N_n`.
* **Purity is lag positivity** (`re_W_curveConfig_lagTest_nonneg`, `exists_negative_lagTest`). If
  every eigenvalue lies on the unit circle, no lag test is negative; if one lies outside, some lag
  test is negative, at a lag in every window `[M + 1, M + 2g]` once
  `2g · R^{−(M+1)} · 2e·2g·(6(2g + 1)(M + 4g + 2))^{2g} < 1`, `R` the modulus of an outer
  eigenvalue. The lag is located by Turán's power-sum theorem
  (`HTGeometry.exists_norm_powerSum_ge_scaled`), which over `𝔽_q` replaces the Bohr-set argument
  used for `ζ`; there is no horizon, since the eigenvalues are finitely many.
* **The golden fake curve is seen at lag `log 5`** (`goldenDatum_lagTest_neg`): `t₁ = √5 > 2`.

So over `𝔽_q` the lag family alone decides the Riemann hypothesis of a curve. The window family of
`TheDegreeFiltrationOfACurveIsItsWindowFiltration` sees an impure curve by the degree
`(2g − 1) log q / 2`, whatever the depth `R`; a single lag is located only up to a window whose
position grows like `log(1/(R − 1))`.
-/

open Complex MeasureTheory Finset
open scoped Real ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- The lag test `g + s·g(· − v)`: two copies of `g` at distance `v`. -/
def lagTest (g : ℝ → ℂ) (s : ℂ) (v : ℝ) : ℝ → ℂ := fun t => g t + s * g (t - v)

theorem lagTest_eq_sum (g : ℝ → ℂ) (s : ℂ) (v : ℝ) :
    lagTest g s v = fun t => ∑ p : Fin 2, (![1, s] : Fin 2 → ℂ) p *
      (![translate 0 g, translate v g] : Fin 2 → ℝ → ℂ) p t := by
  funext t
  simp [lagTest, Fin.sum_univ_two, translate]

theorem lagTest_contDiff {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (s : ℂ) (v : ℝ) :
    ContDiff ℝ 2 (lagTest g s v) :=
  hg.add (contDiff_const.mul (translate_contDiff hg v))

theorem lagTest_hasCompactSupport {g : ℝ → ℂ} (hgc : HasCompactSupport g) (s : ℂ) (v : ℝ) :
    HasCompactSupport (lagTest g s v) :=
  hgc.add (translate_hasCompactSupport hgc v).mul_left

/-- **A lag test on a lag lattice** reads the symbol at `0` and `±n`. -/
theorem hasSum_lag_lagTest {g : ℝ → ℂ} {w ℓ : ℝ} (hℓ : 0 < ℓ) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Set.Icc (-(w / 2)) (w / 2)) (hwℓ : w < ℓ)
    (D : ℤ → ℂ) (s : ℂ) (n : ℕ) :
    HasSum (fun m : ℤ =>
        EF.weilTest (lagTest g s (n * ℓ)) (lagTest g s (n * ℓ)) (m * ℓ) * D m)
      (EF.weilTest g g 0 * ((1 + s * conj s) * D 0 + s * D n + conj s * D (-n))) := by
  have hφ : ∀ p : Fin 2,
      Continuous ((![translate 0 g, translate (n * ℓ) g] : Fin 2 → ℝ → ℂ) p) := by
    intro p
    fin_cases p <;> exact hg.comp (continuous_sub_right _)
  have hφc : ∀ p : Fin 2,
      HasCompactSupport ((![translate 0 g, translate (n * ℓ) g] : Fin 2 → ℝ → ℂ) p) := by
    intro p
    fin_cases p <;> exact translate_hasCompactSupport hgc _
  have e : ∀ m : ℤ,
      EF.weilTest (lagTest g s (n * ℓ)) (lagTest g s (n * ℓ)) (m * ℓ) * D m =
        EF.weilTest (translate 0 g) (translate 0 g) (m * ℓ) * D m +
          conj s * (EF.weilTest (translate 0 g) (translate (n * ℓ) g) (m * ℓ) * D m) +
          s * (EF.weilTest (translate (n * ℓ) g) (translate 0 g) (m * ℓ) * D m) +
          s * conj s * (EF.weilTest (translate (n * ℓ) g) (translate (n * ℓ) g) (m * ℓ) * D m) :=
    fun m => by
      rw [lagTest_eq_sum, weilTest_finset_sum _ _ hφ hφc hφ]
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_one]
      ring
  rw [funext e]
  have h00 := hasSum_lag_translate_coset hℓ hgs hwℓ D (x := 0) (y := 0) (k := 0) (by simp)
  have h0n := hasSum_lag_translate_coset hℓ hgs hwℓ D (x := 0) (y := n * ℓ) (k := -n)
    (by push_cast; ring)
  have hn0 := hasSum_lag_translate_coset hℓ hgs hwℓ D (x := n * ℓ) (y := 0) (k := n)
    (by push_cast; ring)
  have hnn := hasSum_lag_translate_coset hℓ hgs hwℓ D (x := n * ℓ) (y := n * ℓ) (k := 0)
    (by simp)
  convert ((h00.add (h0n.mul_left (conj s))).add (hn0.mul_left s)).add
    (hnn.mul_left (s * conj s)) using 1
  ring

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι) (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq)

/-- `|tₙ| = |Σ_i β_i^n|`: the trace is the real power sum. -/
theorem abs_trace_eq_norm_powerSum (n : ℕ) : |D.trace n| = ‖∑ i, D.β i ^ n‖ := by
  rw [show ∑ i, D.β i ^ n = D.powerSum n from rfl, D.powerSum_eq_trace, Complex.norm_real,
    Real.norm_eq_abs]

/-- **The lag test reads one point count.** For a narrow bump `g` and real `s`,
`Re W(g + s·g(· − n log q)) = log q · ‖g‖² · ((1 + s²) t₀ + 2s tₙ)`. -/
theorem re_W_curveConfig_lagTest {g : ℝ → ℂ} {w : ℝ} (hg : ContDiff ℝ 2 g)
    (hgs : tsupport g ⊆ Set.Icc (-(w / 2)) (w / 2)) (hwL : w < Real.log D.q) (s : ℝ) (n : ℕ) :
    ((D.curveConfig hD).W (lagTest g s (n * Real.log D.q))
        (lagTest g s (n * Real.log D.q))).re =
      Real.log D.q * (∫ u, ‖g u‖ ^ 2) * ((1 + s ^ 2) * D.trace 0 + 2 * s * D.trace n) := by
  have hL := D.log_q_pos
  have hgc : HasCompactSupport g := RHTower.hasCompactSupport_of_tsupport_subset_Icc hgs
  rw [D.W_curveConfig_lagFormula hD (lagTest_contDiff hg _ _) (lagTest_hasCompactSupport hgc _ _),
    (hasSum_lag_lagTest hL hg.continuous hgc hgs hwL _ s n).tsum_eq, weilTest_self_zero]
  simp only [Int.natAbs_zero, Int.natAbs_neg, Int.natAbs_natCast, Complex.conj_ofReal]
  rw [show ((Real.log D.q : ℝ) : ℂ) * (((∫ u, ‖g u‖ ^ 2 : ℝ) : ℂ) *
      ((1 + (s : ℂ) * s) * (D.trace 0 : ℂ) + s * (D.trace n : ℂ) + s * (D.trace n : ℂ))) =
        ((Real.log D.q * (∫ u, ‖g u‖ ^ 2) * ((1 + s ^ 2) * D.trace 0 + 2 * s * D.trace n) :
          ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]

/-- **A pure curve has no negative lag.** If every eigenvalue lies in the closed unit disc, every
lag test has nonnegative Weil form. -/
theorem re_W_curveConfig_lagTest_nonneg (hpure : ∀ i, ‖D.β i‖ ≤ 1) {g : ℝ → ℂ} {w : ℝ}
    (hg : ContDiff ℝ 2 g) (hgs : tsupport g ⊆ Set.Icc (-(w / 2)) (w / 2))
    (hwL : w < Real.log D.q) (s : ℝ) (n : ℕ) :
    0 ≤ ((D.curveConfig hD).W (lagTest g s (n * Real.log D.q))
      (lagTest g s (n * Real.log D.q))).re := by
  rw [D.re_W_curveConfig_lagTest hD hg hgs hwL s n, D.trace_zero]
  have htn : |D.trace n| ≤ Fintype.card ι := by
    rw [D.abs_trace_eq_norm_powerSum]
    calc ‖∑ i, D.β i ^ n‖ ≤ ∑ i, ‖D.β i ^ n‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
          rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hpure i)
      _ = Fintype.card ι := by simp
  have hK : 0 ≤ Real.log D.q * ∫ u, ‖g u‖ ^ 2 :=
    mul_nonneg D.log_q_pos.le (integral_nonneg fun _ => by positivity)
  have hc : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hst : -(|s| * Fintype.card ι) ≤ s * D.trace n := by
    have := abs_le.mp (show |s * D.trace n| ≤ |s| * Fintype.card ι by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left htn (abs_nonneg s))
    exact this.1
  have hsq : 0 ≤ (1 + s ^ 2) * Fintype.card ι + 2 * s * D.trace n := by
    nlinarith [sq_abs s, sq_nonneg (|s| - 1), mul_nonneg (sq_nonneg (|s| - 1)) hc]
  exact mul_nonneg hK hsq

/-- **Turán locates a negative lag.** If an eigenvalue has modulus `R > 1` and `M` satisfies
`N · R^{−(M+1)} · 2e·N·(6(N + 1)(M + 2N + 2))^N < 1`, `N = 2g` the number of eigenvalues, then for
every narrow nonzero bump some lag `n ∈ [M + 1, M + N]` and sign `s = ±1` give a negative lag
test. -/
theorem exists_negative_lagTest_of_window {i₀ : ι} (hR : 1 < ‖D.β i₀‖) {M : ℕ}
    (hM : (Fintype.card ι : ℝ) * (‖D.β i₀‖⁻¹) ^ (M + 1) *
      (2 * (Real.exp 1 * Fintype.card ι * (6 * (Fintype.card ι + 1) *
        ((M : ℝ) + 2 * Fintype.card ι + 2)) ^ Fintype.card ι)) < 1)
    {g : ℝ → ℂ} {w : ℝ} (hg : ContDiff ℝ 2 g) (hgs : tsupport g ⊆ Set.Icc (-(w / 2)) (w / 2))
    (hwL : w < Real.log D.q) (hg0 : 0 < ∫ u, ‖g u‖ ^ 2) :
    ∃ n : ℕ, M + 1 ≤ n ∧ n ≤ M + Fintype.card ι ∧ ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ((D.curveConfig hD).W (lagTest g s (n * Real.log D.q))
        (lagTest g s (n * Real.log D.q))).re < 0 := by
  set R := ‖D.β i₀‖ with hRdef
  set N : ℕ := Fintype.card ι with hN
  have hR0 : 0 < R := by linarith
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨i₀⟩)
  set C : ℝ := 2 * (Real.exp 1 * N * (6 * (N + 1) * ((M : ℝ) + 2 * N + 2)) ^ N) with hC
  have hC0 : 0 < C := mul_pos two_pos (mul_pos (mul_pos (Real.exp_pos 1) hN0)
    (pow_pos (by positivity) N))
  obtain ⟨ν, hν1, hν2, hνT⟩ := exists_norm_powerSum_ge_scaled Finset.univ (fun i => D.β i) hR0
    ⟨i₀, Finset.mem_univ _, le_rfl⟩ M
  simp only [Finset.card_univ] at hν2 hνT
  refine ⟨ν, hν1, hν2, ?_⟩
  -- the power sum at `ν` exceeds the number of eigenvalues
  have hpow : R ^ (M + 1) ≤ R ^ ν := pow_le_pow_right₀ hR.le hν1
  have hRM : (N : ℝ) * C < R ^ (M + 1) := by
    have hRpos : 0 < R ^ (M + 1) := pow_pos hR0 _
    have h' : (N : ℝ) * C / R ^ (M + 1) < 1 := by
      rw [div_eq_mul_inv, ← inv_pow]
      linarith [hM]
    exact (div_lt_one hRpos).mp h'
  have hbig : (N : ℝ) < |D.trace ν| := by
    rw [D.abs_trace_eq_norm_powerSum]
    have h1 : R ^ ν / C ≤ ‖∑ i, D.β i ^ ν‖ := hνT
    have h2 : (N : ℝ) < R ^ ν / C := by
      rw [lt_div_iff₀ hC0]; linarith
    linarith
  have hK : 0 < Real.log D.q * ∫ u, ‖g u‖ ^ 2 := mul_pos D.log_q_pos hg0
  rcases le_or_gt 0 (D.trace ν) with hpos | hneg
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rw [D.re_W_curveConfig_lagTest hD hg hgs hwL, D.trace_zero, ← hN]
    rw [abs_of_nonneg hpos] at hbig
    have : (1 + (-1 : ℝ) ^ 2) * N + 2 * (-1) * D.trace ν < 0 := by nlinarith
    nlinarith
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [D.re_W_curveConfig_lagTest hD hg hgs hwL, D.trace_zero, ← hN]
    rw [abs_of_neg hneg] at hbig
    have : (1 + (1 : ℝ) ^ 2) * N + 2 * 1 * D.trace ν < 0 := by nlinarith
    nlinarith

/-- **Purity is lag positivity.** A curve datum in the strip has an eigenvalue outside the unit
circle iff some lag test on its scaling surface is negative; the lag can be taken in a window
`[M + 1, M + 2g]` located by Turán's theorem. -/
theorem exists_negative_lagTest {i₀ : ι} (hR : 1 < ‖D.β i₀‖) {g : ℝ → ℂ} {w : ℝ}
    (hg : ContDiff ℝ 2 g) (hgs : tsupport g ⊆ Set.Icc (-(w / 2)) (w / 2))
    (hwL : w < Real.log D.q) (hg0 : 0 < ∫ u, ‖g u‖ ^ 2) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ((D.curveConfig hD).W (lagTest g s (n * Real.log D.q))
        (lagTest g s (n * Real.log D.q))).re < 0 := by
  have hρ0 : 0 < ‖D.β i₀‖⁻¹ := inv_pos.mpr (by linarith)
  have hρ1 : ‖D.β i₀‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  obtain ⟨M, hM⟩ := RHTower.exists_turan_window (Fintype.card ι) hρ0 hρ1
    (Fintype.card ι) (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨n, hn1, -, s, hs, hneg⟩ := D.exists_negative_lagTest_of_window hD hR
    (lt_of_le_of_lt hM (by norm_num)) hg hgs hwL hg0
  exact ⟨n, by omega, s, hs, hneg⟩

end CurveDatum

open Real in
/-- **The golden fake curve is seen at lag `log 5`**: `t₁ = φ + φ⁻¹ = √5 > 2`, so
`g − g(· − log 5)` has negative Weil form. -/
theorem goldenDatum_lagTest_neg {g : ℝ → ℂ} {w : ℝ} (hg : ContDiff ℝ 2 g)
    (hgs : tsupport g ⊆ Set.Icc (-(w / 2)) (w / 2)) (hwL : w < Real.log goldenDatum.q)
    (hg0 : 0 < ∫ u, ‖g u‖ ^ 2) :
    ((goldenDatum.curveConfig goldenDatum_strip).W
        (lagTest g (-1 : ℝ) ((1 : ℕ) * Real.log goldenDatum.q))
        (lagTest g (-1 : ℝ) ((1 : ℕ) * Real.log goldenDatum.q))).re < 0 := by
  rw [goldenDatum.re_W_curveConfig_lagTest goldenDatum_strip hg hgs hwL, goldenDatum_trace,
    goldenDatum_trace]
  have hφ : goldenRatio + goldenRatio⁻¹ = Real.sqrt 5 := by
    rw [inv_goldenRatio]
    simp only [goldenRatio, goldenConj]
    ring
  have h5 : (2 : ℝ) < Real.sqrt 5 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hK : 0 < Real.log goldenDatum.q * ∫ u, ‖g u‖ ^ 2 := mul_pos goldenDatum.log_q_pos hg0
  simp only [pow_zero, pow_one]
  rw [hφ]
  nlinarith

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
