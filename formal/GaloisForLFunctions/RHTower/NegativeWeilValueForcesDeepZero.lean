import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection

/-!
# Negative Weil value forces a deep zero nearby

A negative value of the Weil form on a test localized at height `t` can only come from zeros
near `t` whose depth is large on the scale `1/a`.  For `f(u) = e^{-itu} s(u)`, with `s` real,
`C²` and supported in `[-a, a]`, every zero contributes at most
`16 m_ρ N² e^{2|β-½|a}/(1 + |γ - t|)⁴`, with `N = ‖s‖₁ + ‖s''‖₁`.  Summing against the local
count `N(t, t+1] ≤ A₀ log(|t| + 3)` gives:

> if `Re W(f, f) ≤ -μ < 0`, then either `μ ≤ 768 A₀ log(|t| + 3) N² e^a/(1 + R)`, or some zero `ρ`
> with `|γ - t| ≤ R` has `μ ≤ 768 A₀ log(|t| + 3) N² (e^{2|β-½|a} + e^a/(1 + R))`.

In depth form: a negative value of size `μ ≫ A₀ N² log t` at height `t` forces a zero within `R`
of depth `β - ½ ≥ log(μ/(768 A₀ N² log t))/(2a)`, up to the far-zero term `e^a/(1 + R)`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

/-- **A negative Weil value forces a deep zero nearby.** -/
theorem exists_deep_zero_of_negative_weil (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (t : ℝ) {a R μ : ℝ}
    (ha : 0 ≤ a) (hR : 0 ≤ R) (hμ : 0 < μ) {s : ℝ → ℝ} (hs : ContDiff ℝ 2 s)
    (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a)
    (hneg : (Z.W (modulatedTest t s) (modulatedTest t s)).re ≤ -μ) :
    μ ≤ 768 * A₀ * Real.log (|t| + 3) * testNorm s ^ 2 * (Real.exp a / (1 + R)) ∨
      ∃ ρ ∈ Z.carrier, |ρ.im - t| ≤ R ∧
        μ ≤ 768 * A₀ * Real.log (|t| + 3) * testNorm s ^ 2 *
          (Real.exp (2 * |1 / 2 - ρ.re| * a) + Real.exp a / (1 + R)) := by
  classical
  by_contra hcon
  rw [not_or, not_le, not_exists] at hcon
  obtain ⟨hfar, hnear⟩ := hcon
  set L₀ := Real.log (|t| + 3) with hL₀
  have hL₀1 : 1 ≤ L₀ := one_le_log_abs_add_three t
  set N := testNorm s with hNdef
  have hN0 : 0 ≤ N := testNorm_nonneg s
  have hR0 : 0 < 1 + R := by linarith
  rcases eq_or_lt_of_le hN0 with hN | hNpos
  · -- a vanishing test has vanishing Weil form
    have hz : ∀ ρ : Z.carrier, Z.Wsummand (modulatedTest t s) (modulatedTest t s) ρ = 0 := by
      intro ρ
      have hterm := norm_Wsummand_modulatedTest_le Z t hs hsupp (ρ : ℂ)
      rw [← hNdef, ← hN] at hterm
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        zero_div] at hterm
      exact norm_le_zero_iff.mp hterm
    have : Z.W (modulatedTest t s) (modulatedTest t s) = 0 := by
      rw [ZeroConfig.W]; simp [hz]
    rw [this, Complex.zero_re] at hneg
    linarith
  set C := 768 * A₀ * L₀ * N ^ 2 with hC
  have hC0 : 0 < C := by
    have : 0 < A₀ := by linarith
    positivity
  obtain ⟨hwsum, hwle⟩ := window_tsum_le Z hA₀ hloc t
  -- every term is bounded by `(μ/(48 A₀ L₀)) m_ρ/(1 + |γ - t|)³`
  have hbound : ∀ ρ : Z.carrier,
      ‖Z.Wsummand (modulatedTest t s) (modulatedTest t s) ρ‖ ≤
        μ / (48 * A₀ * L₀) * ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - t|) ^ 3) := by
    intro ρ
    have hm : (0 : ℝ) ≤ Z.mult (ρ : ℂ) := Nat.cast_nonneg _
    set D := 1 + |(ρ : ℂ).im - t| with hD
    have hD1 : 1 ≤ D := by linarith [abs_nonneg ((ρ : ℂ).im - t)]
    have hD0 : 0 < D := by linarith
    have hE : Real.exp (|1 / 2 - (ρ : ℂ).re| * a) ^ 2 = Real.exp (2 * |1 / 2 - (ρ : ℂ).re| * a) := by
      rw [sq, ← Real.exp_add]; ring_nf
    have hterm := norm_Wsummand_modulatedTest_le Z t hs hsupp (ρ : ℂ)
    rw [hE] at hterm
    -- the exponential factor is bounded by `μ/C - e^a/(1+R)` near, by `e^a/(1+R)·D` far
    have hkey : Real.exp (2 * |1 / 2 - (ρ : ℂ).re| * a) / D ^ 4 ≤ (μ / C) / D ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      rcases le_or_gt |(ρ : ℂ).im - t| R with hnr | hfr
      · have h := hnear (ρ : ℂ)
        simp only [not_and, not_le] at h
        have h' := h ρ.2 hnr
        have hlt : Real.exp (2 * |1 / 2 - (ρ : ℂ).re| * a) ≤ μ / C := by
          rw [le_div_iff₀ hC0]
          have : 0 ≤ C * (Real.exp a / (1 + R)) := by positivity
          nlinarith
        calc Real.exp (2 * |1 / 2 - (ρ : ℂ).re| * a) * D ^ 3
            ≤ μ / C * D ^ 3 := mul_le_mul_of_nonneg_right hlt (by positivity)
          _ ≤ μ / C * D ^ 4 := by
              apply mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD1 (by norm_num))
              exact (div_pos hμ hC0).le
      · have hst := Z.strip _ ρ.2
        have hex : Real.exp (2 * |1 / 2 - (ρ : ℂ).re| * a) ≤ Real.exp a := by
          apply Real.exp_le_exp.mpr
          have : |1 / 2 - (ρ : ℂ).re| ≤ 1 / 2 := by
            rw [abs_le]; constructor <;> linarith [hst.1, hst.2]
          nlinarith
        have hfar' : Real.exp a / (1 + R) ≤ μ / C := by
          rw [le_div_iff₀ hC0]; linarith [hfar]
        have hDR : 1 + R ≤ D := by rw [hD]; linarith
        calc Real.exp (2 * |1 / 2 - (ρ : ℂ).re| * a) * D ^ 3 ≤ Real.exp a * D ^ 3 :=
              mul_le_mul_of_nonneg_right hex (by positivity)
          _ = Real.exp a / (1 + R) * ((1 + R) * D ^ 3) := by field_simp
          _ ≤ μ / C * (D * D ^ 3) := by
              apply mul_le_mul hfar' (mul_le_mul_of_nonneg_right hDR (by positivity))
                (by positivity) (div_pos hμ hC0).le
          _ = μ / C * D ^ 4 := by ring
    calc ‖Z.Wsummand (modulatedTest t s) (modulatedTest t s) ρ‖
        ≤ (Z.mult (ρ : ℂ) : ℝ) * (Real.exp (2 * |1 / 2 - (ρ : ℂ).re| * a) * (16 * N ^ 2)) /
            D ^ 4 := hterm
      _ = 16 * N ^ 2 * (Z.mult (ρ : ℂ) : ℝ) *
            (Real.exp (2 * |1 / 2 - (ρ : ℂ).re| * a) / D ^ 4) := by ring
      _ ≤ 16 * N ^ 2 * (Z.mult (ρ : ℂ) : ℝ) * ((μ / C) / D ^ 3) := by
          apply mul_le_mul_of_nonneg_left hkey; positivity
      _ = μ / (48 * A₀ * L₀) * ((Z.mult ρ : ℝ) / D ^ 3) := by
          have hNne : N ≠ 0 := hNpos.ne'
          have hA : A₀ ≠ 0 := by linarith
          have hL : L₀ ≠ 0 := by linarith
          rw [hC]; field_simp; ring
  have hsumm : Summable (fun ρ : Z.carrier =>
      Z.Wsummand (modulatedTest t s) (modulatedTest t s) ρ) :=
    Summable.of_norm_bounded (hwsum.mul_left _) hbound
  have hnorm : ‖Z.W (modulatedTest t s) (modulatedTest t s)‖ ≤ μ / 2 := by
    rw [ZeroConfig.W]
    have hns : Summable (fun ρ : Z.carrier =>
        ‖Z.Wsummand (modulatedTest t s) (modulatedTest t s) ρ‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound (hwsum.mul_left _)
    calc ‖∑' ρ : Z.carrier, Z.Wsummand (modulatedTest t s) (modulatedTest t s) ρ‖
        ≤ ∑' ρ : Z.carrier, ‖Z.Wsummand (modulatedTest t s) (modulatedTest t s) ρ‖ :=
          norm_tsum_le_tsum_norm hns
      _ ≤ ∑' ρ : Z.carrier, μ / (48 * A₀ * L₀) * ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - t|) ^ 3) :=
          Summable.tsum_le_tsum hbound hns (hwsum.mul_left _)
      _ = μ / (48 * A₀ * L₀) *
            ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - t|) ^ 3 := tsum_mul_left
      _ ≤ μ / (48 * A₀ * L₀) * (24 * A₀ * L₀) :=
          mul_le_mul_of_nonneg_left hwle (by positivity)
      _ = μ / 2 := by
          have hA : A₀ ≠ 0 := by linarith
          have hL : L₀ ≠ 0 := by linarith
          field_simp; ring
  have hre := neg_le_of_abs_le (Complex.abs_re_le_norm (Z.W (modulatedTest t s) (modulatedTest t s)))
  linarith

/-- The same for the nontrivial zeros of `ζ`, with the unconditional local count. -/
theorem zeta_exists_deep_zero_of_negative_weil :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (t a R μ : ℝ), 0 ≤ a → 0 ≤ R → 0 < μ → ∀ s : ℝ → ℝ,
      ContDiff ℝ 2 s → (∀ u, s u ≠ 0 → |u| ≤ a) →
      (zetaZeroConfig.W (modulatedTest t s) (modulatedTest t s)).re ≤ -μ →
      μ ≤ 768 * A₀ * Real.log (|t| + 3) * testNorm s ^ 2 * (Real.exp a / (1 + R)) ∨
        ∃ ρ ∈ zetaZeroConfig.carrier, |ρ.im - t| ≤ R ∧
          μ ≤ 768 * A₀ * Real.log (|t| + 3) * testNorm s ^ 2 *
            (Real.exp (2 * |1 / 2 - ρ.re| * a) + Real.exp a / (1 + R)) := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  exact ⟨A₀, hA₀, fun t a R μ ha hR hμ s hs hsupp hneg =>
    exists_deep_zero_of_negative_weil zetaZeroConfig hA₀ hloc t ha hR hμ hs hsupp hneg⟩

end RHTower
