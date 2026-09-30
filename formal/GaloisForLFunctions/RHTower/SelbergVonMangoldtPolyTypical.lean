import GaloisForLFunctions.RHTower.ZetaLogDerivSelbergExplicitFormula
import GaloisForLFunctions.RHTower.ZetaTypicalScaleBounds
import GaloisForLFunctions.RHTower.VonMangoldtMollifierPolynomialMeanSquare

/-!
# The smoothed von Mangoldt polynomial at typical heights

`D_x(s) = Σ_n Λ(n) W_x(n) n^{−s}` is a finite Dirichlet polynomial of length `N_x = ⌈x²⌉`
(`selbergVonMangoldtPoly_eq_edPoly`). On `Re s = 1/2 + δ`, `0 < δ ≤ 1`, its mean square over any
window is `≤ (T₂ − T₁ + 8N_x(1 + log N_x)) · 5/δ²` (`integral_normSq_selbergVonMangoldtPoly_le`).

For an entire `F` whose squared modulus has column integrals `≤ Q`, the heights `t ∈ [T, 2T]` near
which `|F| > M` on the box `a ≤ Re z ≤ b`, `|Im z − t| ≤ 6R` have measure
`≤ 15 R (b − a + 2r) Q/(π r² M²)`, `0 < r ≤ R` (`volume_largeNearBox_le`): area mean value on
discs of radius `r` and unit-`R` cells.
-/

noncomputable section

open Complex Set MeasureTheory ArithmeticFunction

namespace RHTower

/-- Coefficients `Λ(n) W_x(n)`. -/
def selbergPolyCoeff (x : ℝ) (n : ℕ) : ℂ := ((vonMangoldt n * selbergWeight x n : ℝ) : ℂ)

/-- The length `N_x = ⌈x²⌉`. -/
def selbergPolyLength (x : ℝ) : ℕ := ⌈x ^ 2⌉₊

theorem selbergVonMangoldtPoly_eq_edPoly {x : ℝ} (hx : 1 < x) (s : ℂ) :
    selbergVonMangoldtPoly x s =
      edPoly (selbergPolyCoeff x) (Finset.Icc 1 (selbergPolyLength x)) s := by
  unfold selbergVonMangoldtPoly edPoly
  rw [tsum_eq_sum (s := Finset.Icc 1 (selbergPolyLength x))]
  · refine Finset.sum_congr rfl fun n _ => ?_
    unfold selbergPolyCoeff
    push_cast
    ring
  · intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    have hN : selbergPolyLength x < n := by
      simp only [Finset.mem_Icc, not_and, not_le] at hn
      exact hn hpos
    have hx2 : x ^ 2 ≤ n := by
      have := Nat.le_ceil (x ^ 2)
      have h2 : (selbergPolyLength x : ℝ) < n := by exact_mod_cast hN
      unfold selbergPolyLength at h2
      linarith
    rw [selbergWeight_eq_zero hx hx2]
    simp

theorem differentiable_selbergVonMangoldtPoly {x : ℝ} (hx : 1 < x) :
    Differentiable ℂ (selbergVonMangoldtPoly x) := by
  have e : selbergVonMangoldtPoly x =
      edPoly (selbergPolyCoeff x) (Finset.Icc 1 (selbergPolyLength x)) :=
    funext (selbergVonMangoldtPoly_eq_edPoly hx)
  rw [e]
  exact differentiable_edPoly _ fun n hn => (Finset.mem_Icc.mp hn).1

/-- **The mean square of `D_x` on `Re s = 1/2 + δ`.** -/
theorem integral_normSq_selbergVonMangoldtPoly_le {x δ : ℝ} (hx : 1 < x) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    ∫ τ in T₁..T₂, ‖selbergVonMangoldtPoly x (((1 / 2 + δ : ℝ) : ℂ) + (τ : ℂ) * I)‖ ^ 2 ≤
      (T₂ - T₁ + 8 * selbergPolyLength x * (1 + Real.log (selbergPolyLength x))) * (5 / δ ^ 2) := by
  set N := selbergPolyLength x with hNdef
  have hpt : ∀ τ : ℝ, selbergVonMangoldtPoly x (((1 / 2 + δ : ℝ) : ℂ) + (τ : ℂ) * I) =
      edPoly (selbergPolyCoeff x) (Finset.Icc 1 N) (displacedLinePt (-δ) τ) := by
    intro τ
    rw [selbergVonMangoldtPoly_eq_edPoly hx]
    congr 1
    unfold displacedLinePt
    congr 2
    ring
  simp_rw [hpt]
  refine (integral_normSq_edPoly_displaced_le (-δ) _ N T₁ T₂).trans ?_
  have hfac : 0 ≤ T₂ - T₁ + 8 * N * (1 + Real.log N) := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · rw [h0]; simp; linarith
    · have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hpos)
      positivity
  refine mul_le_mul_of_nonneg_left ?_ hfac
  refine le_trans (Finset.sum_le_sum fun n hn => ?_) (sum_vonMangoldt_sq_rpow_le hδ hδ1 N)
  have hx0 : 1 < x := hx
  have hW0 := selbergWeight_nonneg hx0 n
  have hW1 := selbergWeight_le_one hx0 n
  have hΛ := (vonMangoldt_nonneg (n := n))
  have hn : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have e : (2 * -δ - 1) = -1 - 2 * δ := by ring
  rw [e]
  unfold selbergPolyCoeff
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hp : 0 ≤ (n : ℝ) ^ (-1 - 2 * δ) := Real.rpow_nonneg hn.le _
  have hsq : (vonMangoldt n * selbergWeight x n) ^ 2 ≤ vonMangoldt n ^ 2 := by
    rw [mul_pow]
    have : selbergWeight x n ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (vonMangoldt n)]
  exact mul_le_mul_of_nonneg_right hsq hp

/-! ## Large values on boxes at scale `R` -/

/-- Heights `t ∈ [T, 2T]` near which `|F| > M` on the box `a ≤ Re z ≤ b`, `|Im z − t| ≤ 6R`. -/
def largeNearBox (F : ℂ → ℂ) (T a b R M : ℝ) : Set ℝ :=
  {t | t ∈ Icc T (2 * T) ∧ ∃ z : ℂ, a ≤ z.re ∧ z.re ≤ b ∧ |z.im - t| ≤ 6 * R ∧ M < ‖F z‖}

theorem continuous_integral_normSq_column {F : ℂ → ℂ} (hF : Differentiable ℂ F) {c d : ℝ}
    (hcd : c ≤ d) :
    Continuous fun x : ℝ => ∫ y in c..d, ‖F ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 := by
  have e : (fun x : ℝ => ∫ y in c..d, ‖F ((x : ℂ) + (y : ℂ) * I)‖ ^ 2) =
      fun x : ℝ => ∫ y in Icc c d, ‖F ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 := by
    funext x; rw [intervalIntegral.integral_of_le hcd, integral_Icc_eq_integral_Ioc]
  rw [e]
  have hc : Continuous fun p : ℝ × ℝ => ‖F ((p.1 : ℂ) + (p.2 : ℂ) * I)‖ ^ 2 :=
    (hF.continuous.comp (by fun_prop)).norm.pow 2
  exact continuous_parametric_integral_of_continuous
    (f := fun x y : ℝ => ‖F ((x : ℂ) + (y : ℂ) * I)‖ ^ 2) hc isCompact_Icc

/-- **Large values on boxes.** -/
theorem volume_largeNearBox_le {F : ℂ → ℂ} (hF : Differentiable ℂ F) {T a b R r M Q : ℝ}
    (hr0 : 0 < r) (hrR : r ≤ R) (hM : 0 < M) (hab : a ≤ b)
    (hcol : ∀ x ∈ Icc (a - r) (b + r),
      ∫ y in (T - (7 : ℕ) * R)..(T + (((⌈T / R⌉₊ + 1 : ℕ) : ℝ) + (8 : ℕ)) * R),
        ‖F ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 ≤ Q) :
    volume (largeNearBox F T a b R M) ≤
      ENNReal.ofReal (R * (15 * ((b - a + 2 * r) * Q)) / (Real.pi * r ^ 2 * M ^ 2)) := by
  have hR0 : 0 < R := lt_of_lt_of_le hr0 hrR
  set A := Real.pi * r ^ 2 * M ^ 2 with hAdef
  have hA : 0 < A := by rw [hAdef]; have := Real.pi_pos; positivity
  set Φ : ℕ → ℝ := fun k => ∫ x in (a - r)..(b + r),
    ∫ y in (T + ((k : ℝ) - (7 : ℕ)) * R)..(T + ((k : ℝ) + (8 : ℕ)) * R),
      ‖F ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 with hΦdef
  have hΦ0 : ∀ k, 0 ≤ Φ k := fun k =>
    intervalIntegral.integral_nonneg (by linarith) fun x _ =>
      intervalIntegral.integral_nonneg (by push_cast; nlinarith) fun y _ => by positivity
  have hbad : ∀ t ∈ Icc T (2 * T),
      (∃ z : ℂ, a ≤ z.re ∧ z.re ≤ b ∧ |z.im - t| ≤ 6 * R ∧ M < ‖F z‖) →
      ∀ k : ℕ, T + k * R ≤ t → t ≤ T + (k + 1) * R → A ≤ Φ k := by
    rintro t ht ⟨z, hz1, hz2, hzt, hzM⟩ k hk1 hk2
    have hzt' := abs_le.mp hzt
    have hmean := normSq_mul_area_le_box hF (z := z) hr0
      (a := a - r) (b := b + r) (c := T + ((k : ℝ) - (7 : ℕ)) * R)
      (d := T + ((k : ℝ) + (8 : ℕ)) * R) (by linarith) (by linarith) (by push_cast; nlinarith)
      (by push_cast; nlinarith)
    have hE2 : M ^ 2 ≤ ‖F z‖ ^ 2 := pow_le_pow_left₀ hM.le hzM.le 2
    calc A = Real.pi * r ^ 2 * M ^ 2 := by rw [hAdef]
      _ ≤ Real.pi * r ^ 2 * ‖F z‖ ^ 2 := by gcongr
      _ ≤ Φ k := hmean
  have hvol := volume_setOf_le_of_cells_scaled hA hR0 hΦ0 hbad
  refine le_trans (measure_mono ?_) (hvol.trans (ENNReal.ofReal_le_ofReal ?_))
  · intro t ht
    exact ⟨ht.1, ht.2⟩
  set m := ⌈T / R⌉₊ + 1 with hm
  have hsum : ∑ k ∈ Finset.range m, Φ k ≤ 15 * ((b - a + 2 * r) * Q) := by
    have hswap : ∑ k ∈ Finset.range m, Φ k = ∫ x in (a - r)..(b + r),
        ∑ k ∈ Finset.range m, ∫ y in (T + ((k : ℝ) - (7 : ℕ)) * R)..(T + ((k : ℝ) + (8 : ℕ)) * R),
          ‖F ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 := by
      rw [intervalIntegral.integral_finsetSum]
      intro k _
      exact (continuous_integral_normSq_column hF (by push_cast; nlinarith)).intervalIntegrable
        _ _
    rw [hswap]
    have hQ0 : 0 ≤ Q := by
      have h := hcol (a - r) ⟨le_rfl, by linarith⟩
      refine le_trans (intervalIntegral.integral_nonneg ?_ fun y _ => by positivity) h
      push_cast
      nlinarith
    have hpt : ∀ x ∈ uIoc (a - r) (b + r), ‖∑ k ∈ Finset.range m,
        ∫ y in (T + ((k : ℝ) - (7 : ℕ)) * R)..(T + ((k : ℝ) + (8 : ℕ)) * R),
          ‖F ((x : ℂ) + (y : ℂ) * I)‖ ^ 2‖ ≤ 15 * Q := by
      intro x hx
      rw [uIoc_of_le (by linarith)] at hx
      have hg : Continuous fun y : ℝ => ‖F ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 :=
        (hF.continuous.comp (by fun_prop)).norm.pow 2
      have hsl := sum_integral_sliding_scaled_le hg (fun y => by positivity) T R hR0.le 7 8 m
      have hcolx := hcol x ⟨hx.1.le, hx.2⟩
      have h0 : 0 ≤ ∑ k ∈ Finset.range m,
          ∫ y in (T + ((k : ℝ) - (7 : ℕ)) * R)..(T + ((k : ℝ) + (8 : ℕ)) * R),
            ‖F ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 :=
        Finset.sum_nonneg fun k _ =>
          intervalIntegral.integral_nonneg (by push_cast; nlinarith) fun y _ => by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      have h15 : ((7 : ℕ) : ℝ) + (8 : ℕ) = 15 := by norm_num
      rw [h15] at hsl
      nlinarith
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [abs_of_pos (by linarith)] at hn
    calc _ ≤ ‖∫ x in (a - r)..(b + r), ∑ k ∈ Finset.range m,
          ∫ y in (T + ((k : ℝ) - (7 : ℕ)) * R)..(T + ((k : ℝ) + (8 : ℕ)) * R),
            ‖F ((x : ℂ) + (y : ℂ) * I)‖ ^ 2‖ := Real.le_norm_self _
      _ ≤ 15 * Q * (b + r - (a - r)) := hn
      _ = 15 * ((b - a + 2 * r) * Q) := by ring
  rw [mul_div_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsum hA.le) hR0.le

end RHTower
