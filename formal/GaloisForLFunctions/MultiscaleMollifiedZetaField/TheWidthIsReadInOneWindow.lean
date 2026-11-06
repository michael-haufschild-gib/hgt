import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheExponentOfTheMollifiedErrorIsRigid
import GaloisForLFunctions.RHTower.MoebiusConvergenceZeroFree
import GaloisForLFunctions.RHTower.LargeValues

/-!
# The width is read at one point and in one window

The height plays no role in the slope of the long-Möbius second moment. Three statements with no parameter `T` are each equivalent to
`zetaZeroWidth ≤ β`.

* **One point** (`zetaZeroWidth_le_iff_pointwise`). For any fixed `t₀`, `|M_X(½ + it₀)| ≪_ε X^{β+ε}`. If this holds, Abel summation gives
  convergence of `Σ μ(n) n^{−s}` to the right of `½ + β + it₀`, and a convergent Möbius series forces a zero-free half-plane.
* **One window, Möbius polynomial** (`zetaZeroWidth_le_of_window_moebius_secondMoment`). For any fixed interval,
  `∫ |M_k(½ + iu)|² du ≪_ε k^{2(β+ε)}` for all `k`. Here `∂_u M_X = −i Σ μ(n) log n n^{−½−iu}`, and Abel summation writes that sum through `M_k`,
  `k ≤ X`, at a cost of `log X`. The Sobolev inequality then reaches every point of the window.
* **One window, mollified zeta** (`zetaZeroWidth_le_iff_unit_window`). `∫_0^1 |ζ M_X(½ + iu)|² du ≪_ε X^{2(β+ε)}`. The factor `ζ` has no zero on this window,
  so it is bounded below there.

At `β = 0` the last form is RH (`riemannHypothesis_iff_unit_window`). These forms need the bound at every length. The sparse form of
`TheExponentOfTheMollifiedErrorIsRigid` trades this for a condition on every window.
-/

noncomputable section

open Complex MeasureTheory Filter Set
open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth zetaZeroWidth_nonneg
  zetaZeroWidth_eq_zetaZeroAbscissa_sub_half zetaZeroWidth_le_iff_xiZeroHalfPlaneBound
  zetaZeroWidth_le_iff_zetaZeroAbscissa_le)

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-! ### One point -/

/-- A power bound for the Möbius section at one point of the critical line bounds the width. -/
theorem zetaZeroWidth_le_of_pointwise {β t₀ : ℝ} (hβ : 0 ≤ β)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
      ‖moebiusPoly X (linePoint t₀)‖ ≤ C * (X : ℝ) ^ (β + ε)) :
    zetaZeroWidth ≤ β := by
  rw [zetaZeroWidth_le_iff_zetaZeroAbscissa_le hβ]
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨ρ, hζ, hbρ⟩ := _root_.RHTower.exists_zetaZero_lt_re hlt
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (ρ.re - 1 / 2 - β) / 3 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨C, hC0, hC⟩ := h ε hε0
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℂ, s₀ = linePoint t₀ := ⟨_, rfl⟩
  rw [← hs₀] at hC
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℂ, a = fun n : ℕ =>
      (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s₀) • _root_.RHTower.mobCoeff (n + 1) := ⟨_, rfl⟩
  have hα : 0 ≤ β + ε := by linarith
  have hA : ∀ N : ℕ, ‖∑ n ∈ Finset.range N, a n‖ ≤ C * ((N : ℝ) + 1) ^ (β + ε) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
      positivity
    · have hrep : ∑ n ∈ Finset.range N, a n = moebiusPoly N s₀ := by
        rw [ha]
        exact (_root_.RHTower.edPoly_mobCoeff_Icc_eq_sum_range N s₀).symm
      rw [hrep]
      refine (hC N hN).trans (mul_le_mul_of_nonneg_left ?_ hC0)
      exact Real.rpow_le_rpow (Nat.cast_nonneg N) (by linarith) hα
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = ((β + 2 * ε : ℝ) : ℂ) := ⟨_, rfl⟩
  have hwre : w.re = β + 2 * ε := by rw [hw]; simp
  obtain ⟨L, hL⟩ := GaloisForLFunctions.RHTower.tendsto_dirichlet_partialSum_of_poly_bounded
    hC0 hα hA (s := w) (by rw [hwre]; linarith)
  have h₀ : GaloisForLFunctions.RHTower.DirichletConvergesAt _root_.RHTower.moebiusShift (s₀ + w) := by
    refine ⟨L, hL.congr fun N => ?_⟩
    unfold GaloisForLFunctions.RHTower.dirichletPartialSum
    refine Finset.sum_congr rfl fun n _ => ?_
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hne : (((n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [ha, neg_add, Complex.cpow_add _ _ hne]
    simp only [_root_.RHTower.moebiusShift, _root_.RHTower.moebiusCoeffC, _root_.RHTower.mobCoeff,
      smul_eq_mul]
    ring
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    exact riemannZeta_ne_zero_of_one_le_re (by simp) hζ
  refine _root_.RHTower.riemannZeta_ne_zero_of_moebius_convergesAt h₀ ?_ hρ1 hζ
  rw [Complex.add_re, hwre, hs₀, linePoint_re]
  have : ρ.re = 1 / 2 + β + 3 * ε := by rw [hε]; ring
  linarith

/-- **One point of the critical line reads the width.** -/
theorem zetaZeroWidth_le_iff_pointwise {β : ℝ} (hβ : 0 ≤ β) (t₀ : ℝ) :
    zetaZeroWidth ≤ β ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
      ‖moebiusPoly X (linePoint t₀)‖ ≤ C * (X : ℝ) ^ (β + ε) := by
  refine ⟨fun hw ε hε => ?_, zetaZeroWidth_le_of_pointwise hβ⟩
  obtain ⟨K, hK0, hK⟩ := exists_norm_moebiusPoly_line_le hε
  refine ⟨2 * (K * (1 + |t₀|)), by positivity, fun X hX => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hmono : (X : ℝ) ^ (zetaZeroWidth + ε) ≤ (X : ℝ) ^ (β + ε) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  calc ‖moebiusPoly X (linePoint t₀)‖
      ≤ 2 * (X : ℝ) ^ (zetaZeroWidth + ε) * (K * (1 + |t₀|)) := hK X t₀ hX
    _ ≤ 2 * (X : ℝ) ^ (β + ε) * (K * (1 + |t₀|)) := by gcongr
    _ = 2 * (K * (1 + |t₀|)) * (X : ℝ) ^ (β + ε) := by ring

/-- **RH at one point**: `M_X(½ + it₀) ≪_ε X^ε`. -/
theorem riemannHypothesis_iff_pointwise (t₀ : ℝ) :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
      ‖moebiusPoly X (linePoint t₀)‖ ≤ C * (X : ℝ) ^ ε := by
  rw [_root_.RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero,
    ← zetaZeroWidth_le_iff_xiZeroHalfPlaneBound le_rfl, zetaZeroWidth_le_iff_pointwise le_rfl t₀]
  simp only [zero_add]

/-! ### The logarithmic derivative in the height -/

/-- `Σ_{n ≤ X} μ(n) log n · n^{−½−iu}`. -/
def moebiusLogPoly (X : ℕ) (u : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, _root_.RHTower.mobCoeff n * (Real.log n : ℂ) *
    ((n : ℝ) : ℂ) ^ (-linePoint u)

theorem continuous_moebiusPoly_line (X : ℕ) : Continuous fun u : ℝ => moebiusPoly X (linePoint u) :=
  (differentiable_moebiusPoly X).continuous.comp continuous_linePoint

/-- The height derivative of `M_X(½ + iu)` is `−i Σ μ(n) log n n^{−½−iu}`. -/
theorem hasDerivAt_moebiusPoly_line (X : ℕ) (u : ℝ) :
    HasDerivAt (fun y : ℝ => moebiusPoly X (linePoint y)) (-I * moebiusLogPoly X u) u := by
  have hterm : ∀ n ∈ Finset.Icc 1 X, HasDerivAt
      (fun y : ℝ => _root_.RHTower.mobCoeff n * ((n : ℝ) : ℂ) ^ (-linePoint y))
      (-I * (_root_.RHTower.mobCoeff n * (Real.log n : ℂ) * ((n : ℝ) : ℂ) ^ (-linePoint u))) u := by
    intro n hn
    have hn1 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hne : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn1.ne'
    have h0 : HasDerivAt (fun z : ℂ => (1 / 2 : ℂ) + z * I) (1 * I) (u : ℂ) :=
      ((hasDerivAt_id' (u : ℂ)).mul_const I).const_add (1 / 2 : ℂ)
    rw [one_mul] at h0
    have h1 : HasDerivAt (fun z : ℂ => -((1 / 2 : ℂ) + z * I)) (-I) (u : ℂ) := h0.neg
    have h2 := h1.const_cpow (c := ((n : ℝ) : ℂ)) (Or.inl hne)
    have h3 := (h2.comp_ofReal).const_mul (_root_.RHTower.mobCoeff n)
    have hlog : Complex.log ((n : ℝ) : ℂ) = (Real.log n : ℂ) :=
      (Complex.ofReal_log hn1.le).symm
    have hlin : linePoint u = (1 / 2 : ℂ) + (u : ℂ) * I := rfl
    show HasDerivAt (fun y : ℝ => _root_.RHTower.mobCoeff n *
      ((n : ℝ) : ℂ) ^ (-((1 / 2 : ℂ) + (y : ℂ) * I))) _ u
    exact h3.congr_deriv (by
      rw [hlin, hlog]
      ring)
  have hsum := HasDerivAt.fun_sum hterm
  have hfun : (fun y : ℝ => ∑ n ∈ Finset.Icc 1 X,
      _root_.RHTower.mobCoeff n * ((n : ℝ) : ℂ) ^ (-linePoint y)) =
      fun y : ℝ => moebiusPoly X (linePoint y) := rfl
  rw [hfun, ← Finset.mul_sum] at hsum
  exact hsum

/-- **Abel summation in the length.** `Σ_{n≤X} μ(n) log n n^{−s} = log X · M_X − Σ_{k<X} (log(k+1) − log k) M_k`. -/
theorem moebiusLogPoly_eq {X : ℕ} (hX : 1 ≤ X) (u : ℝ) :
    moebiusLogPoly X u = (Real.log X : ℂ) * moebiusPoly X (linePoint u) -
      ∑ k ∈ Finset.Ico 1 X,
        ((Real.log ((k : ℝ) + 1) - Real.log k : ℝ) : ℂ) * moebiusPoly k (linePoint u) := by
  induction X, hX using Nat.le_induction with
  | base =>
    simp [moebiusLogPoly]
  | succ X hX ih =>
    have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
    have hstepM : moebiusPoly (X + 1) (linePoint u) = moebiusPoly X (linePoint u) +
        _root_.RHTower.mobCoeff (X + 1) * (((X + 1 : ℕ) : ℝ) : ℂ) ^ (-linePoint u) := by
      show _root_.RHTower.edPoly _ _ _ = _root_.RHTower.edPoly _ _ _ + _
      unfold _root_.RHTower.edPoly
      rw [Finset.sum_Icc_succ_top (by omega)]
    have hstepW : moebiusLogPoly (X + 1) u = moebiusLogPoly X u +
        _root_.RHTower.mobCoeff (X + 1) * (Real.log ((X + 1 : ℕ) : ℝ) : ℂ) *
          (((X + 1 : ℕ) : ℝ) : ℂ) ^ (-linePoint u) := by
      unfold moebiusLogPoly
      rw [Finset.sum_Icc_succ_top (by omega)]
    rw [hstepW, ih, hstepM, Finset.sum_Ico_succ_top hX]
    push_cast
    ring

theorem sum_Ico_log_diff {X : ℕ} (hX : 1 ≤ X) :
    ∑ k ∈ Finset.Ico 1 X, (Real.log ((k : ℝ) + 1) - Real.log k) = Real.log X := by
  induction X, hX using Nat.le_induction with
  | base => simp
  | succ X hX ih =>
    rw [Finset.sum_Ico_succ_top hX, ih]
    push_cast
    ring

theorem log_diff_nonneg {k : ℕ} (hk : 1 ≤ k) : 0 ≤ Real.log ((k : ℝ) + 1) - Real.log k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  exact sub_nonneg.mpr (Real.log_le_log hk0 (by linarith))

/-- Weighted Cauchy–Schwarz for a finite sum of complex numbers. -/
theorem norm_sum_smul_sq_le {ι : Type*} (s : Finset ι) {c : ι → ℝ} (hc : ∀ i ∈ s, 0 ≤ c i) (z : ι → ℂ) :
    ‖∑ i ∈ s, (c i : ℂ) * z i‖ ^ 2 ≤ (∑ i ∈ s, c i) * ∑ i ∈ s, c i * ‖z i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, (c i : ℂ) * z i‖ ≤ ∑ i ∈ s, c i * ‖z i‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc i hi)]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (c i))
    (fun i => Real.sqrt (c i) * ‖z i‖)
  have h3 : ∑ i ∈ s, Real.sqrt (c i) * (Real.sqrt (c i) * ‖z i‖) = ∑ i ∈ s, c i * ‖z i‖ :=
    Finset.sum_congr rfl fun i hi => by
      rw [← mul_assoc, Real.mul_self_sqrt (hc i hi)]
  have h4 : ∑ i ∈ s, Real.sqrt (c i) ^ 2 = ∑ i ∈ s, c i :=
    Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hc i hi)
  have h5 : ∑ i ∈ s, (Real.sqrt (c i) * ‖z i‖) ^ 2 = ∑ i ∈ s, c i * ‖z i‖ ^ 2 :=
    Finset.sum_congr rfl fun i hi => by
      rw [mul_pow, Real.sq_sqrt (hc i hi)]
  rw [h3, h4, h5] at h2
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

/-! ### One window -/

/-- **Sobolev on a window.** If `∫_J |M_k|² ≤ S` for all `1 ≤ k ≤ X`, `J = [c, c + δ]`, then every point of `J` has
`|M_X(½ + it)|² ≤ (1/δ + 4 log X + 1) S`. -/
theorem norm_moebiusPoly_sq_le_of_window {c δ S : ℝ} (hδ : 0 < δ) (hS : 0 ≤ S) {X : ℕ} (hX : 1 ≤ X)
    (hB : ∀ k : ℕ, 1 ≤ k → k ≤ X →
      ∫ u in c..(c + δ), ‖moebiusPoly k (linePoint u)‖ ^ 2 ≤ S)
    {t : ℝ} (ht : t ∈ Icc c (c + δ)) :
    ‖moebiusPoly X (linePoint t)‖ ^ 2 ≤ (1 / δ + 4 * Real.log X + 1) * S := by
  have hcδ : c ≤ c + δ := by linarith
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hX1
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = Real.log (X : ℝ) := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; exact hlog
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℂ, F = fun u => moebiusPoly X (linePoint u) := ⟨_, rfl⟩
  have hFc : Continuous F := by rw [hF]; exact continuous_moebiusPoly_line X
  have hAc : ∀ k : ℕ, Continuous fun u : ℝ => moebiusPoly k (linePoint u) :=
    continuous_moebiusPoly_line
  have hWeq : moebiusLogPoly X = fun u => (Real.log X : ℂ) * moebiusPoly X (linePoint u) -
      ∑ k ∈ Finset.Ico 1 X,
        ((Real.log ((k : ℝ) + 1) - Real.log k : ℝ) : ℂ) * moebiusPoly k (linePoint u) :=
    funext (moebiusLogPoly_eq hX)
  have hWc : Continuous (moebiusLogPoly X) := by
    rw [hWeq]
    exact (continuous_const.mul (hAc X)).sub
      (continuous_finsetSum _ fun k _ => continuous_const.mul (hAc k))
  have hF'c : Continuous fun u => -I * moebiusLogPoly X u := continuous_const.mul hWc
  have hderiv : ∀ y ∈ uIcc c (c + δ), HasDerivAt F (-I * moebiusLogPoly X y) y := by
    intro y _
    rw [hF]
    exact hasDerivAt_moebiusPoly_line X y
  have hsob := _root_.RHTower.sobolev_pointwise (f := F) (f' := fun u => -I * moebiusLogPoly X u)
    (c := c) (δ := δ) hδ hderiv
    ((continuous_const.mul (hFc.inner hF'c)).intervalIntegrable _ _)
    ((hFc.norm.pow 2).intervalIntegrable _ _)
    ((continuous_const.mul (hFc.norm.mul hF'c.norm)).intervalIntegrable _ _) ht
  -- the pointwise bound for the derivative
  have hWpt : ∀ u : ℝ, ‖moebiusLogPoly X u‖ ^ 2 ≤
      2 * Λ ^ 2 * ‖moebiusPoly X (linePoint u)‖ ^ 2 +
        2 * Λ * ∑ k ∈ Finset.Ico 1 X, (Real.log ((k : ℝ) + 1) - Real.log k) *
          ‖moebiusPoly k (linePoint u)‖ ^ 2 := by
    intro u
    have hcs := norm_sum_smul_sq_le (Finset.Ico 1 X)
      (c := fun k : ℕ => Real.log ((k : ℝ) + 1) - Real.log k)
      (fun k hk => log_diff_nonneg (Finset.mem_Ico.mp hk).1)
      (fun k => moebiusPoly k (linePoint u))
    rw [sum_Ico_log_diff hX, ← hΛ] at hcs
    rw [moebiusLogPoly_eq hX u, ← hΛ]
    obtain ⟨a, ha⟩ : ∃ a : ℂ, a = (Λ : ℂ) * moebiusPoly X (linePoint u) := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : ℂ, b = ∑ k ∈ Finset.Ico 1 X,
        ((Real.log ((k : ℝ) + 1) - Real.log k : ℝ) : ℂ) * moebiusPoly k (linePoint u) := ⟨_, rfl⟩
    rw [← ha, ← hb]
    rw [← hb] at hcs
    have ha2 : ‖a‖ ^ 2 = Λ ^ 2 * ‖moebiusPoly X (linePoint u)‖ ^ 2 := by
      rw [ha, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg hΛ0]
    have htri : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
      have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
      nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
    rw [ha2] at htri
    linarith
  have hWint : ∫ u in c..(c + δ), ‖moebiusLogPoly X u‖ ^ 2 ≤ 4 * Λ ^ 2 * S := by
    have hI1 : IntervalIntegrable (fun u : ℝ => ‖moebiusLogPoly X u‖ ^ 2) volume c (c + δ) :=
      (hWc.norm.pow 2).intervalIntegrable _ _
    have hA2 : ∀ k : ℕ, IntervalIntegrable (fun u : ℝ => ‖moebiusPoly k (linePoint u)‖ ^ 2) volume
        c (c + δ) := fun k => ((hAc k).norm.pow 2).intervalIntegrable _ _
    have hsumint : IntervalIntegrable (fun u : ℝ => ∑ k ∈ Finset.Ico 1 X,
        (Real.log ((k : ℝ) + 1) - Real.log k) * ‖moebiusPoly k (linePoint u)‖ ^ 2) volume
        c (c + δ) :=
      (continuous_finsetSum _ fun k _ => continuous_const.mul
        ((hAc k).norm.pow 2)).intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_on hcδ hI1
      (((hA2 X).const_mul (2 * Λ ^ 2)).add (hsumint.const_mul (2 * Λ))) (fun u _ => hWpt u)
    rw [intervalIntegral.integral_add ((hA2 X).const_mul _) (hsumint.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum fun k _ => (hA2 k).const_mul _] at hmono
    have hsum : ∑ k ∈ Finset.Ico 1 X, ∫ u in c..(c + δ),
        (Real.log ((k : ℝ) + 1) - Real.log k) * ‖moebiusPoly k (linePoint u)‖ ^ 2 ≤ Λ * S := by
      calc _ ≤ ∑ k ∈ Finset.Ico 1 X, (Real.log ((k : ℝ) + 1) - Real.log k) * S := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hk' := Finset.mem_Ico.mp hk
            rw [intervalIntegral.integral_const_mul]
            exact mul_le_mul_of_nonneg_left (hB k hk'.1 hk'.2.le) (log_diff_nonneg hk'.1)
        _ = Λ * S := by rw [← Finset.sum_mul, sum_Ico_log_diff hX, hΛ]
    have h1 := mul_le_mul_of_nonneg_left (hB X hX le_rfl) (by positivity : 0 ≤ 2 * Λ ^ 2)
    have h2 := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2 * Λ)
    nlinarith
  have hFint : ∫ u in c..(c + δ), ‖F u‖ ^ 2 ≤ S := by
    rw [hF]
    exact hB X hX le_rfl
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 2 * Λ + 1 := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hM]; linarith
  have hcross : ∫ u in c..(c + δ), 2 * (‖F u‖ * ‖-I * moebiusLogPoly X u‖) ≤
      M * S + (4 * Λ ^ 2 * S) / M := by
    have hA1 : IntervalIntegrable (fun u : ℝ => M * ‖F u‖ ^ 2) volume c (c + δ) :=
      (continuous_const.mul (hFc.norm.pow 2)).intervalIntegrable _ _
    have hA2 : IntervalIntegrable (fun u : ℝ => ‖moebiusLogPoly X u‖ ^ 2 / M) volume c (c + δ) :=
      ((hWc.norm.pow 2).div_const M).intervalIntegrable _ _
    have hmono : ∫ u in c..(c + δ), 2 * (‖F u‖ * ‖-I * moebiusLogPoly X u‖) ≤
        ∫ u in c..(c + δ), (M * ‖F u‖ ^ 2 + ‖moebiusLogPoly X u‖ ^ 2 / M) := by
      refine intervalIntegral.integral_mono_on hcδ
        ((continuous_const.mul (hFc.norm.mul hF'c.norm)).intervalIntegrable _ _)
        (hA1.add hA2) fun u _ => ?_
      have hn : ‖-I * moebiusLogPoly X u‖ = ‖moebiusLogPoly X u‖ := by simp
      rw [hn]
      have h1 : (M * ‖F u‖ - ‖moebiusLogPoly X u‖) ^ 2 / M =
          M * ‖F u‖ ^ 2 + ‖moebiusLogPoly X u‖ ^ 2 / M - 2 * (‖F u‖ * ‖moebiusLogPoly X u‖) := by
        field_simp
        ring
      have h2 : 0 ≤ (M * ‖F u‖ - ‖moebiusLogPoly X u‖) ^ 2 / M := by positivity
      linarith
    refine hmono.trans ?_
    rw [intervalIntegral.integral_add hA1 hA2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_div]
    have h1 := mul_le_mul_of_nonneg_left hFint hM0.le
    have h2 := div_le_div_of_nonneg_right hWint hM0.le
    linarith
  have hratio : (4 * Λ ^ 2 * S) / M ≤ 2 * Λ * S := by
    rw [div_le_iff₀ hM0, hM]
    nlinarith [mul_nonneg hΛ0 hS]
  have hfinal : ‖F t‖ ^ 2 ≤ (1 / δ) * S + (M * S + 2 * Λ * S) := by
    have h1 : (1 / δ) * (∫ u in c..(c + δ), ‖F u‖ ^ 2) ≤ (1 / δ) * S :=
      mul_le_mul_of_nonneg_left hFint (by positivity)
    linarith
  have hgoal : ‖F t‖ ^ 2 = ‖moebiusPoly X (linePoint t)‖ ^ 2 := by rw [hF]
  rw [← hgoal, ← hΛ]
  rw [hM] at hfinal
  nlinarith

/-- **One window of the Möbius polynomial reads the width.** For any interval `[c, c + δ]`, if `∫ |M_k(½ + iu)|² du ≪_ε k^{2(β+ε)}` for all `k`,
then `zetaZeroWidth ≤ β`. -/
theorem zetaZeroWidth_le_of_window_moebius_secondMoment {β c δ : ℝ} (hβ : 0 ≤ β) (hδ : 0 < δ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, 1 ≤ k →
      ∫ u in c..(c + δ), ‖moebiusPoly k (linePoint u)‖ ^ 2 ≤ B * (k : ℝ) ^ (2 * (β + ε))) :
    zetaZeroWidth ≤ β := by
  refine zetaZeroWidth_le_of_pointwise (t₀ := c) hβ fun ε hε => ?_
  obtain ⟨B, hB0, hB⟩ := h (ε / 2) (by positivity)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 1 / δ + 1 + 4 / ε := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  refine ⟨Real.sqrt (K * B), Real.sqrt_nonneg _, fun X hX => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hr0 : 0 ≤ β + ε / 2 := by positivity
  have hS0 : 0 ≤ B * (X : ℝ) ^ (2 * (β + ε / 2)) := by positivity
  have hmem : c ∈ Icc c (c + δ) := ⟨le_rfl, by linarith⟩
  have hb := norm_moebiusPoly_sq_le_of_window hδ hS0 hX (fun k hk hkX => by
    refine (hB k hk).trans (mul_le_mul_of_nonneg_left ?_ hB0)
    exact Real.rpow_le_rpow (Nat.cast_nonneg k) (by exact_mod_cast hkX) (by positivity)) hmem
  have hpow : 1 ≤ (X : ℝ) ^ ε := Real.one_le_rpow hX1 hε.le
  have hlog : Real.log (X : ℝ) ≤ (X : ℝ) ^ ε / ε := by
    have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hX0 ε)
    rw [Real.log_rpow hX0] at h1
    rw [le_div_iff₀ hε]
    linarith
  have hfac : 1 / δ + 4 * Real.log X + 1 ≤ K * (X : ℝ) ^ ε := by
    have h4 : 4 * Real.log (X : ℝ) ≤ 4 / ε * (X : ℝ) ^ ε := by
      calc 4 * Real.log (X : ℝ) ≤ 4 * ((X : ℝ) ^ ε / ε) := by linarith
        _ = 4 / ε * (X : ℝ) ^ ε := by ring
    have h5 : 0 ≤ (1 / δ + 1) * ((X : ℝ) ^ ε - 1) :=
      mul_nonneg (by positivity) (by linarith)
    rw [hK]
    nlinarith
  have hsplit : (X : ℝ) ^ ε * (X : ℝ) ^ (2 * (β + ε / 2)) = ((X : ℝ) ^ (β + ε)) ^ 2 := by
    rw [← Real.rpow_add hX0, ← Real.rpow_two, ← Real.rpow_mul hX0.le]
    congr 1
    ring
  have hsq : ‖moebiusPoly X (linePoint c)‖ ^ 2 ≤ (Real.sqrt (K * B) * (X : ℝ) ^ (β + ε)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    calc ‖moebiusPoly X (linePoint c)‖ ^ 2
        ≤ (1 / δ + 4 * Real.log X + 1) * (B * (X : ℝ) ^ (2 * (β + ε / 2))) := hb
      _ ≤ K * (X : ℝ) ^ ε * (B * (X : ℝ) ^ (2 * (β + ε / 2))) :=
          mul_le_mul_of_nonneg_right hfac hS0
      _ = K * B * ((X : ℝ) ^ ε * (X : ℝ) ^ (2 * (β + ε / 2))) := by ring
      _ = K * B * ((X : ℝ) ^ (β + ε)) ^ 2 := by rw [hsplit]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

theorem continuous_zeta_linePoint : Continuous fun u : ℝ => riemannZeta (linePoint u) :=
  continuous_iff_continuousAt.mpr fun u =>
    (differentiableAt_riemannZeta (linePoint_ne_one u)).continuousAt.comp
      continuous_linePoint.continuousAt

/-- `ζ(½ + iu)` has no zero for `u ∈ [0, 1]`, so it is bounded below there. -/
theorem exists_norm_zeta_linePoint_ge : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ u ∈ Icc (0 : ℝ) 1,
    c₀ ≤ ‖riemannZeta (linePoint u)‖ := by
  obtain ⟨u₀, hu₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMinOn
    ⟨0, by norm_num⟩ continuous_zeta_linePoint.norm.continuousOn
  refine ⟨‖riemannZeta (linePoint u₀)‖, ?_, fun u hu => hmin hu⟩
  refine norm_pos_iff.mpr (_root_.RHTower.riemannZeta_ne_zero_of_im_sq_le (linePoint_ne_one u₀)
    (by rw [linePoint_re]; norm_num) ?_)
  rw [linePoint_im]
  have h0 := hu₀.1
  have h1 := hu₀.2
  nlinarith

/-- **One window of the mollified zeta function reads the width.**
`zetaZeroWidth ≤ β` iff `∫_0^1 |ζ M_X(½ + iu)|² du ≪_ε X^{2(β+ε)}` for all `X`. -/
theorem zetaZeroWidth_le_iff_unit_window {β : ℝ} (hβ : 0 ≤ β) :
    zetaZeroWidth ≤ β ↔ ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℕ, 1 ≤ X →
      ∫ u in (0 : ℝ)..1, ‖riemannZeta (linePoint u) * moebiusPoly X (linePoint u)‖ ^ 2 ≤
        B * (X : ℝ) ^ (2 * (β + ε)) := by
  constructor
  · intro hw ε hε
    obtain ⟨C, hC1, hC⟩ := exists_norm_lineError_le hε
    refine ⟨(4 * C + 1) ^ 2, by positivity, fun X hX => ?_⟩
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
    have hX0 : (0 : ℝ) < X := by linarith
    have hr0 : 0 ≤ β + ε := by positivity
    have hR1 : 1 ≤ (X : ℝ) ^ (β + ε) := Real.one_le_rpow hX1 hr0
    have hmono : (X : ℝ) ^ (zetaZeroWidth + ε) ≤ (X : ℝ) ^ (β + ε) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    have hC0 : 0 ≤ C := by linarith
    have hpt : ∀ u ∈ Icc (0 : ℝ) 1,
        ‖riemannZeta (linePoint u) * moebiusPoly X (linePoint u)‖ ^ 2 ≤
          (4 * C + 1) ^ 2 * (X : ℝ) ^ (2 * (β + ε)) := by
      intro u hu
      have habs : |u| ≤ 1 := by
        rw [abs_of_nonneg hu.1]
        exact hu.2
      have hu2 : (1 + |u|) ^ 2 ≤ 4 := by
        have := abs_nonneg u
        nlinarith
      have hb := hC X u hX
      have hE : ‖lineError (moebiusPoly X) u‖ ≤ 4 * C * (X : ℝ) ^ (β + ε) := by
        refine hb.trans ?_
        calc C * (1 + |u|) ^ 2 * (X : ℝ) ^ (zetaZeroWidth + ε)
            ≤ C * 4 * (X : ℝ) ^ (β + ε) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hu2 hC0) hmono
                (Real.rpow_nonneg hX0.le _) (by positivity)
          _ = 4 * C * (X : ℝ) ^ (β + ε) := by ring
      have hnorm : ‖riemannZeta (linePoint u) * moebiusPoly X (linePoint u)‖ ≤
          (4 * C + 1) * (X : ℝ) ^ (β + ε) := by
        have htri : ‖riemannZeta (linePoint u) * moebiusPoly X (linePoint u)‖ ≤
            ‖lineError (moebiusPoly X) u‖ + 1 := by
          have h := norm_add_le (lineError (moebiusPoly X) u) 1
          rw [norm_one] at h
          have heq : lineError (moebiusPoly X) u + 1 =
              riemannZeta (linePoint u) * moebiusPoly X (linePoint u) := by
            simp [lineError]
          rwa [heq] at h
        nlinarith
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      have hrew : ((4 * C + 1) * (X : ℝ) ^ (β + ε)) ^ 2 =
          (4 * C + 1) ^ 2 * (X : ℝ) ^ (2 * (β + ε)) := by
        rw [mul_pow, mul_comm 2 (β + ε), Real.rpow_mul hX0.le, Real.rpow_two]
      rwa [hrew] at hsq
    have hcont : Continuous fun u : ℝ =>
        ‖riemannZeta (linePoint u) * moebiusPoly X (linePoint u)‖ ^ 2 :=
      ((continuous_zeta_linePoint.mul (continuous_moebiusPoly_line X)).norm).pow 2
    have hint := intervalIntegral.integral_mono_on (μ := volume) (a := (0 : ℝ)) (b := 1) zero_le_one
      (hcont.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _) hpt
    rw [intervalIntegral.integral_const] at hint
    simpa using hint
  · intro h
    obtain ⟨c₀, hc₀, hlow⟩ := exists_norm_zeta_linePoint_ge
    refine zetaZeroWidth_le_of_window_moebius_secondMoment (c := 0) (δ := 1) hβ one_pos
      fun ε hε => ?_
    obtain ⟨B, hB0, hB⟩ := h ε hε
    refine ⟨(c₀ ^ 2)⁻¹ * B, by positivity, fun k hk => ?_⟩
    rw [zero_add]
    have hpt : ∀ u ∈ Icc (0 : ℝ) 1, ‖moebiusPoly k (linePoint u)‖ ^ 2 ≤
        (c₀ ^ 2)⁻¹ * ‖riemannZeta (linePoint u) * moebiusPoly k (linePoint u)‖ ^ 2 := by
      intro u hu
      rw [norm_mul, mul_pow, ← mul_assoc]
      have hc : (c₀ ^ 2) ≤ ‖riemannZeta (linePoint u)‖ ^ 2 :=
        pow_le_pow_left₀ hc₀.le (hlow u hu) 2
      have hc2 : 1 ≤ (c₀ ^ 2)⁻¹ * ‖riemannZeta (linePoint u)‖ ^ 2 := by
        rw [← div_eq_inv_mul, one_le_div (by positivity)]
        exact hc
      nlinarith [sq_nonneg ‖moebiusPoly k (linePoint u)‖]
    have hc1 : Continuous fun u : ℝ => ‖moebiusPoly k (linePoint u)‖ ^ 2 :=
      (continuous_moebiusPoly_line k).norm.pow 2
    have hc2 : Continuous fun u : ℝ =>
        ‖riemannZeta (linePoint u) * moebiusPoly k (linePoint u)‖ ^ 2 :=
      ((continuous_zeta_linePoint.mul (continuous_moebiusPoly_line k)).norm).pow 2
    have hmono := intervalIntegral.integral_mono_on (μ := volume) (a := (0 : ℝ)) (b := 1) zero_le_one
      (hc1.intervalIntegrable _ _) ((hc2.intervalIntegrable _ _).const_mul _) hpt
    rw [intervalIntegral.integral_const_mul] at hmono
    have h3 := mul_le_mul_of_nonneg_left (hB k hk) (by positivity : 0 ≤ (c₀ ^ 2)⁻¹)
    calc _ ≤ _ := hmono
      _ ≤ _ := h3
      _ = _ := by ring

/-- **RH in one window.** `RH ⇔ ∫_0^1 |ζ M_X(½ + iu)|² du ≪_ε X^{2ε}`. -/
theorem riemannHypothesis_iff_unit_window :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℕ, 1 ≤ X →
      ∫ u in (0 : ℝ)..1, ‖riemannZeta (linePoint u) * moebiusPoly X (linePoint u)‖ ^ 2 ≤
        B * (X : ℝ) ^ (2 * ε) := by
  rw [_root_.RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero,
    ← zetaZeroWidth_le_iff_xiZeroHalfPlaneBound le_rfl, zetaZeroWidth_le_iff_unit_window le_rfl]
  simp only [zero_add]

end GaloisForLFunctions.MultiscaleMollifiedZetaField
