import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheWidthIsReadInOneWindow
import GaloisForLFunctions.HTGeometry.BallLogarithm
import GaloisForLFunctions.HTGeometry.ThreeCircles
import GaloisForLFunctions.RHTower.ArgumentVariation

/-!
# The zeros of the Möbius polynomials condense on the abscissa

Let `M_X = Σ_{n≤X} μ(n) n^{−s}` and `Θ = ½ + zetaZeroWidth`, the abscissa of the Möbius series.

* **Jentzsch half** (`exists_zero_moebiusPoly_near`). Every disc around a point of `Re s = Θ` holds a zero of `M_X` for arbitrarily large `X`.
* **Hurwitz half** (`eventually_moebiusPoly_ne_zero`). A compact set in `Re s > Θ` that avoids `s = 1` holds no zero of `M_X` once `X` is large.

So `Re s = Θ` is exactly where the zeros of `M_X` accumulate in `Re s ≥ Θ`, apart from `s = 1`. It reads the width (`zetaZeroWidth_le_iff_moebiusPoly_zero_free`), and RH is the statement that the zeros of `M_X` do not
accumulate in `Re s > ½` away from `s = 1` (`riemannHypothesis_iff_moebiusPoly_zero_free`).

**Mechanism of the Jentzsch half.** Suppose `M_X` has no zero on a disc around `c`, `Re c = Θ + r/4`, for all large `X`. A logarithm `g_X` of `M_X/M_X(c)` exists on the disc. Borel–Carathéodory bounds
`|g_X| ≪ log X` from `|M_X| ≤ X`, and `|g_X| ≪ 1` on a small circle around `c`, which lies right of `Θ`, where `M_X → 1/ζ` stays bounded and away from zero. Hadamard's three circles interpolate:
at `s₁ = c − r/2` the logarithm is `≪ (log X)^θ` with `θ < 1`. Hence `|M_X(s₁)| ≪_ε X^ε` to the left of `Θ`, and by Abel summation the Möbius series converges to the right of `s₁`, which forces a zero-free half
plane left of `Θ`: a contradiction.

**The mollifier fails on the abscissa.** At a zero of `M_X` the error `ζM_X − 1` equals `−1`, wherever `ζ` vanishes or not. So every disc on `Re s = Θ` has `|ζM_X − 1| = 1` at some point for arbitrarily large `X`
(`exists_mollified_error_eq_neg_one_near`).
-/

noncomputable section

open Complex MeasureTheory Filter Set Metric
open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth zetaZeroWidth_nonneg zetaZeroWidth_le_half
  zetaZeroWidth_eq_zetaZeroAbscissa_sub_half riemannHypothesis_iff_zetaZeroWidth_eq_zero)
open GaloisForLFunctions.RHTower (DirichletConvergesAt dirichletPartialSum dirichletSum tendsto_dirichletSum
  tendstoLocallyUniformlyOn_dirichletPartialSum)

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-! ### The Möbius series right of the abscissa -/

theorem moebiusPoly_eq_partialSum (X : ℕ) (s : ℂ) :
    moebiusPoly X s = dirichletPartialSum _root_.RHTower.moebiusShift X s := by
  show _root_.RHTower.edPoly _root_.RHTower.mobCoeff (Finset.Icc 1 X) s = _
  rw [_root_.RHTower.edPoly_mobCoeff_Icc_eq_sum_range]
  unfold dirichletPartialSum
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [_root_.RHTower.moebiusShift, _root_.RHTower.moebiusCoeffC, _root_.RHTower.mobCoeff, smul_eq_mul]
  ring

/-- Sections bounded by a power `α` at `s₁` make the Möbius series converge at `s₁ + w`, `w > α`. -/
theorem moebius_convergesAt_of_section_bound {s₁ : ℂ} {C α w : ℝ} (hC0 : 0 ≤ C) (hα : 0 ≤ α) (hw : α < w)
    (h : ∀ X : ℕ, 1 ≤ X → ‖moebiusPoly X s₁‖ ≤ C * (X : ℝ) ^ α) :
    DirichletConvergesAt _root_.RHTower.moebiusShift (s₁ + (w : ℂ)) := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℂ, a = fun n : ℕ =>
      (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s₁) • _root_.RHTower.mobCoeff (n + 1) := ⟨_, rfl⟩
  have hA : ∀ N : ℕ, ‖∑ n ∈ Finset.range N, a n‖ ≤ C * ((N : ℝ) + 1) ^ α := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
      positivity
    · have hrep : ∑ n ∈ Finset.range N, a n = moebiusPoly N s₁ := by
        rw [ha]
        exact (_root_.RHTower.edPoly_mobCoeff_Icc_eq_sum_range N s₁).symm
      rw [hrep]
      refine (h N hN).trans (mul_le_mul_of_nonneg_left ?_ hC0)
      exact Real.rpow_le_rpow (Nat.cast_nonneg N) (by linarith) hα
  obtain ⟨L, hL⟩ := GaloisForLFunctions.RHTower.tendsto_dirichlet_partialSum_of_poly_bounded
    hC0 hα hA (s := (w : ℂ)) (by rw [Complex.ofReal_re]; exact hw)
  refine ⟨L, hL.congr fun N => ?_⟩
  unfold dirichletPartialSum
  refine Finset.sum_congr rfl fun n _ => ?_
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hne : (((n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [ha, neg_add, Complex.cpow_add _ _ hne]
  simp only [_root_.RHTower.moebiusShift, _root_.RHTower.moebiusCoeffC, _root_.RHTower.mobCoeff, smul_eq_mul]
  ring

/-- Right of the abscissa the Möbius series converges. -/
theorem moebius_convergesAt_of_abscissa_lt {w : ℂ} (hw : 1 / 2 + zetaZeroWidth < w.re) :
    DirichletConvergesAt _root_.RHTower.moebiusShift w := by
  obtain ⟨σ', hσ'⟩ : ∃ σ' : ℝ, σ' = (1 / 2 + zetaZeroWidth + w.re) / 2 := ⟨_, rfl⟩
  have habs : _root_.RHTower.zetaZeroAbscissa = 1 / 2 + zetaZeroWidth := by
    rw [zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]
    ring
  have hσ : _root_.RHTower.zetaZeroAbscissa < σ' := by
    rw [habs, hσ']
    linarith
  obtain ⟨K, hK0, hK⟩ := _root_.RHTower.exists_norm_edPoly_mobCoeff_line_le_of_zetaZeroAbscissa_lt hσ
  have hC0 : 0 ≤ K * (1 + |w.im|) := by positivity
  have hconv := moebius_convergesAt_of_section_bound (s₁ := (σ' : ℂ) + (w.im : ℂ) * I)
    (C := K * (1 + |w.im|)) (α := 0) (w := w.re - σ') hC0 le_rfl (by rw [hσ']; linarith) (fun X _ => by
      rw [Real.rpow_zero, mul_one]
      exact hK X w.im)
  have e : ((σ' : ℂ) + (w.im : ℂ) * I) + ((w.re - σ' : ℝ) : ℂ) = w := by
    apply Complex.ext <;> simp
  rwa [e] at hconv

/-- The sum of a convergent Möbius series is `1/ζ` right of the point of convergence. -/
theorem dirichletSum_mul_zeta_of_convergesAt {s₀ : ℂ}
    (h₀ : DirichletConvergesAt _root_.RHTower.moebiusShift s₀) {s : ℂ} (hs : s₀.re < s.re) (hs1 : s ≠ 1) :
    dirichletSum _root_.RHTower.moebiusShift s * riemannZeta s = 1 := by
  obtain ⟨U, hUdef⟩ : ∃ U : Set ℂ, U = {z : ℂ | s₀.re < z.re} := ⟨_, rfl⟩
  have hUopen : IsOpen U := by
    rw [hUdef]
    exact isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected U := by
    rw [hUdef]
    exact (_root_.RHTower.convex_decayHalfPlane s₀.re).isPreconnected
  have hF : DifferentiableOn ℂ (dirichletSum _root_.RHTower.moebiusShift) U := by
    rw [hUdef]
    refine (tendstoLocallyUniformlyOn_dirichletPartialSum h₀).differentiableOn ?_
      (isOpen_lt continuous_const Complex.continuous_re)
    exact Eventually.of_forall fun N =>
      (_root_.RHTower.differentiable_dirichletPartialSum_moebiusShift N).differentiableOn
  have hF1 : AnalyticOnNhd ℂ
      (fun z : ℂ => dirichletSum _root_.RHTower.moebiusShift z * _root_.RHTower.zetaEntire z) U :=
    (hF.mul _root_.RHTower.differentiable_zetaEntire.differentiableOn).analyticOnNhd hUopen
  have hF2 : AnalyticOnNhd ℂ (fun z : ℂ => z - 1) U :=
    ((differentiable_id.sub_const (1 : ℂ)).differentiableOn).analyticOnNhd hUopen
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ℝ, x₁ = max 2 (s₀.re + 1) := ⟨_, rfl⟩
  have hx₁U : (x₁ : ℂ) ∈ U := by
    rw [hUdef]
    show s₀.re < (x₁ : ℂ).re
    rw [Complex.ofReal_re, hx₁]
    exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hagree : (fun z : ℂ => dirichletSum _root_.RHTower.moebiusShift z * _root_.RHTower.zetaEntire z)
      =ᶠ[nhds (x₁ : ℂ)] fun z : ℂ => z - 1 := by
    have hV : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hx₁V : (x₁ : ℂ) ∈ {z : ℂ | 1 < z.re} := by
      show 1 < (x₁ : ℂ).re
      rw [Complex.ofReal_re, hx₁]
      exact lt_of_lt_of_le one_lt_two (le_max_left _ _)
    filter_upwards [hV.mem_nhds hx₁V] with z hz
    have hz1 : 1 < z.re := hz
    have hzne : z ≠ 1 := by
      intro h
      rw [h] at hz1
      simp at hz1
    rw [_root_.RHTower.zetaEntire_eq hzne]
    have := _root_.RHTower.dirichletSum_moebiusShift_mul_riemannZeta hz1
    linear_combination (z - 1) * this
  have heq := hF1.eqOn_of_preconnected_of_eventuallyEq hF2 hUconn hx₁U hagree
  have hval := heq (show s ∈ U by rw [hUdef]; exact hs)
  simp only at hval
  rw [_root_.RHTower.zetaEntire_eq hs1] at hval
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  refine mul_left_cancel₀ hsub ?_
  linear_combination hval

/-- On a compact set right of the abscissa the Möbius polynomials converge uniformly to the Möbius sum. -/
theorem tendstoUniformlyOn_moebiusPoly {K : Set ℂ} (hK : IsCompact K) {σ : ℝ}
    (hσ : 1 / 2 + zetaZeroWidth < σ) (hKre : ∀ z ∈ K, σ < z.re) :
    TendstoUniformlyOn (fun X : ℕ => moebiusPoly X) (dirichletSum _root_.RHTower.moebiusShift) atTop K := by
  have h₀ : DirichletConvergesAt _root_.RHTower.moebiusShift (σ : ℂ) :=
    moebius_convergesAt_of_abscissa_lt (by rwa [Complex.ofReal_re])
  have hloc := tendstoLocallyUniformlyOn_dirichletPartialSum h₀
  have hopen : IsOpen {s : ℂ | (σ : ℂ).re < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).mp hloc K
    (fun z hz => by
      show (σ : ℂ).re < z.re
      rw [Complex.ofReal_re]
      exact hKre z hz) hK
  have hfun : (fun X : ℕ => moebiusPoly X) =
      fun X : ℕ => dirichletPartialSum _root_.RHTower.moebiusShift X := by
    funext X s
    exact moebiusPoly_eq_partialSum X s
  rw [hfun]
  exact hunif

/-- The Möbius sum is continuous on a compact set right of the abscissa. -/
theorem continuousOn_moebiusSum {K : Set ℂ} (hK : IsCompact K) {σ : ℝ}
    (hσ : 1 / 2 + zetaZeroWidth < σ) (hKre : ∀ z ∈ K, σ < z.re) :
    ContinuousOn (dirichletSum _root_.RHTower.moebiusShift) K :=
  (tendstoUniformlyOn_moebiusPoly hK hσ hKre).continuousOn
    (Eventually.of_forall fun X => (differentiable_moebiusPoly X).continuous.continuousOn).frequently

/-- **Hurwitz half.** A compact set in `Re s > Θ` avoiding `s = 1` holds no zero of `M_X` for large `X`. -/
theorem eventually_moebiusPoly_ne_zero {K : Set ℂ} (hK : IsCompact K) (hre : ∀ z ∈ K, 1 / 2 + zetaZeroWidth < z.re)
    (h1 : (1 : ℂ) ∉ K) : ∀ᶠ X : ℕ in atTop, ∀ z ∈ K, moebiusPoly X z ≠ 0 := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact Eventually.of_forall fun X z hz => absurd hz (Set.notMem_empty z)
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_re.continuousOn
  obtain ⟨σ, hσ, hσ'⟩ := exists_between (hre z₀ hz₀)
  have hKre : ∀ z ∈ K, σ < z.re := fun z hz => lt_of_lt_of_le hσ' (hmin hz)
  have hcont := continuousOn_moebiusSum hK hσ hKre
  obtain ⟨z₁, hz₁, hmin₁⟩ := hK.exists_isMinOn hne hcont.norm
  have hval : ∀ z ∈ K, dirichletSum _root_.RHTower.moebiusShift z ≠ 0 := fun z hz h => by
    have hzne : z ≠ 1 := fun e => h1 (e ▸ hz)
    have h2 := dirichletSum_mul_zeta_of_convergesAt (s₀ := (σ : ℂ))
      (moebius_convergesAt_of_abscissa_lt (by rwa [Complex.ofReal_re]))
      (s := z) (by rw [Complex.ofReal_re]; exact hKre z hz) hzne
    rw [h, zero_mul] at h2
    exact zero_ne_one h2
  have hm : 0 < ‖dirichletSum _root_.RHTower.moebiusShift z₁‖ := norm_pos_iff.mpr (hval z₁ hz₁)
  have hunif := (Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_moebiusPoly hK hσ hKre)) _ hm
  filter_upwards [hunif] with X hX z hz h0
  have h2 := hX z hz
  rw [h0, dist_zero_right] at h2
  exact absurd (hmin₁ hz) (not_le.mpr h2)

/-! ### The Jentzsch half -/

/-- A logarithm of `f` on the disc, of size `≪ log X` on the large circle and `≪ 1` on the small circle. -/
theorem exists_log_bounds {f : ℂ → ℂ} {c : ℂ} {r X A m : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball c (5 * r / 8))) (hne : ∀ z ∈ ball c (5 * r / 8), f z ≠ 0)
    (hX : ∀ z ∈ ball c (5 * r / 8), ‖f z‖ ≤ X) (hA : ∀ z ∈ closedBall c (r / 8), ‖f z‖ ≤ A)
    (hm0 : 0 < m) (hm : m ≤ ‖f c‖) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c (5 * r / 8)) ∧
      (∀ z ∈ ball c (5 * r / 8), f z = f c * Complex.exp (g z)) ∧
      (∀ z : ℂ, ‖z - c‖ = 9 * r / 16 → ‖g z‖ ≤ 18 * (Real.log (X / m) + 1)) ∧
      ∀ z : ℂ, ‖z - c‖ = r / 16 → ‖g z‖ ≤ 2 * (Real.log (A / m) + 1) := by
  obtain ⟨g, hg, hg0, hgeq, hbig⟩ := GaloisForLFunctions.HTGeometry.exists_bound_log_on_ball
    (r := 9 * r / 16) (by positivity) (by linarith) hf hne hX hm0 hm
  refine ⟨g, hg, hgeq, fun z hz => ?_, fun z hz => ?_⟩
  · refine (hbig z hz.le).trans (le_of_eq ?_)
    field_simp
    ring
  · have hsub : ball c (r / 8) ⊆ ball c (5 * r / 8) := ball_subset_ball (by linarith)
    have hc0 : c ∈ closedBall c (r / 8) := mem_closedBall_self (by positivity)
    have hfc : 0 < ‖f c‖ := by linarith
    have hAm : 1 ≤ A / m := by
      rw [le_div_iff₀ hm0, one_mul]
      exact hm.trans (hA c hc0)
    have hlog : 0 ≤ Real.log (A / m) := Real.log_nonneg hAm
    have hRe : ∀ w ∈ ball c (r / 8), (g w).re ≤ Real.log (A / m) + 1 := fun w hw => by
      have h1 := hgeq w (hsub hw)
      have h2 : ‖f w‖ = ‖f c‖ * Real.exp (g w).re := by
        rw [h1, norm_mul, Complex.norm_exp]
      have h3 : Real.exp (g w).re ≤ A / m := by
        rw [le_div_iff₀ hm0]
        have h4 := hA w (ball_subset_closedBall hw)
        rw [h2] at h4
        have h5 := Real.exp_pos (g w).re
        nlinarith
      have h6 := (Real.le_log_iff_exp_le (by linarith)).mpr h3
      linarith
    have hz' : z ∈ ball c (r / 8) := by
      rw [mem_ball_iff_norm, hz]
      linarith
    have hBC := _root_.RHTower.borel_caratheodory (hg.mono hsub) hRe
      (by rw [hg0, Complex.zero_re]; linarith) hz'
    rw [hg0, sub_zero, hz, Complex.zero_re, sub_zero] at hBC
    refine hBC.trans (le_of_eq ?_)
    field_simp
    ring

/-- Hadamard's three circles at `s₁` between the two circles of `exists_log_bounds`. -/
theorem norm_log_left_le {g : ℂ → ℂ} {c s₁ : ℂ} {r M₁ M₃ : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball c (5 * r / 8))) (h1 : ∀ z : ℂ, ‖z - c‖ = r / 16 → ‖g z‖ ≤ M₁)
    (h3 : ∀ z : ℂ, ‖z - c‖ = 9 * r / 16 → ‖g z‖ ≤ M₃) (hs : ‖s₁ - c‖ = r / 2) :
    ‖g s₁‖ ≤ M₁ ^ (1 - (Real.log (r / 2) - Real.log (r / 16)) / (Real.log (9 * r / 16) - Real.log (r / 16))) *
      M₃ ^ ((Real.log (r / 2) - Real.log (r / 16)) / (Real.log (9 * r / 16) - Real.log (r / 16))) := by
  have hmain := GaloisForLFunctions.HTGeometry.norm_le_of_three_circles (f := fun w => g (c + w))
    (r₁ := r / 16) (r₃ := 9 * r / 16) (by positivity) (by linarith) (fun z _ hz3 => by
      have hmem : c + z ∈ ball c (5 * r / 8) := by
        rw [mem_ball_iff_norm, add_sub_cancel_left]
        linarith
      have hd : DifferentiableAt ℂ g (c + z) := hg.differentiableAt (isOpen_ball.mem_nhds hmem)
      exact hd.comp z ((differentiableAt_const c).add differentiableAt_id))
    (M₁ := M₁) (M₃ := M₃) (fun z hz => h1 _ (by rw [add_sub_cancel_left]; exact hz))
    (fun z hz => h3 _ (by rw [add_sub_cancel_left]; exact hz)) (z := s₁ - c)
    (by rw [hs]; linarith) (by rw [hs]; linarith)
  simp only [add_sub_cancel] at hmain
  rw [hs] at hmain
  exact hmain

/-- The interpolation exponent lies in `[0, 1)`. -/
theorem interpolation_exponent_bounds {r : ℝ} (hr : 0 < r) :
    0 ≤ (Real.log (r / 2) - Real.log (r / 16)) / (Real.log (9 * r / 16) - Real.log (r / 16)) ∧
      (Real.log (r / 2) - Real.log (r / 16)) / (Real.log (9 * r / 16) - Real.log (r / 16)) < 1 := by
  have h1 : Real.log (r / 16) < Real.log (r / 2) := Real.log_lt_log (by positivity) (by linarith)
  have h2 : Real.log (r / 2) < Real.log (9 * r / 16) := Real.log_lt_log (by positivity) (by linarith)
  have h3 : 0 < Real.log (9 * r / 16) - Real.log (r / 16) := by linarith
  exact ⟨div_nonneg (by linarith) h3.le, by rw [div_lt_one h3]; linarith⟩

/-- An interpolation below exponent one is eventually beaten by a linear function. -/
theorem eventually_interpolation_le {M₁ K θ ε : ℝ} (hM₁ : 0 ≤ M₁) (hK : 0 ≤ K) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hε : 0 < ε) : ∀ᶠ y : ℝ in atTop, M₁ ^ (1 - θ) * (K * y) ^ θ ≤ ε * y := by
  have hθ : 0 < 1 - θ := by linarith
  filter_upwards [(tendsto_rpow_atTop hθ).eventually_ge_atTop (M₁ ^ (1 - θ) * K ^ θ / ε),
    eventually_gt_atTop 0] with y hy hy0
  rw [div_le_iff₀ hε] at hy
  have hsplit : y = y ^ (1 - θ) * y ^ θ := by
    rw [← Real.rpow_add hy0]
    simp
  have hyθ : 0 ≤ y ^ θ := by positivity
  rw [Real.mul_rpow hK hy0.le]
  calc M₁ ^ (1 - θ) * (K ^ θ * y ^ θ) = (M₁ ^ (1 - θ) * K ^ θ) * y ^ θ := by ring
    _ ≤ (y ^ (1 - θ) * ε) * y ^ θ := mul_le_mul_of_nonneg_right hy hyθ
    _ = ε * (y ^ (1 - θ) * y ^ θ) := by ring
    _ = ε * y := by rw [← hsplit]

/-- Near `c`, right of the abscissa, `M_X` is eventually bounded and bounded away from zero at `c`. -/
theorem exists_bounds_near {c : ℂ} {r : ℝ} (hr : 0 < r) (hcre : c.re = 1 / 2 + zetaZeroWidth + r / 4) (hc1 : c ≠ 1) :
    ∃ m A : ℝ, 0 < m ∧ ∀ᶠ X : ℕ in atTop, m ≤ ‖moebiusPoly X c‖ ∧
      ∀ z ∈ closedBall c (r / 8), ‖moebiusPoly X z‖ ≤ A := by
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = 1 / 2 + zetaZeroWidth + r / 16 := ⟨_, rfl⟩
  have hσ1 : 1 / 2 + zetaZeroWidth < σ := by
    rw [hσ]
    linarith
  have hKre : ∀ z ∈ closedBall c (r / 8), σ < z.re := fun z hz => by
    have h1 : ‖z - c‖ ≤ r / 8 := by rwa [mem_closedBall_iff_norm] at hz
    have h2 := Complex.abs_re_le_norm (z - c)
    rw [Complex.sub_re] at h2
    have h3 := abs_le.mp (h2.trans h1)
    rw [hσ]
    linarith [h3.1]
  have hcomp : IsCompact (closedBall c (r / 8)) := isCompact_closedBall c _
  have hcont := continuousOn_moebiusSum hcomp hσ1 hKre
  obtain ⟨B, hB⟩ := hcomp.exists_bound_of_continuousOn hcont
  have hc0 : c ∈ closedBall c (r / 8) := mem_closedBall_self (by positivity)
  have hval : dirichletSum _root_.RHTower.moebiusShift c ≠ 0 := fun h => by
    have h2 := dirichletSum_mul_zeta_of_convergesAt (s₀ := (σ : ℂ))
      (moebius_convergesAt_of_abscissa_lt (by rwa [Complex.ofReal_re]))
      (s := c) (by rw [Complex.ofReal_re]; exact hKre c hc0) hc1
    rw [h, zero_mul] at h2
    exact zero_ne_one h2
  have hf0 : 0 < ‖dirichletSum _root_.RHTower.moebiusShift c‖ := norm_pos_iff.mpr hval
  refine ⟨‖dirichletSum _root_.RHTower.moebiusShift c‖ / 2, B + ‖dirichletSum _root_.RHTower.moebiusShift c‖ / 2,
    by positivity, ?_⟩
  have hunif := Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_moebiusPoly hcomp hσ1 hKre)
    (‖dirichletSum _root_.RHTower.moebiusShift c‖ / 2) (by positivity)
  filter_upwards [hunif] with X hX
  refine ⟨?_, fun z hz => ?_⟩
  · have h1 := hX c hc0
    rw [dist_eq_norm] at h1
    have h2 := norm_sub_norm_le (dirichletSum _root_.RHTower.moebiusShift c) (moebiusPoly X c)
    linarith
  · have h1 := hX z hz
    rw [dist_eq_norm] at h1
    have h2 := norm_sub_norm_le (moebiusPoly X z) (dirichletSum _root_.RHTower.moebiusShift z)
    rw [norm_sub_rev] at h2
    linarith [hB z hz]

/-- The size of the logarithm on the large circle is linear in `log X`. -/
theorem eventually_large_circle_le {m : ℝ} (hm : 0 < m) :
    ∀ᶠ y : ℝ in atTop, 0 ≤ 18 * (y - Real.log m + 1) ∧ 18 * (y - Real.log m + 1) ≤ 19 * y := by
  filter_upwards [eventually_ge_atTop (18 * (|Real.log m| + 1))] with y hy
  have h0 := abs_nonneg (Real.log m)
  have h1 := le_abs_self (Real.log m)
  have h2 := neg_abs_le (Real.log m)
  constructor <;> nlinarith

/-- If `M_X` has no zero near `s₀` for all large `X`, then `|M_X(s₁)| ≪_ε X^ε` at the point `s₁ = c − r/2` left of the abscissa. -/
theorem exists_section_bound_of_zero_free {c s₀ : ℂ} {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hcre : c.re = 1 / 2 + zetaZeroWidth + r / 4) (hc1 : c ≠ 1)
    (hsub : ball c (5 * r / 8) ⊆ ball s₀ r) (X₀ : ℕ)
    (hfree : ∀ X : ℕ, X₀ ≤ X → ∀ z ∈ ball s₀ r, moebiusPoly X z ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X → ‖moebiusPoly X (c - ((r / 2 : ℝ) : ℂ))‖ ≤ C * (X : ℝ) ^ ε := by
  obtain ⟨m, A, hm, hbounds⟩ := exists_bounds_near hr hcre hc1
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (Real.log (r / 2) - Real.log (r / 16)) / (Real.log (9 * r / 16) - Real.log (r / 16)) :=
    ⟨_, rfl⟩
  obtain ⟨hθ0, hθ1⟩ := interpolation_exponent_bounds hr
  rw [← hθ] at hθ0 hθ1
  obtain ⟨M₁, hM₁⟩ : ∃ M₁ : ℝ, M₁ = max (2 * (Real.log (A / m) + 1)) 0 := ⟨_, rfl⟩
  have hM₁0 : 0 ≤ M₁ := by
    rw [hM₁]
    exact le_max_right _ _
  have hlogX : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop := tendsto_log_natCast_atTop
  have hev := hlogX.eventually (eventually_interpolation_le (M₁ := M₁) (K := 19) hM₁0 (by norm_num) hθ0 hθ1 hε)
  have hev2 := hlogX.eventually (eventually_large_circle_le hm)
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp ((hbounds.and (hev.and hev2)).and
    ((eventually_ge_atTop X₀).and (eventually_ge_atTop 1)))
  have hs₁re : 0 ≤ (c - ((r / 2 : ℝ) : ℂ)).re := by
    rw [Complex.sub_re, Complex.ofReal_re, hcre]
    have := zetaZeroWidth_nonneg
    linarith
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : ℝ, A₀ = max A 0 := ⟨_, rfl⟩
  have hA₀0 : 0 ≤ A₀ := by
    rw [hA₀]
    exact le_max_right _ _
  refine ⟨A₀ + X₁, by positivity, fun X hX => ?_⟩
  have hX1R : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hpow : (1 : ℝ) ≤ (X : ℝ) ^ ε := Real.one_le_rpow hX1R hε.le
  rcases lt_or_ge X X₁ with hlt | hge
  · have h1 := _root_.RHTower.norm_edPoly_mobCoeff_le X hs₁re
    have h2 : (X : ℝ) ≤ X₁ := by exact_mod_cast hlt.le
    have h3 : (X₁ : ℝ) ≤ (A₀ + X₁) * 1 := by linarith
    calc ‖moebiusPoly X (c - ((r / 2 : ℝ) : ℂ))‖ ≤ X := h1
      _ ≤ (A₀ + X₁) * 1 := h2.trans h3
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  · obtain ⟨⟨⟨hmX, hAX⟩, hinterp, hlarge0, hlarge⟩, hX0, hX1⟩ := hX₁ X hge
    have hballs : ∀ z ∈ ball c (5 * r / 8), moebiusPoly X z ≠ 0 := fun z hz => hfree X hX0 z (hsub hz)
    have hXnorm : ∀ z ∈ ball c (5 * r / 8), ‖moebiusPoly X z‖ ≤ (X : ℝ) := fun z hz => by
      refine _root_.RHTower.norm_edPoly_mobCoeff_le X ?_
      have h1 : ‖z - c‖ < 5 * r / 8 := by rwa [mem_ball_iff_norm] at hz
      have h2 := Complex.abs_re_le_norm (z - c)
      rw [Complex.sub_re] at h2
      have h3 := abs_lt.mp (lt_of_le_of_lt h2 h1)
      have h4 := zetaZeroWidth_nonneg
      linarith [h3.1]
    obtain ⟨g, hg, hgeq, hbig, hsmall⟩ := exists_log_bounds (f := moebiusPoly X) hr
      (differentiable_moebiusPoly X).differentiableOn hballs hXnorm hAX hm hmX
    have hsnorm : ‖(c - ((r / 2 : ℝ) : ℂ)) - c‖ = r / 2 := by
      rw [sub_sub_cancel_left, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hthree := norm_log_left_le hr hg (M₁ := M₁)
      (fun z hz => (hsmall z hz).trans (by rw [hM₁]; exact le_max_left _ _)) hbig hsnorm
    rw [← hθ] at hthree
    have hXpos : (0 : ℝ) < X := by linarith
    have hlogdiv : Real.log ((X : ℝ) / m) = Real.log X - Real.log m := Real.log_div hXpos.ne' hm.ne'
    have hM₃ : (18 * (Real.log ((X : ℝ) / m) + 1)) ^ θ ≤ (19 * Real.log X) ^ θ := by
      rw [hlogdiv]
      exact Real.rpow_le_rpow hlarge0 hlarge hθ0
    have hg1 : ‖g (c - ((r / 2 : ℝ) : ℂ))‖ ≤ ε * Real.log X :=
      hthree.trans ((mul_le_mul_of_nonneg_left hM₃ (by positivity)).trans hinterp)
    have hmem : c - ((r / 2 : ℝ) : ℂ) ∈ ball c (5 * r / 8) := by
      rw [mem_ball_iff_norm, hsnorm]
      linarith
    have hval := hgeq _ hmem
    have hexp : Real.exp (g (c - ((r / 2 : ℝ) : ℂ))).re ≤ (X : ℝ) ^ ε := by
      rw [Real.rpow_def_of_pos hXpos]
      refine Real.exp_le_exp.2 ?_
      have h1 := Complex.re_le_norm (g (c - ((r / 2 : ℝ) : ℂ)))
      linarith
    have hc0 : c ∈ closedBall c (r / 8) := mem_closedBall_self (by positivity)
    have hA₀c : ‖moebiusPoly X c‖ ≤ A₀ := (hAX c hc0).trans (by rw [hA₀]; exact le_max_left _ _)
    rw [hval, norm_mul, Complex.norm_exp]
    calc ‖moebiusPoly X c‖ * Real.exp (g (c - ((r / 2 : ℝ) : ℂ))).re ≤ A₀ * (X : ℝ) ^ ε :=
          mul_le_mul hA₀c hexp (Real.exp_pos _).le hA₀0
      _ ≤ (A₀ + X₁) * (X : ℝ) ^ ε := mul_le_mul_of_nonneg_right (by positivity) (by positivity)

/-- Subpower sections at `s₁` put every zero of `ζ` at or left of `s₁`. -/
theorem zero_re_le_of_section_bound {s₁ : ℂ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X → ‖moebiusPoly X s₁‖ ≤ C * (X : ℝ) ^ ε)
    {ρ : ℂ} (hζ : riemannZeta ρ = 0) : ρ.re ≤ s₁.re := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (ρ.re - s₁.re) / 3 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by
    rw [hε]
    linarith
  obtain ⟨C, hC0, hC⟩ := h ε hε0
  have h₀ := moebius_convergesAt_of_section_bound (w := 2 * ε) hC0 hε0.le (by linarith) hC
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    exact riemannZeta_ne_zero_of_one_le_re (by simp) hζ
  refine _root_.RHTower.riemannZeta_ne_zero_of_moebius_convergesAt h₀ ?_ hρ1 hζ
  rw [Complex.add_re, Complex.ofReal_re, hε]
  linarith

/-- **Jentzsch half.** Every disc around a point of `Re s = ½ + zetaZeroWidth` holds a zero of `M_X` for arbitrarily large `X`. -/
theorem exists_zero_moebiusPoly_near {s₀ : ℂ} (hs₀ : s₀.re = 1 / 2 + zetaZeroWidth) {R : ℝ} (hR : 0 < R) (X₀ : ℕ) :
    ∃ X : ℕ, X₀ ≤ X ∧ ∃ z ∈ ball s₀ R, moebiusPoly X z = 0 := by
  by_contra hno
  push_neg at hno
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min R 1 := ⟨_, rfl⟩
  have hr0 : 0 < r := by
    rw [hr]
    exact lt_min hR one_pos
  have hr1 : r ≤ 1 := by
    rw [hr]
    exact min_le_right _ _
  have hrR : r ≤ R := by
    rw [hr]
    exact min_le_left _ _
  have hfree : ∀ X : ℕ, X₀ ≤ X → ∀ z ∈ ball s₀ r, moebiusPoly X z ≠ 0 := fun X hX z hz =>
    hno X hX z (ball_subset_ball hrR hz)
  -- a centre other than `s = 1`, right of the abscissa
  obtain ⟨c, hcre, hc1, hcnorm⟩ : ∃ c : ℂ, c.re = 1 / 2 + zetaZeroWidth + r / 4 ∧ c ≠ 1 ∧ ‖c - s₀‖ ≤ 3 * r / 8 := by
    by_cases h1 : s₀ + ((r / 4 : ℝ) : ℂ) = 1
    · refine ⟨s₀ + ((r / 4 : ℝ) : ℂ) + ((r / 8 : ℝ) : ℂ) * I, ?_, ?_, ?_⟩
      · simp [hs₀]
      · rw [h1]
        intro h2
        have h3 := congrArg Complex.im h2
        simp at h3
        linarith
      · have e : s₀ + ((r / 4 : ℝ) : ℂ) + ((r / 8 : ℝ) : ℂ) * I - s₀ =
            ((r / 4 : ℝ) : ℂ) + ((r / 8 : ℝ) : ℂ) * I := by ring
        rw [e]
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
        linarith
    · refine ⟨s₀ + ((r / 4 : ℝ) : ℂ), ?_, h1, ?_⟩
      · simp [hs₀]
      · rw [add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        linarith
  have hsub : ball c (5 * r / 8) ⊆ ball s₀ r := fun z hz => by
    rw [mem_ball_iff_norm] at hz ⊢
    have h1 : ‖z - s₀‖ ≤ ‖z - c‖ + ‖c - s₀‖ := by
      have e : z - s₀ = (z - c) + (c - s₀) := by ring
      rw [e]
      exact norm_add_le _ _
    linarith
  have hsection := fun (ε : ℝ) (hε : 0 < ε) =>
    exists_section_bound_of_zero_free hr0 hr1 hcre hc1 hsub X₀ hfree hε
  have hle : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re ≤ 1 / 2 + zetaZeroWidth - r / 4 := fun ρ hζ => by
    have h1 := zero_re_le_of_section_bound hsection hζ
    rw [Complex.sub_re, Complex.ofReal_re, hcre] at h1
    linarith
  have habs : _root_.RHTower.zetaZeroAbscissa = 1 / 2 + zetaZeroWidth := by
    rw [zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]
    ring
  obtain ⟨ρ, hζ, hρ⟩ := _root_.RHTower.exists_zetaZero_lt_re
    (b := 1 / 2 + zetaZeroWidth - r / 4) (by rw [habs]; linarith)
  linarith [hle ρ hζ]

/-- **The mollifier fails on the abscissa.** Every disc around a point of `Re s = ½ + zetaZeroWidth` has a point with `ζ M_X − 1 = −1` for arbitrarily large `X`. -/
theorem exists_mollified_error_eq_neg_one_near {s₀ : ℂ} (hs₀ : s₀.re = 1 / 2 + zetaZeroWidth) {R : ℝ} (hR : 0 < R)
    (X₀ : ℕ) : ∃ X : ℕ, X₀ ≤ X ∧ ∃ z ∈ ball s₀ R, riemannZeta z * moebiusPoly X z - 1 = -1 := by
  obtain ⟨X, hX, z, hz, h0⟩ := exists_zero_moebiusPoly_near hs₀ hR X₀
  exact ⟨X, hX, z, hz, by rw [h0, mul_zero, zero_sub]⟩

/-! ### The zeros of the Möbius polynomials read the width -/

/-- **The zeros of `M_X` read the width.** `zetaZeroWidth ≤ β`, `β ≥ 0`, iff each compact set in `Re s > ½ + β` avoiding `s = 1` holds no zero of `M_X` for large `X`. -/
theorem zetaZeroWidth_le_iff_moebiusPoly_zero_free {β : ℝ} (hβ : 0 ≤ β) :
    zetaZeroWidth ≤ β ↔ ∀ K : Set ℂ, IsCompact K → (∀ z ∈ K, 1 / 2 + β < z.re) → (1 : ℂ) ∉ K →
      ∀ᶠ X : ℕ in atTop, ∀ z ∈ K, moebiusPoly X z ≠ 0 := by
  refine ⟨fun hw K hK hre h1 => eventually_moebiusPoly_ne_zero hK (fun z hz => by linarith [hre z hz]) h1, fun h => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  -- a disc on the abscissa, off the real axis and right of `½ + β`
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℂ, s₀ = ((1 / 2 + zetaZeroWidth : ℝ) : ℂ) + I := ⟨_, rfl⟩
  have hs₀re : s₀.re = 1 / 2 + zetaZeroWidth := by
    rw [hs₀]
    simp
  have hs₀im : s₀.im = 1 := by
    rw [hs₀]
    simp
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = min ((zetaZeroWidth - β) / 2) (1 / 2) := ⟨_, rfl⟩
  have hR0 : 0 < R := by
    rw [hR]
    exact lt_min (by linarith) (by norm_num)
  have hR1 : R ≤ (zetaZeroWidth - β) / 2 := by
    rw [hR]
    exact min_le_left _ _
  have hR2 : R ≤ 1 / 2 := by
    rw [hR]
    exact min_le_right _ _
  have hev := h (closedBall s₀ R) (isCompact_closedBall s₀ R) (fun z hz => by
      have h1 : ‖z - s₀‖ ≤ R := by rwa [mem_closedBall_iff_norm] at hz
      have h2 := Complex.abs_re_le_norm (z - s₀)
      rw [Complex.sub_re, hs₀re] at h2
      have h3 := abs_le.mp (h2.trans h1)
      linarith [h3.1]) (fun hmem => by
      have h1 : ‖(1 : ℂ) - s₀‖ ≤ R := by rwa [mem_closedBall_iff_norm] at hmem
      have h2 := Complex.abs_im_le_norm ((1 : ℂ) - s₀)
      rw [Complex.sub_im, hs₀im, Complex.one_im] at h2
      norm_num at h2
      linarith)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hev
  obtain ⟨X, hX, z, hz, h0⟩ := exists_zero_moebiusPoly_near hs₀re hR0 X₀
  exact hX₀ X hX z (ball_subset_closedBall hz) h0

/-- **RH reads the zeros of `M_X`.** RH holds iff each compact set in `Re s > ½` avoiding `s = 1` holds no zero of `M_X` for large `X`. -/
theorem riemannHypothesis_iff_moebiusPoly_zero_free :
    RiemannHypothesis ↔ ∀ K : Set ℂ, IsCompact K → (∀ z ∈ K, 1 / 2 < z.re) → (1 : ℂ) ∉ K →
      ∀ᶠ X : ℕ in atTop, ∀ z ∈ K, moebiusPoly X z ≠ 0 := by
  have h := zetaZeroWidth_le_iff_moebiusPoly_zero_free (β := 0) le_rfl
  simp only [add_zero] at h
  rw [riemannHypothesis_iff_zetaZeroWidth_eq_zero, ← h]
  exact ⟨fun e => e.le, fun e => le_antisymm e zetaZeroWidth_nonneg⟩

end GaloisForLFunctions.MultiscaleMollifiedZetaField
