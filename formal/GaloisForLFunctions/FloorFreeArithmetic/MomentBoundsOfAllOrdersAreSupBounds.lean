import GaloisForLFunctions.FloorFreeArithmetic.MomentsOnWindowsAmplifyTheDepth
import GaloisForLFunctions.SurfaceOfSpecZ.TheTraceZetaFunctionAtThePowerDegrees

/-!
# Moment bounds of all orders are sup bounds

The amplification receiver asks for bounds `∫_T^{T+L} (2 Re S)^{2k} ≤ C_k e^{AT}` of all orders
`k` with one exponent `A`, on arbitrarily late windows of one length. This file identifies the
hypothesis: it is a bound for the powers of the sup norm on the same windows.

The spline trace `2 Re S` of a tempered configuration is Lipschitz on `[−R, R]` with a constant
`D e^{R/2}`: its coefficients decay like `|γ|^{−8}`. A function with the value `M` at a point of
a window and Lipschitz constant `K` has `|f| ≥ M/2` on an interval of length `min(M/2K, L/2)`
of the window, so its `2k`-th moment is at least `(M/2)^{2k} min(M/2K, L/2)`. Hence a bound for
the `2k`-th moment gives `|2 Re S|^{2k+1} ≤ 2^{2k+1} G C e^{(A+1)T}` at every point of the window,
with `G` independent of the order.

* `exists_lipschitz_two_re_lagStructure`: the Lipschitz rate of the spline trace.
* `pow_mul_min_le_integral_pow`: a large value on a window is a large moment.
* `exists_abs_trace_pow_le_of_moment_le`: a moment bound is a pointwise bound.
* `windowMomentsBounded_iff_windowSupPowersBounded`: bounds for all moments with one exponent
  are bounds for all powers of the sup norm with one exponent.
* `windowSupPowersBounded_of_subexponential`,
  `asymptoticAbscissaLaw_of_windowSupPowersBounded`: a two-sided bound `C_ε e^{εT}` for every
  `ε > 0` on arbitrarily late windows is such a family, and it gives the abscissa law.

So amplification over the order of a window moment accepts exactly the producers of a
sub-exponential two-sided bound on the window: the bound of the Riemann hypothesis on some late
windows. A bound of one order `2k` with the exponent `A` reaches the depth `A/2k` only.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open SquareRootThreshold Zeta23 _root_.RHTower SurfaceOfSpecZ SurfaceOfSpecZ.ScaleLocality

variable {Z : ZeroConfig}

/-! ### The Lipschitz rate of the spline trace -/

/-- A character of the strip is Lipschitz on `[−R, R]` with the constant `|γ| e^{R/2}`. -/
theorem norm_cexp_I_mul_sub_le {γ : ℂ} (hγ : |γ.im| ≤ 1 / 2) {R v v' : ℝ} (hv : |v| ≤ R)
    (hv' : |v'| ≤ R) :
    ‖cexp (I * γ * v) - cexp (I * γ * v')‖ ≤ ‖γ‖ * Real.exp (R / 2) * |v - v'| := by
  have hder : ∀ t ∈ Icc (-R) R, HasDerivWithinAt (fun t : ℝ => cexp (I * γ * t))
      (cexp (I * γ * t) * (I * γ * ((1 : ℝ) : ℂ))) (Icc (-R) R) t := fun t _ =>
    (((hasDerivAt_id t).ofReal_comp.const_mul (I * γ)).cexp).hasDerivWithinAt
  have hbound : ∀ t ∈ Icc (-R) R,
      ‖cexp (I * γ * t) * (I * γ * ((1 : ℝ) : ℂ))‖ ≤ ‖γ‖ * Real.exp (R / 2) := by
    intro t ht
    rw [Complex.ofReal_one, mul_one, norm_mul, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_exp, mul_comm ‖γ‖]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg γ)
    have hre : (I * γ * t).re = -(γ.im * t) := by simp [Complex.mul_re]
    rw [hre]
    have h1 : |γ.im * t| ≤ 1 / 2 * R := by
      rw [abs_mul]
      exact mul_le_mul hγ (abs_le.mpr ht) (abs_nonneg _) (by norm_num)
    linarith only [h1, neg_le_abs (γ.im * t)]
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound (convex_Icc (-R) R)
    (abs_le.mp hv') (abs_le.mp hv)
  rwa [Real.norm_eq_abs] at h

/-- Two factors of decay `(1 + x)^{−4}` absorb one power of the frequency. -/
theorem mul_mul_le_of_decay {a c x P : ℝ} (hx : 0 ≤ x) (hP : 0 ≤ P) (hc : 0 ≤ c)
    (h1 : a ≤ P / (1 + x) ^ 4) (h2 : c ≤ P / (1 + x) ^ 4) :
    a * c * x ≤ P ^ 2 / (1 + x ^ 2) := by
  have hD : 0 < (1 + x) ^ 4 := by positivity
  have hac : a * c ≤ P / (1 + x) ^ 4 * (P / (1 + x) ^ 4) :=
    mul_le_mul h1 h2 hc (by positivity)
  have hpoly : x * (1 + x ^ 2) ≤ ((1 + x) ^ 4) ^ 2 := by
    nlinarith only [hx, pow_nonneg hx 2, pow_nonneg hx 3, pow_nonneg hx 4, pow_nonneg hx 5,
      pow_nonneg hx 6, pow_nonneg hx 7, pow_nonneg hx 8]
  rw [le_div_iff₀ (by positivity)]
  calc a * c * x * (1 + x ^ 2) = a * c * (x * (1 + x ^ 2)) := by ring
    _ ≤ P / (1 + x) ^ 4 * (P / (1 + x) ^ 4) * ((1 + x) ^ 4) ^ 2 :=
        mul_le_mul hac hpoly (by positivity) (by positivity)
    _ = P ^ 2 := by field_simp

/-- **The spline trace has the Lipschitz rate `e^{R/2}`.** -/
theorem exists_lipschitz_two_re_lagStructure (hZ : TemperedConfig Z) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ R v v' : ℝ, |v| ≤ R → |v'| ≤ R →
      |2 * (lagStructure Z (boxSpline 1 3) v).re - 2 * (lagStructure Z (boxSpline 1 3) v').re| ≤
        D * Real.exp (R / 2) * |v - v'| := by
  have hB : Continuous (boxSpline 1 3) := (contDiff_boxSpline (r := 1) one_pos 2).continuous
  have hBc : HasCompactSupport (boxSpline 1 3) := hasCompactSupport_boxSpline 3
  have him : ∀ ρ : Z.carrier, |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := by
    intro ρ
    have hstrip := Z.strip ρ.1 ρ.2
    rw [im_gammaOf, abs_le]
    constructor <;> linarith only [hstrip.1, hstrip.2]
  -- the coefficients, weighted by the frequency, are dominated by the tempered sum
  have hcoef : ∀ ρ : Z.carrier,
      ‖(Z.mult ρ : ℂ) * paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3)) (gammaOf ρ)‖ *
        ‖gammaOf (ρ : ℂ)‖ ≤
      (2 ^ 4 * Real.exp 2) ^ 2 * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
    intro ρ
    have him' : |(conj (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
      rw [Complex.conj_im, abs_neg]
      exact him ρ
    have h1 : ‖paperFT (boxSpline 1 3) (gammaOf (ρ : ℂ))‖ ≤
        2 ^ 4 * Real.exp 2 / (1 + ‖gammaOf (ρ : ℂ)‖) ^ 4 :=
      (norm_paperFT_boxSpline_le' 3 (him ρ) (norm_nonneg _) le_rfl).trans
        (le_of_eq (by norm_num))
    have h2 : ‖paperFT (boxSpline 1 3) (conj (gammaOf (ρ : ℂ)))‖ ≤
        2 ^ 4 * Real.exp 2 / (1 + ‖gammaOf (ρ : ℂ)‖) ^ 4 :=
      (norm_paperFT_boxSpline_le' 3 him' (norm_nonneg (gammaOf (ρ : ℂ)))
        (Complex.norm_conj _).ge).trans (le_of_eq (by norm_num))
    have h3 := mul_mul_le_of_decay (norm_nonneg (gammaOf (ρ : ℂ)))
      (by positivity : (0 : ℝ) ≤ 2 ^ 4 * Real.exp 2) (norm_nonneg _) h1 h2
    rw [← Complex.normSq_eq_norm_sq] at h3
    rw [norm_mul, Complex.norm_natCast, EF.paperFT_weilTest hB hB hBc hBc, norm_mul,
      Complex.norm_conj]
    calc (Z.mult ρ : ℝ) * (‖paperFT (boxSpline 1 3) (gammaOf (ρ : ℂ))‖ *
          ‖paperFT (boxSpline 1 3) (conj (gammaOf (ρ : ℂ)))‖) * ‖gammaOf (ρ : ℂ)‖
        = (Z.mult ρ : ℝ) * (‖paperFT (boxSpline 1 3) (gammaOf (ρ : ℂ))‖ *
          ‖paperFT (boxSpline 1 3) (conj (gammaOf (ρ : ℂ)))‖ * ‖gammaOf (ρ : ℂ)‖) := by ring
      _ ≤ (Z.mult ρ : ℝ) * ((2 ^ 4 * Real.exp 2) ^ 2 / (1 + Complex.normSq (gammaOf ρ))) :=
          mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
      _ = (2 ^ 4 * Real.exp 2) ^ 2 * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
          ring
  have hD0 : 0 ≤ ∑' ρ : Z.carrier,
      (2 ^ 4 * Real.exp 2) ^ 2 * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) :=
    tsum_nonneg fun ρ => mul_nonneg (by positivity)
      (div_nonneg (Nat.cast_nonneg _) (by positivity [Complex.normSq_nonneg (gammaOf (ρ : ℂ))]))
  refine ⟨2 * ∑' ρ : Z.carrier,
    (2 ^ 4 * Real.exp 2) ^ 2 * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))),
    mul_nonneg (by norm_num) hD0, fun R v v' hv hv' => ?_⟩
  have hs := summable_lagStructure Z hZ (contDiff_boxSpline (r := 1) one_pos 2)
    (boxSpline_support (r := 1) one_pos 3) v
  have hs' := summable_lagStructure Z hZ (contDiff_boxSpline (r := 1) one_pos 2)
    (boxSpline_support (r := 1) one_pos 3) v'
  have hterm : ∀ ρ : Z.carrier,
      ‖(Z.mult ρ : ℂ) * paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3)) (gammaOf ρ) *
          cexp (I * gammaOf ρ * v) -
        (Z.mult ρ : ℂ) * paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3)) (gammaOf ρ) *
          cexp (I * gammaOf ρ * v')‖ ≤
      (2 ^ 4 * Real.exp 2) ^ 2 * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) *
        (Real.exp (R / 2) * |v - v'|) := by
    intro ρ
    rw [← mul_sub, norm_mul]
    have h1 := norm_cexp_I_mul_sub_le (him ρ) hv hv'
    calc ‖(Z.mult ρ : ℂ) * paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3)) (gammaOf ρ)‖ *
          ‖cexp (I * gammaOf ρ * v) - cexp (I * gammaOf ρ * v')‖
        ≤ ‖(Z.mult ρ : ℂ) * paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3)) (gammaOf ρ)‖ *
          (‖gammaOf (ρ : ℂ)‖ * Real.exp (R / 2) * |v - v'|) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖(Z.mult ρ : ℂ) * paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3)) (gammaOf ρ)‖ *
          ‖gammaOf (ρ : ℂ)‖ * (Real.exp (R / 2) * |v - v'|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hcoef ρ) (by positivity)
  have hnorm : ‖lagStructure Z (boxSpline 1 3) v - lagStructure Z (boxSpline 1 3) v'‖ ≤
      (∑' ρ : Z.carrier,
        (2 ^ 4 * Real.exp 2) ^ 2 * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)))) *
        (Real.exp (R / 2) * |v - v'|) := by
    rw [lagStructure, lagStructure, ← hs.tsum_sub hs', ← tsum_mul_right]
    exact tsum_of_norm_bounded ((hZ.mul_left _).mul_right _).hasSum hterm
  have hre : 2 * (lagStructure Z (boxSpline 1 3) v).re -
      2 * (lagStructure Z (boxSpline 1 3) v').re =
      2 * (lagStructure Z (boxSpline 1 3) v - lagStructure Z (boxSpline 1 3) v').re := by
    rw [Complex.sub_re]
    ring
  rw [hre, abs_mul, abs_two]
  have h4 := Complex.abs_re_le_norm
    (lagStructure Z (boxSpline 1 3) v - lagStructure Z (boxSpline 1 3) v')
  calc 2 * |(lagStructure Z (boxSpline 1 3) v - lagStructure Z (boxSpline 1 3) v').re|
      ≤ 2 * ((∑' ρ : Z.carrier,
        (2 ^ 4 * Real.exp 2) ^ 2 * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)))) *
        (Real.exp (R / 2) * |v - v'|)) := by linarith only [h4, hnorm]
    _ = _ := by ring

/-! ### A large value on a window is a large moment -/

/-- **A large value on a window is a large moment.** A continuous function with Lipschitz
constant `K` on the window `[T, T + L]` has, for every point `u₀` of the window,
`(|f u₀|/2)^{2k} min(|f u₀|/2K, L/2) ≤ ∫_T^{T+L} f^{2k}`. -/
theorem pow_mul_min_le_integral_pow {f : ℝ → ℝ} (hf : Continuous f) {T L K : ℝ} (hL : 0 < L)
    (hK : 0 < K)
    (hlip : ∀ u ∈ Icc T (T + L), ∀ v ∈ Icc T (T + L), |f u - f v| ≤ K * |u - v|) {u₀ : ℝ}
    (hu₀ : u₀ ∈ Icc T (T + L)) (k : ℕ) :
    (|f u₀| / 2) ^ (2 * k) * min (|f u₀| / (2 * K)) (L / 2) ≤
      ∫ u in T..(T + L), f u ^ (2 * k) := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = |f u₀| := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = min (M / (2 * K)) (L / 2) := ⟨_, rfl⟩
  rw [← hM, ← hℓ]
  have hM0 : 0 ≤ M := hM ▸ abs_nonneg _
  have hℓ0 : 0 ≤ ℓ := hℓ ▸ le_min (by positivity) (by positivity)
  have hℓL : ℓ ≤ L / 2 := hℓ ▸ min_le_right _ _
  have hℓM : K * ℓ ≤ M / 2 := by
    have h1 : ℓ ≤ M / (2 * K) := hℓ ▸ min_le_left _ _
    calc K * ℓ ≤ K * (M / (2 * K)) := mul_le_mul_of_nonneg_left h1 hK.le
      _ = M / 2 := by field_simp
  -- a subinterval of length `ℓ` of the window that contains `u₀`
  obtain ⟨a, haT, haL, hau, hua⟩ : ∃ a : ℝ, T ≤ a ∧ a + ℓ ≤ T + L ∧ a ≤ u₀ ∧ u₀ ≤ a + ℓ := by
    by_cases h : u₀ + ℓ ≤ T + L
    · exact ⟨u₀, hu₀.1, h, le_rfl, by linarith only [hℓ0]⟩
    · exact ⟨u₀ - ℓ, by linarith only [not_le.mp h, hℓL], by linarith only [hu₀.2],
        by linarith only [hℓ0], by linarith only⟩
  have hlow : ∀ u ∈ Icc a (a + ℓ), (M / 2) ^ (2 * k) ≤ f u ^ (2 * k) := by
    intro u hu
    have h1 := hlip u ⟨haT.trans hu.1, hu.2.trans haL⟩ u₀ hu₀
    have h2 : |u - u₀| ≤ ℓ := by
      rw [abs_le]
      constructor <;> linarith only [hu.1, hu.2, hau, hua]
    have h4 : K * |u - u₀| ≤ M / 2 := (mul_le_mul_of_nonneg_left h2 hK.le).trans hℓM
    have h5 : |f u₀| - |f u| ≤ |f u - f u₀| := by
      rw [abs_sub_comm (f u) (f u₀)]
      exact abs_sub_abs_le_abs_sub _ _
    have h3 : M / 2 ≤ |f u| := by linarith only [h1, h4, h5, hM]
    calc (M / 2) ^ (2 * k) ≤ |f u| ^ (2 * k) := pow_le_pow_left₀ (by positivity) h3 _
      _ = f u ^ (2 * k) := (even_two_mul k).pow_abs (f u)
  have hnn : ∀ u, 0 ≤ f u ^ (2 * k) := fun u => (even_two_mul k).pow_nonneg (f u)
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u => f u ^ (2 * k)) volume a b := fun a b =>
    (hf.pow _).intervalIntegrable a b
  calc (M / 2) ^ (2 * k) * ℓ = ∫ _u in a..(a + ℓ), (M / 2) ^ (2 * k) := by
        rw [intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul, mul_comm ℓ]
    _ ≤ ∫ u in a..(a + ℓ), f u ^ (2 * k) :=
        intervalIntegral.integral_mono_on (by linarith only [hℓ0]) intervalIntegrable_const
          (hint _ _) hlow
    _ ≤ ∫ u in T..(T + L), f u ^ (2 * k) :=
        intervalIntegral.integral_mono_interval haT (by linarith only [hℓ0]) haL
          (Filter.Eventually.of_forall hnn) (hint _ _)

/-- The arithmetic of the two cases: the short interval of largeness, and the half window. -/
theorem mul_le_of_pow_mul_min_le {X M K L W B P : ℝ} (hX : 0 ≤ X) (hM : 0 ≤ M) (hK : 0 < K)
    (hL : 0 < L) (hW : 0 ≤ W) (hB : M ≤ B) (hP : 0 < P)
    (h : X / P * min (M / (2 * K)) (L / 2) ≤ W) : X * M ≤ 2 * P * W * (K + B / L) := by
  have hB0 : 0 ≤ B := hM.trans hB
  rcases le_total (M / (2 * K)) (L / 2) with hc | hc
  · rw [min_eq_left hc] at h
    have h2 := mul_le_mul_of_nonneg_right h (by positivity : (0 : ℝ) ≤ 2 * P * K)
    have e : X / P * (M / (2 * K)) * (2 * P * K) = X * M := by field_simp
    rw [e] at h2
    have h3 : 0 ≤ 2 * P * W * (B / L) := by positivity
    have e2 : 2 * P * W * (K + B / L) = W * (2 * P * K) + 2 * P * W * (B / L) := by ring
    rw [e2]
    linarith only [h2, h3]
  · rw [min_eq_right hc] at h
    have h2 := mul_le_mul_of_nonneg_right h (by positivity : (0 : ℝ) ≤ 2 * P)
    have e : X / P * (L / 2) * (2 * P) = X * L := by field_simp
    rw [e] at h2
    have h1 : X ≤ W * (2 * P) / L := (le_div_iff₀ hL).mpr h2
    have h3 : X * M ≤ X * B := mul_le_mul_of_nonneg_left hB hX
    have h4 : X * B ≤ W * (2 * P) / L * B := mul_le_mul_of_nonneg_right h1 hB0
    have h5 : 0 ≤ 2 * P * W * K := by positivity
    have e2 : 2 * P * W * (K + B / L) = 2 * P * W * K + W * (2 * P) / L * B := by ring
    rw [e2]
    linarith only [h3, h4, h5]

/-! ### A moment bound is a pointwise bound -/

/-- Every exponent of a configuration has depth at most `½`. -/
theorem topDepth_half (Z : ZeroConfig) : TopDepth Z (1 / 2) := by
  intro z hz
  rcases mem_of_evenCoeff_ne_zero hz with h | h
  · have h1 := (Z.strip _ h).2
    have he : ((1 / 2 : ℂ) + z).re = 1 / 2 + z.re := by norm_num
    rw [he] at h1
    linarith only [h1]
  · have h1 := (Z.strip _ h).2
    have he : ((1 / 2 : ℂ) + conj z).re = 1 / 2 + z.re := by simp
    rw [he] at h1
    linarith only [h1]

/-- The trivial bound of the spline trace: `|2 Re S(u)| ≤ E e^{u/2}` for `u ≥ 0`. -/
theorem abs_two_re_lagStructure_le (hZ : TemperedConfig Z) {u : ℝ} (hu : 0 ≤ u) :
    |2 * (lagStructure Z (boxSpline 1 3) u).re| ≤
      (∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖) * Real.exp (u / 2) := by
  have h := abs_normTrace_le hZ (topDepth_half Z) hu
  unfold normTrace at h
  rw [abs_mul, abs_of_pos (Real.exp_pos _)] at h
  have he : Real.exp (-(1 / 2 * u)) * Real.exp (u / 2) = 1 := by
    rw [← Real.exp_add, show -(1 / 2 * u) + u / 2 = 0 by ring, Real.exp_zero]
  calc |2 * (lagStructure Z (boxSpline 1 3) u).re|
      = |2 * (lagStructure Z (boxSpline 1 3) u).re| * Real.exp (-(1 / 2 * u)) *
          Real.exp (u / 2) := by rw [mul_assoc, he, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

/-- **A moment bound is a pointwise bound.** For a tempered configuration and a window length
`L` there is a constant `G` such that, for every order `k`: if the `2k`-th moment of the spline
trace over `[T, T + L]`, `T ≥ 0`, is at most `C e^{AT}`, `A ≥ 0`, then at every point of the
window `|2 Re S|^{2k+1} ≤ 2^{2k+1} G C e^{(A+1)T}`. -/
theorem exists_abs_trace_pow_le_of_moment_le (hZ : TemperedConfig Z) {L : ℝ} (hL : 0 < L) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ (k : ℕ) (T C A : ℝ), 0 ≤ T → 0 ≤ A →
      (∫ u in T..(T + L), (2 * (lagStructure Z (boxSpline 1 3) u).re) ^ (2 * k)) ≤
        C * Real.exp (A * T) →
      ∀ u ∈ Icc T (T + L), |2 * (lagStructure Z (boxSpline 1 3) u).re| ^ (2 * k + 1) ≤
        2 ^ (2 * k + 1) * G * C * Real.exp ((A + 1) * T) := by
  obtain ⟨D, hD, hlip⟩ := exists_lipschitz_two_re_lagStructure hZ
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := hE ▸ tsum_nonneg fun _ => norm_nonneg _
  have hDE : 0 ≤ D + 1 + E / L := by
    have := div_nonneg hE0 hL.le
    linarith only [hD, this]
  refine ⟨(D + 1 + E / L) * Real.exp (L / 2), mul_nonneg hDE (Real.exp_pos _).le, ?_⟩
  intro k T C A hT hA hmom u hu
  have hKpos : 0 < (D + 1) * Real.exp ((T + L) / 2) :=
    mul_pos (by linarith only [hD]) (Real.exp_pos _)
  -- the Lipschitz constant on the window
  have hlipW : ∀ x ∈ Icc T (T + L), ∀ y ∈ Icc T (T + L),
      |2 * (lagStructure Z (boxSpline 1 3) x).re - 2 * (lagStructure Z (boxSpline 1 3) y).re| ≤
        (D + 1) * Real.exp ((T + L) / 2) * |x - y| := by
    intro x hx y hy
    have hxR : |x| ≤ T + L := by
      rw [abs_of_nonneg (hT.trans hx.1)]
      exact hx.2
    have hyR : |y| ≤ T + L := by
      rw [abs_of_nonneg (hT.trans hy.1)]
      exact hy.2
    have h1 := hlip (T + L) x y hxR hyR
    have h2 : 0 ≤ Real.exp ((T + L) / 2) * |x - y| :=
      mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
    have e : (D + 1) * Real.exp ((T + L) / 2) * |x - y| =
        D * Real.exp ((T + L) / 2) * |x - y| + Real.exp ((T + L) / 2) * |x - y| := by ring
    rw [e]
    linarith only [h1, h2]
  have hbern := pow_mul_min_le_integral_pow (continuous_two_re_lagStructure hZ) hL hKpos hlipW
    hu k
  -- the trivial bound on the window
  have htriv : |2 * (lagStructure Z (boxSpline 1 3) u).re| ≤ E * Real.exp ((T + L) / 2) := by
    rw [hE]
    exact (abs_two_re_lagStructure_le hZ (hT.trans hu.1)).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hu.2])) (hE ▸ hE0))
  have hint0 : 0 ≤ ∫ u in T..(T + L), (2 * (lagStructure Z (boxSpline 1 3) u).re) ^ (2 * k) :=
    intervalIntegral.integral_nonneg (by linarith only [hL]) fun x _ =>
      (even_two_mul k).pow_nonneg _
  have hW0 : 0 ≤ C * Real.exp (A * T) := hint0.trans hmom
  have hC0 : 0 ≤ C := by
    by_contra hneg
    have h1 := mul_neg_of_neg_of_pos (not_le.mp hneg) (Real.exp_pos (A * T))
    linarith only [h1, hW0]
  have hstep := mul_le_of_pow_mul_min_le
    (X := |2 * (lagStructure Z (boxSpline 1 3) u).re| ^ (2 * k))
    (P := 2 ^ (2 * k)) (by positivity) (abs_nonneg _) hKpos hL hW0 htriv (by positivity)
    (by rw [← div_pow]; exact hbern.trans hmom)
  have hstar : Real.exp ((T + L) / 2) * Real.exp (A * T) ≤
      Real.exp (L / 2) * Real.exp ((A + 1) * T) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have e : L / 2 + (A + 1) * T = (T + L) / 2 + A * T + T / 2 := by ring
    rw [e]
    linarith only [hT]
  have hfac : 0 ≤ 2 * 2 ^ (2 * k) * C * (D + 1 + E / L) :=
    mul_nonneg (mul_nonneg (by positivity) hC0) hDE
  rw [pow_succ, pow_succ]
  calc |2 * (lagStructure Z (boxSpline 1 3) u).re| ^ (2 * k) *
        |2 * (lagStructure Z (boxSpline 1 3) u).re|
      ≤ 2 * 2 ^ (2 * k) * (C * Real.exp (A * T)) *
          ((D + 1) * Real.exp ((T + L) / 2) + E * Real.exp ((T + L) / 2) / L) := hstep
    _ = 2 * 2 ^ (2 * k) * C * (D + 1 + E / L) *
          (Real.exp ((T + L) / 2) * Real.exp (A * T)) := by ring
    _ ≤ 2 * 2 ^ (2 * k) * C * (D + 1 + E / L) *
          (Real.exp (L / 2) * Real.exp ((A + 1) * T)) := mul_le_mul_of_nonneg_left hstar hfac
    _ = 2 ^ (2 * k) * 2 * ((D + 1 + E / L) * Real.exp (L / 2)) * C *
          Real.exp ((A + 1) * T) := by ring

/-! ### The two families of hypotheses -/

/-- Bounds for all even moments of the spline trace with one exponent, on arbitrarily late
windows of length `L`; the constants and the windows may depend on the order. -/
def WindowMomentsBounded (Z : ZeroConfig) (L : ℝ) : Prop :=
  ∃ A : ℝ, ∀ k : ℕ, ∃ C : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧
    (∫ u in T..(T + L), (2 * (lagStructure Z (boxSpline 1 3) u).re) ^ (2 * k)) ≤
      C * Real.exp (A * T)

/-- Bounds for all powers of the sup norm of the spline trace with one exponent, on arbitrarily
late windows of length `L`; the constants and the windows may depend on the power. -/
def WindowSupPowersBounded (Z : ZeroConfig) (L : ℝ) : Prop :=
  ∃ A : ℝ, ∀ n : ℕ, ∃ C : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧
    ∀ u ∈ Icc T (T + L), |2 * (lagStructure Z (boxSpline 1 3) u).re| ^ n ≤ C * Real.exp (A * T)

/-- **Moment bounds of all orders are sup bounds.** -/
theorem windowMomentsBounded_iff_windowSupPowersBounded (hZ : TemperedConfig Z) {L : ℝ}
    (hL : 0 < L) : WindowMomentsBounded Z L ↔ WindowSupPowersBounded Z L := by
  constructor
  · rintro ⟨A, hA⟩
    obtain ⟨G, hG, hpt⟩ := exists_abs_trace_pow_le_of_moment_le hZ hL
    refine ⟨max A 0 + 1, fun n => ?_⟩
    obtain ⟨C, hC⟩ := hA n
    refine ⟨1 + 2 ^ (2 * n + 1) * G * |C|, fun U => ?_⟩
    obtain ⟨T, hT, hmom⟩ := hC (max U 0)
    have hT0 : 0 ≤ T := (le_max_right U 0).trans hT
    refine ⟨T, (le_max_left U 0).trans hT, fun u hu => ?_⟩
    -- the moment bound with a nonnegative exponent and constant
    have hexp : Real.exp (A * T) ≤ Real.exp (max A 0 * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left A 0) hT0)
    have hmom' : (∫ u in T..(T + L), (2 * (lagStructure Z (boxSpline 1 3) u).re) ^ (2 * n)) ≤
        |C| * Real.exp (max A 0 * T) := by
      have h1 : C * Real.exp (A * T) ≤ |C| * Real.exp (A * T) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
      have h2 : |C| * Real.exp (A * T) ≤ |C| * Real.exp (max A 0 * T) :=
        mul_le_mul_of_nonneg_left hexp (abs_nonneg C)
      linarith only [hmom, h1, h2]
    have hpow := hpt n T |C| (max A 0) hT0 (le_max_right A 0) hmom' u hu
    have hge1 : 1 ≤ Real.exp ((max A 0 + 1) * T) :=
      Real.one_le_exp (mul_nonneg (by linarith only [le_max_right A 0]) hT0)
    -- a power is at most one plus a higher power
    have hlow : |2 * (lagStructure Z (boxSpline 1 3) u).re| ^ n ≤
        1 + |2 * (lagStructure Z (boxSpline 1 3) u).re| ^ (2 * n + 1) := by
      rcases le_total |2 * (lagStructure Z (boxSpline 1 3) u).re| 1 with h1 | h1
      · have h2 := pow_le_one₀ (n := n) (abs_nonneg _) h1
        have h3 : 0 ≤ |2 * (lagStructure Z (boxSpline 1 3) u).re| ^ (2 * n + 1) := by positivity
        linarith only [h2, h3]
      · have h2 := pow_le_pow_right₀ h1 (show n ≤ 2 * n + 1 by omega)
        linarith only [h2]
    have h4 : 0 ≤ 2 ^ (2 * n + 1) * G * |C| := by positivity
    have e : (1 + 2 ^ (2 * n + 1) * G * |C|) * Real.exp ((max A 0 + 1) * T) =
        Real.exp ((max A 0 + 1) * T) +
          2 ^ (2 * n + 1) * G * |C| * Real.exp ((max A 0 + 1) * T) := by ring
    rw [e]
    linarith only [hlow, hpow, hge1]
  · rintro ⟨A, hA⟩
    refine ⟨A, fun k => ?_⟩
    obtain ⟨C, hC⟩ := hA (2 * k)
    refine ⟨L * C, fun U => ?_⟩
    obtain ⟨T, hT, hsup⟩ := hC U
    refine ⟨T, hT, ?_⟩
    have hint : IntervalIntegrable
        (fun u => (2 * (lagStructure Z (boxSpline 1 3) u).re) ^ (2 * k)) volume T (T + L) :=
      ((continuous_two_re_lagStructure hZ).pow (2 * k)).intervalIntegrable T (T + L)
    have hmono : (∫ u in T..(T + L), (2 * (lagStructure Z (boxSpline 1 3) u).re) ^ (2 * k)) ≤
        ∫ _u in T..(T + L), C * Real.exp (A * T) :=
      intervalIntegral.integral_mono_on (by linarith only [hL]) hint
        (intervalIntegrable_const (μ := volume)) fun u hu => by
          have h1 := hsup u hu
          rwa [(even_two_mul k).pow_abs] at h1
    rw [intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul] at hmono
    linarith only [hmono, mul_assoc L C (Real.exp (A * T))]

/-- A two-sided bound `C_ε e^{εT}` for every `ε > 0`, on arbitrarily late windows, is a bound
for all powers of the sup norm with one exponent. -/
theorem windowSupPowersBounded_of_subexponential {L : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ u ∈ Icc T (T + L),
      |2 * (lagStructure Z (boxSpline 1 3) u).re| ≤ C * Real.exp (ε * T)) :
    WindowSupPowersBounded Z L := by
  refine ⟨1, fun n => ?_⟩
  obtain ⟨C, hC⟩ := h (1 / ((n : ℝ) + 1)) (by positivity)
  refine ⟨|C| ^ n, fun U => ?_⟩
  obtain ⟨T, hT, hsup⟩ := hC (max U 0)
  have hT0 : 0 ≤ T := (le_max_right U 0).trans hT
  refine ⟨T, (le_max_left U 0).trans hT, fun u hu => ?_⟩
  have h1 : |2 * (lagStructure Z (boxSpline 1 3) u).re| ≤
      |C| * Real.exp (1 / ((n : ℝ) + 1) * T) :=
    (hsup u hu).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 n
  rw [mul_pow, ← Real.exp_nat_mul] at h2
  have h3 : Real.exp ((n : ℝ) * (1 / ((n : ℝ) + 1) * T)) ≤ Real.exp (1 * T) := by
    refine Real.exp_le_exp.mpr ?_
    have h4 : (n : ℝ) * (1 / ((n : ℝ) + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]
      linarith only
    have h5 := mul_le_mul_of_nonneg_right h4 hT0
    linarith only [h5, mul_assoc (n : ℝ) (1 / ((n : ℝ) + 1)) T]
  exact h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))

/-- **Sup bounds of all powers give the abscissa law.** -/
theorem asymptoticAbscissaLaw_of_windowSupPowersBounded {L : ℝ} (hL : 0 < L)
    (h : WindowSupPowersBounded zetaZeroConfig L) : _root_.RHTower.AsymptoticAbscissaLaw := by
  obtain ⟨A, hA⟩ :=
    (windowMomentsBounded_iff_windowSupPowersBounded temperedConfig_zetaZeroConfig hL).mpr h
  exact asymptoticAbscissaLaw_of_window_moments ⟨L, hL, A, fun k _ => hA k⟩

end GaloisForLFunctions.FloorFreeArithmetic
