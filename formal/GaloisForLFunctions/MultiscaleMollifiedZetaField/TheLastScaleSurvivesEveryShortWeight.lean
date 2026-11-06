import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheLastScaleSetsTheDefect

/-!
# The last scale survives every short weight

Let `Ψ` be a normalized mollifier of length `y` and `W = Σ_{m≤z} w_m m^{−s}` a short Dirichlet polynomial with
`w_1 = 1`, `|w_m| ≤ 1`, `yz ≤ V^θ`, `z ≤ V^{(½−θ)/4}`. On `Re s = σ = ½ + a/L`, `L = log V`,

`∫_V^{2V} |ζΨ − 1|² |W|² dt ≥ c (e^{−2θa}/a) V Σ_{m≤z} |c_m|² m^{−2σ}`, `c = 1 ⋆ b ⋆ w`,

uniformly in `Ψ`, `W` (`exists_eventually_weighted_shiftedDefect_ge`). The right side is `≥ c (e^{−2θa}/a) V`. If `Ψ`
cancels the prefix up to `z`, then `c_m = w_m`, the sum is the mean square of `W`, and the average of
`|ζΨ − 1|²` against the probability density `|W|²/∫|W|²` stays above the floor
(`exists_eventually_weighted_shiftedDefect_ge_of_prefix`).

**Why this is the barrier statement.** Barrier events are read through short Dirichlet polynomials in the small
primes: `|W|²` is the proxy of the indicator. No such proxy lowers the last-scale defect.

**Mechanism.** `(ζΨ − 1)W = ζ(ΨW) − W`. For a prime `p` above `yz`, `c_{pm} = c_m`: the block primes copy the whole
low-frequency profile of `ΨW` to `pm`, where `W` has no coefficient to cancel it. The energy of `ζΨW` therefore
gains the factor `1 + Σ_p p^{−2σ}`, and everything below the block cancels against `W` as a perfect square
`Σ_{m≤z} |c_m − w_m|² m^{−2σ} ≥ 0`.

**Tools.** The Gaussian floor at any positive energy (`gaussFloor_of_pos`, `gaussFloor_of_norm_le`), since the
convolution `b ⋆ w` is not bounded by one; the twisted first moment against a polynomial
(`norm_integral_zeta_poly_conj_sub_le`); the mean value theorem from below (`integral_normSq_edPoly_ge`).
-/

noncomputable section

open Complex MeasureTheory Set Filter
open RHTower

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-! ### The Gaussian floor at any positive energy -/

/-- The closing algebra of one window: from `K(D−ε) ≤ P ≤ √(K(D+ε)X)` get `X ≥ K(D−3ε)`. -/
theorem window_algebra_of_pos {K D ε P X : ℝ} (hK : 0 < K) (hD : 0 < D) (hε : 0 ≤ ε)
    (hε1 : 2 * ε ≤ D) (hP : K * (D - ε) ≤ P) (hPX : P ≤ Real.sqrt (K * (D + ε) * X))
    (hX : 0 ≤ X) : K * (D - 3 * ε) ≤ X := by
  have hDε : 0 ≤ D - ε := by linarith
  have h0 : 0 ≤ K * (D - ε) := mul_nonneg hK.le hDε
  have hsq : (K * (D - ε)) ^ 2 ≤ K * (D + ε) * X :=
    (Real.le_sqrt h0 (by positivity)).mp (hP.trans hPX)
  have h1 : K * (D - ε) ^ 2 ≤ (D + ε) * X := by
    have : K * (K * (D - ε) ^ 2) ≤ K * ((D + ε) * X) := by nlinarith
    exact le_of_mul_le_mul_left this hK
  have h2 : (D - 3 * ε) * (D + ε) ≤ (D - ε) ^ 2 := by nlinarith
  have h3 : K * (D - 3 * ε) * (D + ε) ≤ X * (D + ε) := by nlinarith
  exact le_of_mul_le_mul_right h3 (by linarith)

/-- **One Gaussian window, at any energy.** If the pairing and mean-value errors are at most `ε`
(relative to the window mass) and `2ε ≤ D`, then `∫_{τ−R}^{τ+R} |ζΨ|² w_τ ≥ √(πH²/2)(D − 3ε)`. -/
theorem gaussFloor_window_of_pos {σ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1) {y M : ℕ} (hM : 1 ≤ M)
    {b : ℕ → ℂ} (hb : ∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1) {T H R τ ε : ℝ} (hT : 4 ≤ T) (hH : 0 < H)
    (hHM : 24 * (M : ℝ) ≤ H ^ 2) (hR : 0 ≤ R) (hτ1 : T ≤ τ - R) (hτ2 : τ + R ≤ 2 * T)
    (hD1 : 0 < ∑ n ∈ Finset.Icc 1 M, ‖mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * σ))
    (hε0 : 0 ≤ ε) (hε : 2 * ε ≤ ∑ n ∈ Finset.Icc 1 M, ‖mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * σ))
    (hE1 : (y : ℝ) ^ 2 * M * (27 * Real.sqrt T * M * Real.exp (1 - R ^ 2 / H ^ 2) +
      2 * M * gaussTwistError H R M) ≤ Real.sqrt (Real.pi * H ^ 2 / 2) * ε)
    (hE2 : (∑ n ∈ Finset.Icc 1 M, ‖mollifiedZetaCoeff b y n‖ * (n : ℝ) ^ (-σ)) ^ 2 *
      Real.exp (-(H ^ 2 / (8 * (M : ℝ) ^ 2))) ≤ ε) :
    Real.sqrt (Real.pi * H ^ 2 / 2) *
        ((∑ n ∈ Finset.Icc 1 M, ‖mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) - 3 * ε) ≤
      ∫ t in (τ - R)..(τ + R), ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 *
        Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) := by
  set c : ℕ → ℂ := mollifiedZetaCoeff b y with hc
  set K : ℝ := Real.sqrt (Real.pi * H ^ 2 / 2) with hK
  set D : ℝ := ∑ n ∈ Finset.Icc 1 M, ‖c n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) with hDdef
  set w : ℝ → ℝ := fun t => Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) with hw
  have hK0 : 0 < K := Real.sqrt_pos.mpr (by positivity)
  have hs : ∀ n ∈ Finset.Icc 1 M, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hsy : ∀ n ∈ Finset.Icc 1 y, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hline : ∀ t : ℝ, ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro t h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hZc : Continuous fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    exact (ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I)
      (differentiableAt_riemannZeta (hline t)).continuousAt (by fun_prop)).mul
      (((differentiable_edPoly b hsy).continuous.comp (by fun_prop)).continuousAt)
  have hQc : Continuous fun t : ℝ => edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I) :=
    (differentiable_edPoly c hs).continuous.comp (by fun_prop)
  have hwc : Continuous w := by simp only [hw]; fun_prop
  have hw0 : ∀ t, 0 ≤ w t := fun t => (Real.exp_pos _).le
  have hsqw : ∀ t, Real.sqrt (w t) ^ 2 = w t := fun t => Real.sq_sqrt (hw0 t)
  set f : ℝ → ℂ := fun t => edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I) *
    ((Real.sqrt (w t) : ℝ) : ℂ) with hf
  set g : ℝ → ℂ := fun t => riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
    edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I) * ((Real.sqrt (w t) : ℝ) : ℂ) with hg
  have hfc : Continuous f := hQc.mul (Complex.continuous_ofReal.comp (hwc.sqrt))
  have hgc : Continuous g := hZc.mul (Complex.continuous_ofReal.comp (hwc.sqrt))
  have hnf : ∀ t, ‖f t‖ ^ 2 = ‖edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 * w t := by
    intro t
    simp only [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, hsqw]
  have hng : ∀ t, ‖g t‖ ^ 2 = ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 * w t := by
    intro t
    simp only [hg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, hsqw]
  -- the mean value on the window
  have hMVT := integral_normSq_edPoly_gauss_le c hM σ τ hH
  have hfS : ∫ t in (τ - R)..(τ + R), ‖f t‖ ^ 2 ≤ K * (D + ε) := by
    simp only [hnf]
    have hint : Integrable fun t : ℝ => ‖edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 * w t := by
      have hb2 : Integrable w := by
        simp only [hw]
        exact (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 2 / H ^ 2)).comp_sub_right τ
      obtain ⟨C, hC⟩ : ∃ C, ∀ t : ℝ, ‖edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ C := by
        refine ⟨(∑ n ∈ Finset.Icc 1 M, ‖c n‖ * (n : ℝ) ^ (-σ)) ^ 2, fun t => ?_⟩
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        unfold edPoly
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
        rw [norm_mul, norm_ofReal_natCast_cpow (hs n hn)]
        simp
      refine (hb2.const_mul C).mono' ((hQc.norm.pow 2).mul hwc).aestronglyMeasurable
        (Filter.Eventually.of_forall fun t => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hw0 t))]
      exact mul_le_mul_of_nonneg_right (hC t) (hw0 t)
    calc ∫ t in (τ - R)..(τ + R), ‖edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 * w t
        ≤ ∫ t : ℝ, ‖edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 * w t := by
          rw [intervalIntegral.integral_of_le (by linarith)]
          exact setIntegral_le_integral hint (Filter.Eventually.of_forall fun t => by
            have := hw0 t; positivity)
      _ ≤ K * (D + (∑ n ∈ Finset.Icc 1 M, ‖c n‖ * (n : ℝ) ^ (-σ)) ^ 2 *
            Real.exp (-(H ^ 2 / (8 * (M : ℝ) ^ 2)))) := hMVT
      _ ≤ K * (D + ε) := by gcongr
  -- Cauchy–Schwarz
  have hSA : 0 < K * (D + ε) := by
    have : 0 < D + ε := by linarith
    positivity
  have hcs := GaloisForLFunctions.HTGeometry.integral_norm_mul_le_sqrt_of_bound
    (A := τ - R) (B := τ + R) (by linarith) hfc hgc hSA hfS
  have hgS : ∫ t in (τ - R)..(τ + R), ‖g t‖ ^ 2 =
      ∫ t in (τ - R)..(τ + R), ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 * w t := by
    simp only [hng]
  rw [hgS] at hcs
  -- the pairing
  have hpair := norm_window_pairing_sub_le hσ hσ1 hM hb hT hH hHM hR hτ1 hτ2
  rw [← hc, ← hDdef] at hpair
  have hP : K * (D - ε) ≤ ∫ t in (τ - R)..(τ + R), ‖f t‖ * ‖g t‖ := by
    have h1 : ‖((K * D : ℝ) : ℂ)‖ - K * ε ≤
        ‖∫ t in (τ - R)..(τ + R), riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I) *
          (starRingEnd ℂ) (edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)) *
          ((Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) : ℝ) : ℂ)‖ := by
      have := norm_sub_norm_le ((K * D : ℝ) : ℂ) (∫ t in (τ - R)..(τ + R),
        riemannZeta ((σ : ℂ) + (t : ℂ) * I) * edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I) *
          (starRingEnd ℂ) (edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)) *
          ((Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) : ℝ) : ℂ))
      rw [norm_sub_rev] at this
      linarith
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
    have h2 : K * (D - ε) = K * D - K * ε := by ring
    rw [h2]
    refine h1.trans ?_
    refine (intervalIntegral.norm_integral_le_integral_norm (by linarith)).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hf, hg, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.abs_exp]
    have hwt : Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) = Real.sqrt (w t) * Real.sqrt (w t) :=
      (Real.mul_self_sqrt (hw0 t)).symm
    rw [hwt]
    ring
  have hX0 : 0 ≤ ∫ t in (τ - R)..(τ + R), ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 * w t :=
    intervalIntegral.integral_nonneg (by linarith) fun t _ => by have := hw0 t; positivity
  exact window_algebra_of_pos hK0 hD1 hε0 hε hP hcs hX0

/-- The Gaussian floor on `Re s = 1/2 + a/L` for any positive lower bound `D₀` on the truncated
energy, at unit coefficient bound. -/
theorem gaussFloor_of_pos {a θ₁ L D₀ δ : ℝ}
    (ha : 0 ≤ a) (hθ₁0 : 0 < θ₁) (hθ₁1 : θ₁ < 1) (hD₀ : 0 < D₀) (hδ : 0 < δ) (hδD : δ ≤ D₀)
    (hLa : 2 * a + 3 ≤ L) (hδL8 : 8 ≤ (1 - θ₁) / 4 * L)
    (hδLc : 32 / (δ / D₀) ≤ (1 - θ₁) / 4 * L)
    (hsup : 99 * (Real.exp (5 * L) * Real.exp (-(1 / 128 * Real.exp ((1 - θ₁) / 2 * L)))) ≤ δ / 6)
    {y : ℕ} (hy : 1 ≤ y) (hyle : (y : ℝ) ≤ Real.exp (θ₁ * L)) {b : ℕ → ℂ}
    (hb : ∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1)
    (hD_ge : D₀ ≤ ∑ n ∈ Finset.Icc 1 ⌊Real.exp ((θ₁ + (1 - θ₁) / 4) * L)⌋₊,
      ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + a / L))) :
    (D₀ - δ) * Real.exp L ≤
      ∫ t in (Real.exp L)..(2 * Real.exp L),
        ‖riemannZeta (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hL0 : 0 < L := by linarith
  set M : ℕ := ⌊Real.exp ((θ₁ + (1 - θ₁) / 4) * L)⌋₊
  have hMle : (M : ℝ) ≤ Real.exp ((θ₁ + (1 - θ₁) / 4) * L) := Nat.floor_le (by positivity)
  have hMgt : Real.exp ((θ₁ + (1 - θ₁) / 4) * L) - 1 < M := by
    have := Nat.lt_floor_add_one (Real.exp ((θ₁ + (1 - θ₁) / 4) * L)); linarith
  have hc0 : 0 < δ / D₀ := by positivity
  obtain ⟨hM2, _, _, hHM, h2R⟩ :=
    RHTower.gaussFloor_scale hθ₁0 hc0 hL0 hδL8 hδLc hyle hMle hMgt
  have hσ12 : 1 / 2 ≤ 1 / 2 + a / L := by
    have : 0 ≤ a / L := div_nonneg ha hL0.le; linarith
  have hσ1 : 1 / 2 + a / L < 1 := by
    have : a / L < 1 / 2 := by rw [div_lt_iff₀ hL0]; linarith
    linarith
  obtain ⟨hE1, hE2⟩ := RHTower.gaussFloor_error_bounds (σ := 1 / 2 + a / L) hθ₁0.le hθ₁1 hL0.le
    hy hyle (by omega : 1 ≤ M) hMle hsup hb (by linarith)
  set H : ℝ := Real.exp ((θ₁ + (1 - θ₁) / 2) * L)
  set R : ℝ := Real.exp ((θ₁ + 3 * (1 - θ₁) / 4) * L)
  have hR0 : 0 < R := Real.exp_pos _
  have hH0 : 0 < H := Real.exp_pos _
  have hT4 : 4 ≤ Real.exp L := by have := Real.add_one_le_exp L; linarith
  have hδD_le1 : δ / D₀ ≤ 1 := (div_le_one hD₀).mpr hδD
  have h2R_le : 32 * R ≤ Real.exp L :=
    h2R.trans (mul_le_of_le_one_left (Real.exp_pos _).le hδD_le1)
  have hRT : Real.exp L + R ≤ 2 * Real.exp L - R := by linarith
  have hZc := RHTower.continuous_normSq_zetaMollified_line (σ := 1 / 2 + a / L) (by linarith) b y
  set Z : ℝ → ℝ := fun t => ‖riemannZeta (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I) *
    RHTower.edPoly b (Finset.Icc 1 y) (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 with hZ
  have hZ0 : ∀ t, 0 ≤ Z t := fun t => by simp only [hZ]; positivity
  set D : ℝ := ∑ n ∈ Finset.Icc 1 M, ‖RHTower.mollifiedZetaCoeff b y n‖ ^ 2 *
    (n : ℝ) ^ (-2 * (1 / 2 + a / L)) with hDdef
  have hwin : ∀ τ ∈ Icc (Real.exp L + R) (2 * Real.exp L - R),
      Real.sqrt (Real.pi * H ^ 2 / 2) * (D - 3 * (δ / 6)) ≤
        ∫ t in (Real.exp L)..(2 * Real.exp L), Z t * Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) := by
    intro τ hτ
    have hτ1 : Real.exp L ≤ τ - R := by linarith [hτ.1]
    have hτ2 : τ + R ≤ 2 * Real.exp L := by linarith [hτ.2]
    have h1 := gaussFloor_window_of_pos hσ12 hσ1 (by omega : 1 ≤ M) hb hT4 hH0 hHM hR0.le hτ1 hτ2
      (lt_of_lt_of_le hD₀ hD_ge) (by positivity) (by linarith) hE1 hE2
    refine h1.trans ?_
    have hcont : Continuous fun t => Z t * Real.exp (-(2 / H ^ 2) * (t - τ) ^ 2) :=
      hZc.mul (by fun_prop)
    exact intervalIntegral.integral_mono_interval hτ1 (by linarith) hτ2
      (Filter.Eventually.of_forall fun t => mul_nonneg (hZ0 t) (Real.exp_pos _).le)
      (hcont.intervalIntegrable _ _)
  have hfub := RHTower.integral_ge_of_gaussian_windows hZc hZ0 hH0 hRT hR0.le hwin
  have hTR2 : 0 ≤ Real.exp L - 2 * R := by linarith
  have hRD : 2 * R * D₀ ≤ (δ / 16) * Real.exp L := by
    have h1 : 32 * R * D₀ ≤ δ * Real.exp L := by
      have hm := mul_le_mul_of_nonneg_right h2R (by linarith : (0 : ℝ) ≤ D₀)
      have heq : δ / D₀ * Real.exp L * D₀ = δ * Real.exp L := by
        have hD₀_ne : D₀ ≠ 0 := by linarith
        field_simp
      linarith
    linarith
  have halg : (D₀ - δ) * Real.exp L ≤ (Real.exp L - 2 * R) * (D - 3 * (δ / 6)) := by
    have hDsub : D₀ - δ / 2 ≤ D - 3 * (δ / 6) := by linarith
    calc (D₀ - δ) * Real.exp L
        ≤ (Real.exp L - 2 * R) * (D₀ - δ / 2) := by
          have : 0 ≤ R * δ := by positivity
          have : 0 ≤ δ * Real.exp L := by positivity
          nlinarith
      _ ≤ (Real.exp L - 2 * R) * (D - 3 * (δ / 6)) :=
          mul_le_mul_of_nonneg_left hDsub hTR2
  exact halg.trans hfub

/-- The Gaussian floor with coefficient bound `A`, by homogeneity. -/
theorem gaussFloor_of_norm_le {a θ₁ L D₀ δ A : ℝ} (ha : 0 ≤ a) (hθ₁0 : 0 < θ₁) (hθ₁1 : θ₁ < 1)
    (hD₀ : 0 < D₀) (hδ : 0 < δ) (hδD : δ ≤ D₀) (hLa : 2 * a + 3 ≤ L)
    (hδL8 : 8 ≤ (1 - θ₁) / 4 * L) (hδLc : 32 / (δ / D₀) ≤ (1 - θ₁) / 4 * L) (hA : 0 < A)
    (hsup : 99 * (Real.exp (5 * L) * Real.exp (-(1 / 128 * Real.exp ((1 - θ₁) / 2 * L)))) ≤
      δ / A ^ 2 / 6)
    {y : ℕ} (hy : 1 ≤ y) (hyle : (y : ℝ) ≤ Real.exp (θ₁ * L)) {β : ℕ → ℂ}
    (hβ : ∀ d ∈ Finset.Icc 1 y, ‖β d‖ ≤ A)
    (hD_ge : D₀ ≤ ∑ n ∈ Finset.Icc 1 ⌊Real.exp ((θ₁ + (1 - θ₁) / 4) * L)⌋₊,
      ‖mollifiedZetaCoeff β y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + a / L))) :
    (D₀ - δ) * Real.exp L ≤
      ∫ t in (Real.exp L)..(2 * Real.exp L),
        ‖riemannZeta (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly β (Finset.Icc 1 y) (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hA2 : 0 < A ^ 2 := by positivity
  have hAc : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  set b : ℕ → ℂ := fun d => β d / (A : ℂ) with hbdef
  have hb : ∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1 := by
    intro d hd
    simp only [hbdef]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA, div_le_one hA]
    exact hβ d hd
  have hc : ∀ n, mollifiedZetaCoeff b y n = mollifiedZetaCoeff β y n / (A : ℂ) := by
    intro n
    unfold mollifiedZetaCoeff
    rw [Finset.sum_div]
  have hp : ∀ s, edPoly b (Finset.Icc 1 y) s = edPoly β (Finset.Icc 1 y) s / (A : ℂ) := by
    intro s
    unfold edPoly
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hbdef]
    ring
  have hratio : δ / A ^ 2 / (D₀ / A ^ 2) = δ / D₀ := by
    field_simp
  have hnc : ∀ n, ‖mollifiedZetaCoeff b y n‖ ^ 2 = ‖mollifiedZetaCoeff β y n‖ ^ 2 / A ^ 2 := by
    intro n
    rw [hc, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA, div_pow]
  have hD' : D₀ / A ^ 2 ≤ ∑ n ∈ Finset.Icc 1 ⌊Real.exp ((θ₁ + (1 - θ₁) / 4) * L)⌋₊,
      ‖mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + a / L)) := by
    have e : ∑ n ∈ Finset.Icc 1 ⌊Real.exp ((θ₁ + (1 - θ₁) / 4) * L)⌋₊,
        ‖mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + a / L)) =
        (∑ n ∈ Finset.Icc 1 ⌊Real.exp ((θ₁ + (1 - θ₁) / 4) * L)⌋₊,
          ‖mollifiedZetaCoeff β y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + a / L))) / A ^ 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hnc]
      ring
    rw [e]
    exact div_le_div_of_nonneg_right hD_ge hA2.le
  have hfloor := gaussFloor_of_pos (a := a) (θ₁ := θ₁) (L := L) (D₀ := D₀ / A ^ 2) (δ := δ / A ^ 2)
    ha hθ₁0 hθ₁1 (by positivity) (by positivity) (div_le_div_of_nonneg_right hδD hA2.le) hLa hδL8
    (by rw [hratio]; exact hδLc) hsup hy hyle hb hD'
  have hint : (∫ t in (Real.exp L)..(2 * Real.exp L),
        ‖riemannZeta (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 y) (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) =
      (∫ t in (Real.exp L)..(2 * Real.exp L),
        ‖riemannZeta (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly β (Finset.Icc 1 y) (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) / A ^ 2 := by
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [hp, ← mul_div_assoc, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA, div_pow]
  rw [hint] at hfloor
  have e2 : (D₀ / A ^ 2 - δ / A ^ 2) * Real.exp L = ((D₀ - δ) * Real.exp L) / A ^ 2 := by ring
  rw [e2, div_le_div_iff_of_pos_right hA2] at hfloor
  exact hfloor

/-! ### The product polynomial -/

/-- The Dirichlet convolution of two finite coefficient sequences. -/
def polyConv (b w : ℕ → ℂ) (y z n : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 y, ∑ m ∈ Finset.Icc 1 z, if d * m = n then b d * w m else 0

theorem mul_mem_Icc {d m y z : ℕ} (hd : d ∈ Finset.Icc 1 y) (hm : m ∈ Finset.Icc 1 z) :
    d * m ∈ Finset.Icc 1 (y * z) := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hd
  obtain ⟨h3, h4⟩ := Finset.mem_Icc.mp hm
  exact Finset.mem_Icc.mpr ⟨Nat.mul_pos h1 h3, Nat.mul_le_mul h2 h4⟩

theorem sum_polyConv_mul (b w : ℕ → ℂ) (y z : ℕ) (g : ℕ → ℂ) :
    ∑ n ∈ Finset.Icc 1 (y * z), polyConv b w y z n * g n =
      ∑ d ∈ Finset.Icc 1 y, ∑ m ∈ Finset.Icc 1 z, b d * w m * g (d * m) := by
  classical
  unfold polyConv
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.sum_eq_single (d * m)]
  · simp
  · intro n _ hne
    rw [if_neg (Ne.symm hne)]
    simp
  · intro hnot
    exact absurd (mul_mem_Icc hd hm) hnot

/-- `Ψ W` is the polynomial of the convolution. -/
theorem edPoly_polyConv (b w : ℕ → ℂ) (y z : ℕ) (s : ℂ) :
    edPoly (polyConv b w y z) (Finset.Icc 1 (y * z)) s =
      edPoly b (Finset.Icc 1 y) s * edPoly w (Finset.Icc 1 z) s := by
  unfold edPoly
  rw [sum_polyConv_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun m _ => ?_
  have e : (((d * m : ℕ) : ℝ) : ℂ) ^ (-s) = ((d : ℝ) : ℂ) ^ (-s) * ((m : ℝ) : ℂ) ^ (-s) := by
    simp only [Nat.cast_mul, Complex.ofReal_mul, Complex.ofReal_natCast]
    exact Complex.natCast_mul_natCast_cpow d m (-s)
  rw [e]
  ring

theorem polyConv_one {b w : ℕ → ℂ} {y z : ℕ} (hy : 1 ≤ y) (hz : 1 ≤ z) :
    polyConv b w y z 1 = b 1 * w 1 := by
  classical
  unfold polyConv
  rw [Finset.sum_eq_single 1, Finset.sum_eq_single 1]
  · simp
  · intro m _ hm
    rw [if_neg]
    simpa using hm
  · intro h
    exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hz⟩) h
  · intro d _ hd
    refine Finset.sum_eq_zero fun m _ => if_neg fun h => hd ?_
    exact Nat.dvd_one.mp ⟨m, h.symm⟩
  · intro h
    exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hy⟩) h

theorem norm_polyConv_le_of_ite {b w : ℕ → ℂ} {y z : ℕ} (hb : ∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1)
    (hw : ∀ m ∈ Finset.Icc 1 z, ‖w m‖ ≤ 1) (n : ℕ) :
    ‖polyConv b w y z n‖ ≤
      ∑ d ∈ Finset.Icc 1 y, ∑ m ∈ Finset.Icc 1 z, if d * m = n then (1 : ℝ) else 0 := by
  unfold polyConv
  refine norm_sum_le_of_le _ fun d hd => norm_sum_le_of_le _ fun m hm => ?_
  split_ifs
  · rw [norm_mul]
    exact mul_le_one₀ (hb d hd) (norm_nonneg _) (hw m hm)
  · simp

theorem norm_polyConv_le {b w : ℕ → ℂ} {y z : ℕ} (hb : ∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1)
    (hw : ∀ m ∈ Finset.Icc 1 z, ‖w m‖ ≤ 1) (n : ℕ) :
    ‖polyConv b w y z n‖ ≤ (y : ℝ) * z := by
  refine (norm_polyConv_le_of_ite hb hw n).trans ?_
  calc _ ≤ ∑ _d ∈ Finset.Icc 1 y, ∑ _m ∈ Finset.Icc 1 z, (1 : ℝ) := by
        refine Finset.sum_le_sum fun d _ => Finset.sum_le_sum fun m _ => ?_
        split_ifs <;> norm_num
    _ = _ := by simp

theorem sum_norm_polyConv_le {b w : ℕ → ℂ} {y z : ℕ} (hb : ∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1)
    (hw : ∀ m ∈ Finset.Icc 1 z, ‖w m‖ ≤ 1) :
    ∑ n ∈ Finset.Icc 1 (y * z), ‖polyConv b w y z n‖ ≤ (y : ℝ) * z := by
  classical
  calc _ ≤ ∑ n ∈ Finset.Icc 1 (y * z), ∑ d ∈ Finset.Icc 1 y, ∑ m ∈ Finset.Icc 1 z,
          (if d * m = n then (1 : ℝ) else 0) :=
        Finset.sum_le_sum fun n _ => norm_polyConv_le_of_ite hb hw n
    _ = ∑ d ∈ Finset.Icc 1 y, ∑ m ∈ Finset.Icc 1 z, ∑ n ∈ Finset.Icc 1 (y * z),
          (if d * m = n then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ _d ∈ Finset.Icc 1 y, ∑ _m ∈ Finset.Icc 1 z, (1 : ℝ) := by
        refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun m hm => ?_
        rw [Finset.sum_ite_eq, if_pos (mul_mem_Icc hd hm)]
    _ = _ := by simp

/-- The coefficients of `ζΨW` are `(1 ⋆ b) ⋆ w`. -/
theorem mollifiedZetaCoeff_polyConv (b w : ℕ → ℂ) (y z n : ℕ) (hn : 1 ≤ n) :
    mollifiedZetaCoeff (polyConv b w y z) (y * z) n =
      ∑ m ∈ (Finset.Icc 1 z).filter (fun m => m ∣ n), w m * mollifiedZetaCoeff b y (n / m) := by
  classical
  have h1 : mollifiedZetaCoeff (polyConv b w y z) (y * z) n =
      ∑ e ∈ Finset.Icc 1 (y * z), polyConv b w y z e * (if e ∣ n then (1 : ℂ) else 0) := by
    unfold mollifiedZetaCoeff
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs <;> simp
  rw [h1, sum_polyConv_mul, Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  split_ifs with hmn
  · obtain ⟨k, rfl⟩ := hmn
    rw [Nat.mul_div_cancel_left k hm1]
    unfold mollifiedZetaCoeff
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hiff : d * m ∣ m * k ↔ d ∣ k := by
      rw [mul_comm d m]
      exact Nat.mul_dvd_mul_iff_left hm1
    by_cases hd : d ∣ k
    · rw [if_pos (hiff.mpr hd), if_pos hd]
      ring
    · rw [if_neg (fun h => hd (hiff.mp h)), if_neg hd]
      ring
  · refine Finset.sum_eq_zero fun d _ => ?_
    rw [if_neg (fun h => hmn (dvd_trans (dvd_mul_left m d) h))]
    ring

/-- A mollifier cancelling the prefix up to `z` reproduces the weight below `z`. -/
theorem mollifiedZetaCoeff_polyConv_of_prefix {b w : ℕ → ℂ} {y z : ℕ} (hy : 1 ≤ y) (hb1 : b 1 = 1)
    (hprefix : ∀ k ∈ Finset.Icc 2 z, mollifiedZetaCoeff b y k = 0) {n : ℕ}
    (hn : n ∈ Finset.Icc 1 z) :
    mollifiedZetaCoeff (polyConv b w y z) (y * z) n = w n := by
  classical
  obtain ⟨hn1, hnz⟩ := Finset.mem_Icc.mp hn
  rw [mollifiedZetaCoeff_polyConv b w y z n hn1, Finset.sum_eq_single n]
  · rw [Nat.div_self hn1, mollifiedZetaCoeff_one hy, hb1, mul_one]
  · intro m hm hne
    obtain ⟨hm', hmn⟩ := Finset.mem_filter.mp hm
    obtain ⟨hm1, hmz⟩ := Finset.mem_Icc.mp hm'
    obtain ⟨k, rfl⟩ := hmn
    rw [Nat.mul_div_cancel_left k hm1]
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp at hn1
      · exact h
    have hk2 : 2 ≤ k := by
      by_contra h
      have : k = 1 := by omega
      exact hne (by rw [this, mul_one])
    have hkz : k ≤ z := le_trans (Nat.le_mul_of_pos_left k hm1) hnz
    rw [hprefix k (Finset.mem_Icc.mpr ⟨hk2, hkz⟩), mul_zero]
  · intro h
    exact (h (Finset.mem_filter.mpr ⟨hn, dvd_refl n⟩)).elim

/-! ### The energy of the last scale above a weight -/

/-- Above the length of the polynomial, a prime copies the coefficient. -/
theorem mollifiedZetaCoeff_prime_mul {β : ℕ → ℂ} {Y p m : ℕ} (hp : p.Prime) (hYp : Y < p) :
    mollifiedZetaCoeff β Y (p * m) = mollifiedZetaCoeff β Y m := by
  unfold mollifiedZetaCoeff
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hd⟩
    have hc : Nat.Coprime d p := by
      have hnd : ¬ p ∣ d := fun h => by
        have := Nat.le_of_dvd (by omega) h
        omega
      exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd).symm
    exact ⟨⟨h1, h2⟩, hc.dvd_of_dvd_mul_left hd⟩
  · rintro ⟨h, hd⟩
    exact ⟨h, Dvd.dvd.mul_left hd p⟩

/-- **The block copies the whole low-frequency energy.** The primes of `(V^θ, V^{θ+1/a}]` multiply the energy
of `ζP` below `z` by `1 + c e^{−2θa}/a`, whatever the polynomial `P` of length `≤ V^θ` is. -/
theorem energy_ge_weighted_last_scale {θ a L : ℝ} (hθ : θ < 1 / 2) (ha : 4 ≤ a) (hL8 : 8 * a ≤ L)
    (hθL : 1 ≤ θ * L) (hCm : 12 * mertensError * a ≤ θ * L) {Y z : ℕ}
    (hYle : (Y : ℝ) ≤ Real.exp (θ * L)) (hzle : (z : ℝ) ≤ Real.exp (θ * L))
    (hzM : (z : ℝ) * Real.exp ((θ + 1 / a) * L) ≤ Real.exp ((3 / 4 + (1 - 3 / 4) / 4) * L))
    (β : ℕ → ℂ) :
    (∑ m ∈ Finset.Icc 1 z, ‖mollifiedZetaCoeff β Y m‖ ^ 2 * (m : ℝ) ^ (-2 * (1 / 2 + a / L))) *
        (1 + Real.exp (-2) * Real.exp (-(2 * θ * a)) * (1 / (6 * a))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp ((3 / 4 + (1 - 3 / 4) / 4) * L)⌋₊,
        ‖mollifiedZetaCoeff β Y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + a / L)) := by
  classical
  have ha1 : 1 ≤ a := by linarith
  have ha0 : 0 < a := by linarith
  have hL0 : 0 < L := by linarith
  obtain ⟨h1, h2, h3, h4, h5⟩ := last_scale_block_bounds ha1 hL8 hθL
  have hmass := sum_prime_inv_block_ge hθ ha1 hL8 hθL hCm
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ⌊Real.exp ((3 / 4 + (1 - 3 / 4) / 4) * L)⌋₊ := ⟨_, rfl⟩
  rw [← hM]
  have hMfloor : ∀ n : ℕ, (n : ℝ) ≤ Real.exp ((3 / 4 + (1 - 3 / 4) / 4) * L) → n ≤ M := by
    intro n hn
    rw [hM]
    exact Nat.le_floor hn
  generalize ⌈Real.exp (θ * L)⌉₊ = A at h1 h2 h5 hmass
  generalize ⌊Real.exp ((θ + 1 / a) * L)⌋₊ = B at h3 h4 h5 hmass
  obtain ⟨Pset, hPset⟩ : ∃ s : Finset ℕ, s = (Finset.Ioc A B).filter Nat.Prime := ⟨_, rfl⟩
  have hsum1 : ∑ p ∈ Pset, 1 / (p : ℝ) = Sieve.mertensS B - Sieve.mertensS A := by
    rw [hPset]
    exact ConjugateDiagonalGeometry.NearLineLogMean.sum_Ioc_prime_inv_eq_mertensS_sub' h5
  have hPmem : ∀ p ∈ Pset, p.Prime ∧ A < p ∧ p ≤ B := by
    intro p hp
    rw [hPset] at hp
    obtain ⟨hpIoc, hpp⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpA, hpB⟩ := Finset.mem_Ioc.mp hpIoc
    exact ⟨hpp, hpA, hpB⟩
  have hYA : Y ≤ A := by
    have : (Y : ℝ) ≤ A := hYle.trans h1
    exact_mod_cast this
  have hzA : z ≤ A := by
    have : (z : ℝ) ≤ A := hzle.trans h1
    exact_mod_cast this
  set σ : ℝ := 1 / 2 + a / L with hσ
  set c : ℕ → ℂ := mollifiedZetaCoeff β Y with hc
  set f : ℕ → ℝ := fun n => ‖c n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  set F : ℝ := ∑ m ∈ Finset.Icc 1 z, f m with hF
  have hF0 : 0 ≤ F := Finset.sum_nonneg fun m _ => hf0 m
  -- the product map is injective on primes times the low range
  set Φ : ℕ × ℕ → ℕ := fun x => x.1 * x.2 with hΦ
  have hinj : Set.InjOn Φ (Pset ×ˢ Finset.Icc 1 z : Finset (ℕ × ℕ)) := by
    rintro ⟨p, m⟩ hx ⟨p', m'⟩ hx' he
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_Icc] at hx hx'
    obtain ⟨hp, hm1, hmz⟩ := hx
    obtain ⟨hp', hm1', hmz'⟩ := hx'
    obtain ⟨hpp, hpA, -⟩ := hPmem p hp
    obtain ⟨hpp', hpA', -⟩ := hPmem p' hp'
    have he' : p * m = p' * m' := he
    have hdvd : p ∣ p' * m' := ⟨m, he'.symm⟩
    have hpe : p = p' := by
      rcases (Nat.Prime.dvd_mul hpp).1 hdvd with h | h
      · exact (Nat.prime_dvd_prime_iff_eq hpp hpp').1 h
      · have := Nat.le_of_dvd (by omega) h
        omega
    subst hpe
    have hme : m = m' := Nat.eq_of_mul_eq_mul_left hpp.pos he'
    rw [hme]
  set S₂ : Finset ℕ := (Pset ×ˢ Finset.Icc 1 z).image Φ with hS₂
  have hdisj : Disjoint (Finset.Icc 1 z) S₂ := by
    refine Finset.disjoint_left.2 fun n hn hn' => ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn'
    obtain ⟨hp, hm⟩ := Finset.mem_product.mp hx
    obtain ⟨hpp, hpA, -⟩ := hPmem x.1 hp
    have hm1 := (Finset.mem_Icc.mp hm).1
    have hle : x.1 ≤ x.1 * x.2 := Nat.le_mul_of_pos_right _ hm1
    have hnz := (Finset.mem_Icc.mp hn).2
    simp only [hΦ] at hnz
    omega
  have hsub : Finset.Icc 1 z ∪ S₂ ⊆ Finset.Icc 1 M := by
    intro n hn
    rcases Finset.mem_union.mp hn with h | h
    · obtain ⟨h1', h2'⟩ := Finset.mem_Icc.mp h
      refine Finset.mem_Icc.mpr ⟨h1', hMfloor n ?_⟩
      have hz1 : (z : ℝ) ≤ (z : ℝ) * Real.exp ((θ + 1 / a) * L) := by
        have hexp : 1 ≤ Real.exp ((θ + 1 / a) * L) := by
          have hθ0 : 0 < θ := by
            by_contra h
            have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) hL0.le
            linarith
          exact Real.one_le_exp (by positivity)
        exact le_mul_of_one_le_right (Nat.cast_nonneg z) hexp
      have hnz : (n : ℝ) ≤ z := by exact_mod_cast h2'
      linarith
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hp, hm⟩ := Finset.mem_product.mp hx
      obtain ⟨hpp, hpA, hpB⟩ := hPmem x.1 hp
      obtain ⟨hm1, hmz⟩ := Finset.mem_Icc.mp hm
      refine Finset.mem_Icc.mpr ⟨Nat.mul_pos hpp.pos hm1, hMfloor _ ?_⟩
      simp only [hΦ]
      push_cast
      have hpR : (x.1 : ℝ) ≤ Real.exp ((θ + 1 / a) * L) :=
        (by exact_mod_cast hpB : (x.1 : ℝ) ≤ B).trans h3
      have hmR : (x.2 : ℝ) ≤ z := by exact_mod_cast hmz
      calc (x.1 : ℝ) * x.2 ≤ Real.exp ((θ + 1 / a) * L) * z :=
            mul_le_mul hpR hmR (Nat.cast_nonneg _) (Real.exp_pos _).le
        _ = (z : ℝ) * Real.exp ((θ + 1 / a) * L) := mul_comm _ _
        _ ≤ _ := hzM
  have hnn : ∀ n ∈ Finset.Icc 1 M, n ∉ Finset.Icc 1 z ∪ S₂ → 0 ≤ f n := fun n _ _ => hf0 n
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn)
  rw [Finset.sum_union hdisj, hS₂, Finset.sum_image hinj, Finset.sum_product]
  have hterm : ∀ p ∈ Pset, ∀ m ∈ Finset.Icc 1 z,
      Real.exp (-2) * Real.exp (-(2 * θ * a)) * (1 / (p : ℝ)) * f m ≤ f (Φ (p, m)) := by
    intro p hp m hm
    obtain ⟨hpp, hpA, hpB⟩ := hPmem p hp
    have hYp : Y < p := by omega
    have hrp := prime_rpow_ge hL0 ha0 hpp.one_lt.le
      ((by exact_mod_cast hpB : (p : ℝ) ≤ B).trans h3)
    have hval : f (Φ (p, m)) = (p : ℝ) ^ (-2 * σ) * f m := by
      simp only [hf, hΦ, hc]
      rw [mollifiedZetaCoeff_prime_mul hpp hYp]
      push_cast
      rw [Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg m)]
      ring
    rw [hval]
    exact mul_le_mul_of_nonneg_right hrp (hf0 m)
  have hsum2 : Real.exp (-2) * Real.exp (-(2 * θ * a)) * (1 / (6 * a)) * F ≤
      ∑ p ∈ Pset, ∑ m ∈ Finset.Icc 1 z, f (Φ (p, m)) := by
    calc Real.exp (-2) * Real.exp (-(2 * θ * a)) * (1 / (6 * a)) * F
        ≤ Real.exp (-2) * Real.exp (-(2 * θ * a)) * (∑ p ∈ Pset, 1 / (p : ℝ)) * F := by
          rw [hsum1]
          gcongr
      _ = ∑ p ∈ Pset, ∑ m ∈ Finset.Icc 1 z,
            Real.exp (-2) * Real.exp (-(2 * θ * a)) * (1 / (p : ℝ)) * f m := by
          rw [Finset.mul_sum Pset (fun p : ℕ => 1 / (p : ℝ))
            (Real.exp (-2) * Real.exp (-(2 * θ * a))), Finset.sum_mul]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [hF, Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun m hm => hterm p hp m hm
  rw [mul_add, mul_one]
  have e : F * (Real.exp (-2) * Real.exp (-(2 * θ * a)) * (1 / (6 * a))) =
      Real.exp (-2) * Real.exp (-(2 * θ * a)) * (1 / (6 * a)) * F := mul_comm _ _
  rw [e]
  exact add_le_add le_rfl hsum2

/-! ### The first moment against a polynomial -/

/-- **The twisted first moment against a polynomial.** -/
theorem norm_integral_zeta_poly_conj_sub_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1) (β w : ℕ → ℂ)
    (Y z : ℕ) {V : ℝ} (hV : 4 ≤ V) :
    ‖(∫ t in V..(2 * V), riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
          edPoly β (Finset.Icc 1 Y) ((σ : ℂ) + (t : ℂ) * I) *
          (starRingEnd ℂ) (edPoly w (Finset.Icc 1 z) ((σ : ℂ) + (t : ℂ) * I))) -
        ∑ m ∈ Finset.Icc 1 z, mollifiedZetaCoeff β Y m * (starRingEnd ℂ) (w m) *
          (((m : ℝ) ^ (-2 * σ) * V : ℝ) : ℂ)‖ ≤
      (∑ d ∈ Finset.Icc 1 Y, ‖β d‖) * (∑ m ∈ Finset.Icc 1 z, ‖w m‖) *
        (27 * Real.sqrt V * z + 8 * (z : ℝ) ^ 2) := by
  classical
  have hs : ∀ n ∈ Finset.Icc 1 z, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hsY : ∀ n ∈ Finset.Icc 1 Y, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hline : ∀ t : ℝ, ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro t h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hcont : ∀ d ∈ Finset.Icc 1 Y, ∀ m ∈ Finset.Icc 1 z,
      Continuous (fun t : ℝ => β d * (starRingEnd ℂ) (w m) *
        twistedZeta σ d m ((σ : ℂ) + (t : ℂ) * I)) := by
    intro d hd m hm
    refine continuous_const.mul (continuous_iff_continuousAt.mpr fun t => ?_)
    exact ContinuousAt.comp (g := twistedZeta σ d m) (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I)
      (differentiableAt_twistedZeta σ (hsY d hd) (hs m hm) (hline t)).continuousAt (by fun_prop)
  have hcorr : (∫ t in V..(2 * V), riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
      edPoly β (Finset.Icc 1 Y) ((σ : ℂ) + (t : ℂ) * I) *
        (starRingEnd ℂ) (edPoly w (Finset.Icc 1 z) ((σ : ℂ) + (t : ℂ) * I))) =
      ∑ d ∈ Finset.Icc 1 Y, ∑ m ∈ Finset.Icc 1 z, β d * (starRingEnd ℂ) (w m) *
        ∫ t in V..(2 * V), twistedZeta σ d m ((σ : ℂ) + (t : ℂ) * I) := by
    simp only [zeta_mul_edPoly_mul_conj_eq_sum]
    rw [intervalIntegral.integral_finsetSum (f := fun d t => ∑ m ∈ Finset.Icc 1 z,
      β d * (starRingEnd ℂ) (w m) * twistedZeta σ d m ((σ : ℂ) + (t : ℂ) * I))
      fun d hd => (continuous_finsetSum _ fun m hm => hcont d hd m hm).intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [intervalIntegral.integral_finsetSum (f := fun m t =>
      β d * (starRingEnd ℂ) (w m) * twistedZeta σ d m ((σ : ℂ) + (t : ℂ) * I))
      fun m hm => (hcont d hd m hm).intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun m _ => ?_
    exact intervalIntegral.integral_const_mul _ _
  set diag : ℕ → ℕ → ℂ := fun d m =>
    if d ∣ m then (((m : ℝ) ^ (-2 * σ) * V : ℝ) : ℂ) else 0 with hdiag
  have hmain : ∑ d ∈ Finset.Icc 1 Y, ∑ m ∈ Finset.Icc 1 z, β d * (starRingEnd ℂ) (w m) * diag d m =
      ∑ m ∈ Finset.Icc 1 z, mollifiedZetaCoeff β Y m * (starRingEnd ℂ) (w m) *
        (((m : ℝ) ^ (-2 * σ) * V : ℝ) : ℂ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold mollifiedZetaCoeff
    rw [Finset.sum_filter, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [hdiag]
    split_ifs <;> simp
  have hzR : ∀ m ∈ Finset.Icc 1 z, (m : ℝ) ≤ z := fun m hm => by
    exact_mod_cast (Finset.mem_Icc.mp hm).2
  have hterm : ∀ d ∈ Finset.Icc 1 Y, ∀ m ∈ Finset.Icc 1 z,
      ‖β d * (starRingEnd ℂ) (w m) * (∫ t in V..(2 * V), twistedZeta σ d m ((σ : ℂ) + (t : ℂ) * I)) -
        β d * (starRingEnd ℂ) (w m) * diag d m‖ ≤
      ‖β d‖ * ‖w m‖ * (27 * Real.sqrt V * z + 8 * (z : ℝ) ^ 2) := by
    intro d hd m hm
    have h1 := norm_integral_twistedZeta_sub_diag_le hσ (by linarith) (hsY d hd) (hs m hm) hV
    have hmz := hzR m hm
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hb : 27 * Real.sqrt V * m + 8 * (m : ℝ) ^ 2 ≤ 27 * Real.sqrt V * z + 8 * (z : ℝ) ^ 2 := by
      have h2 : (m : ℝ) ^ 2 ≤ (z : ℝ) ^ 2 := pow_le_pow_left₀ hm0 hmz 2
      have h3 : Real.sqrt V * m ≤ Real.sqrt V * z :=
        mul_le_mul_of_nonneg_left hmz (Real.sqrt_nonneg V)
      nlinarith
    rw [← mul_sub, norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (h1.trans hb) (by positivity)
  rw [hcorr, ← hmain]
  simp_rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ d ∈ Finset.Icc 1 Y, ∑ m ∈ Finset.Icc 1 z,
        ‖β d‖ * ‖w m‖ * (27 * Real.sqrt V * z + 8 * (z : ℝ) ^ 2) :=
        Finset.sum_le_sum fun d hd =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => hterm d hd m hm)
    _ = _ := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]

/-! ### The mean value theorem from below -/

theorem one_div_le_log_sub_log {m n : ℕ} (hm : 1 ≤ m) (h : m < n) :
    1 / (n : ℝ) ≤ Real.log n - Real.log m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hn0 hm0)
  rw [Real.log_div hn0.ne' hm0.ne', inv_div] at hlog
  have hmn : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
  have e : 1 / (n : ℝ) ≤ 1 - (m : ℝ) / n := by
    rw [le_sub_iff_add_le, ← add_div, div_le_one hn0]
    linarith
  linarith

theorem one_div_le_abs_log_sub_log {m n z : ℕ} (hm : m ∈ Finset.Icc 1 z) (hn : n ∈ Finset.Icc 1 z)
    (hne : m ≠ n) : 1 / (z : ℝ) ≤ |Real.log n - Real.log m| := by
  obtain ⟨hm1, hmz⟩ := Finset.mem_Icc.mp hm
  obtain ⟨hn1, hnz⟩ := Finset.mem_Icc.mp hn
  rcases lt_or_gt_of_ne hne with h | h
  · have h1 := one_div_le_log_sub_log hm1 h
    have hnR : (n : ℝ) ≤ z := by exact_mod_cast hnz
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have h2 : 1 / (z : ℝ) ≤ 1 / (n : ℝ) := one_div_le_one_div_of_le hn0 hnR
    exact h2.trans (h1.trans (le_abs_self _))
  · have h1 := one_div_le_log_sub_log hn1 h
    have hmR : (m : ℝ) ≤ z := by exact_mod_cast hmz
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have h2 : 1 / (z : ℝ) ≤ 1 / (m : ℝ) := one_div_le_one_div_of_le hm0 hmR
    rw [abs_sub_comm]
    exact h2.trans (h1.trans (le_abs_self _))

theorem normSq_edPoly_line_eq (c : ℕ → ℂ) (M : ℕ) (σ t : ℝ) :
    ((‖edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M, c m * (starRingEnd ℂ) (c n) *
        (((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ) *
          Complex.exp (I * ((t * (Real.log n - Real.log m) : ℝ) : ℂ)) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hQ : ((‖edPoly c (Finset.Icc 1 M) s‖ ^ 2 : ℝ) : ℂ) =
      edPoly c (Finset.Icc 1 M) s * (starRingEnd ℂ) (edPoly c (Finset.Icc 1 M) s) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hQ]
  unfold edPoly
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun n hn => ?_
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hexp : ((m : ℝ) : ℂ) ^ (-s) * ((n : ℝ) : ℂ) ^ (s - 2 * (σ : ℂ)) =
      (((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ) *
        Complex.exp (I * ((t * (Real.log n - Real.log m) : ℝ) : ℂ)) := by
    rw [ofReal_natCast_cpow_eq_exp hm1, ofReal_natCast_cpow_eq_exp hn1, Real.rpow_def_of_pos hm0,
      Real.rpow_def_of_pos hn0, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_exp,
      ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [hs]
    push_cast
    ring
  calc c m * ((m : ℝ) : ℂ) ^ (-s) * (starRingEnd ℂ) (c n * ((n : ℝ) : ℂ) ^ (-s))
      = c m * (starRingEnd ℂ) (c n) *
          (((m : ℝ) : ℂ) ^ (-s) * ((n : ℝ) : ℂ) ^ (s - 2 * (σ : ℂ))) := by
        rw [map_mul, hs, conj_natCast_cpow_line]
        ring
    _ = _ := by
        rw [hexp]
        ring

/-- **The mean value theorem from below.** -/
theorem integral_normSq_edPoly_ge (c : ℕ → ℂ) (z : ℕ) (σ V : ℝ) :
    V * ∑ m ∈ Finset.Icc 1 z, ‖c m‖ ^ 2 * (m : ℝ) ^ (-2 * σ) -
        2 * z * (∑ m ∈ Finset.Icc 1 z, ‖c m‖ * (m : ℝ) ^ (-σ)) ^ 2 ≤
      ∫ t in V..(2 * V), ‖edPoly c (Finset.Icc 1 z) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  classical
  set a : ℕ → ℝ := fun m => ‖c m‖ * (m : ℝ) ^ (-σ) with ha
  have ha0 : ∀ m, 0 ≤ a m := fun m =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg m) _)
  set J : ℕ → ℕ → ℂ := fun m n => ∫ t in V..(2 * V),
    Complex.exp (I * ((t * (Real.log n - Real.log m) : ℝ) : ℂ)) with hJ
  have hcont : ∀ m n : ℕ, Continuous fun t : ℝ =>
      Complex.exp (I * ((t * (Real.log n - Real.log m) : ℝ) : ℂ)) := fun m n => by
    push_cast
    fun_prop
  have hexpand : ((∫ t in V..(2 * V), ‖edPoly c (Finset.Icc 1 z) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ Finset.Icc 1 z, ∑ n ∈ Finset.Icc 1 z, c m * (starRingEnd ℂ) (c n) *
        (((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ) * J m n := by
    rw [← intervalIntegral.integral_ofReal]
    simp only [normSq_edPoly_line_eq]
    rw [intervalIntegral.integral_finsetSum (f := fun m t => ∑ n ∈ Finset.Icc 1 z,
      c m * (starRingEnd ℂ) (c n) * (((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ) *
        Complex.exp (I * ((t * (Real.log n - Real.log m) : ℝ) : ℂ)))
      fun m _ => (continuous_finsetSum _ fun n _ =>
        continuous_const.mul (hcont m n)).intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [intervalIntegral.integral_finsetSum (f := fun n t =>
      c m * (starRingEnd ℂ) (c n) * (((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ) *
        Complex.exp (I * ((t * (Real.log n - Real.log m) : ℝ) : ℂ)))
      fun n _ => (continuous_const.mul (hcont m n)).intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun n _ => ?_
    exact intervalIntegral.integral_const_mul _ _
  have hdiagJ : ∀ m : ℕ, J m m = (V : ℂ) := by
    intro m
    simp only [hJ, sub_self, mul_zero, Complex.ofReal_zero, Complex.exp_zero]
    rw [intervalIntegral.integral_const, Complex.real_smul]
    push_cast
    ring
  have hterm : ∀ m ∈ Finset.Icc 1 z, ∀ n ∈ Finset.Icc 1 z,
      ‖c m * (starRingEnd ℂ) (c n) * (((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ) * J m n -
        (if n = m then ((‖c m‖ ^ 2 * (m : ℝ) ^ (-2 * σ) * V : ℝ) : ℂ) else 0)‖ ≤
      a m * a n * (2 * z) := by
    intro m hm n hn
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    by_cases hmn : n = m
    · subst hmn
      rw [if_pos rfl, hdiagJ]
      have e : c n * (starRingEnd ℂ) (c n) * (((n : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ) * (V : ℂ) =
          ((‖c n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) * V : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Real.rpow_add hm0]
        have : -σ + -σ = -2 * σ := by ring
        rw [this]
        push_cast
        ring
      rw [e, sub_self, norm_zero]
      have := ha0 n
      positivity
    · rw [if_neg hmn, sub_zero, norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) _)
          (Real.rpow_nonneg (Nat.cast_nonneg n) _))]
      have hφ := one_div_le_abs_log_sub_log hm hn (Ne.symm hmn)
      have hz0 : (0 : ℝ) < z := by
        have : 1 ≤ z := hm1.trans (Finset.mem_Icc.mp hm).2
        exact_mod_cast this
      have hφ0 : 0 < |Real.log n - Real.log m| := lt_of_lt_of_le (by positivity) hφ
      have hne : Real.log n - Real.log m ≠ 0 := abs_pos.mp hφ0
      have hJb : ‖J m n‖ ≤ 2 * z := by
        refine (integral_exp_I_mul_window_le _ V hne).trans ?_
        rw [div_le_iff₀ hφ0]
        have := mul_le_mul_of_nonneg_left hφ (by positivity : (0 : ℝ) ≤ 2 * z)
        have e : 2 * (z : ℝ) * (1 / z) = 2 := by
          field_simp
        linarith
      calc ‖c m‖ * ‖c n‖ * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ)) * ‖J m n‖
          ≤ ‖c m‖ * ‖c n‖ * ((m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ)) * (2 * z) :=
            mul_le_mul_of_nonneg_left hJb
              (mul_nonneg (by positivity) (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) _)
                (Real.rpow_nonneg (Nat.cast_nonneg n) _)))
        _ = _ := by
            simp only [ha]
            ring
  have hbound : ‖((∫ t in V..(2 * V), ‖edPoly c (Finset.Icc 1 z) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ) -
      ((V * ∑ m ∈ Finset.Icc 1 z, ‖c m‖ ^ 2 * (m : ℝ) ^ (-2 * σ) : ℝ) : ℂ)‖ ≤
      2 * z * (∑ m ∈ Finset.Icc 1 z, a m) ^ 2 := by
    have hsumdiag : ((V * ∑ m ∈ Finset.Icc 1 z, ‖c m‖ ^ 2 * (m : ℝ) ^ (-2 * σ) : ℝ) : ℂ) =
        ∑ m ∈ Finset.Icc 1 z, ∑ n ∈ Finset.Icc 1 z,
          (if n = m then ((‖c m‖ ^ 2 * (m : ℝ) ^ (-2 * σ) * V : ℝ) : ℂ) else 0) := by
      rw [Finset.mul_sum, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [Finset.sum_ite_eq' , if_pos hm]
      push_cast
      ring
    rw [hexpand, hsumdiag]
    simp_rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ m ∈ Finset.Icc 1 z, ∑ n ∈ Finset.Icc 1 z, a m * a n * (2 * z) :=
          Finset.sum_le_sum fun m hm =>
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => hterm m hm n hn)
      _ = _ := by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          ring
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hbound
  have := (abs_le.mp hbound).1
  linarith

/-! ### Assembly -/

/-- The square of `ζP − W` on a segment. -/
theorem integral_norm_zetaPoly_sub_poly_sq_eq {σ : ℝ} (hσ1 : σ < 1) (β w : ℕ → ℂ) (Y z : ℕ)
    (V : ℝ) :
    (∫ t in V..(2 * V), ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
        edPoly β (Finset.Icc 1 Y) ((σ : ℂ) + (t : ℂ) * I) -
        edPoly w (Finset.Icc 1 z) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) =
      (∫ t in V..(2 * V), ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
        edPoly β (Finset.Icc 1 Y) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) -
      2 * (∫ t in V..(2 * V), riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
        edPoly β (Finset.Icc 1 Y) ((σ : ℂ) + (t : ℂ) * I) *
        (starRingEnd ℂ) (edPoly w (Finset.Icc 1 z) ((σ : ℂ) + (t : ℂ) * I))).re +
      ∫ t in V..(2 * V), ‖edPoly w (Finset.Icc 1 z) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hline : ∀ t : ℝ, ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro t h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hsY : ∀ n ∈ Finset.Icc 1 Y, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hsz : ∀ n ∈ Finset.Icc 1 z, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hZc : Continuous fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
      edPoly β (Finset.Icc 1 Y) ((σ : ℂ) + (t : ℂ) * I) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    exact (ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I)
      (differentiableAt_riemannZeta (hline t)).continuousAt (by fun_prop)).mul
      (((differentiable_edPoly β hsY).continuous.comp (by fun_prop)).continuousAt)
  have hWc : Continuous fun t : ℝ => edPoly w (Finset.Icc 1 z) ((σ : ℂ) + (t : ℂ) * I) :=
    (differentiable_edPoly w hsz).continuous.comp (by fun_prop)
  have hcross : Continuous fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
      edPoly β (Finset.Icc 1 Y) ((σ : ℂ) + (t : ℂ) * I) *
      (starRingEnd ℂ) (edPoly w (Finset.Icc 1 z) ((σ : ℂ) + (t : ℂ) * I)) :=
    hZc.mul (Complex.continuous_conj.comp hWc)
  have hre : (∫ t in V..(2 * V), (riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
      edPoly β (Finset.Icc 1 Y) ((σ : ℂ) + (t : ℂ) * I) *
      (starRingEnd ℂ) (edPoly w (Finset.Icc 1 z) ((σ : ℂ) + (t : ℂ) * I))).re) =
      (∫ t in V..(2 * V), riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
        edPoly β (Finset.Icc 1 Y) ((σ : ℂ) + (t : ℂ) * I) *
        (starRingEnd ℂ) (edPoly w (Finset.Icc 1 z) ((σ : ℂ) + (t : ℂ) * I))).re :=
    Complex.reCLM.intervalIntegral_comp_comm (hcross.intervalIntegrable _ _)
  have hpt : ∀ t : ℝ, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
      edPoly β (Finset.Icc 1 Y) ((σ : ℂ) + (t : ℂ) * I) -
      edPoly w (Finset.Icc 1 z) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 =
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
        edPoly β (Finset.Icc 1 Y) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 -
      2 * (riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
        edPoly β (Finset.Icc 1 Y) ((σ : ℂ) + (t : ℂ) * I) *
        (starRingEnd ℂ) (edPoly w (Finset.Icc 1 z) ((σ : ℂ) + (t : ℂ) * I))).re +
      ‖edPoly w (Finset.Icc 1 z) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    intro t
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]
    ring
  simp_rw [hpt]
  have hi1 : IntervalIntegrable (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
      edPoly β (Finset.Icc 1 Y) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume V (2 * V) :=
    (hZc.norm.pow 2).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t : ℝ => 2 * (riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
      edPoly β (Finset.Icc 1 Y) ((σ : ℂ) + (t : ℂ) * I) *
      (starRingEnd ℂ) (edPoly w (Finset.Icc 1 z) ((σ : ℂ) + (t : ℂ) * I))).re) volume V (2 * V) :=
    (continuous_const.mul (Complex.continuous_re.comp hcross)).intervalIntegrable _ _
  have hi3 : IntervalIntegrable (fun t : ℝ =>
      ‖edPoly w (Finset.Icc 1 z) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume V (2 * V) :=
    (hWc.norm.pow 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hi1.sub hi2) hi3, intervalIntegral.integral_sub hi1 hi2,
    intervalIntegral.integral_const_mul, hre]

/-- Everything below the block is a perfect square. -/
theorem main_terms_nonneg {V : ℝ} (hV : 0 ≤ V) (c w : ℕ → ℂ) {r : ℕ → ℝ} (hr : ∀ m, 0 ≤ r m)
    (S : Finset ℕ) :
    0 ≤ V * ∑ m ∈ S, ‖c m‖ ^ 2 * r m -
      2 * (∑ m ∈ S, c m * (starRingEnd ℂ) (w m) * ((r m * V : ℝ) : ℂ)).re +
      V * ∑ m ∈ S, ‖w m‖ ^ 2 * r m := by
  have e : V * ∑ m ∈ S, ‖c m‖ ^ 2 * r m -
      2 * (∑ m ∈ S, c m * (starRingEnd ℂ) (w m) * ((r m * V : ℝ) : ℂ)).re +
      V * ∑ m ∈ S, ‖w m‖ ^ 2 * r m = V * ∑ m ∈ S, ‖c m - w m‖ ^ 2 * r m := by
    rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Complex.re_mul_ofReal, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_sub]
    ring
  rw [e]
  exact mul_nonneg hV (Finset.sum_nonneg fun m _ => mul_nonneg (sq_nonneg _) (hr m))

/-- The energy below `z` of the coefficients of `ζΨW` at abscissa `σ`. -/
def weightEnergy (b w : ℕ → ℂ) (y z : ℕ) (σ : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 z, ‖mollifiedZetaCoeff (polyConv b w y z) (y * z) m‖ ^ 2 * (m : ℝ) ^ (-2 * σ)

theorem one_le_weightEnergy {b w : ℕ → ℂ} {y z : ℕ} (hy : 1 ≤ y) (hz : 1 ≤ z) (hb1 : b 1 = 1)
    (hw1 : w 1 = 1) (σ : ℝ) : 1 ≤ weightEnergy b w y z σ := by
  have hone : ‖mollifiedZetaCoeff (polyConv b w y z) (y * z) 1‖ ^ 2 *
      ((1 : ℕ) : ℝ) ^ (-2 * σ) = 1 := by
    rw [mollifiedZetaCoeff_one (Nat.mul_pos hy hz), polyConv_one hy hz, hb1, hw1]
    simp
  have h : ‖mollifiedZetaCoeff (polyConv b w y z) (y * z) 1‖ ^ 2 * ((1 : ℕ) : ℝ) ^ (-2 * σ) ≤
      weightEnergy b w y z σ :=
    Finset.single_le_sum (f := fun m : ℕ =>
      ‖mollifiedZetaCoeff (polyConv b w y z) (y * z) m‖ ^ 2 * (m : ℝ) ^ (-2 * σ))
      (s := Finset.Icc 1 z) (fun m _ => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (Nat.cast_nonneg m) _)) (Finset.mem_Icc.mpr ⟨le_rfl, hz⟩)
  rwa [hone] at h

/-- The size conditions on the floor `m = e^{−2} g/6`, `g = e^{−2θa}/a`. -/
theorem floor_size_conditions {θ a L K m : ℝ} (hθ0 : 0 ≤ θ) (ha : 4 ≤ a) (hL128 : 128 ≤ L)
    (hK2 : 200000 ≤ K)
    (hm : m = Real.exp (-2) * (Real.exp (-(2 * θ * a)) / a) * (1 / 6))
    (hgL : K / L ≤ Real.exp (-(2 * θ * a)) / a) :
    0 < m ∧ m ≤ 1 ∧ 1 / (48 * L) ≤ m ∧ 32 / (m / 4 / (1 + m)) ≤ (1 - 3 / 4) / 4 * L := by
  have hL0 : 0 < L := by linarith
  have ha0 : 0 < a := by linarith
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = Real.exp (-(2 * θ * a)) / a := ⟨_, rfl⟩
  rw [← hg] at hm hgL
  have hgpos : 0 < g := by
    rw [hg]
    positivity
  have hm0 : 0 < m := by
    rw [hm]
    positivity
  have he1 : Real.exp (-2) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hgle : g ≤ 1 / a := by
    rw [hg]
    refine div_le_div_of_nonneg_right ?_ ha0.le
    exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hθ0 ha0.le])
  have hg1 : g ≤ 1 := hgle.trans (by
    rw [div_le_one ha0]
    linarith)
  have hm1 : m ≤ 1 := by
    rw [hm]
    nlinarith
  have hcond := floor_scale_conditions hK2 hL128 hgL hm hm1
  have he8 : 1 / 8 ≤ Real.exp (-2) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos 2) exp_two_le_eight
  have hgLow : 1 / L ≤ g := le_trans (div_le_div_of_nonneg_right (by linarith) hL0.le) hgL
  have hmLow : 1 / (48 * L) ≤ m := by
    have h1 : g / 48 ≤ m := by
      rw [hm]
      nlinarith
    have h2 : 1 / (48 * L) = (1 / L) / 48 := by
      field_simp
    rw [h2]
    linarith
  exact ⟨hm0, hm1, hmLow, hcond⟩

/-- The supremum condition of the Gaussian floor with coefficient bound `A`, `A² ≤ e^L`. -/
theorem sup_condition_of_norm_le {L m A δ : ℝ} (hL0 : 0 < L) (hmLow : 1 / (48 * L) ≤ m) (hA0 : 0 < A)
    (hA2 : A ^ 2 ≤ Real.exp L) (hδ : m / 4 ≤ δ)
    (hsupV : Real.exp (7 * L) * Real.exp (-(1 / 128 * Real.exp (1 / 8 * L))) ≤ 1 / (99 * 1152)) :
    99 * (Real.exp (5 * L) * Real.exp (-(1 / 128 * Real.exp ((1 - 3 / 4) / 2 * L)))) ≤
      δ / A ^ 2 / 6 := by
  have e1 : (1 - 3 / 4 : ℝ) / 2 = 1 / 8 := by norm_num
  rw [e1]
  set E := Real.exp L with hE
  have hE0 : 0 < E := Real.exp_pos L
  have hLE : L ≤ E := by
    have := Real.add_one_le_exp L
    linarith
  have hsplit : Real.exp (5 * L) = (E ^ 2)⁻¹ * Real.exp (7 * L) := by
    rw [hE, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have h1 : 99 * (Real.exp (5 * L) * Real.exp (-(1 / 128 * Real.exp (1 / 8 * L)))) ≤
      (E ^ 2)⁻¹ / 1152 := by
    rw [hsplit, mul_assoc]
    have h2 := mul_le_mul_of_nonneg_left hsupV (by positivity : (0 : ℝ) ≤ (E ^ 2)⁻¹)
    have e2 : 99 * ((E ^ 2)⁻¹ * (1 / (99 * 1152))) = (E ^ 2)⁻¹ / 1152 := by
      field_simp
    calc _ ≤ 99 * ((E ^ 2)⁻¹ * (1 / (99 * 1152))) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = _ := e2
  refine h1.trans ?_
  have hlow : 1 / (192 * L) ≤ δ := by
    have e3 : 1 / (192 * L) = 1 / (48 * L) / 4 := by
      field_simp
      norm_num
    rw [e3]
    linarith
  have hδ0 : 0 < δ := lt_of_lt_of_le (by positivity) hlow
  have hA20 : 0 < A ^ 2 := by positivity
  rw [div_div, le_div_iff₀ (by positivity)]
  have h3 : (E ^ 2)⁻¹ / 1152 * (A ^ 2 * 6) ≤ (E ^ 2)⁻¹ / 1152 * (E * 6) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  refine h3.trans ?_
  have e4 : (E ^ 2)⁻¹ / 1152 * (E * 6) = 1 / (192 * E) := by
    field_simp
    norm_num
  rw [e4]
  refine le_trans (one_div_le_one_div_of_le (by positivity) ?_) hlow
  linarith

/-- The first moment and mean value errors against the floor. -/
theorem weighted_error_le {V L θ m : ℝ} {y z : ℕ} (hV1 : 1 ≤ V) (hL0 : 0 < L) (hθ0 : 0 < θ)
    (hθ : θ < 1 / 2) (hz1 : 1 ≤ z) (hyz : (y : ℝ) * z ≤ V ^ θ)
    (hzle : (z : ℝ) ≤ V ^ ((1 / 2 - θ) / 4)) (hmLow : 1 / (48 * L) ≤ m)
    (hlogV : 72 * 192 * L ≤ V ^ ((1 / 2 - θ) / 2)) :
    2 * ((y : ℝ) * z * z * (27 * Real.sqrt V * z + 8 * (z : ℝ) ^ 2)) + 2 * z * (z : ℝ) ^ 2 ≤
      m / 4 * V := by
  have hV0 : 0 < V := by linarith
  have hZ1 : (1 : ℝ) ≤ z := by exact_mod_cast hz1
  set η := (1 / 2 - θ) / 4 with hη
  set κ := 3 / 4 + θ / 2 with hκ
  have hsqrt : Real.sqrt V = V ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow V
  have hY0 : 0 ≤ (y : ℝ) * z := by positivity
  have hVη : 0 ≤ V ^ η := by positivity
  have hZ2 : (z : ℝ) ^ 2 ≤ V ^ (2 * η) := by
    have h := pow_le_pow_left₀ (by positivity) hzle 2
    have e : (V ^ η) ^ 2 = V ^ (2 * η) := by
      rw [← Real.rpow_natCast (V ^ η) 2, ← Real.rpow_mul hV0.le]
      congr 1
      push_cast
      ring
    rwa [e] at h
  have hZ3 : (z : ℝ) ^ 3 ≤ V ^ (3 * η) := by
    have h := pow_le_pow_left₀ (by positivity) hzle 3
    have e : (V ^ η) ^ 3 = V ^ (3 * η) := by
      rw [← Real.rpow_natCast (V ^ η) 3, ← Real.rpow_mul hV0.le]
      congr 1
      push_cast
      ring
    rwa [e] at h
  have hmono : ∀ {x : ℝ}, x ≤ κ → V ^ x ≤ V ^ κ := fun h =>
    Real.rpow_le_rpow_of_exponent_le hV1 h
  have ht1 : (y : ℝ) * z * z * (Real.sqrt V * z) ≤ V ^ κ := by
    have e : (y : ℝ) * z * z * (Real.sqrt V * z) = ((y : ℝ) * z) * (z : ℝ) ^ 2 * Real.sqrt V := by
      ring
    rw [e, hsqrt]
    have h1 : ((y : ℝ) * z) * (z : ℝ) ^ 2 ≤ V ^ θ * V ^ (2 * η) :=
      mul_le_mul hyz hZ2 (by positivity) (by positivity)
    have h2 : V ^ θ * V ^ (2 * η) * V ^ (1 / 2 : ℝ) = V ^ κ := by
      rw [← Real.rpow_add hV0, ← Real.rpow_add hV0]
      congr 1
      rw [hη, hκ]
      ring
    calc _ ≤ V ^ θ * V ^ (2 * η) * V ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := h2
  have ht2 : (y : ℝ) * z * z * (z : ℝ) ^ 2 ≤ V ^ κ := by
    have e : (y : ℝ) * z * z * (z : ℝ) ^ 2 = ((y : ℝ) * z) * (z : ℝ) ^ 3 := by ring
    rw [e]
    have h1 : ((y : ℝ) * z) * (z : ℝ) ^ 3 ≤ V ^ θ * V ^ (3 * η) :=
      mul_le_mul hyz hZ3 (by positivity) (by positivity)
    refine h1.trans ?_
    rw [← Real.rpow_add hV0]
    exact hmono (by rw [hη, hκ]; linarith)
  have ht3 : (z : ℝ) * (z : ℝ) ^ 2 ≤ V ^ κ := by
    have e : (z : ℝ) * (z : ℝ) ^ 2 = (z : ℝ) ^ 3 := by ring
    rw [e]
    exact hZ3.trans (hmono (by rw [hη, hκ]; linarith))
  have hsum : 2 * ((y : ℝ) * z * z * (27 * Real.sqrt V * z + 8 * (z : ℝ) ^ 2)) +
      2 * z * (z : ℝ) ^ 2 ≤ 72 * V ^ κ := by
    have e : 2 * ((y : ℝ) * z * z * (27 * Real.sqrt V * z + 8 * (z : ℝ) ^ 2)) +
        2 * z * (z : ℝ) ^ 2 =
        54 * ((y : ℝ) * z * z * (Real.sqrt V * z)) + 16 * ((y : ℝ) * z * z * (z : ℝ) ^ 2) +
          2 * ((z : ℝ) * (z : ℝ) ^ 2) := by
      ring
    rw [e]
    linarith
  have hprod : V ^ ((1 / 2 - θ) / 2) * V ^ κ = V := by
    rw [← Real.rpow_add hV0]
    have : (1 / 2 - θ) / 2 + κ = 1 := by
      rw [hκ]
      ring
    rw [this, Real.rpow_one]
  have hLV : 72 * 192 * L * V ^ κ ≤ V := by
    calc 72 * 192 * L * V ^ κ ≤ V ^ ((1 / 2 - θ) / 2) * V ^ κ :=
          mul_le_mul_of_nonneg_right hlogV (by positivity)
      _ = V := hprod
  have h2 : 1 / (192 * L) * V ≤ m / 4 * V := by
    refine mul_le_mul_of_nonneg_right ?_ hV0.le
    have e : 1 / (192 * L) = 1 / (48 * L) / 4 := by
      field_simp
      norm_num
    rw [e]
    linarith
  have h3 : 72 * V ^ κ ≤ 1 / (192 * L) * V := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    nlinarith
  linarith

/-- The two sums of the weight are at most its length. -/
theorem sum_norm_weight_le {w : ℕ → ℂ} {z : ℕ} (hw : ∀ m ∈ Finset.Icc 1 z, ‖w m‖ ≤ 1) :
    ∑ m ∈ Finset.Icc 1 z, ‖w m‖ ≤ z := by
  calc _ ≤ ∑ _m ∈ Finset.Icc 1 z, (1 : ℝ) := Finset.sum_le_sum hw
    _ = z := by simp

theorem sum_norm_rpow_weight_le {w : ℕ → ℂ} {z : ℕ} (hw : ∀ m ∈ Finset.Icc 1 z, ‖w m‖ ≤ 1)
    {σ : ℝ} (hσ : 0 ≤ σ) : ∑ m ∈ Finset.Icc 1 z, ‖w m‖ * (m : ℝ) ^ (-σ) ≤ z := by
  calc _ ≤ ∑ _m ∈ Finset.Icc 1 z, (1 : ℝ) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
        have h1 : (m : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hm1 (by linarith)
        have h0 : 0 ≤ (m : ℝ) ^ (-σ) := Real.rpow_nonneg (by linarith) _
        calc ‖w m‖ * (m : ℝ) ^ (-σ) ≤ 1 * 1 :=
              mul_le_mul (hw m hm) h1 h0 (by norm_num)
          _ = 1 := by norm_num
    _ = z := by simp

/-- The closing arithmetic of the weighted floor. -/
theorem weighted_defect_arith {I₁ X I₃ V D m W₂ R E O : ℝ}
    (hfloor : (D * (1 + m) - D * (m / 4)) * V ≤ I₁) (hX : X - R ≤ E) (hmean : V * W₂ - O ≤ I₃)
    (hsquare : 0 ≤ V * D - 2 * R + V * W₂) (herr : 2 * E + O ≤ m / 4 * V) (hD : 1 ≤ D) (hm : 0 < m)
    (hV : 0 < V) : m / 2 * D * V ≤ I₁ - 2 * X + I₃ := by
  have h : 0 ≤ (D - 1) * (m / 4 * V) := mul_nonneg (by linarith) (by positivity)
  nlinarith

/-- The floor for `ζΨW` from the energy of the last scale. -/
theorem zetaPoly_floor_of_scale {θ a L m : ℝ} {y z : ℕ} {b w : ℕ → ℂ} (hθ0 : 0 < θ) (hθ : θ < 1 / 2)
    (ha : 4 ≤ a) (hL128 : 128 ≤ L) (hL8 : 8 * a ≤ L) (hθL : 1 ≤ θ * L)
    (hCm : 12 * mertensError * a ≤ θ * L) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (hyz : (y : ℝ) * z ≤ Real.exp (θ * L))
    (hzM : (z : ℝ) * Real.exp ((θ + 1 / a) * L) ≤ Real.exp ((3 / 4 + (1 - 3 / 4) / 4) * L))
    (hb1 : b 1 = 1) (hb : ∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1) (hw1 : w 1 = 1)
    (hw : ∀ m ∈ Finset.Icc 1 z, ‖w m‖ ≤ 1) (hm0 : 0 < m) (hmLow : 1 / (48 * L) ≤ m)
    (hcond : 32 / (m / 4 / (1 + m)) ≤ (1 - 3 / 4) / 4 * L)
    (hEneq : Real.exp (-2) * Real.exp (-(2 * θ * a)) * (1 / (6 * a)) = m)
    (hsupV : Real.exp (7 * L) * Real.exp (-(1 / 128 * Real.exp (1 / 8 * L))) ≤ 1 / (99 * 1152)) :
    (weightEnergy b w y z (1 / 2 + a / L) * (1 + m) -
        weightEnergy b w y z (1 / 2 + a / L) * (m / 4)) * Real.exp L ≤
      ∫ t in (Real.exp L)..(2 * Real.exp L),
        ‖riemannZeta (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly (polyConv b w y z) (Finset.Icc 1 (y * z))
            (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hL0 : 0 < L := by linarith
  have hY1 : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hZ1 : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have hzθ : (z : ℝ) ≤ Real.exp (θ * L) :=
    le_trans (le_mul_of_one_le_left (by linarith) hY1) hyz
  have hYle : ((y * z : ℕ) : ℝ) ≤ Real.exp (θ * L) := by
    push_cast
    exact hyz
  have hEn := energy_ge_weighted_last_scale hθ ha hL8 hθL hCm hYle hzθ hzM (polyConv b w y z)
  rw [hEneq] at hEn
  have hDz1 := one_le_weightEnergy hy hz hb1 hw1 (1 / 2 + a / L)
  have hEn' : weightEnergy b w y z (1 / 2 + a / L) * (1 + m) ≤
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp ((3 / 4 + (1 - 3 / 4) / 4) * L)⌋₊,
        ‖mollifiedZetaCoeff (polyConv b w y z) (y * z) n‖ ^ 2 *
          (n : ℝ) ^ (-2 * (1 / 2 + a / L)) := hEn
  generalize weightEnergy b w y z (1 / 2 + a / L) = D at hDz1 hEn' ⊢
  have hD0 : 0 < D := by linarith
  have hA0 : 0 < (y : ℝ) * z := by positivity
  have hA2 : ((y : ℝ) * z) ^ 2 ≤ Real.exp L := by
    have h1 : ((y : ℝ) * z) ^ 2 ≤ Real.exp (θ * L) ^ 2 := pow_le_pow_left₀ hA0.le hyz 2
    refine h1.trans ?_
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    push_cast
    nlinarith
  have hδ : m / 4 ≤ D * (m / 4) := le_mul_of_one_le_left (by positivity) hDz1
  have hsup := sup_condition_of_norm_le hL0 hmLow hA0 hA2 hδ hsupV
  have hratio : D * (m / 4) / (D * (1 + m)) = m / 4 / (1 + m) := mul_div_mul_left _ _ hD0.ne'
  have hcond' : 32 / (D * (m / 4) / (D * (1 + m))) ≤ (1 - 3 / 4) / 4 * L := by
    rw [hratio]
    exact hcond
  have hD₀ : 0 < D * (1 + m) := by positivity
  have hδ0 : 0 < D * (m / 4) := by positivity
  have hδD : D * (m / 4) ≤ D * (1 + m) := mul_le_mul_of_nonneg_left (by linarith) hD0.le
  have hLa : 2 * a + 3 ≤ L := by linarith
  have h8 : (8 : ℝ) ≤ (1 - 3 / 4) / 4 * L := by linarith
  have hY34 : ((y * z : ℕ) : ℝ) ≤ Real.exp (3 / 4 * L) :=
    hYle.trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) hL0.le))
  have hβ : ∀ d ∈ Finset.Icc 1 (y * z), ‖polyConv b w y z d‖ ≤ (y : ℝ) * z :=
    fun d _ => norm_polyConv_le hb hw d
  exact gaussFloor_of_norm_le (a := a) (θ₁ := 3 / 4) (L := L) (D₀ := D * (1 + m))
    (δ := D * (m / 4)) (A := (y : ℝ) * z) (by linarith) (by norm_num) (by norm_num) hD₀ hδ0 hδD hLa h8
    hcond' hA0 hsup (Nat.mul_pos hy hz) hY34 hβ hEn'

/-- The defect of `ζP − W` from the floor for `ζP`: the first moment and the mean value theorem
turn everything below the block into a perfect square. -/
theorem weighted_defect_ge_of_floor {σ V m : ℝ} {y z : ℕ} {b w : ℕ → ℂ} (hσlo : 1 / 2 ≤ σ)
    (hσhi : σ < 1) (hV4 : 4 ≤ V) (hy : 1 ≤ y) (hz : 1 ≤ z) (hb1 : b 1 = 1)
    (hb : ∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1) (hw1 : w 1 = 1) (hw : ∀ m ∈ Finset.Icc 1 z, ‖w m‖ ≤ 1)
    (hm0 : 0 < m)
    (hfloor : (weightEnergy b w y z σ * (1 + m) - weightEnergy b w y z σ * (m / 4)) * V ≤
      ∫ t in V..(2 * V), ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
        edPoly (polyConv b w y z) (Finset.Icc 1 (y * z)) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
    (herr : 2 * ((y : ℝ) * z * z * (27 * Real.sqrt V * z + 8 * (z : ℝ) ^ 2)) + 2 * z * (z : ℝ) ^ 2 ≤
      m / 4 * V) :
    m / 2 * weightEnergy b w y z σ * V ≤
      ∫ t in V..(2 * V), ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
          edPoly (polyConv b w y z) (Finset.Icc 1 (y * z)) ((σ : ℂ) + (t : ℂ) * I) -
        edPoly w (Finset.Icc 1 z) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hV0 : 0 < V := by linarith
  have hDz1 := one_le_weightEnergy hy hz hb1 hw1 σ
  have hcross := norm_integral_zeta_poly_conj_sub_le hσlo hσhi (polyConv b w y z) w (y * z) z hV4
  have hSβ := sum_norm_polyConv_le hb hw
  have hSw := sum_norm_weight_le hw
  have hS0 : 0 ≤ 27 * Real.sqrt V * z + 8 * (z : ℝ) ^ 2 := by positivity
  have hcross2 : (∑ d ∈ Finset.Icc 1 (y * z), ‖polyConv b w y z d‖) *
      (∑ m ∈ Finset.Icc 1 z, ‖w m‖) * (27 * Real.sqrt V * z + 8 * (z : ℝ) ^ 2) ≤
      (y : ℝ) * z * z * (27 * Real.sqrt V * z + 8 * (z : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul hSβ hSw (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (by positivity)) hS0
  have hmean := integral_normSq_edPoly_ge w z σ V
  have hrw : (∑ m ∈ Finset.Icc 1 z, ‖w m‖ * (m : ℝ) ^ (-σ)) ^ 2 ≤ (z : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Finset.sum_nonneg fun m _ => mul_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (Nat.cast_nonneg m) _)) (sum_norm_rpow_weight_le hw (by linarith)) 2
  have hmean2 : 2 * (z : ℝ) * (∑ m ∈ Finset.Icc 1 z, ‖w m‖ * (m : ℝ) ^ (-σ)) ^ 2 ≤
      2 * z * (z : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hrw (by positivity)
  have hsquare := main_terms_nonneg hV0.le (mollifiedZetaCoeff (polyConv b w y z) (y * z)) w
    (r := fun m : ℕ => (m : ℝ) ^ (-2 * σ)) (fun m => Real.rpow_nonneg (Nat.cast_nonneg m) _)
    (Finset.Icc 1 z)
  have hre := (Complex.abs_re_le_norm _).trans (hcross.trans hcross2)
  rw [Complex.sub_re] at hre
  rw [integral_norm_zetaPoly_sub_poly_sq_eq hσhi (polyConv b w y z) w (y * z) z V]
  refine weighted_defect_arith hfloor (abs_le.mp hre).2 (le_trans (sub_le_sub_left hmean2 _) hmean)
    hsquare herr hDz1 hm0 hV0

/-- **The weighted defect at the last scale**, on `V = e^L`. -/
theorem weighted_defect_ge_of_scale {θ a L K m : ℝ} {y z : ℕ} {b w : ℕ → ℂ} (hθ0 : 0 < θ)
    (hθ : θ < 1 / 2) (ha : 4 ≤ a) (hL128 : 128 ≤ L) (hKa : K * a ≤ L) (hK2 : 200000 ≤ K)
    (hθL : 1 ≤ θ * L) (hCm : 12 * mertensError * a ≤ θ * L) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (hyz : (y : ℝ) * z ≤ Real.exp L ^ θ) (hzle : (z : ℝ) ≤ Real.exp L ^ ((1 / 2 - θ) / 4))
    (hb1 : b 1 = 1) (hb : ∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1) (hw1 : w 1 = 1)
    (hw : ∀ m ∈ Finset.Icc 1 z, ‖w m‖ ≤ 1)
    (hm : m = Real.exp (-2) * (Real.exp (-(2 * θ * a)) / a) * (1 / 6))
    (hgL : K / L ≤ Real.exp (-(2 * θ * a)) / a)
    (hsupV : Real.exp (7 * L) * Real.exp (-(1 / 128 * Real.exp (1 / 8 * L))) ≤ 1 / (99 * 1152))
    (hlogV : 72 * 192 * L ≤ Real.exp L ^ ((1 / 2 - θ) / 2)) :
    m / 2 * weightEnergy b w y z (1 / 2 + a / L) * Real.exp L ≤
      ∫ t in (Real.exp L)..(2 * Real.exp L),
        ‖riemannZeta (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I) *
            edPoly (polyConv b w y z) (Finset.Icc 1 (y * z))
              (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I) -
          edPoly w (Finset.Icc 1 z) (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hL0 : 0 < L := by linarith
  have ha0 : 0 < a := by linarith
  have hL8 : 8 * a ≤ L := by nlinarith
  obtain ⟨hm0, -, hmLow, hcond⟩ := floor_size_conditions hθ0.le ha hL128 hK2 hm hgL
  have hexpθ : ∀ x : ℝ, Real.exp L ^ x = Real.exp (x * L) := by
    intro x
    rw [← Real.exp_mul, mul_comm]
  have hyz' : (y : ℝ) * z ≤ Real.exp (θ * L) := by rwa [hexpθ] at hyz
  have hzle' : (z : ℝ) ≤ Real.exp ((1 / 2 - θ) / 4 * L) := by rwa [hexpθ] at hzle
  have h1a : 1 / a ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) ha
  have hzM : (z : ℝ) * Real.exp ((θ + 1 / a) * L) ≤
      Real.exp ((3 / 4 + (1 - 3 / 4) / 4) * L) := by
    calc (z : ℝ) * Real.exp ((θ + 1 / a) * L)
        ≤ Real.exp ((1 / 2 - θ) / 4 * L) * Real.exp ((θ + 1 / a) * L) :=
          mul_le_mul_of_nonneg_right hzle' (Real.exp_pos _).le
      _ = Real.exp (((1 / 2 - θ) / 4 + (θ + 1 / a)) * L) := by
          rw [← Real.exp_add]
          congr 1
          ring
      _ ≤ _ := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) hL0.le)
  have hEneq : Real.exp (-2) * Real.exp (-(2 * θ * a)) * (1 / (6 * a)) = m := by
    rw [hm]
    field_simp
  have hfloor := zetaPoly_floor_of_scale hθ0 hθ ha hL128 hL8 hθL hCm hy hz hyz' hzM hb1 hb hw1 hw hm0
    hmLow hcond hEneq hsupV
  have hσlo : 1 / 2 ≤ 1 / 2 + a / L := by
    have : 0 ≤ a / L := by positivity
    linarith
  have hσhi : 1 / 2 + a / L < 1 := by
    have : a / L < 1 / 2 := by
      rw [div_lt_iff₀ hL0]
      linarith
    linarith
  have hV4 : 4 ≤ Real.exp L := by
    have := Real.add_one_le_exp L
    linarith
  have hV1 : 1 ≤ Real.exp L := by linarith
  have herr := weighted_error_le hV1 hL0 hθ0 hθ hz hyz hzle hmLow hlogV
  exact weighted_defect_ge_of_floor hσlo hσhi hV4 hy hz hb1 hb hw1 hw hm0 hfloor herr

/-- **The last scale survives every short weight.** Uniformly over all normalized mollifiers `Ψ` and all
short weights `W`, with `w_1 = 1`, `|w_m| ≤ 1`, `yz ≤ V^θ`, `z ≤ V^{(½−θ)/4}`,
`∫_V^{2V} |ζΨ − 1|² |W|² ≥ (e^{−2}/12) (e^{−2θa}/a) V Σ_{m≤z} |c_m|² m^{−2σ}`, `c = 1 ⋆ b ⋆ w`. -/
theorem exists_eventually_weighted_shiftedDefect_ge {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1 / 2) :
    ∃ K : ℝ, 200000 ≤ K ∧ ∀ᶠ V : ℝ in atTop, ∀ a : ℝ, 4 ≤ a →
      K / Real.log V ≤ Real.exp (-(2 * θ * a)) / a →
      ∀ y z : ℕ, 1 ≤ y → 1 ≤ z → (y : ℝ) * z ≤ V ^ θ → (z : ℝ) ≤ V ^ ((1 / 2 - θ) / 4) →
      ∀ b w : ℕ → ℂ, b 1 = 1 → (∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1) → w 1 = 1 →
        (∀ m ∈ Finset.Icc 1 z, ‖w m‖ ≤ 1) →
        Real.exp (-2) / 12 * (Real.exp (-(2 * θ * a)) / a) *
            weightEnergy b w y z (1 / 2 + a / Real.log V) * V ≤
          ∫ t in V..(2 * V),
            ‖(riemannZeta (((1 / 2 + a / Real.log V : ℝ) : ℂ) + (t : ℂ) * I) *
                edPoly b (Finset.Icc 1 y) (((1 / 2 + a / Real.log V : ℝ) : ℂ) + (t : ℂ) * I) - 1) *
              edPoly w (Finset.Icc 1 z) (((1 / 2 + a / Real.log V : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hE0 := mertensError_pos
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 200000 + 96 * mertensError / θ := ⟨_, rfl⟩
  have hK2 : 200000 ≤ K := by
    have : 0 ≤ 96 * mertensError / θ := by positivity
    rw [hK]
    linarith
  have hKθ : 96 * mertensError ≤ K * θ := by
    have h : 96 * mertensError / θ ≤ K := by
      rw [hK]
      linarith
    rwa [div_le_iff₀ hθ0] at h
  refine ⟨K, hK2, ?_⟩
  have hsup := eventually_exp_mul_exp_neg_exp_le (k := 7) (C := 1 / 128) (δ := 1 / 8)
    (ε := 1 / (99 * 1152)) (by norm_num) (by norm_num) (by norm_num)
  have hlogo := (isLittleO_log_rpow_atTop (show 0 < (1 / 2 - θ) / 2 by linarith)).bound
    (show (0 : ℝ) < 1 / (72 * 192) by norm_num)
  filter_upwards [Real.tendsto_log_atTop.eventually hsup,
    Real.tendsto_log_atTop.eventually_ge_atTop (128 + 8 / θ), hlogo, eventually_ge_atTop 16]
    with V hsupV hLV hlogV hV16 a ha hgL y z hy hz hyz hzle b w hb1 hb hw1 hw
  have hV0 : 0 < V := by linarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log V := ⟨_, rfl⟩
  rw [← hL] at hsupV hLV hgL hlogV ⊢
  have h8θ : 0 ≤ 8 / θ := by positivity
  have hL128 : 128 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have ha0 : 0 < a := by linarith
  have hexpL : Real.exp L = V := by
    rw [hL, Real.exp_log hV0]
  have hgle : Real.exp (-(2 * θ * a)) / a ≤ 1 / a :=
    div_le_div_of_nonneg_right (Real.exp_le_one_iff.mpr (by nlinarith)) ha0.le
  have hKa : K * a ≤ L := by
    have h1 : K / L ≤ 1 / a := hgL.trans hgle
    rwa [div_le_div_iff₀ hL0 ha0, one_mul] at h1
  have hθL : 1 ≤ θ * L := by
    have h1 : 8 / θ ≤ L := by linarith
    rw [div_le_iff₀ hθ0] at h1
    nlinarith
  have hCm : 12 * mertensError * a ≤ θ * L := by
    have h1 : (K * θ) * a ≤ L * θ := by
      have := mul_le_mul_of_nonneg_right hKa hθ0.le
      nlinarith
    nlinarith
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = Real.exp (-2) * (Real.exp (-(2 * θ * a)) / a) * (1 / 6) := ⟨_, rfl⟩
  have hlogV2 : 72 * 192 * L ≤ V ^ ((1 / 2 - θ) / 2) := by
    simp only [Real.norm_eq_abs] at hlogV
    rw [abs_of_pos hL0, abs_of_pos (by positivity)] at hlogV
    have := mul_le_mul_of_nonneg_left hlogV (show (0 : ℝ) ≤ 72 * 192 by norm_num)
    have e : (72 * 192 : ℝ) * (1 / (72 * 192) * V ^ ((1 / 2 - θ) / 2)) = V ^ ((1 / 2 - θ) / 2) := by
      field_simp
    linarith
  have hmain := weighted_defect_ge_of_scale hθ0 hθ ha hL128 hKa hK2 hθL hCm hy hz
    (by rw [hexpL]; exact hyz) (by rw [hexpL]; exact hzle) hb1 hb hw1 hw hm hgL hsupV
    (by rw [hexpL]; exact hlogV2)
  rw [hexpL] at hmain
  have e0 : Real.exp (-2) / 12 * (Real.exp (-(2 * θ * a)) / a) = m / 2 := by
    rw [hm]
    ring
  rw [e0]
  refine hmain.trans (le_of_eq ?_)
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [edPoly_polyConv, sub_mul, one_mul, mul_assoc]

/-- **No short weight lowers the defect.** A mollifier cancelling the prefix up to `z` keeps its defect above the
floor on average against the probability density `|W|²/∫|W|²`: the energy is the mean square
`Σ_{m≤z} |w_m|² m^{−2σ}` of `W`. -/
theorem exists_eventually_weighted_shiftedDefect_ge_of_prefix {θ : ℝ} (hθ0 : 0 < θ)
    (hθ : θ < 1 / 2) :
    ∃ K : ℝ, 200000 ≤ K ∧ ∀ᶠ V : ℝ in atTop, ∀ a : ℝ, 4 ≤ a →
      K / Real.log V ≤ Real.exp (-(2 * θ * a)) / a →
      ∀ y z : ℕ, 1 ≤ y → 1 ≤ z → (y : ℝ) * z ≤ V ^ θ → (z : ℝ) ≤ V ^ ((1 / 2 - θ) / 4) →
      ∀ b w : ℕ → ℂ, b 1 = 1 → (∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1) →
        (∀ k ∈ Finset.Icc 2 z, mollifiedZetaCoeff b y k = 0) → w 1 = 1 →
        (∀ m ∈ Finset.Icc 1 z, ‖w m‖ ≤ 1) →
        Real.exp (-2) / 12 * (Real.exp (-(2 * θ * a)) / a) *
            (∑ m ∈ Finset.Icc 1 z, ‖w m‖ ^ 2 * (m : ℝ) ^ (-2 * (1 / 2 + a / Real.log V))) * V ≤
          ∫ t in V..(2 * V),
            ‖(riemannZeta (((1 / 2 + a / Real.log V : ℝ) : ℂ) + (t : ℂ) * I) *
                edPoly b (Finset.Icc 1 y) (((1 / 2 + a / Real.log V : ℝ) : ℂ) + (t : ℂ) * I) - 1) *
              edPoly w (Finset.Icc 1 z) (((1 / 2 + a / Real.log V : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  obtain ⟨K, hK2, h⟩ := exists_eventually_weighted_shiftedDefect_ge hθ0 hθ
  refine ⟨K, hK2, ?_⟩
  filter_upwards [h] with V hV a ha hgL y z hy hz hyz hzle b w hb1 hb hprefix hw1 hw
  have hE : weightEnergy b w y z (1 / 2 + a / Real.log V) =
      ∑ m ∈ Finset.Icc 1 z, ‖w m‖ ^ 2 * (m : ℝ) ^ (-2 * (1 / 2 + a / Real.log V)) := by
    unfold weightEnergy
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [mollifiedZetaCoeff_polyConv_of_prefix hy hb1 hprefix hm]
  rw [← hE]
  exact hV a ha hgL y z hy hz hyz hzle b w hb1 hb hw1 hw

end GaloisForLFunctions.MultiscaleMollifiedZetaField
