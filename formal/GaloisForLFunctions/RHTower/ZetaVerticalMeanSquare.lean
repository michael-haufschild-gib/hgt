import GaloisForLFunctions.RHTower.SelbergNearLineWindowBounds
import GaloisForLFunctions.RHTower.Sieve.InghamCriticalGlobalErrorMomentPolylog
import GaloisForLFunctions.HTGeometry.StripSquareMeanConvexity

/-!
# Mean squares of `ζ` on vertical lines of the strip

For `½ ≤ σ ≤ 3`,

  `∫_T^{2T} |ζ(σ + it)|² dt ≤ C T (1 + log T)³`   for all large `T`
  (`exists_integral_normSq_zeta_vertical_le`).

The field `F(z) = exp((z − iτ)²/H²) · (z − 1)ζ(z)/z` is holomorphic on `Re z > 0` and bounded on the
strip `½ ≤ Re z ≤ 3`. On the right edge `|ζ(3 + iu)| ≤ π²/6`, so every window carries mass
`O(H)`. On the critical line the mass inside `[−N, N]` is at most the critical mean square, which
Cauchy–Schwarz bounds by the fourth moment (`Sieve.exists_inghamCriticalZetaFourthMoment…`); outside
`[−N, N]` the Gaussian beats the linear growth of `ζ`. The L² three-lines lemma
(`HTGeometry.integral_normSq_le_of_three_lines`) interpolates, and on the window `|t − τ| ≤ H/8`,
`|t| ≥ 2`, the field dominates `ζ` up to a constant. With `τ = 3T/2`, `H = 8T` and
`N ≈ 16T(1 + log T)` the Gaussian tail is `O(T^{−3})`.
-/

noncomputable section

open Complex Set MeasureTheory

namespace RHTower

/-! ## The pole-cleared zeta and its window field -/

/-- The pole-cleared zeta `(z − 1)ζ(z)/z`. -/
def zetaPoleCleared (z : ℂ) : ℂ := zetaEntire z / z

theorem differentiableOn_zetaPoleCleared :
    DifferentiableOn ℂ zetaPoleCleared {z : ℂ | 0 < z.re} :=
  differentiable_zetaEntire.differentiableOn.div differentiableOn_id fun z hz h => by
    rw [h] at hz; simp at hz

theorem zetaPoleCleared_eq {z : ℂ} (hz1 : z ≠ 1) :
    zetaPoleCleared z = (z - 1) / z * riemannZeta z := by
  unfold zetaPoleCleared
  rw [zetaEntire_eq hz1]
  ring

/-- **Linear growth on the strip.** -/
theorem exists_norm_zetaPoleCleared_le :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 3 → ‖zetaPoleCleared z‖ ≤ C * (1 + |z.im|) := by
  set K : Set ℂ := (Icc (1 / 2 : ℝ) 3) ×ℂ (Icc (-2 : ℝ) 2) with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn zetaPoleCleared K := by
    refine differentiableOn_zetaPoleCleared.continuousOn.mono fun z hz => ?_
    have := (Complex.mem_reProdIm.mp hz).1
    show 0 < z.re
    linarith [this.1]
  obtain ⟨CZ, hCZ⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨max CZ 0 + 10, by positivity, fun z hz hz' => ?_⟩
  have hab := abs_nonneg z.im
  have hCZ0 := le_max_left CZ 0
  have hCZ1 := le_max_right CZ 0
  rcases le_or_gt |z.im| 2 with h | h
  · have hzK : z ∈ K := Complex.mem_reProdIm.mpr ⟨⟨hz, hz'⟩, abs_le.mp h⟩
    have h1 := hCZ z hzK
    nlinarith
  · have hz1 : z ≠ 1 := by intro h1; rw [h1] at h; simp at h; linarith
    rw [zetaPoleCleared_eq hz1, norm_mul]
    have h1 := norm_sub_one_div_le_one hz
    have h2 := norm_riemannZeta_le_quarter (by linarith) h.le
    calc ‖(z - 1) / z‖ * ‖riemannZeta z‖ ≤ 1 * (2 + 8 * |z.im|) :=
          mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ ≤ (max CZ 0 + 10) * (1 + |z.im|) := by nlinarith

/-- The window field `exp((z − iτ)²/H²)(z − 1)ζ(z)/z`. -/
def zetaWindowField (H τ : ℝ) (z : ℂ) : ℂ := nearLineGauss H τ z * zetaPoleCleared z

theorem differentiableOn_zetaWindowField (H τ : ℝ) :
    DifferentiableOn ℂ (zetaWindowField H τ) {z : ℂ | 0 < z.re} :=
  (differentiable_nearLineGauss H τ).differentiableOn.mul differentiableOn_zetaPoleCleared

theorem continuous_zetaWindowField_line (H τ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Continuous fun u : ℝ => zetaWindowField H τ ((σ : ℂ) + (u : ℂ) * I) := by
  refine (differentiableOn_zetaWindowField H τ).continuousOn.comp_continuous (by fun_prop)
    fun u => ?_
  show 0 < ((σ : ℂ) + (u : ℂ) * I).re
  simpa using hσ

/-- **The field is bounded on the strip.** -/
theorem norm_zetaWindowField_le_strip {C : ℝ} (hC : 0 < C)
    (hgrowth : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 3 → ‖zetaPoleCleared z‖ ≤ C * (1 + |z.im|))
    {H : ℝ} (hH : 3 ≤ H) (τ : ℝ) {z : ℂ} (hz : 1 / 2 ≤ z.re) (hz' : z.re ≤ 3) :
    ‖zetaWindowField H τ z‖ ≤ Real.exp 1 * (C * (1 + |τ| + H)) := by
  have hH0 : 0 < H := by linarith
  have hG := norm_nearLineGauss_le (τ := τ) hH (z := z) (abs_le.mpr ⟨by linarith, hz'⟩)
  have hf := hgrowth z hz hz'
  set x : ℝ := z.im - τ with hx
  have hkey : (1 + |z.im|) * Real.exp (-(x ^ 2 / H ^ 2)) ≤ 1 + |τ| + H := by
    have h1 : |z.im| ≤ |τ| + |x| := by
      have := abs_add_le τ x
      rwa [show τ + x = z.im by rw [hx]; ring] at this
    have h2 := mul_exp_neg_sq_div_le (x := |x|) (abs_nonneg x) hH0
    rw [sq_abs] at h2
    have hE1 : Real.exp (-(x ^ 2 / H ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have : 0 ≤ x ^ 2 / H ^ 2 := by positivity
      linarith)
    have hE0 : 0 ≤ Real.exp (-(x ^ 2 / H ^ 2)) := (Real.exp_pos _).le
    calc (1 + |z.im|) * Real.exp (-(x ^ 2 / H ^ 2))
        ≤ (1 + |τ|) * Real.exp (-(x ^ 2 / H ^ 2)) + |x| * Real.exp (-(x ^ 2 / H ^ 2)) := by
          nlinarith
      _ ≤ (1 + |τ|) * 1 + H := by
          have := mul_le_mul_of_nonneg_left hE1 (by positivity : (0 : ℝ) ≤ 1 + |τ|)
          linarith
      _ = 1 + |τ| + H := by ring
  unfold zetaWindowField
  rw [norm_mul]
  calc ‖nearLineGauss H τ z‖ * ‖zetaPoleCleared z‖
      ≤ Real.exp 1 * Real.exp (-((z.im - τ) ^ 2 / H ^ 2)) * (C * (1 + |z.im|)) :=
        mul_le_mul hG hf (norm_nonneg _) (by positivity)
    _ = Real.exp 1 * (C * ((1 + |z.im|) * Real.exp (-(x ^ 2 / H ^ 2)))) := by rw [hx]; ring
    _ ≤ Real.exp 1 * (C * (1 + |τ| + H)) := by gcongr

/-! ## The edges -/

/-- The Gaussian mass of any window. -/
theorem intervalIntegral_gauss_le {a b : ℝ} (hab : a ≤ b) {c : ℝ} (hc : 0 < c) (τ : ℝ) :
    ∫ t in a..b, Real.exp (-c * (t - τ) ^ 2) ≤ Real.sqrt (Real.pi / c) := by
  have hint : Integrable (fun t : ℝ => Real.exp (-c * (t - τ) ^ 2)) :=
    (integrable_exp_neg_mul_sq hc).comp_sub_right τ
  rw [intervalIntegral.integral_of_le hab]
  refine (setIntegral_le_integral hint
    (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le)).trans (le_of_eq ?_)
  rw [integral_sub_right_eq_self (fun t => Real.exp (-c * t ^ 2)) τ, integral_gaussian]

/-- **Right edge.** Every window on `Re z = 3` carries mass at most `4e²√(πH²/2)`. -/
theorem integral_zetaWindowField_three_le {H : ℝ} (hH : 3 ≤ H) (τ : ℝ) {A B : ℝ} (hAB : A ≤ B)
    (y : ℝ) :
    ∫ t in A..B, ‖zetaWindowField H τ (((3 : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤
      4 * Real.exp 1 ^ 2 * Real.sqrt (Real.pi / (2 / H ^ 2)) := by
  have hH0 : 0 < H := by linarith
  have hpt : ∀ t : ℝ, ‖zetaWindowField H τ (((3 : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤
      4 * Real.exp 1 ^ 2 * Real.exp (-(2 / H ^ 2) * (t - (τ - y)) ^ 2) := by
    intro t
    set z : ℂ := ((3 : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I with hz
    have hzre : z.re = 3 := by simp [hz]
    have hzim : z.im = y + t := by simp [hz]
    have hz1 : z ≠ 1 := by intro h; rw [h] at hzre; norm_num at hzre
    have hZ : ‖zetaPoleCleared z‖ ≤ 2 := by
      rw [zetaPoleCleared_eq hz1, norm_mul]
      have h1 := norm_sub_one_div_le_one (z := z) (by rw [hzre]; norm_num)
      have h2 := norm_riemannZeta_le_of_two_le_re (s := z) (by rw [hzre]; norm_num)
      have hpi : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_gt_three]
      calc ‖(z - 1) / z‖ * ‖riemannZeta z‖ ≤ 1 * 2 :=
            mul_le_mul h1 (h2.trans hpi) (norm_nonneg _) zero_le_one
        _ = 2 := by ring
    have hG : ‖nearLineGauss H τ z‖ ^ 2 ≤ Real.exp 1 ^ 2 *
        Real.exp (-(2 / H ^ 2) * (t - (τ - y)) ^ 2) := by
      rw [norm_nearLineGauss_eq, hzre, hzim, ← Real.exp_nat_mul, ← Real.exp_nat_mul,
        ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hH9 : 9 ≤ H ^ 2 := by nlinarith
      have e : ((2 : ℕ) : ℝ) * ((3 ^ 2 - (y + t - τ) ^ 2) / H ^ 2)
          = 18 / H ^ 2 + -(2 / H ^ 2) * (t - (τ - y)) ^ 2 := by push_cast; field_simp; ring
      rw [e]
      have h18 : 18 / H ^ 2 ≤ 2 := by rw [div_le_iff₀ (by positivity)]; nlinarith
      push_cast
      linarith
    unfold zetaWindowField
    rw [norm_mul, mul_pow]
    calc ‖nearLineGauss H τ z‖ ^ 2 * ‖zetaPoleCleared z‖ ^ 2
        ≤ (Real.exp 1 ^ 2 * Real.exp (-(2 / H ^ 2) * (t - (τ - y)) ^ 2)) * 2 ^ 2 :=
          mul_le_mul hG (pow_le_pow_left₀ (norm_nonneg _) hZ 2) (by positivity) (by positivity)
      _ = 4 * Real.exp 1 ^ 2 * Real.exp (-(2 / H ^ 2) * (t - (τ - y)) ^ 2) := by ring
  have hc : (0 : ℝ) < 2 / H ^ 2 := by positivity
  have hcont : Continuous fun t : ℝ =>
      ‖zetaWindowField H τ (((3 : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 := by
    have h := continuous_zetaWindowField_line H τ (σ := 3) (by norm_num)
    exact (h.comp (continuous_const.add continuous_id : Continuous fun t : ℝ => y + t)).norm.pow 2
  calc ∫ t in A..B, ‖zetaWindowField H τ (((3 : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2
      ≤ ∫ t in A..B, 4 * Real.exp 1 ^ 2 * Real.exp (-(2 / H ^ 2) * (t - (τ - y)) ^ 2) :=
        intervalIntegral.integral_mono_on hAB (hcont.intervalIntegrable A B)
          ((Continuous.intervalIntegrable (by fun_prop) A B)) fun t _ => hpt t
    _ = 4 * Real.exp 1 ^ 2 * ∫ t in A..B, Real.exp (-(2 / H ^ 2) * (t - (τ - y)) ^ 2) :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ 4 * Real.exp 1 ^ 2 * Real.sqrt (Real.pi / (2 / H ^ 2)) :=
        mul_le_mul_of_nonneg_left (intervalIntegral_gauss_le hAB hc _) (by positivity)

/-- **The critical mean square from the fourth moment.** -/
theorem exists_integral_normSq_zeta_critical_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {N : ℕ}, 4 ≤ N →
      ∫ t in (-(N : ℝ))..(N : ℝ), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        D * N * (1 + Real.log N) ^ 2 := by
  obtain ⟨D, hD, hbound⟩ := Sieve.exists_inghamCriticalZetaFourthMoment_symmetric_nat_le_polylog
  refine ⟨Real.sqrt (2 * (D + 1)), Real.sqrt_nonneg _, fun {N} hN => ?_⟩
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hcz : Continuous fun t : ℝ => riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hne : (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this
    exact ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
      (differentiableAt_riemannZeta hne).continuousAt (by fun_prop)
  have h4 : ∫ t in (-(N : ℝ))..(N : ℝ), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 4 ≤
      D * N * (1 + Real.log N) ^ 4 := by
    have hb := hbound hN
    have heq : Sieve.inghamCriticalZetaFourthMoment (-(N : ℝ)) (N : ℝ) =
        ∫ t in (-(N : ℝ))..(N : ℝ), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 4 := by
      unfold Sieve.inghamCriticalZetaFourthMoment
      rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      have hpt : Sieve.inghamCriticalPoint t = ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I := by
        unfold Sieve.inghamCriticalPoint; push_cast; ring
      simp only [hpt]
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [← heq]
    exact hb
  set SA : ℝ := (D + 1) * N * (1 + Real.log N) ^ 4 with hSA
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hSA0 : 0 < SA := by positivity
  have hfS : ∫ t in (-(N : ℝ))..(N : ℝ),
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ^ 2‖ ^ 2 ≤ SA := by
    have e : ∀ t : ℝ, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ^ 2‖ ^ 2 =
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 4 := by
      intro t; rw [norm_pow]; ring
    simp_rw [e]
    refine h4.trans ?_
    have : D * N * (1 + Real.log N) ^ 4 ≤ (D + 1) * N * (1 + Real.log N) ^ 4 := by
      have : 0 ≤ (N : ℝ) * (1 + Real.log N) ^ 4 := by positivity
      nlinarith
    linarith
  have hCS := GaloisForLFunctions.HTGeometry.integral_norm_mul_le_sqrt_of_bound
    (f := fun t : ℝ => riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ^ 2)
    (g := fun _ : ℝ => (1 : ℂ)) (A := -(N : ℝ)) (B := N) (by linarith) (hcz.pow 2)
    continuous_const hSA0 hfS
  simp only [norm_pow, norm_one, one_pow, intervalIntegral.integral_const, smul_eq_mul, mul_one]
    at hCS
  refine hCS.trans ?_
  have hlen : N - -(N : ℝ) = 2 * N := by ring
  rw [hlen]
  have e2 : SA * (2 * N) = (2 * (D + 1)) * ((N : ℝ) * (1 + Real.log N) ^ 2) ^ 2 := by
    rw [hSA]; ring
  rw [e2, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  exact le_of_eq (by ring)

/-- **Left edge, pointwise.** On `Re z = ½`, the squared field is at most `e` times the squared zeta
inside `[−N, N]`, and at most a Gaussian tail outside, once `|τ| + R₀ ≤ N`. -/
theorem normSq_zetaWindowField_half_le {H τ R₀ : ℝ} (hH : 3 ≤ H) {N : ℕ} (hN : 4 ≤ N)
    (hR₀ : 0 ≤ R₀) (hNR : |τ| + R₀ ≤ N) (u : ℝ) :
    ‖zetaWindowField H τ (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤
      Real.exp 1 * (Icc (-(N : ℝ)) N).indicator
          (fun v => ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖ ^ 2) u
        + Real.exp 1 * (64 * Real.exp (-(R₀ ^ 2 / H ^ 2)) * (2 * (1 + |τ|) ^ 2 + 2 * H ^ 2)) := by
  have hH0 : 0 < H := by linarith
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  set z : ℂ := ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I with hz
  have hzre : z.re = 1 / 2 := by simp [hz]
  have hzim : z.im = u := by simp [hz]
  have hz1 : z ≠ 1 := by intro h; rw [h] at hzre; norm_num at hzre
  have hP : ‖zetaPoleCleared z‖ ≤ ‖riemannZeta z‖ := by
    rw [zetaPoleCleared_eq hz1, norm_mul]
    have h1 := norm_sub_one_div_le_one (z := z) (by rw [hzre])
    calc ‖(z - 1) / z‖ * ‖riemannZeta z‖ ≤ 1 * ‖riemannZeta z‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖riemannZeta z‖ := one_mul _
  have hG : ‖nearLineGauss H τ z‖ ^ 2 ≤ Real.exp 1 * Real.exp (-(2 * (u - τ) ^ 2 / H ^ 2)) := by
    rw [norm_nearLineGauss_eq, hzre, hzim, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hH9 : 9 ≤ H ^ 2 := by nlinarith
    have e : ((2 : ℕ) : ℝ) * ((((1 : ℝ) / 2) ^ 2 - (u - τ) ^ 2) / H ^ 2)
        = 1 / (2 * H ^ 2) - 2 * (u - τ) ^ 2 / H ^ 2 := by push_cast; field_simp
    have h1 : 1 / (2 * H ^ 2) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    rw [e]
    linarith
  have hfu : ‖zetaWindowField H τ z‖ ^ 2 ≤
      Real.exp 1 * Real.exp (-(2 * (u - τ) ^ 2 / H ^ 2)) * ‖riemannZeta z‖ ^ 2 := by
    unfold zetaWindowField
    rw [norm_mul, mul_pow]
    exact mul_le_mul hG (pow_le_pow_left₀ (norm_nonneg _) hP 2) (by positivity) (by positivity)
  have hE1 : Real.exp (-(2 * (u - τ) ^ 2 / H ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  set Tc : ℝ := 64 * Real.exp (-(R₀ ^ 2 / H ^ 2)) * (2 * (1 + |τ|) ^ 2 + 2 * H ^ 2) with hTc
  have hTc0 : 0 ≤ Real.exp 1 * Tc := by positivity
  by_cases hu : u ∈ Icc (-(N : ℝ)) N
  · rw [Set.indicator_of_mem hu]
    have h1 : Real.exp 1 * Real.exp (-(2 * (u - τ) ^ 2 / H ^ 2)) * ‖riemannZeta z‖ ^ 2 ≤
        Real.exp 1 * ‖riemannZeta z‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hE1 (Real.exp_pos 1).le
      have h2 := sq_nonneg ‖riemannZeta z‖
      calc Real.exp 1 * Real.exp (-(2 * (u - τ) ^ 2 / H ^ 2)) * ‖riemannZeta z‖ ^ 2
          ≤ Real.exp 1 * 1 * ‖riemannZeta z‖ ^ 2 := mul_le_mul_of_nonneg_right this h2
        _ = Real.exp 1 * ‖riemannZeta z‖ ^ 2 := by ring
    linarith
  · rw [Set.indicator_of_notMem hu, mul_zero, zero_add]
    have huN : (N : ℝ) < |u| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    set x : ℝ := u - τ with hx
    have hxR : R₀ ≤ |x| := by
      have := abs_sub_abs_le_abs_sub u τ
      rw [← hx] at this
      linarith
    have hζ : ‖riemannZeta z‖ ≤ 8 * (1 + |u|) := by
      have := norm_riemannZeta_le_quarter (s := z) (by rw [hzre]; norm_num)
        (by rw [hzim]; linarith)
      rw [hzim] at this
      linarith [abs_nonneg u]
    have hu2 : (1 + |u|) ^ 2 ≤ 2 * (1 + |τ|) ^ 2 + 2 * x ^ 2 := by
      have h1 : |u| ≤ |τ| + |x| := by
        have := abs_add_le τ x
        rwa [show τ + x = u by rw [hx]; ring] at this
      have h2 : (1 + |u|) ^ 2 ≤ ((1 + |τ|) + |x|) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      nlinarith [sq_abs x, sq_nonneg ((1 + |τ|) - |x|)]
    have hsplit : Real.exp (-(2 * x ^ 2 / H ^ 2)) ≤
        Real.exp (-(R₀ ^ 2 / H ^ 2)) * Real.exp (-(x ^ 2 / H ^ 2)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hR2 : R₀ ^ 2 ≤ x ^ 2 := by
        rw [← sq_abs x]; exact pow_le_pow_left₀ hR₀ hxR 2
      have : R₀ ^ 2 / H ^ 2 ≤ x ^ 2 / H ^ 2 := div_le_div_of_nonneg_right hR2 (by positivity)
      have e : 2 * x ^ 2 / H ^ 2 = x ^ 2 / H ^ 2 + x ^ 2 / H ^ 2 := by ring
      rw [e]
      linarith
    have hsq := sq_mul_exp_neg_sq_div_le (x := x) hH0
    have hE1' : Real.exp (-(x ^ 2 / H ^ 2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    have hkey : (2 * (1 + |τ|) ^ 2 + 2 * x ^ 2) * Real.exp (-(x ^ 2 / H ^ 2)) ≤
        2 * (1 + |τ|) ^ 2 + 2 * H ^ 2 := by
      have := mul_le_mul_of_nonneg_left hE1' (by positivity : (0 : ℝ) ≤ 2 * (1 + |τ|) ^ 2)
      linarith
    have hζ2 : ‖riemannZeta z‖ ^ 2 ≤ 64 * (2 * (1 + |τ|) ^ 2 + 2 * x ^ 2) := by
      calc ‖riemannZeta z‖ ^ 2 ≤ (8 * (1 + |u|)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hζ 2
        _ = 64 * (1 + |u|) ^ 2 := by ring
        _ ≤ 64 * (2 * (1 + |τ|) ^ 2 + 2 * x ^ 2) := by linarith
    refine hfu.trans ?_
    set Ex := Real.exp (-(x ^ 2 / H ^ 2)) with hEx
    set ER := Real.exp (-(R₀ ^ 2 / H ^ 2)) with hER
    set Q := 2 * (1 + |τ|) ^ 2 + 2 * x ^ 2 with hQ
    have hEx0 : 0 ≤ Ex := (Real.exp_pos _).le
    have hER0 : 0 ≤ ER := (Real.exp_pos _).le
    calc Real.exp 1 * Real.exp (-(2 * x ^ 2 / H ^ 2)) * ‖riemannZeta z‖ ^ 2
        ≤ Real.exp 1 * (ER * Ex) * (64 * Q) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsplit (Real.exp_pos 1).le) hζ2
            (sq_nonneg _) (by positivity)
      _ = Real.exp 1 * (64 * ER * (Q * Ex)) := by ring
      _ ≤ Real.exp 1 * Tc := by
          rw [hTc]
          gcongr

/-- **Left edge.** On `Re z = ½`, every window carries at most `e` times the critical mean
square over `[−N, N]` plus a Gaussian tail, once `|τ| + R₀ ≤ N`. -/
theorem integral_zetaWindowField_half_le {H τ R₀ I₀ : ℝ} (hH : 3 ≤ H) {N : ℕ} (hN : 4 ≤ N)
    (hR₀ : 0 ≤ R₀) (hNR : |τ| + R₀ ≤ N)
    (hI : ∫ u in (-(N : ℝ))..(N : ℝ), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤ I₀)
    {A B : ℝ} (hAB : A ≤ B) (y : ℝ) :
    ∫ t in A..B, ‖zetaWindowField H τ (((1 / 2 : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤
      Real.exp 1 * I₀ + (B - A) * (Real.exp 1 * (64 * Real.exp (-(R₀ ^ 2 / H ^ 2))
        * (2 * (1 + |τ|) ^ 2 + 2 * H ^ 2))) := by
  set g : ℝ → ℝ := fun v => ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖ ^ 2 with hg
  set f : ℝ → ℝ := fun u => ‖zetaWindowField H τ (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 with hf
  set c : ℝ := Real.exp 1 * (64 * Real.exp (-(R₀ ^ 2 / H ^ 2)) * (2 * (1 + |τ|) ^ 2 + 2 * H ^ 2))
    with hc
  have hc0 : 0 ≤ c := by positivity
  have hcz : Continuous fun u : ℝ => riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hne : (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this
    exact ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
      (differentiableAt_riemannZeta hne).continuousAt (by fun_prop)
  have hgc : Continuous g := hcz.norm.pow 2
  have hfc : Continuous f := (continuous_zetaWindowField_line H τ (by norm_num)).norm.pow 2
  have hpt : ∀ u : ℝ, f u ≤ Real.exp 1 * (Icc (-(N : ℝ)) N).indicator g u + c :=
    fun u => normSq_zetaWindowField_half_le hH hN hR₀ hNR u
  have hAB' : y + A ≤ y + B := by linarith
  have hind_int : IntervalIntegrable ((Icc (-(N : ℝ)) N).indicator g) volume (y + A) (y + B) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hAB').mpr
      ((hgc.integrableOn_Icc (a := -(N : ℝ)) (b := N)).integrable_indicator
        measurableSet_Icc).integrableOn
  have hlhs : ∫ t in A..B, ‖zetaWindowField H τ (((1 / 2 : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2
      = ∫ u in (y + A)..(y + B), f u :=
    intervalIntegral.integral_comp_add_left f y (a := A) (b := B)
  rw [hlhs]
  have hmono : ∫ u in (y + A)..(y + B), f u ≤
      ∫ u in (y + A)..(y + B), (Real.exp 1 * (Icc (-(N : ℝ)) N).indicator g u + c) :=
    intervalIntegral.integral_mono_on hAB' (hfc.intervalIntegrable _ _)
      ((hind_int.const_mul _).add intervalIntegrable_const) fun u _ => hpt u
  have hsplit : ∫ u in (y + A)..(y + B), (Real.exp 1 * (Icc (-(N : ℝ)) N).indicator g u + c)
      = Real.exp 1 * (∫ u in (y + A)..(y + B), (Icc (-(N : ℝ)) N).indicator g u) + (B - A) * c := by
    rw [intervalIntegral.integral_add (hind_int.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hind : ∫ u in (y + A)..(y + B), (Icc (-(N : ℝ)) N).indicator g u ≤ I₀ := by
    rw [intervalIntegral.integral_of_le hAB', setIntegral_indicator measurableSet_Icc]
    refine le_trans ?_ hI
    have hN0 : -(N : ℝ) ≤ N := by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith
    rw [intervalIntegral.integral_of_le hN0, ← integral_Icc_eq_integral_Ioc]
    exact setIntegral_mono_set (hgc.integrableOn_Icc)
      (Filter.Eventually.of_forall fun v => by simp only [hg]; positivity)
      (Filter.Eventually.of_forall inter_subset_right)
  rw [hsplit] at hmono
  refine hmono.trans ?_
  have := mul_le_mul_of_nonneg_left hind (Real.exp_pos 1).le
  linarith

/-! ## Interpolation and the window -/

/-- **Three lines for the window field.** -/
theorem integral_normSq_zetaWindowField_le {C : ℝ} (hC : 0 < C)
    (hgrowth : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 3 → ‖zetaPoleCleared z‖ ≤ C * (1 + |z.im|))
    {H τ σ T₁ T₂ SL : ℝ} (hH : 3 ≤ H) (hσ : 1 / 2 ≤ σ) (hσ3 : σ ≤ 3) (hT : T₁ ≤ T₂)
    (hSL : 0 < SL)
    (hL : ∀ y : ℝ, ∫ t in T₁..T₂,
      ‖zetaWindowField H τ (((1 / 2 : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤ SL) :
    ∫ t in T₁..T₂, ‖zetaWindowField H τ ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      SL + 4 * Real.exp 1 ^ 2 * Real.sqrt (Real.pi / (2 / H ^ 2)) := by
  have hH0 : 0 < H := by linarith
  set SR : ℝ := 4 * Real.exp 1 ^ 2 * Real.sqrt (Real.pi / (2 / H ^ 2)) with hSR
  have hSR0 : 0 < SR := by
    have : 0 < Real.sqrt (Real.pi / (2 / H ^ 2)) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have hdiff : DiffContOnCl ℂ (zetaWindowField H τ)
      (Complex.HadamardThreeLines.verticalStrip (1 / 2) 3) := by
    apply DifferentiableOn.diffContOnCl
    rw [GaloisForLFunctions.HTGeometry.closure_verticalStrip (by norm_num)]
    refine (differentiableOn_zetaWindowField H τ).mono fun z hz => ?_
    have : z.re ∈ Icc (1 / 2 : ℝ) 3 := hz
    show 0 < z.re
    linarith [this.1]
  have hbound : ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip (1 / 2) 3,
      ‖zetaWindowField H τ z‖ ≤ Real.exp 1 * (C * (1 + |τ| + H)) := by
    intro z hz
    have : z.re ∈ Icc (1 / 2 : ℝ) 3 := hz
    exact norm_zetaWindowField_le_strip hC hgrowth hH τ this.1 this.2
  have hR : ∀ y : ℝ, ∫ t in T₁..T₂,
      ‖zetaWindowField H τ (((3 : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤ SR :=
    fun y => integral_zetaWindowField_three_le hH τ hT y
  have h3 := GaloisForLFunctions.HTGeometry.integral_normSq_le_of_three_lines
    (F := zetaWindowField H τ) (l := 1 / 2) (u := 3) (σ := σ) (A := T₁) (B := T₂) (by norm_num)
    hσ hσ3 hT hdiff hbound hSL hSR0 (by exact_mod_cast hL) (by exact_mod_cast hR)
  refine h3.trans ?_
  set w : ℝ := (σ - 1 / 2) / (3 - 1 / 2) with hw
  have hw0 : 0 ≤ w := div_nonneg (by linarith) (by norm_num)
  have hw1 : w ≤ 1 := by rw [hw, div_le_one (by norm_num)]; linarith
  have hAM := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 - w) (w₂ := w) (p₁ := SL) (p₂ := SR)
    (by linarith) hw0 hSL.le hSR0.le (by ring)
  have h1 : (1 - w) * SL ≤ SL := by nlinarith
  have h2 : w * SR ≤ SR := by nlinarith
  linarith

/-- **The field dominates `ζ` inside the window.** -/
theorem normSq_zeta_le_five_mul_window {H τ σ t : ℝ} (hH : 3 ≤ H) (ht2 : 2 ≤ |t|)
    (hwin : |t - τ| ≤ H / 8) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      5 * ‖zetaWindowField H τ ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hH0 : 0 < H := by linarith
  set z : ℂ := (σ : ℂ) + (t : ℂ) * I with hz
  have hzre : z.re = σ := by simp [hz]
  have hzim : z.im = t := by simp [hz]
  have hz1 : z ≠ 1 := by intro h; rw [h] at hzim; simp at hzim; rw [← hzim] at ht2; norm_num at ht2
  have hznorm : 2 ≤ ‖z‖ := le_trans ht2 (by rw [← hzim]; exact Complex.abs_im_le_norm z)
  have hz0 : 0 < ‖z‖ := by linarith
  have hq : 1 / 2 ≤ ‖(z - 1) / z‖ := by
    rw [norm_div, le_div_iff₀ hz0]
    have := norm_sub_norm_le z 1
    rw [norm_one] at this
    linarith
  have hG : Real.exp (-(1 / 64 : ℝ)) ≤ ‖nearLineGauss H τ z‖ := by
    rw [norm_nearLineGauss_eq, hzre, hzim]
    apply Real.exp_le_exp.mpr
    have h1 : (t - τ) ^ 2 ≤ (H / 8) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hwin 2
    have h2 : (t - τ) ^ 2 / H ^ 2 ≤ 1 / 64 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have h3 : 0 ≤ σ ^ 2 / H ^ 2 := by positivity
    have e : (σ ^ 2 - (t - τ) ^ 2) / H ^ 2 = σ ^ 2 / H ^ 2 - (t - τ) ^ 2 / H ^ 2 := by ring
    rw [e]
    linarith
  have hF : ‖zetaWindowField H τ z‖ = ‖nearLineGauss H τ z‖ * (‖(z - 1) / z‖ * ‖riemannZeta z‖) := by
    unfold zetaWindowField
    rw [zetaPoleCleared_eq hz1, norm_mul, norm_mul]
  have hexp : 63 / 64 ≤ Real.exp (-(1 / 64 : ℝ)) := by
    have := Real.add_one_le_exp (-(1 / 64 : ℝ))
    linarith
  have hlow : 63 / 128 * ‖riemannZeta z‖ ≤ ‖zetaWindowField H τ z‖ := by
    rw [hF]
    have hζ0 := norm_nonneg (riemannZeta z)
    calc 63 / 128 * ‖riemannZeta z‖ = 63 / 64 * (1 / 2 * ‖riemannZeta z‖) := by ring
      _ ≤ ‖nearLineGauss H τ z‖ * (‖(z - 1) / z‖ * ‖riemannZeta z‖) :=
          mul_le_mul (hexp.trans hG) (mul_le_mul_of_nonneg_right hq hζ0) (by positivity)
            (norm_nonneg _)
  have := pow_le_pow_left₀ (by positivity) hlow 2
  nlinarith [sq_nonneg ‖riemannZeta z‖]

/-! ## The bound with explicit parameters -/

theorem log_seventeen_lt_three : Real.log 17 < 3 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have he := Real.exp_one_gt_d9
  have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  nlinarith [sq_nonneg (Real.exp 1)]

theorem sqrt_gauss_mass_le {H : ℝ} (hH : 0 < H) :
    4 * Real.exp 1 ^ 2 * Real.sqrt (Real.pi / (2 / H ^ 2)) ≤ 300 * H / 8 := by
  have e : Real.pi / (2 / H ^ 2) = (Real.pi / 2) * H ^ 2 := by field_simp
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq hH.le]
  have hs : Real.sqrt (Real.pi / 2) ≤ 1.26 := by
    rw [Real.sqrt_le_left (by norm_num)]
    have := Real.pi_lt_d2
    linarith
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have he2 : Real.exp 1 ^ 2 ≤ 7.39 := by nlinarith
  have hs0 := Real.sqrt_nonneg (Real.pi / 2)
  calc 4 * Real.exp 1 ^ 2 * (Real.sqrt (Real.pi / 2) * H) ≤ 4 * 7.39 * (1.26 * H) := by gcongr
    _ ≤ 300 * H / 8 := by nlinarith

/-- The logarithm of the cut-off height. -/
theorem one_add_log_cutoff_le {T : ℝ} (hT : 2 ≤ T) {N : ℕ} (hN4 : 4 ≤ N)
    (hN2 : (N : ℝ) ≤ 16 * T * (1 + Real.log T) + 1) :
    1 + Real.log N ≤ 4 * (1 + Real.log T) := by
  have hT0 : 0 < T := by linarith
  have hL0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hTL : 1 ≤ T * (1 + Real.log T) := by nlinarith
  have hNpos : (0 : ℝ) < N := by have : (4 : ℝ) ≤ N := by exact_mod_cast hN4
                                 linarith
  have h17 : (N : ℝ) ≤ 17 * T * (1 + Real.log T) := by nlinarith
  have h1 : Real.log N ≤ Real.log (17 * T * (1 + Real.log T)) := Real.log_le_log hNpos h17
  have h2 : Real.log (17 * T * (1 + Real.log T)) =
      Real.log 17 + Real.log T + Real.log (1 + Real.log T) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity)]
  have h3 : Real.log (1 + Real.log T) ≤ Real.log T := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + Real.log T); linarith
  have h4 := log_seventeen_lt_three
  linarith

/-- The critical mass at the cut-off. -/
theorem critical_mass_le {D T : ℝ} (hD : 0 ≤ D) (hT : 2 ≤ T) {N : ℕ} (hN4 : 4 ≤ N)
    (hN2 : (N : ℝ) ≤ 16 * T * (1 + Real.log T) + 1) :
    D * N * (1 + Real.log N) ^ 2 ≤ 272 * D * (T * (1 + Real.log T) ^ 3) := by
  have hL0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hTL : 1 ≤ T * (1 + Real.log T) := by nlinarith
  have hlogN := one_add_log_cutoff_le hT hN4 hN2
  have hlogN0 : 0 ≤ 1 + Real.log N := by
    have : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    linarith
  have h1 : (1 + Real.log N) ^ 2 ≤ (4 * (1 + Real.log T)) ^ 2 := pow_le_pow_left₀ hlogN0 hlogN 2
  have h17 : (N : ℝ) ≤ 17 * T * (1 + Real.log T) := by nlinarith
  calc D * N * (1 + Real.log N) ^ 2 ≤ D * (17 * T * (1 + Real.log T)) * (4 * (1 + Real.log T)) ^ 2 := by
        gcongr
    _ = 272 * D * (T * (1 + Real.log T) ^ 3) := by ring

/-- The Gaussian tail at the cut-off. -/
theorem gauss_tail_le {T R₀ : ℝ} (hT : 2 ≤ T) (hR₀ : 14 * T * (1 + Real.log T) ≤ R₀) :
    T * (Real.exp 1 * (64 * Real.exp (-(R₀ ^ 2 / (8 * T) ^ 2))
      * (2 * (1 + 3 * T / 2) ^ 2 + 2 * (8 * T) ^ 2))) ≤ 1300 * (T * (1 + Real.log T) ^ 3) := by
  have hT0 : 0 < T := by linarith
  have hL0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hP1 : 1 ≤ T * (1 + Real.log T) ^ 3 := by
    have : 1 ≤ (1 + Real.log T) ^ 3 := one_le_pow₀ (by linarith)
    nlinarith
  have hexp3 : Real.exp (-(R₀ ^ 2 / (8 * T) ^ 2)) ≤ Real.exp (-3) / T ^ 3 := by
    have hR2 : 3 * (1 + Real.log T) ≤ R₀ ^ 2 / (8 * T) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have h1 : (14 * T * (1 + Real.log T)) ^ 2 ≤ R₀ ^ 2 :=
        pow_le_pow_left₀ (by positivity) hR₀ 2
      nlinarith
    have hT3 : Real.exp (3 * Real.log T) = T ^ 3 := by
      rw [show (3 : ℝ) * Real.log T = ((3 : ℕ) : ℝ) * Real.log T by norm_num, Real.exp_nat_mul,
        Real.exp_log hT0]
    calc Real.exp (-(R₀ ^ 2 / (8 * T) ^ 2)) ≤ Real.exp (-(3 * (1 + Real.log T))) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (-3) / T ^ 3 := by
          rw [← hT3, ← Real.exp_sub]; ring_nf
  have hq : 2 * (1 + 3 * T / 2) ^ 2 + 2 * (8 * T) ^ 2 ≤ 141 * T ^ 2 := by nlinarith
  have he := Real.exp_one_gt_d9
  have he2 : Real.exp 1 * Real.exp (-3) ≤ 1 / 7 := by
    rw [← Real.exp_add]
    have : Real.exp (1 + -3) = 1 / Real.exp 1 ^ 2 := by
      rw [show (1 : ℝ) + -3 = -2 by norm_num, Real.exp_neg,
        show Real.exp 2 = Real.exp 1 ^ 2 by rw [← Real.exp_nat_mul]; norm_num]
      ring
    rw [this, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hT3 : 0 < T ^ 3 := by positivity
  calc T * (Real.exp 1 * (64 * Real.exp (-(R₀ ^ 2 / (8 * T) ^ 2))
        * (2 * (1 + 3 * T / 2) ^ 2 + 2 * (8 * T) ^ 2)))
      ≤ T * (Real.exp 1 * (64 * (Real.exp (-3) / T ^ 3) * (141 * T ^ 2))) := by gcongr
    _ = 64 * 141 * (Real.exp 1 * Real.exp (-3)) * (T ^ 3 / T ^ 3) := by ring
    _ ≤ 64 * 141 * (1 / 7) * 1 := by
        rw [div_self hT3.ne']
        gcongr
    _ ≤ 1300 * (T * (1 + Real.log T) ^ 3) := by nlinarith

/-- **Mean square of `ζ` on vertical lines, with the window data.** -/
theorem integral_normSq_zeta_vertical_le_window {D Cg : ℝ} (hD : 0 ≤ D) (hCg : 0 < Cg)
    (hcrit : ∀ {N : ℕ}, 4 ≤ N →
      ∫ t in (-(N : ℝ))..(N : ℝ), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        D * N * (1 + Real.log N) ^ 2)
    (hgrowth : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 3 → ‖zetaPoleCleared z‖ ≤ Cg * (1 + |z.im|))
    {T σ : ℝ} (hT : 2 ≤ T) (hσ : 1 / 2 ≤ σ) (hσ3 : σ ≤ 3) {N : ℕ}
    (hN1 : 16 * T * (1 + Real.log T) ≤ N) (hN4 : 4 ≤ N) :
    ∫ t in T..(2 * T), ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      5 * ((Real.exp 1 * (D * N * (1 + Real.log N) ^ 2) + T * (Real.exp 1 * (64
          * Real.exp (-(((N : ℝ) - 3 * T / 2) ^ 2 / (8 * T) ^ 2))
          * (2 * (1 + 3 * T / 2) ^ 2 + 2 * (8 * T) ^ 2))))
        + 4 * Real.exp 1 ^ 2 * Real.sqrt (Real.pi / (2 / (8 * T) ^ 2))) := by
  have hT0 : 0 < T := by linarith
  have hL0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hH3 : 3 ≤ 8 * T := by linarith
  have hτabs : |3 * T / 2| = 3 * T / 2 := abs_of_pos (by linarith)
  have hR₀0 : 0 ≤ (N : ℝ) - 3 * T / 2 := by nlinarith
  have hNR : |3 * T / 2| + ((N : ℝ) - 3 * T / 2) ≤ N := by rw [hτabs]; linarith
  have hleft : ∀ y : ℝ, ∫ t in T..(2 * T),
      ‖zetaWindowField (8 * T) (3 * T / 2) (((1 / 2 : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤
      Real.exp 1 * (D * N * (1 + Real.log N) ^ 2) + T * (Real.exp 1 * (64
          * Real.exp (-(((N : ℝ) - 3 * T / 2) ^ 2 / (8 * T) ^ 2))
          * (2 * (1 + 3 * T / 2) ^ 2 + 2 * (8 * T) ^ 2))) := by
    intro y
    have h := integral_zetaWindowField_half_le hH3 hN4 hR₀0 hNR (hcrit hN4) (by linarith : T ≤ 2 * T) y
    rw [hτabs, show 2 * T - T = T by ring] at h
    exact h
  have hSL0 : 0 < Real.exp 1 * (D * N * (1 + Real.log N) ^ 2) + T * (Real.exp 1 * (64
          * Real.exp (-(((N : ℝ) - 3 * T / 2) ^ 2 / (8 * T) ^ 2))
          * (2 * (1 + 3 * T / 2) ^ 2 + 2 * (8 * T) ^ 2))) := by
    have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    have : 0 ≤ Real.exp 1 * (D * N * (1 + Real.log N) ^ 2) := by positivity
    have : 0 < T * (Real.exp 1 * (64 * Real.exp (-(((N : ℝ) - 3 * T / 2) ^ 2 / (8 * T) ^ 2))
          * (2 * (1 + 3 * T / 2) ^ 2 + 2 * (8 * T) ^ 2))) := by positivity
    linarith
  have hF := integral_normSq_zetaWindowField_le hCg hgrowth hH3 hσ hσ3 (by linarith : T ≤ 2 * T)
    hSL0 hleft
  have hσ0 : 0 < σ := by linarith
  have hcont : ContinuousOn (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      (uIcc T (2 * T)) := by
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    have hne : (σ : ℂ) + (t : ℂ) * I ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith [ht.1]
    exact (ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I)
      (differentiableAt_riemannZeta hne).continuousAt (by fun_prop)).norm.pow 2
      |>.continuousWithinAt
  have hwin : ∫ t in T..(2 * T), ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      ∫ t in T..(2 * T), 5 * ‖zetaWindowField (8 * T) (3 * T / 2) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    refine intervalIntegral.integral_mono_on (by linarith) hcont.intervalIntegrable
      ((((continuous_zetaWindowField_line (8 * T) (3 * T / 2) hσ0).norm.pow 2).intervalIntegrable
        _ _).const_mul _) fun t ht => ?_
    refine normSq_zeta_le_five_mul_window hH3 ?_ ?_
    · rw [abs_of_pos (by linarith [ht.1])]; linarith [ht.1]
    · rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  rw [intervalIntegral.integral_const_mul] at hwin
  linarith

/-- **Mean square of `ζ` on vertical lines of the strip.** -/
theorem exists_integral_normSq_zeta_vertical_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 3 →
      ∫ t in T..(2 * T), ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        C * T * (1 + Real.log T) ^ 3 := by
  obtain ⟨D, hD, hcrit⟩ := exists_integral_normSq_zeta_critical_le
  obtain ⟨Cg, hCg, hgrowth⟩ := exists_norm_zetaPoleCleared_le
  refine ⟨5 * (816 * D + 1600), by positivity, fun T hT σ hσ hσ3 => ?_⟩
  have hT0 : 0 < T := by linarith
  have hL0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hTL : 1 ≤ T * (1 + Real.log T) := by nlinarith
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌈16 * T * (1 + Real.log T)⌉₊ := ⟨_, rfl⟩
  have hN1 : 16 * T * (1 + Real.log T) ≤ N := hNdef ▸ Nat.le_ceil _
  have hN2 : (N : ℝ) ≤ 16 * T * (1 + Real.log T) + 1 :=
    hNdef ▸ (Nat.ceil_lt_add_one (by positivity)).le
  have hN4 : 4 ≤ N := by
    have : (4 : ℝ) ≤ N := by nlinarith
    exact_mod_cast this
  have hmain := integral_normSq_zeta_vertical_le_window hD hCg hcrit hgrowth hT hσ hσ3 hN1 hN4
  have hI₀ := critical_mass_le hD hT hN4 hN2
  have hR₀ : 14 * T * (1 + Real.log T) ≤ (N : ℝ) - 3 * T / 2 := by nlinarith
  have htail := gauss_tail_le hT hR₀
  have hSR := sqrt_gauss_mass_le (H := 8 * T) (by linarith)
  have he3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hP1 : T ≤ T * (1 + Real.log T) ^ 3 := by
    have : 1 ≤ (1 + Real.log T) ^ 3 := one_le_pow₀ (by linarith)
    nlinarith
  have hI₀0 : 0 ≤ D * N * (1 + Real.log N) ^ 2 := by
    have : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    positivity
  have h1 : Real.exp 1 * (D * N * (1 + Real.log N) ^ 2) ≤ 816 * D * (T * (1 + Real.log T) ^ 3) := by
    calc Real.exp 1 * (D * N * (1 + Real.log N) ^ 2) ≤ 3 * (D * N * (1 + Real.log N) ^ 2) :=
          mul_le_mul_of_nonneg_right he3 hI₀0
      _ ≤ 816 * D * (T * (1 + Real.log T) ^ 3) := by linarith
  calc ∫ t in T..(2 * T), ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
      ≤ _ := hmain
    _ ≤ 5 * (816 * D * (T * (1 + Real.log T) ^ 3) + 1300 * (T * (1 + Real.log T) ^ 3)
        + 300 * (T * (1 + Real.log T) ^ 3)) := by
        have : 300 * (8 * T) / 8 ≤ 300 * (T * (1 + Real.log T) ^ 3) := by linarith
        linarith
    _ = 5 * (816 * D + 1600) * T * (1 + Real.log T) ^ 3 := by ring

end RHTower

end
