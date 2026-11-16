import GaloisForLFunctions.ExclusionOfTheCriticalState.TheTransformOfTheStateIsMeromorphicInThePlane
import GaloisForLFunctions.RHTower.XiExplicitFormulaLogDeriv
import GaloisForLFunctions.RHTower.GaussianFormationZeroField
import GaloisForLFunctions.RHTower.LagExplicitFormula

/-!
# The zero sum of a profile converges after one subtraction

For a profile `F` of the energy domain and the centred zeros `z = ρ - ½` of `ξ` (with multiplicity),
the zero side of the pairing with the probe `e_p` is `Σ_z L F(z)/(p - z)`. The values `L F(z)` are
bounded but need not decay, so the series is taken after one subtraction:

  `Z F(p) = Σ_z L F(z) (1/(p - z) - 1/(1 - z))`,

absolutely convergent by `Σ 1/|z|² < ∞`. It is holomorphic off the zeros, with the simple pole
`L F(z)/(p - z)` per copy. The partial fraction of `ξ'/ξ` removes the poles:

  `Z F(p) = Δ F(p) + L F(p) ξ'/ξ(½ + p)`,

where `Δ F(p) = Σ_z [-(L F(p) - L F(z))/(p - z) - L F(z)/(1 - z) - L F(p)/z]` is a sum of divided
differences. `Δ F` is holomorphic on `Re p > -2`, zeros included, and `O(|p|²)` there with no input on
the position of the zeros. Off the strip `Z F` itself is `O(|p|²)`, and `Z F(p) = o(|p|)` along the
negative real axis.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### Centred zeros -/

/-- The centred coordinate `z = ρ - ½` of a zero copy of `ξ`. -/
def zeroCoord (q : XiZeroCopy) : ℂ := (q.1 : ℂ) - 1 / 2

theorem abs_re_zeroCoord_lt (q : XiZeroCopy) : |(zeroCoord q).re| < 1 / 2 := by
  have h1 := xiZeroCopy_re_pos q
  have h2 := xiZeroCopy_re_lt_one q
  have h3 : (zeroCoord q).re = ((q.1 : ℂ)).re - 1 / 2 := by simp [zeroCoord]
  rw [h3, abs_lt]
  constructor <;> linarith

theorem one_lt_norm_zeroCoord (q : XiZeroCopy) : 1 < ‖zeroCoord q‖ := one_lt_norm_xiZero_sub_half q

theorem zeroCoord_ne_zero (q : XiZeroCopy) : zeroCoord q ≠ 0 :=
  norm_pos_iff.mp (zero_lt_one.trans (one_lt_norm_zeroCoord q))

theorem summable_inv_sq_zeroCoord : Summable fun q : XiZeroCopy => ‖zeroCoord q‖⁻¹ ^ 2 := by
  refine summable_norm_inv_xiZero_sub_half_sq.congr fun q => ?_
  rw [norm_inv]
  rfl

theorem xi_zeroCoord (q : XiZeroCopy) : xi (1 / 2 + zeroCoord q) = 0 := by
  rw [show (1 : ℂ) / 2 + zeroCoord q = (q.1 : ℂ) by unfold zeroCoord; ring]
  exact xi_xiZeroCopy_eq_zero q

/-- The zeros stay at distance `½` from the half-planes `|Re p| ≥ 1`. -/
theorem half_le_norm_sub_zeroCoord {p : ℂ} (hp : 1 ≤ |p.re|) (q : XiZeroCopy) :
    1 / 2 ≤ ‖p - zeroCoord q‖ := by
  have hz := abs_re_zeroCoord_lt q
  have h := Complex.abs_re_le_norm (p - zeroCoord q)
  rw [Complex.sub_re] at h
  have h2 := abs_sub_abs_le_abs_sub p.re (zeroCoord q).re
  linarith

theorem half_le_norm_one_sub_zeroCoord (q : XiZeroCopy) : 1 / 2 ≤ ‖1 - zeroCoord q‖ :=
  half_le_norm_sub_zeroCoord (p := 1) (by simp) q

/-- A point with `ξ(½ + p) ≠ 0` has a ball every point of which is at distance at least the radius
from every zero. -/
theorem exists_zeroFree_ball {p₁ : ℂ} (h : xi (1 / 2 + p₁) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ ball p₁ δ, ∀ q : XiZeroCopy, δ ≤ ‖p - zeroCoord q‖ := by
  have hc : ContinuousAt (fun p : ℂ => xi (1 / 2 + p)) p₁ :=
    (xi_differentiable.continuous.comp (continuous_const.add continuous_id)).continuousAt
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hc.eventually_ne h)
  refine ⟨ε / 2, by positivity, fun p hp q => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hd : dist (zeroCoord q) p₁ < ε := by
    calc dist (zeroCoord q) p₁ ≤ dist (zeroCoord q) p + dist p p₁ := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by
          refine add_lt_add ?_ (mem_ball.mp hp)
          rw [dist_comm, dist_eq_norm]
          exact hlt
      _ = ε := by ring
  exact hball hd (xi_zeroCoord q)

/-- At distance `δ` from `z`, `1/(p - z)` is comparable to `1/z`. -/
theorem norm_inv_sub_le {p z : ℂ} {δ P : ℝ} (hδ : 0 < δ) (hz : z ≠ 0) (hpz : δ ≤ ‖p - z‖)
    (hP : ‖p‖ ≤ P) : ‖(p - z)⁻¹‖ ≤ (1 + P / δ) * ‖z‖⁻¹ := by
  have hP0 : 0 ≤ P := (norm_nonneg p).trans hP
  have hd : 0 < ‖p - z‖ := hδ.trans_le hpz
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h2 : ‖z‖ ≤ ‖p‖ + ‖p - z‖ := by
    have := norm_sub_le p (p - z)
    rwa [sub_sub_cancel] at this
  have h3 : P ≤ P / δ * ‖p - z‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    exact mul_le_mul_of_nonneg_left hpz hP0
  have h1 : ‖z‖ ≤ ‖p - z‖ * (1 + P / δ) := by
    calc ‖z‖ ≤ ‖p‖ + ‖p - z‖ := h2
      _ ≤ P / δ * ‖p - z‖ + ‖p - z‖ := by linarith
      _ = ‖p - z‖ * (1 + P / δ) := by ring
  rw [norm_inv, ← div_eq_mul_inv, le_div_iff₀ hzpos, inv_mul_le_iff₀ hd]
  exact h1

theorem norm_inv_one_sub_zeroCoord_le (q : XiZeroCopy) :
    ‖((1 : ℂ) - zeroCoord q)⁻¹‖ ≤ 3 * ‖zeroCoord q‖⁻¹ := by
  have h := norm_inv_sub_le (p := 1) (δ := 1 / 2) (P := 1) (by norm_num) (zeroCoord_ne_zero q)
    (half_le_norm_one_sub_zeroCoord q) (by simp)
  rwa [show (1 : ℝ) + 1 / (1 / 2) = 3 by norm_num] at h

theorem inv_sub_inv_eq {p z : ℂ} (hp : p - z ≠ 0) (h1 : 1 - z ≠ 0) :
    (p - z)⁻¹ - (1 - z)⁻¹ = (1 - p) * ((p - z)⁻¹ * (1 - z)⁻¹) := by
  field_simp
  ring

theorem inv_add_inv_sub_eq {p z : ℂ} (hp : p - z ≠ 0) (hz : z ≠ 0) :
    z⁻¹ + (p - z)⁻¹ = p * ((p - z)⁻¹ * z⁻¹) := by
  field_simp
  ring

/-! ### Bounds for the transform -/

/-- The mass `∫ |F(u)| e^{σu} du`, which bounds the transform on `Re p ≥ σ`. -/
def laplaceMass (F : ℝ → ℝ) (σ : ℝ) : ℝ := ∫ u, |F u| * Real.exp (σ * u)

theorem laplaceMass_nonneg (F : ℝ → ℝ) (σ : ℝ) : 0 ≤ laplaceMass F σ :=
  integral_nonneg fun u => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le

theorem halfPoleMass_nonneg (F : ℝ → ℝ) : 0 ≤ halfPoleMass F :=
  integral_nonneg fun u => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le

theorem norm_laplace_le_laplaceMass {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {σ : ℝ}
    (hσ : -4 < σ) {p : ℂ} (hp : σ ≤ p.re) :
    ‖negativeHalfLineLaplace (cx F) p‖ ≤ laplaceMass F σ := by
  refine norm_integral_le_of_norm_le (integrable_abs_mul_exp_of_domain hF hσ)
    (Eventually.of_forall fun u => ?_)
  rw [norm_mul, norm_cexp_mul_ofReal]
  simp only [cx, Complex.norm_real, Real.norm_eq_abs]
  rcases lt_or_ge u 0 with hu | hu
  · rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (abs_nonneg _)
  · simp [hF.support u hu]

/-- Cauchy's estimate: on `Re p ≥ -2` the derivative of the transform is bounded by the mass at
`-3`. -/
theorem norm_deriv_laplace_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : -2 ≤ p.re) : ‖deriv (negativeHalfLineLaplace (cx F)) p‖ ≤ laplaceMass F (-3) := by
  have hLap := differentiableOn_laplace_of_sq hF.meas hF.support hF.exponential
  have hsub : closedBall p 1 ⊆ {p : ℂ | -(8 / 2) < p.re} := fun z hz => by
    have := (re_mem_of_mem_closedBall hz).2
    show -(8 / 2) < z.re
    linarith
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := p) (R := 1) one_pos
    (hLap.mono hsub).diffContOnCl_ball (C := laplaceMass F (-3)) fun z hz => by
      refine norm_laplace_le_laplaceMass hF (by norm_num) ?_
      have := (re_mem_of_mem_closedBall (sphere_subset_closedBall hz)).2
      linarith
  simpa using h

/-- Divided differences of the transform between points of `Re ≥ -2` are bounded by the mass at
`-3`: the mean value inequality on the convex half-plane. -/
theorem norm_dslope_laplace_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {a p : ℂ}
    (ha : -2 ≤ a.re) (hp : -2 ≤ p.re) :
    ‖dslope (negativeHalfLineLaplace (cx F)) a p‖ ≤ laplaceMass F (-3) := by
  rcases eq_or_ne p a with rfl | hne
  · rw [dslope_same]
    exact norm_deriv_laplace_le hF ha
  · have hLap := differentiableOn_laplace_of_sq hF.meas hF.support hF.exponential
    have hopen4 : IsOpen {p : ℂ | -(8 / 2) < p.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := negativeHalfLineLaplace (cx F))
      (s := {z : ℂ | -2 ≤ z.re}) (C := laplaceMass F (-3))
      (fun z hz => hLap.differentiableAt (hopen4.mem_nhds (by
        show -(8 / 2) < z.re
        have : -2 ≤ z.re := hz
        linarith)))
      (fun z hz => norm_deriv_laplace_le hF hz) (convex_halfSpace_re_ge _) ha hp
    rw [dslope_of_ne _ hne, slope_def_field, norm_div,
      div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hne))]
    exact hmv

/-! ### The subtracted zero sum -/

/-- The zero sum of a profile, subtracted at the base point `1`:
`Z F(p) = Σ_z L F(z) (1/(p - z) - 1/(1 - z))`. -/
def zeroSum (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (zeroCoord q) *
    ((p - zeroCoord q)⁻¹ - (1 - zeroCoord q)⁻¹)

theorem norm_zeroSum_term_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ} {δ P : ℝ}
    (hδ : 0 < δ) (hP : ‖p‖ ≤ P) {q : XiZeroCopy} (hq : δ ≤ ‖p - zeroCoord q‖) :
    ‖negativeHalfLineLaplace (cx F) (zeroCoord q) *
        ((p - zeroCoord q)⁻¹ - (1 - zeroCoord q)⁻¹)‖ ≤
      halfPoleMass F * (1 + P) * (1 + P / δ) * 3 * ‖zeroCoord q‖⁻¹ ^ 2 := by
  have hz0 := zeroCoord_ne_zero q
  have hpz : p - zeroCoord q ≠ 0 := norm_pos_iff.mp (hδ.trans_le hq)
  have h1 := half_le_norm_one_sub_zeroCoord q
  have h1z : (1 : ℂ) - zeroCoord q ≠ 0 := norm_pos_iff.mp (by linarith)
  have hL : ‖negativeHalfLineLaplace (cx F) (zeroCoord q)‖ ≤ halfPoleMass F :=
    norm_laplace_le_halfPoleMass hF (by
      have := (abs_lt.mp (abs_re_zeroCoord_lt q)).1
      linarith)
  have hA : ‖(p - zeroCoord q)⁻¹‖ ≤ (1 + P / δ) * ‖zeroCoord q‖⁻¹ := norm_inv_sub_le hδ hz0 hq hP
  have hB := norm_inv_one_sub_zeroCoord_le q
  have hp1 : ‖(1 : ℂ) - p‖ ≤ 1 + P := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have hP0 : 0 ≤ P := (norm_nonneg p).trans hP
  have hm0 := halfPoleMass_nonneg F
  have hzi : 0 ≤ ‖zeroCoord q‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have hδP : 0 ≤ P / δ := div_nonneg hP0 hδ.le
  rw [inv_sub_inv_eq hpz h1z, norm_mul, norm_mul, norm_mul]
  calc ‖negativeHalfLineLaplace (cx F) (zeroCoord q)‖ *
        (‖(1 : ℂ) - p‖ * (‖(p - zeroCoord q)⁻¹‖ * ‖((1 : ℂ) - zeroCoord q)⁻¹‖))
      ≤ halfPoleMass F * ((1 + P) * (((1 + P / δ) * ‖zeroCoord q‖⁻¹) *
          (3 * ‖zeroCoord q‖⁻¹))) := by gcongr
    _ = _ := by ring

theorem summable_zeroSum_term {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hq : ∀ q : XiZeroCopy, δ ≤ ‖p - zeroCoord q‖) :
    Summable fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (zeroCoord q) *
      ((p - zeroCoord q)⁻¹ - (1 - zeroCoord q)⁻¹) :=
  Summable.of_norm_bounded (summable_inv_sq_zeroCoord.mul_left _)
    fun q => norm_zeroSum_term_le hF hδ le_rfl (hq q)

/-- **The zero sum is holomorphic off the zeros.** -/
theorem differentiableAt_zeroSum {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p₁ : ℂ}
    (h : xi (1 / 2 + p₁) ≠ 0) : DifferentiableAt ℂ (zeroSum F) p₁ := by
  obtain ⟨δ, hδ, hball⟩ := exists_zeroFree_ball h
  show DifferentiableAt ℂ (fun p => ∑' q : XiZeroCopy,
    negativeHalfLineLaplace (cx F) (zeroCoord q) * ((p - zeroCoord q)⁻¹ - (1 - zeroCoord q)⁻¹)) p₁
  refine (Complex.differentiableOn_tsum_of_summable_norm
    (summable_inv_sq_zeroCoord.mul_left
      (halfPoleMass F * (1 + (‖p₁‖ + δ)) * (1 + (‖p₁‖ + δ) / δ) * 3))
    (fun q => ?_) isOpen_ball (fun q p hp => ?_)).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self hδ))
  · refine DifferentiableOn.const_mul (DifferentiableOn.sub_const
      (DifferentiableOn.inv (differentiableOn_id.sub_const _) fun p hp => ?_) _) _
    exact norm_pos_iff.mp (hδ.trans_le (hball p hp q))
  · refine norm_zeroSum_term_le hF hδ ?_ (hball p hp q)
    have h1 := mem_ball.mp hp
    rw [dist_eq_norm] at h1
    have h2 := norm_sub_norm_le p p₁
    linarith

/-- Off the strip, `Z F(p) = O(|p|²)`. -/
theorem norm_zeroSum_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : 1 ≤ |p.re|) :
    ‖zeroSum F p‖ ≤
      6 * halfPoleMass F * (∑' q : XiZeroCopy, ‖zeroCoord q‖⁻¹ ^ 2) * (1 + ‖p‖) ^ 2 := by
  have hm0 := halfPoleMass_nonneg F
  have hs := (summable_inv_sq_zeroCoord.mul_left
    (halfPoleMass F * (1 + ‖p‖) * (1 + ‖p‖ / (1 / 2)) * 3)).hasSum
  unfold zeroSum
  refine (tsum_of_norm_bounded hs fun q => norm_zeroSum_term_le hF (by norm_num) le_rfl
    (half_le_norm_sub_zeroCoord hp q)).trans ?_
  rw [tsum_mul_left]
  have hS : 0 ≤ ∑' q : XiZeroCopy, ‖zeroCoord q‖⁻¹ ^ 2 := tsum_nonneg fun q => by positivity
  have hn := norm_nonneg p
  have h1 : (1 + ‖p‖) * (1 + ‖p‖ / (1 / 2)) ≤ 2 * (1 + ‖p‖) ^ 2 := by
    rw [div_div_eq_mul_div, div_one]
    nlinarith
  have h2 : halfPoleMass F * (1 + ‖p‖) * (1 + ‖p‖ / (1 / 2)) * 3 ≤
      6 * halfPoleMass F * (1 + ‖p‖) ^ 2 := by
    have := mul_le_mul_of_nonneg_left h1 hm0
    nlinarith
  calc halfPoleMass F * (1 + ‖p‖) * (1 + ‖p‖ / (1 / 2)) * 3 *
        ∑' q : XiZeroCopy, ‖zeroCoord q‖⁻¹ ^ 2
      ≤ 6 * halfPoleMass F * (1 + ‖p‖) ^ 2 * ∑' q : XiZeroCopy, ‖zeroCoord q‖⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_right h2 hS
    _ = _ := by ring

/-- **Along the negative real axis `Z F(p) = o(|p|)`**: `Z F(p)/(1 - p) = Σ_z L F(z)/((p - z)(1 - z))`
tends to zero by dominated convergence. -/
theorem tendsto_zeroSum_div {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    Tendsto (fun n : ℕ => zeroSum F (-((n : ℂ) + 1)) / (1 - -((n : ℂ) + 1))) atTop (𝓝 0) := by
  have hm0 := halfPoleMass_nonneg F
  have hre : ∀ (n : ℕ) (q : XiZeroCopy), (n : ℝ) + 1 / 2 ≤ ‖-((n : ℂ) + 1) - zeroCoord q‖ := by
    intro n q
    have hz := (abs_lt.mp (abs_re_zeroCoord_lt q)).2
    have h := Complex.abs_re_le_norm (-((n : ℂ) + 1) - zeroCoord q)
    have h2 := neg_abs_le ((-((n : ℂ) + 1) - zeroCoord q).re)
    simp only [Complex.sub_re, Complex.neg_re, Complex.add_re, Complex.natCast_re,
      Complex.one_re] at h h2
    linarith
  have hne : ∀ (n : ℕ) (q : XiZeroCopy), -((n : ℂ) + 1) - zeroCoord q ≠ 0 := fun n q =>
    norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (hre n q))
  have h1z : ∀ q : XiZeroCopy, (1 : ℂ) - zeroCoord q ≠ 0 := fun q =>
    norm_pos_iff.mp (by have := half_le_norm_one_sub_zeroCoord q; linarith)
  -- the quotient is a sum of products of two inverse distances
  have hquot : ∀ n : ℕ, zeroSum F (-((n : ℂ) + 1)) / (1 - -((n : ℂ) + 1)) =
      ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (zeroCoord q) *
        ((-((n : ℂ) + 1) - zeroCoord q)⁻¹ * (1 - zeroCoord q)⁻¹) := by
    intro n
    have hn0 : (1 : ℂ) - -((n : ℂ) + 1) ≠ 0 := by
      rw [show (1 : ℂ) - -((n : ℂ) + 1) = ((n + 2 : ℕ) : ℂ) by push_cast; ring]
      exact_mod_cast (by omega : n + 2 ≠ 0)
    unfold zeroSum
    rw [div_eq_iff hn0, ← tsum_mul_right]
    refine tsum_congr fun q => ?_
    rw [inv_sub_inv_eq (hne n q) (h1z q)]
    ring
  simp only [hquot]
  have hlim := tendsto_tsum_of_dominated_convergence
    (f := fun (n : ℕ) (q : XiZeroCopy) => negativeHalfLineLaplace (cx F) (zeroCoord q) *
      ((-((n : ℂ) + 1) - zeroCoord q)⁻¹ * (1 - zeroCoord q)⁻¹))
    (g := fun _ => (0 : ℂ)) (𝓕 := atTop)
    (bound := fun q : XiZeroCopy => halfPoleMass F * 6 * ‖zeroCoord q‖⁻¹ ^ 2)
    (summable_inv_sq_zeroCoord.mul_left _) (fun q => ?_) (Eventually.of_forall fun n q => ?_)
  · simpa using hlim
  · -- each term tends to zero
    have hL : ‖negativeHalfLineLaplace (cx F) (zeroCoord q)‖ ≤ halfPoleMass F :=
      norm_laplace_le_halfPoleMass hF (by
        have := (abs_lt.mp (abs_re_zeroCoord_lt q)).1
        linarith)
    have hB := norm_inv_one_sub_zeroCoord_le q
    have hzi : 0 ≤ ‖zeroCoord q‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
    refine squeeze_zero_norm (a := fun n : ℕ => halfPoleMass F * (3 * ‖zeroCoord q‖⁻¹) *
      ((n : ℝ) + 1 / 2)⁻¹) (fun n => ?_) ?_
    · have hpos : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
      have hA : ‖(-((n : ℂ) + 1) - zeroCoord q)⁻¹‖ ≤ ((n : ℝ) + 1 / 2)⁻¹ := by
        rw [norm_inv]
        exact inv_anti₀ hpos (hre n q)
      rw [norm_mul, norm_mul]
      calc ‖negativeHalfLineLaplace (cx F) (zeroCoord q)‖ *
            (‖(-((n : ℂ) + 1) - zeroCoord q)⁻¹‖ * ‖((1 : ℂ) - zeroCoord q)⁻¹‖)
          ≤ halfPoleMass F * (((n : ℝ) + 1 / 2)⁻¹ * (3 * ‖zeroCoord q‖⁻¹)) := by gcongr
        _ = _ := by ring
    · have h0 : Tendsto (fun n : ℕ => ((n : ℝ) + 1 / 2)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp
          (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
      simpa using h0.const_mul (halfPoleMass F * (3 * ‖zeroCoord q‖⁻¹))
  · -- the dominating series: for real p, |p - z| ≥ |Im z| ≥ |z|/2
    have hL : ‖negativeHalfLineLaplace (cx F) (zeroCoord q)‖ ≤ halfPoleMass F :=
      norm_laplace_le_halfPoleMass hF (by
        have := (abs_lt.mp (abs_re_zeroCoord_lt q)).1
        linarith)
    have hB := norm_inv_one_sub_zeroCoord_le q
    have hz1 := one_lt_norm_zeroCoord q
    have hzi : 0 ≤ ‖zeroCoord q‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
    have him : ‖zeroCoord q‖ / 2 ≤ ‖-((n : ℂ) + 1) - zeroCoord q‖ := by
      have h1 := Complex.norm_le_abs_re_add_abs_im (zeroCoord q)
      have h2 := abs_re_zeroCoord_lt q
      have h3 := Complex.abs_im_le_norm (-((n : ℂ) + 1) - zeroCoord q)
      simp only [Complex.sub_im, Complex.neg_im, Complex.add_im, Complex.natCast_im,
        Complex.one_im, add_zero, neg_zero, zero_sub, abs_neg] at h3
      linarith
    have hA : ‖(-((n : ℂ) + 1) - zeroCoord q)⁻¹‖ ≤ 2 * ‖zeroCoord q‖⁻¹ := by
      rw [norm_inv]
      have := inv_anti₀ (by linarith : (0 : ℝ) < ‖zeroCoord q‖ / 2) him
      rwa [inv_div, div_eq_mul_inv] at this
    rw [norm_mul, norm_mul]
    calc ‖negativeHalfLineLaplace (cx F) (zeroCoord q)‖ *
          (‖(-((n : ℂ) + 1) - zeroCoord q)⁻¹‖ * ‖((1 : ℂ) - zeroCoord q)⁻¹‖)
        ≤ halfPoleMass F * ((2 * ‖zeroCoord q‖⁻¹) * (3 * ‖zeroCoord q‖⁻¹)) := by gcongr
      _ = _ := by ring

/-! ### The divided-difference sum -/

/-- One term of the divided-difference sum. Off the zero it is
`L F(z)(1/(p-z) - 1/(1-z)) - L F(p)(1/z + 1/(p-z))`; it is holomorphic at the zero as well. -/
def dividedTerm (F : ℝ → ℝ) (q : XiZeroCopy) (p : ℂ) : ℂ :=
  -dslope (negativeHalfLineLaplace (cx F)) (zeroCoord q) p -
    negativeHalfLineLaplace (cx F) (zeroCoord q) * (1 - zeroCoord q)⁻¹ -
    negativeHalfLineLaplace (cx F) p * (zeroCoord q)⁻¹

/-- The divided-difference sum `Δ F(p)`. -/
def dividedSum (F : ℝ → ℝ) (p : ℂ) : ℂ := ∑' q : XiZeroCopy, dividedTerm F q p

theorem dividedTerm_eq (F : ℝ → ℝ) {q : XiZeroCopy} {p : ℂ} (hp : p ≠ zeroCoord q) :
    dividedTerm F q p =
      negativeHalfLineLaplace (cx F) (zeroCoord q) *
          ((p - zeroCoord q)⁻¹ - (1 - zeroCoord q)⁻¹) -
        negativeHalfLineLaplace (cx F) p * ((zeroCoord q)⁻¹ + (p - zeroCoord q)⁻¹) := by
  unfold dividedTerm
  rw [dslope_of_ne _ hp, slope_def_field]
  ring

/-- Each term is `O((1+|p|)²/|z|²)` on `Re p ≥ -2`: within distance one of the zero by the mean
value bound, beyond it by the two-point form. -/
theorem norm_dividedTerm_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ} {P : ℝ}
    (hp : -2 ≤ p.re) (hP : ‖p‖ ≤ P) (q : XiZeroCopy) :
    ‖dividedTerm F q p‖ ≤ 4 * laplaceMass F (-3) * (1 + P) ^ 2 * ‖zeroCoord q‖⁻¹ ^ 2 := by
  have hB0 : 0 ≤ laplaceMass F (-3) := laplaceMass_nonneg F _
  have hP0 : 0 ≤ P := (norm_nonneg p).trans hP
  have hz0 := zeroCoord_ne_zero q
  have hz1 := one_lt_norm_zeroCoord q
  have hzre : -2 ≤ (zeroCoord q).re := by
    have := (abs_lt.mp (abs_re_zeroCoord_lt q)).1
    linarith
  have hLz : ‖negativeHalfLineLaplace (cx F) (zeroCoord q)‖ ≤ laplaceMass F (-3) :=
    norm_laplace_le_laplaceMass hF (by norm_num) (by linarith)
  have hLp : ‖negativeHalfLineLaplace (cx F) p‖ ≤ laplaceMass F (-3) :=
    norm_laplace_le_laplaceMass hF (by norm_num) (by linarith)
  have hzi : 0 ≤ ‖zeroCoord q‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have hzinv : ‖(zeroCoord q)⁻¹‖ ≤ ‖zeroCoord q‖⁻¹ := (norm_inv _).le
  have h1 := half_le_norm_one_sub_zeroCoord q
  have h1z : (1 : ℂ) - zeroCoord q ≠ 0 := norm_pos_iff.mp (by linarith)
  rcases le_or_gt ‖p - zeroCoord q‖ 1 with hnear | hfar
  · have hD := norm_dslope_laplace_le hF hzre hp
    have h1i : ‖((1 : ℂ) - zeroCoord q)⁻¹‖ ≤ 2 := by
      rw [norm_inv]
      have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) h1
      norm_num at this
      exact this
    have hzi1 : ‖(zeroCoord q)⁻¹‖ ≤ 1 := hzinv.trans (inv_le_one_of_one_le₀ hz1.le)
    have hzP : ‖zeroCoord q‖ ≤ 1 + P := by
      have := norm_sub_le p (p - zeroCoord q)
      rw [sub_sub_cancel] at this
      linarith
    have hone : 1 ≤ (1 + P) * ‖zeroCoord q‖⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by linarith)]
      linarith
    have hsq : 1 ≤ (1 + P) ^ 2 * ‖zeroCoord q‖⁻¹ ^ 2 := by
      rw [← mul_pow]
      exact one_le_pow₀ hone
    have hbound : ‖dividedTerm F q p‖ ≤ 4 * laplaceMass F (-3) := by
      unfold dividedTerm
      calc ‖-dslope (negativeHalfLineLaplace (cx F)) (zeroCoord q) p -
              negativeHalfLineLaplace (cx F) (zeroCoord q) * (1 - zeroCoord q)⁻¹ -
              negativeHalfLineLaplace (cx F) p * (zeroCoord q)⁻¹‖
          ≤ ‖dslope (negativeHalfLineLaplace (cx F)) (zeroCoord q) p‖ +
              ‖negativeHalfLineLaplace (cx F) (zeroCoord q)‖ * ‖((1 : ℂ) - zeroCoord q)⁻¹‖ +
              ‖negativeHalfLineLaplace (cx F) p‖ * ‖(zeroCoord q)⁻¹‖ := by
            refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) ?_)
            · rw [norm_neg, norm_mul]
            · rw [norm_mul]
        _ ≤ laplaceMass F (-3) + laplaceMass F (-3) * 2 + laplaceMass F (-3) * 1 := by gcongr
        _ = 4 * laplaceMass F (-3) := by ring
    calc ‖dividedTerm F q p‖ ≤ 4 * laplaceMass F (-3) := hbound
      _ ≤ 4 * laplaceMass F (-3) * ((1 + P) ^ 2 * ‖zeroCoord q‖⁻¹ ^ 2) :=
          le_mul_of_one_le_right (by positivity) hsq
      _ = _ := by ring
  · have hne : p ≠ zeroCoord q := fun h => by
      rw [h, sub_self, norm_zero] at hfar
      linarith
    have hpz : p - zeroCoord q ≠ 0 := sub_ne_zero.mpr hne
    have hA : ‖(p - zeroCoord q)⁻¹‖ ≤ (1 + P) * ‖zeroCoord q‖⁻¹ := by
      have := norm_inv_sub_le (δ := 1) one_pos hz0 hfar.le hP
      rwa [div_one] at this
    have hB3 := norm_inv_one_sub_zeroCoord_le q
    have hp1 : ‖(1 : ℂ) - p‖ ≤ 1 + P := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
    rw [dividedTerm_eq F hne, inv_sub_inv_eq hpz h1z, inv_add_inv_sub_eq hpz hz0]
    calc ‖negativeHalfLineLaplace (cx F) (zeroCoord q) *
              ((1 - p) * ((p - zeroCoord q)⁻¹ * (1 - zeroCoord q)⁻¹)) -
            negativeHalfLineLaplace (cx F) p * (p * ((p - zeroCoord q)⁻¹ * (zeroCoord q)⁻¹))‖
        ≤ ‖negativeHalfLineLaplace (cx F) (zeroCoord q)‖ *
              (‖(1 : ℂ) - p‖ * (‖(p - zeroCoord q)⁻¹‖ * ‖((1 : ℂ) - zeroCoord q)⁻¹‖)) +
            ‖negativeHalfLineLaplace (cx F) p‖ *
              (‖p‖ * (‖(p - zeroCoord q)⁻¹‖ * ‖(zeroCoord q)⁻¹‖)) := by
          refine (norm_sub_le _ _).trans (le_of_eq ?_)
          simp only [norm_mul]
      _ ≤ laplaceMass F (-3) * ((1 + P) * (((1 + P) * ‖zeroCoord q‖⁻¹) *
              (3 * ‖zeroCoord q‖⁻¹))) +
            laplaceMass F (-3) * (P * (((1 + P) * ‖zeroCoord q‖⁻¹) * ‖zeroCoord q‖⁻¹)) := by
          gcongr
      _ ≤ 4 * laplaceMass F (-3) * (1 + P) ^ 2 * ‖zeroCoord q‖⁻¹ ^ 2 := by
          have h := mul_nonneg (mul_nonneg hB0 (sq_nonneg ‖zeroCoord q‖⁻¹))
            (by linarith : (0 : ℝ) ≤ 1 + P)
          nlinarith

theorem summable_dividedTerm {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : -2 ≤ p.re) : Summable fun q : XiZeroCopy => dividedTerm F q p :=
  Summable.of_norm_bounded (summable_inv_sq_zeroCoord.mul_left _)
    fun q => norm_dividedTerm_le hF hp le_rfl q

/-- **`Δ F(p) = O(|p|²)` on `Re p ≥ -2`**, zeros included. -/
theorem norm_dividedSum_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : -2 ≤ p.re) :
    ‖dividedSum F p‖ ≤
      4 * laplaceMass F (-3) * (∑' q : XiZeroCopy, ‖zeroCoord q‖⁻¹ ^ 2) * (1 + ‖p‖) ^ 2 := by
  have hs := (summable_inv_sq_zeroCoord.mul_left (4 * laplaceMass F (-3) * (1 + ‖p‖) ^ 2)).hasSum
  unfold dividedSum
  refine (tsum_of_norm_bounded hs fun q => norm_dividedTerm_le hF hp le_rfl q).trans (le_of_eq ?_)
  rw [tsum_mul_left]
  ring

/-- **The divided-difference sum is holomorphic on `Re p > -2`**, across the zeros. -/
theorem differentiableAt_dividedSum {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p₁ : ℂ}
    (hp : -2 < p₁.re) : DifferentiableAt ℂ (dividedSum F) p₁ := by
  have hLap := differentiableOn_laplace_of_sq hF.meas hF.support hF.exponential
  have hopen4 : IsOpen {p : ℂ | -(8 / 2) < p.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUo : IsOpen ({p : ℂ | -2 < p.re} ∩ ball p₁ 1) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ball
  have hU4 : {p : ℂ | -2 < p.re} ∩ ball p₁ 1 ⊆ {p : ℂ | -(8 / 2) < p.re} := fun p hp => by
    have : -2 < p.re := hp.1
    show -(8 / 2) < p.re
    linarith
  show DifferentiableAt ℂ (fun p => ∑' q : XiZeroCopy, dividedTerm F q p) p₁
  refine (Complex.differentiableOn_tsum_of_summable_norm
    (summable_inv_sq_zeroCoord.mul_left (4 * laplaceMass F (-3) * (1 + (‖p₁‖ + 1)) ^ 2))
    (fun q => ?_) hUo (fun q p hp => ?_)).differentiableAt
      (hUo.mem_nhds ⟨hp, mem_ball_self one_pos⟩)
  · have hz4 : {p : ℂ | -(8 / 2) < p.re} ∈ 𝓝 (zeroCoord q) := hopen4.mem_nhds (by
      show -(8 / 2) < (zeroCoord q).re
      have := (abs_lt.mp (abs_re_zeroCoord_lt q)).1
      linarith)
    have hD : DifferentiableOn ℂ (dslope (negativeHalfLineLaplace (cx F)) (zeroCoord q))
        ({p : ℂ | -2 < p.re} ∩ ball p₁ 1) := ((differentiableOn_dslope hz4).mpr hLap).mono hU4
    exact ((hD.neg).sub_const _).sub ((hLap.mono hU4).mul_const _)
  · refine norm_dividedTerm_le hF hp.1.le ?_ q
    have h1 := mem_ball.mp hp.2
    rw [dist_eq_norm] at h1
    have h2 := norm_sub_norm_le p p₁
    linarith

/-- **Removing the poles.** Off the zeros, `Z F(p) = Δ F(p) + L F(p) ξ'/ξ(½ + p)`: the partial
fraction of `ξ'/ξ` carries exactly the poles of the zero sum. -/
theorem zeroSum_eq_dividedSum_add {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : xi (1 / 2 + p) ≠ 0) :
    zeroSum F p =
      dividedSum F p + negativeHalfLineLaplace (cx F) p * logDeriv xi (1 / 2 + p) := by
  obtain ⟨δ, hδ, hball⟩ := exists_zeroFree_ball hp
  have hq : ∀ q : XiZeroCopy, δ ≤ ‖p - zeroCoord q‖ := hball p (mem_ball_self hδ)
  have hne : ∀ q : XiZeroCopy, p ≠ zeroCoord q := fun q h => by
    have := hq q
    rw [h, sub_self, norm_zero] at this
    linarith
  have ha := summable_zeroSum_term hF hδ hq
  have hb : Summable fun q : XiZeroCopy => (zeroCoord q)⁻¹ + (p - zeroCoord q)⁻¹ := by
    refine Summable.of_norm_bounded (summable_inv_sq_zeroCoord.mul_left (‖p‖ * (1 + ‖p‖ / δ)))
      fun q => ?_
    rw [inv_add_inv_sub_eq (sub_ne_zero.mpr (hne q)) (zeroCoord_ne_zero q), norm_mul, norm_mul,
      norm_inv (zeroCoord q)]
    have hA := norm_inv_sub_le hδ (zeroCoord_ne_zero q) (hq q) (le_refl ‖p‖)
    have hzi : 0 ≤ ‖zeroCoord q‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
    calc ‖p‖ * (‖(p - zeroCoord q)⁻¹‖ * ‖zeroCoord q‖⁻¹)
        ≤ ‖p‖ * (((1 + ‖p‖ / δ) * ‖zeroCoord q‖⁻¹) * ‖zeroCoord q‖⁻¹) := by gcongr
      _ = _ := by ring
  have hpf : logDeriv xi (1 / 2 + p) =
      ∑' q : XiZeroCopy, ((zeroCoord q)⁻¹ + (p - zeroCoord q)⁻¹) := by
    rw [logDeriv_xi_eq_partialFraction hp]
    refine tsum_congr fun q => ?_
    rw [show (1 : ℂ) / 2 + p - (q.1 : ℂ) = p - zeroCoord q by unfold zeroCoord; ring]
    rfl
  have hd : (fun q : XiZeroCopy => dividedTerm F q p) = fun q =>
      negativeHalfLineLaplace (cx F) (zeroCoord q) *
          ((p - zeroCoord q)⁻¹ - (1 - zeroCoord q)⁻¹) -
        negativeHalfLineLaplace (cx F) p * ((zeroCoord q)⁻¹ + (p - zeroCoord q)⁻¹) :=
    funext fun q => dividedTerm_eq F (hne q)
  unfold zeroSum dividedSum
  rw [hd, hpf, ha.tsum_sub (hb.mul_left _), tsum_mul_left]
  ring

end GaloisForLFunctions.ExclusionOfTheCriticalState
