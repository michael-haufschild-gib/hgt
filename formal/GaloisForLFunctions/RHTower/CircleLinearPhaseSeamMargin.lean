import GaloisForLFunctions.RHTower.CircleHolomorphicPhaseSeamContraction

/-!
# Seams of zero-free phases come arbitrarily close to one

For `0 < r < 1` let `q(z) = 1 − r z`: holomorphic and zero-free on a neighbourhood of the closed
unit disc, with its only zero at `1/r` outside it.  Its boundary phase `u = q/|q|` has relative
index zero, so the adjoint Hankel seam `(1 − P) U† P` is a strict contraction
(`CircleHolomorphicPhaseSeamContraction`).  We prove the explicit lower bound

`‖(1 − P) U† P‖² ≥ 1 − 2π / log(1 + π/(1 − r))`,

so the seam norm tends to one as the zero `1/r` approaches the circle.  Test vector: the boundary
values of `g = q^{-1/2}`, a Hardy-space vector with `U† g = conj(a) · q⁻¹`, `a = q g`.  By Cauchy's
formula the nonnegative Fourier coefficients of `conj(a) q⁻¹` are `r^j · conj(a(r))`, so
`‖P(U† g)‖ = 1` exactly, while `‖g‖² = ∫ |q|⁻¹ ≥ (1/2π) log(1 + π/(1 − r))`.

Consequence: no argument that uses only holomorphy and zero-freeness of a boundary phase can give
a seam bound `‖(1 − P) U† P‖ ≤ 1 − c` with `c > 0` uniform over discs.  Every producer for the
seam criterion `riemannHypothesis_iff_forall_xiRightDisc_adjointSeam_lt_one` must degrade as zeros
approach the boundary; the rate here is logarithmic.
-/

noncomputable section

open Complex MeasureTheory Metric intervalIntegral ContinuousLinearMap
open scoped Real InnerProductSpace

namespace RHTower

namespace LinearPhaseSeam

/-- The linear function `q(z) = 1 − r z`. -/
def q (r : ℝ) (s : ℂ) : ℂ := 1 - (r : ℂ) * s

/-- The inverse square root `g = q^{-1/2}` (principal branch). -/
def g (r : ℝ) (s : ℂ) : ℂ := q r s ^ (-(1 / 2 : ℂ))

variable {r : ℝ}

theorem q_re_pos (hr0 : 0 < r) {s : ℂ} (hs : ‖s‖ < 1 / r) : 0 < (q r s).re := by
  have h1 : ‖(r : ℂ) * s‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    calc r * ‖s‖ < r * (1 / r) := mul_lt_mul_of_pos_left hs hr0
      _ = 1 := by field_simp
  have h2 : ((r : ℂ) * s).re < 1 := lt_of_le_of_lt (Complex.re_le_norm _) h1
  simp only [q, Complex.sub_re, Complex.one_re]
  linarith

theorem q_ne_zero (hr0 : 0 < r) {s : ℂ} (hs : ‖s‖ < 1 / r) : q r s ≠ 0 := by
  intro h
  have := q_re_pos hr0 hs
  rw [h, Complex.zero_re] at this
  exact lt_irrefl 0 this

theorem q_mem_slitPlane (hr0 : 0 < r) {s : ℂ} (hs : ‖s‖ < 1 / r) : q r s ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inl (q_re_pos hr0 hs))

theorem g_sq (_hr0 : 0 < r) {s : ℂ} (_hs : ‖s‖ < 1 / r) : g r s ^ 2 = (q r s)⁻¹ := by
  rw [g, ← Complex.cpow_nat_mul]
  norm_num
  rw [Complex.cpow_neg_one]

theorem g_ne_zero (hr0 : 0 < r) {s : ℂ} (hs : ‖s‖ < 1 / r) : g r s ≠ 0 := by
  intro h
  have h2 := g_sq hr0 hs
  rw [h] at h2
  norm_num at h2
  exact q_ne_zero hr0 hs h2.symm

theorem differentiableAt_q (s : ℂ) : DifferentiableAt ℂ (q r) s :=
  (differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id)

theorem differentiableAt_g (hr0 : 0 < r) {s : ℂ} (hs : ‖s‖ < 1 / r) :
    DifferentiableAt ℂ (g r) s :=
  (differentiableAt_q s).cpow_const (q_mem_slitPlane hr0 hs)

theorem one_lt_inv (hr0 : 0 < r) (hr1 : r < 1) : 1 < 1 / r := by
  rw [lt_div_iff₀ hr0]; linarith

/-- The disc datum of a holomorphic function on `ball 0 (1/r)` over the unit circle. -/
def datum (hr0 : 0 < r) (hr1 : r < 1) (F : ℂ → ℂ)
    (hF : ∀ s : ℂ, ‖s‖ < 1 / r → DifferentiableAt ℂ F s)
    (hne : ∀ s : ℂ, ‖s‖ < 1 / r → F s ≠ 0) : DiscArgumentDatum where
  c := 0
  t := 1
  R := (1 + 1 / r) / 2
  U := ball 0 (1 / r)
  F := F
  t_pos := one_pos
  t_lt_R := by have := one_lt_inv hr0 hr1; linarith
  isOpen := isOpen_ball
  closedBall_subset := by
    apply closedBall_subset_ball
    have := one_lt_inv hr0 hr1; linarith
  differentiableOn := fun s hs =>
    (hF s (by simpa [mem_ball, dist_zero_right] using hs)).differentiableWithinAt
  ne_zero := fun s hs => hne s (by
    rw [mem_sphere, dist_zero_right] at hs
    rw [hs]; exact one_lt_inv hr0 hr1)

/-- The datum of the linear function `q`. -/
def qDatum (hr0 : 0 < r) (hr1 : r < 1) : DiscArgumentDatum :=
  datum hr0 hr1 (q r) (fun s _ => differentiableAt_q s) (fun _ hs => q_ne_zero hr0 hs)

/-- The datum of the inverse square root `g`. -/
def gDatum (hr0 : 0 < r) (hr1 : r < 1) : DiscArgumentDatum :=
  datum hr0 hr1 (g r) (fun _ hs => differentiableAt_g hr0 hs) (fun _ hs => g_ne_zero hr0 hs)

/-- Boundary points of the unit circle. -/
def e (x : ℝ) : ℂ := circleMap 0 1 (2 * π * x)

theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  rw [e, norm_circleMap_zero]; norm_num

theorem norm_e_lt (hr0 : 0 < r) (hr1 : r < 1) (x : ℝ) : ‖e x‖ < 1 / r := by
  rw [norm_e]; exact one_lt_inv hr0 hr1

theorem conj_e (x : ℝ) : starRingEnd ℂ (e x) = (e x)⁻¹ := by
  have h : e x * starRingEnd ℂ (e x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_e]; norm_num
  exact (eq_inv_of_mul_eq_one_right h)

theorem qDatum_value (hr0 : 0 < r) (hr1 : r < 1) (x : ℝ) :
    (qDatum hr0 hr1).value x = q r (e x) := by
  simp [qDatum, datum, DiscArgumentDatum.value, DiscArgumentDatum.boundary, e]

theorem gDatum_value (hr0 : 0 < r) (hr1 : r < 1) (x : ℝ) :
    (gDatum hr0 hr1).value x = g r (e x) := by
  simp [gDatum, datum, DiscArgumentDatum.value, DiscArgumentDatum.boundary, e]

/-- `a = q g`, the square root `q^{1/2}`. -/
def a (r : ℝ) (s : ℂ) : ℂ := q r s * g r s

theorem a_sq (hr0 : 0 < r) {s : ℂ} (hs : ‖s‖ < 1 / r) : a r s ^ 2 = q r s := by
  rw [a, mul_pow, g_sq hr0 hs, pow_two]
  field_simp [q_ne_zero hr0 hs]

/-- The key boundary identity: `conj(u) · g = conj(a) / q` on the unit circle, `u = q/|q|`. -/
theorem conj_phase_mul_g (hr0 : 0 < r) (hr1 : r < 1) (x : ℝ) :
    starRingEnd ℂ ((qDatum hr0 hr1).phase x) * (gDatum hr0 hr1).value x =
      starRingEnd ℂ (a r (e x)) * (q r (e x))⁻¹ := by
  have hs := norm_e_lt hr0 hr1 x
  have hq := q_ne_zero hr0 hs
  have hg := g_ne_zero hr0 hs
  have hgq : g r (e x) ^ 2 * q r (e x) = 1 := by rw [g_sq hr0 hs]; field_simp
  have hnorm : ((‖q r (e x)‖ : ℝ) : ℂ) =
      1 / (g r (e x) * starRingEnd ℂ (g r (e x))) := by
    have h1 : ‖q r (e x)‖ = 1 / ‖g r (e x)‖ ^ 2 := by
      have := congrArg norm (g_sq hr0 hs)
      rw [norm_pow, norm_inv] at this
      rw [this]; field_simp
    rw [h1, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  simp only [DiscArgumentDatum.phase, DiscArgumentDatum.modulus, qDatum_value, gDatum_value,
    map_mul, map_inv₀, Complex.conj_ofReal, a]
  rw [hnorm]
  have hcg : starRingEnd ℂ (g r (e x)) ≠ 0 := (map_ne_zero _).mpr hg
  have hcq : starRingEnd ℂ (q r (e x)) = (starRingEnd ℂ (g r (e x)) ^ 2)⁻¹ := by
    have := congrArg (starRingEnd ℂ) (g_sq hr0 hs)
    rw [map_pow, map_inv₀] at this
    rw [this, inv_inv]
  rw [hcq]
  field_simp
  have : q r (e x) = (g r (e x) ^ 2)⁻¹ := by rw [g_sq hr0 hs, inv_inv]
  rw [this]
  field_simp

/-! ## The boundary function `conj(a)/q` and its Fourier coefficients -/

/-- `H = conj(a)/q` on the circle. -/
def H (r : ℝ) (x : ℝ) : ℂ := starRingEnd ℂ (a r (e x)) * (q r (e x))⁻¹

theorem e_ne_zero (x : ℝ) : e x ≠ 0 := by
  intro h; have := norm_e x; rw [h, norm_zero] at this; exact zero_ne_one this

theorem e_sub_ne_zero (hr0 : 0 < r) (hr1 : r < 1) (x : ℝ) : e x - (r : ℂ) ≠ 0 := by
  intro h
  have h1 : e x = (r : ℂ) := sub_eq_zero.mp h
  have := norm_e x
  rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0] at this
  linarith

theorem e_pow (x : ℝ) (j : ℕ) : e x ^ j = fourier (j : ℤ) (x : AddCircle (1 : ℝ)) := by
  rw [fourier_coe_apply, e, circleMap_zero, Complex.ofReal_one, one_mul, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem interval_integral_conj {f : ℝ → ℂ} :
    ∫ x in (0 : ℝ)..1, starRingEnd ℂ (f x) = starRingEnd ℂ (∫ x in (0 : ℝ)..1, f x) := by
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  exact integral_conj

/-- Cauchy's formula on the unit circle, in the parametrization `e`. -/
theorem integral_e_cauchy (hr0 : 0 < r) (hr1 : r < 1) (j : ℕ) :
    ∫ x in (0 : ℝ)..1, e x ^ (j + 1) * a r (e x) * (e x - (r : ℂ))⁻¹ =
      (r : ℂ) ^ j * a r (r : ℂ) := by
  set G : ℂ → ℂ := fun z => z ^ j * a r z with hG
  have hdiff : ∀ z : ℂ, ‖z‖ < 1 / r → DifferentiableAt ℂ G z := fun z hz =>
    (differentiableAt_id.pow j).mul ((differentiableAt_q z).mul (differentiableAt_g hr0 hz))
  have hone := one_lt_inv hr0 hr1
  have hw : (r : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    exact hr1
  have hC := circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (R := 1) (c := 0) (w := (r : ℂ)) (f := G) Set.countable_empty hw
    (fun z hz => (hdiff z (by
      rw [mem_closedBall, dist_zero_right] at hz; linarith)).continuousAt.continuousWithinAt)
    (fun z hz => hdiff z (by
      have := hz.1; rw [mem_ball, dist_zero_right] at this; linarith))
  rw [circleIntegral] at hC
  set φ : ℝ → ℂ := fun θ => deriv (circleMap 0 1) θ •
    ((circleMap 0 1 θ - (r : ℂ))⁻¹ • G (circleMap 0 1 θ)) with hφ
  have hsub : ∫ x in (0 : ℝ)..1, φ (2 * π * x) =
      (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, φ θ := by
    rw [intervalIntegral.integral_comp_mul_left φ (by positivity : (2 * π : ℝ) ≠ 0), mul_zero,
      mul_one]
  have hpt : ∀ x : ℝ, φ (2 * π * x) =
      I * (e x ^ (j + 1) * a r (e x) * (e x - (r : ℂ))⁻¹) := by
    intro x
    simp only [hφ, hG, deriv_circleMap, smul_eq_mul]
    rw [show circleMap 0 1 (2 * π * x) = e x from rfl]
    ring
  simp_rw [hpt] at hsub
  rw [intervalIntegral.integral_const_mul, hC] at hsub
  have hI : I ≠ 0 := I_ne_zero
  simp only [smul_eq_mul, real_smul, hG] at hsub
  have hpi' : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  apply mul_left_cancel₀ hI
  rw [hsub]
  push_cast
  field_simp

/-- Fourier coefficients of `H` at nonnegative frequencies: `r^j · conj(a(r))`. -/
theorem fourierCoeff_H (hr0 : 0 < r) (hr1 : r < 1) (j : ℕ) :
    fourierCoeff (circleLift (H r)) (j : ℤ) = (r : ℂ) ^ j * starRingEnd ℂ (a r (r : ℂ)) := by
  rw [fourierCoeff_circleLift]
  have hpt : ∀ x : ℝ, starRingEnd ℂ (fourier (-(j : ℤ)) (x : AddCircle (1 : ℝ)) * H r x) =
      e x ^ (j + 1) * a r (e x) * (e x - (r : ℂ))⁻¹ := by
    intro x
    have hex := e_ne_zero x
    have hexr := e_sub_ne_zero hr0 hr1 x
    rw [map_mul, fourier_neg, Complex.conj_conj, ← e_pow, H, map_mul, Complex.conj_conj,
      map_inv₀, q, map_sub, map_one, map_mul, Complex.conj_ofReal, conj_e]
    field_simp
    ring
  have h := interval_integral_conj (f := fun x => fourier (-(j : ℤ)) (x : AddCircle (1 : ℝ)) * H r x)
  simp_rw [hpt] at h
  rw [integral_e_cauchy hr0 hr1 j] at h
  have h2 := congrArg (starRingEnd ℂ) h
  rw [Complex.conj_conj] at h2
  rw [← h2, map_mul, map_pow, Complex.conj_ofReal]

theorem a_r_norm_sq (hr0 : 0 < r) (hr1 : r < 1) : ‖a r (r : ℂ)‖ ^ 2 = 1 - r ^ 2 := by
  have hs : ‖(r : ℂ)‖ < 1 / r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    exact lt_trans hr1 (one_lt_inv hr0 hr1)
  have h := congrArg norm (a_sq hr0 hs)
  rw [norm_pow] at h
  rw [h, q]
  have : (1 : ℂ) - (r : ℂ) * (r : ℂ) = ((1 - r ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by nlinarith)]

/-! ## General circle `L²` facts -/

private theorem haarAddCircle_eq_volume :
    (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) = volume := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simp

/-- Parseval on the circle: `‖w‖² = Σ_n |ŵ(n)|²`. -/
theorem norm_sq_eq_tsum_fourierCoeff (w : CCMCircleL2) :
    ‖w‖ ^ 2 = ∑' n : ℤ, ‖fourierCoeff ((w : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) n‖ ^ 2 := by
  have hP := (fourierBasis (T := (1 : ℝ))).tsum_inner_mul_inner w w
  have hrepr : ∀ n : ℤ, inner ℂ ((fourierBasis (T := (1 : ℝ))) n) w =
      fourierCoeff ((w : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) n := by
    intro n
    rw [← (fourierBasis (T := (1 : ℝ))).repr_apply_apply, fourierBasis_repr]
  have hterm : ∀ n : ℤ, inner ℂ w ((fourierBasis (T := (1 : ℝ))) n) *
      inner ℂ ((fourierBasis (T := (1 : ℝ))) n) w =
      ((‖fourierCoeff ((w : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) n‖ ^ 2 : ℝ) : ℂ) := by
    intro n
    rw [← inner_conj_symm, hrepr, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [hterm] at hP
  rw [@norm_sq_eq_re_inner ℂ, ← hP, ← Complex.ofReal_tsum]
  exact Complex.ofReal_re _

/-- The Hardy projection keeps exactly the nonnegative Fourier modes. -/
theorem norm_sq_hardy_eq_tsum (v : CCMCircleL2) :
    ‖ccmCircleHardyProjection v‖ ^ 2 =
      ∑' n : ℕ, ‖fourierCoeff ((v : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ^ 2 := by
  rw [norm_sq_eq_tsum_fourierCoeff]
  have hc : ∀ n : ℤ, fourierCoeff ((ccmCircleHardyProjection v : CCMCircleL2) :
      AddCircle (1 : ℝ) → ℂ) n =
      if 0 ≤ n then fourierCoeff ((v : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) n else 0 := by
    intro n
    rw [← GaloisForLFunctions.inner_fourierLp_eq_fourierCoeff,
      inner_fourierLp_ccmCircleHardyProjection, GaloisForLFunctions.inner_fourierLp_eq_fourierCoeff]
  simp_rw [hc]
  have hsupp : Function.support (fun n : ℤ =>
      ‖if 0 ≤ n then fourierCoeff ((v : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) n else 0‖ ^ 2) ⊆
      Set.range (Nat.cast : ℕ → ℤ) := by
    intro n hn
    by_contra hnot
    apply hn
    have hneg : ¬ 0 ≤ n := fun h => hnot ⟨n.toNat, Int.toNat_of_nonneg h⟩
    simp [hneg]
  rw [← Function.Injective.tsum_eq Nat.cast_injective hsupp]
  refine tsum_congr fun n => ?_
  simp

/-- A circle vector without negative Fourier modes is fixed by the Hardy projection. -/
theorem hardy_eq_self_of_fourierCoeff_neg (v : CCMCircleL2)
    (hv : ∀ n : ℤ, n < 0 → fourierCoeff ((v : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) n = 0) :
    ccmCircleHardyProjection v = v := by
  apply (fourierBasis (T := (1 : ℝ))).repr.injective
  ext n
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, coe_fourierBasis,
    inner_fourierLp_ccmCircleHardyProjection]
  by_cases hn : 0 ≤ n
  · rw [if_pos hn]
  · rw [if_neg hn, GaloisForLFunctions.inner_fourierLp_eq_fourierCoeff, hv n (by omega)]

/-- `L²` norm of a continuous periodic function. -/
theorem norm_sq_circleLiftLp {f : ℝ → ℂ} (hf : Function.Periodic f 1) (hc : Continuous f) :
    ‖circleLiftLp hf hc‖ ^ 2 = ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 := by
  have h := tsum_conj_fourierCoeff_mul_fourierCoeff hf hc hf hc
  have hleft : ∑' n : ℤ, starRingEnd ℂ (fourierCoeff (circleLift f) n) *
      fourierCoeff (circleLift f) n =
      ((∑' n : ℤ, ‖fourierCoeff (circleLift f) n‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hright : ∫ x in (0 : ℝ)..1, starRingEnd ℂ (f x) * f x =
      ((∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hleft, hright] at h
  rw [norm_sq_eq_tsum_fourierCoeff, fourierCoeff_circleLiftLp]
  exact_mod_cast h

/-! ## The test vector and the seam estimate -/

theorem periodic_e : Function.Periodic e 1 := by
  intro x
  simp only [e, mul_add, mul_one]
  exact periodic_circleMap 0 1 _

theorem periodic_H : Function.Periodic (H r) 1 := fun x => by simp only [H, periodic_e x]

theorem continuous_H (hr0 : 0 < r) (hr1 : r < 1) : Continuous (H r) := by
  have he : Continuous e := (continuous_circleMap 0 1).comp (continuous_const.mul continuous_id)
  have ha : Continuous (fun x => a r (e x)) := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    have hs := norm_e_lt hr0 hr1 x
    exact ((differentiableAt_q (e x)).mul (differentiableAt_g hr0 hs)).continuousAt.comp
      he.continuousAt
  have hq : Continuous (fun x => q r (e x)) :=
    continuous_const.sub (continuous_const.mul he)
  exact (Complex.continuous_conj.comp ha).mul
    (hq.inv₀ fun x => q_ne_zero hr0 (norm_e_lt hr0 hr1 x))

theorem conj_phase_mul_g_eq_H (hr0 : 0 < r) (hr1 : r < 1) (z : AddCircle (1 : ℝ)) :
    starRingEnd ℂ ((qDatum hr0 hr1).circlePhase.toFun z) *
        circleLift (gDatum hr0 hr1).value z = circleLift (H r) z := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [DiscArgumentDatum.circlePhase_toFun, circleLift_coe (qDatum hr0 hr1).periodic_phase,
    circleLift_coe (gDatum hr0 hr1).periodic_value, circleLift_coe periodic_H]
  exact conj_phase_mul_g hr0 hr1 x

/-- The test vector: boundary values of `g = q^{-1/2}`. -/
def testVector (hr0 : 0 < r) (hr1 : r < 1) : CCMCircleL2 :=
  circleLiftLp (gDatum hr0 hr1).periodic_value (gDatum hr0 hr1).contDiff_value.continuous

theorem hardy_testVector (hr0 : 0 < r) (hr1 : r < 1) :
    ccmCircleHardyProjection (testVector hr0 hr1) = testVector hr0 hr1 := by
  apply hardy_eq_self_of_fourierCoeff_neg
  intro n hn
  rw [testVector, fourierCoeff_circleLiftLp]
  exact (gDatum hr0 hr1).fourierCoeff_circleLift_value_of_neg hn

theorem fourierCoeff_conjMultiplier_testVector (hr0 : 0 < r) (hr1 : r < 1) :
    fourierCoeff (((qDatum hr0 hr1).circlePhase.conjMultiplier (testVector hr0 hr1) :
      CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) = fourierCoeff (circleLift (H r)) := by
  apply fourierCoeff_congr_ae
  filter_upwards [(qDatum hr0 hr1).circlePhase.conjMultiplier_coeFn (testVector hr0 hr1),
    circleLiftLp_coeFn (gDatum hr0 hr1).periodic_value
      (gDatum hr0 hr1).contDiff_value.continuous] with z h1 h2
  rw [h1, show ((testVector hr0 hr1 : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) z =
      circleLift (gDatum hr0 hr1).value z from h2]
  exact conj_phase_mul_g_eq_H hr0 hr1 z

/-- `‖P(U† g)‖ = 1` exactly. -/
theorem norm_sq_hardy_adjoint_testVector (hr0 : 0 < r) (hr1 : r < 1) :
    ‖ccmCircleHardyProjection ((qDatum hr0 hr1).circlePhase.conjMultiplier
      (testVector hr0 hr1))‖ ^ 2 = 1 := by
  rw [norm_sq_hardy_eq_tsum, fourierCoeff_conjMultiplier_testVector]
  have hterm : ∀ n : ℕ, ‖fourierCoeff (circleLift (H r)) (n : ℤ)‖ ^ 2 =
      (1 - r ^ 2) * (r ^ 2) ^ n := by
    intro n
    rw [fourierCoeff_H hr0 hr1 n, norm_mul, norm_pow, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr0, mul_pow, a_r_norm_sq hr0 hr1, ← pow_mul, ← pow_mul]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) (by nlinarith)]
  have : (1 : ℝ) - r ^ 2 ≠ 0 := by nlinarith
  field_simp

/-- Seam lower bound from a Hardy-space test vector. -/
theorem seam_sq_mul_ge (D : RestrictedUnitaryDatum CCMCircleL2) (f : CCMCircleL2)
    (hf : D.projection f = f) :
    ‖f‖ ^ 2 - ‖D.projection (ContinuousLinearMap.adjoint D.unitary f)‖ ^ 2 ≤
      ‖D.adjointHankelSeam‖ ^ 2 * ‖f‖ ^ 2 := by
  set P := D.projection
  set U := D.unitary
  have hUU : ∀ w, U (ContinuousLinearMap.adjoint U w) = w := fun w => by
    have := congrArg (fun T : CCMCircleL2 →L[ℂ] CCMCircleL2 => T w) D.unitary_mul_adjoint
    simpa [mul_apply_eq_comp] using this
  have hiso : ‖ContinuousLinearMap.adjoint U f‖ = ‖f‖ := by
    have hsq : ‖ContinuousLinearMap.adjoint U f‖ ^ 2 = ‖f‖ ^ 2 := by
      rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, adjoint_inner_left, hUU]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq
  have happ : D.adjointHankelSeam f =
      ContinuousLinearMap.adjoint U f - P (ContinuousLinearMap.adjoint U f) := by
    change ((1 - P) * ContinuousLinearMap.adjoint U * P) f = _
    simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self]
    rw [show P f = f from hf]
  have hpy := norm_sq_eq_add_of_orthogonalProjection P D.projection_idempotent
    D.projection_adjoint (ContinuousLinearMap.adjoint U f)
  rw [hiso] at hpy
  have hle : ‖D.adjointHankelSeam f‖ ≤ ‖D.adjointHankelSeam‖ * ‖f‖ :=
    ContinuousLinearMap.le_opNorm _ _
  rw [happ] at hle
  have h0 : 0 ≤ ‖ContinuousLinearMap.adjoint U f - P (ContinuousLinearMap.adjoint U f)‖ :=
    norm_nonneg _
  nlinarith [mul_self_le_mul_self h0 hle]

/-! ## The test vector is large -/

theorem norm_sq_g_e (hr0 : 0 < r) (hr1 : r < 1) (x : ℝ) :
    ‖g r (e x)‖ ^ 2 = ‖q r (e x)‖⁻¹ := by
  rw [← norm_pow, g_sq hr0 (norm_e_lt hr0 hr1 x), norm_inv]

theorem norm_q_e_le (hr0 : 0 < r) (hr1 : r < 1) {x : ℝ} (hx : 0 ≤ x) :
    ‖q r (e x)‖ ≤ (1 - r) + 2 * π * x := by
  have hsplit : q r (e x) = ((1 - r : ℝ) : ℂ) + (r : ℂ) * (1 - e x) := by
    simp only [q]; push_cast; ring
  have hchord : ‖1 - e x‖ ≤ 2 * π * x := by
    rw [norm_sub_rev, e, circleMap_zero, Complex.ofReal_one, one_mul,
      show ((2 * π * x : ℝ) : ℂ) * I = I * ((2 * π * x : ℝ) : ℂ) by ring]
    calc ‖Complex.exp (I * ((2 * π * x : ℝ) : ℂ)) - 1‖ ≤ ‖(2 * π * x : ℝ)‖ :=
          Real.norm_exp_I_mul_ofReal_sub_one_le
      _ = 2 * π * x := by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hsplit]
  calc ‖((1 - r : ℝ) : ℂ) + (r : ℂ) * (1 - e x)‖
      ≤ ‖((1 - r : ℝ) : ℂ)‖ + ‖(r : ℂ) * (1 - e x)‖ := norm_add_le _ _
    _ = (1 - r) + r * ‖1 - e x‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), norm_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    _ ≤ (1 - r) + 1 * ‖1 - e x‖ := by gcongr
    _ ≤ (1 - r) + 2 * π * x := by linarith

theorem continuous_norm_q_e_inv (hr0 : 0 < r) (hr1 : r < 1) :
    Continuous (fun x => ‖q r (e x)‖⁻¹) := by
  have he : Continuous e := (continuous_circleMap 0 1).comp (continuous_const.mul continuous_id)
  exact ((continuous_const.sub (continuous_const.mul he)).norm).inv₀ fun x =>
    norm_ne_zero_iff.mpr (q_ne_zero hr0 (norm_e_lt hr0 hr1 x))

/-- `‖g‖² ≥ (1/2π) log(1 + π/(1 − r))`. -/
theorem log_le_norm_sq_testVector (hr0 : 0 < r) (hr1 : r < 1) :
    Real.log (1 + π / (1 - r)) / (2 * π) ≤ ‖testVector hr0 hr1‖ ^ 2 := by
  rw [testVector, norm_sq_circleLiftLp]
  simp_rw [gDatum_value, norm_sq_g_e hr0 hr1]
  have hc := continuous_norm_q_e_inv hr0 hr1
  have hpos : ∀ x, 0 ≤ ‖q r (e x)‖⁻¹ := fun x => inv_nonneg.mpr (norm_nonneg _)
  have hsplit : ∫ x in (0 : ℝ)..1, ‖q r (e x)‖⁻¹ =
      (∫ x in (0 : ℝ)..(1 / 2), ‖q r (e x)‖⁻¹) + ∫ x in (1 / 2 : ℝ)..1, ‖q r (e x)‖⁻¹ :=
    (intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)).symm
  have hsecond : 0 ≤ ∫ x in (1 / 2 : ℝ)..1, ‖q r (e x)‖⁻¹ :=
    intervalIntegral.integral_nonneg (by norm_num) fun x _ => hpos x
  have hc1r : 0 < 1 - r := by linarith
  have hden : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2), 0 < (1 - r) + 2 * π * x := fun x hx => by
    have := hx.1; positivity
  have hmono : ∫ x in (0 : ℝ)..(1 / 2), ((1 - r) + 2 * π * x)⁻¹ ≤
      ∫ x in (0 : ℝ)..(1 / 2), ‖q r (e x)‖⁻¹ := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact ContinuousOn.intervalIntegrable (fun x hx => by
        have hx' : x ∈ Set.Icc (0 : ℝ) (1 / 2) := by
          rw [Set.uIcc_of_le (by norm_num)] at hx; exact hx
        exact ((continuous_const.add (continuous_const.mul continuous_id)).continuousAt.inv₀
          (hden x hx').ne').continuousWithinAt)
    · exact hc.intervalIntegrable _ _
    · intro x hx
      have hq := norm_q_e_le hr0 hr1 hx.1
      have hqpos : 0 < ‖q r (e x)‖ :=
        norm_pos_iff.mpr (q_ne_zero hr0 (norm_e_lt hr0 hr1 x))
      exact inv_anti₀ hqpos hq
  have hexact : ∫ x in (0 : ℝ)..(1 / 2), ((1 - r) + 2 * π * x)⁻¹ =
      Real.log (1 + π / (1 - r)) / (2 * π) := by
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (1 / 2),
        HasDerivAt (fun y => Real.log ((1 - r) + 2 * π * y) / (2 * π))
          (((1 - r) + 2 * π * x)⁻¹) x := by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num)] at hx
      have hlin : HasDerivAt (fun y => (1 - r) + 2 * π * y) (2 * π) x := by
        simpa using ((hasDerivAt_id x).const_mul (2 * π)).const_add (1 - r)
      have h := (hlin.log (hden x hx).ne').div_const (2 * π)
      have hpi : (2 * π : ℝ) ≠ 0 := by positivity
      have hne := (hden x hx).ne'
      refine h.congr_deriv ?_
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (ContinuousOn.intervalIntegrable (fun x hx => by
        rw [Set.uIcc_of_le (by norm_num)] at hx
        exact ((continuous_const.add (continuous_const.mul continuous_id)).continuousAt.inv₀
          (hden x hx).ne').continuousWithinAt))]
    rw [mul_zero, add_zero, ← sub_div, ← Real.log_div (by positivity) hc1r.ne']
    congr 2
    field_simp
  rw [hsplit, ← hexact]
  linarith

/-! ## Main results -/

/-- **Explicit seam bound for the zero-free linear phase.**  For `u = q/|q|`, `q(z) = 1 − r z`,
`‖(1 − P) U† P‖² ≥ 1 − 2π / log(1 + π/(1 − r))`. -/
theorem one_sub_le_norm_sq_adjointSeam (hr0 : 0 < r) (hr1 : r < 1) :
    1 - 2 * π / Real.log (1 + π / (1 - r)) ≤
      ‖(qDatum hr0 hr1).circlePhase.datum.adjointHankelSeam‖ ^ 2 := by
  set D := (qDatum hr0 hr1).circlePhase.datum with hD
  set f := testVector hr0 hr1
  have hP : D.projection f = f := hardy_testVector hr0 hr1
  have hU : ContinuousLinearMap.adjoint D.unitary = (qDatum hr0 hr1).circlePhase.conjMultiplier :=
    (qDatum hr0 hr1).circlePhase.adjoint_multiplier
  have hineq := seam_sq_mul_ge D f hP
  rw [hU] at hineq
  change ‖f‖ ^ 2 - ‖ccmCircleHardyProjection
    ((qDatum hr0 hr1).circlePhase.conjMultiplier f)‖ ^ 2 ≤ _ at hineq
  rw [norm_sq_hardy_adjoint_testVector hr0 hr1] at hineq
  have hL := log_le_norm_sq_testVector hr0 hr1
  have hlogpos : 0 < Real.log (1 + π / (1 - r)) := by
    apply Real.log_pos
    have : 0 < π / (1 - r) := div_pos Real.pi_pos (by linarith)
    linarith
  have hLpos : 0 < Real.log (1 + π / (1 - r)) / (2 * π) := by positivity
  have hfpos : 0 < ‖f‖ ^ 2 := lt_of_lt_of_le hLpos hL
  have h1 : 1 - 1 / ‖f‖ ^ 2 ≤ ‖D.adjointHankelSeam‖ ^ 2 := by
    have key : (1 - 1 / ‖f‖ ^ 2) * ‖f‖ ^ 2 ≤ ‖D.adjointHankelSeam‖ ^ 2 * ‖f‖ ^ 2 := by
      have : (1 - 1 / ‖f‖ ^ 2) * ‖f‖ ^ 2 = ‖f‖ ^ 2 - 1 := by
        rw [sub_mul, one_mul, one_div, inv_mul_cancel₀ hfpos.ne']
      rw [this]; exact hineq
    exact le_of_mul_le_mul_right key hfpos
  have h2 : 1 / ‖f‖ ^ 2 ≤ 2 * π / Real.log (1 + π / (1 - r)) := by
    rw [div_le_div_iff₀ hfpos hlogpos]
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * π)).mp hL
    linarith
  linarith

/-- **No uniform seam margin for zero-free phases.**  For every `ε > 0` some zero-free disc datum
has adjoint Hankel seam of norm `> 1 − ε`.  No producer using only holomorphy and zero-freeness of
the boundary phase can give a seam bound bounded away from one. -/
theorem exists_datum_adjointSeam_gt (ε : ℝ) (hε : 0 < ε) :
    ∃ D : DiscArgumentDatum, 1 - ε < ‖D.circlePhase.datum.adjointHankelSeam‖ := by
  set M := Real.exp (2 * π / ε) with hM
  have hM1 : 1 < M := Real.one_lt_exp_iff.mpr (by positivity)
  set r := 1 - π / (M + π) with hr
  have hpiM : 0 < π / (M + π) := div_pos Real.pi_pos (by linarith [Real.pi_pos])
  have hpiM1 : π / (M + π) < 1 := by
    rw [div_lt_one (by linarith [Real.pi_pos])]; linarith
  have hr0 : 0 < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  refine ⟨qDatum hr0 hr1, ?_⟩
  have hbound := one_sub_le_norm_sq_adjointSeam hr0 hr1
  have h1r : 1 - r = π / (M + π) := by rw [hr]; ring
  have h2 : π / (1 - r) = M + π := by
    rw [h1r]
    have : M + π ≠ 0 := by linarith [Real.pi_pos]
    field_simp
  have hlog : 2 * π / ε < Real.log (1 + π / (1 - r)) := by
    rw [h2, show 2 * π / ε = Real.log M from (Real.log_exp _).symm]
    exact Real.log_lt_log (by linarith) (by linarith [Real.pi_pos])
  have hlogpos : 0 < Real.log (1 + π / (1 - r)) := lt_trans (by positivity) hlog
  have hsmall : 2 * π / Real.log (1 + π / (1 - r)) < ε := by
    rw [div_lt_iff₀ hlogpos]
    have := (div_lt_iff₀ hε).mp hlog
    linarith
  set x := ‖(qDatum hr0 hr1).circlePhase.datum.adjointHankelSeam‖
  have hx0 : 0 ≤ x := norm_nonneg _
  have hsq : 1 - ε < x ^ 2 := by linarith
  by_cases hx1 : 1 ≤ x
  · linarith
  · push Not at hx1
    nlinarith

end LinearPhaseSeam

end RHTower
