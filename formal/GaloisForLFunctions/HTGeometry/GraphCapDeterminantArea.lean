import Mathlib

/-!
# Determinant-line area of a radial Kähler potential

On the graph cell of the restricted Grassmannian the determinant line carries the Kähler form
`ω_det = (i/2π) ∂∂̄ log det(I + Z*Z)`.  Along a graph cap `z ↦ zA` with `K = A*A` of eigenvalues
`λ_j` the pulled-back potential is radial, `Φ(z) = ψ(|z|²)` with `ψ(s) = ∑ log(1 + λ_j s)`.  In the
coordinate `z = x + iy` one has `(i/2π) ∂∂̄ Φ = (1/4π) ΔΦ dx ∧ dy`.

* `laplacian_radial`: `Δ(ψ(|z|²)) = 4(ψ'(s) + s ψ''(s))`, `s = |z|²`.
* `integral_ball_radial`: the disk integral of a radial density reduces to `2π ∫₀¹ r G(r) dr`.
* `logDetSeries` and its first two derivatives for a nonnegative summable spectrum.
* `capArea_eq_tsum` **(BGCA.4)–(BGCA.6)**: the determinant-line area of the cap over the unit disk is
  `∑ λ_j/(1 + λ_j)`.
* `schubertArea_eq_one`: the full rank-one cap over `ℂ` has area one — the normalization making the
  determinant line integral.
-/

open MeasureTheory Set Filter Topology Metric Laplacian InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace Real

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The Laplacian of a radial function on `ℂ` -/

theorem real_inner_complex (z u : ℂ) : ⟪z, u⟫_ℝ = z.re * u.re + z.im * u.im := by
  rw [Complex.inner]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **Laplacian of a radial function.**  If `ψ` and `ψ'` are differentiable on `[0, ∞)` with
derivatives `ψ₁`, `ψ₂`, then `Δ (ψ(|z|²)) = 4 (ψ₁(s) + s ψ₂(s))` with `s = |z|²`. -/
theorem laplacian_radial {ψ ψ₁ ψ₂ : ℝ → ℝ}
    (h₁ : ∀ s, 0 ≤ s → HasDerivAt ψ (ψ₁ s) s) (h₂ : ∀ s, 0 ≤ s → HasDerivAt ψ₁ (ψ₂ s) s) (z : ℂ) :
    Δ (fun w : ℂ => ψ (‖w‖ ^ 2)) z = 4 * (ψ₁ (‖z‖ ^ 2) + ‖z‖ ^ 2 * ψ₂ (‖z‖ ^ 2)) := by
  set f : ℂ → ℝ := fun w => ψ (‖w‖ ^ 2) with hf
  have hfd : ∀ w : ℂ, HasFDerivAt f (ψ₁ (‖w‖ ^ 2) • (2 • innerSL ℝ w)) w := fun w =>
    (h₁ _ (by positivity)).comp_hasFDerivAt w (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  have hfderiv : fderiv ℝ f = fun w => ψ₁ (‖w‖ ^ 2) • (2 • innerSL ℝ w) :=
    funext fun w => (hfd w).fderiv
  -- the directional derivative `w ↦ ∂_u f(w) = 2 ψ₁(|w|²) ⟪w, u⟫`
  have hdir : ∀ u w : ℂ, fderiv ℝ f w u = 2 * ψ₁ (‖w‖ ^ 2) * ⟪u, w⟫_ℝ := by
    intro u w
    rw [hfderiv]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
      Nat.cast_ofNat, real_inner_comm]
    ring
  have hψ₁ : ∀ w : ℂ, HasFDerivAt (fun w : ℂ => ψ₁ (‖w‖ ^ 2)) (ψ₂ (‖w‖ ^ 2) • (2 • innerSL ℝ w)) w :=
    fun w => (h₂ _ (by positivity)).comp_hasFDerivAt w (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  have hsecond : ∀ u : ℂ, iteratedFDeriv ℝ 2 f z ![u, u] =
      2 * ψ₁ (‖z‖ ^ 2) * ⟪u, u⟫_ℝ + 4 * ψ₂ (‖z‖ ^ 2) * ⟪u, z⟫_ℝ ^ 2 := by
    intro u
    rw [iteratedFDeriv_two_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hdiff : DifferentiableAt ℝ (fderiv ℝ f) z := by
      rw [hfderiv]
      exact ((hψ₁ z).differentiableAt).smul ((innerSL ℝ).differentiableAt.const_smul 2)
    have hcomp : fderiv ℝ (fun y => (fderiv ℝ f y) u) z
        = (ContinuousLinearMap.apply ℝ ℝ u).comp (fderiv ℝ (fderiv ℝ f) z) := by
      rw [show (fun y => (fderiv ℝ f y) u) = (ContinuousLinearMap.apply ℝ ℝ u) ∘ (fderiv ℝ f) from rfl,
        fderiv_comp z (ContinuousLinearMap.apply ℝ ℝ u).differentiableAt hdiff,
        ContinuousLinearMap.fderiv]
    have h1 : (fderiv ℝ (fderiv ℝ f) z u) u = fderiv ℝ (fun y => (fderiv ℝ f y) u) z u := by
      rw [hcomp]
      rfl
    rw [h1]
    have hg : HasFDerivAt (fun y => (fderiv ℝ f y) u)
        ((2 * ψ₁ (‖z‖ ^ 2)) • innerSL ℝ u + ⟪u, z⟫_ℝ • (2 • ψ₂ (‖z‖ ^ 2) • (2 • innerSL ℝ z))) z := by
      have e : (fun y => (fderiv ℝ f y) u) = fun y => (2 * ψ₁ (‖y‖ ^ 2)) * ⟪u, y⟫_ℝ :=
        funext fun y => by rw [hdir]
      rw [e]
      have ha : HasFDerivAt (fun y : ℂ => 2 * ψ₁ (‖y‖ ^ 2)) (2 • ψ₂ (‖z‖ ^ 2) • (2 • innerSL ℝ z)) z := by
        have := (hψ₁ z).const_mul 2
        simpa [two_smul, smul_add] using this
      have hb : HasFDerivAt (fun y : ℂ => ⟪u, y⟫_ℝ) (innerSL ℝ u) z :=
        (innerSL ℝ u).hasFDerivAt
      exact ha.mul hb
    rw [hg.fderiv]
    simp only [add_apply, smul_apply, innerSL_apply_apply,
      smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, real_inner_comm z u]
    ring
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only
  rw [hsecond, hsecond, real_inner_complex, real_inner_complex, real_inner_complex,
    real_inner_complex]
  have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  rw [hz]
  ring

/-! ## Disk integrals of radial densities -/

theorem volume_real_ball_one_complex : (volume : Measure ℂ).real (ball (0 : ℂ) 1) = π := by
  rw [Measure.real, Complex.volume_ball]
  simp

/-- **Polar reduction.**  `∫_{|z|<1} G(|z|) = 2π ∫₀¹ r G(r) dr`. -/
theorem integral_ball_radial (G : ℝ → ℝ) :
    ∫ z in ball (0 : ℂ) 1, G ‖z‖ = 2 * π * ∫ r in (0 : ℝ)..1, r * G r := by
  set g : ℝ → ℝ := fun r => if r < 1 then G r else 0 with hg
  have h1 : ∫ z in ball (0 : ℂ) 1, G ‖z‖ = ∫ z : ℂ, g ‖z‖ := by
    rw [← integral_indicator measurableSet_ball]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [Set.indicator, mem_ball_zero_iff]
    rfl
  have h2 := integral_fun_norm_addHaar (volume : Measure ℂ) g
  rw [Complex.finrank_real_complex, volume_real_ball_one_complex] at h2
  have h3 : ∫ r in Ioi (0 : ℝ), r ^ (2 - 1) • g r = ∫ r in (0 : ℝ)..1, r * G r := by
    have e : (fun r : ℝ => r ^ (2 - 1) • g r) = (Iio 1).indicator (fun r => r * G r) := by
      funext r
      simp only [hg, Set.indicator_apply, Set.mem_Iio, smul_eq_mul]
      split_ifs <;> simp
    rw [e, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio, intervalIntegral.integral_of_le
      zero_le_one, integral_Ioc_eq_integral_Ioo]
  rw [h1, h2, h3, nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat, mul_assoc]

/-- **The determinant-line area of a radial cap** over the unit disk:
`∫_D (1/4π) Δ ψ(|z|²)`. -/
def radialCapArea (ψ : ℝ → ℝ) : ℝ :=
  ∫ z in ball (0 : ℂ) 1, (1 / (4 * π)) * Δ (fun w : ℂ => ψ (‖w‖ ^ 2)) z

/-- **The area is the boundary slope**: `∫_D (1/4π) Δ ψ(|z|²) = ψ'(1)`, because
`2r(ψ'(r²) + r²ψ''(r²)) = (d/dr)(r² ψ'(r²))`. -/
theorem radialCapArea_eq {ψ ψ₁ ψ₂ : ℝ → ℝ}
    (h₁ : ∀ s, 0 ≤ s → HasDerivAt ψ (ψ₁ s) s) (h₂ : ∀ s, 0 ≤ s → HasDerivAt ψ₁ (ψ₂ s) s)
    (hc : ContinuousOn ψ₂ (Ici 0)) : radialCapArea ψ = ψ₁ 1 := by
  set G : ℝ → ℝ := fun r => (1 / π) * (ψ₁ (r ^ 2) + r ^ 2 * ψ₂ (r ^ 2)) with hG
  have hint : ∀ z : ℂ, (1 / (4 * π)) * Δ (fun w : ℂ => ψ (‖w‖ ^ 2)) z = G ‖z‖ := by
    intro z
    rw [laplacian_radial h₁ h₂ z, hG]
    field_simp
  rw [radialCapArea, integral_congr_ae (Eventually.of_forall hint), integral_ball_radial]
  have hc₁ : Continuous fun r : ℝ => ψ₁ (r ^ 2) := by
    refine ContinuousOn.comp_continuous (s := Ici 0) (fun s hs => ?_) (continuous_pow 2)
      fun r => sq_nonneg r
    exact (h₂ s hs).continuousAt.continuousWithinAt
  have hc₂ : Continuous fun r : ℝ => ψ₂ (r ^ 2) :=
    hc.comp_continuous (continuous_pow 2) fun r => sq_nonneg r
  have hF : ∀ r ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r => r ^ 2 * ψ₁ (r ^ 2))
      (2 * π * (r * G r)) r := by
    intro r _
    have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by simpa using hasDerivAt_pow 2 r
    have hd := hp.mul ((h₂ (r ^ 2) (sq_nonneg r)).comp (h := fun x : ℝ => x ^ 2) r hp)
    have hd' : HasDerivAt (fun r => r ^ 2 * ψ₁ (r ^ 2))
        (2 * r * ψ₁ (r ^ 2) + r ^ 2 * (ψ₂ (r ^ 2) * (2 * r))) r := hd
    refine hd'.congr_deriv ?_
    rw [hG]
    have := Real.pi_pos
    field_simp
  have hFi : IntervalIntegrable (fun r => 2 * π * (r * G r)) volume 0 1 := by
    refine Continuous.intervalIntegrable ?_ 0 1
    simp only [hG]
    exact continuous_const.mul (continuous_id.mul (continuous_const.mul
      (hc₁.add ((continuous_pow 2).mul hc₂))))
  rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_eq_sub_of_hasDerivAt hF hFi]
  simp

/-! ## The log-determinant series of a nonnegative summable spectrum -/

section LogDet

variable {ι : Type*} {ev : ι → ℝ}

/-- `ψ(s) = ∑ log(1 + λ_j s) = log det(I + sK)`. -/
def logDetSeries (ev : ι → ℝ) (s : ℝ) : ℝ := ∑' i, Real.log (1 + ev i * s)

/-- `ψ'(s) = ∑ λ_j / (1 + λ_j s)`. -/
def logDetSeries₁ (ev : ι → ℝ) (s : ℝ) : ℝ := ∑' i, ev i / (1 + ev i * s)

/-- `ψ''(s) = -∑ λ_j² / (1 + λ_j s)²`. -/
def logDetSeries₂ (ev : ι → ℝ) (s : ℝ) : ℝ := ∑' i, -(ev i ^ 2 / (1 + ev i * s) ^ 2)

/-- A radius `δ > 0` with `1 + λ_j s > 1/2` for all `s > -δ`. -/
def logDetRadius (ev : ι → ℝ) : ℝ := 1 / (2 * ∑' i, ev i + 2)

variable (hev : ∀ i, 0 ≤ ev i) (hsum : Summable ev)
include hev hsum

omit hsum in
theorem logDetRadius_pos : 0 < logDetRadius ev := by
  have : 0 ≤ ∑' i, ev i := tsum_nonneg hev
  unfold logDetRadius
  positivity

theorem half_lt_one_add {s : ℝ} (hs : -logDetRadius ev < s) (i : ι) : 1 / 2 < 1 + ev i * s := by
  have hle : ev i ≤ ∑' j, ev j := hsum.le_tsum i fun j _ => hev j
  have hT : 0 ≤ ∑' i, ev i := tsum_nonneg hev
  rcases le_or_gt 0 s with h0 | h0
  · nlinarith [hev i]
  · have hδ : ev i * logDetRadius ev < 1 / 2 := by
      unfold logDetRadius
      rw [mul_one_div, div_lt_iff₀ (by positivity)]
      nlinarith
    nlinarith [hev i]

theorem hasDerivAt_logDetSeries {s : ℝ} (hs : -logDetRadius ev < s) :
    HasDerivAt (logDetSeries ev) (logDetSeries₁ ev s) s := by
  show HasDerivAt (fun s => ∑' i, Real.log (1 + ev i * s)) (∑' i, ev i / (1 + ev i * s)) s
  have hU : IsOpen (Ioi (-logDetRadius ev)) := isOpen_Ioi
  refine hasDerivAt_tsum_of_isPreconnected (u := fun i => 2 * ev i)
    (g := fun i s => Real.log (1 + ev i * s)) (g' := fun i s => ev i / (1 + ev i * s)) (hsum.mul_left 2) hU
    isPreconnected_Ioi (fun i y hy => ?_) (fun i y hy => ?_)
    (show (0 : ℝ) ∈ Ioi (-logDetRadius ev) from neg_lt_zero.2 (logDetRadius_pos hev)) ?_ hs
  · have hpos := half_lt_one_add hev hsum hy i
    have h := (((hasDerivAt_id y).const_mul (ev i)).const_add 1).log
      (ne_of_gt (by simp only [id_eq]; linarith))
    exact h.congr_deriv (by simp only [id_eq, mul_one])
  · have hpos := half_lt_one_add hev hsum hy i
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hev i) (by linarith)), div_le_iff₀ (by linarith)]
    nlinarith [hev i]
  · simp

theorem hasDerivAt_logDetSeries₁ {s : ℝ} (hs : -logDetRadius ev < s) :
    HasDerivAt (logDetSeries₁ ev) (logDetSeries₂ ev s) s := by
  show HasDerivAt (fun s => ∑' i, ev i / (1 + ev i * s)) (∑' i, -(ev i ^ 2 / (1 + ev i * s) ^ 2)) s
  have hU : IsOpen (Ioi (-logDetRadius ev)) := isOpen_Ioi
  have hle : ∀ i, ev i ≤ ∑' j, ev j := fun i => hsum.le_tsum i fun j _ => hev j
  refine hasDerivAt_tsum_of_isPreconnected (u := fun i => 4 * (∑' j, ev j) * ev i)
    (g := fun i s => ev i / (1 + ev i * s)) (g' := fun i s => -(ev i ^ 2 / (1 + ev i * s) ^ 2))
    (hsum.mul_left _) hU isPreconnected_Ioi (fun i y hy => ?_) (fun i y hy => ?_)
    (show (0 : ℝ) ∈ Ioi (-logDetRadius ev) from neg_lt_zero.2 (logDetRadius_pos hev)) ?_ hs
  · have hpos := half_lt_one_add hev hsum hy i
    have h := (hasDerivAt_const y (ev i)).div (((hasDerivAt_id y).const_mul (ev i)).const_add 1)
      (ne_of_gt (by simp only [id_eq]; linarith))
    exact h.congr_deriv (by simp only [id_eq]; ring)
  · have hpos := half_lt_one_add hev hsum hy i
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    have h1 : ev i ^ 2 ≤ (∑' j, ev j) * ev i := by nlinarith [hev i, hle i]
    have hsq : (1 : ℝ) / 4 ≤ (1 + ev i * y) ^ 2 := by nlinarith
    have hT : 0 ≤ ∑' j, ev j := tsum_nonneg hev
    have h4 : 0 ≤ 4 * (∑' j, ev j) * ev i := by have := hev i; positivity
    calc ev i ^ 2 ≤ (∑' j, ev j) * ev i := h1
      _ = 4 * (∑' j, ev j) * ev i * (1 / 4) := by ring
      _ ≤ 4 * (∑' j, ev j) * ev i * (1 + ev i * y) ^ 2 := mul_le_mul_of_nonneg_left hsq h4
  · simpa using hsum

theorem continuousOn_logDetSeries₂ : ContinuousOn (logDetSeries₂ ev) (Ici 0) := by
  have hle : ∀ i, ev i ≤ ∑' j, ev j := fun i => hsum.le_tsum i fun j _ => hev j
  have hT : 0 ≤ ∑' i, ev i := tsum_nonneg hev
  refine continuousOn_tsum (u := fun i => (∑' j, ev j) * ev i)
    (f := fun i s => -(ev i ^ 2 / (1 + ev i * s) ^ 2)) (fun i => ?_) (hsum.mul_left _)
    fun i y hy => ?_
  · refine ContinuousOn.neg (ContinuousOn.div continuousOn_const (by fun_prop) fun y hy => ?_)
    have : 0 ≤ ev i * y := mul_nonneg (hev i) hy
    positivity
  · have hy' : 0 ≤ ev i * y := mul_nonneg (hev i) hy
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    have h1 : ev i ^ 2 ≤ (∑' j, ev j) * ev i := by nlinarith [hev i, hle i]
    nlinarith [hev i, sq_nonneg (ev i * y), mul_nonneg hT (hev i)]

/-- **(BGCA.4)–(BGCA.6)** The determinant-line area of the cap with spectrum `λ` over the unit disk
is `∑ λ_j / (1 + λ_j)`. -/
theorem capArea_eq_tsum : radialCapArea (logDetSeries ev) = ∑' i, ev i / (1 + ev i) := by
  have hδ := logDetRadius_pos hev
  rw [radialCapArea_eq (ψ₁ := logDetSeries₁ ev) (ψ₂ := logDetSeries₂ ev)
    (fun s hs => hasDerivAt_logDetSeries hev hsum (by linarith))
    (fun s hs => hasDerivAt_logDetSeries₁ hev hsum (by linarith))
    (continuousOn_logDetSeries₂ hev hsum)]
  simp [logDetSeries₁]

/-- The area lies in `[0, ∑ λ_j]`. -/
theorem capArea_le_tsum : 0 ≤ ∑' i, ev i / (1 + ev i) ∧ ∑' i, ev i / (1 + ev i) ≤ ∑' i, ev i := by
  have hs : Summable fun i => ev i / (1 + ev i) :=
    hsum.of_nonneg_of_le (fun i => div_nonneg (hev i) (by linarith [hev i]))
      fun i => div_le_self (hev i) (by linarith [hev i])
  exact ⟨tsum_nonneg fun i => div_nonneg (hev i) (by linarith [hev i]),
    hs.tsum_le_tsum (fun i => div_le_self (hev i) (by linarith [hev i])) hsum⟩

/-- A positive eigenvalue makes the inequality strict. -/
theorem capArea_lt_tsum {i₀ : ι} (hi₀ : 0 < ev i₀) : ∑' i, ev i / (1 + ev i) < ∑' i, ev i := by
  have hs : Summable fun i => ev i / (1 + ev i) :=
    hsum.of_nonneg_of_le (fun i => div_nonneg (hev i) (by linarith [hev i]))
      fun i => div_le_self (hev i) (by linarith [hev i])
  refine hs.tsum_lt_tsum (i := i₀) (fun i => div_le_self (hev i) (by linarith [hev i])) ?_ hsum
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

end LogDet

/-! ## Normalization: the rank-one Schubert sphere has area one -/

/-- **Normalization of `ω_det`.**  For every `λ > 0` the full rank-one cap over `ℂ` — the graph
chart of the Schubert sphere — has determinant-line area `∫_ℂ (1/4π) Δ log(1 + λ|z|²) = 1`. -/
theorem schubertArea_eq_one {e : ℝ} (he : 0 < e) :
    ∫ z : ℂ, (1 / (4 * π)) * Δ (fun w : ℂ => Real.log (1 + e * ‖w‖ ^ 2)) z = 1 := by
  have h₁ : ∀ s, 0 ≤ s → HasDerivAt (fun s => Real.log (1 + e * s)) (e / (1 + e * s)) s := by
    intro s hs
    have h := (((hasDerivAt_id s).const_mul e).const_add 1).log
      (ne_of_gt (by simp only [id_eq]; positivity))
    exact h.congr_deriv (by simp only [id_eq, mul_one])
  have h₂ : ∀ s, 0 ≤ s → HasDerivAt (fun s => e / (1 + e * s)) (-(e ^ 2 / (1 + e * s) ^ 2)) s := by
    intro s hs
    have h := (hasDerivAt_const s e).div (((hasDerivAt_id s).const_mul e).const_add 1)
      (ne_of_gt (by simp only [id_eq]; positivity))
    exact h.congr_deriv (by simp only [id_eq]; ring)
  set G : ℝ → ℝ := fun r => (1 / π) * (e / (1 + e * r ^ 2) ^ 2) with hG
  have hint : ∀ z : ℂ, (1 / (4 * π)) * Δ (fun w : ℂ => Real.log (1 + e * ‖w‖ ^ 2)) z = G ‖z‖ := by
    intro z
    rw [laplacian_radial (ψ := fun s => Real.log (1 + e * s)) h₁ h₂ z, hG]
    have : 0 < 1 + e * ‖z‖ ^ 2 := by positivity
    field_simp
    ring
  rw [integral_congr_ae (Eventually.of_forall hint), integral_fun_norm_addHaar (volume : Measure ℂ) G,
    Complex.finrank_real_complex, volume_real_ball_one_complex]
  set F : ℝ → ℝ := fun r => e * r ^ 2 / (1 + e * r ^ 2) with hF
  have hFd : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt F (2 * π * (r ^ (2 - 1) • G r)) r := by
    intro r _
    have h := ((hasDerivAt_pow 2 r).const_mul e).div (((hasDerivAt_pow 2 r).const_mul e).const_add 1)
      (ne_of_gt (by positivity))
    have h' : HasDerivAt F ((e * ((2 : ℕ) * r ^ (2 - 1)) * (1 + e * r ^ 2) -
        e * r ^ 2 * (e * ((2 : ℕ) * r ^ (2 - 1)))) / (1 + e * r ^ 2) ^ 2) r := h
    refine h'.congr_deriv ?_
    rw [hG]
    have : 0 < 1 + e * r ^ 2 := by positivity
    have := Real.pi_pos
    simp only [smul_eq_mul]
    norm_num
    field_simp
    ring
  have hlim : Tendsto F atTop (𝓝 1) := by
    have h : F = fun r => 1 - 1 / (1 + e * r ^ 2) := by
      funext r
      rw [hF]
      have : 0 < 1 + e * r ^ 2 := by positivity
      field_simp
      ring
    rw [h]
    have h2 : Tendsto (fun r : ℝ => 1 + e * r ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left _ _ ((tendsto_pow_atTop two_ne_zero).const_mul_atTop he)
    simpa using tendsto_const_nhds.sub (h2.inv_tendsto_atTop.congr fun r => by simp)
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    refine (Continuous.continuousAt ?_).continuousWithinAt
    rw [hF]
    exact Continuous.div (by fun_prop) (by fun_prop) fun r => by positivity
  have hnn : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ 2 * π * (r ^ (2 - 1) • G r) := by
    intro r hr
    rw [hG, smul_eq_mul]
    have : 0 < (1 + e * r ^ 2) ^ 2 := by positivity
    have := Real.pi_pos
    have hr' : 0 < r := hr
    positivity
  have hI := integrableOn_Ioi_deriv_of_nonneg hcont hFd hnn hlim
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto hcont hFd hI hlim
  rw [integral_const_mul] at hval
  rw [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat, ← mul_assoc, hval]
  simp [hF]

end GaloisForLFunctions.HTGeometry
