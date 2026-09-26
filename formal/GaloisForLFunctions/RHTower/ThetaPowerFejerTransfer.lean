import GaloisForLFunctions.RHTower.ThetaPowerErrorCesaroMeanSquare
import GaloisForLFunctions.RHTower.ThetaPowerCoefficientSummability
import GaloisForLFunctions.HTGeometry.FejerWeightedQuadraticAverage
import GaloisForLFunctions.HTGeometry.CauchyCircleAverageBound
import GaloisForLFunctions.HTGeometry.WeightedDoubleIntegralBound

/-!
# Transfer of a target to a vertical translate of the theta-power Dirichlet function

Let `f` be holomorphic on the disc `|z - σ₀| < R` inside `1/4 < Re z ≤ 1` and a uniform limit there of phased
partial sums `Σ_{n<N} u_n β_n(z)`, `β_n(z) = b_n (n+α)^{-z}`, `|u_n| = 1`.  If the frequencies
`ω_n = -log(n+α)` are independent over `ℤ`, then for every `ε > 0` some translate satisfies
`|D(z + it) - f(z)| ≤ ε` on the disc `|z - σ₀| ≤ r`.

For each `t`, the Cauchy circle-average bound on the circle of radius `R' = (r+R)/2` and the splitting

  `D(ζ+it) - f(ζ) = [Σ_{n<N} u_n β_n - f] + Σ_{n<N} β_n (e^{iω_n t} - u_n) + Σ_{n<N} β_n (e^{-λ_n δ} - 1) e^{iω_n t}`
  `              + Σ_{N≤n<M} β_n e^{-λ_n δ} e^{iω_n t} + Σ_{n≥M} β_n(ζ+it) e^{-λ_n δ} + E^δ(ζ+it)`

with `|X| ≤ κ/2 + |X|²/(2κ)` give a majorant `Φ(t)`.  If `Φ(t) > ε` for all `t`, integrating against the Fejér
weight `ψ` concentrated at `ω_n t ≡ arg u_n` (`n < N`) contradicts the averages of the Fejér module (for the
first four groups) and the mean square of `E^δ` through `ψ ≤ L^N` and Tonelli (for the last).
-/

open Complex Real Filter Topology MeasureTheory Set Metric

namespace RHTower

noncomputable section

variable {a : ℝ}

/-- The frequencies `ω_n = -log(n + a/4)`. -/
def thetaPowerLogFreq (a : ℝ) (n : ℕ) : ℝ := -Real.log ((n : ℝ) + a / 4)

theorem le_half_add_sq_div {κ : ℝ} (hκ : 0 < κ) (x : ℝ) : x ≤ κ / 2 + x ^ 2 / (2 * κ) := by
  rw [show κ / 2 + x ^ 2 / (2 * κ) = (κ ^ 2 + x ^ 2) / (2 * κ) by field_simp,
    le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (x - κ)]

theorem continuousOn_thetaPowerDirichletError (ha0 : 0 < a) (ha4 : a ≤ 4) {δ : ℝ} (hδ : 0 < δ) :
    ContinuousOn (thetaPowerDirichletError a δ) {z : ℂ | 0 < z.re ∧ z.re < 2} := by
  refine ((differentiable_thetaPowerDirichlet ha0).continuous.continuousOn.sub
    (continuousOn_thetaPowerSmoothDirichlet ha0 ha4 hδ)).congr fun z hz => ?_
  rw [Pi.sub_apply, thetaPowerDirichlet_split ha0 hδ hz.1]
  ring

theorem re_mem_of_mem_closedBall {σ₀ R : ℝ} {z : ℂ} (hz : z ∈ closedBall (σ₀ : ℂ) R) :
    σ₀ - R ≤ z.re ∧ z.re ≤ σ₀ + R := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have h := (Complex.abs_re_le_norm (z - σ₀)).trans hz
  simp only [Complex.sub_re, Complex.ofReal_re] at h
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

theorem abs_im_le_of_mem_closedBall {σ₀ R : ℝ} {z : ℂ} (hz : z ∈ closedBall (σ₀ : ℂ) R) :
    |z.im| ≤ R := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have h := (Complex.abs_im_le_norm (z - σ₀)).trans hz
  simpa using h

/-- `|β_n(z)| ≤ |b_n| α^{-2}` on `0 ≤ Re z ≤ 2`. -/
theorem norm_shiftedTerm_le_const (ha0 : 0 < a) (ha4 : a ≤ 4) (n : ℕ) {z : ℂ} (hz0 : 0 ≤ z.re)
    (hz2 : z.re ≤ 2) :
    ‖shiftedTerm (a / 4) (thetaPowerCoeff a) n z‖ ≤ ‖thetaPowerCoeff a n‖ * (a / 4) ^ (-2 : ℝ) := by
  unfold shiftedTerm
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_shift_cpow_le (by positivity) (by linarith) n hz0 hz2)
    (norm_nonneg _)

/-- **Pointwise majorant** on the disc of radius `R`. -/
theorem norm_dirichlet_shift_sub_le_pointwise (ha0 : 0 < a) (ha1 : a < 1 / 2) {δ : ℝ} (hδ : 0 < δ)
    {σ₀ R : ℝ} (hlo : 1 / 4 < σ₀ - R) (hhi : σ₀ + R ≤ 1) {f : ℂ → ℂ} {u : ℕ → ℂ} {θ' : ℕ → ℝ}
    (hθ : ∀ n, u n = Complex.exp ((θ' n : ℂ) * I)) {N M : ℕ} (hNM : N ≤ M) {εF : ℝ}
    (hF : ∀ z ∈ closedBall (σ₀ : ℂ) R,
      ‖f z - ∑ n ∈ Finset.range N, u n * shiftedTerm (a / 4) (thetaPowerCoeff a) n z‖ ≤ εF)
    {κ κA : ℝ} (hκ : 0 < κ) (hκA : 0 < κA) (t : ℝ) {ζ : ℂ} (hζ : ζ ∈ closedBall (σ₀ : ℂ) R) :
    ‖thetaPowerDirichlet a (ζ + t * I) - f ζ‖ ≤
      (εF + ∑ n ∈ Finset.range N, ‖thetaPowerCoeff a n‖ * (a / 4) ^ (-2 : ℝ) *
            (κA / 2 + ‖Complex.exp (((thetaPowerLogFreq a n * t : ℝ) : ℂ) * I) -
              Complex.exp ((θ' n : ℂ) * I)‖ ^ 2 / (2 * κA)) +
          ∑ n ∈ Finset.range N, ‖thetaPowerCoeff a n‖ * (a / 4) ^ (-2 : ℝ) *
            (1 - thetaPowerSmoothWeight a δ n) +
          (∑' k, ‖thetaPowerCoeff a (k + M)‖ * thetaPowerSmoothWeight a δ (k + M)) *
            (a / 4) ^ (-2 : ℝ) + κ) +
        ‖∑ n ∈ Finset.Ico N M, shiftedTerm (a / 4) (thetaPowerCoeff a) n ζ *
            (thetaPowerSmoothWeight a δ n : ℂ) *
            Complex.exp (((thetaPowerLogFreq a n * t : ℝ) : ℂ) * I)‖ ^ 2 / (2 * κ) +
        ‖thetaPowerDirichletError a δ (ζ + t * I)‖ ^ 2 / (2 * κ) := by
  obtain ⟨hre1, hre2⟩ := re_mem_of_mem_closedBall hζ
  have ha4 : a ≤ 4 := by linarith
  have hre : (ζ + t * I).re = ζ.re := by simp
  have hζ0 : 0 < ζ.re := by linarith
  have hζ2 : ζ.re < 2 := by linarith
  have hdec : thetaPowerDirichlet a (ζ + t * I) =
      ∑ n ∈ Finset.range M, shiftedTerm (a / 4) (thetaPowerCoeff a) n ζ *
          (thetaPowerSmoothWeight a δ n : ℂ) *
          Complex.exp (((thetaPowerLogFreq a n * t : ℝ) : ℂ) * I) +
        ∑' k, shiftedTerm (a / 4) (thetaPowerCoeff a) (k + M) (ζ + t * I) *
          (thetaPowerSmoothWeight a δ (k + M) : ℂ) +
        thetaPowerDirichletError a δ (ζ + t * I) :=
    thetaPowerDirichlet_shift_decomp ha0 ha4 hδ hζ0 hζ2 t M
  rw [← Finset.sum_range_add_sum_Ico _ hNM] at hdec
  have hsumN : ∑ n ∈ Finset.range N, shiftedTerm (a / 4) (thetaPowerCoeff a) n ζ *
        (thetaPowerSmoothWeight a δ n : ℂ) * Complex.exp (((thetaPowerLogFreq a n * t : ℝ) : ℂ) * I) =
      ∑ n ∈ Finset.range N, u n * shiftedTerm (a / 4) (thetaPowerCoeff a) n ζ +
        ∑ n ∈ Finset.range N, shiftedTerm (a / 4) (thetaPowerCoeff a) n ζ *
          (Complex.exp (((thetaPowerLogFreq a n * t : ℝ) : ℂ) * I) - u n) +
        ∑ n ∈ Finset.range N, shiftedTerm (a / 4) (thetaPowerCoeff a) n ζ *
          ((thetaPowerSmoothWeight a δ n : ℂ) - 1) *
          Complex.exp (((thetaPowerLogFreq a n * t : ℝ) : ℂ) * I) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hsumN] at hdec
  set Fv := ∑ n ∈ Finset.range N, u n * shiftedTerm (a / 4) (thetaPowerCoeff a) n ζ - f ζ with hFv
  set Av := ∑ n ∈ Finset.range N, shiftedTerm (a / 4) (thetaPowerCoeff a) n ζ *
    (Complex.exp (((thetaPowerLogFreq a n * t : ℝ) : ℂ) * I) - u n) with hAv
  set Wv := ∑ n ∈ Finset.range N, shiftedTerm (a / 4) (thetaPowerCoeff a) n ζ *
    ((thetaPowerSmoothWeight a δ n : ℂ) - 1) *
    Complex.exp (((thetaPowerLogFreq a n * t : ℝ) : ℂ) * I) with hWv
  set Yv := ∑ n ∈ Finset.Ico N M, shiftedTerm (a / 4) (thetaPowerCoeff a) n ζ *
    (thetaPowerSmoothWeight a δ n : ℂ) * Complex.exp (((thetaPowerLogFreq a n * t : ℝ) : ℂ) * I) with hYv
  set Tv := ∑' k, shiftedTerm (a / 4) (thetaPowerCoeff a) (k + M) (ζ + t * I) *
    (thetaPowerSmoothWeight a δ (k + M) : ℂ) with hTv
  set Ev := thetaPowerDirichletError a δ (ζ + t * I) with hEv
  have hid : thetaPowerDirichlet a (ζ + t * I) - f ζ = Fv + Av + Wv + Yv + Tv + Ev := by
    rw [hdec, hFv]; ring
  have hβ : ∀ n, ‖shiftedTerm (a / 4) (thetaPowerCoeff a) n ζ‖ ≤
      ‖thetaPowerCoeff a n‖ * (a / 4) ^ (-2 : ℝ) :=
    fun n => norm_shiftedTerm_le_const ha0 ha4 n hζ0.le hζ2.le
  have he1 : ∀ n, ‖Complex.exp (((thetaPowerLogFreq a n * t : ℝ) : ℂ) * I)‖ = 1 :=
    fun n => Complex.norm_exp_ofReal_mul_I _
  have hF' : ‖Fv‖ ≤ εF := by rw [hFv, norm_sub_rev]; exact hF ζ hζ
  have hA' : ‖Av‖ ≤ ∑ n ∈ Finset.range N, ‖thetaPowerCoeff a n‖ * (a / 4) ^ (-2 : ℝ) *
      (κA / 2 + ‖Complex.exp (((thetaPowerLogFreq a n * t : ℝ) : ℂ) * I) -
        Complex.exp ((θ' n : ℂ) * I)‖ ^ 2 / (2 * κA)) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [norm_mul, hθ n]
    exact mul_le_mul (hβ n) (le_half_add_sq_div hκA _) (norm_nonneg _) (by positivity)
  have hW' : ‖Wv‖ ≤ ∑ n ∈ Finset.range N, ‖thetaPowerCoeff a n‖ * (a / 4) ^ (-2 : ℝ) *
      (1 - thetaPowerSmoothWeight a δ n) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    have hw1 := thetaPowerSmoothWeight_le_one ha0 hδ.le n
    have hwn : ‖(thetaPowerSmoothWeight a δ n : ℂ) - 1‖ = 1 - thetaPowerSmoothWeight a δ n := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith)]
      ring
    rw [norm_mul, norm_mul, he1, mul_one, hwn]
    exact mul_le_mul_of_nonneg_right (hβ n) (by linarith)
  have hT' : ‖Tv‖ ≤ (∑' k, ‖thetaPowerCoeff a (k + M)‖ * thetaPowerSmoothWeight a δ (k + M)) *
      (a / 4) ^ (-2 : ℝ) :=
    norm_smoothTail_le ha0 ha4 hδ M (by rw [hre]; exact hζ0.le) (by rw [hre]; exact hζ2.le)
  have hY' := le_half_add_sq_div hκ ‖Yv‖
  have hE' := le_half_add_sq_div hκ ‖Ev‖
  have h6 : ‖Fv + Av + Wv + Yv + Tv + Ev‖ ≤ ‖Fv‖ + ‖Av‖ + ‖Wv‖ + ‖Yv‖ + ‖Tv‖ + ‖Ev‖ := by
    have := norm_add_le (Fv + Av + Wv + Yv + Tv) Ev
    have := norm_add_le (Fv + Av + Wv + Yv) Tv
    have := norm_add_le (Fv + Av + Wv) Yv
    have := norm_add_le (Fv + Av) Wv
    have := norm_add_le Fv Av
    linarith
  rw [hid]
  linarith

/-- **Circle majorant.** For `|z - σ₀| ≤ r`, `|D(z+it) - f(z)|` is at most the circle average (radius
`R' = (r+R)/2`) of the pointwise majorant. -/
theorem norm_dirichlet_shift_sub_le_majorant (ha0 : 0 < a) (ha1 : a < 1 / 2) {δ : ℝ} (hδ : 0 < δ)
    {σ₀ R r : ℝ} (hr : 0 < r) (hrR : r < R) (hlo : 1 / 4 < σ₀ - R) (hhi : σ₀ + R ≤ 1) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball (σ₀ : ℂ) R)) {u : ℕ → ℂ} {θ' : ℕ → ℝ}
    (hθ : ∀ n, u n = Complex.exp ((θ' n : ℂ) * I)) {N M : ℕ} (hNM : N ≤ M) {εF : ℝ}
    (hF : ∀ z ∈ closedBall (σ₀ : ℂ) R,
      ‖f z - ∑ n ∈ Finset.range N, u n * shiftedTerm (a / 4) (thetaPowerCoeff a) n z‖ ≤ εF)
    {κ κA : ℝ} (hκ : 0 < κ) (hκA : 0 < κA) (t : ℝ) {z : ℂ} (hz : z ∈ closedBall (σ₀ : ℂ) r) :
    ‖thetaPowerDirichlet a (z + t * I) - f z‖ ≤
      (r + R) / 2 / ((r + R) / 2 - r) / (2 * π) *
        (2 * π * (εF + ∑ n ∈ Finset.range N, ‖thetaPowerCoeff a n‖ * (a / 4) ^ (-2 : ℝ) *
              (κA / 2 + ‖Complex.exp (((thetaPowerLogFreq a n * t : ℝ) : ℂ) * I) -
                Complex.exp ((θ' n : ℂ) * I)‖ ^ 2 / (2 * κA)) +
            ∑ n ∈ Finset.range N, ‖thetaPowerCoeff a n‖ * (a / 4) ^ (-2 : ℝ) *
              (1 - thetaPowerSmoothWeight a δ n) +
            (∑' k, ‖thetaPowerCoeff a (k + M)‖ * thetaPowerSmoothWeight a δ (k + M)) *
              (a / 4) ^ (-2 : ℝ) + κ) +
          (∫ θ in (0 : ℝ)..2 * π, ‖∑ n ∈ Finset.Ico N M,
              (shiftedTerm (a / 4) (thetaPowerCoeff a) n (circleMap (σ₀ : ℂ) ((r + R) / 2) θ) *
                (thetaPowerSmoothWeight a δ n : ℂ)) *
              Complex.exp (((thetaPowerLogFreq a n * t : ℝ) : ℂ) * I)‖ ^ 2) / (2 * κ) +
          (∫ θ in (0 : ℝ)..2 * π, ‖thetaPowerDirichletError a δ
              (circleMap (σ₀ : ℂ) ((r + R) / 2) θ + t * I)‖ ^ 2) / (2 * κ)) := by
  set R' : ℝ := (r + R) / 2 with hR'
  have hrR' : r < R' := by rw [hR']; linarith
  have hR'R : R' < R := by rw [hR']; linarith
  have hR'0 : 0 ≤ R' := by linarith
  have ha4 : a ≤ 4 := by linarith
  set c : ℝ := εF + ∑ n ∈ Finset.range N, ‖thetaPowerCoeff a n‖ * (a / 4) ^ (-2 : ℝ) *
        (κA / 2 + ‖Complex.exp (((thetaPowerLogFreq a n * t : ℝ) : ℂ) * I) -
          Complex.exp ((θ' n : ℂ) * I)‖ ^ 2 / (2 * κA)) +
      ∑ n ∈ Finset.range N, ‖thetaPowerCoeff a n‖ * (a / 4) ^ (-2 : ℝ) *
        (1 - thetaPowerSmoothWeight a δ n) +
      (∑' k, ‖thetaPowerCoeff a (k + M)‖ * thetaPowerSmoothWeight a δ (k + M)) *
        (a / 4) ^ (-2 : ℝ) + κ with hc
  set h : ℂ → ℂ := fun w => thetaPowerDirichlet a (w + t * I) - f w with hh
  have hdiffD : Differentiable ℂ fun w : ℂ => thetaPowerDirichlet a (w + t * I) :=
    (differentiable_thetaPowerDirichlet ha0).comp (differentiable_id.add_const _)
  have hdiff : DifferentiableOn ℂ h (ball (σ₀ : ℂ) R) := hdiffD.differentiableOn.sub hf
  have hcl : DiffContOnCl ℂ h (ball (σ₀ : ℂ) R') :=
    hdiff.diffContOnCl_ball (closedBall_subset_ball hR'R)
  have hdist : dist z (σ₀ : ℂ) ≤ r := mem_closedBall.mp hz
  have hcirc := GaloisForLFunctions.HTGeometry.norm_le_circle_average hr.le hrR' hcl hdist
  have hmem : ∀ θ, circleMap (σ₀ : ℂ) R' θ ∈ closedBall (σ₀ : ℂ) R := fun θ =>
    closedBall_subset_closedBall hR'R.le (circleMap_mem_closedBall _ hR'0 θ)
  have hmemb : ∀ θ, circleMap (σ₀ : ℂ) R' θ ∈ ball (σ₀ : ℂ) R := fun θ =>
    closedBall_subset_ball hR'R (circleMap_mem_closedBall _ hR'0 θ)
  have hhc : Continuous fun θ => ‖h (circleMap (σ₀ : ℂ) R' θ)‖ :=
    (hdiff.continuousOn.comp_continuous (continuous_circleMap _ _) hmemb).norm
  have hYc : Continuous fun θ => ‖∑ n ∈ Finset.Ico N M,
      (shiftedTerm (a / 4) (thetaPowerCoeff a) n (circleMap (σ₀ : ℂ) R' θ) *
        (thetaPowerSmoothWeight a δ n : ℂ)) *
      Complex.exp (((thetaPowerLogFreq a n * t : ℝ) : ℂ) * I)‖ ^ 2 := by
    refine (continuous_finsetSum _ fun n _ => ?_).norm.pow 2
    exact (((differentiable_shiftedTerm (by positivity) _ n).continuous.comp
      (continuous_circleMap _ _)).mul continuous_const).mul continuous_const
  have hstrip : ∀ θ, circleMap (σ₀ : ℂ) R' θ + t * I ∈ {w : ℂ | 0 < w.re ∧ w.re < 2} := by
    intro θ
    obtain ⟨h1, h2⟩ := re_mem_of_mem_closedBall (hmem θ)
    simp only [mem_setOf_eq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    constructor <;> linarith
  have hEc : Continuous fun θ => ‖thetaPowerDirichletError a δ (circleMap (σ₀ : ℂ) R' θ + t * I)‖ ^ 2 :=
    ((continuousOn_thetaPowerDirichletError ha0 ha4 hδ).comp_continuous
      ((continuous_circleMap _ _).add continuous_const) hstrip).norm.pow 2
  have hpt : ∀ θ, ‖h (circleMap (σ₀ : ℂ) R' θ)‖ ≤ c +
      ‖∑ n ∈ Finset.Ico N M,
        (shiftedTerm (a / 4) (thetaPowerCoeff a) n (circleMap (σ₀ : ℂ) R' θ) *
          (thetaPowerSmoothWeight a δ n : ℂ)) *
        Complex.exp (((thetaPowerLogFreq a n * t : ℝ) : ℂ) * I)‖ ^ 2 / (2 * κ) +
      ‖thetaPowerDirichletError a δ (circleMap (σ₀ : ℂ) R' θ + t * I)‖ ^ 2 / (2 * κ) := by
    intro θ
    exact norm_dirichlet_shift_sub_le_pointwise ha0 ha1 hδ hlo hhi hθ hNM hF hκ hκA t (hmem θ)
  have hint : ∫ θ in (0 : ℝ)..2 * π, ‖h (circleMap (σ₀ : ℂ) R' θ)‖ ≤
      2 * π * c + (∫ θ in (0 : ℝ)..2 * π, ‖∑ n ∈ Finset.Ico N M,
          (shiftedTerm (a / 4) (thetaPowerCoeff a) n (circleMap (σ₀ : ℂ) R' θ) *
            (thetaPowerSmoothWeight a δ n : ℂ)) *
          Complex.exp (((thetaPowerLogFreq a n * t : ℝ) : ℂ) * I)‖ ^ 2) / (2 * κ) +
        (∫ θ in (0 : ℝ)..2 * π,
          ‖thetaPowerDirichletError a δ (circleMap (σ₀ : ℂ) R' θ + t * I)‖ ^ 2) / (2 * κ) := by
    have i1 : IntervalIntegrable (fun _ : ℝ => c) volume 0 (2 * π) := intervalIntegrable_const
    have i2 : IntervalIntegrable (fun θ => ‖∑ n ∈ Finset.Ico N M,
        (shiftedTerm (a / 4) (thetaPowerCoeff a) n (circleMap (σ₀ : ℂ) R' θ) *
          (thetaPowerSmoothWeight a δ n : ℂ)) *
        Complex.exp (((thetaPowerLogFreq a n * t : ℝ) : ℂ) * I)‖ ^ 2 / (2 * κ)) volume 0 (2 * π) :=
      (hYc.div_const _).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun θ =>
        ‖thetaPowerDirichletError a δ (circleMap (σ₀ : ℂ) R' θ + t * I)‖ ^ 2 / (2 * κ))
        volume 0 (2 * π) :=
      (hEc.div_const _).intervalIntegrable _ _
    refine (intervalIntegral.integral_mono_on (by positivity) (hhc.intervalIntegrable _ _)
      ((i1.add i2).add i3) fun θ _ => hpt θ).trans (le_of_eq ?_)
    rw [intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
      intervalIntegral.integral_const, intervalIntegral.integral_div, intervalIntegral.integral_div,
      smul_eq_mul, sub_zero]
  have hC0 : 0 ≤ R' / (R' - r) / (2 * π) := by
    have : 0 < R' - r := by linarith
    positivity
  calc ‖thetaPowerDirichlet a (z + t * I) - f z‖ = ‖h z‖ := rfl
    _ ≤ R' / (R' - r) / (2 * π) * ∫ θ in (0 : ℝ)..2 * π, ‖h (circleMap (σ₀ : ℂ) R' θ)‖ := hcirc
    _ ≤ _ := mul_le_mul_of_nonneg_left hint hC0

/-- **Averaging against a majorant.** Suppose `ε < Φ(t)` for every `t ≥ T₀`, where
`Φ = Cc (2π(εF + Σ p_n (κA/2 + x_n/(2κA)) + W + Tl + κ) + Q_Y/(2κ) + Q_E/(2κ))`, and let
`H = c₀ ψ - Σ d_n ψ x_n - d_Y ψ Q_Y` with the matching coefficients.  If `H` has mean `ℓ`, `0 ≤ ψ ≤ Λ` and
`∫_{[0,T]} q(t, θ) dt ≤ C₀ + C₁ T` with `Q_E = ∫₀^{2π} q`, then `ℓ ≤ Λ (Cc/(2κ)) 2π C₁`.  The finitely many
times `t < T₀` contribute a bounded amount to `∫₀ᵀ H`. -/
theorem average_majorant_le {ψ QY QE : ℝ → ℝ} {x : ℕ → ℝ → ℝ} {q : ℝ → ℝ → ℝ} {s : Finset ℕ}
    {c₀ dY ε εF W Tl κ κA Cc Λ C₀ C₁ ℓ T₀ : ℝ} {d p : ℕ → ℝ}
    (hlim : Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T,
      (c₀ * ψ t - ∑ n ∈ s, d n * (ψ t * x n t) - dY * (ψ t * QY t))) atTop (𝓝 ℓ))
    (hψc : Continuous ψ) (hψ0 : ∀ t, 0 ≤ ψ t) (hψΛ : ∀ t, ψ t ≤ Λ)
    (hxc : ∀ n, Continuous (x n)) (hQYc : Continuous QY)
    (hq : Continuous (Function.uncurry q)) (hq0 : ∀ t θ, 0 ≤ q t θ)
    (hQE : ∀ t, QE t = ∫ θ in (0 : ℝ)..2 * π, q t θ)
    (hκ : 0 < κ) (hCc : 0 ≤ Cc) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hbound : ∀ T : ℝ, 1 ≤ T → ∀ θ,
      ∫⁻ t in Icc 0 T, ENNReal.ofReal (q t θ) ≤ ENNReal.ofReal (C₀ + C₁ * T))
    (hc₀ : c₀ = ε - Cc * (2 * π) * (εF + (∑ n ∈ s, p n) * (κA / 2) + W + Tl + κ))
    (hd : ∀ n, d n = Cc * (2 * π) * (p n / (2 * κA))) (hdY : dY = Cc / (2 * κ))
    (hΦ : ∀ t, T₀ ≤ t → ε < Cc * (2 * π * (εF + ∑ n ∈ s, p n * (κA / 2 + x n t / (2 * κA)) + W + Tl +
      κ) + QY t / (2 * κ) + QE t / (2 * κ))) :
    ℓ ≤ Λ * (Cc / (2 * κ)) * (2 * π * C₁) := by
  have hK : 0 ≤ Cc / (2 * κ) := by positivity
  set H : ℝ → ℝ := fun t => c₀ * ψ t - ∑ n ∈ s, d n * (ψ t * x n t) - dY * (ψ t * QY t) with hH
  set G : ℝ → ℝ := fun t => ψ t * (Cc / (2 * κ) * ∫ θ in (0 : ℝ)..2 * π, q t θ) with hG
  have hHle : ∀ t, T₀ ≤ t → H t ≤ G t := by
    intro t ht
    have e1 : ∑ n ∈ s, p n * (κA / 2 + x n t / (2 * κA)) =
        (∑ n ∈ s, p n) * (κA / 2) + ∑ n ∈ s, p n / (2 * κA) * x n t := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    have e2 : ∑ n ∈ s, d n * (ψ t * x n t) = Cc * (2 * π) * ψ t * ∑ n ∈ s, p n / (2 * κA) * x n t := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by rw [hd]; ring
    have hΦt := hΦ t ht
    rw [e1] at hΦt
    have key : ψ t * (Cc / (2 * κ) * QE t) -
        (c₀ * ψ t - ∑ n ∈ s, d n * (ψ t * x n t) - dY * (ψ t * QY t)) =
        ψ t * (Cc * (2 * π * (εF + ((∑ n ∈ s, p n) * (κA / 2) + ∑ n ∈ s, p n / (2 * κA) * x n t) +
          W + Tl + κ) + QY t / (2 * κ) + QE t / (2 * κ)) - ε) := by
      rw [e2, hc₀, hdY]
      ring
    simp only [hH, hG]
    rw [← hQE t]
    linarith [mul_nonneg (hψ0 t) (sub_nonneg.2 hΦt.le)]
  have hHc : Continuous H :=
    ((continuous_const.mul hψc).sub (continuous_finsetSum _ fun n _ =>
      continuous_const.mul (hψc.mul (hxc n)))).sub (continuous_const.mul (hψc.mul hQYc))
  have hGc : Continuous G := hψc.mul (continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hq 0 (2 * π)))
  -- the excess before `T₀`
  set Rf : ℝ → ℝ := fun t => max (H t - G t) 0 with hRf
  have hRc : Continuous Rf := (hHc.sub hGc).max continuous_const
  have hR0 : ∀ t, T₀ ≤ t → Rf t = 0 := fun t ht => max_eq_right (by linarith [hHle t ht])
  set T₁ : ℝ := max T₀ 1 with hT₁
  set CR : ℝ := ∫ t in (0 : ℝ)..T₁, Rf t with hCR
  have hint : ∀ T : ℝ, T₁ ≤ T → ∫ t in (0 : ℝ)..T, H t ≤ CR + Λ * (Cc / (2 * κ)) * (2 * π * (C₀ + C₁ * T)) := by
    intro T hT
    have hT1 : 1 ≤ T := (le_max_right _ _).trans hT
    have h1 : ∫ t in (0 : ℝ)..T, (H t - Rf t) ≤ Λ * (Cc / (2 * κ)) * (2 * π * (C₀ + C₁ * T)) :=
      GaloisForLFunctions.HTGeometry.integral_le_of_weighted_double (hHc.sub hRc) hq hq0 hψ0 hψΛ hK
        (by linarith) (by positivity) (hbound T hT1) fun t => by
          have : H t - Rf t ≤ G t := by simp only [hRf]; rcases le_total (H t - G t) 0 with h | h
                                        · rw [max_eq_right h]; linarith
                                        · rw [max_eq_left h]; linarith
          simpa [hG] using this
    have h2 : ∫ t in (0 : ℝ)..T, Rf t = CR := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := T₁) (hRc.intervalIntegrable _ _)
        (hRc.intervalIntegrable _ _), hCR]
      have : ∫ t in T₁..T, Rf t = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_]
        · simp
        · rw [Set.uIcc_of_le hT] at ht
          exact hR0 t ((le_max_left _ _).trans ht.1)
      rw [this, add_zero]
    have i1 : IntervalIntegrable (fun t => H t - Rf t) volume 0 T := (hHc.sub hRc).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun t => Rf t) volume 0 T := hRc.intervalIntegrable _ _
    have hsplit : ∫ t in (0 : ℝ)..T, H t =
        (∫ t in (0 : ℝ)..T, (H t - Rf t)) + ∫ t in (0 : ℝ)..T, Rf t := by
      rw [← intervalIntegral.integral_add i1 i2]
      congr 1
      funext t
      ring
    rw [hsplit, h2]
    linarith
  have hR : Tendsto (fun T : ℝ => CR / T + Λ * (Cc / (2 * κ)) * (2 * π * (C₀ / T + C₁))) atTop
      (𝓝 (0 + Λ * (Cc / (2 * κ)) * (2 * π * (0 + C₁)))) :=
    (tendsto_const_nhds.div_atTop tendsto_id).add
      (((tendsto_const_nhds.div_atTop tendsto_id).add tendsto_const_nhds).const_mul _ |>.const_mul _)
  rw [zero_add, zero_add] at hR
  refine le_of_tendsto_of_tendsto hlim hR (eventually_atTop.2 ⟨T₁, fun T hT => ?_⟩)
  have hT0 : 0 < T := lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_right _ _)) hT
  have := mul_le_mul_of_nonneg_left (hint T hT) (inv_nonneg.2 hT0.le)
  refine this.trans (le_of_eq ?_)
  field_simp

/-- Tails of a series are eventually small. -/
theorem exists_tail_le (Q : ℕ → ℝ) {s : ℝ} (hs : 0 < s) : ∃ N₁ : ℕ, ∀ N ≥ N₁, ∑' k, Q (k + N) ≤ s := by
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 ((tendsto_order.1 (tendsto_sum_nat_add Q)).2 s hs)
  exact ⟨N₁, fun N hN => (hN₁ N hN).le⟩

/-- A Fejér order `L` with `X S / (κ_A L) ≤ ε/10`. -/
theorem exists_fejer_order (X SP : ℝ) {κA ε : ℝ} (hκA : 0 < κA) (hε : 0 < ε) :
    ∃ L : ℕ, 0 < L ∧ X * SP / (κA * L) ≤ ε / 10 := by
  obtain ⟨L, hL⟩ := exists_nat_gt (10 * X * SP / (κA * ε))
  refine ⟨L + 1, Nat.succ_pos _, ?_⟩
  rw [div_lt_iff₀ (by positivity)] at hL
  rw [div_le_iff₀ (by positivity)]
  push_cast
  nlinarith [mul_pos hκA hε]

/-- A smoothing parameter making the weight defect and the error constant small. -/
theorem exists_smoothing_parameter (a : ℝ) (N : ℕ) (X : ℝ) (c : ℕ → ℝ) (K : ℝ) {η ε : ℝ} (hη : 0 < η)
    (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ X * ∑ n ∈ Finset.range N, c n * (1 - thetaPowerSmoothWeight a δ n) ≤ ε / 10 ∧
      K * δ ^ (2 * η) ≤ ε / 10 := by
  have hW : Tendsto (fun δ => X * ∑ n ∈ Finset.range N, c n * (1 - thetaPowerSmoothWeight a δ n))
      (𝓝 0) (𝓝 0) := by
    have h := (tendsto_finsetSum (Finset.range N) fun n _ =>
      ((tendsto_thetaPowerSmoothWeight a n).const_sub 1).const_mul (c n)).const_mul X
    have h0 : X * ∑ n ∈ Finset.range N, c n * (1 - 1) = 0 := by simp
    rwa [h0] at h
  have hE : Tendsto (fun δ : ℝ => K * δ ^ (2 * η)) (𝓝 0) (𝓝 0) := by
    have := ((Real.continuous_rpow_const (by positivity : 0 ≤ 2 * η)).tendsto 0).const_mul K
    rwa [Real.zero_rpow (by positivity), mul_zero] at this
  have hev := (((hW.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < ε / 10))).and
    (hE.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < ε / 10)))).filter_mono
      nhdsWithin_le_nhds).and (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)
  obtain ⟨δ, ⟨h1, h2⟩, h3⟩ := hev.exists
  exact ⟨δ, h3, h1, h2⟩

/-- A truncation `M ≥ N` making the smoothed tail small. -/
theorem exists_truncation (a δ X P : ℝ) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, N ≤ M ∧
      X * ((∑' k, ‖thetaPowerCoeff a (k + M)‖ * thetaPowerSmoothWeight a δ (k + M)) * P) ≤ ε / 10 := by
  have ht := tendsto_sum_nat_add (fun n => ‖thetaPowerCoeff a n‖ * thetaPowerSmoothWeight a δ n)
  have ht2 : Tendsto (fun M => X * ((∑' k, ‖thetaPowerCoeff a (k + M)‖ *
      thetaPowerSmoothWeight a δ (k + M)) * P)) atTop (𝓝 0) := by
    have := (ht.mul_const P).const_mul X
    rwa [zero_mul, mul_zero] at this
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1
    (ht2.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < ε / 10)))
  exact ⟨max M₀ N, le_max_right _ _, hM₀ _ (le_max_left _ _)⟩

/-- Position of the circle `|ζ - σ₀| = R'` inside the strip. -/
theorem circleMap_re_im_bounds {σ₀ R R' : ℝ} (hlo : 1 / 4 < σ₀ - R) (hhi : σ₀ + R ≤ 1) (hR'0 : 0 ≤ R')
    (hR'R : R' ≤ R) (θ : ℝ) :
    σ₀ - R ≤ (circleMap (σ₀ : ℂ) R' θ).re ∧ (circleMap (σ₀ : ℂ) R' θ).re ≤ 1 ∧
      |(circleMap (σ₀ : ℂ) R' θ).im| ≤ 1 := by
  have hmem := closedBall_subset_closedBall hR'R (circleMap_mem_closedBall (σ₀ : ℂ) hR'0 θ)
  obtain ⟨h1, h2⟩ := re_mem_of_mem_closedBall hmem
  have h3 := abs_im_le_of_mem_closedBall hmem
  exact ⟨h1, by linarith, by linarith⟩

/-- `(t, θ) ↦ |E^δ(ζ_θ + it)|²` is continuous on circles inside the strip. -/
theorem continuous_error_on_circle (ha0 : 0 < a) (ha1 : a < 1 / 2) {δ : ℝ} (hδ : 0 < δ) {σ₀ R R' : ℝ}
    (hlo : 1 / 4 < σ₀ - R) (hhi : σ₀ + R ≤ 1) (hR'0 : 0 ≤ R') (hR'R : R' ≤ R) :
    Continuous (Function.uncurry fun t θ : ℝ =>
      ‖thetaPowerDirichletError a δ (circleMap (σ₀ : ℂ) R' θ + t * I)‖ ^ 2) := by
  refine ((continuousOn_thetaPowerDirichletError ha0 (by linarith) hδ).comp_continuous ?_ ?_).norm.pow 2
  · exact ((continuous_circleMap _ _).comp continuous_snd).add
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)
  · intro p
    obtain ⟨h1, h2, -⟩ := circleMap_re_im_bounds hlo hhi hR'0 hR'R p.2
    simp only [mem_setOf_eq, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    constructor <;> linarith

/-- Circle mass of a smoothed term. -/
theorem integral_norm_sq_smoothTerm_le (ha0 : 0 < a) {δ : ℝ} (hδ : 0 < δ) {σ₀ R R' : ℝ} (hR'0 : 0 ≤ R')
    (hR'R : R' ≤ R) (n : ℕ) :
    ∫ θ in (0 : ℝ)..2 * π, ‖shiftedTerm (a / 4) (thetaPowerCoeff a) n (circleMap (σ₀ : ℂ) R' θ) *
      (thetaPowerSmoothWeight a δ n : ℂ)‖ ^ 2 ≤
      2 * π * (‖thetaPowerCoeff a n‖ ^ 2 *
        (((n : ℝ) + a / 4) ^ (-(2 * (σ₀ - R))) + ((n : ℝ) + a / 4) ^ (-(2 * (σ₀ + R))))) := by
  have hα0 : 0 < a / 4 := by positivity
  have hc : Continuous fun θ => ‖shiftedTerm (a / 4) (thetaPowerCoeff a) n
      (circleMap (σ₀ : ℂ) R' θ) * (thetaPowerSmoothWeight a δ n : ℂ)‖ ^ 2 :=
    (((differentiable_shiftedTerm hα0 _ n).continuous.comp (continuous_circleMap _ _)).mul
      continuous_const).norm.pow 2
  refine (intervalIntegral.integral_mono_on (g := fun _ => ‖thetaPowerCoeff a n‖ ^ 2 *
      (((n : ℝ) + a / 4) ^ (-(2 * (σ₀ - R))) + ((n : ℝ) + a / 4) ^ (-(2 * (σ₀ + R)))))
    (by positivity) (hc.intervalIntegrable _ _) intervalIntegrable_const fun θ _ => ?_).trans
    (le_of_eq ?_)
  · have hmem := closedBall_subset_closedBall hR'R (circleMap_mem_closedBall (σ₀ : ℂ) hR'0 θ)
    obtain ⟨h1, h2⟩ := re_mem_of_mem_closedBall hmem
    have hw0 := (thetaPowerSmoothWeight_pos a δ n).le
    have hw1 := thetaPowerSmoothWeight_le_one ha0 hδ.le n
    have hβ := norm_shiftedTerm_sq_le hα0 (thetaPowerCoeff a) n h1 h2
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0, mul_pow]
    calc _ ≤ ‖shiftedTerm (a / 4) (thetaPowerCoeff a) n (circleMap (σ₀ : ℂ) R' θ)‖ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hw0 hw1) (sq_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact hβ
  · rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]

/-- The middle block `N ≤ n < M` has circle mass at most `2π` times the tail of the envelope. -/
theorem sum_Ico_integral_norm_sq_smoothTerm_le (ha0 : 0 < a) {δ : ℝ} (hδ : 0 < δ) {σ₀ R R' : ℝ}
    (hR'0 : 0 ≤ R') (hR'R : R' ≤ R) {Q : ℕ → ℝ}
    (hQ : Q = fun n => ‖thetaPowerCoeff a n‖ ^ 2 *
      (((n : ℝ) + a / 4) ^ (-(2 * (σ₀ - R))) + ((n : ℝ) + a / 4) ^ (-(2 * (σ₀ + R)))))
    (hQs : Summable Q) (N M : ℕ) :
    ∑ n ∈ Finset.Ico N M, ∫ θ in (0 : ℝ)..2 * π,
      ‖shiftedTerm (a / 4) (thetaPowerCoeff a) n (circleMap (σ₀ : ℂ) R' θ) *
        (thetaPowerSmoothWeight a δ n : ℂ)‖ ^ 2 ≤ 2 * π * ∑' k, Q (k + N) := by
  have hQ0 : ∀ n, 0 ≤ Q n := fun n => by rw [hQ]; positivity
  calc _ ≤ ∑ n ∈ Finset.Ico N M, 2 * π * Q n := Finset.sum_le_sum fun n _ => by
        have := integral_norm_sq_smoothTerm_le ha0 hδ (σ₀ := σ₀) hR'0 hR'R n
        rw [hQ]
        exact this
    _ = 2 * π * ∑ n ∈ Finset.Ico N M, Q n := by rw [Finset.mul_sum]
    _ ≤ 2 * π * ∑' k, Q (k + N) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [Finset.sum_Ico_eq_sum_range]
        have := ((summable_nat_add_iff N).mpr hQs).sum_le_tsum (Finset.range (M - N))
          (fun k _ => hQ0 _)
        exact le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => by rw [add_comm])) this

theorem half_budget_le {X SP ε : ℝ} (hX : 0 < X) (hSP : 0 ≤ SP) (hε : 0 < ε) :
    X * (SP * (ε / (10 * X * (SP + 1)) / 2)) ≤ ε / 20 := by
  rw [show X * (SP * (ε / (10 * X * (SP + 1)) / 2)) = ε / 20 * (SP / (SP + 1)) by field_simp; ring]
  have : SP / (SP + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  nlinarith

theorem sum_fejer_coeff_eq (N L : ℕ) (hL : 0 < L) (X P : ℝ) {κA : ℝ} (hκA : κA ≠ 0) (c : ℕ → ℝ) :
    ∑ n ∈ Finset.range N, X * (c n * P / (2 * κA)) * (2 / (L : ℝ)) =
      X * (∑ n ∈ Finset.range N, c n * P) / (κA * L) := by
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_div]
  generalize (∑ n ∈ Finset.range N, c n * P) = S
  have : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  field_simp

theorem budget_false {ε A B W Tl K Sd Yt E : ℝ} (hℓ : ε - (A + B + W + Tl + K) - Sd - Yt ≤ E)
    (hA : A = ε / 10) (hB : B ≤ ε / 20) (hW : W ≤ ε / 10) (hTl : Tl ≤ ε / 10) (hK : K = ε / 10)
    (hSd : Sd ≤ ε / 10) (hYt : Yt ≤ ε / 10) (hE : E ≤ ε / 10) (hε : 0 < ε) : False := by
  linarith

/-- **Transfer to a vertical translate.** If the frequencies `-log(n + a/4)` are independent over `ℤ` and `f` is
a uniform limit on `|z - σ₀| ≤ R` of phased partial sums `Σ_{n<N} u_n β_n` (for arbitrarily large `N`), then
for every `ε > 0` and `T₀` some translate `D(· + it)`, `t ≥ T₀`, is `ε`-close to `f` on `|z - σ₀| ≤ r`. -/
theorem exists_shift_near_target (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (hω : ∀ M : ℕ, ∀ m : Fin M → ℤ, ∑ i, (m i : ℝ) * thetaPowerLogFreq a i = 0 → m = 0)
    {σ₀ R r : ℝ} (hr : 0 < r) (hrR : r < R) (hlo : 1 / 4 < σ₀ - R) (hhi : σ₀ + R ≤ 1)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball (σ₀ : ℂ) R)) {u : ℕ → ℂ} (hu : ∀ n, ‖u n‖ = 1)
    (happrox : ∀ ε > 0, ∀ N₁ : ℕ, ∃ N ≥ N₁, ∀ z ∈ closedBall (σ₀ : ℂ) R,
      ‖f z - ∑ n ∈ Finset.range N, u n * shiftedTerm (a / 4) (thetaPowerCoeff a) n z‖ ≤ ε)
    {ε : ℝ} (hε : 0 < ε) (T₀ : ℝ) :
    ∃ t : ℝ, T₀ ≤ t ∧ ∀ z ∈ closedBall (σ₀ : ℂ) r, ‖thetaPowerDirichlet a (z + t * I) - f z‖ ≤ ε := by
  classical
  have hα0 : 0 < a / 4 := by positivity
  obtain ⟨θ', hθ⟩ : ∃ θ' : ℕ → ℝ, ∀ n, u n = Complex.exp ((θ' n : ℂ) * I) := by
    refine ⟨fun n => Complex.arg (u n), fun n => ?_⟩
    have h := Complex.norm_mul_exp_arg_mul_I (u n)
    rw [hu n, Complex.ofReal_one, one_mul] at h
    exact h.symm
  -- geometry
  obtain ⟨R', hR'⟩ : ∃ R' : ℝ, R' = (r + R) / 2 := ⟨_, rfl⟩
  have hrR' : r < R' := by rw [hR']; linarith
  have hR'R : R' < R := by rw [hR']; linarith
  have hR'0 : 0 ≤ R' := by linarith
  obtain ⟨Cc, hCc⟩ : ∃ Cc : ℝ, Cc = R' / (R' - r) / (2 * π) := ⟨_, rfl⟩
  have hCc0 : 0 < Cc := by
    have h1 : 0 < R' - r := by linarith
    have h2 : 0 < R' := by linarith
    rw [hCc]; positivity
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = Cc * (2 * π) := ⟨_, rfl⟩
  have hX0 : 0 < X := by rw [hX]; positivity
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (a / 4) ^ (-2 : ℝ) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  -- square-summable envelope of `|β_n|²` on the disc
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ → ℝ, Q = fun n => ‖thetaPowerCoeff a n‖ ^ 2 *
      (((n : ℝ) + a / 4) ^ (-(2 * (σ₀ - R))) + ((n : ℝ) + a / 4) ^ (-(2 * (σ₀ + R)))) := ⟨_, rfl⟩
  have hQs : Summable Q := by
    rw [hQ]
    refine ((summable_thetaPowerCoeff_sq_rpow ha0 ha1 (u := 2 * (σ₀ - R)) (by linarith)).add
      (summable_thetaPowerCoeff_sq_rpow ha0 ha1 (u := 2 * (σ₀ + R)) (by linarith))).congr fun n => ?_
    ring
  -- mean square of the error
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = (σ₀ - R - 1 / 4) / 2 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; linarith
  have hη1 : η ≤ 1 := by rw [hη]; linarith
  obtain ⟨C, hC0, hM2⟩ := exists_lintegral_thetaPowerDirichletError_Icc_zero_le ha0 ha1 hη0 hη1
    (show 1 / 4 + η < σ₀ - R by rw [hη]; linarith)
  -- parameters `κ`, `N`, `κA`, `L`, `δ`, `M`, in this order
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = ε / (10 * X) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  obtain ⟨N₁, hN₁⟩ := exists_tail_le Q (show 0 < κ * ε / (5 * X) by positivity)
  obtain ⟨N, hNN₁, hFN⟩ := happrox (ε / (10 * X)) (by positivity) N₁
  obtain ⟨SP, hSP⟩ : ∃ SP : ℝ, SP = ∑ n ∈ Finset.range N, ‖thetaPowerCoeff a n‖ * P := ⟨_, rfl⟩
  have hSP0 : 0 ≤ SP := by rw [hSP]; exact Finset.sum_nonneg fun n _ => by positivity
  obtain ⟨κA, hκA⟩ : ∃ κA : ℝ, κA = ε / (10 * X * (SP + 1)) := ⟨_, rfl⟩
  have hκA0 : 0 < κA := by rw [hκA]; positivity
  obtain ⟨L, hL0, hLb⟩ := exists_fejer_order X SP hκA0 hε
  obtain ⟨δ, hδ0, hδW, hδE⟩ := exists_smoothing_parameter a N X (fun n => ‖thetaPowerCoeff a n‖ * P)
    ((L : ℝ) ^ N * (Cc / (2 * κ)) * (2 * π * (4 * C))) hη0 hε
  obtain ⟨C₀, hC₀0, hM2δ⟩ := hM2 δ hδ0
  obtain ⟨M, hNM, hMT⟩ := exists_truncation a δ X P N hε
  -- the Fejér average of the computable part
  have hy : ∀ n, Continuous fun θ =>
      shiftedTerm (a / 4) (thetaPowerCoeff a) n (circleMap (σ₀ : ℂ) R' θ) *
        (thetaPowerSmoothWeight a δ n : ℂ) := fun n =>
    ((differentiable_shiftedTerm hα0 _ n).continuous.comp (continuous_circleMap _ _)).mul
      continuous_const
  have hlim := RHTower.Weyl.tendsto_fejerWeight_combination N L hL0 hNM (thetaPowerLogFreq a) θ'
    (hω M)
    (ε - X * (ε / (10 * X) + SP * (κA / 2) +
      ∑ n ∈ Finset.range N, ‖thetaPowerCoeff a n‖ * P * (1 - thetaPowerSmoothWeight a δ n) +
      (∑' k, ‖thetaPowerCoeff a (k + M)‖ * thetaPowerSmoothWeight a δ (k + M)) * P + κ))
    (Cc / (2 * κ)) (fun n => X * (‖thetaPowerCoeff a n‖ * P / (2 * κA)))
    (fun n θ => shiftedTerm (a / 4) (thetaPowerCoeff a) n (circleMap (σ₀ : ℂ) R' θ) *
      (thetaPowerSmoothWeight a δ n : ℂ)) hy
  have hψc := RHTower.Weyl.continuous_fejerWeight_re N L (fun j : Fin M => θ' j)
    (fun j : Fin M => thetaPowerLogFreq a j)
  have hψb := fun t => RHTower.Weyl.fejerWeight_bounds N L (fun j : Fin M => θ' j) hL0
    (fun j : Fin M => thetaPowerLogFreq a j) t
  have hqc := continuous_error_on_circle ha0 ha1 hδ0 hlo hhi hR'0 hR'R.le
  -- if no translate works, the majorant exceeds `ε` everywhere
  by_contra hcon
  push Not at hcon
  have hΦ : ∀ t : ℝ, T₀ ≤ t → ε < Cc * (2 * π * (ε / (10 * X) + ∑ n ∈ Finset.range N,
          ‖thetaPowerCoeff a n‖ * P * (κA / 2 +
            ‖Complex.exp (((thetaPowerLogFreq a n * t : ℝ) : ℂ) * I) -
              Complex.exp ((θ' n : ℂ) * I)‖ ^ 2 / (2 * κA)) +
        ∑ n ∈ Finset.range N, ‖thetaPowerCoeff a n‖ * P * (1 - thetaPowerSmoothWeight a δ n) +
        (∑' k, ‖thetaPowerCoeff a (k + M)‖ * thetaPowerSmoothWeight a δ (k + M)) * P + κ) +
      (∫ θ in (0 : ℝ)..2 * π, ‖∑ n ∈ Finset.Ico N M,
          (shiftedTerm (a / 4) (thetaPowerCoeff a) n (circleMap (σ₀ : ℂ) R' θ) *
            (thetaPowerSmoothWeight a δ n : ℂ)) *
          Complex.exp (((thetaPowerLogFreq a n * t : ℝ) : ℂ) * I)‖ ^ 2) / (2 * κ) +
      (∫ θ in (0 : ℝ)..2 * π,
        ‖thetaPowerDirichletError a δ (circleMap (σ₀ : ℂ) R' θ + t * I)‖ ^ 2) / (2 * κ)) := by
    intro t ht
    obtain ⟨z, hz, hlt⟩ := hcon t ht
    have hm := norm_dirichlet_shift_sub_le_majorant ha0 ha1 hδ0 hr hrR hlo hhi hf hθ hNM hFN hκ0 hκA0
      t hz
    rw [hCc, hP, hR']
    exact hlt.trans_le hm
  have hℓ := average_majorant_le (s := Finset.range N) (ε := ε) (εF := ε / (10 * X))
    (W := ∑ n ∈ Finset.range N, ‖thetaPowerCoeff a n‖ * P * (1 - thetaPowerSmoothWeight a δ n))
    (Tl := (∑' k, ‖thetaPowerCoeff a (k + M)‖ * thetaPowerSmoothWeight a δ (k + M)) * P)
    (κ := κ) (κA := κA) (Cc := Cc) (Λ := (L : ℝ) ^ N) (C₀ := C₀) (C₁ := 4 * C * δ ^ (2 * η))
    (p := fun n => ‖thetaPowerCoeff a n‖ * P)
    (q := fun t θ => ‖thetaPowerDirichletError a δ (circleMap (σ₀ : ℂ) R' θ + t * I)‖ ^ 2)
    (QE := fun t => ∫ θ in (0 : ℝ)..2 * π,
      ‖thetaPowerDirichletError a δ (circleMap (σ₀ : ℂ) R' θ + t * I)‖ ^ 2)
    hlim hψc (fun t => (hψb t).2.1) (fun t => (hψb t).2.2) (fun n => by fun_prop)
    (RHTower.Weyl.continuous_integral_norm_sq_trig_sum (Finset.Ico N M) (thetaPowerLogFreq a) _ hy)
    hqc (fun t θ => sq_nonneg _) (fun t => rfl) hκ0 hCc0.le hC₀0 (by positivity)
    (fun T hT θ => by
      obtain ⟨h1, h2, h3⟩ := circleMap_re_im_bounds hlo hhi hR'0 hR'R.le θ
      exact hM2δ _ T h1 h2 h3 hT)
    (by rw [hX, hSP]) (fun n => by rw [hX]) rfl hΦ
  beta_reduce at hℓ
  -- the budget
  have f7 : Cc / (2 * κ) * ∑ n ∈ Finset.Ico N M, ∫ θ in (0 : ℝ)..2 * π,
      ‖shiftedTerm (a / 4) (thetaPowerCoeff a) n (circleMap (σ₀ : ℂ) R' θ) *
        (thetaPowerSmoothWeight a δ n : ℂ)‖ ^ 2 ≤ ε / 10 := by
    have hsum := (sum_Ico_integral_norm_sq_smoothTerm_le ha0 hδ0 hR'0 hR'R.le hQ hQs N M).trans
      (mul_le_mul_of_nonneg_left (hN₁ N hNN₁) (by positivity))
    refine (mul_le_mul_of_nonneg_left hsum (by positivity)).trans (le_of_eq ?_)
    rw [hX, hκ]
    field_simp
    ring
  have hexp : X * (ε / (10 * X) + SP * (κA / 2) +
      ∑ n ∈ Finset.range N, ‖thetaPowerCoeff a n‖ * P * (1 - thetaPowerSmoothWeight a δ n) +
      (∑' k, ‖thetaPowerCoeff a (k + M)‖ * thetaPowerSmoothWeight a δ (k + M)) * P + κ) =
      X * (ε / (10 * X)) + X * (SP * (κA / 2)) +
      X * ∑ n ∈ Finset.range N, ‖thetaPowerCoeff a n‖ * P * (1 - thetaPowerSmoothWeight a δ n) +
      X * ((∑' k, ‖thetaPowerCoeff a (k + M)‖ * thetaPowerSmoothWeight a δ (k + M)) * P) +
      X * κ := by ring
  rw [hexp, sum_fejer_coeff_eq N L hL0 X P hκA0.ne', ← hSP] at hℓ
  refine budget_false hℓ (by field_simp) (by rw [hκA]; exact half_budget_le hX0 hSP0 hε) hδW hMT
    (by rw [hκ]; field_simp) hLb f7 ?_ hε
  calc (L : ℝ) ^ N * (Cc / (2 * κ)) * (2 * π * (4 * C * δ ^ (2 * η)))
      = (L : ℝ) ^ N * (Cc / (2 * κ)) * (2 * π * (4 * C)) * δ ^ (2 * η) := by ring
    _ ≤ ε / 10 := hδE

end

end RHTower
