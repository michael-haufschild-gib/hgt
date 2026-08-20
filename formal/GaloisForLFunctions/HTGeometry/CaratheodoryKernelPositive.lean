import GaloisForLFunctions.HTGeometry.PSDKernelOperations
import GaloisForLFunctions.HTGeometry.CaratheodoryNevanlinnaPick
import GaloisForLFunctions.HTGeometry.ImaginaryPoleBezoutianGram

/-!
# The Carathéodory kernel of a function with nonnegative real part is positive semidefinite

For an analytic `f` on a disc the Cauchy formula, applied to `f` divided by the reflected pole,
represents the Carathéodory kernel

`K (x, y) = (f x + conj (f y)) / (r ^ 2 - x * conj y)`

as the circle average of `2 Re f` against the rank-one kernel `(ζ - x)⁻¹ conj ((ζ - y)⁻¹)`.  A
nonnegative boundary real part therefore makes every finite Gram matrix of `K` positive
semidefinite.  Rescaling the function and passing to the limit gives the same statement on the
open unit disc, and the Cayley transform carries it to the right half plane.
-/

noncomputable section

open Complex Metric Set Filter Topology
open scoped ComplexConjugate ComplexOrder Real InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

/-! ### The circle evaluation vector -/

/-- The Cauchy evaluation vector of a node against the circle of radius `r`. -/
def circleEval (r : ℝ) (x : ℂ) (θ : ℝ) : ℂ := (circleMap 0 r θ - x)⁻¹

theorem pos_of_norm_lt {r : ℝ} {x : ℂ} (hx : ‖x‖ < r) : 0 < r :=
  lt_of_le_of_lt (norm_nonneg x) hx

theorem norm_circleMap_zero_eq {r : ℝ} (hr : 0 < r) (θ : ℝ) : ‖circleMap 0 r θ‖ = r := by
  rw [norm_circleMap_zero, abs_of_pos hr]

private theorem circleMap_ne_zero {r : ℝ} (hr : 0 < r) (θ : ℝ) : circleMap 0 r θ ≠ 0 := by
  intro h
  have := norm_circleMap_zero_eq hr θ
  rw [h, norm_zero] at this
  exact absurd this.symm (ne_of_gt hr)

theorem circleMap_sub_ne_zero {r : ℝ} {x : ℂ} (hx : ‖x‖ < r) (θ : ℝ) :
    circleMap 0 r θ - x ≠ 0 := by
  intro h
  have hr : 0 < r := pos_of_norm_lt hx
  have hx' : circleMap 0 r θ = x := by linear_combination h
  have := norm_circleMap_zero_eq hr θ
  rw [hx'] at this
  exact absurd this.symm (ne_of_gt hx)

theorem circle_reflected_den_ne_zero {r : ℝ} {y : ℂ} (hy : ‖y‖ < r) (θ : ℝ) :
    (r : ℂ) ^ 2 - conj y * circleMap 0 r θ ≠ 0 := by
  have hr : 0 < r := pos_of_norm_lt hy
  intro h
  have heq : (r : ℂ) ^ 2 = conj y * circleMap 0 r θ := by linear_combination h
  have hnorm : ‖((r : ℂ) ^ 2)‖ = r ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hprod : ‖conj y * circleMap 0 r θ‖ = ‖y‖ * r := by
    rw [norm_mul, RCLike.norm_conj, norm_circleMap_zero_eq hr]
  rw [heq, hprod] at hnorm
  nlinarith

theorem conj_circleMap {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    conj (circleMap 0 r θ) = (r : ℂ) ^ 2 / circleMap 0 r θ := by
  have hne := circleMap_ne_zero hr θ
  have hmul : circleMap 0 r θ * conj (circleMap 0 r θ) = (r : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_circleMap_zero_eq hr]
    push_cast
    ring
  field_simp
  linear_combination hmul

theorem conj_circleEval {r : ℝ} {y : ℂ} (hy : ‖y‖ < r) (θ : ℝ) :
    conj (circleEval r y θ) = circleMap 0 r θ / ((r : ℂ) ^ 2 - conj y * circleMap 0 r θ) := by
  have hr : 0 < r := pos_of_norm_lt hy
  have hne := circleMap_ne_zero hr θ
  have hden := circle_reflected_den_ne_zero hy θ
  have hsub := circleMap_sub_ne_zero hy θ
  have hconjsub : conj (circleMap 0 r θ - y) ≠ 0 := by
    simpa using (map_ne_zero (starRingEnd ℂ)).mpr hsub
  rw [circleEval, map_inv₀, map_sub, conj_circleMap hr]
  rw [eq_div_iff hden, inv_mul_eq_div, div_eq_iff]
  · field_simp
  · rw [sub_ne_zero]
    intro h
    apply hden
    rw [← h]
    field_simp
    ring

/-! ### The two-node Cauchy transform -/

theorem continuous_circleEval {r : ℝ} {x : ℂ} (hx : ‖x‖ < r) :
    Continuous (circleEval r x) := by
  refine Continuous.inv₀ ?_ (circleMap_sub_ne_zero hx)
  exact (continuous_circleMap 0 r).sub continuous_const

/-- **The two-node Cauchy transform.**  Integrating `f` against the product of the evaluation
vectors of two interior nodes reproduces `f` at the first node, divided by the reflected
denominator. -/
theorem integral_circle_two_point {r : ℝ} {f : ℂ → ℂ}
    (hc : ContinuousOn f (closedBall 0 r))
    (hd : ∀ z ∈ ball (0 : ℂ) r, DifferentiableAt ℂ f z)
    {x y : ℂ} (hx : ‖x‖ < r) (hy : ‖y‖ < r) :
    (∫ θ in (0 : ℝ)..(2 * π),
        f (circleMap 0 r θ) * (circleEval r x θ * conj (circleEval r y θ)))
      = 2 * π * (f x / ((r : ℂ) ^ 2 - x * conj y)) := by
  have hr : 0 < r := pos_of_norm_lt hx
  set g : ℂ → ℂ := fun z => f z / ((r : ℂ) ^ 2 - conj y * z) with hg
  have hdenball : ∀ z ∈ closedBall (0 : ℂ) r, (r : ℂ) ^ 2 - conj y * z ≠ 0 := by
    intro z hz
    have hzn : ‖z‖ ≤ r := by simpa using hz
    intro h
    have heq : (r : ℂ) ^ 2 = conj y * z := by linear_combination h
    have hnorm : ‖((r : ℂ) ^ 2)‖ = r ^ 2 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have hprod : ‖conj y * z‖ = ‖y‖ * ‖z‖ := by rw [norm_mul, RCLike.norm_conj]
    rw [heq, hprod] at hnorm
    nlinarith [norm_nonneg y, norm_nonneg z]
  have hgc : ContinuousOn g (closedBall 0 r) := by
    refine hc.div (Continuous.continuousOn (by fun_prop)) hdenball
  have hgd : ∀ z ∈ ball (0 : ℂ) r, DifferentiableAt ℂ g z := by
    intro z hz
    refine DifferentiableAt.div (hd z hz) (by fun_prop) (hdenball z (ball_subset_closedBall hz))
  have hxb : x ∈ ball (0 : ℂ) r := by simpa using hx
  have hcauchy := circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (s := (∅ : Set ℂ)) countable_empty hxb hgc (fun z hz => hgd z hz.1)
  rw [circleIntegral] at hcauchy
  simp only [deriv_circleMap, smul_eq_mul] at hcauchy
  have hcongr : ∀ θ : ℝ,
      circleMap 0 r θ * I * ((circleMap 0 r θ - x)⁻¹ * g (circleMap 0 r θ))
        = I * (f (circleMap 0 r θ) * (circleEval r x θ * conj (circleEval r y θ))) := by
    intro θ
    rw [conj_circleEval hy, circleEval, hg]
    field_simp
  rw [intervalIntegral.integral_congr (g := fun θ =>
    I * (f (circleMap 0 r θ) * (circleEval r x θ * conj (circleEval r y θ))))
    (fun θ _ => hcongr θ), intervalIntegral.integral_const_mul] at hcauchy
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hfinal : I * (∫ θ in (0 : ℝ)..(2 * π),
      f (circleMap 0 r θ) * (circleEval r x θ * conj (circleEval r y θ)))
      = I * (2 * π * (f x / ((r : ℂ) ^ 2 - x * conj y))) := by
    rw [hcauchy]
    simp only [hg]
    rw [show (r : ℂ) ^ 2 - conj y * x = (r : ℂ) ^ 2 - x * conj y by ring]
    ring
  exact mul_left_cancel₀ hI hfinal

/-! ### The circle representation -/

private theorem continuous_comp_circleMap {r : ℝ} {f : ℂ → ℂ} (hr : 0 < r)
    (hc : ContinuousOn f (closedBall 0 r)) :
    Continuous (fun θ : ℝ => f (circleMap 0 r θ)) := by
  refine hc.comp_continuous (continuous_circleMap 0 r) (fun θ => ?_)
  simp [norm_circleMap_zero_eq hr]

/-- **The circle representation of the Carathéodory kernel.**  The kernel is the circle average of
twice the real part of `f` against the rank-one kernel of the evaluation vectors. -/
theorem circle_caratheodory_representation {r : ℝ} {f : ℂ → ℂ}
    (hc : ContinuousOn f (closedBall 0 r))
    (hd : ∀ z ∈ ball (0 : ℂ) r, DifferentiableAt ℂ f z)
    {x y : ℂ} (hx : ‖x‖ < r) (hy : ‖y‖ < r) :
    (f x + conj (f y)) / ((r : ℂ) ^ 2 - x * conj y)
      = ((2 * π)⁻¹ : ℝ) * ∫ θ in (0 : ℝ)..(2 * π),
          ((2 * (f (circleMap 0 r θ)).re : ℝ) : ℂ) *
            (circleEval r x θ * conj (circleEval r y θ)) := by
  have hr : 0 < r := pos_of_norm_lt hx
  have hFc : Continuous (fun θ : ℝ => f (circleMap 0 r θ)) := continuous_comp_circleMap hr hc
  have hEx : Continuous (circleEval r x) := continuous_circleEval hx
  have hEy : Continuous (circleEval r y) := continuous_circleEval hy
  have hcx : Continuous (fun θ : ℝ => conj (circleEval r x θ)) :=
    Complex.continuous_conj.comp hEx
  have hcy : Continuous (fun θ : ℝ => conj (circleEval r y θ)) :=
    Complex.continuous_conj.comp hEy
  have hcf : Continuous (fun θ : ℝ => conj (f (circleMap 0 r θ))) :=
    Complex.continuous_conj.comp hFc
  have hint1 : IntervalIntegrable
      (fun θ : ℝ => f (circleMap 0 r θ) * (circleEval r x θ * conj (circleEval r y θ)))
      MeasureTheory.volume 0 (2 * π) :=
    (hFc.mul (hEx.mul hcy)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable
      (fun θ : ℝ => conj (f (circleMap 0 r θ)) * (circleEval r x θ * conj (circleEval r y θ)))
      MeasureTheory.volume 0 (2 * π) :=
    (hcf.mul (hEx.mul hcy)).intervalIntegrable _ _
  have hsplit : (∫ θ in (0 : ℝ)..(2 * π),
        ((2 * (f (circleMap 0 r θ)).re : ℝ) : ℂ) *
          (circleEval r x θ * conj (circleEval r y θ)))
      = (∫ θ in (0 : ℝ)..(2 * π),
          f (circleMap 0 r θ) * (circleEval r x θ * conj (circleEval r y θ)))
        + ∫ θ in (0 : ℝ)..(2 * π),
          conj (f (circleMap 0 r θ)) * (circleEval r x θ * conj (circleEval r y θ)) := by
    rw [← intervalIntegral.integral_add hint1 hint2]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    rw [← Complex.add_conj]
    ring
  have hsecond : (∫ θ in (0 : ℝ)..(2 * π),
        conj (f (circleMap 0 r θ)) * (circleEval r x θ * conj (circleEval r y θ)))
      = conj (∫ θ in (0 : ℝ)..(2 * π),
          f (circleMap 0 r θ) * (circleEval r y θ * conj (circleEval r x θ))) := by
    rw [← intervalIntegral.intervalIntegral_conj]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    simp only [map_mul, Complex.conj_conj]
    ring
  have h1 := integral_circle_two_point hc hd hx hy
  have h2 := integral_circle_two_point hc hd hy hx
  have hden : (r : ℂ) ^ 2 - x * conj y ≠ 0 := by
    intro h
    have hx' : ‖x * conj y‖ = ‖x‖ * ‖y‖ := by rw [norm_mul, RCLike.norm_conj]
    have heq : (r : ℂ) ^ 2 = x * conj y := by linear_combination h
    have hnorm : ‖((r : ℂ) ^ 2)‖ = r ^ 2 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    rw [heq, hx'] at hnorm
    nlinarith [norm_nonneg x, norm_nonneg y]
  have hconjden : conj ((r : ℂ) ^ 2 - y * conj x) = (r : ℂ) ^ 2 - x * conj y := by
    simp only [map_sub, map_mul, map_pow, Complex.conj_ofReal, Complex.conj_conj]
    ring
  have hpi : ((2 * π : ℝ) : ℂ) ≠ 0 := by
    simp only [Ne, Complex.ofReal_eq_zero]
    positivity
  have h2pi : (2 : ℂ) * (π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  have hconjrhs : conj (2 * (π : ℂ) * (f y / ((r : ℂ) ^ 2 - y * conj x)))
      = 2 * (π : ℂ) * (conj (f y) / ((r : ℂ) ^ 2 - x * conj y)) := by
    rw [h2pi, map_mul, map_div₀, hconjden, Complex.conj_ofReal]
  rw [hsplit, h1, hsecond, h2, hconjrhs]
  push_cast
  field_simp

/-! ### Positivity of the Gram matrices -/

/-- **The circle Carathéodory kernel is a positive Gram kernel.**  If the real part of `f` is
nonnegative on the circle of radius `r`, every finite Gram matrix of the kernel
`(f x + conj (f y)) / (r ^ 2 - x * conj y)` at interior nodes is positive semidefinite. -/
theorem posSemidef_circleCaratheodoryGram {r : ℝ} {f : ℂ → ℂ} (hr : 0 < r)
    (hc : ContinuousOn f (closedBall 0 r))
    (hd : ∀ z ∈ ball (0 : ℂ) r, DifferentiableAt ℂ f z)
    (hu : ∀ θ : ℝ, 0 ≤ (f (circleMap 0 r θ)).re)
    {n : ℕ} (w : Fin n → ℂ) (hw : ∀ j, ‖w j‖ < r) :
    (Matrix.of fun j k =>
      (f (w j) + conj (f (w k))) / ((r : ℂ) ^ 2 - w j * conj (w k))).PosSemidef := by
  classical
  have hFc : Continuous (fun θ : ℝ => f (circleMap 0 r θ)) := continuous_comp_circleMap hr hc
  have hE : ∀ j, Continuous (circleEval r (w j)) := fun j => continuous_circleEval (hw j)
  have hcE : ∀ j, Continuous (fun θ : ℝ => conj (circleEval r (w j) θ)) :=
    fun j => Complex.continuous_conj.comp (hE j)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext j k
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def, map_div₀, map_add,
      Complex.conj_conj, map_sub, map_mul, map_pow, Complex.conj_ofReal]
    ring_nf
  · intro c
    set G : ℝ → ℂ := fun θ => ∑ j, c j * conj (circleEval r (w j) θ) with hGdef
    set B : Fin n → Fin n → ℝ → ℂ := fun j k θ =>
      conj (c j) * c k *
        (((2 * (f (circleMap 0 r θ)).re : ℝ) : ℂ) *
          (circleEval r (w j) θ * conj (circleEval r (w k) θ))) with hBdef
    have hcontB : ∀ j k, Continuous (B j k) := by
      intro j k
      rw [hBdef]
      exact continuous_const.mul
        ((Complex.continuous_ofReal.comp
          (continuous_const.mul (Complex.continuous_re.comp hFc))).mul ((hE j).mul (hcE k)))
    have hintjk : ∀ j k, IntervalIntegrable (B j k) MeasureTheory.volume 0 (2 * π) :=
      fun j k => (hcontB j k).intervalIntegrable _ _
    have hintsum : ∀ j, IntervalIntegrable (fun θ => ∑ k, B j k θ)
        MeasureTheory.volume 0 (2 * π) :=
      fun j => (continuous_finsetSum _ fun k _ => hcontB j k).intervalIntegrable _ _
    have hpoint : ∀ θ : ℝ, (∑ j, ∑ k, B j k θ)
        = ((2 * (f (circleMap 0 r θ)).re * Complex.normSq (G θ) : ℝ) : ℂ) := by
      intro θ
      have hconjG : conj (G θ) = ∑ j, conj (c j) * circleEval r (w j) θ := by
        rw [hGdef]
        simp only [map_sum, map_mul, Complex.conj_conj]
      have hexp : conj (G θ) * G θ
          = ∑ j, ∑ k, (conj (c j) * circleEval r (w j) θ) *
              (c k * conj (circleEval r (w k) θ)) := by
        rw [hconjG, hGdef, Finset.sum_mul_sum]
      have hprod : (∑ j, ∑ k, B j k θ)
          = ((2 * (f (circleMap 0 r θ)).re : ℝ) : ℂ) * (conj (G θ) * G θ) := by
        rw [hexp, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hBdef]
        ring
      rw [hprod, mul_comm (conj (G θ)) (G θ), Complex.mul_conj]
      push_cast
      ring
    have hdot : star c ⬝ᵥ (Matrix.of fun j k =>
        (f (w j) + conj (f (w k))) / ((r : ℂ) ^ 2 - w j * conj (w k))).mulVec c
        = ∑ j, ∑ k, conj (c j) * c k *
            ((f (w j) + conj (f (w k))) / ((r : ℂ) ^ 2 - w j * conj (w k))) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hstep : ∀ j k, conj (c j) * c k *
          ((f (w j) + conj (f (w k))) / ((r : ℂ) ^ 2 - w j * conj (w k)))
        = ((2 * π)⁻¹ : ℝ) * ∫ θ in (0 : ℝ)..(2 * π), B j k θ := by
      intro j k
      rw [circle_caratheodory_representation hc hd (hw j) (hw k), hBdef,
        intervalIntegral.integral_const_mul]
      ring
    have hpull : (∑ j, ∑ k, ((2 * π)⁻¹ : ℝ) * ∫ θ in (0 : ℝ)..(2 * π), B j k θ)
        = ((2 * π)⁻¹ : ℝ) * ∑ j, ∑ k, ∫ θ in (0 : ℝ)..(2 * π), B j k θ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
    have hsum2 : (∫ θ in (0 : ℝ)..(2 * π), ∑ j, ∑ k, B j k θ)
        = ∑ j, ∑ k, ∫ θ in (0 : ℝ)..(2 * π), B j k θ := by
      rw [intervalIntegral.integral_finsetSum (fun j _ => hintsum j)]
      exact Finset.sum_congr rfl fun j _ =>
        intervalIntegral.integral_finsetSum (fun k _ => hintjk j k)
    rw [hdot]
    simp only [hstep]
    rw [hpull, ← hsum2]
    simp only [hpoint]
    rw [intervalIntegral.integral_ofReal, ← Complex.ofReal_mul]
    refine Complex.zero_le_real.mpr (mul_nonneg (by positivity) ?_)
    refine intervalIntegral.integral_nonneg (by positivity) (fun θ _ => ?_)
    exact mul_nonneg (by linarith [hu θ]) (Complex.normSq_nonneg _)

/-! ### The open unit disc -/

theorem complex_nonneg_of_tendsto {Q : ℝ → ℂ} {z : ℂ} {l : Filter ℝ} [l.NeBot]
    (hQ : Tendsto Q l (𝓝 z)) (h : ∀ᶠ t in l, 0 ≤ Q t) : 0 ≤ z := by
  have hre : (0 : ℝ) ≤ z.re :=
    ge_of_tendsto ((Complex.continuous_re.tendsto z).comp hQ)
      (h.mono fun t ht => by simpa using (Complex.le_def.mp ht).1)
  have him : Tendsto (fun t => (Q t).im) l (𝓝 z.im) := (Complex.continuous_im.tendsto z).comp hQ
  have him0 : Tendsto (fun t => (Q t).im) l (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    exact h.mono fun t ht => by simpa using (Complex.le_def.mp ht).2
  have hz : z.im = 0 := tendsto_nhds_unique him him0
  exact Complex.le_def.mpr ⟨by simpa using hre, by simp [hz]⟩

/-- **The unit-disc Carathéodory kernel is a positive Gram kernel.**  A function analytic on the
open unit disc with nonnegative real part has positive semidefinite Carathéodory Gram matrices at
every finite family of interior nodes. -/
theorem posSemidef_discCaratheodoryGram {f : ℂ → ℂ}
    (hd : ∀ z ∈ ball (0 : ℂ) 1, DifferentiableAt ℂ f z)
    (hu : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (f z).re)
    {n : ℕ} (w : Fin n → ℂ) (hw : ∀ j, ‖w j‖ < 1) :
    (Matrix.of fun j k => (f (w j) + conj (f (w k))) / (1 - w j * conj (w k))).PosSemidef := by
  classical
  have hmemball : ∀ {t : ℝ}, 0 < t → t < 1 → ∀ z : ℂ, ‖z‖ ≤ 1 → (t : ℂ) * z ∈ ball (0 : ℂ) 1 := by
    intro t ht ht1 z hz
    have hnorm : ‖(t : ℂ) * z‖ = t * ‖z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    simp only [mem_ball_zero_iff, hnorm]
    nlinarith [norm_nonneg z]
  have hden : ∀ j k, (1 : ℂ) - w j * conj (w k) ≠ 0 := by
    intro j k h
    have heq : (1 : ℂ) = w j * conj (w k) := by linear_combination h
    have hn : ‖w j * conj (w k)‖ = ‖w j‖ * ‖w k‖ := by rw [norm_mul, RCLike.norm_conj]
    have : (1 : ℝ) = ‖w j‖ * ‖w k‖ := by rw [← hn, ← heq, norm_one]
    nlinarith [norm_nonneg (w j), norm_nonneg (w k), hw j, hw k]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext j k
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def, map_div₀, map_add,
      Complex.conj_conj, map_sub, map_mul, map_one]
    ring_nf
  · intro c
    set g : Fin n → Fin n → ℝ → ℂ := fun j k t => conj (c j) * c k *
      ((f ((t : ℂ) * w j) + conj (f ((t : ℂ) * w k))) / (1 - w j * conj (w k))) with hgdef
    set Q : ℝ → ℂ := fun t => ∑ j, ∑ k, g j k t with hQdef
    have hQpos : ∀ t : ℝ, 0 < t → t < 1 → 0 ≤ Q t := by
      intro t ht ht1
      set g : ℂ → ℂ := fun z => f ((t : ℂ) * z) with hg
      have hgd : ∀ z ∈ ball (0 : ℂ) 1, DifferentiableAt ℂ g z := by
        intro z hz
        have hzc : ‖z‖ ≤ 1 := le_of_lt (mem_ball_zero_iff.mp hz)
        exact (hd _ (hmemball ht ht1 z hzc)).comp z (by fun_prop)
      have hgc : ContinuousOn g (closedBall 0 1) := by
        intro z hz
        have hzc : ‖z‖ ≤ 1 := by simpa using hz
        exact (((hd _ (hmemball ht ht1 z hzc)).continuousAt.comp
          (by fun_prop : ContinuousAt (fun z : ℂ => (t : ℂ) * z) z))).continuousWithinAt
      have hgu : ∀ θ : ℝ, 0 ≤ (g (circleMap 0 1 θ)).re := by
        intro θ
        exact hu _ (hmemball ht ht1 _ (le_of_eq (norm_circleMap_zero_eq one_pos θ)))
      have hmat := posSemidef_circleCaratheodoryGram (r := 1) one_pos hgc hgd hgu w
        (fun j => by simpa using hw j)
      have hquad := hmat.dotProduct_mulVec_nonneg c
      have hval : star c ⬝ᵥ (Matrix.of fun j k =>
          (g (w j) + conj (g (w k))) / (((1 : ℝ) : ℂ) ^ 2 - w j * conj (w k))).mulVec c = Q t := by
        simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def,
          hQdef, hgdef, hg, Complex.ofReal_one, one_pow]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rwa [hval] at hquad
    have hcontw : ∀ j, ContinuousAt (fun t : ℝ => f ((t : ℂ) * w j)) 1 := by
      intro j
      have h1 : ContinuousAt (fun t : ℝ => (t : ℂ) * w j) 1 := by fun_prop
      have h2 : ContinuousAt f (((1 : ℝ) : ℂ) * w j) := by
        refine (hd _ ?_).continuousAt
        simp only [Complex.ofReal_one, one_mul]
        simpa using hw j
      exact ContinuousAt.comp (x := (1 : ℝ)) h2 h1
    have hcontjk : ∀ j k, ContinuousAt (g j k) 1 := by
      intro j k
      rw [hgdef]
      refine ContinuousAt.mul continuousAt_const
        (ContinuousAt.div ?_ continuousAt_const (hden j k))
      exact (hcontw j).add ((Complex.continuous_conj.continuousAt).comp (hcontw k))
    have hQcont : ContinuousAt Q 1 := by
      have h1 : ∀ j, ContinuousAt (fun t => ∑ k, g j k t) 1 :=
        fun j => tendsto_finsetSum _ fun k _ => hcontjk j k
      exact tendsto_finsetSum _ fun j _ => h1 j
    have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), 0 ≤ Q t := by
      have h1 : ∀ᶠ t in 𝓝[<] (1 : ℝ), t < 1 := eventually_mem_nhdsWithin
      have h2 : ∀ᶠ t in 𝓝[<] (1 : ℝ), (0 : ℝ) < t :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num))
      filter_upwards [h1, h2] with t ht1 ht2 using hQpos t ht2 ht1
    have hlim : Tendsto Q (𝓝[<] (1 : ℝ)) (𝓝 (Q 1)) := hQcont.tendsto.mono_left nhdsWithin_le_nhds
    have hQ1 : (0 : ℂ) ≤ Q 1 := complex_nonneg_of_tendsto hlim hev
    have hval1 : star c ⬝ᵥ (Matrix.of fun j k =>
        (f (w j) + conj (f (w k))) / (1 - w j * conj (w k))).mulVec c = Q 1 := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def,
        hQdef, hgdef, Complex.ofReal_one, one_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hval1]
    exact hQ1

/-! ### The right half plane -/

/-- The inverse Cayley chart maps the open unit disc into the open right half plane. -/
theorem re_cayleyChart_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < ((1 + z) / (1 - z)).re := by
  have hne : (1 : ℂ) - z ≠ 0 := by
    intro h
    have hz1 : z = 1 := by linear_combination -h
    rw [hz1] at hz
    simp at hz
  have hden : (0 : ℝ) < Complex.normSq (1 - z) := Complex.normSq_pos.mpr hne
  have hsq : Complex.normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  rw [Complex.div_re]
  have hnum : (1 + z).re * (1 - z).re / Complex.normSq (1 - z)
      + (1 + z).im * (1 - z).im / Complex.normSq (1 - z)
      = (1 - Complex.normSq z) / Complex.normSq (1 - z) := by
    rw [← add_div]
    congr 1
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  rw [hnum]
  exact div_pos (by linarith) hden

/-- The Cayley denominator identity: the Szegő denominator of two Cayley images is the Cauchy
denominator of the original half-plane nodes. -/
theorem one_sub_cayleyRight_mul_conj {u v : ℂ} (hu : 0 ≤ u.re) (hv : 0 ≤ v.re) :
    1 - cayleyRight u * conj (cayleyRight v)
      = 2 * (u + conj v) / ((u + 1) * (conj v + 1)) := by
  have hu1 : u + 1 ≠ 0 := add_one_ne_zero_of_re_nonneg hu
  have hv1 : v + 1 ≠ 0 := add_one_ne_zero_of_re_nonneg hv
  have hcv1 : conj v + 1 ≠ 0 := by
    intro h
    apply hv1
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  rw [cayleyRight, cayleyRight, map_div₀, map_sub, map_add, map_one]
  field_simp
  ring

/-- **The half-plane Carathéodory kernel is a positive Gram kernel.** -/
theorem posSemidef_halfPlaneCaratheodoryGram {F : ℂ → ℂ}
    (hFd : ∀ u : ℂ, 0 < u.re → DifferentiableAt ℂ F u)
    (hFu : ∀ u : ℂ, 0 < u.re → 0 ≤ (F u).re)
    {n : ℕ} (u : Fin n → ℂ) (hup : ∀ j, 0 < (u j).re) :
    (Matrix.of fun j k => (F (u j) + conj (F (u k))) / (u j + conj (u k))).PosSemidef := by
  classical
  set f : ℂ → ℂ := fun z => F ((1 + z) / (1 - z)) with hf
  have hchartne : ∀ z : ℂ, ‖z‖ < 1 → (1 : ℂ) - z ≠ 0 := by
    intro z hz h
    have hz1 : z = 1 := by linear_combination -h
    rw [hz1] at hz
    simp at hz
  have hfd : ∀ z ∈ ball (0 : ℂ) 1, DifferentiableAt ℂ f z := by
    intro z hz
    have hzn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hchart : DifferentiableAt ℂ (fun z : ℂ => (1 + z) / (1 - z)) z :=
      DifferentiableAt.div (by fun_prop) (by fun_prop) (hchartne z hzn)
    exact (hFd _ (re_cayleyChart_pos hzn)).comp z hchart
  have hfu : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (f z).re := by
    intro z hz
    exact hFu _ (re_cayleyChart_pos (mem_ball_zero_iff.mp hz))
  have hwn : ∀ j, ‖cayleyRight (u j)‖ < 1 := fun j => norm_cayleyRight_lt_one (hup j)
  have hfw : ∀ j, f (cayleyRight (u j)) = F (u j) := by
    intro j
    rw [hf]
    exact congrArg F (cayleyRight_inv (hup j).le)
  have hdisc := posSemidef_discCaratheodoryGram hfd hfu (fun j => cayleyRight (u j)) hwn
  have hcong := posSemidef_congr_diagonal hdisc
    (fun j => ((Real.sqrt 2 : ℝ) : ℂ) / (u j + 1))
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hentry : (Matrix.of fun j k => ((Real.sqrt 2 : ℝ) : ℂ) / (u j + 1) *
        ((Matrix.of fun j k => (f (cayleyRight (u j)) + conj (f (cayleyRight (u k)))) /
          (1 - cayleyRight (u j) * conj (cayleyRight (u k)))) j k) *
        conj (((Real.sqrt 2 : ℝ) : ℂ) / (u k + 1)))
      = Matrix.of fun j k => (F (u j) + conj (F (u k))) / (u j + conj (u k)) := by
    ext j k
    have hu1 : u j + 1 ≠ 0 := add_one_ne_zero_of_re_nonneg (hup j).le
    have hu2 : u k + 1 ≠ 0 := add_one_ne_zero_of_re_nonneg (hup k).le
    have hcu2 : conj (u k) + 1 ≠ 0 := by
      intro h
      apply hu2
      have := congrArg (starRingEnd ℂ) h
      simpa using this
    have hsum : u j + conj (u k) ≠ 0 := by
      intro h
      have hre : (u j + conj (u k)).re = 0 := by rw [h]; simp
      simp only [Complex.add_re, Complex.conj_re] at hre
      have h1 := hup j
      have h2 := hup k
      linarith
    simp only [Matrix.of_apply]
    rw [hfw j, hfw k, one_sub_cayleyRight_mul_conj (hup j).le (hup k).le, map_div₀,
      Complex.conj_ofReal, map_add, map_one]
    field_simp
    ring_nf
    rw [hsq]
    ring
  rwa [hentry] at hcong

/-- **The Carathéodory kernel of a positive-real function on the right half plane.** -/
theorem isPSDKernel_halfPlaneCaratheodory {F : ℂ → ℂ}
    (hFd : ∀ u : ℂ, 0 < u.re → DifferentiableAt ℂ F u)
    (hFu : ∀ u : ℂ, 0 < u.re → 0 ≤ (F u).re) :
    IsPSDKernel (fun x y : {u : ℂ // 0 < u.re} =>
      (F (x : ℂ) + conj (F (y : ℂ))) / ((x : ℂ) + conj (y : ℂ))) := by
  refine isPSDKernel_of_forall_posSemidef (fun x y => ?_) (fun n v => ?_)
  · rw [map_div₀, map_add, map_add, Complex.conj_conj, Complex.conj_conj]
    ring_nf
  · exact posSemidef_halfPlaneCaratheodoryGram hFd hFu (fun j => ((v j : ℂ))) (fun j => (v j).2)

/-- **The shifted Carathéodory kernel.**  On the half plane `Re u > a` the kernel with the shifted
Cauchy denominator `u + conj v - 2 a` is positive semidefinite. -/
theorem isPSDKernel_shiftedCaratheodory {F : ℂ → ℂ} (a : ℝ)
    (hFd : ∀ u : ℂ, a < u.re → DifferentiableAt ℂ F u)
    (hFu : ∀ u : ℂ, a < u.re → 0 ≤ (F u).re) :
    IsPSDKernel (fun x y : {u : ℂ // a < u.re} =>
      (F (x : ℂ) + conj (F (y : ℂ))) / ((x : ℂ) + conj (y : ℂ) - 2 * (a : ℂ))) := by
  have hshift := isPSDKernel_halfPlaneCaratheodory
    (F := fun z => F (z + (a : ℂ)))
    (fun z hz => (hFd (z + (a : ℂ)) (by simpa using by linarith [hz] : a < (z + (a : ℂ)).re)).comp z
      (by fun_prop))
    (fun z hz => hFu (z + (a : ℂ)) (by simp only [Complex.add_re, Complex.ofReal_re]; linarith))
  refine (hshift.comp (fun x : {u : ℂ // a < u.re} => (⟨(x : ℂ) - (a : ℂ), by
      simp only [Complex.sub_re, Complex.ofReal_re]
      linarith [x.2]⟩ : {u : ℂ // 0 < u.re}))).congr fun x y => ?_
  simp only
  rw [show ((x : ℂ) - (a : ℂ)) + (a : ℂ) = (x : ℂ) by ring,
    show ((y : ℂ) - (a : ℂ)) + (a : ℂ) = (y : ℂ) by ring]
  congr 1
  rw [map_sub, Complex.conj_ofReal]
  ring

end GaloisForLFunctions.HTGeometry
