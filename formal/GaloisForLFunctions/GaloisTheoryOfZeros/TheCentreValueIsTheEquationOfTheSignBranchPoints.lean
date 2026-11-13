import GaloisForLFunctions.GaloisTheoryOfZeros.TheFunctionalEquationIsAMonodromyOfTheHeatCover
import GaloisForLFunctions.GaloisTheoryOfZeros.CenteredJensenDiscriminantField

/-!
# The centre value is the equation of the sign branch points

The heat family satisfies the backward heat equation in complex time,
`∂_τ H_τ^{(k)}(z) = −H_τ^{(k+2)}(z)` (`hasDerivAt_time_iteratedDeriv_complexHeat`), hence
`∂_τ^n H_τ(z) = (−1)^n H_τ^{(2n)}(z)` (`iteratedDeriv_time_complexHeat`). Three consequences.

* **Time order.** At a collision of order `2k` the function `τ ↦ H_τ(z₀)` vanishes to order exactly
  `k` (`IsCollision.analyticOrderAt_time`).
* **The sign part of the monodromy.** The centre value `c(τ) = H_τ(0)` is entire, and a zero of
  order `k` of `c` is exactly a collision of order `2k` at the centre
  (`isCollision_center_iff`). There `2k` sheets meet in `k` pairs `±z`, and the turn of the time
  flips the sign of each pair (`center_monodromy_of_analyticOrderAt`). So the number of signs
  flipped around a centre time is the order of `c`: the product of the signs is the Kummer
  character of `√c`. The normalized Taylor coefficients of `c` at `0` are the normalized even
  moments of the Riemann kernel, the generators of the coefficient field of the Jensen equations
  (`iteratedDeriv_centreValue_zero_div`, `hasSum_centreValue`).
* **Singular points and folds.** A point of the heat cover is singular exactly when it is a
  collision of order at least three (`deriv_eq_zero_and_deriv_time_eq_zero_iff`). At a collision
  of order two the cover is the graph of an analytic function of the place, on which the time has
  a critical point (`exists_time_of_isCollision_two`).

In the same language the Riemann hypothesis says that no branch time is real and positive
(`riemannHypothesis_iff_forall_pos_not_mem_branchTimes`).
-/

open Complex MeasureTheory Filter Topology Set Metric
open RHTower RHTower.DeBruijn GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

variable {τ₀ z₀ : ℂ} {m : ℕ}

/-! ## The heat equation in complex time -/

/-- The weight at a complex time is dominated by the weight at a real time above its norm. -/
theorem norm_complexWeight_le_of_norm_le {τ : ℂ} {R : ℝ} (h : ‖τ‖ ≤ R) (x : ℝ) :
    ‖complexWeight τ x‖ ≤ ‖heatWeight R x‖ := by
  refine (norm_complexWeight_le τ x).trans ?_
  have hpos := riemannKernelReal_pos x
  rw [heatWeight, heatWeight, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (mul_pos hpos (Real.exp_pos _)),
    abs_of_pos (mul_pos hpos (Real.exp_pos _))]
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h (sq_nonneg x))) hpos.le

/-- Differentiation in the time under the integral: the time derivative multiplies the weight by
`x² = −(ix)²`. -/
theorem hasDerivAt_time_expTransform (k : ℕ) (τ₀ z : ℂ) :
    HasDerivAt (fun τ => expTransform (fun x => complexWeight τ x * (I * x) ^ k) z)
      (-expTransform (fun x => complexWeight τ₀ x * (I * x) ^ (k + 2)) z) τ₀ := by
  have hcont : ∀ τ : ℂ, Continuous fun x : ℝ =>
      complexWeight τ x * (I * x) ^ k * cexp (I * z * x) := fun τ => by
    have := continuous_complexWeight τ
    fun_prop
  have hcont' : Continuous fun x : ℝ =>
      (x : ℂ) ^ 2 * (complexWeight τ₀ x * (I * x) ^ k * cexp (I * z * x)) := by
    have := continuous_complexWeight τ₀
    fun_prop
  have hbound : ∀ x : ℝ, ∀ τ ∈ ball τ₀ 1,
      ‖(x : ℂ) ^ 2 * (complexWeight τ x * (I * x) ^ k * cexp (I * z * x))‖ ≤
        |x| ^ (k + 2) * ‖heatWeight (‖τ₀‖ + 1) x‖ * Real.exp (|z.im| * |x|) := by
    intro x τ hτ
    have hτn : ‖τ‖ ≤ ‖τ₀‖ + 1 := by
      have h1 : ‖τ - τ₀‖ < 1 := by rwa [mem_ball, dist_eq_norm] at hτ
      have h2 := norm_le_norm_add_norm_sub' τ τ₀
      linarith
    have h1 := norm_complexWeight_le_of_norm_le hτn x
    have h2 := norm_exp_I_mul_le z x
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    calc |x| ^ 2 * (‖complexWeight τ x‖ * |x| ^ k * ‖cexp (I * z * x)‖)
        ≤ |x| ^ 2 * (‖heatWeight (‖τ₀‖ + 1) x‖ * |x| ^ k * Real.exp (|z.im| * |x|)) := by
          gcongr
      _ = |x| ^ (k + 2) * ‖heatWeight (‖τ₀‖ + 1) x‖ * Real.exp (|z.im| * |x|) := by ring
  have hdiff : ∀ x : ℝ, ∀ τ ∈ ball τ₀ 1,
      HasDerivAt (fun τ => complexWeight τ x * (I * x) ^ k * cexp (I * z * x))
        ((x : ℂ) ^ 2 * (complexWeight τ x * (I * x) ^ k * cexp (I * z * x))) τ := by
    intro x τ _
    have h1 : HasDerivAt (fun τ : ℂ => cexp (τ * (x : ℂ) ^ 2))
        (cexp (τ * (x : ℂ) ^ 2) * (x : ℂ) ^ 2) τ :=
      (hasDerivAt_mul_const ((x : ℂ) ^ 2)).cexp
    have h2 := ((h1.const_mul (riemannKernelReal x : ℂ)).mul_const ((I * x) ^ k)).mul_const
      (cexp (I * z * x))
    have hval : (x : ℂ) ^ 2 * (complexWeight τ x * (I * x) ^ k * cexp (I * z * x)) =
        (riemannKernelReal x : ℂ) * (cexp (τ * (x : ℂ) ^ 2) * (x : ℂ) ^ 2) * (I * x) ^ k *
          cexp (I * z * x) := by
      rw [complexWeight]
      ring
    rw [hval]
    exact h2
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℝ))
    (F := fun τ x => complexWeight τ x * (I * x) ^ k * cexp (I * z * x))
    (F' := fun τ x => (x : ℂ) ^ 2 * (complexWeight τ x * (I * x) ^ k * cexp (I * z * x)))
    (x₀ := τ₀)
    (bound := fun x => |x| ^ (k + 2) * ‖heatWeight (‖τ₀‖ + 1) x‖ * Real.exp (|z.im| * |x|))
    (ball_mem_nhds τ₀ one_pos)
    (Eventually.of_forall fun τ => (hcont τ).aestronglyMeasurable)
    (integrable_complexWeight_mul_pow_mul_exp τ₀ k z)
    hcont'.aestronglyMeasurable
    (Eventually.of_forall hbound)
    (integrable_pow_mul_heatWeight (by positivity) (k + 2) |z.im|)
    (Eventually.of_forall hdiff)
  have hval : ∫ x : ℝ, (x : ℂ) ^ 2 * (complexWeight τ₀ x * (I * x) ^ k * cexp (I * z * x)) =
      -expTransform (fun x => complexWeight τ₀ x * (I * x) ^ (k + 2)) z := by
    rw [expTransform, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show (x : ℂ) ^ 2 * (complexWeight τ₀ x * (I * x) ^ k * cexp (I * z * x)) =
      -(complexWeight τ₀ x * (I * x) ^ (k + 2) * cexp (I * z * x))
    rw [pow_add (I * (x : ℂ)) k 2, mul_pow I (x : ℂ) 2, I_sq]
    ring
  rw [← hval]
  exact key.2

/-- **The heat equation in complex time**, for every derivative in the place:
`∂_τ H_τ^{(k)}(z) = −H_τ^{(k+2)}(z)`. -/
theorem hasDerivAt_time_iteratedDeriv_complexHeat (k : ℕ) (τ₀ z : ℂ) :
    HasDerivAt (fun τ => iteratedDeriv k (complexHeat τ) z)
      (-iteratedDeriv (k + 2) (complexHeat τ₀) z) τ₀ := by
  simp only [iteratedDeriv_complexHeat]
  exact hasDerivAt_time_expTransform k τ₀ z

theorem hasDerivAt_time_complexHeat (τ₀ z : ℂ) :
    HasDerivAt (fun τ => complexHeat τ z) (-iteratedDeriv 2 (complexHeat τ₀) z) τ₀ := by
  have h := hasDerivAt_time_iteratedDeriv_complexHeat 0 τ₀ z
  simp only [iteratedDeriv_zero, zero_add] at h
  exact h

theorem deriv_time_complexHeat (τ z : ℂ) :
    deriv (fun τ => complexHeat τ z) τ = -iteratedDeriv 2 (complexHeat τ) z :=
  (hasDerivAt_time_complexHeat τ z).deriv

/-- At a fixed place the family is an entire function of the time. -/
theorem differentiable_time_complexHeat (z : ℂ) : Differentiable ℂ fun τ : ℂ => complexHeat τ z :=
  fun τ => (hasDerivAt_time_complexHeat τ z).differentiableAt

theorem iteratedDeriv_time_iteratedDeriv_complexHeat (n k : ℕ) (z : ℂ) :
    iteratedDeriv n (fun τ => iteratedDeriv k (complexHeat τ) z) =
      fun τ => (-1) ^ n * iteratedDeriv (k + 2 * n) (complexHeat τ) z := by
  induction n with
  | zero =>
    funext τ
    simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext τ
    rw [((hasDerivAt_time_iteratedDeriv_complexHeat (k + 2 * n) τ z).const_mul
      ((-1 : ℂ) ^ n)).deriv, show k + 2 * (n + 1) = k + 2 * n + 2 by ring]
    ring

/-- **Time derivatives are place derivatives**: `∂_τ^n H_τ(z) = (−1)^n H_τ^{(2n)}(z)`. -/
theorem iteratedDeriv_time_complexHeat (n : ℕ) (τ z : ℂ) :
    iteratedDeriv n (fun τ => complexHeat τ z) τ =
      (-1) ^ n * iteratedDeriv (2 * n) (complexHeat τ) z := by
  have h := congrFun (iteratedDeriv_time_iteratedDeriv_complexHeat n 0 z) τ
  simp only [iteratedDeriv_zero, zero_add] at h
  exact h

/-! ## The order in the time at a collision -/

/-- At a collision of order `m` the time derivatives of order `i` with `2i < m` vanish. -/
theorem IsCollision.iteratedDeriv_time_eq_zero (hc : IsCollision τ₀ z₀ m) {i : ℕ}
    (hi : 2 * i < m) : iteratedDeriv i (fun τ => complexHeat τ z₀) τ₀ = 0 := by
  rw [iteratedDeriv_time_complexHeat, hc.vanish (2 * i) hi, mul_zero]

/-- **Time order.** At a collision of order `2k` the family at the fixed place `z₀` vanishes to
order exactly `k` in the time. -/
theorem IsCollision.analyticOrderAt_time {k : ℕ} (hc : IsCollision τ₀ z₀ (2 * k)) :
    analyticOrderAt (fun τ => complexHeat τ z₀) τ₀ = (k : ℕ∞) := by
  rw [analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    ((differentiable_time_complexHeat z₀).analyticAt τ₀)]
  refine ⟨fun i hi => hc.iteratedDeriv_time_eq_zero (by omega), ?_⟩
  rw [iteratedDeriv_time_complexHeat]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hc.top_ne_zero

/-! ## The centre value -/

/-- The centre value `c(τ) = H_τ(0) = ∫ Φ(x) e^{τx²} dx`. -/
def centreValue (τ : ℂ) : ℂ := complexHeat τ 0

theorem differentiable_centreValue : Differentiable ℂ centreValue :=
  differentiable_time_complexHeat 0

theorem iteratedDeriv_centreValue (n : ℕ) (τ : ℂ) :
    iteratedDeriv n centreValue τ = (-1) ^ n * iteratedDeriv (2 * n) (complexHeat τ) 0 :=
  iteratedDeriv_time_complexHeat n τ 0

/-- The centre value has infinitely many zeros, none of them real. -/
theorem infinite_setOf_centreValue_eq_zero : {τ : ℂ | centreValue τ = 0}.Infinite :=
  infinite_centerTimes

theorem im_ne_zero_of_centreValue_eq_zero {τ : ℂ} (h : centreValue τ = 0) : τ.im ≠ 0 :=
  im_ne_zero_of_complexHeat_center_eq_zero h

/-- The odd derivatives of the even function `H_τ` vanish at the centre. -/
theorem iteratedDeriv_complexHeat_center_odd (τ : ℂ) {i : ℕ} (hi : Odd i) :
    iteratedDeriv i (complexHeat τ) 0 = 0 := by
  have h := iteratedDeriv_complexHeat_neg τ i 0
  rw [neg_zero, hi.neg_one_pow] at h
  linear_combination (1 / 2 : ℂ) * h

/-- **A zero of order `k` of the centre value is a collision of order `2k` at the centre.** -/
theorem isCollision_center_iff {k : ℕ} :
    IsCollision τ₀ 0 (2 * k) ↔ analyticOrderAt centreValue τ₀ = (k : ℕ∞) := by
  constructor
  · exact fun hc => hc.analyticOrderAt_time
  · intro h
    rw [analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
      (differentiable_centreValue.analyticAt τ₀)] at h
    obtain ⟨hlow, htop⟩ := h
    refine ⟨fun i hi => ?_, ?_⟩
    · obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
      · have h1 := hlow j (by omega)
        rw [iteratedDeriv_centreValue] at h1
        exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ (by norm_num))
      · exact iteratedDeriv_complexHeat_center_odd τ₀ (odd_two_mul_add_one j)
    · rw [iteratedDeriv_centreValue] at htop
      exact right_ne_zero_of_mul htop

/-- **The sign part of the monodromy.** At a zero of order `k` of the centre value, `2k` zeros
collide at the centre. The profile has `2k` roots, none of them `0`, so the sheets form `k` pairs,
and the turn of the time around `τ₀` carries the zero on each sheet to its negative. -/
theorem center_monodromy_of_analyticOrderAt {k : ℕ}
    (h : analyticOrderAt centreValue τ₀ = (k : ℕ∞)) :
    IsCollision τ₀ 0 (2 * k) ∧ (profileRoots (2 * k)).card = 2 * k ∧
      (∀ ρ : ℂ, heatModelFwd (2 * k) ρ = 0 → ρ ≠ 0) ∧
      ∀ ρ : ℂ, heatModelFwd (2 * k) ρ = 0 →
        ∀ᶠ s in 𝓝 0, -collisionZero τ₀ 0 (2 * k) ρ s = collisionZero τ₀ 0 (2 * k) ρ (-s) := by
  have hc := isCollision_center_iff.mpr h
  refine ⟨hc, card_profileRoots (2 * k), fun ρ hρ h0 => ?_, fun ρ hρ =>
    neg_collisionZero_center hc hρ⟩
  rw [h0] at hρ
  exact (Nat.not_odd_iff_even.mpr (even_two_mul k)) ((heatModelFwd_zero_eq_zero_iff _).mp hρ)

/-! ## The centre value over the coefficient field of the Jensen equations -/

/-- The Taylor coefficients of the centre value at `0` are the even moments of the kernel:
`c^{(n)}(0) = ∫ Φ(x) x^{2n} dx`. -/
theorem iteratedDeriv_centreValue_zero (n : ℕ) :
    iteratedDeriv n centreValue 0 = (FiniteFreeProbability.xiMoment (1 / 2) (2 * n) : ℂ) := by
  have h := integral_ofReal (μ := (volume : Measure ℝ)) (𝕜 := ℂ)
    (f := fun x : ℝ => riemannKernelReal x * x ^ (2 * n) * Real.exp ((1 / 2 - 1 / 2) * x))
  rw [iteratedDeriv_centreValue, iteratedDeriv_complexHeat, expTransform,
    FiniteFreeProbability.xiMoment, ← integral_const_mul]
  refine Eq.trans (integral_congr_ae (Eventually.of_forall fun x => ?_)) h
  show (-1 : ℂ) ^ n * (complexWeight 0 x * (I * x) ^ (2 * n) * cexp (I * 0 * x)) =
    ((riemannKernelReal x * x ^ (2 * n) * Real.exp ((1 / 2 - 1 / 2) * x) : ℝ) : ℂ)
  have e1 : complexWeight 0 x = (riemannKernelReal x : ℂ) := by
    rw [complexWeight, zero_mul, Complex.exp_zero, mul_one]
  have e2 : cexp (I * 0 * x) = 1 := by rw [mul_zero, zero_mul, Complex.exp_zero]
  have e3 : Real.exp ((1 / 2 - 1 / 2) * x) = 1 := by rw [sub_self, zero_mul, Real.exp_zero]
  have e4 : (I * (x : ℂ)) ^ (2 * n) = (-1) ^ n * (x : ℂ) ^ (2 * n) := by
    rw [mul_pow, pow_mul I 2 n, I_sq]
  have e5 : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  rw [e1, e2, e3, e4]
  push_cast
  linear_combination (riemannKernelReal x : ℂ) * (x : ℂ) ^ (2 * n) * e5

/-- **The equation of the sign branch points is defined over the coefficient field of the Jensen
equations**: the normalized Taylor coefficients of the centre value are the normalized even
moments. -/
theorem iteratedDeriv_centreValue_zero_div (n : ℕ) :
    iteratedDeriv n centreValue 0 / centreValue 0 = (normalizedEvenMoment n : ℂ) := by
  have h0 := iteratedDeriv_centreValue_zero 0
  rw [iteratedDeriv_zero, mul_zero] at h0
  rw [iteratedDeriv_centreValue_zero, h0, normalizedEvenMoment, Complex.ofReal_div]

/-- The centre value is the exponential generating function of the even moments. -/
theorem hasSum_centreValue (τ : ℂ) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ *
      (τ ^ n * (FiniteFreeProbability.xiMoment (1 / 2) (2 * n) : ℂ))) (centreValue τ) := by
  have h := Complex.hasSum_taylorSeries_of_entire differentiable_centreValue 0 τ
  simp only [sub_zero, smul_eq_mul, iteratedDeriv_centreValue_zero] at h
  exact h

/-! ## Singular points and folds of the heat cover -/

/-- **The singular points of the heat cover are the collisions of order at least three.** Both
partial derivatives vanish at a zero exactly there. -/
theorem deriv_eq_zero_and_deriv_time_eq_zero_iff (h : complexHeat τ₀ z₀ = 0) :
    (deriv (complexHeat τ₀) z₀ = 0 ∧ deriv (fun τ => complexHeat τ z₀) τ₀ = 0) ↔
      ∃ m, 3 ≤ m ∧ IsCollision τ₀ z₀ m := by
  obtain ⟨m, hm1, hc⟩ := exists_isCollision h
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨m, ?_, hc⟩
    by_contra hlt
    rw [deriv_time_complexHeat, neg_eq_zero] at h2
    have hm : m = 1 ∨ m = 2 := by omega
    rcases hm with rfl | rfl
    · exact hc.top_ne_zero (by rw [iteratedDeriv_one]; exact h1)
    · exact hc.top_ne_zero h2
  · rintro ⟨m', hm', hc'⟩
    refine ⟨?_, ?_⟩
    · rw [← iteratedDeriv_one]
      exact hc'.vanish 1 (by omega)
    · rw [deriv_time_complexHeat, hc'.vanish 2 (by omega), neg_zero]

/-- **A double collision is a fold of the heat cover.** Near a collision of order two the cover
contains the graph of an analytic function `T` of the place through the collision, and the time
`T` has a critical point there. -/
theorem exists_time_of_isCollision_two (hc : IsCollision τ₀ z₀ 2) :
    ∃ T : ℂ → ℂ, AnalyticAt ℂ T z₀ ∧ T z₀ = τ₀ ∧
      (∀ᶠ z in 𝓝 z₀, complexHeat (T z) z = 0) ∧ deriv T z₀ = 0 := by
  have hswap : AnalyticAt ℂ (fun p : ℂ × ℂ => (p.2, p.1)) (z₀, τ₀) :=
    analyticAt_snd.prod analyticAt_fst
  have hf : AnalyticAt ℂ (fun p : ℂ × ℂ => complexHeat p.2 p.1) (z₀, τ₀) :=
    AnalyticAt.comp (g := fun p : ℂ × ℂ => complexHeat p.1 p.2)
      (f := fun p : ℂ × ℂ => (p.2, p.1)) (x := (z₀, τ₀)) (analyticAt_complexHeat (τ₀, z₀)) hswap
  have hd := hf.differentiableAt.hasFDerivAt
  have h0 : complexHeat τ₀ z₀ = 0 := by
    have := hc.vanish 0 (by norm_num)
    rwa [iteratedDeriv_zero] at this
  -- the derivative in the time is `−H''(z₀) ≠ 0`
  have htime : (fderiv ℂ (fun p : ℂ × ℂ => complexHeat p.2 p.1) (z₀, τ₀)) (0, 1) =
      -iteratedDeriv 2 (complexHeat τ₀) z₀ := by
    have hline : HasDerivAt (fun τ : ℂ => (z₀, τ)) ((0 : ℂ), (1 : ℂ)) τ₀ :=
      (hasDerivAt_const τ₀ z₀).prodMk (hasDerivAt_id τ₀)
    have h1 := HasFDerivAt.comp_hasDerivAt (l := fun p : ℂ × ℂ => complexHeat p.2 p.1)
      (f := fun τ : ℂ => (z₀, τ)) τ₀ hd hline
    have h2 : HasDerivAt (fun τ : ℂ => complexHeat τ z₀)
        ((fderiv ℂ (fun p : ℂ × ℂ => complexHeat p.2 p.1) (z₀, τ₀)) (0, 1)) τ₀ := h1
    exact h2.unique (hasDerivAt_time_complexHeat τ₀ z₀)
  -- the derivative in the place is `H'(z₀) = 0`
  have hplace : (fderiv ℂ (fun p : ℂ × ℂ => complexHeat p.2 p.1) (z₀, τ₀)) (1, 0) = 0 := by
    have hline : HasDerivAt (fun z : ℂ => (z, τ₀)) ((1 : ℂ), (0 : ℂ)) z₀ :=
      (hasDerivAt_id z₀).prodMk (hasDerivAt_const z₀ τ₀)
    have h1 := HasFDerivAt.comp_hasDerivAt (l := fun p : ℂ × ℂ => complexHeat p.2 p.1)
      (f := fun z : ℂ => (z, τ₀)) z₀ hd hline
    have h2 : HasDerivAt (fun z : ℂ => complexHeat τ₀ z)
        ((fderiv ℂ (fun p : ℂ × ℂ => complexHeat p.2 p.1) (z₀, τ₀)) (1, 0)) z₀ := h1
    rw [h2.unique (differentiable_complexHeat τ₀ z₀).hasDerivAt, ← iteratedDeriv_one]
    exact hc.vanish 1 (by norm_num)
  have hne : (fderiv ℂ (fun p : ℂ × ℂ => complexHeat p.2 p.1) (z₀, τ₀)) (0, 1) ≠ 0 := by
    rw [htime]
    exact neg_ne_zero.mpr hc.top_ne_zero
  obtain ⟨T, hTan, hT0, hTzero⟩ := parametric_holo_implicit hf h0 hne
  refine ⟨T, hTan, hT0, hTzero, ?_⟩
  -- differentiate `H(T(z), z) = 0` at `z₀`
  have hcurve : HasDerivAt (fun z : ℂ => (z, T z)) ((1 : ℂ), deriv T z₀) z₀ :=
    (hasDerivAt_id z₀).prodMk hTan.differentiableAt.hasDerivAt
  have hd' : HasFDerivAt (fun p : ℂ × ℂ => complexHeat p.2 p.1)
      (fderiv ℂ (fun p : ℂ × ℂ => complexHeat p.2 p.1) (z₀, τ₀)) ((fun z : ℂ => (z, T z)) z₀) := by
    rw [show (fun z : ℂ => (z, T z)) z₀ = (z₀, τ₀) from Prod.ext rfl hT0]
    exact hd
  have h3' := HasFDerivAt.comp_hasDerivAt (l := fun p : ℂ × ℂ => complexHeat p.2 p.1)
    (f := fun z : ℂ => (z, T z)) z₀ hd' hcurve
  have h3 : HasDerivAt (fun z : ℂ => complexHeat (T z) z)
      ((fderiv ℂ (fun p : ℂ × ℂ => complexHeat p.2 p.1) (z₀, τ₀)) (1, deriv T z₀)) z₀ := h3'
  have h4 : HasDerivAt (fun z : ℂ => complexHeat (T z) z) 0 z₀ :=
    (hasDerivAt_const z₀ (0 : ℂ)).congr_of_eventuallyEq hTzero
  have h5 := h3.unique h4
  have hsplit : ((1 : ℂ), deriv T z₀) = ((1 : ℂ), (0 : ℂ)) + deriv T z₀ • ((0 : ℂ), (1 : ℂ)) := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [hsplit, map_add, map_smul, hplace, zero_add, smul_eq_mul] at h5
  exact (mul_eq_zero.mp h5).resolve_right hne

/-! ## The Riemann hypothesis in the language of the cover -/

/-- **The Riemann hypothesis says that no branch time of the heat cover is real and positive.** -/
theorem riemannHypothesis_iff_forall_pos_not_mem_branchTimes :
    RiemannHypothesis ↔ ∀ t : ℝ, 0 < t → (t : ℂ) ∉ branchTimes := by
  have hfun : ∀ t : ℝ, complexHeat (t : ℂ) = riemannHeat t := fun t =>
    funext (complexHeat_ofReal t)
  rw [riemannHypothesis_iff_forall_zeros_simple]
  constructor
  · rintro h t ht ⟨⟨τ, z⟩, ⟨hz, hd⟩, hτ⟩
    have hτ' : τ = (t : ℂ) := hτ
    subst hτ'
    rw [hfun] at hz hd
    exact h t ht z hz hd
  · intro h t ht z hz hd
    refine h t ht ⟨((t : ℂ), z), ⟨?_, ?_⟩, rfl⟩
    · show complexHeat (t : ℂ) z = 0
      rw [hfun]
      exact hz
    · show deriv (complexHeat (t : ℂ)) z = 0
      rw [hfun]
      exact hd

end

end GaloisForLFunctions.GaloisTheoryOfZeros
