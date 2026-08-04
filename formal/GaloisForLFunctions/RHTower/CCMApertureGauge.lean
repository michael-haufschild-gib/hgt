import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The invisible aperture gauge of restricted summation

The CCM summation map is

```text
E(f)(u) = sqrt u * sum_(n>=1) f(nu),
```

restricted to the aperture `[lambda^(-1), lambda]`.  Even smooth zero-integral corrections supported
inside `(-lambda^(-1), lambda^(-1))` are invisible to the restriction: on the aperture the smallest
sampling point is `u >= lambda^(-1)`, which already lies outside their support.  They therefore form a
gauge group `K_lambda` acting trivially on the finite-aperture image, and the central value `f(0)` is
not an invariant of that image.

* `summationMap`, `ApertureCorrector` — the map and the gauge class `K_lambda`.
* `summationMap_eq_zero_of_vanishing`, `apertureCorrector_mem_kernel` — `K_lambda ⊆ ker(R_lambda E)`.
* `exists_centralCorrector`, `exists_apertureCorrector_apply_zero` — surjectivity of `ev_0` on
  `K_lambda`: an even smooth corrector of arbitrarily small support with prescribed central value and
  zero integral exists.
* `exists_zero_center_representative` — every even zero-integral source has a representative with
  `f(0) = 0` and the same finite-aperture image.

Two points about the formalisation.  First, no summability hypothesis is needed anywhere: the
correction annihilates *every* term of the series on the aperture, so the two `tsum`s are equal
termwise, whether or not either converges.  Second, only the support condition of `K_lambda` enters the
kernel statement; the zero-integral condition is what keeps the *global* constraint
`Fourier(f)(0) = 0` intact while the central value is being moved.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set

/-- The CCM summation map `E(f)(u) = sqrt u * sum_(n>=1) f(nu)`. -/
def summationMap (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  Real.sqrt u * ∑' n : ℕ, f (((n : ℝ) + 1) * u)

/-- The aperture gauge class `K_lambda`: even smooth functions vanishing outside
`(-lambda^(-1), lambda^(-1))` and of total integral zero. -/
structure ApertureCorrector (lam : ℝ) (b : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b
  isEven : ∀ x, b (-x) = b x
  vanishing : ∀ x : ℝ, lam⁻¹ ≤ |x| → b x = 0
  integral : (∫ x, b x) = 0

/-! ## The kernel statement -/

/-- **Part 1.**  A function vanishing outside the inner aperture is annihilated by the summation map
at every aperture point, because the very first sampling point `u` is already outside its support. -/
theorem summationMap_eq_zero_of_vanishing {lam : ℝ} (hlam : 0 < lam) {b : ℝ → ℝ}
    (hb : ∀ x : ℝ, lam⁻¹ ≤ |x| → b x = 0) {u : ℝ} (hu : lam⁻¹ ≤ u) :
    summationMap b u = 0 := by
  have hupos : 0 < u := lt_of_lt_of_le (by positivity) hu
  have hterm : ∀ n : ℕ, b (((n : ℝ) + 1) * u) = 0 := by
    intro n
    refine hb _ ?_
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  rw [summationMap]
  simp [hterm]

/-- **Part 1, in the card's form.**  `K_lambda` is contained in the kernel of the restricted
summation map. -/
theorem apertureCorrector_mem_kernel {lam : ℝ} (hlam : 0 < lam) {b : ℝ → ℝ}
    (hb : ApertureCorrector lam b) :
    ∀ u ∈ Icc lam⁻¹ lam, summationMap b u = 0 :=
  fun _ hu => summationMap_eq_zero_of_vanishing hlam hb.vanishing hu.1

/-- The correction is invisible to the restricted map, termwise.  No summability is used. -/
theorem summationMap_sub_of_vanishing {lam : ℝ} (hlam : 0 < lam) {f b : ℝ → ℝ} (c : ℝ)
    (hb : ∀ x : ℝ, lam⁻¹ ≤ |x| → b x = 0) {u : ℝ} (hu : lam⁻¹ ≤ u) :
    summationMap (fun x => f x - c * b x) u = summationMap f u := by
  have hupos : 0 < u := lt_of_lt_of_le (by positivity) hu
  rw [summationMap, summationMap]
  congr 1
  refine tsum_congr fun n => ?_
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hz : b (((n : ℝ) + 1) * u) = 0 := by
    refine hb _ ?_
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  rw [hz]
  ring

/-! ## The central corrector -/

/-- **The corrector.**  For every `a > 0` there is an even smooth function supported in `(-a, a)` with
central value one and total integral zero.

The construction is `b = (1 - c x²) φ(x)` for a bump `φ` centred at the origin: multiplying by `x²`
produces a second even bump that vanishes at the origin, which is exactly what the card's `psi` is used
for, and avoids having to place a second bump off centre and symmetrise it. -/
theorem exists_centralCorrector {a : ℝ} (ha : 0 < a) :
    ∃ b : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b ∧ (∀ x, b (-x) = b x) ∧
      (∀ x : ℝ, a ≤ |x| → b x = 0) ∧ HasCompactSupport b ∧ b 0 = 1 ∧ (∫ x, b x) = 0 := by
  set φ : ContDiffBump (0 : ℝ) := ⟨a / 2, a, by positivity, by linarith⟩ with hφdef
  have hφvanish : ∀ x : ℝ, a ≤ |x| → φ x = 0 := by
    intro x hx
    have hns : x ∉ Function.support (φ : ℝ → ℝ) := by
      rw [φ.support_eq]
      simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt]
      exact hx
    simpa [Function.mem_support] using hns
  have hφ0 : φ 0 = 1 := φ.one_of_mem_closedBall (by simp [Metric.mem_closedBall]; positivity)
  have hφcont : Continuous (φ : ℝ → ℝ) := φ.continuous
  have hφsupp : HasCompactSupport (φ : ℝ → ℝ) := φ.hasCompactSupport
  have hφint : Integrable (φ : ℝ → ℝ) := φ.integrable
  -- the second, centrally vanishing bump
  set ψ : ℝ → ℝ := fun x => x ^ 2 * φ x with hψdef
  have hψcont : Continuous ψ := by
    rw [hψdef]
    exact (continuous_pow 2).mul hφcont
  have hψvanish : ∀ x : ℝ, a ≤ |x| → ψ x = 0 := by
    intro x hx
    show x ^ 2 * (φ : ℝ → ℝ) x = 0
    rw [hφvanish x hx, mul_zero]
  have hψeven : ∀ x : ℝ, ψ (-x) = ψ x := by
    intro x
    show (-x) ^ 2 * (φ : ℝ → ℝ) (-x) = x ^ 2 * (φ : ℝ → ℝ) x
    rw [φ.neg]
    ring
  have hψ0 : ψ 0 = 0 := by
    show (0 : ℝ) ^ 2 * (φ : ℝ → ℝ) 0 = 0
    norm_num
  have hψsupp : HasCompactSupport ψ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) a) ?_
    intro x hx
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
    exact hψvanish x hx.le
  have hψint : Integrable ψ := hψcont.integrable_of_hasCompactSupport hψsupp
  have hψnn : 0 ≤ ψ := by
    intro x
    show (0 : ℝ) ≤ x ^ 2 * (φ : ℝ → ℝ) x
    exact mul_nonneg (sq_nonneg x) φ.nonneg
  have hψpos : 0 < ∫ x, ψ x := by
    rw [integral_pos_iff_support_of_nonneg hψnn hψint]
    have hsub : Ioo (0 : ℝ) a ⊆ Function.support ψ := by
      intro x hx
      have hball : x ∈ Metric.ball (0 : ℝ) a := by
        simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
        rw [abs_of_pos hx.1]
        exact hx.2
      have hpos : 0 < φ x := φ.pos_of_mem_ball hball
      refine Function.mem_support.mpr ?_
      show x ^ 2 * (φ : ℝ → ℝ) x ≠ 0
      have hx2 : (0 : ℝ) < x ^ 2 := pow_pos hx.1 2
      exact ne_of_gt (mul_pos hx2 hpos)
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [Real.volume_Ioo]
    simp only [sub_zero]
    exact ENNReal.ofReal_pos.mpr ha
  set c : ℝ := (∫ x, (φ : ℝ → ℝ) x) / ∫ x, ψ x with hcdef
  refine ⟨fun x => φ x - c * ψ x, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact φ.contDiff.sub (contDiff_const.mul (((contDiff_id (𝕜 := ℝ)).pow 2).mul φ.contDiff))
  · intro x
    show (φ : ℝ → ℝ) (-x) - c * ψ (-x) = (φ : ℝ → ℝ) x - c * ψ x
    rw [φ.neg, hψeven]
  · intro x hx
    show (φ : ℝ → ℝ) x - c * ψ x = 0
    rw [hφvanish x hx, hψvanish x hx]
    ring
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) a) ?_
    intro x hx
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
    show (φ : ℝ → ℝ) x - c * ψ x = 0
    rw [hφvanish x hx.le, hψvanish x hx.le]
    ring
  · show (φ : ℝ → ℝ) 0 - c * ψ 0 = 1
    rw [hφ0, hψ0]
    ring
  · show (∫ x, ((φ : ℝ → ℝ) x - c * ψ x)) = 0
    rw [integral_sub hφint (hψint.const_mul c), integral_const_mul, hcdef,
      div_mul_cancel₀ _ hψpos.ne', sub_self]

/-! ## Surjectivity of the central evaluation -/

/-- **Part 2.**  The central evaluation `ev_0 : K_lambda → ℝ` is surjective. -/
theorem exists_apertureCorrector_apply_zero {lam : ℝ} (hlam : 0 < lam) (t : ℝ) :
    ∃ b : ℝ → ℝ, ApertureCorrector lam b ∧ HasCompactSupport b ∧ b 0 = t := by
  obtain ⟨b, hsmooth, heven, hvanish, hcsupp, hb0, hbint⟩ :=
    exists_centralCorrector (a := lam⁻¹) (by positivity)
  refine ⟨fun x => t * b x, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact contDiff_const.mul hsmooth
  · intro x; rw [heven]
  · intro x hx; rw [hvanish x hx, mul_zero]
  · rw [integral_const_mul, hbint, mul_zero]
  · exact hcsupp.mul_left
  · show t * b 0 = t
    rw [hb0, mul_one]

/-! ## The zero-centre representative -/

/-- **Part 3.**  Every even zero-integral source has a representative with vanishing central value,
differing from it by a smooth compactly supported function, with the same restricted summation image.

The representative keeps the endpoint regularity of `f`, since it differs from `f` by a function that
is smooth everywhere; this is the card's "exact limitation": the correction repairs the two scalar
conditions but does not put the source in the Schwartz space. -/
theorem exists_zero_center_representative {lam : ℝ} (hlam : 0 < lam) {f : ℝ → ℝ}
    (hfi : Integrable f) (hf0 : (∫ x, f x) = 0) (hfeven : ∀ x, f (-x) = f x) :
    ∃ b : ℝ → ℝ, ApertureCorrector lam b ∧ HasCompactSupport b ∧
      (fun x => f x - f 0 * b x) 0 = 0 ∧
      (∫ x, (f x - f 0 * b x)) = 0 ∧
      (∀ x, (f (-x) - f 0 * b (-x)) = f x - f 0 * b x) ∧
      ∀ u ∈ Icc lam⁻¹ lam,
        summationMap (fun x => f x - f 0 * b x) u = summationMap f u := by
  obtain ⟨b, hsmooth, heven, hvanish, hcsupp, hb0, hbint⟩ :=
    exists_centralCorrector (a := lam⁻¹) (by positivity)
  have hbi : Integrable b := by
    refine Continuous.integrable_of_hasCompactSupport ?_ hcsupp
    exact hsmooth.continuous
  refine ⟨b, ⟨hsmooth, heven, hvanish, hbint⟩, hcsupp, ?_, ?_, ?_, ?_⟩
  · show f 0 - f 0 * b 0 = 0
    rw [hb0, mul_one, sub_self]
  · show (∫ x, (f x - f 0 * b x)) = 0
    rw [integral_sub hfi (hbi.const_mul (f 0)), integral_const_mul, hf0, hbint, mul_zero,
      sub_zero]
  · intro x
    rw [hfeven, heven]
  · intro u hu
    exact summationMap_sub_of_vanishing hlam (f 0) hvanish hu.1

/-! ## Gauge invariance of the finite-aperture image -/

/-- **The image is a function of the gauge class.**  Two sources differing by an element of
`K_lambda` have the same restricted summation image.  This is the sense in which the gauge is
invisible: `R_lambda E` factors through the quotient by `K_lambda`. -/
theorem summationMap_eq_of_sub_apertureCorrector {lam : ℝ} (hlam : 0 < lam) {f g : ℝ → ℝ}
    (h : ApertureCorrector lam fun x => f x - g x) :
    ∀ u ∈ Icc lam⁻¹ lam, summationMap f u = summationMap g u := by
  intro u hu
  have hrw : g = fun x => f x - 1 * (f x - g x) := by
    funext x
    ring
  rw [hrw]
  exact (summationMap_sub_of_vanishing hlam 1 h.vanishing hu.1).symm

end GaloisForLFunctions.RHTower

end
