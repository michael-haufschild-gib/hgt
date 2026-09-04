import GaloisForLFunctions.HTGeometry.StrelitzMaximumModulusSet
import GaloisForLFunctions.HTGeometry.ThreeCircles

/-!
# The exact circle maximum norm

The maximum modulus on a centered circle is represented as the supremum of the continuous angular
profile.  For an entire coefficient sum the supremum is finite and attained on every positive
circle.  This gives a choice-free scalar maximum function and identifies it exactly with the
previous pointwise maximum-locus predicate.
-/

open Set Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Maximum norm of the coefficient entire function on the centered circle of real radius `r`. -/
def coeffCircleMaximumNorm (a : ℕ → ℂ) (r : ℝ) : ℝ :=
  sSup (Set.range fun θ : ℝ => ‖coeffFun a (circleMap 0 r θ)‖)

/-- The angular norm profile of an entire coefficient sum is bounded above. -/
theorem bddAbove_range_norm_coeffFun_circleMap
    {a : ℕ → ℂ} (ha : EntireCoeffs a) (r : ℝ) :
    BddAbove (Set.range fun θ : ℝ => ‖coeffFun a (circleMap 0 r θ)‖) := by
  by_cases hr : r = 0
  · subst r
    refine ⟨‖coeffFun a 0‖, ?_⟩
    rintro y ⟨θ, rfl⟩
    simp [circleMap]
  · refine ⟨coeffSum a |r|, ?_⟩
    rintro y ⟨θ, rfl⟩
    have hnorm : 0 < ‖circleMap 0 r θ‖ := by
      rw [norm_circleMap_zero]
      exact abs_pos.mpr hr
    simpa [norm_circleMap_zero] using norm_coeffFun_le ha hnorm

/-- Every value on a centered circle is bounded by its exact circle maximum norm. -/
theorem norm_coeffFun_circleMap_le_coeffCircleMaximumNorm
    {a : ℕ → ℂ} (ha : EntireCoeffs a) (r θ : ℝ) :
    ‖coeffFun a (circleMap 0 r θ)‖ ≤ coeffCircleMaximumNorm a r := by
  exact le_csSup (bddAbove_range_norm_coeffFun_circleMap ha r) ⟨θ, rfl⟩

/-- Every point on a positive centered circle is bounded by its exact circle maximum norm. -/
theorem norm_coeffFun_le_coeffCircleMaximumNorm_of_norm_eq
    {a : ℕ → ℂ} (ha : EntireCoeffs a) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : ‖z‖ = r) :
    ‖coeffFun a z‖ ≤ coeffCircleMaximumNorm a r := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; exact ne_of_gt hr)
  let θ : ℝ := Complex.arg z
  have hcircle : circleMap 0 r θ = z := by
    rw [circleMap, zero_add, ← hz]
    simpa [θ, mul_comm] using Complex.norm_mul_exp_arg_mul_I z
  rw [← hcircle]
  exact norm_coeffFun_circleMap_le_coeffCircleMaximumNorm ha r θ

/-- The exact circle maximum norm is attained on every positive circle. -/
theorem exists_circleMap_norm_eq_coeffCircleMaximumNorm
    {a : ℕ → ℂ} (ha : EntireCoeffs a) {r : ℝ} (hr : 0 < r) :
    ∃ θ : ℝ, ‖coeffFun a (circleMap 0 r θ)‖ = coeffCircleMaximumNorm a r := by
  obtain ⟨z, hz, hmax⟩ := exists_max_on_circle ha hr
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; exact ne_of_gt hr)
  let θ : ℝ := Complex.arg z
  have hcircle : circleMap 0 r θ = z := by
    rw [circleMap, zero_add, ← hz]
    simpa [θ, mul_comm] using Complex.norm_mul_exp_arg_mul_I z
  refine ⟨θ, ?_⟩
  apply le_antisymm
  · exact norm_coeffFun_circleMap_le_coeffCircleMaximumNorm ha r θ
  · apply csSup_le
    · exact Set.range_nonempty _
    · rintro y ⟨φ, rfl⟩
      simpa [hcircle] using hmax φ

/-- The maximum term is bounded by the exact circle maximum norm. -/
theorem maxTerm_le_coeffCircleMaximumNorm
    {a : ℕ → ℂ} (ha : EntireCoeffs a) {r : ℝ} (hr : 0 < r) :
    maxTerm a r ≤ coeffCircleMaximumNorm a r := by
  obtain ⟨θ, hθ⟩ :=
    exists_circleMap_norm_eq_coeffCircleMaximumNorm ha hr
  have hz : ‖circleMap 0 r θ‖ = r := by
    rw [norm_circleMap_zero, abs_of_pos hr]
  rw [← hθ]
  apply maxTerm_le_norm_of_max_on_circle ha hr hz
  intro φ
  rw [hθ]
  exact norm_coeffFun_circleMap_le_coeffCircleMaximumNorm ha r φ

/-- A nonzero coefficient makes every positive circle maximum strictly positive. -/
theorem coeffCircleMaximumNorm_pos
    {a : ℕ → ℂ} (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {r : ℝ} (hr : 0 < r) :
    0 < coeffCircleMaximumNorm a r := by
  obtain ⟨_, _, hμpos⟩ := exists_maxTerm_eq ha hr hn₀
  exact hμpos.trans_le (maxTerm_le_coeffCircleMaximumNorm ha hr)

/-- A nonzero point lies in the circle maximum locus exactly when its value realizes the exact
circle maximum norm. -/
theorem mem_circleMaximumSet_iff_norm_eq_coeffCircleMaximumNorm
    {a : ℕ → ℂ} (ha : EntireCoeffs a) {z : ℂ} (hz : 0 < ‖z‖) :
    z ∈ circleMaximumSet (coeffFun a) ↔
      ‖coeffFun a z‖ = coeffCircleMaximumNorm a ‖z‖ := by
  let θ : ℝ := Complex.arg z
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hz)
  have hcircle : circleMap 0 ‖z‖ θ = z := by
    rw [circleMap, zero_add]
    simpa [θ, mul_comm] using Complex.norm_mul_exp_arg_mul_I z
  constructor
  · intro hmax
    apply le_antisymm
    · calc
        ‖coeffFun a z‖ = ‖coeffFun a (circleMap 0 ‖z‖ θ)‖ := by rw [hcircle]
        _ ≤ coeffCircleMaximumNorm a ‖z‖ :=
          norm_coeffFun_circleMap_le_coeffCircleMaximumNorm ha ‖z‖ θ
    · apply csSup_le
      · exact Set.range_nonempty _
      · rintro y ⟨φ, rfl⟩
        apply hmax
        rw [norm_circleMap_zero, abs_of_pos hz]
  · intro heq w hw
    let φ : ℝ := Complex.arg w
    have hw0 : w ≠ 0 := by
      intro h
      subst w
      rw [norm_zero] at hw
      linarith
    have hcirclew : circleMap 0 ‖z‖ φ = w := by
      rw [circleMap, zero_add, ← hw]
      simpa [φ, mul_comm] using Complex.norm_mul_exp_arg_mul_I w
    rw [← hcirclew, heq]
    exact norm_coeffFun_circleMap_le_coeffCircleMaximumNorm ha ‖z‖ φ

/-- Two points on the same radial ray of the centered circle parametrization are separated by the
absolute difference of their real radii. -/
theorem dist_circleMap_zero_same_angle (r s θ : ℝ) :
    dist (circleMap 0 r θ) (circleMap 0 s θ) = |r - s| := by
  rw [dist_eq, circleMap, circleMap, zero_add, zero_add, ← sub_mul, norm_mul,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  norm_num

/-- The exact circle maximum norm is continuous at every positive radius. -/
theorem continuousAt_coeffCircleMaximumNorm
    {a : ℕ → ℂ} (ha : EntireCoeffs a) {r0 : ℝ} (hr0 : 0 < r0) :
    ContinuousAt (coeffCircleMaximumNorm a) r0 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  let R := r0 + 1
  have huc : UniformContinuousOn (coeffFun a) (Metric.closedBall 0 R) :=
    (isCompact_closedBall (0 : ℂ) R).uniformContinuousOn_of_continuous
      (differentiable_coeffFun ha).continuous.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδmain⟩ := huc ε hε
  let δ0 := min (r0 / 2) (min 1 δ)
  have hδ0 : 0 < δ0 := by
    dsimp [δ0]
    positivity
  refine ⟨δ0, hδ0, ?_⟩
  intro r hrr0
  have habs : |r - r0| < δ0 := by simpa [Real.dist_eq] using hrr0
  have hrpos : 0 < r := by
    have hδ0le : δ0 ≤ r0 / 2 := min_le_left _ _
    have hlow : -(r0 / 2) < r - r0 :=
      (neg_le_neg hδ0le).trans_lt (abs_lt.mp habs).1
    linarith
  have hrR : r ≤ R := by
    have hupp : r - r0 < 1 :=
      (le_abs_self (r - r0)).trans_lt
        (habs.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    dsimp [R]
    linarith
  have hr0R : r0 ≤ R := by
    dsimp [R]
    linarith
  obtain ⟨θr, hθr⟩ :=
    exists_circleMap_norm_eq_coeffCircleMaximumNorm ha hrpos
  obtain ⟨θ0, hθ0⟩ :=
    exists_circleMap_norm_eq_coeffCircleMaximumNorm ha hr0
  have hδdist : |r - r0| < δ :=
    habs.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hpoint (θ : ℝ) (s : ℝ) (hs : 0 ≤ s) (hsR : s ≤ R) :
      circleMap 0 s θ ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hs]
    exact hsR
  have hfun (θ : ℝ) :
      dist (coeffFun a (circleMap 0 r θ))
        (coeffFun a (circleMap 0 r0 θ)) < ε := by
    apply hδmain
    · exact hpoint θ r hrpos.le hrR
    · exact hpoint θ r0 hr0.le hr0R
    · rw [dist_circleMap_zero_same_angle]
      exact hδdist
  have hnorm (θ : ℝ) :
      |‖coeffFun a (circleMap 0 r θ)‖ -
        ‖coeffFun a (circleMap 0 r0 θ)‖| < ε := by
    exact (abs_norm_sub_norm_le _ _).trans_lt (by simpa [dist_eq] using hfun θ)
  have hupper : coeffCircleMaximumNorm a r -
      coeffCircleMaximumNorm a r0 < ε := by
    have hle := norm_coeffFun_circleMap_le_coeffCircleMaximumNorm ha r0 θr
    have hlt := (abs_lt.mp (hnorm θr)).2
    rw [hθr] at hlt
    linarith
  have hlower : -(ε) < coeffCircleMaximumNorm a r -
      coeffCircleMaximumNorm a r0 := by
    have hle := norm_coeffFun_circleMap_le_coeffCircleMaximumNorm ha r θ0
    have hlt := (abs_lt.mp (hnorm θ0)).1
    rw [hθ0] at hlt
    linarith
  simpa [Real.dist_eq] using abs_lt.mpr ⟨hlower, hupper⟩

/-- Logarithm of the exact maximum modulus in logarithmic radius. -/
def strelitzLogMaximum (a : ℕ → ℂ) (x : ℝ) : ℝ :=
  Real.log (coeffCircleMaximumNorm a (Real.exp x))

/-- The logarithmic maximum modulus is continuous when the entire function is nonzero. -/
theorem continuousAt_strelitzLogMaximum
    {a : ℕ → ℂ} (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (x : ℝ) : ContinuousAt (strelitzLogMaximum a) x := by
  unfold strelitzLogMaximum
  exact ((continuousAt_coeffCircleMaximumNorm ha (Real.exp_pos x)).comp
      Real.continuous_exp.continuousAt).log
    (ne_of_gt (coeffCircleMaximumNorm_pos ha hn₀ (Real.exp_pos x)))

/-- Three-circles interpolation for the logarithmic maximum modulus. -/
theorem strelitzLogMaximum_le_interpolation
    {a : ℕ → ℂ} (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {x1 x x3 : ℝ} (h13 : x1 < x3) (h1x : x1 ≤ x) (hx3 : x ≤ x3) :
    strelitzLogMaximum a x ≤
      (1 - (x - x1) / (x3 - x1)) * strelitzLogMaximum a x1 +
        ((x - x1) / (x3 - x1)) * strelitzLogMaximum a x3 := by
  obtain ⟨θ, hθ⟩ := exists_circleMap_norm_eq_coeffCircleMaximumNorm
    ha (Real.exp_pos x)
  have hnorm : ‖circleMap 0 (Real.exp x) θ‖ = Real.exp x := by
    rw [norm_circleMap_zero, abs_of_pos (Real.exp_pos x)]
  have hbound := norm_le_of_three_circles
    (f := coeffFun a) (r₁ := Real.exp x1) (r₃ := Real.exp x3)
    (Real.exp_pos x1) (Real.exp_lt_exp.mpr h13)
    (fun z _ _ => (differentiable_coeffFun ha) z)
    (M₁ := coeffCircleMaximumNorm a (Real.exp x1))
    (M₃ := coeffCircleMaximumNorm a (Real.exp x3))
    (fun z hz => norm_coeffFun_le_coeffCircleMaximumNorm_of_norm_eq
      ha (Real.exp_pos x1) hz)
    (fun z hz => norm_coeffFun_le_coeffCircleMaximumNorm_of_norm_eq
      ha (Real.exp_pos x3) hz)
    (z := circleMap 0 (Real.exp x) θ)
    (by rw [hnorm]; exact Real.exp_le_exp.mpr h1x)
    (by rw [hnorm]; exact Real.exp_le_exp.mpr hx3)
  rw [hθ, hnorm, Real.log_exp, Real.log_exp, Real.log_exp] at hbound
  have hM1 : 0 < coeffCircleMaximumNorm a (Real.exp x1) :=
    coeffCircleMaximumNorm_pos ha hn₀ (Real.exp_pos x1)
  have hM3 : 0 < coeffCircleMaximumNorm a (Real.exp x3) :=
    coeffCircleMaximumNorm_pos ha hn₀ (Real.exp_pos x3)
  have hlog := Real.log_le_log
    (coeffCircleMaximumNorm_pos ha hn₀ (Real.exp_pos x)) hbound
  rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hM1 _))
      (ne_of_gt (Real.rpow_pos_of_pos hM3 _)),
    Real.log_rpow hM1, Real.log_rpow hM3] at hlog
  simpa [strelitzLogMaximum, mul_comm] using hlog

/-- The logarithmic maximum modulus is convex on the full logarithmic-radius line. -/
theorem convexOn_strelitzLogMaximum
    {a : ℕ → ℂ} (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    ConvexOn ℝ Set.univ (strelitzLogMaximum a) := by
  rw [convexOn_iff_forall_pos]
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ α β hα hβ hab
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have hm : α • x + β • y = x + β * (y - x) := by
      simp only [smul_eq_mul]
      calc
        α * x + β * y = (α + β) * x + β * (y - x) := by ring
        _ = x + β * (y - x) := by rw [hab, one_mul]
    have hβle : β ≤ 1 := by linarith
    have hxm : x ≤ α • x + β • y := by
      rw [hm]
      exact le_add_of_nonneg_right (mul_nonneg hβ.le (sub_nonneg.mpr hxy.le))
    have hmy : α • x + β • y ≤ y := by
      rw [hm]
      have hmul := mul_le_mul_of_nonneg_right hβle (sub_nonneg.mpr hxy.le)
      linarith
    have hinterp := strelitzLogMaximum_le_interpolation ha hn₀ hxy hxm hmy
    have ht : ((α • x + β • y) - x) / (y - x) = β := by
      rw [hm]
      field_simp [ne_of_gt (sub_pos.mpr hxy)]
      ring
    rw [ht] at hinterp
    have haeq : 1 - β = α := by linarith
    simpa [haeq, smul_eq_mul] using hinterp
  · subst y
    have hpoint : α • x + β • x = x := by
      simp only [smul_eq_mul]
      rw [← add_mul, hab, one_mul]
    rw [hpoint]
    apply le_of_eq
    simp only [smul_eq_mul]
    calc
      strelitzLogMaximum a x =
          (α + β) * strelitzLogMaximum a x := by rw [hab, one_mul]
      _ = α * strelitzLogMaximum a x +
          β * strelitzLogMaximum a x := by ring
  · have hm : α • x + β • y = y + α * (x - y) := by
      simp only [smul_eq_mul]
      calc
        α * x + β * y = (α + β) * y + α * (x - y) := by ring
        _ = y + α * (x - y) := by rw [hab, one_mul]
    have hαle : α ≤ 1 := by linarith
    have hym : y ≤ α • x + β • y := by
      rw [hm]
      exact le_add_of_nonneg_right (mul_nonneg hα.le (sub_nonneg.mpr hxy.le))
    have hmx : α • x + β • y ≤ x := by
      rw [hm]
      have hmul := mul_le_mul_of_nonneg_right hαle (sub_nonneg.mpr hxy.le)
      linarith
    have hinterp := strelitzLogMaximum_le_interpolation ha hn₀ hxy hym hmx
    have ht : ((α • x + β • y) - y) / (x - y) = α := by
      rw [hm]
      field_simp [ne_of_gt (sub_pos.mpr hxy)]
      ring
    rw [ht] at hinterp
    have hbeq : 1 - α = β := by linarith
    simpa [hbeq, smul_eq_mul, add_comm] using hinterp

end

end GaloisForLFunctions.HTGeometry
