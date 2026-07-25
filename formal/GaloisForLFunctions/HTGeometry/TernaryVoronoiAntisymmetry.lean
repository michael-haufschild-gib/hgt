/-
The resonant kernel of a double Voronoi expansion, and its antisymmetry.

Expanding a shift-average of divisor-correlation errors by Voronoi summation twice produces a double
sum over the two dual variables.  One factor enters as a sine (it comes from differencing a cosine
along the shift), the other as a cosine (it is the Voronoi kernel), so the product-to-sum identity
splits the double sum into a non-resonant part carrying the phase `φ m + φ l` and a resonant part
carrying `φ m - φ l`.

After the substitution that flattens the `k`-th-root phase — `y = u^k`, under which the weight
`y^{-(k-1)/k} dy` becomes `k du` — the resonant integral is elementary:

  `∫_1^X sin(c u) du = (cos c - cos (cX)) / c =: resonantKernel c X`.

This kernel is an **odd** function of `c`.  The accompanying weight is symmetric in the two dual
variables, and `c = φ m - φ l` is antisymmetric, so the whole resonant double sum vanishes
identically.  The size of the shift-average is therefore not governed by the resonant term at all,
but by whatever breaks the symmetry: the truncations of the two dual ranges, the curvature term
dropped when the shift-difference is linearised, and the range in which the linearisation is invalid.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace HTGeometry

open Real intervalIntegral

/-- The resonant kernel: the exact value of `∫_1^X sin(cu) du`. -/
noncomputable def resonantKernel (c X : ℝ) : ℝ := (Real.cos c - Real.cos (c * X)) / c

/-- **The resonant integral is elementary.**  After flattening the `k`-th-root phase the integral
that carries the resonance is a plain sine integral. -/
theorem integral_sin_mul_eq_resonantKernel {c : ℝ} (hc : c ≠ 0) (X : ℝ) :
    (∫ u in (1 : ℝ)..X, Real.sin (c * u)) = resonantKernel c X := by
  rw [intervalIntegral.integral_comp_mul_left (fun u => Real.sin u) hc]
  rw [integral_sin]
  unfold resonantKernel
  rw [smul_eq_mul, mul_one]
  field_simp

/-- **Product-to-sum: the split into non-resonant and resonant parts.**  The sine comes from
differencing along the shift, the cosine from the Voronoi kernel. -/
theorem sin_mul_cos_split (A B : ℝ) :
    Real.sin A * Real.cos B = (Real.sin (A + B) + Real.sin (A - B)) / 2 := by
  have h1 := Real.sin_add A B
  have h2 := Real.sin_sub A B
  linarith

/-- **The resonant kernel is odd.** -/
theorem resonantKernel_neg (c X : ℝ) : resonantKernel (-c) X = -resonantKernel c X := by
  unfold resonantKernel
  rw [Real.cos_neg, show -c * X = -(c * X) by ring, Real.cos_neg]
  field_simp

/-- **The resonant double sum vanishes identically.**  For any symmetric weight `w` and any phase
`φ`, an odd kernel evaluated at the antisymmetric argument `φ m - φ l` sums to zero over a square
index set.  This is the antisymmetry that removes the leading term of the double Voronoi expansion:
the two dual variables enter with the same weight, while the resonant kernel is odd in their
difference. -/
theorem resonant_double_sum_eq_zero {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (w : ι → ι → ℝ) (K : ℝ → ℝ) (φ : ι → ℝ)
    (hw : ∀ m l, w m l = w l m) (hK : ∀ c, K (-c) = -K c) :
    ∑ m ∈ S, ∑ l ∈ S, w m l * K (φ m - φ l) = 0 := by
  have key : ∀ m l : ι, w l m * K (φ l - φ m) = -(w m l * K (φ m - φ l)) := by
    intro m l
    rw [hw l m, show φ l - φ m = -(φ m - φ l) by ring, hK]
    ring
  have h1 : (∑ m ∈ S, ∑ l ∈ S, w m l * K (φ m - φ l))
      = ∑ m ∈ S, ∑ l ∈ S, w l m * K (φ l - φ m) := Finset.sum_comm
  have h2 : (∑ m ∈ S, ∑ l ∈ S, w l m * K (φ l - φ m))
      = -∑ m ∈ S, ∑ l ∈ S, w m l * K (φ m - φ l) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _ => key m l
  have h3 := h1.trans h2
  linarith

/-- **The mechanism, assembled.**  The resonant kernel is odd, hence the resonant half of the double
Voronoi expansion contributes nothing; only the non-resonant half — carrying the phase `φ m + φ l`,
which has no stationary point — and the symmetry-breaking terms survive. -/
theorem double_voronoi_resonant_cancellation {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (w : ι → ι → ℝ) (φ : ι → ℝ) (X : ℝ) (hw : ∀ m l, w m l = w l m) :
    ∑ m ∈ S, ∑ l ∈ S, w m l * resonantKernel (φ m - φ l) X = 0 :=
  resonant_double_sum_eq_zero S w (fun c => resonantKernel c X) φ hw
    (fun c => resonantKernel_neg c X)

/-- The non-resonant kernel carries the phase `φ m + φ l` together with the weight `1/(φ m + φ l)`.
Neither factor is separately of product form, but the weight has a Laplace representation
`1/c = ∫_0^∞ e^{-ct} dt` and the phase is additive, so after introducing the auxiliary variable `t`
the double sum becomes the **square of a single sum**.  This is the step that converts a
shift-averaged correlation of two divisor functions into a classical one-variable divisor
exponential sum. -/
theorem laplace_reciprocal {c : ℝ} (hc : 0 < c) :
    (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(c * t))) = 1 / c := by
  have h := MeasureTheory.integral_comp_mul_left_Ioi (fun t => Real.exp (-t)) (0 : ℝ) hc
  simp only [mul_zero, smul_eq_mul] at h
  rw [h, integral_exp_neg_Ioi_zero, mul_one, one_div]

/-- **The non-resonant double sum is a square.**  With the Laplace variable inserted, the summand
splits as a product of a function of `m` and the same function of `l`, so the double sum over the
index set is the square of a single sum. -/
theorem nonresonant_double_sum_is_square {ι : Type*} (S : Finset ι) (g : ι → ℝ) :
    ∑ m ∈ S, ∑ l ∈ S, g m * g l = (∑ m ∈ S, g m) ^ 2 := by
  rw [sq, Finset.sum_mul_sum]

/-- The length beyond which the dual variable of a `d_k` Voronoi expansion at scale `y` stops
oscillating.  The dual phase is `2πk(my)^{1/k}`, whose derivative in `m` is `2π(y/m^{k-1})^{1/k}`;
this is `≥ 1` exactly for `m ≲ y^{1/(k-1)}`. -/
noncomputable def voronoiFastRange (k y : ℝ) : ℝ := y ^ (1 / (k - 1))

/-- **The dual is fast on its whole natural range only at `k = 2`.**  For `y > 1` the fast range
`y^{1/(k-1)}` reaches the natural truncation `y` precisely when `k ≤ 2`.  For every `k ≥ 3` the
Voronoi dual of `d_k` necessarily extends past its oscillatory range, into a tail where consecutive
terms are in phase and no cancellation in the dual variable is available. -/
theorem voronoiFastRange_covers_iff {k y : ℝ} (hy : 1 < y) (hk : 1 < k) :
    y ≤ voronoiFastRange k y ↔ k ≤ 2 := by
  have hk1 : (0 : ℝ) < k - 1 := by linarith
  unfold voronoiFastRange
  constructor
  · intro h
    have h' : y ^ (1 : ℝ) ≤ y ^ (1 / (k - 1)) := by rwa [Real.rpow_one]
    rw [Real.rpow_le_rpow_left_iff hy, le_div_iff₀ hk1] at h'
    linarith
  · intro h
    have h' : y ^ (1 : ℝ) ≤ y ^ (1 / (k - 1)) := by
      rw [Real.rpow_le_rpow_left_iff hy, le_div_iff₀ hk1]; linarith
    rwa [Real.rpow_one] at h'

/-- At `k = 3` the fast range is `√y`: the dual must be carried to `y` but only oscillates to
`y^{1/2}`. -/
theorem voronoiFastRange_three (y : ℝ) : voronoiFastRange 3 y = y ^ (1/2 : ℝ) := by
  unfold voronoiFastRange; norm_num

end HTGeometry
