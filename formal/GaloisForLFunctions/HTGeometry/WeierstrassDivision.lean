import GaloisForLFunctions.HTGeometry.SliceWeierstrassUnit
import GaloisForLFunctions.HTGeometry.PolynomialDividedDifference

/-!
# Weierstrass' division theorem

Dividing a holomorphic function by the Weierstrass polynomial of a slice leaves a remainder that is
a polynomial in the distinguished variable of degree below that of the divisor.  Both quotient and
remainder are manufactured from contour integrals: the quotient from the Cauchy kernel damped by
the divisor, the remainder from the divided difference of the divisor, which is a polynomial of
degree one less in the evaluation variable.

The identity is Cauchy's formula after the algebraic split
`W(ζ)/(ζ − z) = W(z)/(ζ − z) + (W(ζ) − W(z))/(ζ − z)`.

* `HTGeometry.SliceHolomorphic`, `HTGeometry.wCoeff`, `HTGeometry.wDiff`;
* `HTGeometry.wDiff_mul`;
* `HTGeometry.weierstrass_division_divQuot`;
* `HTGeometry.divRemCoeff_top_eq_zero`, `HTGeometry.divRem_eq_sum_range`.
-/

open Complex Metric
open scoped Real Topology

namespace HTGeometry

variable {n : ℕ}

/-- The slice is holomorphic on a neighbourhood of the closed disc. -/
def SliceHolomorphic (g : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ) (y : Fin n → ℂ) : Prop :=
  ∃ Ug : Set ℂ, IsOpen Ug ∧ closedBall (0 : ℂ) t ⊆ Ug ∧
    DifferentiableOn ℂ (fun z => g (Fin.cons z y)) Ug

/-- The coefficients of the Weierstrass polynomial of a slice. -/
noncomputable def wCoeff (f : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ) (k j : ℕ) (y : Fin n → ℂ) : ℂ :=
  (-1) ^ (k - j) * (sliceRoots f t y).esymm (k - j)

/-- The Weierstrass polynomial written in its coefficients. -/
theorem sliceWeierstrass_eq_sum_wCoeff {f : (Fin (n + 1) → ℂ) → ℂ} {t : ℝ} {y : Fin n → ℂ} {k : ℕ}
    (hcard : Multiset.card (sliceRoots f t y) = k) (z : ℂ) :
    sliceWeierstrass f t (Fin.cons z y) = ∑ j ∈ Finset.range (k + 1), wCoeff f t k j y * z ^ j := by
  rw [sliceWeierstrass_cons, multisetLinearProd_eq_sum, hcard]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [wCoeff]

/-- The divided difference of the Weierstrass polynomial. -/
noncomputable def wDiff (f : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ) (k : ℕ) (y : Fin n → ℂ)
    (ζ z : ℂ) : ℂ :=
  ∑ l ∈ Finset.range (k + 1),
    (∑ j ∈ Finset.Ico (l + 1) (k + 1), wCoeff f t k j y * ζ ^ (j - 1 - l)) * z ^ l

/-- **The divided difference divides the difference.** -/
theorem wDiff_mul {f : (Fin (n + 1) → ℂ) → ℂ} {t : ℝ} {y : Fin n → ℂ} {k : ℕ}
    (hcard : Multiset.card (sliceRoots f t y) = k) (ζ z : ℂ) :
    wDiff f t k y ζ z * (ζ - z)
      = sliceWeierstrass f t (Fin.cons ζ y) - sliceWeierstrass f t (Fin.cons z y) := by
  rw [sliceWeierstrass_eq_sum_wCoeff hcard ζ, sliceWeierstrass_eq_sum_wCoeff hcard z, wDiff]
  exact (GaloisForLFunctions.HTGeometry.sum_pow_sub_sum_pow_eq
    (fun j => wCoeff f t k j y) (k + 1) ζ z).symm

/-- The quotient of Weierstrass' division. -/
noncomputable def divQuot (f : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ) (g : (Fin (n + 1) → ℂ) → ℂ)
    (w : Fin (n + 1) → ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∮ ζ in C(0, t), g (Fin.cons ζ (Fin.tail w)) /
      (sliceWeierstrass f t (Fin.cons ζ (Fin.tail w)) * (ζ - w 0))

/-- The coefficients of the remainder of Weierstrass' division. -/
noncomputable def divRemCoeff (f : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ) (g : (Fin (n + 1) → ℂ) → ℂ)
    (k l : ℕ) (y : Fin n → ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∮ ζ in C(0, t), g (Fin.cons ζ y) *
      (∑ j ∈ Finset.Ico (l + 1) (k + 1), wCoeff f t k j y * ζ ^ (j - 1 - l))
        / sliceWeierstrass f t (Fin.cons ζ y)

/-- The remainder of Weierstrass' division. -/
noncomputable def divRem (f : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ) (g : (Fin (n + 1) → ℂ) → ℂ)
    (k : ℕ) (w : Fin (n + 1) → ℂ) : ℂ :=
  ∑ l ∈ Finset.range (k + 1), divRemCoeff f t g k l (Fin.tail w) * (w 0) ^ l

/-- **The top coefficient of the remainder vanishes**, so the remainder has degree below the
degree of the divisor. -/
theorem divRemCoeff_top_eq_zero (f : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ) (g : (Fin (n + 1) → ℂ) → ℂ)
    (k : ℕ) (y : Fin n → ℂ) : divRemCoeff f t g k k y = 0 := by
  have hempty : Finset.Ico (k + 1) (k + 1) = (∅ : Finset ℕ) := by
    simp
  rw [divRemCoeff]
  have hzero : ∀ ζ : ℂ, g (Fin.cons ζ y) *
      (∑ j ∈ Finset.Ico (k + 1) (k + 1), wCoeff f t k j y * ζ ^ (j - 1 - k))
        / sliceWeierstrass f t (Fin.cons ζ y) = 0 := by
    intro ζ
    rw [hempty]
    simp
  simp only [hzero]
  simp [circleIntegral]

/-- **Weierstrass' division theorem.**  A holomorphic function is the Weierstrass polynomial of a
slice times a holomorphic quotient, plus a remainder that is a polynomial in the distinguished
variable of degree below that of the polynomial. -/
theorem weierstrass_division_divQuot {f g : (Fin (n + 1) → ℂ) → ℂ} {t : ℝ} (ht : 0 < t)
    {y : Fin n → ℂ} (hy : SliceAdmissible f t y) (hg : SliceHolomorphic g t y)
    {k : ℕ} (hcard : Multiset.card (sliceRoots f t y) = k) {z : ℂ} (hz : ‖z‖ < t) :
    g (Fin.cons z y)
      = sliceWeierstrass f t (Fin.cons z y) * divQuot f t g (Fin.cons z y)
        + divRem f t g k (Fin.cons z y) := by
  classical
  obtain ⟨Ug, hUgopen, hUgsub, hgd⟩ := hg
  have hne0 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hsphere : ∀ ζ ∈ sphere (0 : ℂ) t, ‖ζ‖ = t := fun ζ hζ => by
    simpa using mem_sphere_iff_norm.1 hζ
  have hWne : ∀ ζ ∈ sphere (0 : ℂ) t, sliceWeierstrass f t (Fin.cons ζ y) ≠ 0 :=
    fun ζ hζ => sliceWeierstrass_ne_zero_of_norm_eq ht hy (hsphere ζ hζ)
  have hzne : ∀ ζ ∈ sphere (0 : ℂ) t, ζ - z ≠ 0 := by
    intro ζ hζ hcon
    have hzeq : ζ = z := sub_eq_zero.mp hcon
    have := hsphere ζ hζ
    rw [hzeq] at this
    rw [this] at hz
    exact lt_irrefl t hz
  -- continuity data on the circle
  have hgcont : ContinuousOn (fun ζ : ℂ => g (Fin.cons ζ y)) (sphere (0 : ℂ) t) := by
    refine ContinuousOn.mono (hgd.continuousOn) ?_
    exact subset_trans sphere_subset_closedBall hUgsub
  have hWcont : Continuous fun ζ : ℂ => sliceWeierstrass f t (Fin.cons ζ y) := by
    have heq : (fun ζ : ℂ => sliceWeierstrass f t (Fin.cons ζ y))
        = multisetLinearProd (sliceRoots f t y) := by
      funext ζ
      rw [sliceWeierstrass_cons]
    rw [heq]
    exact continuous_multisetLinearProd _
  -- the pieces are circle integrable
  have hintQ : CircleIntegrable (fun ζ : ℂ => sliceWeierstrass f t (Fin.cons z y) *
      (g (Fin.cons ζ y) / (sliceWeierstrass f t (Fin.cons ζ y) * (ζ - z)))) (0 : ℂ) t := by
    refine ContinuousOn.circleIntegrable ht.le ?_
    refine continuousOn_const.mul (hgcont.div (hWcont.continuousOn.mul (by fun_prop)) ?_)
    intro ζ hζ
    exact mul_ne_zero (hWne ζ hζ) (hzne ζ hζ)
  have hintR : ∀ l ∈ Finset.range (k + 1), CircleIntegrable (fun ζ : ℂ =>
      z ^ l * (g (Fin.cons ζ y) *
        (∑ j ∈ Finset.Ico (l + 1) (k + 1), wCoeff f t k j y * ζ ^ (j - 1 - l))
          / sliceWeierstrass f t (Fin.cons ζ y))) (0 : ℂ) t := by
    intro l _
    refine ContinuousOn.circleIntegrable ht.le ?_
    refine continuousOn_const.mul ((hgcont.mul ?_).div hWcont.continuousOn ?_)
    · exact continuousOn_finsetSum _ fun j _ => by fun_prop
    · intro ζ hζ
      exact hWne ζ hζ
  -- the remainder is a single contour integral
  have hremeq : divRem f t g k (Fin.cons z y)
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∮ ζ in C(0, t), g (Fin.cons ζ y) * wDiff f t k y ζ z
          / sliceWeierstrass f t (Fin.cons ζ y) := by
    rw [divRem, Fin.tail_cons, Fin.cons_zero]
    have hstep : ∀ l ∈ Finset.range (k + 1),
        divRemCoeff f t g k l y * z ^ l
          = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
            ∮ ζ in C(0, t), z ^ l * (g (Fin.cons ζ y) *
              (∑ j ∈ Finset.Ico (l + 1) (k + 1), wCoeff f t k j y * ζ ^ (j - 1 - l))
                / sliceWeierstrass f t (Fin.cons ζ y)) := by
      intro l _
      rw [divRemCoeff]
      have := circleIntegral.integral_smul (z ^ l) (fun ζ : ℂ => g (Fin.cons ζ y) *
        (∑ j ∈ Finset.Ico (l + 1) (k + 1), wCoeff f t k j y * ζ ^ (j - 1 - l))
          / sliceWeierstrass f t (Fin.cons ζ y)) 0 t
      simp only [smul_eq_mul] at this
      rw [this]
      ring
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum,
      ← circleIntegral_finset_sum (fun l ζ => z ^ l * (g (Fin.cons ζ y) *
        (∑ j ∈ Finset.Ico (l + 1) (k + 1), wCoeff f t k j y * ζ ^ (j - 1 - l))
          / sliceWeierstrass f t (Fin.cons ζ y))) 0 t _ hintR]
    congr 1
    refine circleIntegral.integral_congr ht.le fun ζ hζ => ?_
    rw [wDiff, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  -- assemble
  have hquoteq : sliceWeierstrass f t (Fin.cons z y) * divQuot f t g (Fin.cons z y)
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∮ ζ in C(0, t), sliceWeierstrass f t (Fin.cons z y) *
          (g (Fin.cons ζ y) / (sliceWeierstrass f t (Fin.cons ζ y) * (ζ - z))) := by
    rw [divQuot, Fin.tail_cons, Fin.cons_zero]
    have := circleIntegral.integral_smul (sliceWeierstrass f t (Fin.cons z y))
      (fun ζ : ℂ => g (Fin.cons ζ y) /
        (sliceWeierstrass f t (Fin.cons ζ y) * (ζ - z))) 0 t
    simp only [smul_eq_mul] at this
    rw [this]
    ring
  have hintB : CircleIntegrable (fun ζ : ℂ =>
      g (Fin.cons ζ y) * wDiff f t k y ζ z / sliceWeierstrass f t (Fin.cons ζ y)) (0 : ℂ) t := by
    refine ContinuousOn.circleIntegrable ht.le ?_
    refine (hgcont.mul ?_).div hWcont.continuousOn (fun ζ hζ => hWne ζ hζ)
    refine continuousOn_finsetSum _ fun l _ => ?_
    exact (continuousOn_finsetSum _ fun j _ => by fun_prop).mul continuousOn_const
  have hcomb : (∮ ζ in C(0, t), sliceWeierstrass f t (Fin.cons z y) *
        (g (Fin.cons ζ y) / (sliceWeierstrass f t (Fin.cons ζ y) * (ζ - z))))
      + (∮ ζ in C(0, t), g (Fin.cons ζ y) * wDiff f t k y ζ z
          / sliceWeierstrass f t (Fin.cons ζ y))
      = ∮ ζ in C(0, t), (ζ - z)⁻¹ • g (Fin.cons ζ y) := by
    rw [← circleIntegral.integral_add hintQ hintB]
    refine circleIntegral.integral_congr ht.le fun ζ hζ => ?_
    have hW := hWne ζ hζ
    have hzz := hzne ζ hζ
    have hdiff := wDiff_mul hcard ζ z
    rw [smul_eq_mul]
    field_simp
    linear_combination (g (Fin.cons ζ y)) * hdiff
  have hcauchy : (∮ ζ in C(0, t), (ζ - z)⁻¹ • g (Fin.cons ζ y))
      = (2 * (Real.pi : ℂ) * Complex.I) • g (Fin.cons z y) := by
    refine Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      Set.countable_empty (by rw [mem_ball_zero_iff]; exact hz) ?_ ?_
    · exact (hgd.mono hUgsub).continuousOn
    · intro w hw
      exact hgd.differentiableAt (hUgopen.mem_nhds (hUgsub (ball_subset_closedBall hw.1)))
  rw [hquoteq, hremeq, ← mul_add, hcomb, hcauchy, smul_eq_mul]
  field_simp

/-- **The remainder has degree below that of the divisor.**  Its top coefficient vanishes, so the
sum may be taken over `range k` — a polynomial in the distinguished variable of degree `< k`. -/
theorem divRem_eq_sum_range (f : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ) (g : (Fin (n + 1) → ℂ) → ℂ)
    (k : ℕ) (w : Fin (n + 1) → ℂ) :
    divRem f t g k w
      = ∑ l ∈ Finset.range k, divRemCoeff f t g k l (Fin.tail w) * (w 0) ^ l := by
  rw [divRem, Finset.sum_range_succ, divRemCoeff_top_eq_zero, zero_mul, add_zero]

end HTGeometry
