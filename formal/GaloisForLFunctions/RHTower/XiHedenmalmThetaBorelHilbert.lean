import GaloisForLFunctions.RHTower.XiHedenmalmThetaBorelHolonomy
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangleExhaustion
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The Borel boundary Hilbert space of the flat theta tail

On the fixed Hilbert space `L²((0,∞), dt)` the square root of the Borel source density is a genuine
vector, and the Hedenmalm two-ended eigenfunction is one of its matrix coefficients against the
dilation character.

Writing `g x t = sqrt (b x t)` and `M α t = exp (i α log (1 + t) / 2)`, the module proves

* `g x` and every tilt `M α * g x` lie in `L²((0,∞))` for centered parameters in the open half
  strip, which contains the whole centered Xi divisor;
* the exact sesquilinear law `⟪M α * g x, M β * g x⟫ = ∫ M (β - conj α) * b x`;
* the squared norm of `g x` is the theta tail mass `∫_x^∞ k`;
* at a centered Xi zero, `⟪g x, M α * g x⟫ = -u α x`;
* the tilt is norm preserving exactly for real centered parameters.

Nothing here places a zero on the critical line.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- The Borel boundary vector: the square root of the positive source density. -/
def hedenmalmBorelVectorFun (x t : ℝ) : ℂ :=
  ((Real.sqrt (hedenmalmBorelDensity x t) : ℝ) : ℂ)

/-- The Borel boundary vector tilted by the dilation character. -/
def hedenmalmBorelHolonomyFun (alpha : ℂ) (x t : ℝ) : ℂ :=
  hedenmalmBorelCharacter alpha t * hedenmalmBorelVectorFun x t

@[simp] theorem hedenmalmBorelHolonomyFun_zero (x t : ℝ) :
    hedenmalmBorelHolonomyFun 0 x t = hedenmalmBorelVectorFun x t := by
  simp [hedenmalmBorelHolonomyFun]

theorem norm_sq_hedenmalmBorelHolonomyFun (alpha : ℂ) (x : ℝ) {t : ℝ} (ht : -1 < t) :
    ‖hedenmalmBorelHolonomyFun alpha x t‖ ^ 2 =
      ‖hedenmalmBorelCharacter alpha t‖ ^ 2 * hedenmalmBorelDensity x t := by
  rw [hedenmalmBorelHolonomyFun, hedenmalmBorelVectorFun, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (hedenmalmBorelDensity_nonneg x ht)]

theorem continuousOn_hedenmalmBorelVectorFun (x : ℝ) :
    ContinuousOn (hedenmalmBorelVectorFun x) (Ioi (-1 : ℝ)) := by
  unfold hedenmalmBorelVectorFun
  exact Complex.continuous_ofReal.comp_continuousOn
    (Real.continuous_sqrt.comp_continuousOn (continuousOn_hedenmalmBorelDensity x))

theorem continuousOn_hedenmalmBorelHolonomyFun (alpha : ℂ) (x : ℝ) :
    ContinuousOn (hedenmalmBorelHolonomyFun alpha x) (Ioi (-1 : ℝ)) :=
  (continuousOn_hedenmalmBorelCharacter alpha).mul (continuousOn_hedenmalmBorelVectorFun x)

theorem aestronglyMeasurable_hedenmalmBorelHolonomyFun (alpha : ℂ) (x : ℝ) :
    AEStronglyMeasurable (hedenmalmBorelHolonomyFun alpha x)
      (volume.restrict (Ioi (0 : ℝ))) := by
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
  exact (continuousOn_hedenmalmBorelHolonomyFun alpha x).mono
    (fun t ht => mem_Ioi.mpr (by have := mem_Ioi.mp ht; linarith))

/-- **The tilted Borel boundary vector is square integrable.**  Superexponential flatness of the
theta tail makes every centered parameter of the open half strip admissible. -/
theorem memLp_hedenmalmBorelHolonomyFun {alpha : ℂ} (halpha : |alpha.im| < 1 / 2) (x : ℝ) :
    MemLp (hedenmalmBorelHolonomyFun alpha x) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  rw [memLp_two_iff_integrable_sq_norm
    (aestronglyMeasurable_hedenmalmBorelHolonomyFun alpha x)]
  refine (integrableOn_norm_sq_hedenmalmBorelCharacter_mul_density halpha x).congr_fun
    ?_ measurableSet_Ioi
  intro t ht
  exact (norm_sq_hedenmalmBorelHolonomyFun alpha x
    (by have := mem_Ioi.mp ht; linarith)).symm

theorem abs_im_zero_lt_half : |(0 : ℂ).im| < 1 / 2 := by norm_num

/-- The tilted Borel boundary vector as an element of `L²((0,∞))`. -/
def hedenmalmBorelHolonomyVector {alpha : ℂ} (halpha : |alpha.im| < 1 / 2) (x : ℝ) :
    Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (memLp_hedenmalmBorelHolonomyFun halpha x).toLp _

/-- The untilted Borel boundary vector. -/
def hedenmalmBorelVector (x : ℝ) : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  hedenmalmBorelHolonomyVector abs_im_zero_lt_half x

/-- **Exact sesquilinear law of the Borel boundary.**  The inner product of two tilts is the
integral of the difference character against the positive source density. -/
theorem inner_hedenmalmBorelHolonomyVector
    {alpha beta : ℂ} (ha : |alpha.im| < 1 / 2) (hb : |beta.im| < 1 / 2) (x : ℝ) :
    inner ℂ (hedenmalmBorelHolonomyVector ha x) (hedenmalmBorelHolonomyVector hb x) =
      ∫ t in Ioi (0 : ℝ),
        hedenmalmBorelCharacter (beta - (starRingEnd ℂ) alpha) t *
          (hedenmalmBorelDensity x t : ℂ) := by
  unfold hedenmalmBorelHolonomyVector
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_hedenmalmBorelHolonomyFun ha x).coeFn_toLp,
    (memLp_hedenmalmBorelHolonomyFun hb x).coeFn_toLp,
    ae_restrict_mem measurableSet_Ioi] with t h1 h2 ht
  have ht' : (-1 : ℝ) < t := by have := mem_Ioi.mp ht; linarith
  have hnn : 0 ≤ hedenmalmBorelDensity x t := hedenmalmBorelDensity_nonneg x ht'
  rw [h1, h2, RCLike.inner_apply, hedenmalmBorelHolonomyFun, hedenmalmBorelHolonomyFun,
    hedenmalmBorelVectorFun, map_mul, Complex.conj_ofReal,
    conj_hedenmalmBorelCharacter]
  have hchar :
      hedenmalmBorelCharacter beta t * hedenmalmBorelCharacter (-(starRingEnd ℂ) alpha) t =
        hedenmalmBorelCharacter (beta - (starRingEnd ℂ) alpha) t := by
    rw [← hedenmalmBorelCharacter_mul, ← sub_eq_add_neg]
  calc
    hedenmalmBorelCharacter beta t * ((Real.sqrt (hedenmalmBorelDensity x t) : ℝ) : ℂ) *
        (hedenmalmBorelCharacter (-(starRingEnd ℂ) alpha) t *
          ((Real.sqrt (hedenmalmBorelDensity x t) : ℝ) : ℂ))
        = (hedenmalmBorelCharacter beta t *
            hedenmalmBorelCharacter (-(starRingEnd ℂ) alpha) t) *
          (((Real.sqrt (hedenmalmBorelDensity x t) *
              Real.sqrt (hedenmalmBorelDensity x t) : ℝ)) : ℂ) := by
        push_cast
        ring
    _ = hedenmalmBorelCharacter (beta - (starRingEnd ℂ) alpha) t *
          (hedenmalmBorelDensity x t : ℂ) := by
        rw [hchar, Real.mul_self_sqrt hnn]

/-- The matrix coefficient of the dilation character against the Borel boundary vector. -/
theorem inner_hedenmalmBorelVector_holonomy
    {alpha : ℂ} (ha : |alpha.im| < 1 / 2) (x : ℝ) :
    inner ℂ (hedenmalmBorelVector x) (hedenmalmBorelHolonomyVector ha x) =
      ∫ t in Ioi (0 : ℝ),
        hedenmalmBorelCharacter alpha t * (hedenmalmBorelDensity x t : ℂ) := by
  rw [hedenmalmBorelVector, inner_hedenmalmBorelHolonomyVector]
  simp only [map_zero, sub_zero]

/-- **Squared norm of the Borel boundary vector.**  It is exactly the theta tail mass. -/
theorem inner_self_hedenmalmBorelVector (x : ℝ) :
    inner ℂ (hedenmalmBorelVector x) (hedenmalmBorelVector x) =
      ((∫ y in Ioi x, thetaCuspFullSource y : ℝ) : ℂ) := by
  rw [hedenmalmBorelVector, inner_hedenmalmBorelHolonomyVector]
  simp only [map_zero, sub_zero, hedenmalmBorelCharacter_zero, one_mul]
  rw [← integral_Ioi_hedenmalmBorelDensity x, ← integral_complex_ofReal]

theorem norm_sq_hedenmalmBorelVector (x : ℝ) :
    ‖hedenmalmBorelVector x‖ ^ 2 = ∫ y in Ioi x, thetaCuspFullSource y := by
  have h := inner_self_hedenmalmBorelVector x
  rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : ((‖hedenmalmBorelVector x‖ ^ 2 : ℝ) : ℂ) =
      ((∫ y in Ioi x, thetaCuspFullSource y : ℝ) : ℂ) := by
    push_cast
    exact h
  exact_mod_cast h2

/-- Every centered Xi zero lies in the open half strip. -/
theorem abs_im_lt_half_of_XiC_eq_zero {alpha : ℂ} (hzero : XiC alpha = 0) :
    |alpha.im| < 1 / 2 := by
  obtain ⟨h1, h2⟩ := xiC_zero_im_mem_openHalf hzero
  rw [abs_lt]
  constructor <;> linarith

theorem abs_im_lt_one_of_XiC_eq_zero {alpha : ℂ} (hzero : XiC alpha = 0) :
    |alpha.im| < 1 :=
  lt_trans (abs_im_lt_half_of_XiC_eq_zero hzero) (by norm_num)

/-- **The Hedenmalm eigenfunction is a Borel boundary matrix coefficient.**  At every centered Xi
zero the two-ended theta solution is minus the inner product of the source vector with its own
dilation tilt. -/
theorem inner_hedenmalmBorelVector_eq_neg_eigenfunction
    {alpha : ℂ} (hzero : XiC alpha = 0) (x : ℝ) :
    inner ℂ (hedenmalmBorelVector x)
        (hedenmalmBorelHolonomyVector (abs_im_lt_half_of_XiC_eq_zero hzero) x) =
      -xiHedenmalmBoundaryEigenfunction alpha x := by
  rw [inner_hedenmalmBorelVector_holonomy,
    xiHedenmalmBoundaryEigenfunction_eq_borelTail
      (abs_im_lt_one_of_XiC_eq_zero hzero) hzero x, neg_neg]

/-- **Unitarity of the tilt on the source vector.**  The dilation tilt preserves the Borel norm
exactly at real centered parameters, that is exactly on the critical line. -/
theorem norm_hedenmalmBorelHolonomyVector_of_im_eq_zero
    {alpha : ℂ} (ha : |alpha.im| < 1 / 2) (halpha : alpha.im = 0) (x : ℝ) :
    ‖hedenmalmBorelHolonomyVector ha x‖ = ‖hedenmalmBorelVector x‖ := by
  have hconj : alpha - (starRingEnd ℂ) alpha = 0 := by
    rw [Complex.sub_conj, halpha]
    simp
  have h : inner ℂ (hedenmalmBorelHolonomyVector ha x)
      (hedenmalmBorelHolonomyVector ha x) =
      inner ℂ (hedenmalmBorelVector x) (hedenmalmBorelVector x) := by
    rw [inner_hedenmalmBorelHolonomyVector, hedenmalmBorelVector,
      inner_hedenmalmBorelHolonomyVector, hconj]
    simp only [map_zero, sub_zero]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖hedenmalmBorelHolonomyVector ha x‖ ^ 2 = ‖hedenmalmBorelVector x‖ ^ 2 := by
    exact_mod_cast h
  have hsqrt := congrArg Real.sqrt h'
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hsqrt

end RHTower
