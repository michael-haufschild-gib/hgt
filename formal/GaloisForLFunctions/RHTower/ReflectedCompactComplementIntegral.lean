import GaloisForLFunctions.RHTower.SmoothAFEReflectedComplementScale
import Mathlib.MeasureTheory.Group.Integral

open Complex MeasureTheory Set
noncomputable section
namespace RHTower

/-- Translating the literal deep contour makes its arithmetic numerator independent
of the spectral parameter. -/
def reflectedCompactDeepIntegrand (z : ℂ) (N : ℝ) (n : ℕ) (v : ℝ) : ℂ :=
  zetaChi ((-7 / 2 : ℂ) + (v : ℂ) * I) *
    (n + 1 : ℂ) ^ ((-9 / 2 : ℂ) + (v : ℂ) * I) *
    (N : ℂ) ^ (z - 9 / 2 + (v : ℂ) * I) *
    smoothAFEGaussianKernel (z - 9 / 2 + (v : ℂ) * I)

/-- The deep cofactor in complex spectral coordinates, before its exact chi prefactor. -/
def reflectedCompactDeepCoefficient (z : ℂ) (N : ℝ) (n : ℕ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ v : ℝ, reflectedCompactDeepIntegrand z N n v

/-- Exact translation of the original deep coefficient, valid without replacing
its cutoff, integer power or archimedean factor. -/
theorem smoothAFEZetaDisplacedDeepCoefficient_eq_compactIntegral
    (d tau N : ℝ) (n : ℕ) :
    smoothAFEZetaDisplacedDeepCoefficient d (-tau) N n =
      reflectedCompactDeepCoefficient (rightDisplacedLinePt d tau) N n := by
  unfold smoothAFEZetaDisplacedDeepCoefficient reflectedCompactDeepCoefficient
  congr 1
  let F : ℝ → ℂ := fun v => smoothAFEZetaReflectedTerm (displacedLinePt d (-tau)) N n
    (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)
  have heq (v : ℝ) : F (v + tau) =
      reflectedCompactDeepIntegrand (rightDisplacedLinePt d tau) N n v := by
    dsimp only [F]
    rw [smoothAFEZetaReflectedTerm_eq_cpow]
    have hsum : displacedLinePt d (-tau) +
        (((d - 4 : ℝ) : ℂ) + ((v + tau : ℝ) : ℂ) * I) = (-7 / 2 : ℂ) + (v : ℂ) * I := by
      unfold displacedLinePt
      push_cast
      ring
    have hw : (((d - 4 : ℝ) : ℂ) + ((v + tau : ℝ) : ℂ) * I) =
        rightDisplacedLinePt d tau - 9 / 2 + (v : ℂ) * I := by
      unfold rightDisplacedLinePt
      push_cast
      ring
    rw [hsum, show ((-7 / 2 : ℂ) + (v : ℂ) * I) - 1 =
      (-9 / 2 : ℂ) + (v : ℂ) * I by ring, hw]
    rfl
  calc
    (∫ v : ℝ, F v) = ∫ v : ℝ, F (v + tau) := (integral_add_right_eq_self F tau).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall heq)

/-- The actual complementary coefficient is the translated integral with its
original negative chi prefactor, throughout the full strict displacement strip. -/
theorem smoothAFEZetaRightComplementCoefficient_eq_compactIntegral
    {d N : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) (hN : 0 < N) (tau : ℝ) (n : ℕ) :
    smoothAFEZetaRightComplementCoefficient d tau N n =
      -zetaChi (rightDisplacedLinePt d tau) *
        reflectedCompactDeepCoefficient (rightDisplacedLinePt d tau) N n := by
  rw [smoothAFEZetaRightComplementCoefficient_eq_neg_chi_mul_deep hd hdhalf hN,
    smoothAFEZetaDisplacedDeepCoefficient_eq_compactIntegral]

/-- In translated coordinates the spectral dependence of each integrand is
holomorphic on an entire half-plane containing the open critical strip. -/
theorem differentiableOn_reflectedCompactDeepIntegrand {N : ℝ} (hN : 0 < N)
    (n : ℕ) (v : ℝ) :
    DifferentiableOn ℂ (fun z => reflectedCompactDeepIntegrand z N n v) {z | z.re < 9 / 2} := by
  have hw : Differentiable ℂ (fun z : ℂ => z - 9 / 2 + (v : ℂ) * I) :=
    (differentiable_id.sub_const _).add_const _
  have hpow : Differentiable ℂ (fun z : ℂ => (N : ℂ) ^ (z - 9 / 2 + (v : ℂ) * I)) :=
    hw.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hN.ne'))
  intro z hz
  have hz' : z.re < 9 / 2 := hz
  have hwne : z - 9 / 2 + (v : ℂ) * I ≠ 0 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp at hre
    linarith
  have hker : DifferentiableAt ℂ (fun z : ℂ =>
      smoothAFEGaussianKernel (z - 9 / 2 + (v : ℂ) * I)) z :=
    ((hw.differentiableAt.pow 2).cexp).div hw.differentiableAt hwne
  exact ((hpow.differentiableAt.const_mul _).mul hker).differentiableWithinAt

end RHTower
