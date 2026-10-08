import GaloisForLFunctions.RHTower.WeilPaperCovarianceWindowDuality
import Mathlib.Analysis.Convex.Function

/-!
# Geometry of covariance-window energy certificates

The certificate decreases convexly with the measurement tolerance. As a
function of the bounded spectral penalty it is concave and 1-Lipschitz, and
its attained minimizer gives a supporting affine bound and controlled transfer.
-/

open MeasureTheory Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided
variable {ι : Type*}

/-- Relaxing measurement precision cannot raise the certified energy. -/
theorem antitone_paperCovarianceGammaCertificate_tolerance
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) :
    Antitone (paperCovarianceGammaCertificate c F G μ s) := by
  intro r q hrq
  exact paperCovarianceGammaCertificate_refinement c F G μ s ⟨s, le_rfl⟩ q ⟨r, hrq⟩

/-- The exact dual formula makes the dependence on nonnegative tolerance
convex, including the endpoint of exact measurements. -/
theorem convexOn_paperCovarianceGammaCertificate_tolerance
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) :
    ConvexOn ℝ≥0 Set.univ (paperCovarianceGammaCertificate c F G μ s) := by
  refine ⟨convex_univ, ?_⟩
  intro r _ q _ a b _ _ hab
  rw [paperCovarianceGammaCertificate_eq_sSup_robustAffineValues]
  apply csSup_le (paperCovarianceRobustAffineValues_nonempty c F G μ s _)
  rintro _ ⟨A, rfl⟩
  have hr := paperCovarianceRobustAffineValue_le_certificate c F G μ s r A
  have hq := paperCovarianceRobustAffineValue_le_certificate c F G μ s q A
  have habR : (a : ℝ) + (b : ℝ) = 1 := by exact_mod_cast hab
  have heq : paperCovarianceRobustAffineValue c F G μ s (a • r + b • q) A =
      (a : ℝ) * paperCovarianceRobustAffineValue c F G μ s r A +
      (b : ℝ) * paperCovarianceRobustAffineValue c F G μ s q A := by
    unfold paperCovarianceRobustAffineValue
    simp only [smul_eq_mul, NNReal.coe_add, NNReal.coe_mul]
    linear_combination -(A.1.2 + ∑ k : s, A.1.1 k * paperObservedPhaseCovariances c F μ k.1) * habR
  rw [heq]
  exact add_le_add (mul_le_mul_of_nonneg_left hr a.2) (mul_le_mul_of_nonneg_left hq b.2)

/-- A window minimizer gives a supporting affine bound for changes to the
spectral penalty, while preserving every covariance constraint. -/
theorem paperCovarianceGammaCertificate_supergradient
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G H : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) :
    paperCovarianceGammaCertificate c F H μ s r ≤ paperCovarianceGammaCertificate c F G μ s r +
      ∫ ξ, (H - G) ξ ∂((paperCovarianceWindowGammaMinimizer c F G μ s r).1 : Measure ℝ) := by
  have hm := paperCovarianceGammaCertificate_le c F H μ s r
    ⟨paperCovarianceWindowGammaMinimizer c F G μ s r,
      paperCovarianceWindowGammaMinimizer_mem c F G μ s r⟩
  have hd := paperPerturbedGammaExpectation_sub (paperCovarianceWindowGammaMinimizer c F G μ s r).1 H G
  change _ ≤ paperPerturbedGammaExpectation G (paperCovarianceWindowGammaMinimizer c F G μ s r).1 + _
  linarith

theorem paperCovarianceGammaCertificate_le_add_norm
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G H : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) :
    paperCovarianceGammaCertificate c F G μ s r ≤ paperCovarianceGammaCertificate c F H μ s r +
      ‖G - H‖ := by
  have h := paperCovarianceGammaCertificate_supergradient c F H G μ s r
  have hi := (G - H).norm_integral_le_norm
    ((paperCovarianceWindowGammaMinimizer c F H μ s r).1 : Measure ℝ)
  rw [Real.norm_eq_abs] at hi
  linarith [le_abs_self (∫ ξ, (G - H) ξ
    ∂((paperCovarianceWindowGammaMinimizer c F H μ s r).1 : Measure ℝ))]

/-- Finite measurement restrictions preserve the sharp uniform perturbation
bound of the unconstrained variational problem. -/
theorem abs_paperCovarianceGammaCertificate_sub_le
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G H : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) :
    |paperCovarianceGammaCertificate c F G μ s r - paperCovarianceGammaCertificate c F H μ s r| ≤
      ‖G - H‖ := by
  apply abs_le.mpr
  constructor
  · have h := paperCovarianceGammaCertificate_le_add_norm c F H G μ s r
    rw [norm_sub_rev] at h
    linarith
  · have h := paperCovarianceGammaCertificate_le_add_norm c F G H μ s r
    linarith

theorem lipschitzWith_paperCovarianceGammaCertificate_penalty
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) :
    LipschitzWith 1 (fun G => paperCovarianceGammaCertificate c F G μ s r) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro G H
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using
    abs_paperCovarianceGammaCertificate_sub_le c F G H μ s r

/-- Window energy remains concave in the bounded spectral penalty. -/
theorem paperCovarianceGammaCertificate_concave_penalty
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G H : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) (t : Icc (0 : ℝ) 1) :
    t.1 * paperCovarianceGammaCertificate c F G μ s r +
      (1 - t.1) * paperCovarianceGammaCertificate c F H μ s r ≤
        paperCovarianceGammaCertificate c F (t.1 • G + (1 - t.1) • H) μ s r := by
  let ν := paperCovarianceWindowGammaMinimizer c F (t.1 • G + (1 - t.1) • H) μ s r
  have hν : ν ∈ paperCovarianceWindow c F μ s r := paperCovarianceWindowGammaMinimizer_mem c F _ μ s r
  calc
    _ ≤ t.1 * paperPerturbedGammaExpectation G ν.1 +
        (1 - t.1) * paperPerturbedGammaExpectation H ν.1 :=
      add_le_add (mul_le_mul_of_nonneg_left (paperCovarianceGammaCertificate_le c F G μ s r ⟨ν, hν⟩) t.2.1)
        (mul_le_mul_of_nonneg_left (paperCovarianceGammaCertificate_le c F H μ s r ⟨ν, hν⟩)
          (sub_nonneg.mpr t.2.2))
    _ = paperPerturbedGammaExpectation (t.1 • G + (1 - t.1) • H) ν.1 :=
      (paperPerturbedGammaExpectation_segment ν.1 G H t).symm
    _ = _ := rfl

/-- Reusing an optimizer after a bounded penalty change costs at most twice
the uniform size of that change, with measurement constraints unchanged. -/
theorem paperCovarianceWindowGammaMinimizer_transfer_bound
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G H : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) :
    0 ≤ paperPerturbedGammaExpectation G (paperCovarianceWindowGammaMinimizer c F H μ s r).1 -
      paperCovarianceGammaCertificate c F G μ s r ∧
    paperPerturbedGammaExpectation G (paperCovarianceWindowGammaMinimizer c F H μ s r).1 -
      paperCovarianceGammaCertificate c F G μ s r ≤ 2 * ‖G - H‖ := by
  let ν := paperCovarianceWindowGammaMinimizer c F H μ s r
  have hν : ν ∈ paperCovarianceWindow c F μ s r := paperCovarianceWindowGammaMinimizer_mem c F H μ s r
  have hm := paperCovarianceGammaCertificate_le c F G μ s r ⟨ν, hν⟩
  have hd := paperPerturbedGammaExpectation_sub ν.1 G H
  have hi := (G - H).norm_integral_le_norm (ν.1 : Measure ℝ)
  rw [Real.norm_eq_abs] at hi
  have hv := paperCovarianceGammaCertificate_le_add_norm c F H G μ s r
  rw [norm_sub_rev] at hv
  change paperPerturbedGammaExpectation H ν.1 ≤ paperCovarianceGammaCertificate c F G μ s r + _ at hv
  constructor
  · exact sub_nonneg.mpr hm
  · linarith [le_abs_self (∫ ξ, (G - H) ξ ∂(ν.1 : Measure ℝ))]

end RHTower.WeilWorkPBAP
