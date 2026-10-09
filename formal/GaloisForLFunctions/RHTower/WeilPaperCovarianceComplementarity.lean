import GaloisForLFunctions.RHTower.WeilPaperCovarianceDualAttainment

/-!
# Active measurements in optimal covariance certificates

The exact primal-dual gap splits into globally valid affine slack and
nonnegative coordinate slacks. At an optimum all these slacks vanish.
Consequently nonzero weights require saturated measurements, and universal
diagonal channels receive zero weight. The same weights support the value
function under simultaneous changes of measurements and tolerance.
-/

open MeasureTheory Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided
variable {ι : Type*}

/-- The excess above the worst allowed contribution of one measured coordinate. -/
def paperCovarianceCoordinateSlack
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0)
    (A : PaperCovarianceAffineMinorant c F G s)
    (ν : PaperObservedSpectralCompletion c F) (k : s) : ℝ :=
  A.1.1 k * (paperObservedPhaseCovariances c F ν k.1 -
    paperObservedPhaseCovariances c F μ k.1) + r * |A.1.1 k|

theorem paperCovarianceCoordinateSlack_nonneg
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0)
    (A : PaperCovarianceAffineMinorant c F G s)
    (ν : paperCovarianceWindow c F μ s r) (k : s) :
    0 ≤ paperCovarianceCoordinateSlack c F G μ s r A ν.1 k := by
  have hk := ν.2 k.1 k.2
  have hm := mul_le_mul_of_nonneg_left hk (abs_nonneg (A.1.1 k))
  have ha := neg_abs_le (A.1.1 k * (paperObservedPhaseCovariances c F ν.1 k.1 -
    paperObservedPhaseCovariances c F μ k.1))
  rw [abs_mul] at ha
  unfold paperCovarianceCoordinateSlack
  nlinarith

/-- An exact decomposition valid for every law and every globally valid affine bound. -/
theorem paperCovariancePrimalDualGap_decomposition
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0)
    (A : PaperCovarianceAffineMinorant c F G s)
    (ν : PaperObservedSpectralCompletion c F) :
    paperPerturbedGammaExpectation G ν.1 - paperCovarianceRobustAffineValue c F G μ s r A =
      (paperPerturbedGammaExpectation G ν.1 -
        (A.1.2 + ∑ k : s, A.1.1 k * paperObservedPhaseCovariances c F ν k.1)) +
      ∑ k : s, paperCovarianceCoordinateSlack c F G μ s r A ν k := by
  simp only [paperCovarianceCoordinateSlack, paperCovarianceRobustAffineValue,
    mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

private theorem optimal_complementarity
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : {r : ℝ≥0 // 0 < r}) :
    let A := paperCovarianceOptimalAffineMinorant c F G μ s r
    let ν := paperCovarianceWindowGammaMinimizer c F G μ s r.1
    (A.1.2 + ∑ k : s, A.1.1 k * paperObservedPhaseCovariances c F ν k.1 =
      paperPerturbedGammaExpectation G ν.1) ∧
    ∀ k : s, paperCovarianceCoordinateSlack c F G μ s r.1 A ν k = 0 := by
  classical
  dsimp only
  let A := paperCovarianceOptimalAffineMinorant c F G μ s r
  let ν := paperCovarianceWindowGammaMinimizer c F G μ s r.1
  have hwin := paperCovarianceWindowGammaMinimizer_mem c F G μ s r.1
  have hn (k : s) : 0 ≤ paperCovarianceCoordinateSlack c F G μ s r.1 A ν k :=
    paperCovarianceCoordinateSlack_nonneg c F G μ s r.1 A ⟨ν, hwin⟩ k
  have hs : 0 ≤ ∑ k : s, paperCovarianceCoordinateSlack c F G μ s r.1 A ν k :=
    Finset.sum_nonneg fun k _ => hn k
  have he := paperCovariancePrimalDualGap_decomposition c F G μ s r.1 A ν
  have hv := A.2 ν
  have hz : paperPerturbedGammaExpectation G ν.1 -
      paperCovarianceRobustAffineValue c F G μ s r.1 A = 0 := by
    rw [paperCovarianceOptimalAffineMinorant_value]
    exact sub_self _
  rw [hz] at he
  have hsum : (∑ k : s, paperCovarianceCoordinateSlack c F G μ s r.1 A ν k) = 0 := by
    linarith
  refine ⟨by linarith, ?_⟩
  exact fun k => (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hsum k
    (Finset.mem_univ k)

/-- The optimal affine bound touches the energy at the attained window minimizer. -/
theorem paperCovarianceOptimalAffineMinorant_tight
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : {r : ℝ≥0 // 0 < r}) :
    let A := paperCovarianceOptimalAffineMinorant c F G μ s r
    let ν := paperCovarianceWindowGammaMinimizer c F G μ s r.1
    A.1.2 + ∑ k : s, A.1.1 k * paperObservedPhaseCovariances c F ν k.1 =
      paperPerturbedGammaExpectation G ν.1 :=
  (optimal_complementarity c F G μ s r).1

/-- Each optimal coefficient realizes its exact worst-case coordinate contribution. -/
theorem paperCovarianceOptimalAffineMinorant_coordinate
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : {r : ℝ≥0 // 0 < r}) (k : s) :
    let A := paperCovarianceOptimalAffineMinorant c F G μ s r
    let ν := paperCovarianceWindowGammaMinimizer c F G μ s r.1
    A.1.1 k * (paperObservedPhaseCovariances c F ν k.1 -
      paperObservedPhaseCovariances c F μ k.1) = -(r.1 : ℝ) * |A.1.1 k| := by
  have h := (optimal_complementarity c F G μ s r).2 k
  unfold paperCovarianceCoordinateSlack at h
  dsimp only
  linarith

/-- Positive optimal weights select the lower face of the measurement window. -/
theorem paperCovarianceOptimalAffineMinorant_positive_face
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : {r : ℝ≥0 // 0 < r})
    (k : {k : s // 0 < (paperCovarianceOptimalAffineMinorant c F G μ s r).1.1 k}) :
    paperObservedPhaseCovariances c F (paperCovarianceWindowGammaMinimizer c F G μ s r.1) k.1.1 =
      paperObservedPhaseCovariances c F μ k.1.1 - r.1 := by
  have h := paperCovarianceOptimalAffineMinorant_coordinate c F G μ s r k.1
  dsimp only at h
  rw [abs_of_pos k.2] at h
  have hz : (paperCovarianceOptimalAffineMinorant c F G μ s r).1.1 k.1 *
      (paperObservedPhaseCovariances c F (paperCovarianceWindowGammaMinimizer c F G μ s r.1) k.1.1 -
        paperObservedPhaseCovariances c F μ k.1.1 + (r.1 : ℝ)) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with hw | hd
  · exact (ne_of_gt k.2 hw).elim
  · linarith

/-- Negative optimal weights select the upper face of the measurement window. -/
theorem paperCovarianceOptimalAffineMinorant_negative_face
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : {r : ℝ≥0 // 0 < r})
    (k : {k : s // (paperCovarianceOptimalAffineMinorant c F G μ s r).1.1 k < 0}) :
    paperObservedPhaseCovariances c F (paperCovarianceWindowGammaMinimizer c F G μ s r.1) k.1.1 =
      paperObservedPhaseCovariances c F μ k.1.1 + r.1 := by
  have h := paperCovarianceOptimalAffineMinorant_coordinate c F G μ s r k.1
  dsimp only at h
  rw [abs_of_neg k.2] at h
  have hz : (paperCovarianceOptimalAffineMinorant c F G μ s r).1.1 k.1 *
      (paperObservedPhaseCovariances c F (paperCovarianceWindowGammaMinimizer c F G μ s r.1) k.1.1 -
        paperObservedPhaseCovariances c F μ k.1.1 - (r.1 : ℝ)) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with hw | hd
  · exact (ne_of_lt k.2 hw).elim
  · linarith

/-- A measurement strictly inside its allowed interval has zero optimal weight. -/
theorem paperCovarianceOptimalAffineMinorant_interior_zero
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : {r : ℝ≥0 // 0 < r})
    (k : {k : s // |paperObservedPhaseCovariances c F
        (paperCovarianceWindowGammaMinimizer c F G μ s r.1) k.1 -
      paperObservedPhaseCovariances c F μ k.1| < (r.1 : ℝ)}) :
    (paperCovarianceOptimalAffineMinorant c F G μ s r).1.1 k.1 = 0 := by
  let w : ℝ := (paperCovarianceOptimalAffineMinorant c F G μ s r).1.1 k.1
  let d : ℝ := paperObservedPhaseCovariances c F
    (paperCovarianceWindowGammaMinimizer c F G μ s r.1) k.1.1 -
    paperObservedPhaseCovariances c F μ k.1.1
  let ρ : ℝ := r.1
  have hρ : 0 ≤ ρ := r.1.2
  have hk : |d| < ρ := k.2
  have he : w * d = -ρ * |w| :=
    paperCovarianceOptimalAffineMinorant_coordinate c F G μ s r k.1
  have h : |w| * |d| = ρ * |w| := by
    calc
      _ = |w * d| := (abs_mul w d).symm
      _ = |(-ρ) * (|w|)| := congrArg abs he
      _ = _ := by rw [abs_mul, abs_neg, abs_of_nonneg hρ, abs_abs]
  have hz : |w| * (ρ - |d|) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with hw | hd
  · exact abs_eq_zero.mp hw
  · exact (ne_of_gt (sub_pos.mpr hk) hd).elim

/-- Universal diagonal phase channels automatically receive zero optimal weight. -/
theorem paperCovarianceOptimalAffineMinorant_diagonal_zero
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : {r : ℝ≥0 // 0 < r})
    (k : {k : s // k.1.1 = k.1.2.1}) :
    (paperCovarianceOptimalAffineMinorant c F G μ s r).1.1 k.1 = 0 := by
  let ν := paperCovarianceWindowGammaMinimizer c F G μ s r.1
  have hd (n : LogIndex) (b : Bool) :
      paperObservedPhaseCovariances c F ν (n, n, b) = paperObservedPhaseCovariances c F μ (n, n, b) := by
    cases b
    · exact (paperObservedPhaseCovariances_diagonal c F ν n).1.trans
        (paperObservedPhaseCovariances_diagonal c F μ n).1.symm
    · exact (paperObservedPhaseCovariances_diagonal c F ν n).2.trans
        (paperObservedPhaseCovariances_diagonal c F μ n).2.symm
  have hc : paperObservedPhaseCovariances c F ν k.1.1 = paperObservedPhaseCovariances c F μ k.1.1 := by
    rcases k with ⟨⟨⟨n, m, b⟩, hk⟩, hdiag⟩
    change n = m at hdiag
    subst m
    exact hd n b
  have hi : |paperObservedPhaseCovariances c F ν k.1.1 -
      paperObservedPhaseCovariances c F μ k.1.1| < (r.1 : ℝ) := by
    rw [hc, sub_self, abs_zero]
    exact_mod_cast r.2
  exact paperCovarianceOptimalAffineMinorant_interior_zero c F G μ s r ⟨k.1, hi⟩

/-- Optimal weights give a supporting affine bound for simultaneous changes
of measured covariances and tolerance. -/
theorem paperCovarianceOptimalAffineMinorant_supports_parameters
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ ν : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : {r : ℝ≥0 // 0 < r}) (q : ℝ≥0) :
    let A := paperCovarianceOptimalAffineMinorant c F G μ s r
    paperCovarianceGammaCertificate c F G μ s r.1 +
        (∑ k : s, A.1.1 k * (paperObservedPhaseCovariances c F ν k.1 -
          paperObservedPhaseCovariances c F μ k.1)) -
        ((q : ℝ) - (r.1 : ℝ)) * ∑ k : s, |A.1.1 k| ≤
      paperCovarianceGammaCertificate c F G ν s q := by
  dsimp only
  let A := paperCovarianceOptimalAffineMinorant c F G μ s r
  have he := paperCovarianceOptimalAffineMinorant_value c F G μ s r
  calc
    _ = paperCovarianceRobustAffineValue c F G ν s q A := by
      rw [← he]
      unfold paperCovarianceRobustAffineValue
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      ring
    _ ≤ _ := paperCovarianceRobustAffineValue_le_certificate c F G ν s q A

end RHTower.WeilWorkPBAP
