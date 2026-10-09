import GaloisForLFunctions.RHTower.WeilPaperCovarianceMeasurementStability

/-!
# Attained finite covariance dual certificates

A positive tolerance bounds the weights of any competitive affine minorant.
Centering its intercept at the measured law yields a compact coefficient set,
so the exact finite-window dual supremum is attained. The selected optimum has
both a sharp target-dependent weight bound and the uniform paid-budget bound.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided
variable {ι : Type*}

/-- The paid energy budget bounds the entire range of perturbed gamma values
on the observed completion. -/
theorem abs_paperPerturbedGammaExpectation_sub_le_oscillation
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ ν : PaperObservedSpectralCompletion c F) :
    |paperPerturbedGammaExpectation G μ.1 - paperPerturbedGammaExpectation G ν.1| ≤
      paperCovarianceEnergyOscillation c G := by
  have h (μ ν : PaperObservedSpectralCompletion c F) :
      paperPerturbedGammaExpectation G μ.1 - paperPerturbedGammaExpectation G ν.1 ≤
        paperCovarianceEnergyOscillation c G := by
    have hu := paperObservedSpectralCompletion_gammaCost_le c F μ
    have hl := paperCompletedGammaExpectation_lower (paperPoleCompensatedEnergy c.1)
      ⟨ν.1, paperObservedSpectralCompletion_subset_budget c F ν.2⟩
    have hi := G.norm_integral_le_norm (μ.1 : Measure ℝ)
    have hj := G.norm_integral_le_norm (ν.1 : Measure ℝ)
    rw [Real.norm_eq_abs] at hi hj
    change _ ≤ paperPoleCompensatedEnergy c.1 + 2 * ‖G‖
    unfold paperPerturbedGammaExpectation
    linarith [(abs_le.mp hi).2, (abs_le.mp hj).1]
  exact abs_le.mpr ⟨by linarith [h ν μ], h μ ν⟩

/-- The robust value when the intercept records the affine value at the center. -/
def paperCenteredCovarianceDualValue
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) (p : (s → ℝ) × ℝ) : ℝ :=
  p.2 - r * ∑ k : s, |p.1 k|

/-- Centered globally valid minorants competitive with the attained global minimum. -/
def paperCenteredCovarianceDualSet
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) : Set ((s → ℝ) × ℝ) :=
  {p | (∀ ν : PaperObservedSpectralCompletion c F,
      p.2 + ∑ k : s, p.1 k * (paperObservedPhaseCovariances c F ν k.1 -
        paperObservedPhaseCovariances c F μ k.1) ≤ paperPerturbedGammaExpectation G ν.1) ∧
    paperObservedGammaValue c F G ≤ paperCenteredCovarianceDualValue s r p}

private theorem continuous_centeredValue
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) :
    Continuous (paperCenteredCovarianceDualValue s r) :=
  continuous_snd.sub (continuous_const.mul (continuous_finsetSum _ fun k _ =>
    ((continuous_apply k).comp continuous_fst).abs))

theorem paperCenteredCovarianceDualSet_nonempty
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) :
    (paperCenteredCovarianceDualSet c F G μ s r).Nonempty := by
  refine ⟨(0, paperObservedGammaValue c F G), ?_, ?_⟩
  · intro ν
    simpa using paperObservedGammaValue_le c F G ν
  · simp [paperCenteredCovarianceDualValue]

theorem isClosed_paperCenteredCovarianceDualSet
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) :
    IsClosed (paperCenteredCovarianceDualSet c F G μ s r) := by
  have hc : IsClosed {p : (s → ℝ) × ℝ | ∀ ν : PaperObservedSpectralCompletion c F,
      p.2 + ∑ k : s, p.1 k * (paperObservedPhaseCovariances c F ν k.1 -
        paperObservedPhaseCovariances c F μ k.1) ≤ paperPerturbedGammaExpectation G ν.1} := by
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro ν
    exact isClosed_le (continuous_snd.add (continuous_finsetSum _ fun k _ =>
      ((continuous_apply k).comp continuous_fst).mul continuous_const)) continuous_const
  exact hc.inter (isClosed_le continuous_const (continuous_centeredValue s r))

/-- Positive tolerance confines all competitive globally valid coefficients
to a compact finite box. -/
theorem isCompact_paperCenteredCovarianceDualSet
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : {r : ℝ≥0 // 0 < r}) :
    IsCompact (paperCenteredCovarianceDualSet c F G μ s r.1) := by
  classical
  let V := paperObservedGammaValue c F G
  let J := paperPerturbedGammaExpectation G μ.1
  let C := (J - V) / (r.1 : ℝ)
  have hr : 0 < (r.1 : ℝ) := by exact_mod_cast r.2
  have hsub : paperCenteredCovarianceDualSet c F G μ s r.1 ⊆
      Icc (fun _ : s => -C) (fun _ => C) ×ˢ Icc V J := by
    intro p hp
    have hu : p.2 ≤ J := by simpa using hp.1 μ
    have hv : V ≤ p.2 - (r.1 : ℝ) * ∑ k : s, |p.1 k| := hp.2
    have hn : 0 ≤ ∑ k : s, |p.1 k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hsum : (∑ k : s, |p.1 k|) ≤ C := by
      apply (le_div_iff₀ hr).mpr
      dsimp [J, V] at hu hv ⊢
      nlinarith
    have hk (k : s) : |p.1 k| ≤ C :=
      (Finset.single_le_sum (fun j _ => abs_nonneg (p.1 j)) (Finset.mem_univ k)).trans hsum
    exact ⟨⟨fun k => (abs_le.mp (hk k)).1, fun k => (abs_le.mp (hk k)).2⟩,
      by nlinarith, hu⟩
  exact (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
    (isClosed_paperCenteredCovarianceDualSet c F G μ s r.1) hsub

/-- Convert centered coefficients into a certified original affine minorant. -/
def paperCenteredCovarianceMinorant
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0)
    (p : paperCenteredCovarianceDualSet c F G μ s r) : PaperCovarianceAffineMinorant c F G s :=
  ⟨(p.1.1, p.1.2 - ∑ k : s, p.1.1 k * paperObservedPhaseCovariances c F μ k.1), by
    intro ν
    have h := p.2.1 ν
    simp_rw [mul_sub, Finset.sum_sub_distrib] at h
    change p.1.2 - (∑ k : s, p.1.1 k * paperObservedPhaseCovariances c F μ k.1) +
      (∑ k : s, p.1.1 k * paperObservedPhaseCovariances c F ν k.1) ≤ _
    linarith⟩

theorem paperCenteredCovarianceMinorant_value
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0)
    (p : paperCenteredCovarianceDualSet c F G μ s r) :
    paperCovarianceRobustAffineValue c F G μ s r (paperCenteredCovarianceMinorant c F G μ s r p) =
      paperCenteredCovarianceDualValue s r p.1 := by
  change (p.1.2 - ∑ k : s, p.1.1 k * paperObservedPhaseCovariances c F μ k.1) +
    (∑ k : s, p.1.1 k * paperObservedPhaseCovariances c F μ k.1) -
    (r : ℝ) * ∑ k : s, |p.1.1 k| = p.1.2 - (r : ℝ) * ∑ k : s, |p.1.1 k|
  ring

/-- With positive measurement tolerance the exact affine dual bound is
attained by finite coefficients. -/
theorem exists_paperCovarianceOptimalAffineMinorant
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : {r : ℝ≥0 // 0 < r}) :
    ∃ A : PaperCovarianceAffineMinorant c F G s,
      paperCovarianceRobustAffineValue c F G μ s r.1 A = paperCovarianceGammaCertificate c F G μ s r.1 := by
  classical
  obtain ⟨p, hp, hmax⟩ := (isCompact_paperCenteredCovarianceDualSet c F G μ s r).exists_isMaxOn
    (paperCenteredCovarianceDualSet_nonempty c F G μ s r.1) (continuous_centeredValue s r.1).continuousOn
  let A := paperCenteredCovarianceMinorant c F G μ s r.1 ⟨p, hp⟩
  have hA := paperCenteredCovarianceMinorant_value c F G μ s r.1 ⟨p, hp⟩
  refine ⟨A, le_antisymm (paperCovarianceRobustAffineValue_le_certificate c F G μ s r.1 A) ?_⟩
  by_contra hn
  have hlt := lt_of_not_ge hn
  let δ : {d : ℝ // 0 < d} :=
    ⟨(paperCovarianceGammaCertificate c F G μ s r.1 - paperCovarianceRobustAffineValue c F G μ s r.1 A) / 2,
      by linarith⟩
  obtain ⟨B, hB⟩ := exists_paperCovarianceRobustAffineApproximation c F G μ s r.1 δ
  have hab : paperCovarianceRobustAffineValue c F G μ s r.1 A <
      paperCovarianceRobustAffineValue c F G μ s r.1 B := by
    dsimp [δ] at hB
    linarith
  let q : (s → ℝ) × ℝ :=
    (B.1.1, B.1.2 + ∑ k : s, B.1.1 k * paperObservedPhaseCovariances c F μ k.1)
  have hqval : paperCenteredCovarianceDualValue s r.1 q = paperCovarianceRobustAffineValue c F G μ s r.1 B := rfl
  have hq : q ∈ paperCenteredCovarianceDualSet c F G μ s r.1 := by
    constructor
    · intro ν
      have h := B.2 ν
      change B.1.2 + (∑ k : s, B.1.1 k * paperObservedPhaseCovariances c F μ k.1) +
        (∑ k : s, B.1.1 k * (paperObservedPhaseCovariances c F ν k.1 -
          paperObservedPhaseCovariances c F μ k.1)) ≤ _
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      linarith
    · rw [hqval]
      have hv : paperObservedGammaValue c F G ≤ paperCovarianceRobustAffineValue c F G μ s r.1 A :=
        hp.2.trans_eq hA.symm
      exact hv.trans hab.le
  have hm : paperCenteredCovarianceDualValue s r.1 q ≤
      paperCenteredCovarianceDualValue s r.1 p := hmax hq
  rw [hqval, ← hA] at hm
  exact (not_lt_of_ge hm) hab

/-- A selected exact finite affine certificate for each positive-tolerance window. -/
def paperCovarianceOptimalAffineMinorant
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : {r : ℝ≥0 // 0 < r}) :
    PaperCovarianceAffineMinorant c F G s :=
  Classical.choose (exists_paperCovarianceOptimalAffineMinorant c F G μ s r)

theorem paperCovarianceOptimalAffineMinorant_value
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : {r : ℝ≥0 // 0 < r}) :
    paperCovarianceRobustAffineValue c F G μ s r.1 (paperCovarianceOptimalAffineMinorant c F G μ s r) =
      paperCovarianceGammaCertificate c F G μ s r.1 :=
  Classical.choose_spec (exists_paperCovarianceOptimalAffineMinorant c F G μ s r)

/-- The optimum's total coefficient size is bounded by its actual energy gap
at the measured law divided by tolerance. -/
theorem paperCovarianceOptimalAffineMinorant_weight_bound
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : {r : ℝ≥0 // 0 < r}) :
    (∑ k : s, |(paperCovarianceOptimalAffineMinorant c F G μ s r).1.1 k|) ≤
      (paperPerturbedGammaExpectation G μ.1 - paperCovarianceGammaCertificate c F G μ s r.1) / r.1 := by
  let A := paperCovarianceOptimalAffineMinorant c F G μ s r
  have h := A.2 μ
  have he := paperCovarianceOptimalAffineMinorant_value c F G μ s r
  change A.1.2 + (∑ k : s, A.1.1 k * paperObservedPhaseCovariances c F μ k.1) -
    (r.1 : ℝ) * ∑ k : s, |A.1.1 k| = _ at he
  have hr : 0 < (r.1 : ℝ) := by exact_mod_cast r.2
  apply (le_div_iff₀ hr).mpr
  change (∑ k : s, |A.1.1 k|) * (r.1 : ℝ) ≤ _
  nlinarith

/-- The original native budget supplies a uniform coefficient bound. -/
theorem paperCovarianceOptimalAffineMinorant_uniform_weight_bound
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : {r : ℝ≥0 // 0 < r}) :
    (∑ k : s, |(paperCovarianceOptimalAffineMinorant c F G μ s r).1.1 k|) ≤
      paperCovarianceUniformSlopeBound c G r := by
  have h := abs_paperPerturbedGammaExpectation_sub_le_oscillation c F G μ
    (paperCovarianceWindowGammaMinimizer c F G μ s r.1)
  have hg := (le_abs_self _).trans h
  exact (paperCovarianceOptimalAffineMinorant_weight_bound c F G μ s r).trans
    (div_le_div_of_nonneg_right hg r.1.2)

end RHTower.WeilWorkPBAP
