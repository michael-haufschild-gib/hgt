import GaloisForLFunctions.RHTower.WeilPaperFiniteCovarianceControl

/-!
# Finite covariance certificates for the actual gamma objective

Every finite closed covariance window is nonempty and compact, hence the actual
lower semicontinuous gamma objective attains its minimum there. These finite
measurement certificates recover the exact objective as their supremum. This is
one-sided certification; it requires no continuity of the unbounded gamma weight.
-/

open MeasureTheory Filter Set Topology Uniformity
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

private theorem finite_coordinate_neighborhood {κ : Type*} (K : Set (κ → ℝ))
    (x : K) (U : Set K) (hU : U ∈ 𝓝 x) :
    ∃ s : Finset κ, ∃ ε : {r : ℝ // 0 < r}, ∀ y : K,
      (∀ k ∈ s, |y.1 k - x.1 k| < ε.1) → y ∈ U := by
  classical
  have hb : (𝓝 (0 : κ → ℝ)).HasBasis
      (fun q : Set κ × ℝ => q.1.Finite ∧ 0 < q.2)
      (fun q => q.1.pi (fun _ => Metric.ball 0 q.2)) := by
    rw [nhds_pi]
    exact Metric.nhds_basis_ball.pi_self
  rw [nhds_subtype, ← nhds_translation_sub x.1, comap_comap] at hU
  obtain ⟨⟨s, ε⟩, ⟨hs, hε⟩, hsub⟩ := (hb.comap _).mem_iff.mp hU
  refine ⟨hs.toFinset, ⟨ε, hε⟩, fun y hxy => @hsub y ?_⟩
  change ∀ k ∈ s, (y.1 - x.1) k ∈ Metric.ball 0 ε
  intro k hk
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, Pi.sub_apply]
    using hxy k (hs.mem_toFinset.mpr hk)

variable {ι : Type*}

/-- Finitely many covariance measurements certify the gamma objective from below
at any fixed completed law, to arbitrary prescribed accuracy. -/
theorem exists_paperGamma_finiteCovarianceLowerBound
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F) (δ : {r : ℝ // 0 < r}) :
    ∃ s : Finset (LogIndex × LogIndex × Bool), ∃ ε : {r : ℝ // 0 < r},
      ∀ ν : PaperObservedSpectralCompletion c F,
        (∀ k ∈ s, |paperObservedPhaseCovariances c F ν k -
          paperObservedPhaseCovariances c F μ k| < ε.1) →
        paperPerturbedGammaExpectation G μ.1 - δ.1 < paperPerturbedGammaExpectation G ν.1 := by
  let K := Set.range (paperObservedPhaseCovariances c F)
  let E : K → ℝ := fun q =>
    paperPerturbedGammaExpectation G (paperPhaseCovarianceRecovery c F q).1
  have hE : LowerSemicontinuous E :=
    (lowerSemicontinuous_paperObservedPerturbedGammaExpectation c F G).comp
      (paperPhaseCovarianceRecovery c F).continuous
  let x := paperPhaseCovarianceRecoveryHomeomorph c F μ
  have hx : E x = paperPerturbedGammaExpectation G μ.1 :=
    congrArg (fun ν : PaperObservedSpectralCompletion c F =>
      paperPerturbedGammaExpectation G ν.1) (paperPhaseCovarianceRecovery_roundtrip c F μ)
  have hU : {q : K | paperPerturbedGammaExpectation G μ.1 - δ.1 < E q} ∈ 𝓝 x := by
    apply hE x
    rw [hx]
    exact sub_lt_self _ δ.2
  obtain ⟨s, ε, h⟩ := finite_coordinate_neighborhood K x _ hU
  refine ⟨s, ε, fun ν hν => ?_⟩
  have hp := h (paperPhaseCovarianceRecoveryHomeomorph c F ν) hν
  change paperPerturbedGammaExpectation G μ.1 - δ.1 < E
    (paperPhaseCovarianceRecoveryHomeomorph c F ν) at hp
  have hνE : E (paperPhaseCovarianceRecoveryHomeomorph c F ν) =
      paperPerturbedGammaExpectation G ν.1 :=
    congrArg (fun η : PaperObservedSpectralCompletion c F =>
      paperPerturbedGammaExpectation G η.1) (paperPhaseCovarianceRecovery_roundtrip c F ν)
  rwa [hνE] at hp

/-- Completed laws consistent with finitely many covariance measurements and a
nonnegative error tolerance. -/
def paperCovarianceWindow (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) :
    Set (PaperObservedSpectralCompletion c F) :=
  {ν | ∀ k ∈ s, |paperObservedPhaseCovariances c F ν k -
    paperObservedPhaseCovariances c F μ k| ≤ r}

@[simp] theorem paperCovarianceWindow_self
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) :
    μ ∈ paperCovarianceWindow c F μ s r := by
  intro k _
  change |paperObservedPhaseCovariances c F μ k - paperObservedPhaseCovariances c F μ k| ≤ (r : ℝ)
  rw [sub_self, abs_zero]
  exact r.2

/-- Measurement windows are closed in the already proved compact completion. -/
theorem isClosed_paperCovarianceWindow
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) :
    IsClosed (paperCovarianceWindow c F μ s r) := by
  unfold paperCovarianceWindow
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro k
  apply isClosed_iInter
  intro _
  exact isClosed_le (((continuous_apply k).comp
    (paperObservedPhaseCovariances c F).continuous).sub continuous_const).abs continuous_const

theorem isCompact_paperCovarianceWindow
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) :
    IsCompact (paperCovarianceWindow c F μ s r) :=
  (isClosed_paperCovarianceWindow c F μ s r).isCompact

/-- Every finite measurement window has an actual attained gamma minimum. -/
theorem exists_paperCovarianceWindow_gammaMinimizer
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) :
    ∃ ν ∈ paperCovarianceWindow c F μ s r,
      ∀ η ∈ paperCovarianceWindow c F μ s r,
        paperPerturbedGammaExpectation G ν.1 ≤ paperPerturbedGammaExpectation G η.1 :=
  LowerSemicontinuousOn.exists_isMinOn
    ⟨μ, paperCovarianceWindow_self c F μ s r⟩ (isCompact_paperCovarianceWindow c F μ s r)
    ((lowerSemicontinuous_paperObservedPerturbedGammaExpectation c F G).lowerSemicontinuousOn _)

/-- A minimizing law consistent with the finite covariance window. -/
def paperCovarianceWindowGammaMinimizer
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) :
    PaperObservedSpectralCompletion c F :=
  Classical.choose (exists_paperCovarianceWindow_gammaMinimizer c F G μ s r)

/-- The best lower bound certified by a finite covariance window. -/
def paperCovarianceGammaCertificate
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) : ℝ :=
  paperPerturbedGammaExpectation G (paperCovarianceWindowGammaMinimizer c F G μ s r).1

theorem paperCovarianceWindowGammaMinimizer_mem
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) :
    paperCovarianceWindowGammaMinimizer c F G μ s r ∈ paperCovarianceWindow c F μ s r :=
  (Classical.choose_spec (exists_paperCovarianceWindow_gammaMinimizer c F G μ s r)).1

/-- The certificate bounds every law compatible with its measurements. -/
theorem paperCovarianceGammaCertificate_le
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0)
    (ν : paperCovarianceWindow c F μ s r) :
    paperCovarianceGammaCertificate c F G μ s r ≤ paperPerturbedGammaExpectation G ν.1.1 :=
  (Classical.choose_spec (exists_paperCovarianceWindow_gammaMinimizer c F G μ s r)).2 ν.1 ν.2

/-- In particular, each certificate is a valid lower bound on the measured law. -/
theorem paperCovarianceGammaCertificate_le_target
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) :
    paperCovarianceGammaCertificate c F G μ s r ≤ paperPerturbedGammaExpectation G μ.1 :=
  paperCovarianceGammaCertificate_le c F G μ s r ⟨μ, paperCovarianceWindow_self c F μ s r⟩


/-- Every finite certificate refines the unconstrained minimum over the completion. -/
theorem paperObservedGammaValue_le_covarianceCertificate
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) :
    paperObservedGammaValue c F G ≤ paperCovarianceGammaCertificate c F G μ s r :=
  paperObservedGammaValue_le c F G (paperCovarianceWindowGammaMinimizer c F G μ s r)

/-- With no measurements the certificate is exactly the unconstrained gamma minimum. -/
@[simp] theorem paperCovarianceGammaCertificate_empty
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F) (r : ℝ≥0) :
    paperCovarianceGammaCertificate c F G μ ∅ r = paperObservedGammaValue c F G := by
  apply le_antisymm
  · exact paperCovarianceGammaCertificate_le c F G μ ∅ r
      ⟨paperObservedGammaMinimizer c F G, by
        intro k hk
        simp at hk⟩
  · exact paperObservedGammaValue_le_covarianceCertificate c F G μ ∅ r

/-- Discarding the universal diagonal leaves the entire measurement window unchanged. -/
theorem paperCovarianceWindow_offDiagonal
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) :
    paperCovarianceWindow c F μ (s.filter fun k => k.1 ≠ k.2.1) r =
      paperCovarianceWindow c F μ s r := by
  classical
  ext ν
  constructor
  · intro h
    rintro ⟨n, m, b⟩ hk
    by_cases hnm : n = m
    · subst m
      have heq : paperObservedPhaseCovariances c F ν (n, n, b) =
          paperObservedPhaseCovariances c F μ (n, n, b) := by
        cases b
        · exact (paperObservedPhaseCovariances_diagonal c F ν n).1.trans
            (paperObservedPhaseCovariances_diagonal c F μ n).1.symm
        · exact (paperObservedPhaseCovariances_diagonal c F ν n).2.trans
            (paperObservedPhaseCovariances_diagonal c F μ n).2.symm
      change |paperObservedPhaseCovariances c F ν (n, n, b) -
        paperObservedPhaseCovariances c F μ (n, n, b)| ≤ (r : ℝ)
      rw [heq, sub_self, abs_zero]
      exact r.2
    · exact h (n, m, b) (Finset.mem_filter.mpr ⟨hk, hnm⟩)
  · intro h k hk
    exact h k (Finset.mem_filter.mp hk).1

/-- Diagonal measurements cannot improve the gamma certificate. -/
theorem paperCovarianceGammaCertificate_offDiagonal
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool)) (r : ℝ≥0) :
    paperCovarianceGammaCertificate c F G μ (s.filter fun k => k.1 ≠ k.2.1) r =
      paperCovarianceGammaCertificate c F G μ s r := by
  classical
  apply le_antisymm
  · apply paperCovarianceGammaCertificate_le c F G μ _ r
      ⟨paperCovarianceWindowGammaMinimizer c F G μ s r, ?_⟩
    rw [paperCovarianceWindow_offDiagonal]
    exact paperCovarianceWindowGammaMinimizer_mem c F G μ s r
  · apply paperCovarianceGammaCertificate_le c F G μ s r
      ⟨paperCovarianceWindowGammaMinimizer c F G μ (s.filter fun k => k.1 ≠ k.2.1) r, ?_⟩
    rw [← paperCovarianceWindow_offDiagonal c F μ s r]
    exact paperCovarianceWindowGammaMinimizer_mem c F G μ _ r

/-- More coordinates and smaller error tolerance can only improve the certificate. -/
theorem paperCovarianceGammaCertificate_refinement
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F)
    (s : Finset (LogIndex × LogIndex × Bool))
    (t : {t : Finset (LogIndex × LogIndex × Bool) // s ⊆ t})
    (r : ℝ≥0) (q : {q : ℝ≥0 // q ≤ r}) :
    paperCovarianceGammaCertificate c F G μ s r ≤
      paperCovarianceGammaCertificate c F G μ t.1 q.1 := by
  let ν := paperCovarianceWindowGammaMinimizer c F G μ t.1 q.1
  have hν : ν ∈ paperCovarianceWindow c F μ s r := by
    intro k hk
    exact ((paperCovarianceWindowGammaMinimizer_mem c F G μ t.1 q.1) k (t.2 hk)).trans q.2
  exact paperCovarianceGammaCertificate_le c F G μ s r ⟨ν, hν⟩

/-- Positive-tolerance finite certificates approach the exact gamma objective
from below, without assuming gamma expectation is continuous. -/
theorem exists_paperCovarianceGammaCertificate_approximation
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F) (δ : {r : ℝ // 0 < r}) :
    ∃ s : Finset (LogIndex × LogIndex × Bool), ∃ r : {r : ℝ≥0 // 0 < r},
      paperPerturbedGammaExpectation G μ.1 - δ.1 <
        paperCovarianceGammaCertificate c F G μ s r.1 := by
  obtain ⟨s, ε, h⟩ := exists_paperGamma_finiteCovarianceLowerBound c F G μ δ
  let r : ℝ≥0 := ⟨ε.1 / 2, (half_pos ε.2).le⟩
  refine ⟨s, ⟨r, half_pos ε.2⟩, ?_⟩
  apply h (paperCovarianceWindowGammaMinimizer c F G μ s r)
  intro k hk
  exact ((paperCovarianceWindowGammaMinimizer_mem c F G μ s r) k hk).trans_lt
    (half_lt_self ε.2)


/-- Arbitrarily accurate lower certificates use only finitely many off-diagonal
covariances, each measured at a strictly positive tolerance. -/
theorem exists_paperOffDiagonalCovarianceGammaCertificate_approximation
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F) (δ : {r : ℝ // 0 < r}) :
    ∃ s : Finset (LogIndex × LogIndex × Bool), (∀ k ∈ s, k.1 ≠ k.2.1) ∧
      ∃ r : {r : ℝ≥0 // 0 < r},
        paperPerturbedGammaExpectation G μ.1 - δ.1 <
          paperCovarianceGammaCertificate c F G μ s r.1 := by
  classical
  obtain ⟨s, r, h⟩ := exists_paperCovarianceGammaCertificate_approximation c F G μ δ
  refine ⟨s.filter (fun k => k.1 ≠ k.2.1), fun k hk => (Finset.mem_filter.mp hk).2, r, ?_⟩
  rwa [paperCovarianceGammaCertificate_offDiagonal]

/-- The exact objective is the supremum of genuine finite positive-tolerance
covariance certificates. -/
theorem paperPerturbedGammaExpectation_eq_sSup_covarianceCertificates
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F) :
    paperPerturbedGammaExpectation G μ.1 =
      sSup (Set.range (fun p : Finset (LogIndex × LogIndex × Bool) × {r : ℝ≥0 // 0 < r} =>
        paperCovarianceGammaCertificate c F G μ p.1 p.2.1)) := by
  symm
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · exact ⟨_, ⟨(∅, ⟨1, zero_lt_one⟩), rfl⟩⟩
  · rintro _ ⟨⟨s, r⟩, rfl⟩
    exact paperCovarianceGammaCertificate_le_target c F G μ s r.1
  · intro a ha
    obtain ⟨s, r, h⟩ := exists_paperCovarianceGammaCertificate_approximation c F G μ
      ⟨paperPerturbedGammaExpectation G μ.1 - a, sub_pos.mpr ha⟩
    refine ⟨_, ⟨(s, r), rfl⟩, ?_⟩
    dsimp only at h
    linarith

end RHTower.WeilWorkPBAP
