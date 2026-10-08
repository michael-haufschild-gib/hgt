import GaloisForLFunctions.RHTower.WeilPaperObservedConvexity
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Finite affine covariance certificates for gamma energy

The finite covariance-energy epigraph is closed and convex. Strong separation
produces affine lower bounds valid on the entire actual completion, arbitrarily
close at a prescribed law. Expanding the finite linear functional gives literal
finite sums of off-diagonal covariance measurements. Their supremum is exactly
the paid gamma objective.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided
variable {ι : Type*}

/-- A finite restriction of the actual phase covariance array. -/
def paperFiniteCovarianceData (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (s : Finset (LogIndex × LogIndex × Bool)) :
    C(PaperObservedSpectralCompletion c F, s → ℝ) :=
  ⟨fun μ k => paperObservedPhaseCovariances c F μ k.1, continuous_pi fun k =>
    (continuous_apply k.1).comp (paperObservedPhaseCovariances c F).continuous⟩

/-- The finite covariance-energy epigraph, with a genuine completed-law witness. -/
def paperFiniteCovarianceEnergyEpigraph
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (s : Finset (LogIndex × LogIndex × Bool)) : Set ((s → ℝ) × ℝ) :=
  {p | ∃ μ : PaperObservedSpectralCompletion c F,
    paperFiniteCovarianceData c F s μ = p.1 ∧ paperPerturbedGammaExpectation G μ.1 ≤ p.2}

/-- Finite covariance and gamma-energy data retain the convexity of actual laws. -/
theorem convex_paperFiniteCovarianceEnergyEpigraph
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (s : Finset (LogIndex × LogIndex × Bool)) :
    Convex ℝ (paperFiniteCovarianceEnergyEpigraph c F G s) := by
  rintro x ⟨μ, hμ, hμE⟩ y ⟨ν, hν, hνE⟩ a b ha hb hab
  let t : Icc (0 : ℝ) 1 := ⟨b, hb, by linarith⟩
  refine ⟨paperObservedProbabilitySegment c F μ ν t, ?_, ?_⟩
  · funext k
    have hk := congrFun (paperObservedPhaseCovariances_segment c F μ ν t) k.1
    change paperObservedPhaseCovariances c F (paperObservedProbabilitySegment c F μ ν t) k.1 =
      a * x.1 k + b * y.1 k
    change _ = (1 - b) * paperObservedPhaseCovariances c F μ k.1 +
      b * paperObservedPhaseCovariances c F ν k.1 at hk
    have hm : paperObservedPhaseCovariances c F μ k.1 = x.1 k := congrFun hμ k
    have hn : paperObservedPhaseCovariances c F ν k.1 = y.1 k := congrFun hν k
    rw [hm, hn, show 1 - b = a by linarith] at hk
    exact hk
  · rw [paperPerturbedGammaExpectation_observedSegment]
    change (1 - b) * paperPerturbedGammaExpectation G μ.1 +
      b * paperPerturbedGammaExpectation G ν.1 ≤ a * x.2 + b * y.2
    rw [show 1 - b = a by linarith]
    exact add_le_add (mul_le_mul_of_nonneg_left hμE ha) (mul_le_mul_of_nonneg_left hνE hb)

/-- Compactness of completed laws and lower semicontinuity of gamma energy make
its finite covariance projection a closed epigraph. -/
theorem isClosed_paperFiniteCovarianceEnergyEpigraph
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (s : Finset (LogIndex × LogIndex × Bool)) :
    IsClosed (paperFiniteCovarianceEnergyEpigraph c F G s) := by
  let A : Set (((s → ℝ) × ℝ) × PaperObservedSpectralCompletion c F) :=
    {p | paperFiniteCovarianceData c F s p.2 = p.1.1 ∧
      paperPerturbedGammaExpectation G p.2.1 ≤ p.1.2}
  have hc : IsClosed {p : ((s → ℝ) × ℝ) × PaperObservedSpectralCompletion c F |
      paperFiniteCovarianceData c F s p.2 = p.1.1} :=
    isClosed_eq ((paperFiniteCovarianceData c F s).continuous.comp continuous_snd)
      (continuous_fst.comp continuous_fst)
  have he : IsClosed {p : ((s → ℝ) × ℝ) × PaperObservedSpectralCompletion c F |
      paperPerturbedGammaExpectation G p.2.1 ≤ p.1.2} :=
    (lowerSemicontinuous_paperObservedPerturbedGammaExpectation c F G).isClosed_epigraph.preimage
      (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
  have hA : IsClosed A := hc.inter he
  have heq : Prod.fst '' A = paperFiniteCovarianceEnergyEpigraph c F G s := by
    ext p
    constructor
    · rintro ⟨⟨q, μ⟩, h, rfl⟩
      exact ⟨μ, h⟩
    · rintro ⟨μ, h⟩
      exact ⟨(p, μ), h, rfl⟩
  rw [← heq]
  exact isClosedMap_fst_of_compactSpace A hA

private theorem linear_pair {κ : Type*} [Fintype κ]
    (L : ((κ → ℝ) × ℝ) →L[ℝ] ℝ) (x : κ → ℝ) (e : ℝ) :
    L (x, e) = L (x, 0) + e * L (0, 1) := by
  have h : (x, e) = (x, (0 : ℝ)) + e • ((0 : κ → ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [h, map_add, map_smul]
  rfl

/-- Every completed gamma value has arbitrarily sharp lower certificates that
are affine functions of finitely many actual covariance measurements. -/
theorem exists_paperFiniteAffineCovarianceLowerBound
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F) (δ : {r : ℝ // 0 < r}) :
    ∃ s : Finset (LogIndex × LogIndex × Bool), (∀ k ∈ s, k.1 ≠ k.2.1) ∧
      ∃ L : (s → ℝ) →L[ℝ] ℝ, ∃ b : ℝ,
      (∀ ν : PaperObservedSpectralCompletion c F,
        L (paperFiniteCovarianceData c F s ν) + b ≤ paperPerturbedGammaExpectation G ν.1) ∧
      paperPerturbedGammaExpectation G μ.1 - δ.1 < L (paperFiniteCovarianceData c F s μ) + b := by
  classical
  obtain ⟨s, hs, r, hr⟩ := exists_paperOffDiagonalCovarianceGammaCertificate_approximation c F G μ δ
  let a := paperPerturbedGammaExpectation G μ.1 - δ.1
  have hout : (paperFiniteCovarianceData c F s μ, a) ∉
      paperFiniteCovarianceEnergyEpigraph c F G s := by
    rintro ⟨ν, hν, hE⟩
    have hwin : ν ∈ paperCovarianceWindow c F μ s r.1 := by
      intro k hk
      have hp := congrFun hν ⟨k, hk⟩
      change paperObservedPhaseCovariances c F ν k = paperObservedPhaseCovariances c F μ k at hp
      rw [hp, sub_self, abs_zero]
      exact r.1.2
    have hv := paperCovarianceGammaCertificate_le c F G μ s r.1 ⟨ν, hwin⟩
    exact (not_lt_of_ge (hv.trans hE)) hr
  obtain ⟨T, u, hpoint, hsep⟩ := geometric_hahn_banach_point_closed
    (convex_paperFiniteCovarianceEnergyEpigraph c F G s)
    (isClosed_paperFiniteCovarianceEnergyEpigraph c F G s) hout
  let w := T (0, 1)
  have hμ := hsep (paperFiniteCovarianceData c F s μ, paperPerturbedGammaExpectation G μ.1)
    ⟨μ, rfl, le_rfl⟩
  rw [linear_pair] at hpoint hμ
  have hw : 0 < w := by
    by_contra hn
    have hn : w ≤ 0 := le_of_not_gt hn
    have hd : 0 ≤ paperPerturbedGammaExpectation G μ.1 - a := by
      dsimp [a]
      linarith [δ.2]
    have hp := mul_nonpos_of_nonneg_of_nonpos hd hn
    change (paperPerturbedGammaExpectation G μ.1 - a) * T (0, 1) ≤ 0 at hp
    nlinarith
  let L : (s → ℝ) →L[ℝ] ℝ := (-w⁻¹) • (T.comp (ContinuousLinearMap.inl ℝ (s → ℝ) ℝ))
  let b := u / w
  have hval (x : s → ℝ) : L x + b = (u - T (x, 0)) / w := by
    change (-w⁻¹) * T (x, 0) + u / w = _
    ring
  refine ⟨s, hs, L, b, ?_, ?_⟩
  · intro ν
    rw [hval]
    have hv := hsep (paperFiniteCovarianceData c F s ν, paperPerturbedGammaExpectation G ν.1)
      ⟨ν, rfl, le_rfl⟩
    rw [linear_pair] at hv
    apply le_of_lt
    apply (div_lt_iff₀ hw).mpr
    dsimp [w]
    linarith
  · rw [hval]
    change a < (u - T (paperFiniteCovarianceData c F s μ, 0)) / w
    apply (lt_div_iff₀ hw).mpr
    dsimp [w]
    linarith

private theorem linear_finite_sum {κ : Type*} [Fintype κ] [DecidableEq κ]
    (L : (κ → ℝ) →L[ℝ] ℝ) (x : κ → ℝ) :
    L x = ∑ i, x i * L (Pi.single i 1) := by
  have hx : x = ∑ i, x i • (Pi.single i (1 : ℝ) : κ → ℝ) := by
    funext j
    simp [Pi.single_apply, Finset.sum_apply]
  calc
    L x = L (∑ i, x i • (Pi.single i (1 : ℝ) : κ → ℝ)) := congrArg L hx
    _ = ∑ i, x i * L (Pi.single i 1) := by simp only [map_sum, map_smul, smul_eq_mul]

/-- The affine certificate is literally a finite weighted sum of off-diagonal
covariances plus a constant, with no implicit infinite functional. -/
theorem exists_paperFiniteCovarianceSumLowerBound
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F) (δ : {r : ℝ // 0 < r}) :
    ∃ s : Finset (LogIndex × LogIndex × Bool), (∀ k ∈ s, k.1 ≠ k.2.1) ∧
      ∃ w : s → ℝ, ∃ b : ℝ,
        (∀ ν : PaperObservedSpectralCompletion c F,
          b + ∑ k : s, w k * paperObservedPhaseCovariances c F ν k.1 ≤
            paperPerturbedGammaExpectation G ν.1) ∧
        paperPerturbedGammaExpectation G μ.1 - δ.1 <
          b + ∑ k : s, w k * paperObservedPhaseCovariances c F μ k.1 := by
  classical
  obtain ⟨s, hs, L, b, hL, hμ⟩ := exists_paperFiniteAffineCovarianceLowerBound c F G μ δ
  refine ⟨s, hs, fun k => L (Pi.single k 1), b, ?_, ?_⟩
  · intro ν
    have hv := hL ν
    rw [linear_finite_sum] at hv
    simpa only [paperFiniteCovarianceData, ContinuousMap.coe_mk, mul_comm, add_comm] using hv
  · rw [linear_finite_sum] at hμ
    simpa only [paperFiniteCovarianceData, ContinuousMap.coe_mk, mul_comm, add_comm] using hμ

/-- Values at a chosen law of all globally valid finite off-diagonal affine
covariance lower bounds. -/
def paperFiniteAffineCovarianceValues
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F) : Set ℝ :=
  {v | ∃ s : Finset (LogIndex × LogIndex × Bool), (∀ k ∈ s, k.1 ≠ k.2.1) ∧
    ∃ w : s → ℝ, ∃ b : ℝ,
      (∀ ν : PaperObservedSpectralCompletion c F,
        b + ∑ k : s, w k * paperObservedPhaseCovariances c F ν k.1 ≤
          paperPerturbedGammaExpectation G ν.1) ∧
      v = b + ∑ k : s, w k * paperObservedPhaseCovariances c F μ k.1}

theorem paperFiniteAffineCovarianceValues_nonempty
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F) :
    (paperFiniteAffineCovarianceValues c F G μ).Nonempty := by
  obtain ⟨s, hs, w, b, h, _⟩ := exists_paperFiniteCovarianceSumLowerBound c F G μ ⟨1, zero_lt_one⟩
  exact ⟨_, s, hs, w, b, h, rfl⟩

theorem paperFiniteAffineCovarianceValues_bddAbove
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F) :
    BddAbove (paperFiniteAffineCovarianceValues c F G μ) := by
  refine ⟨paperPerturbedGammaExpectation G μ.1, ?_⟩
  rintro v ⟨s, _, w, b, h, rfl⟩
  exact h μ

/-- Exact finite-observation duality: gamma energy is the supremum of globally
valid affine bounds involving finitely many off-diagonal covariances. -/
theorem paperPerturbedGammaExpectation_eq_sSup_finiteAffineCovariances
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (μ : PaperObservedSpectralCompletion c F) :
    paperPerturbedGammaExpectation G μ.1 = sSup (paperFiniteAffineCovarianceValues c F G μ) := by
  symm
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
    (paperFiniteAffineCovarianceValues_nonempty c F G μ)
  · rintro v ⟨s, _, w, b, h, rfl⟩
    exact h μ
  · intro a ha
    obtain ⟨s, hs, w, b, h, hμ⟩ := exists_paperFiniteCovarianceSumLowerBound c F G μ
      ⟨paperPerturbedGammaExpectation G μ.1 - a, sub_pos.mpr ha⟩
    refine ⟨_, ⟨s, hs, w, b, h, rfl⟩, ?_⟩
    dsimp only at hμ
    linarith

end RHTower.WeilWorkPBAP
