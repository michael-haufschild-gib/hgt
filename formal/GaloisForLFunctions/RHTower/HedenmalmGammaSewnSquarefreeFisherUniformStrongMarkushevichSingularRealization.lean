import GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock
import GaloisForLFunctions.HTGeometry.StrongMarkushevichSystem
import GaloisForLFunctions.RHTower.HedenmalmGammaSewnSquarefreeFisherMarkushevichSingularRealization

/-!
# Uniform strong-Markushevich singular realization of the physical MSC columns

Every arbitrary mixture of the normalized MSC modes and their explicit biorthogonal dual is
complete.  The primal vectors have norm one and the dual norms are uniformly bounded by `sqrt 2`,
yet every finite Bessel bound fails when `Re rho ≤ 1`.  Thus even hereditary completeness together
with uniform minimality cannot supply the missing quantitative stability in the MSC route to RH.
-/

open Complex Filter Set Topology
open scoped BigOperators Topology InnerProductSpace

noncomputable section

namespace RHTower.HedenmalmThetaSource.MarkushevichSingular

open Classical
open RHTower

namespace Block

theorem isStrongMarkushevichPair
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (j : ℕ) :
    GaloisForLFunctions.HTGeometry.IsStrongMarkushevichPair ℂ
      (primal rho sigma j) (dual rho sigma j) :=
  GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.isStrongMarkushevichPair_phase
    ↥(block j) (phase rho sigma j) (norm_phase rho hsigma j)

theorem norm_dual_sq_le_two
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (j : ℕ) (i : ↥(block j)) :
    ‖dual rho sigma j i‖ ^ 2 ≤ 2 :=
  GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.norm_phaseDual_sq_le_two
    ↥(block j) (phase rho sigma j) (norm_phase rho hsigma j) i

end Block

theorem mixed_of_mem_block
    (rho : ℂ) (sigma : ℝ) (s : Set ℕ) {j n : ℕ} (hmem : n ∈ block j) :
    GaloisForLFunctions.HTGeometry.strongMarkushevichMixed
        (normalizedMode rho sigma) (normalizedDual rho sigma) s n =
      WithLp.toLp 2
        (lp.single 2 j
          (GaloisForLFunctions.HTGeometry.strongMarkushevichMixed
            (Block.primal rho sigma j) (Block.dual rho sigma j)
            {i : ↥(block j) | (i : ℕ) ∈ s} ⟨n, hmem⟩), 0) := by
  by_cases hn : n ∈ s
  · rw [GaloisForLFunctions.HTGeometry.strongMarkushevichMixed]
    simp only [if_pos hn]
    rw [normalizedMode_of_mem_block rho sigma hmem]
    simp [GaloisForLFunctions.HTGeometry.strongMarkushevichMixed, hn]
  · rw [GaloisForLFunctions.HTGeometry.strongMarkushevichMixed]
    simp only [if_neg hn]
    rw [normalizedDual_of_mem_block rho sigma hmem]
    simp [GaloisForLFunctions.HTGeometry.strongMarkushevichMixed, hn]

theorem isCompleteSystem_mixed
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (s : Set ℕ) :
    GaloisForLFunctions.HTGeometry.IsCompleteSystem ℂ
      (GaloisForLFunctions.HTGeometry.strongMarkushevichMixed
        (normalizedMode rho sigma) (normalizedDual rho sigma) s) := by
  rw [GaloisForLFunctions.HTGeometry.isCompleteSystem_iff_forall_inner_eq_zero]
  intro x hx
  apply withLp_ext
  · apply lp.ext
    funext j
    have hc := (Block.isStrongMarkushevichPair rho hsigma j).2
      {i : ↥(block j) | (i : ℕ) ∈ s}
    rw [GaloisForLFunctions.HTGeometry.isCompleteSystem_iff_forall_inner_eq_zero] at hc
    apply hc
    intro i
    have hi := hx (i : ℕ)
    rw [mixed_of_mem_block rho sigma s i.property, WithLp.prod_inner_apply] at hi
    simp only [inner_zero_left, add_zero] at hi
    rw [lp.inner_single_left] at hi
    exact hi
  · apply lp.ext
    funext q
    rcases q.property with hq | hq
    · have hqeq : q = headIndex := Subtype.ext hq
      subst q
      have h := hx 1
      by_cases h1s : 1 ∈ s
      · rw [GaloisForLFunctions.HTGeometry.strongMarkushevichMixed,
          if_pos h1s, normalizedMode_one, WithLp.prod_inner_apply] at h
        simp only [inner_zero_left, zero_add] at h
        rw [lp.inner_single_left] at h
        simpa using h
      · rw [GaloisForLFunctions.HTGeometry.strongMarkushevichMixed,
          if_neg h1s, normalizedDual_one, WithLp.prod_inner_apply] at h
        simp only [inner_zero_left, zero_add] at h
        rw [lp.inner_single_left] at h
        simpa using h
    · have hq1 : (q : ℕ) ≠ 1 := by
        intro heq
        apply hq
        simp [heq]
      have h := hx (q : ℕ)
      by_cases hqs : (q : ℕ) ∈ s
      · rw [GaloisForLFunctions.HTGeometry.strongMarkushevichMixed,
          if_pos hqs,
          normalizedMode_of_not_squarefree rho sigma hq1 hq,
          WithLp.prod_inner_apply] at h
        simp only [inner_zero_left, zero_add] at h
        rw [lp.inner_single_left] at h
        simpa using h
      · rw [GaloisForLFunctions.HTGeometry.strongMarkushevichMixed,
          if_neg hqs,
          normalizedDual_of_not_squarefree rho sigma hq1 hq,
          WithLp.prod_inner_apply] at h
        simp only [inner_zero_left, zero_add] at h
        rw [lp.inner_single_left] at h
        simpa using h

theorem isStrongMarkushevichPair_normalized
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) :
    GaloisForLFunctions.HTGeometry.IsStrongMarkushevichPair ℂ
      (normalizedMode rho sigma) (normalizedDual rho sigma) :=
  ⟨isDualSystem_normalizedMode_normalizedDual rho hsigma,
    isCompleteSystem_mixed rho hsigma⟩

theorem norm_normalizedDual_sq_le_two
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    ‖normalizedDual rho sigma n‖ ^ 2 ≤ 2 := by
  classical
  by_cases h1 : n = 1
  · subst n
    rw [normalizedDual_one, norm_withLp_right,
      lp.norm_single (by norm_num), norm_one]
    norm_num
  · by_cases hn : Squarefree n
    · rw [normalizedDual_of_squarefree rho sigma h1 hn,
        norm_withLp_left, lp.norm_single (by norm_num)]
      exact Block.norm_dual_sq_le_two rho hsigma _ _
    · rw [normalizedDual_of_not_squarefree rho sigma h1 hn,
        norm_withLp_right, lp.norm_single (by norm_num), norm_one]
      norm_num

def IsMSCPhysicalOverlapUniformStrongMarkushevichHilbertRealization
    (rho : ℂ) (sigma : ℝ) (modes : ℕ → H) (source overlap : H)
    (dual : ℕ → H) : Prop :=
  RHTower.HedenmalmThetaSource.IsMSCPhysicalOverlapHilbertRealization
      rho sigma modes source overlap ∧
    GaloisForLFunctions.HTGeometry.IsStrongMarkushevichPair ℂ
      (RHTower.HedenmalmThetaSource.mscSignGaugeNormalizedMode modes) dual ∧
    (∀ n, ‖RHTower.HedenmalmThetaSource.mscSignGaugeNormalizedMode modes n‖ = 1) ∧
    ∀ n, ‖dual n‖ ^ 2 ≤ 2

theorem isMSCPhysicalOverlapUniformStrongMarkushevichHilbertRealization
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 1 / 2 < rho.re) :
    IsMSCPhysicalOverlapUniformStrongMarkushevichHilbertRealization rho sigma
      (mode rho sigma) (sourceVector rho hsigma hrho) (overlapVector rho hsigma hrho)
        (normalizedDual rho sigma) := by
  refine ⟨isMSCPhysicalOverlapHilbertRealization rho hsigma hrho, ?_, ?_,
    norm_normalizedDual_sq_le_two rho hsigma⟩
  · rw [show RHTower.HedenmalmThetaSource.mscSignGaugeNormalizedMode
        (mode rho sigma) = normalizedMode rho sigma by
      funext n
      exact normalized_mode rho hsigma n]
    exact isStrongMarkushevichPair_normalized rho hsigma
  · intro n
    rw [normalized_mode rho hsigma]
    exact norm_normalizedMode rho hsigma n

theorem exists_mscPhysicalOverlapUniformStrongMarkushevichNonBesselRealization
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma)
    (hrho : 1 / 2 < rho.re) (hrho1 : rho.re ≤ 1) :
    ∃ (modes : ℕ → H) (source overlap : H) (dual : ℕ → H),
      IsMSCPhysicalOverlapUniformStrongMarkushevichHilbertRealization
          rho sigma modes source overlap dual ∧
        ∀ B : ℝ, ∃ packet : Finset ℕ, ∃ x : H,
          B * ‖x‖ ^ 2 <
            ∑ n ∈ packet,
              ‖inner ℂ
                (RHTower.HedenmalmThetaSource.mscSignGaugeNormalizedMode modes n) x‖ ^ 2 := by
  refine ⟨mode rho sigma, sourceVector rho hsigma hrho, overlapVector rho hsigma hrho,
    normalizedDual rho sigma,
    isMSCPhysicalOverlapUniformStrongMarkushevichHilbertRealization rho hsigma hrho, ?_⟩
  intro B
  exact RHTower.HedenmalmThetaSource.exists_besselViolation_of_re_le_one
    rho hsigma hrho1 (mode rho sigma) (sourceVector rho hsigma hrho)
      (overlapVector rho hsigma hrho)
        (isMSCPhysicalOverlapHilbertRealization rho hsigma hrho) B

/-- Strict-right route kill: the literal physical MSC columns coexist with a uniformly bounded
strong Markushevich pair, hence every mixed primal/dual system is complete, while every finite
Bessel bound fails. Qualitative hereditary completeness and uniform minimality therefore cannot
supply the stability step required by the MSC route to RH. -/
theorem strictRightXiZero_mscUniformStrongMarkushevichSingularRouteKill
    {rho : ℂ} (hhalf : 1 / 2 < rho.re) (hone : rho.re < 1)
    (hzero : RHTower.xi rho = 0) {sigma : ℝ} (hsigma : 1 < sigma) :
    (∃ k : ℕ, analyticOrderAt RHTower.xi rho = (k + 1 : ℕ) ∧
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g rho ∧
        (∀ tau : ℝ, 1 < tau →
          AnalyticAt ℂ (RHTower.mscPhysicalRegularGerm rho g tau)
              (RHTower.mscPhysicalZeroCoordinate rho tau) ∧
            (fun v =>
              GaloisForLFunctions.squarefreeFisherScore
                  (tau : ℂ) ((tau - 1 : ℝ) : ℂ) v /
                GaloisForLFunctions.squarefreeBoundaryOverlap
                  (tau : ℂ) ((tau - 1 : ℝ) : ℂ) v) =ᶠ[
              𝓝[≠] (RHTower.mscPhysicalZeroCoordinate rho tau)]
                fun v => 2 * ((k + 1 : ℕ) : ℂ) /
                  (v - RHTower.mscPhysicalZeroCoordinate rho tau) +
                    RHTower.mscPhysicalRegularGerm rho g tau v) ∧
          Tendsto
            (fun tau : ℝ =>
              Complex.normSq
                (RHTower.mscPhysicalRegularGerm rho g tau
                  (RHTower.mscPhysicalZeroCoordinate rho tau)))
            (nhdsWithin 1 (Set.Ioi 1)) (nhds 4)) ∧
      ∃ (modes : ℕ → H) (source overlap : H) (dual : ℕ → H),
        IsMSCPhysicalOverlapUniformStrongMarkushevichHilbertRealization
            rho sigma modes source overlap dual ∧
          ∀ B : ℝ, ∃ packet : Finset ℕ, ∃ x : H,
            B * ‖x‖ ^ 2 <
              ∑ n ∈ packet,
                ‖inner ℂ
                  (RHTower.HedenmalmThetaSource.mscSignGaugeNormalizedMode modes n) x‖ ^ 2 := by
  have hstrong :=
    isMSCPhysicalOverlapUniformStrongMarkushevichHilbertRealization rho hsigma hhalf
  have hwall :=
    RHTower.HedenmalmThetaSource.strictRightXiZero_mscBesselHilbertStabilityWall
      hhalf hone hzero hsigma (mode rho sigma) (sourceVector rho hsigma hhalf)
        (overlapVector rho hsigma hhalf)
  rcases hwall with ⟨hregular, _, hviolation⟩
  exact ⟨hregular, mode rho sigma, sourceVector rho hsigma hhalf,
    overlapVector rho hsigma hhalf, normalizedDual rho sigma, hstrong,
    hviolation hstrong.1⟩

end RHTower.HedenmalmThetaSource.MarkushevichSingular
