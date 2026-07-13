import GaloisForLFunctions.HTGeometry.CanonicalFrameContinuity
import GaloisForLFunctions.HTGeometry.DeterminantRatioRoot
import GaloisForLFunctions.HTGeometry.RieszBrothersReduction
import GaloisForLFunctions.HTGeometry.SzegoFirstLimitInterface
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# The pure-singular carrier trichotomy from exact classical inputs

This module draws a hard formal boundary around the two classical circle theorems used by the
cofinal Cholesky paper.  The Riesz-brothers input is the already isolated predicate
`HasRieszBrothersDensityConclusion`.  The Szegő input is the general classical conclusion
`HasSzegoFirstLimitConclusion`, whose limit is the geometric mean of the Radon--Nikodym density.
Pure singularity is specialized to a zero ratio inside Lean.  No assertion about normalized roots,
graph closure,
analytic completeness, Cholesky repair, eigenvalues, or operator norms is hidden in either input.

From those two exact leaves, Lean proves the complete three-level geometry: full-product closure
of the raw analytic-polynomial graph, density of analytic monomials, collapse of the least Gram
eigenvalue, and escape of both the normalized determinant and the Euclidean operator norm of the
canonical inverse-Cholesky tower.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Matrix MeasureTheory Filter Polynomial Topology
open scoped ComplexOrder ENNReal InnerProductSpace NNReal Topology

noncomputable section

/-- The two-sided Fourier moment sequence of a finite measure on the multiplicative unit circle. -/
def circleMeasureMomentZ (mu : Measure Circle) (q : ℤ) : ℂ :=
  ∫ z : Circle, (z : ℂ) ^ q ∂mu

/-- The Toeplitz Gram tower belonging to a circle measure. -/
def circleMeasureGramTower (mu : Measure Circle) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  circleToeplitzGram N (circleMeasureMomentZ mu)

/-- The conjugate `n`th circle monomial as an element of `L²(mu)`.  Conjugation aligns the
project's Toeplitz indexing `c_(i-j)` with mathlib's inner-product convention. -/
noncomputable def circleConjugateMonomialLp
    (mu : Measure Circle) [IsFiniteMeasure mu] (n : ℕ) : Lp ℂ 2 mu :=
  MemLp.toLp (fun z : Circle => star ((z : ℂ) ^ n)) <|
    (circleMonomial_memLp mu n).star

theorem circleConjugateMonomialLp_coeFn_ae
    (mu : Measure Circle) [IsFiniteMeasure mu] (n : ℕ) :
    ⇑(circleConjugateMonomialLp mu n) =ᵐ[mu]
      fun z : Circle => star ((z : ℂ) ^ n) :=
  (circleMonomial_memLp mu n).star.coeFn_toLp

/-- Inner products of conjugate circle monomials are exactly the two-sided circle moments. -/
theorem circleConjugateMonomialLp_inner
    (mu : Measure Circle) [IsFiniteMeasure mu] (i j : ℕ) :
    inner ℂ (circleConjugateMonomialLp mu i) (circleConjugateMonomialLp mu j) =
      circleMeasureMomentZ mu ((i : ℤ) - (j : ℤ)) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [circleConjugateMonomialLp_coeFn_ae mu i,
    circleConjugateMonomialLp_coeFn_ae mu j] with z hi hj
  rw [hi, hj]
  have hne : (z : ℂ) ≠ 0 := by
    intro hzero
    have := congrArg norm hzero
    rw [Circle.norm_coe] at this
    norm_num at this
  simp [RCLike.inner_apply,
    ← Complex.inv_eq_conj (Circle.norm_coe z),
    zpow_natCast_sub_natCast₀ hne, div_eq_mul_inv, mul_comm]

/-- Every finite circle Toeplitz section is literally a Hilbert-space Gram matrix. -/
theorem circleMeasureGramTower_eq_gram
    (mu : Measure Circle) [IsFiniteMeasure mu] (N : ℕ) :
    circleMeasureGramTower mu N =
      Matrix.gram ℂ (fun i : Fin (N + 1) => circleConjugateMonomialLp mu i) := by
  ext i j
  exact (circleConjugateMonomialLp_inner mu i j).symm

/-- A continuous complex function vanishing almost everywhere vanishes on the measure support. -/
theorem circle_continuous_eq_zero_on_support_of_ae_eq_zero
    (mu : Measure Circle) (f : Circle → ℂ) (hfcont : Continuous f)
    (hfzero : f =ᵐ[mu] 0) : ∀ z ∈ mu.support, f z = 0 := by
  intro z hz
  by_contra hfz
  have hopen : IsOpen {w : Circle | f w ≠ 0} :=
    (isClosed_eq hfcont continuous_const).isOpen_compl
  have hnhds : {w : Circle | f w ≠ 0} ∈ 𝓝 z := hopen.mem_nhds hfz
  have hpos : 0 < mu {w : Circle | f w ≠ 0} :=
    (Measure.mem_support_iff_forall (μ := mu) z).mp hz _ hnhds
  have hnull : mu {w : Circle | f w ≠ 0} = 0 := by
    change mu ({w : Circle | f w = 0}ᶜ) = 0
    exact mem_ae_iff.mp hfzero
  exact hpos.ne' hnull

/-- Infinite support makes every finite family of conjugate circle monomials linearly
independent in `L²(mu)`. -/
theorem linearIndependent_circleConjugateMonomialLp_of_infiniteSupport
    (mu : Measure Circle) [IsFiniteMeasure mu] (hmu : mu.support.Infinite) (N : ℕ) :
    LinearIndependent ℂ
      (fun i : Fin (N + 1) => circleConjugateMonomialLp mu i) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let p : Polynomial ℂ :=
    ∑ i : Fin (N + 1), Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)
  let f : Circle → ℂ := fun z => p.eval (star (z : ℂ))
  have hfcont : Continuous f :=
    p.continuous.comp (continuous_star.comp continuous_subtype_val)
  have hsumcoe :
      ⇑(∑ i : Fin (N + 1), c i • circleConjugateMonomialLp mu i) =ᵐ[mu] f := by
    classical
    dsimp only [f, p]
    simp_rw [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    induction (Finset.univ : Finset (Fin (N + 1))) using Finset.induction_on with
    | empty => simpa using (Lp.coeFn_zero ℂ 2 mu)
    | @insert a S ha ih =>
        rw [Finset.sum_insert ha]
        filter_upwards [Lp.coeFn_add
            (c a • circleConjugateMonomialLp mu a)
            (∑ i ∈ S, c i • circleConjugateMonomialLp mu i),
          Lp.coeFn_smul (c a) (circleConjugateMonomialLp mu a),
          circleConjugateMonomialLp_coeFn_ae mu a, ih] with z hadd hsmul hmono htail
        rw [hadd]
        change ⇑(c a • circleConjugateMonomialLp mu a) z +
          ⇑(∑ i ∈ S, c i • circleConjugateMonomialLp mu i) z = _
        rw [hsmul, Pi.smul_apply, hmono, htail]
        simp [Finset.sum_insert ha]
  have hfzero : f =ᵐ[mu] 0 :=
    hsumcoe.symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hc)
  have hsuppzero : ∀ z ∈ mu.support, f z = 0 :=
    circle_continuous_eq_zero_on_support_of_ae_eq_zero mu f hfcont hfzero
  let S : Set ℂ := (fun z : Circle => star (z : ℂ)) '' mu.support
  have hSinfinite : S.Infinite := by
    apply hmu.image
    exact (star_injective.comp Subtype.val_injective).injOn
  have hSroot : S ⊆ {z : ℂ | p.IsRoot z} := by
    rintro z ⟨w, hw, rfl⟩
    exact hsuppzero w hw
  have hpzero : p = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot p (hSinfinite.mono hSroot)
  intro i
  have hcoeff := congrArg (fun q : Polynomial ℂ => q.coeff (i : ℕ)) hpzero
  simp [p] at hcoeff
  have hi : (∑ x : Fin (N + 1), if (i : ℕ) = (x : ℕ) then c x else 0) = c i := by
    classical
    calc
      (∑ x : Fin (N + 1), if (i : ℕ) = (x : ℕ) then c x else 0) =
          (if (i : ℕ) = (i : ℕ) then c i else 0) := by
        apply Finset.sum_eq_single i
        · intro b hb hbi
          have hnat : (i : ℕ) ≠ (b : ℕ) := fun h => hbi (Fin.ext h.symm)
          simp [hnat]
        · simp
      _ = c i := by simp
  rw [hi] at hcoeff
  exact hcoeff

/-- Infinite support supplies strict positivity at every level of the circle Toeplitz tower. -/
theorem circleMeasureGramTower_posDef_of_infiniteSupport
    (mu : Measure Circle) [IsFiniteMeasure mu] (hmu : mu.support.Infinite) (N : ℕ) :
    (circleMeasureGramTower mu N).PosDef := by
  rw [circleMeasureGramTower_eq_gram]
  exact Matrix.posDef_gram_of_linearIndependent
    (linearIndependent_circleConjugateMonomialLp_of_infiniteSupport mu hmu N)

/-- The canonical positive-diagonal inverse-Cholesky tower of an infinite-support circle
measure. -/
noncomputable def circleMeasureCanonicalFrameTower
    (mu : Measure Circle) [IsFiniteMeasure mu] (hmu : mu.support.Infinite) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  canonicalInverseCholeskyFactor
    ⟨circleMeasureGramTower mu N,
      circleMeasureGramTower_posDef_of_infiniteSupport mu hmu N⟩

theorem circleMeasureCanonicalFrameTower_isCanonical
    (mu : Measure Circle) [IsFiniteMeasure mu] (hmu : mu.support.Infinite) (N : ℕ) :
    IsCanonicalInverseCholeskyFrame
      (circleMeasureCanonicalFrameTower mu hmu N) (circleMeasureGramTower mu N) := by
  exact canonicalInverseCholeskyFactor_isCanonical
    ⟨circleMeasureGramTower mu N,
      circleMeasureGramTower_posDef_of_infiniteSupport mu hmu N⟩

/-- The normalized-root conclusion needed by the Cholesky geometry.  Unlike the ratio predicate,
this is not the external literature interface. -/
def HasSzegoNormalizedGramVanishingConclusion (mu : Measure Circle) : Prop :=
  Tendsto (normalizedGramDetRoot (circleMeasureGramTower mu)) atTop (𝓝 0)

/-- The general classical first Szegő conclusion specializes through Lebesgue decomposition and
then implies the normalized-root conclusion entirely inside Lean. -/
theorem hasSzegoNormalizedGramVanishingConclusion_of_classicalSzego
    (mu : Measure Circle) [IsFiniteMeasure mu] (hmu : mu.support.Infinite)
    (hsing : mu ⟂ₘ circleLebesgue)
    (hszego : HasSzegoFirstLimitConclusion (circleMeasureGramTower mu)
      mu circleLebesgue) :
    HasSzegoNormalizedGramVanishingConclusion mu := by
  let a : ℕ → ℝ := fun N => (circleMeasureGramTower mu N).det.re
  have ha : ∀ N, 0 < a N := by
    intro N
    have hp := (circleMeasureGramTower_posDef_of_infiniteSupport mu hmu N).det_pos
    simp only [Complex.lt_def, Complex.zero_re, Complex.zero_im] at hp
    exact hp.1
  have hratio :=
    consecutiveGramDeterminantRatio_tendsto_zero_of_szego_of_mutuallySingular
      (circleMeasureGramTower mu) mu circleLebesgue hsing hszego
  have hroot := tendsto_rpow_inv_succ_zero_of_ratio_zero a ha (by
    simpa only [a, consecutiveGramDeterminantRatio] using hratio)
  change Tendsto (fun N => (circleMeasureGramTower mu N).det.re ^
    (((N + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0)
  simpa only [a, Nat.cast_add, Nat.cast_one] using hroot

/-- From the exact Riesz-brothers leaf, all graph and analytic-completeness conclusions are
formal consequences. -/
theorem pureSingular_graph_and_completeness_of_rieszBrothers
    (mu : Measure Circle) [IsFiniteMeasure mu]
    (hsing : mu ⟂ₘ circleLebesgue)
    (hriesz : HasRieszBrothersDensityConclusion mu circleLebesgue) :
    (linearGraphSubmodule finsuppCoefficientL2
        (polynomialSynthesisL2 mu)).topologicalClosure = ⊤ ∧
      (analyticMonomialSpan mu).topologicalClosure = ⊤ := by
  have hrigid : IsOneSidedFourierRigid mu :=
    oneSidedFourierRigid_of_mutuallySingular_of_rieszBrothers
      mu circleLebesgue hsing hriesz
  exact ⟨polynomialGraph_closure_eq_top_of_oneSidedFourierRigid mu hrigid,
    analyticMonomialSpan_closure_eq_top_of_oneSidedFourierRigid mu hrigid⟩

/-- From the exact general Szegő leaf and pure singularity, every spectral and canonical-repair
escape statement is a formal consequence. -/
theorem circleMeasure_frame_escape_of_szego
    (mu : Measure Circle) [IsFiniteMeasure mu] (hmu : mu.support.Infinite)
    (hsing : mu ⟂ₘ circleLebesgue)
    (hszego : HasSzegoFirstLimitConclusion (circleMeasureGramTower mu)
      mu circleLebesgue) :
    Tendsto (fun N => leastEigenvalue (circleMeasureGramTower mu N)
        (circleMeasureGramTower_posDef_of_infiniteSupport mu hmu N)) atTop (𝓝 0) ∧
      Tendsto (normalizedFrameDetRoot (circleMeasureCanonicalFrameTower mu hmu))
        atTop atTop ∧
      Tendsto (euclideanFrameOpNorm (circleMeasureCanonicalFrameTower mu hmu))
        atTop atTop := by
  let G := circleMeasureGramTower mu
  let C := circleMeasureCanonicalFrameTower mu hmu
  have hG : ∀ N, (G N).PosDef := fun N =>
    circleMeasureGramTower_posDef_of_infiniteSupport mu hmu N
  have hC : ∀ N, IsCanonicalInverseCholeskyFrame (C N) (G N) := fun N =>
    circleMeasureCanonicalFrameTower_isCanonical mu hmu N
  have hzero : HasSzegoNormalizedGramVanishingConclusion mu :=
    hasSzegoNormalizedGramVanishingConclusion_of_classicalSzego mu hmu hsing hszego
  have hleast :=
    leastEigenvalue_tendsto_zero_of_normalizedGramDetRoot_tendsto_zero G hG hzero
  have hdet :=
    normalizedFrameDetRoot_tendsto_atTop_of_gram_tendsto_zero G C hG hC hzero
  have hop :=
    euclideanFrameOpNorm_tendsto_atTop_of_normalizedGramDetRoot_tendsto_zero
      G C hG hC hzero
  exact ⟨hleast, hdet, hop⟩

/-- **Pure-singular carrier trichotomy.**  Once the two cited classical circle theorems are
supplied in their exact interfaces, every asserted interaction between raw graph saturation,
analytic completeness, finite Gram collapse, and coherent Cholesky escape is proved in Lean. -/
theorem pureSingularCarrier_trichotomy_of_classical_inputs
    (mu : Measure Circle) [IsFiniteMeasure mu] (hmu : mu.support.Infinite)
    (hsing : mu ⟂ₘ circleLebesgue)
    (hriesz : HasRieszBrothersDensityConclusion mu circleLebesgue)
    (hszego : HasSzegoFirstLimitConclusion (circleMeasureGramTower mu)
      mu circleLebesgue) :
    (linearGraphSubmodule finsuppCoefficientL2
        (polynomialSynthesisL2 mu)).topologicalClosure = ⊤ ∧
      (analyticMonomialSpan mu).topologicalClosure = ⊤ ∧
      Tendsto (fun N => leastEigenvalue (circleMeasureGramTower mu N)
        (circleMeasureGramTower_posDef_of_infiniteSupport mu hmu N)) atTop (𝓝 0) ∧
      Tendsto (normalizedFrameDetRoot (circleMeasureCanonicalFrameTower mu hmu))
        atTop atTop ∧
      Tendsto (euclideanFrameOpNorm (circleMeasureCanonicalFrameTower mu hmu))
        atTop atTop := by
  have hgraph := pureSingular_graph_and_completeness_of_rieszBrothers mu hsing hriesz
  have hescape := circleMeasure_frame_escape_of_szego mu hmu hsing hszego
  exact ⟨hgraph.1, hgraph.2, hescape.1, hescape.2.1, hescape.2.2⟩

end

end GaloisForLFunctions.HTGeometry
