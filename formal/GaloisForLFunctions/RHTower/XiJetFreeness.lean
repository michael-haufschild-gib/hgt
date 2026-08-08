import GaloisForLFunctions.HTGeometry.DifferentialOrder
import GaloisForLFunctions.HTGeometry.EntireJetEvaluation
import GaloisForLFunctions.HTGeometry.EvaluationMinorGeneralDomain
import GaloisForLFunctions.HTGeometry.ComplexRealChannelIndependence
import GaloisForLFunctions.HTGeometry.FiniteObservableKoopmanBoundary
import GaloisForLFunctions.HTGeometry.FiniteReporterIsometricRecovery
import GaloisForLFunctions.HTGeometry.FiniteReporterNetworkFusion
import GaloisForLFunctions.HTGeometry.HypertranscendentalPointJetFreeness
import GaloisForLFunctions.HTGeometry.HypertranscendentalReporterFreeness
import GaloisForLFunctions.HilbertMetric.PolynomialMomentCancellation
import GaloisForLFunctions.HilbertMetric.UnisolventEvaluation
import GaloisForLFunctions.HTGeometry.FiniteLindemannWeierstrass
import GaloisForLFunctions.RHTower.XiHypertranscendenceUnconditional
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Free derivative jets of the completed xi function

This leaf instantiates the generic jet consequences of function hypertranscendence with the
unconditional theorem for the completed Riemann xi function.  It records algebraic independence of
the derivative functions, algebraic independence after adjoining the point coordinate, isolation of
every nonzero differential-polynomial relation locus, and failure of differential algebraicity at
each finite order.

These are global function-theoretic consequences of xi hypertranscendence.  They contain no
zero-location or Riemann-hypothesis conclusion.
-/

namespace RHTower

open GaloisForLFunctions
open scoped ComplexOrder

/-- Every finite initial family of completed-xi derivative functions is algebraically independent
over `ℂ`. -/
theorem algebraicIndependent_xi_initialJets (n : ℕ) :
    AlgebraicIndependent ℂ
      (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) xi) :=
  xi_hypertranscendental.algebraicIndependent_initialJets n

/-- **Completed-xi free jets.** All derivative functions of xi are algebraically independent over
`ℂ`. -/
theorem algebraicIndependent_xi_iteratedDeriv :
    AlgebraicIndependent ℂ (fun j : ℕ => iteratedDeriv j xi) :=
  xi_hypertranscendental.algebraicIndependent_iteratedDeriv

/-- Square evaluation matrix of the first `n + 1` completed-Xi derivative functions on a packet
of `n + 1` complex sample points. -/
noncomputable def xiInitialJetEvaluationMatrix
    (n : ℕ) (points : Fin (n + 1) → ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun row j => iteratedDeriv (j : ℕ) xi (points row)

/-- Evaluation column of one completed-Xi derivative function in the finite sample Hilbert
space. -/
noncomputable def xiInitialJetEvaluationColumn
    (n : ℕ) (points : Fin (n + 1) → ℂ) (j : Fin (n + 1)) :
    EuclideanSpace ℂ (Fin (n + 1)) :=
  WithLp.toLp 2 fun row => iteratedDeriv (j : ℕ) xi (points row)

/-- Hilbert Gram matrix of the first `n + 1` completed-Xi derivative functions on a square sample
packet. -/
noncomputable def xiInitialJetEvaluationGram
    (n : ℕ) (points : Fin (n + 1) → ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.gram ℂ (xiInitialJetEvaluationColumn n points)

/-- The completed-Xi jet Hilbert Gram is exactly the adjoint-square of its evaluation matrix. -/
theorem xiInitialJetEvaluationGram_eq_conjTranspose_mul
    (n : ℕ) (points : Fin (n + 1) → ℂ) :
    xiInitialJetEvaluationGram n points =
      (xiInitialJetEvaluationMatrix n points).conjTranspose *
        xiInitialJetEvaluationMatrix n points := by
  rw [xiInitialJetEvaluationGram,
    Matrix.gram_eq_conjTranspose_mul
      (EuclideanSpace.basisFun (Fin (n + 1)) ℂ)]
  rfl

/-- Exact finite-volume law: the completed-Xi jet Gram determinant is the squared complex norm of
the corresponding evaluation determinant. -/
theorem xiInitialJetEvaluationGram_det_eq_normSq
    (n : ℕ) (points : Fin (n + 1) → ℂ) :
    (xiInitialJetEvaluationGram n points).det =
      (Complex.normSq (xiInitialJetEvaluationMatrix n points).det : ℂ) := by
  rw [xiInitialJetEvaluationGram_eq_conjTranspose_mul,
    Matrix.det_mul, Matrix.det_conjTranspose,
    Complex.normSq_eq_conj_mul_self]
  rfl

/-- **Unconditional completed-Xi jet unisolvency.** At every finite jet depth there are pairwise
distinct complex sample points whose literal derivative evaluation matrix is invertible. -/
theorem exists_injective_xiInitialJetEvaluationMatrix_det_isUnit (n : ℕ) :
    ∃ points : Fin (n + 1) → ℂ, Function.Injective points ∧
      IsUnit (xiInitialJetEvaluationMatrix n points).det := by
  have hlin : LinearIndependent ℂ
      (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) xi) :=
    (algebraicIndependent_xi_initialJets n).linearIndependent
  obtain ⟨points, P, hinj, hdet, hP⟩ :=
    GaloisForLFunctions.HTGeometry.exists_injective_evaluation_minor_of_linearIndependent
      (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) xi) hlin
  refine ⟨points, hinj, ?_⟩
  have hmatrix : P = xiInitialJetEvaluationMatrix n points := by
    ext row j
    exact hP row j
  simpa [hmatrix] using hdet

/-- **Completed-Xi finite Hilbert reconstruction.** At every finite jet depth one packet of
pairwise distinct complex samples simultaneously supports exact dual recovery, a positive-definite
jet Gram, and strictly positive Hilbert volume. -/
theorem exists_injective_xiInitialJetEvaluationHilbertReconstruction (n : ℕ) :
    ∃ (points : Fin (n + 1) → ℂ)
        (dual : Fin (n + 1) → Fin (n + 1) → ℂ),
      Function.Injective points ∧
      (∀ (q r : Fin (n + 1)),
        ∑ i, dual q i * iteratedDeriv (r : ℕ) xi (points i) =
          if q = r then 1 else 0) ∧
      (∀ (a : Fin (n + 1) → ℂ) q, ∑ i, dual q i *
          (∑ r, a r * iteratedDeriv (r : ℕ) xi (points i)) = a q) ∧
      (xiInitialJetEvaluationGram n points).PosDef ∧
      0 < (xiInitialJetEvaluationGram n points).det := by
  obtain ⟨points, dual, hinj, hdelta, hrecovery, hgram, hdet⟩ :=
    HTGeometry.exists_injective_finiteEvaluationHilbertReconstruction_of_linearIndependent
      (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) xi)
      (algebraicIndependent_xi_initialJets n).linearIndependent
  refine ⟨points, dual, hinj, hdelta, hrecovery, ?_, ?_⟩
  · simpa [xiInitialJetEvaluationGram, xiInitialJetEvaluationColumn,
      HTGeometry.finiteEvaluationGram, HTGeometry.finiteEvaluationColumn] using! hgram
  · simpa [xiInitialJetEvaluationGram, xiInitialJetEvaluationColumn,
      HTGeometry.finiteEvaluationGram, HTGeometry.finiteEvaluationColumn] using! hdet

/-- **Unconditional completed-Xi finite-sample Hilbert metric.** Every finite initial derivative
jet admits distinct complex sample points on which its actual evaluation Gram is strictly positive
definite. -/
theorem exists_injective_xiInitialJetEvaluationGram_posDef (n : ℕ) :
    ∃ points : Fin (n + 1) → ℂ, Function.Injective points ∧
      (xiInitialJetEvaluationGram n points).PosDef := by
  obtain ⟨points, _dual, hinj, _hdelta, _hrecovery, hgram, _hdet⟩ :=
    exists_injective_xiInitialJetEvaluationHilbertReconstruction n
  exact ⟨points, hinj, hgram⟩

/-- The unconditional completed-Xi finite-sample Hilbert metric has strictly positive volume at
every finite jet depth. -/
theorem exists_injective_xiInitialJetEvaluationGram_det_pos (n : ℕ) :
    ∃ points : Fin (n + 1) → ℂ, Function.Injective points ∧
      0 < (xiInitialJetEvaluationGram n points).det := by
  obtain ⟨points, _dual, hinj, _hdelta, _hrecovery, _hgram, hdet⟩ :=
    exists_injective_xiInitialJetEvaluationHilbertReconstruction n
  exact ⟨points, hinj, hdet⟩

/-- **Exact complex completed-Xi jet reconstruction.** At every finite jet depth there are pairwise
distinct complex sample points and dual weights that isolate each derivative function and recover
every complex jet coefficient vector from its literal Xi evaluations. -/
theorem exists_injective_xiInitialJetEvaluation_dualReconstruction (n : ℕ) :
    ∃ (points : Fin (n + 1) → ℂ)
        (dual : Fin (n + 1) → Fin (n + 1) → ℂ),
      Function.Injective points ∧
      (∀ (q r : Fin (n + 1)),
        ∑ i, dual q i * iteratedDeriv (r : ℕ) xi (points i) =
          if q = r then 1 else 0) ∧
      ∀ (a : Fin (n + 1) → ℂ) q, ∑ i, dual q i *
          (∑ r, a r * iteratedDeriv (r : ℕ) xi (points i)) = a q := by
  obtain ⟨points, dual, hinj, hdelta, hrecovery, _hgram, _hdet⟩ :=
    exists_injective_xiInitialJetEvaluationHilbertReconstruction n
  exact ⟨points, dual, hinj, hdelta, hrecovery⟩

/-- Real-or-imaginary observation of one completed-Xi derivative, with the observation channel
recorded in the sample domain. -/
noncomputable def xiInitialJetRealChannelFeature
    (n : ℕ) (j : Fin (n + 1)) (sample : ℂ × Bool) : ℝ :=
  match sample.2 with
  | false => (iteratedDeriv (j : ℕ) xi sample.1).re
  | true => (iteratedDeriv (j : ℕ) xi sample.1).im

/-- Complex linear freeness of the completed-Xi jets implies real linear freeness of the joint
real/imaginary observation channels. -/
theorem linearIndependent_xiInitialJetRealChannelFeature (n : ℕ) :
    LinearIndependent ℝ (xiInitialJetRealChannelFeature n) := by
  simpa [xiInitialJetRealChannelFeature,
    GaloisForLFunctions.HTGeometry.complexRealChannelFeature] using!
    GaloisForLFunctions.HTGeometry.linearIndependent_complexRealChannelFeature_of_complex
      (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) xi)
      (algebraicIndependent_xi_initialJets n).linearIndependent

/-- **Exact finite completed-Xi jet reconstruction.** At every finite jet depth there is a packet
of pairwise distinct tagged real/imaginary measurements with dual weights that isolate each jet
coordinate. Consequently the same weights recover every real coefficient vector from its literal
Xi-jet observations. -/
theorem exists_injective_xiInitialJetRealChannel_dualReconstruction (n : ℕ) :
    ∃ (nodes : Fin (n + 1) → ℂ × Bool)
        (dual : Fin (n + 1) → Fin (n + 1) → ℝ),
      Function.Injective nodes ∧
      (∀ q r, ∑ i, dual q i * xiInitialJetRealChannelFeature n r (nodes i) =
        if q = r then 1 else 0) ∧
      ∀ (a : Fin (n + 1) → ℝ) q, ∑ i, dual q i *
          (∑ r, a r * xiInitialJetRealChannelFeature n r (nodes i)) = a q := by
  simpa only using
    GaloisForLFunctions.HilbertMetric.exists_injective_nodes_dual_reconstruction
      (xiInitialJetRealChannelFeature n)
      (linearIndependent_xiInitialJetRealChannelFeature n)

/-- One completed-Xi derivative feature as a vector of real channel observations. -/
noncomputable def xiInitialJetRealChannelEvaluationColumn
    (n : ℕ) (nodes : Fin (n + 1) → ℂ × Bool) (j : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 fun row => xiInitialJetRealChannelFeature n j (nodes row)

/-- Real Hilbert Gram of the first `n + 1` completed-Xi derivatives on a square packet of tagged
real/imaginary measurements. -/
noncomputable def xiInitialJetRealChannelEvaluationGram
    (n : ℕ) (nodes : Fin (n + 1) → ℂ × Bool) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.gram ℝ (xiInitialJetRealChannelEvaluationColumn n nodes)

/-- **Finite real-channel completed-Xi Hilbert reconstruction.** At every finite jet depth one
pairwise-distinct tagged packet simultaneously carries exact dual recovery, a positive-definite
real Gram, and positive Hilbert volume. -/
theorem exists_injective_xiInitialJetRealChannelEvaluationHilbertReconstruction (n : ℕ) :
    ∃ (nodes : Fin (n + 1) → ℂ × Bool)
        (dual : Fin (n + 1) → Fin (n + 1) → ℝ),
      Function.Injective nodes ∧
      (∀ q r, ∑ i, dual q i * xiInitialJetRealChannelFeature n r (nodes i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin (n + 1) → ℝ) q,
        ∑ i, dual q i *
          (∑ r, a r * xiInitialJetRealChannelFeature n r (nodes i)) = a q) ∧
      (xiInitialJetRealChannelEvaluationGram n nodes).PosDef ∧
      0 < (xiInitialJetRealChannelEvaluationGram n nodes).det := by
  simpa only [xiInitialJetRealChannelEvaluationGram,
    xiInitialJetRealChannelEvaluationColumn,
    GaloisForLFunctions.HilbertMetric.realEvaluationGram,
    GaloisForLFunctions.HilbertMetric.realEvaluationColumn] using!
    GaloisForLFunctions.HilbertMetric.exists_injective_realEvaluationHilbertReconstruction
      (xiInitialJetRealChannelFeature n)
      (linearIndependent_xiInitialJetRealChannelFeature n)

/-- **Unconditional real-channel completed-Xi Hilbert metric.** At every finite jet depth there are
pairwise distinct tagged real/imaginary measurements whose actual Xi-jet Gram is positive
definite. -/
theorem exists_injective_xiInitialJetRealChannelEvaluationGram_posDef (n : ℕ) :
    ∃ nodes : Fin (n + 1) → ℂ × Bool, Function.Injective nodes ∧
      (xiInitialJetRealChannelEvaluationGram n nodes).PosDef := by
  obtain ⟨nodes, _dual, hinj, _hdelta, _hrecovery, hgram, _hdet⟩ :=
    exists_injective_xiInitialJetRealChannelEvaluationHilbertReconstruction n
  exact ⟨nodes, hinj, hgram⟩

/-- The unconditional real-channel completed-Xi Hilbert metric has strictly positive volume at
every finite jet depth. -/
theorem exists_injective_xiInitialJetRealChannelEvaluationGram_det_pos (n : ℕ) :
    ∃ nodes : Fin (n + 1) → ℂ × Bool, Function.Injective nodes ∧
      0 < (xiInitialJetRealChannelEvaluationGram n nodes).det := by
  obtain ⟨nodes, _dual, hinj, _hdelta, _hrecovery, _hgram, hdet⟩ :=
    exists_injective_xiInitialJetRealChannelEvaluationHilbertReconstruction n
  exact ⟨nodes, hinj, hdet⟩

/-- The point coordinate together with every finite initial completed-xi derivative jet is
algebraically independent over `ℂ`. -/
theorem algebraicIndependent_xi_pointInitialJets (n : ℕ) :
    AlgebraicIndependent ℂ (pointJetFunctionTuple xi n) :=
  xi_hypertranscendental.algebraicIndependent_pointInitialJets n

/-- Finite square-matrix index enumerating every point/Xi-jet monomial of total degree at most
`M`. -/
abbrev XiPointInitialJetMonomialIndex (n M : ℕ) :=
  Fin (Fintype.card
    (GaloisForLFunctions.HilbertMetric.TruncatedMultiIndex (n + 2) M))

/-- Exponent vector represented by one finite point/Xi-jet monomial index. -/
noncomputable def xiPointInitialJetMonomialExponent
    (n M : ℕ) (i : XiPointInitialJetMonomialIndex n M) : Fin (n + 2) →₀ ℕ :=
  GaloisForLFunctions.HilbertMetric.TruncatedMultiIndex.exponent
    ((Fintype.equivFin
      (GaloisForLFunctions.HilbertMetric.TruncatedMultiIndex (n + 2) M)).symm i)

/-- The finite enumeration of bounded point/Xi-jet monomial exponents has no collisions. -/
theorem xiPointInitialJetMonomialExponent_injective (n M : ℕ) :
    Function.Injective (xiPointInitialJetMonomialExponent n M) :=
  GaloisForLFunctions.HilbertMetric.TruncatedMultiIndex.exponent_injective.comp
    (Fintype.equivFin
      (GaloisForLFunctions.HilbertMetric.TruncatedMultiIndex (n + 2) M)).symm.injective

/-- A bounded differential monomial in the point coordinate and the first completed-Xi jets. -/
noncomputable def xiPointInitialJetMonomial
    (n M : ℕ) (i : XiPointInitialJetMonomialIndex n M) : ℂ → ℂ :=
  (xiPointInitialJetMonomialExponent n M i).prod
    fun j k => pointJetFunctionTuple xi n j ^ k

/-- Distinct bounded monomials in `z, ξ, ξ′, …, ξ⁽ⁿ⁾` are linearly independent as actual
complex-valued functions. -/
theorem linearIndependent_xiPointInitialJetMonomial (n M : ℕ) :
    LinearIndependent ℂ (xiPointInitialJetMonomial n M) := by
  simpa only [xiPointInitialJetMonomial] using!
    GaloisForLFunctions.RHTower.monomial_linearIndependent_of_algebraicIndependent
      (pointJetFunctionTuple xi n)
      (algebraicIndependent_xi_pointInitialJets n)
      (xiPointInitialJetMonomialExponent n M)
      (xiPointInitialJetMonomialExponent_injective n M)

/-- **Finite differential-polynomial Hilbert reconstruction for completed Xi.** At every jet
depth and total-degree cutoff, one packet of pairwise distinct complex samples simultaneously
isolates every monomial in `z, ξ, ξ′, …, ξ⁽ⁿ⁾`, recovers every coefficient vector supported on
those monomials, and carries a positive-definite evaluation Gram with strictly positive volume. -/
theorem exists_injective_xiPointInitialJetMonomialEvaluationHilbertReconstruction
    (n M : ℕ) :
    ∃ (points : XiPointInitialJetMonomialIndex n M → ℂ)
        (dual : XiPointInitialJetMonomialIndex n M →
          XiPointInitialJetMonomialIndex n M → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i * xiPointInitialJetMonomial n M r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : XiPointInitialJetMonomialIndex n M → ℂ) q,
        ∑ i, dual q i *
          (∑ r, a r * xiPointInitialJetMonomial n M r (points i)) = a q) ∧
      (HTGeometry.finiteEvaluationGram
        (xiPointInitialJetMonomial n M) points).PosDef ∧
      0 < (HTGeometry.finiteEvaluationGram
        (xiPointInitialJetMonomial n M) points).det := by
  exact
    HTGeometry.exists_injective_finiteEvaluationHilbertReconstruction_of_linearIndependent
      (xiPointInitialJetMonomial n M)
      (linearIndependent_xiPointInitialJetMonomial n M)

/-- **Universal bounded differential-polynomial detector.** One fixed sample packet detects every
nonzero coefficient vector of total degree at most `M`; the same packet also carries the strict
Hilbert metric. Thus sample selection is uniform over all bounded differential polynomials, not
chosen separately after seeing a relation. -/
theorem exists_injective_xiPointInitialJetMonomialEvaluation_universalDetector
    (n M : ℕ) :
    ∃ points : XiPointInitialJetMonomialIndex n M → ℂ,
      Function.Injective points ∧
      (∀ a : XiPointInitialJetMonomialIndex n M → ℂ, a ≠ 0 →
        ∃ i, (∑ r, a r * xiPointInitialJetMonomial n M r (points i)) ≠ 0) ∧
      (HTGeometry.finiteEvaluationGram
        (xiPointInitialJetMonomial n M) points).PosDef ∧
      0 < (HTGeometry.finiteEvaluationGram
        (xiPointInitialJetMonomial n M) points).det := by
  classical
  obtain ⟨points, dual, hinj, _hdelta, hrecovery, hgram, hdet⟩ :=
    exists_injective_xiPointInitialJetMonomialEvaluationHilbertReconstruction n M
  refine ⟨points, hinj, ?_, hgram, hdet⟩
  intro a ha
  by_contra hdetect
  have hzero : ∀ i, ∑ r, a r * xiPointInitialJetMonomial n M r (points i) = 0 := by
    intro i
    by_contra hi
    exact hdetect ⟨i, hi⟩
  apply ha
  funext q
  calc
    a q = ∑ i, dual q i *
        (∑ r, a r * xiPointInitialJetMonomial n M r (points i)) :=
      (hrecovery a q).symm
    _ = 0 := by simp [hzero]

/-- **Joint point/jet completed-Xi Hilbert reconstruction.** At every finite depth one packet of
pairwise distinct complex samples simultaneously supports exact dual recovery of the point
coordinate and Xi jets, a positive-definite Gram, and strictly positive Hilbert volume. -/
theorem exists_injective_xiPointInitialJetEvaluationHilbertReconstruction (n : ℕ) :
    ∃ (points : Fin (n + 2) → ℂ)
        (dual : Fin (n + 2) → Fin (n + 2) → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i * pointJetFunctionTuple xi n r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin (n + 2) → ℂ) q, ∑ i, dual q i *
          (∑ r, a r * pointJetFunctionTuple xi n r (points i)) = a q) ∧
      (HTGeometry.finiteEvaluationGram
        (pointJetFunctionTuple xi n) points).PosDef ∧
      0 < (HTGeometry.finiteEvaluationGram
        (pointJetFunctionTuple xi n) points).det := by
  simpa only using
    HTGeometry.exists_injective_finiteEvaluationHilbertReconstruction_of_linearIndependent
      (pointJetFunctionTuple xi n)
      (algebraicIndependent_xi_pointInitialJets n).linearIndependent

/-- **Exact joint point/jet reconstruction for completed Xi.** At every finite depth there are
pairwise distinct complex samples and dual weights that jointly isolate and recover the point
coordinate together with `ξ, ξ′, …, ξ⁽ⁿ⁾`. -/
theorem exists_injective_xiPointInitialJetEvaluation_dualReconstruction (n : ℕ) :
    ∃ (points : Fin (n + 2) → ℂ)
        (dual : Fin (n + 2) → Fin (n + 2) → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i * pointJetFunctionTuple xi n r (points i) =
        if q = r then 1 else 0) ∧
      ∀ (a : Fin (n + 2) → ℂ) q, ∑ i, dual q i *
          (∑ r, a r * pointJetFunctionTuple xi n r (points i)) = a q := by
  obtain ⟨points, dual, hinj, hdelta, hrecovery, _hgram, _hdet⟩ :=
    exists_injective_xiPointInitialJetEvaluationHilbertReconstruction n
  exact ⟨points, dual, hinj, hdelta, hrecovery⟩

/-- **Joint point/jet Hilbert metric for completed Xi.** Every finite family consisting of the
point coordinate and the initial completed-Xi derivative jet has a strictly positive evaluation
Gram on pairwise distinct complex samples. -/
theorem exists_injective_xiPointInitialJetEvaluationGram_posDef (n : ℕ) :
    ∃ points : Fin (n + 2) → ℂ, Function.Injective points ∧
      (HTGeometry.finiteEvaluationGram
        (pointJetFunctionTuple xi n) points).PosDef := by
  obtain ⟨points, _dual, hinj, _hdelta, _hrecovery, hgram, _hdet⟩ :=
    exists_injective_xiPointInitialJetEvaluationHilbertReconstruction n
  exact ⟨points, hinj, hgram⟩

/-- The joint point/jet completed-Xi evaluation metric has strictly positive Hilbert volume at every
finite depth. -/
theorem exists_injective_xiPointInitialJetEvaluationGram_det_pos (n : ℕ) :
    ∃ points : Fin (n + 2) → ℂ, Function.Injective points ∧
      0 < (HTGeometry.finiteEvaluationGram
        (pointJetFunctionTuple xi n) points).det := by
  obtain ⟨points, _dual, hinj, _hdelta, _hrecovery, _hgram, hdet⟩ :=
    exists_injective_xiPointInitialJetEvaluationHilbertReconstruction n
  exact ⟨points, hinj, hdet⟩

/-- Every nonzero differential polynomial has an isolated vanishing locus on the completed-xi
jets. -/
theorem xi_jetEval_isolated {n : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ} (hP : P ≠ 0) :
    ∀ z₀, ¬ (∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ, MvPolynomial.eval
      (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) xi z) P = 0) :=
  xi_hypertranscendental.jetEval_isolated xi_differentiable hP

/-- The completed xi function satisfies no algebraic differential equation of any prescribed
finite order. -/
theorem xi_not_differentiallyAlgebraicOfOrder (n : ℕ) :
    ¬ DifferentiallyAlgebraicOfOrder xi n :=
  xi_hypertranscendental.not_differentiallyAlgebraicOfOrder n

/-- **Exact Xi finite-dictionary jet capacity.**  Every finite set of completed-Xi derivative
observables captured by a finite-dimensional function space has cardinality at most that space's
dimension. -/
theorem xi_iteratedDeriv_mem_finset_card_le_finrank
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V]
    (s : Finset ℕ) (hmem : ∀ n ∈ s, iteratedDeriv n xi ∈ V) :
    s.card ≤ Module.finrank ℂ V :=
  HTGeometry.iteratedDeriv_mem_finset_card_le_finrank_of_constantCoefficientDifferentiallyTranscendental
    V (HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
      xi_hypertranscendental) s hmem

/-- Some completed-Xi derivative among orders at most `finrank V` escapes every fixed
finite-dimensional observable dictionary `V`. -/
theorem exists_xi_iteratedDeriv_not_mem_le_finrank
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V] :
    ∃ n ≤ Module.finrank ℂ V, iteratedDeriv n xi ∉ V :=
  HTGeometry.exists_iteratedDeriv_not_mem_le_finrank_of_constantCoefficientDifferentiallyTranscendental
    V (HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
      xi_hypertranscendental)

/-- **Unconditional finite-network completed-Xi Gram alternative.**  Fused reporter information
is singular exactly when every reporter erases one common genuinely nonzero Xi derivative
packet. -/
theorem xi_reporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
    (N : ℕ) {ι : Type*} [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) :
    (HTGeometry.finiteDerivativeReporterGram N xi
      (HTGeometry.finiteFamilyDerivativeReporter report)).det = 0 ↔
      ∃ c : Fin N → ℂ,
        (∀ a, report a (HTGeometry.finiteDerivativeReporterPacket c xi) = 0) ∧
        HTGeometry.finiteDerivativeReporterPacket c xi ≠ 0 := by
  apply HTGeometry.finiteDerivativeReporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
  exact HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
    xi_hypertranscendental

/-- **Completed-Xi data-processing no-recovery law.**  Some derivative order no larger than the
reporter dimension is new at the Xi source but redundant both before and after every downstream
linear decoder. -/
theorem exists_xi_finiteReporterConditionalInformation_dataProcessing_collapse
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k xi report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k xi
        (decode.comp report) = 0 ∧
      report (iteratedDeriv k xi) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k xi report ∧
      decode (report (iteratedDeriv k xi)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k xi (decode.comp report) ∧
      iteratedDeriv k xi ∉ Submodule.span ℂ
        (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) xi) := by
  apply HTGeometry.exists_finiteDerivativeReporterConditionalInformation_dataProcessing_collapse
  exact HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
    xi_hypertranscendental

/-- **Perfectly recoverable completed-Xi reporter, irrecoverable source direction.**  At one
bounded-order Xi collapse witness, an isometric encoding preserves zero information and its
adjoint recovers the reporter exactly, while the source derivative remains new. -/
theorem exists_xi_isometricReporterRecovery_collapse
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k xi report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k xi
        (decode.toLinearMap.comp report) = 0 ∧
      report (iteratedDeriv k xi) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k xi report ∧
      decode (report (iteratedDeriv k xi)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k xi
          (decode.toLinearMap.comp report) ∧
      decode.toContinuousLinearMap.adjoint.toLinearMap.comp
          (decode.toLinearMap.comp report) = report ∧
      iteratedDeriv k xi ∉ Submodule.span ℂ
        (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) xi) := by
  apply HTGeometry.exists_finiteDerivativeReporter_isometricRecovery_collapse
  exact HTGeometry.hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
    xi_hypertranscendental

/-- Every completed-Xi coefficient direction newly erased by a decoder is a genuine nonzero Xi
derivative packet which was visible before decoding. -/
theorem xi_finiteDerivativeReporterMap_postcomp_newBlindPacket
    {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {N : ℕ} (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z)
    {c : Fin N → ℂ}
    (hcpost : c ∈ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap N xi (decode.comp report)))
    (hcpre : c ∉ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap N xi report)) :
    HTGeometry.finiteDerivativeReporterPacket c xi ≠ 0 ∧
      report (HTGeometry.finiteDerivativeReporterPacket c xi) ≠ 0 ∧
      decode (report (HTGeometry.finiteDerivativeReporterPacket c xi)) = 0 := by
  exact HTGeometry.finiteDerivativeReporterMap_postcomp_newBlindPacket
    report decode hcpost hcpre

/-! ## Finite Gibbs spectral dressing -/

/-- Completed Xi retains infinite constant-coefficient spectral complexity after addition of any
finite Gibbs partition response. -/
theorem xi_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
    {A : Type*} [Fintype A] (energy : A → ℝ) :
    HTGeometry.ConstantCoefficientDifferentiallyTranscendental
      (xi + HTGeometry.finiteComplexGibbsPartition energy) :=
  GaloisForLFunctions.Hypertranscendental.add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
    xi_hypertranscendental xi_differentiable.contDiff energy

/-- Fused reporter information for finite-Gibbs dressed completed Xi is singular exactly when all
reporters erase one common genuinely nonzero dressed-Xi derivative packet. -/
theorem xi_add_finiteGibbs_reporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
    (N : ℕ) {A ι : Type*} [Fintype A] [Fintype ι]
    {Y : ι → Type*}
    [∀ a, NormedAddCommGroup (Y a)] [∀ a, InnerProductSpace ℂ (Y a)]
    (energy : A → ℝ) (report : ∀ a, (ℂ → ℂ) →ₗ[ℂ] Y a) :
    (HTGeometry.finiteDerivativeReporterGram N
      (xi + HTGeometry.finiteComplexGibbsPartition energy)
      (HTGeometry.finiteFamilyDerivativeReporter report)).det = 0 ↔
      ∃ c : Fin N → ℂ,
        (∀ a, report a (HTGeometry.finiteDerivativeReporterPacket c
          (xi + HTGeometry.finiteComplexGibbsPartition energy)) = 0) ∧
        HTGeometry.finiteDerivativeReporterPacket c
          (xi + HTGeometry.finiteComplexGibbsPartition energy) ≠ 0 := by
  apply HTGeometry.finiteDerivativeReporterGram_family_det_eq_zero_iff_exists_commonBlindPacket
  exact xi_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental energy

/-- Finite-Gibbs dressing preserves the completed-Xi same-witness data-processing collapse. -/
theorem exists_xi_add_finiteGibbs_finiteReporterConditionalInformation_dataProcessing_collapse
    {A : Type*} [Fintype A] (energy : A → ℝ)
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k
          (xi + HTGeometry.finiteComplexGibbsPartition energy) report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k
          (xi + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.comp report) = 0 ∧
      report (iteratedDeriv k
          (xi + HTGeometry.finiteComplexGibbsPartition energy)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k
          (xi + HTGeometry.finiteComplexGibbsPartition energy) report ∧
      decode (report (iteratedDeriv k
          (xi + HTGeometry.finiteComplexGibbsPartition energy))) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k
          (xi + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.comp report) ∧
      iteratedDeriv k (xi + HTGeometry.finiteComplexGibbsPartition energy) ∉
        Submodule.span ℂ (Set.range fun i : Fin k =>
          iteratedDeriv (i : ℕ)
            (xi + HTGeometry.finiteComplexGibbsPartition energy)) := by
  apply HTGeometry.exists_finiteDerivativeReporterConditionalInformation_dataProcessing_collapse
  exact xi_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental energy

/-- An isometrically encoded finite-Gibbs dressed-Xi reporter is exactly recovered, while the same
bounded-order source direction erased before encoding remains genuinely new. -/
theorem exists_xi_add_finiteGibbs_isometricReporterRecovery_collapse
    {A : Type*} [Fintype A] (energy : A → ℝ)
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗᵢ[ℂ] Z) :
    ∃ k : ℕ, k ≤ Module.finrank ℂ Y ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k
          (xi + HTGeometry.finiteComplexGibbsPartition energy) report = 0 ∧
      HTGeometry.finiteDerivativeReporterConditionalInformation k
          (xi + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.toLinearMap.comp report) = 0 ∧
      report (iteratedDeriv k
          (xi + HTGeometry.finiteComplexGibbsPartition energy)) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k
          (xi + HTGeometry.finiteComplexGibbsPartition energy) report ∧
      decode (report (iteratedDeriv k
          (xi + HTGeometry.finiteComplexGibbsPartition energy))) ∈
        HTGeometry.finiteDerivativeReporterPreviousSpace k
          (xi + HTGeometry.finiteComplexGibbsPartition energy)
          (decode.toLinearMap.comp report) ∧
      decode.toContinuousLinearMap.adjoint.toLinearMap.comp
          (decode.toLinearMap.comp report) = report ∧
      iteratedDeriv k (xi + HTGeometry.finiteComplexGibbsPartition energy) ∉
        Submodule.span ℂ (Set.range fun i : Fin k =>
          iteratedDeriv (i : ℕ)
            (xi + HTGeometry.finiteComplexGibbsPartition energy)) := by
  apply HTGeometry.exists_finiteDerivativeReporter_isometricRecovery_collapse
  exact xi_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental energy

/-- Every coefficient direction newly erased by a decoder for finite-Gibbs dressed completed Xi
synthesizes a genuine nonzero packet visible before decoding. -/
theorem xi_add_finiteGibbs_finiteDerivativeReporterMap_postcomp_newBlindPacket
    {A : Type*} [Fintype A] (energy : A → ℝ)
    {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {N : ℕ} (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z)
    {c : Fin N → ℂ}
    (hcpost : c ∈ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap N
        (xi + HTGeometry.finiteComplexGibbsPartition energy) (decode.comp report)))
    (hcpre : c ∉ LinearMap.ker
      (HTGeometry.finiteDerivativeReporterMap N
        (xi + HTGeometry.finiteComplexGibbsPartition energy) report)) :
    HTGeometry.finiteDerivativeReporterPacket c
        (xi + HTGeometry.finiteComplexGibbsPartition energy) ≠ 0 ∧
      report (HTGeometry.finiteDerivativeReporterPacket c
        (xi + HTGeometry.finiteComplexGibbsPartition energy)) ≠ 0 ∧
      decode (report (HTGeometry.finiteDerivativeReporterPacket c
        (xi + HTGeometry.finiteComplexGibbsPartition energy))) = 0 := by
  exact HTGeometry.finiteDerivativeReporterMap_postcomp_newBlindPacket
    report decode hcpost hcpre

end RHTower
