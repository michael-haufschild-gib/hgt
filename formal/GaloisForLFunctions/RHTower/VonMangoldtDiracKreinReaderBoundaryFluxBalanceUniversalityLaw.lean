import GaloisForLFunctions.RHTower.VonMangoldtCyclicReaderFluxNoGo
import GaloisForLFunctions.RHTower.VonMangoldtWeightedMarginalBoundaryAnomaly
import GaloisForLFunctions.RHTower.VonMangoldtDiracKreinInertiaMarginalUniversalityLaw

/-!
# Von Mangoldt Dirac--Krein reader/boundary flux-balance universality

The cyclic-reader opening law and weighted marginal boundary anomaly use the same positive-order
relative moment.  On the exact finite Dirac--Krein realization, eliminating that moment gives a
conservation law: reader opening flux is cancelled exactly by the newly exposed symmetric density
boundary.  Positive data force strict reader growth, a negative boundary coefficient, and a
negative Krein direction simultaneously.
-/

open scoped BigOperators Matrix

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- **Exact reader/boundary flux balance.**  Across consecutive Dirac--Krein jet sections sharing
one weighted source marginal, the cyclic-reader increment and the new density-boundary flux cancel
after the common corner normalization is accounted for. -/
theorem finiteVonMangoldtDiracKrein_readerBoundaryFluxBalance
    {P : Type*} [Fintype P]
    (sourceDensity : Matrix P P ℝ) (jetDensity : ℕ → ℕ → ℝ)
    (B : Matrix P P ℝ) (M N : ℕ)
    (C0 : Matrix (P × Fin (N + 1)) (P × Fin (N + 1)) ℝ)
    (C1 : Matrix (P × Fin (N + 2)) (P × Fin (N + 2)) ℝ)
    (hJ0 :
      HTGeometry.densityBivariateJetMarginal sourceDensity C0 =
        finiteVonMangoldtSuccessorDiracKreinGram M (N + 1))
    (hP0 :
      HTGeometry.densityBivariateSourceMarginal
          (finiteVonMangoldtJetDensity jetDensity (N + 1)) C0 = B)
    (hJ1 :
      HTGeometry.densityBivariateJetMarginal sourceDensity C1 =
        finiteVonMangoldtSuccessorDiracKreinGram M (N + 2))
    (hP1 :
      HTGeometry.densityBivariateSourceMarginal
          (finiteVonMangoldtJetDensity jetDensity (N + 2)) C1 = B)
    (Φ0 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ →ₗ[ℝ] ℝ)
    (Φ1 : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ →ₗ[ℝ] ℝ)
    (hcyc0 : HTGeometry.MatrixCyclicReader Φ0)
    (hcyc1 : HTGeometry.MatrixCyclicReader Φ1)
    (hcorner :
      Φ0 (Matrix.single (0 : Fin (N + 1)) 0 1) =
        Φ1 (Matrix.single (0 : Fin (N + 2)) 0 1)) :
    jetDensity (N + 1) (N + 1) *
          (Φ1 (finiteVonMangoldtSuccessorDiracKreinGram M (N + 2)) -
            Φ0 (finiteVonMangoldtSuccessorDiracKreinGram M (N + 1))) +
        Φ0 (Matrix.single (0 : Fin (N + 1)) 0 1) *
          ∑ i : Fin (N + 1),
            (jetDensity (N + 1) i + jetDensity i (N + 1)) *
              finiteVonMangoldtSuccessorRelativeMoment M ((N + 1) + i + 2) =
      0 := by
  have hJ0' :
      HTGeometry.densityBivariateJetMarginal sourceDensity C0 =
        finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 1) := by
    simpa only [finiteVonMangoldtSuccessorDiracKreinGram_eq] using hJ0
  have hJ1' :
      HTGeometry.densityBivariateJetMarginal sourceDensity C1 =
        finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 2) := by
    simpa only [finiteVonMangoldtSuccessorDiracKreinGram_eq] using hJ1
  have hcancel :=
    fixedSourceDensityMarginals_force_boundaryCancellation
      sourceDensity jetDensity B M (N + 1) C0 C1 hJ0' hP0 hJ1' hP1
  have hopen :=
    finiteVonMangoldtSuccessor_cyclicReader_opening_eq
      M N Φ0 Φ1 hcyc0 hcyc1 hcorner
  have hopen' :
      Φ1 (finiteVonMangoldtSuccessorDiracKreinGram M (N + 2)) -
          Φ0 (finiteVonMangoldtSuccessorDiracKreinGram M (N + 1)) =
        Φ0 (Matrix.single (0 : Fin (N + 1)) 0 1) *
          finiteVonMangoldtSuccessorRelativeMoment M (2 * (N + 1) + 2) := by
    simpa only [finiteVonMangoldtSuccessorDiracKreinGram_eq] using hopen
  rw [hopen']
  calc
    jetDensity (N + 1) (N + 1) *
            (Φ0 (Matrix.single (0 : Fin (N + 1)) 0 1) *
              finiteVonMangoldtSuccessorRelativeMoment M (2 * (N + 1) + 2)) +
          Φ0 (Matrix.single (0 : Fin (N + 1)) 0 1) *
            ∑ i : Fin (N + 1),
              (jetDensity (N + 1) i + jetDensity i (N + 1)) *
                finiteVonMangoldtSuccessorRelativeMoment M ((N + 1) + i + 2) =
        Φ0 (Matrix.single (0 : Fin (N + 1)) 0 1) *
          (jetDensity (N + 1) (N + 1) *
              finiteVonMangoldtSuccessorRelativeMoment M (2 * (N + 1) + 2) +
            ∑ i : Fin (N + 1),
              (jetDensity (N + 1) i + jetDensity i (N + 1)) *
                finiteVonMangoldtSuccessorRelativeMoment M ((N + 1) + i + 2)) := by
      ring
    _ = 0 := by rw [hcancel, mul_zero]

/-- Positive data turn exact flux balance into a four-part obstruction certificate: strict reader
growth, a negative symmetric boundary coefficient, a negative Krein direction, and the exact
reader/boundary conservation identity. -/
theorem finiteVonMangoldtDiracKrein_readerBoundaryFluxObstructionUniversality
    {P : Type*} [Fintype P]
    (sourceDensity : Matrix P P ℝ) (jetDensity : ℕ → ℕ → ℝ)
    (B : Matrix P P ℝ) (M N : ℕ) (hM : 0 < M)
    (hdiag : 0 < jetDensity (N + 1) (N + 1))
    (C0 : Matrix (P × Fin (N + 1)) (P × Fin (N + 1)) ℝ)
    (C1 : Matrix (P × Fin (N + 2)) (P × Fin (N + 2)) ℝ)
    (hJ0 :
      HTGeometry.densityBivariateJetMarginal sourceDensity C0 =
        finiteVonMangoldtSuccessorDiracKreinGram M (N + 1))
    (hP0 :
      HTGeometry.densityBivariateSourceMarginal
          (finiteVonMangoldtJetDensity jetDensity (N + 1)) C0 = B)
    (hJ1 :
      HTGeometry.densityBivariateJetMarginal sourceDensity C1 =
        finiteVonMangoldtSuccessorDiracKreinGram M (N + 2))
    (hP1 :
      HTGeometry.densityBivariateSourceMarginal
          (finiteVonMangoldtJetDensity jetDensity (N + 2)) C1 = B)
    (Φ0 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ →ₗ[ℝ] ℝ)
    (Φ1 : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ →ₗ[ℝ] ℝ)
    (hcyc0 : HTGeometry.MatrixCyclicReader Φ0)
    (hcyc1 : HTGeometry.MatrixCyclicReader Φ1)
    (hpositive :
      0 < Φ0 (Matrix.single (0 : Fin (N + 1)) 0 1))
    (hcorner :
      Φ0 (Matrix.single (0 : Fin (N + 1)) 0 1) =
        Φ1 (Matrix.single (0 : Fin (N + 2)) 0 1)) :
    (Φ0 (finiteVonMangoldtSuccessorDiracKreinGram M (N + 1)) <
        Φ1 (finiteVonMangoldtSuccessorDiracKreinGram M (N + 2))) ∧
      (∃ i : Fin (N + 1),
        jetDensity (N + 1) i + jetDensity i (N + 1) < 0) ∧
      0 < sigNeg
        (finiteVonMangoldtSuccessorDiracKreinGram
          M (M + 1)).toQuadraticForm' ∧
      jetDensity (N + 1) (N + 1) *
            (Φ1 (finiteVonMangoldtSuccessorDiracKreinGram M (N + 2)) -
              Φ0 (finiteVonMangoldtSuccessorDiracKreinGram M (N + 1))) +
          Φ0 (Matrix.single (0 : Fin (N + 1)) 0 1) *
            ∑ i : Fin (N + 1),
              (jetDensity (N + 1) i + jetDensity i (N + 1)) *
                finiteVonMangoldtSuccessorRelativeMoment M ((N + 1) + i + 2) =
        0 := by
  have hJ0' :
      HTGeometry.densityBivariateJetMarginal sourceDensity C0 =
        finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 1) := by
    simpa only [finiteVonMangoldtSuccessorDiracKreinGram_eq] using hJ0
  have hJ1' :
      HTGeometry.densityBivariateJetMarginal sourceDensity C1 =
        finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 2) := by
    simpa only [finiteVonMangoldtSuccessorDiracKreinGram_eq] using hJ1
  have hreader :=
    finiteVonMangoldtSuccessor_cyclicReader_strictMono
      M N hM Φ0 Φ1 hcyc0 hcyc1 hpositive hcorner
  have hreader' :
      Φ0 (finiteVonMangoldtSuccessorDiracKreinGram M (N + 1)) <
        Φ1 (finiteVonMangoldtSuccessorDiracKreinGram M (N + 2)) := by
    simpa only [finiteVonMangoldtSuccessorDiracKreinGram_eq] using hreader
  have hboundary :=
    fixedSourceDensityMarginals_require_negativeBoundary
      sourceDensity jetDensity B M (N + 1) hM hdiag
        C0 C1 hJ0' hP0 hJ1' hP1
  exact
    ⟨hreader', hboundary,
      sigNeg_finiteVonMangoldtSuccessorDiracKreinGram_pos M hM,
      finiteVonMangoldtDiracKrein_readerBoundaryFluxBalance
        sourceDensity jetDensity B M N C0 C1 hJ0 hP0 hJ1 hP1
          Φ0 Φ1 hcyc0 hcyc1 hcorner⟩

end

end RHTower
