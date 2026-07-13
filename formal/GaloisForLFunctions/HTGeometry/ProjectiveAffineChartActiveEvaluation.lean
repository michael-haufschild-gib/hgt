import GaloisForLFunctions.HTGeometry.ProjectiveAffineChartIncidenceBaseChange
import GaloisForLFunctions.HTGeometry.IteratedBlockEvaluation

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def projectiveChartBaseChangedQuotientMap
    {row κ : Type} [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (projectiveChartCoefficientRing j)) [p.IsPrime] :
    MvPolynomial (row × Fin n) (Localization.AtPrime p) →ₐ[Localization.AtPrime p]
      projectiveChartBaseChangedGlobalIncidenceRing q n z j exponent p :=
  Ideal.Quotient.mkₐ _ _

def projectiveChartActiveEquationData
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (projectiveChartCoefficientRing j)) [p.IsPrime]
    (i : Fin (Nat.card (projectiveChartGoodRow q z j p))) :
    BlockEquationData (Localization.AtPrime p)
      (projectiveChartBaseChangedGlobalIncidenceRing q n z j exponent p) n where
  polynomial := localizedCoefficientRowPolynomial q n z
    (projectiveChartCoefficient j) exponent p
      ((Finite.equivFin (projectiveChartGoodRow q z j p)).symm i).1
  point k := projectiveChartBaseChangedQuotientMap q n z j exponent p
    (MvPolynomial.X (((Finite.equivFin (projectiveChartGoodRow q z j p)).symm i).1, k))
  vanishes := by
    let b : projectiveChartGoodRow q z j p :=
      (Finite.equivFin (projectiveChartGoodRow q z j p)).symm i
    let Q := projectiveChartBaseChangedQuotientMap q n z j exponent p
    rw [show ((Finite.equivFin (projectiveChartGoodRow q z j p)).symm i).1 = b.1 by rfl]
    rw [← MvPolynomial.eval₂_rename_prod_mk
      (f := algebraMap (Localization.AtPrime p)
        (projectiveChartBaseChangedGlobalIncidenceRing q n z j exponent p))
      (g := fun bk : row × Fin n => Q (MvPolynomial.X bk))]
    have hQ : MvPolynomial.eval₂AlgHom (Localization.AtPrime p)
        (fun bk : row × Fin n => Q (MvPolynomial.X bk)) = Q := by
      ext bk
      simp [Q, projectiveChartBaseChangedQuotientMap]
    change (MvPolynomial.eval₂AlgHom (Localization.AtPrime p)
      (fun bk : row × Fin n => Q (MvPolynomial.X bk)))
        (projectiveChartBaseChangedRowPolynomial q n z j exponent p b.1) = 0
    rw [hQ]
    change Ideal.Quotient.mk _
      (projectiveChartBaseChangedRowPolynomial q n z j exponent p b.1) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have hmem : projectiveChartBaseChangedRowPolynomial q n z j exponent p b.1 ∈
        projectiveChartBaseChangedIncidenceIdeal q n z j exponent p :=
      Ideal.subset_span (Set.mem_range_self b.1)
    rwa [← projectiveChartGlobalIncidenceIdeal_map_localization] at hmem

/-- The active-block evaluation together with exact preimages of every active packet coordinate.
Packaging the map and its coordinate witnesses together makes the dependent base-change transport
part of the construction rather than an external cast calculation. -/
def projectiveChartActiveEvaluationPackage
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (projectiveChartCoefficientRing j)) [p.IsPrime] :
    { E : projectiveChartActiveBlockRing q n z j exponent p →ₐ[Localization.AtPrime p]
        projectiveChartBaseChangedGlobalIncidenceRing q n z j exponent p //
      ∀ (i : Fin (Nat.card (projectiveChartGoodRow q z j p))) (k : Fin n),
        ∃ x, E x = projectiveChartBaseChangedQuotientMap q n z j exponent p
          (MvPolynomial.X
            (((Finite.equivFin (projectiveChartGoodRow q z j p)).symm i).1, k)) } := by
  let D := List.ofFn fun i : Fin (Nat.card (projectiveChartGoodRow q z j p)) =>
    projectiveChartActiveEquationData q n z j exponent p i
  have hD : blockEquationPolynomials D =
      List.ofFn (fun i : Fin (Nat.card (projectiveChartGoodRow q z j p)) =>
        localizedCoefficientRowPolynomial q n z (projectiveChartCoefficient j) exponent p
          ((Finite.equivFin (projectiveChartGoodRow q z j p)).symm i).1) := by
    dsimp [blockEquationPolynomials, D]
    rw [List.map_ofFn]
    rfl
  change { E : iteratedUnitCoefficientBlockRing (Localization.AtPrime p)
      (List.ofFn (fun i : Fin (Nat.card (projectiveChartGoodRow q z j p)) =>
        localizedCoefficientRowPolynomial q n z (projectiveChartCoefficient j) exponent p
          ((Finite.equivFin (projectiveChartGoodRow q z j p)).symm i).1)) →ₐ[Localization.AtPrime p]
        projectiveChartBaseChangedGlobalIncidenceRing q n z j exponent p //
      ∀ (i : Fin (Nat.card (projectiveChartGoodRow q z j p))) (k : Fin n),
        ∃ x, E x = projectiveChartBaseChangedQuotientMap q n z j exponent p
          (MvPolynomial.X
            (((Finite.equivFin (projectiveChartGoodRow q z j p)).symm i).1, k)) }
  rw [← hD]
  refine ⟨iteratedBlockEvaluation D, ?_⟩
  intro i k
  let iD : Fin D.length := Fin.cast (by simp [D]) i
  refine ⟨iteratedBlockCoordinate D iD k, ?_⟩
  rw [iteratedBlockEvaluation_iteratedBlockCoordinate]
  simp [D, iD, projectiveChartActiveEquationData]

def projectiveChartActiveBlockEvaluation
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (projectiveChartCoefficientRing j)) [p.IsPrime] :
    projectiveChartActiveBlockRing q n z j exponent p →ₐ[Localization.AtPrime p]
      projectiveChartBaseChangedGlobalIncidenceRing q n z j exponent p :=
  (projectiveChartActiveEvaluationPackage q n z j exponent p).1

/-- Every active global packet coordinate has a preimage in the nested active-block quotient. -/
theorem projectiveChartActiveBlockEvaluation_exists_preimage
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (projectiveChartCoefficientRing j)) [p.IsPrime]
    (i : Fin (Nat.card (projectiveChartGoodRow q z j p))) (k : Fin n) :
    ∃ x : projectiveChartActiveBlockRing q n z j exponent p,
      projectiveChartActiveBlockEvaluation q n z j exponent p x =
        projectiveChartBaseChangedQuotientMap q n z j exponent p
          (MvPolynomial.X
            (((Finite.equivFin (projectiveChartGoodRow q z j p)).symm i).1, k)) :=
  (projectiveChartActiveEvaluationPackage q n z j exponent p).2 i k

end
end GaloisForLFunctions.HTGeometry
