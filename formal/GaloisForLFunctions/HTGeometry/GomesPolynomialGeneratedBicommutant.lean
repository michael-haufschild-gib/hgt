import GaloisForLFunctions.HTGeometry.GomesActualGeneratedSymmetryBoundary

/-!
# Exact commutant and bicommutant of the generated polynomial algebra

The generated algebra preserves constants. Its commutant consists precisely of
formal functions F(D²), and its bicommutant is the full D² symmetry algebra,
which forgets constant-line preservation. All statements concern actual operators.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry
variable (K : Type*) [Field K] [CharZero K]

/-- Every formal function of D² commutes with every actual second-derivative symmetry. -/
theorem gomesEvenFormalPolynomialOperator_commutes_fullSymmetry
    (F : PowerSeries K) (E : GomesPolynomialDerivativePowerCommutant K 2) :
    Commute (gomesEvenFormalPolynomialOperator K F) E.val := by
  have h := (Matrix.scalar_commute F (Commute.all F)
    (gomesPolynomialDerivativePowerCommutantEquiv K 2 E)).map (gomesTwoChainPolynomialAlgHom K)
  simpa only [gomesTwoChainPolynomialAlgHom_scalar, gomesTwoChainPolynomialAlgHom_matrix] using h

/-- The formal scalar variable acts as the actual second derivative. -/
theorem gomesEvenFormalPolynomialOperator_X :
    gomesEvenFormalPolynomialOperator K PowerSeries.X = (Polynomial.derivative ^ (2 : ℕ) : Module.End K K[X]) := by
  rw [gomesEvenFormalPolynomialOperator_eq_expanded, PowerSeries.expand_X,
    gomesFormalSeriesPolynomialOperator_X_pow]

/-- The full commutant of the generated actual algebra consists exactly of formal functions F(D²). -/
theorem gomesPolynomialDerivativeReflectionAdjoin_centralizer_mem_iff
    (c : K) (E : Module.End K K[X]) :
    E ∈ Subalgebra.centralizer K
      (gomesPolynomialDerivativeReflectionAdjoin K c : Set (Module.End K K[X])) ↔
        ∃ F : PowerSeries K, E = gomesEvenFormalPolynomialOperator K F := by
  constructor
  · intro h
    rw [Subalgebra.mem_centralizer_iff] at h
    have hD : (Polynomial.derivative : Module.End K K[X]) ∈ gomesPolynomialDerivativeReflectionAdjoin K c :=
      Algebra.subset_adjoin (Or.inl (Set.mem_insert _ _))
    have hR : gomesPolynomialReflectionEnd K c ∈ gomesPolynomialDerivativeReflectionAdjoin K c :=
      Algebra.subset_adjoin (Or.inl (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    exact (gomesPolynomialDerivativeReflection_joint_commutant K c E).mp ⟨(h _ hD).symm, (h _ hR).symm⟩
  · rintro ⟨F, rfl⟩
    rw [Subalgebra.mem_centralizer_iff]
    intro T hT
    let t : GomesPolynomialDerivativePowerCommutant K 2 :=
      ⟨T, (gomesCentralizerSingleton_mem_iff K _ _).mpr
        ((gomesPolynomialDerivativeReflectionAdjoin_mem_iff K c T).mp hT).1.eq.symm⟩
    exact (gomesEvenFormalPolynomialOperator_commutes_fullSymmetry K F t).eq.symm

/-- Taking commutants twice recovers exactly the full second-derivative symmetry algebra. -/
theorem gomesPolynomialDerivativeReflectionAdjoin_doubleCentralizer (c : K) :
    Subalgebra.centralizer K
      (Subalgebra.centralizer K (gomesPolynomialDerivativeReflectionAdjoin K c : Set (Module.End K K[X])) :
        Set (Module.End K K[X])) = gomesPolynomialDerivativePowerCommutantAlgebra K 2 := by
  ext E
  constructor
  · intro h
    rw [Subalgebra.mem_centralizer_iff] at h
    have hD : (Polynomial.derivative ^ (2 : ℕ) : Module.End K K[X]) ∈ Subalgebra.centralizer K
        (gomesPolynomialDerivativeReflectionAdjoin K c : Set (Module.End K K[X])) := by
      apply (gomesPolynomialDerivativeReflectionAdjoin_centralizer_mem_iff K c _).mpr
      exact ⟨PowerSeries.X, (gomesEvenFormalPolynomialOperator_X K).symm⟩
    exact (gomesCentralizerSingleton_mem_iff K _ _).mpr (h _ hD)
  · intro hE
    rw [Subalgebra.mem_centralizer_iff]
    intro T hT
    obtain ⟨F, rfl⟩ := (gomesPolynomialDerivativeReflectionAdjoin_centralizer_mem_iff K c T).mp hT
    exact (gomesEvenFormalPolynomialOperator_commutes_fullSymmetry K F ⟨E, hE⟩).eq

/-- The actual generated algebra is strictly smaller than its bicommutant, at every center. -/
theorem gomesPolynomialDerivativeReflectionAdjoin_lt_doubleCentralizer (c : K) :
    gomesPolynomialDerivativeReflectionAdjoin K c < Subalgebra.centralizer K
      (Subalgebra.centralizer K (gomesPolynomialDerivativeReflectionAdjoin K c : Set (Module.End K K[X])) :
        Set (Module.End K K[X])) := by
  rw [gomesPolynomialDerivativeReflectionAdjoin_doubleCentralizer]
  exact gomesPolynomialDerivativeReflectionAdjoin_lt_fullCommutant K c

end GaloisForLFunctions.HTGeometry
