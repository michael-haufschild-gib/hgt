import GaloisForLFunctions.RHTower.InverseSquareChainCubicProjectiveFirstReturnLaw
import GaloisForLFunctions.RHTower.PairQubitProjectiveSeedWeakTwoLocalSameDrawLaw
import GaloisForLFunctions.RHTower.StaticChoiPhysicalNormalizedTraceBridgeLaw

/-!
# Physical projective return transported to the spectral Choi orbit

Matrix reindexing preserves Schrödinger evolution and normalized trace.
Consequently the inverse-square-chain cubic projective-return obstruction
survives both coordinate changes used by the ordinary two-local Gaussian
pencil and becomes a scalar-return exclusion for its spectral Choi orbit.
-/

open scoped Matrix Matrix.Norms.L2Operator
open Matrix Set

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

noncomputable section

/-- Schrödinger evolution is natural under finite matrix reindexing. -/
theorem unitaryEvolution_reindexAlgEquiv
    {m n : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    [Fintype n] [DecidableEq n] [Nonempty n]
    (e : m ≃ n) (H : Matrix m m ℂ) (t : ℝ) :
    Matrix.reindexAlgEquiv ℂ ℂ e (unitaryEvolution H t) =
      unitaryEvolution (Matrix.reindexAlgEquiv ℂ ℂ e H) t := by
  letI : NormedAlgebra ℚ (Matrix m m ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ (Matrix m m ℂ)
  letI : NormedAlgebra ℚ (Matrix n n ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ (Matrix n n ℂ)
  let E := Matrix.reindexAlgEquiv ℂ ℂ e
  unfold unitaryEvolution
  change E (NormedSpace.exp (t • ((-Complex.I) • H))) =
    NormedSpace.exp (t • ((-Complex.I) • E H))
  have harg : E.toRingEquiv (t • ((-Complex.I) • H)) =
      t • ((-Complex.I) • E H) := by
    ext i j
    simp [E, Matrix.reindexAlgEquiv, Complex.real_smul]
  calc
    E (NormedSpace.exp (t • ((-Complex.I) • H))) =
        E.toRingEquiv (NormedSpace.exp (t • ((-Complex.I) • H))) := rfl
    _ = NormedSpace.exp (E.toRingEquiv (t • ((-Complex.I) • H))) :=
      NormedSpace.map_exp E.toRingEquiv
        E.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional _
    _ = NormedSpace.exp (t • ((-Complex.I) • E H)) :=
      congrArg NormedSpace.exp harg

/-- Matrix trace is invariant under simultaneous row-column reindexing. -/
theorem trace_reindexAlgEquiv
    {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n]
    (e : m ≃ n) (A : Matrix m m ℂ) :
    Matrix.trace (Matrix.reindexAlgEquiv ℂ ℂ e A) = Matrix.trace A := by
  simp only [Matrix.trace, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  exact e.symm.sum_comp (fun x => A x x)

/-- Normalized trace of a static evolution is coordinate invariant. -/
theorem normalizedTrace_unitaryEvolution_reindexAlgEquiv
    {m n : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    [Fintype n] [DecidableEq n] [Nonempty n]
    (e : m ≃ n) (H : Matrix m m ℂ) (t : ℝ) :
    (Fintype.card n : ℂ)⁻¹ * Matrix.trace
        (unitaryEvolution (Matrix.reindexAlgEquiv ℂ ℂ e H) t) =
      (Fintype.card m : ℂ)⁻¹ * Matrix.trace (unitaryEvolution H t) := by
  rw [← unitaryEvolution_reindexAlgEquiv, trace_reindexAlgEquiv]
  rw [Fintype.card_congr e]

/-- The canonical finite-coordinate pencil Hamiltonian is exactly the
physical projective-seed draw transported through its two reindexings. -/
theorem pairQubitProjective_finiteHamiltonian_eq_doubleReindex
    (L : ℕ) (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ)
    (scale : ℝ) (x : TwoLocalPauliCoefficientSpace (L * 2)) :
    (twoLocalPauliGaussianHermitianPencil (L * 2)).affineReindexedHamiltonian
        (pairQubitProjectivePauliSeed L p) (scale • x) =
      Matrix.reindexAlgEquiv ℂ ℂ
          (Fintype.equivFin (FiniteQubitConfiguration (Fin (L * 2))))
        (Matrix.reindexAlgEquiv ℂ ℂ (pairQubitPathConfigurationEquiv L)
          (projectiveSeedWeakTwoLocalHamiltonian L p scale x)) := by
  rw [← pairQubitProjectiveSeed_reindexedHamiltonian_eq_physical]
  simp [FiniteGaussianHermitianPencil.affineReindexedHamiltonian,
    twoLocalPauliGaussianHermitianPencil_hamiltonian]

/-- Cubic projective-return control for the spectral Choi orbit of the same
ordinary static two-local draw used by the growth theorem. -/
theorem pairQubitProjective_spectralChoiScalar_cubic_le
    {L : ℕ} (hL : 2 ≤ L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    {rho scale guard : ℝ}
    (hseed : ‖nearestNeighborPathLocalHamiltonian L p -
        inverseSquareChainHamiltonian L‖ ≤
      rho * nearestNeighborPathLocalGeneratorMass L)
    {x : TwoLocalPauliCoefficientSpace (L * 2)}
    (hx : x ∈ weakTwoLocalPauliCertifiedGrowthSet L)
    (hguard : 0 ≤ guard) {t : ℝ}
    (ht : t ∈ Icc guard (2 * Real.pi * (L : ℝ) ^ 3 - guard)) :
    ‖inner ℂ
        (staticSpectralChoiVector
          (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))) t
          (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x))
        (staticSpectralChoiVector
          (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))) 0
          (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x))‖ ≤
      Real.sqrt (1 - inverseSquareChainCubicReturnSeparation L guard ^ 2 /
        (2 * (Fintype.card (Config (PairQubit L)) : ℝ) ^ 2)) +
      |t| * (rho * nearestNeighborPathLocalGeneratorMass L +
        |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3)) := by
  let P := twoLocalPauliGaussianHermitianPencil (L * 2)
  let Hfin := P.affineReindexedHamiltonian
    (pairQubitProjectivePauliSeed L p) (scale • x)
  let K := projectiveSeedWeakTwoLocalHamiltonian L p scale x
  have hHfin : Hfin.IsHermitian := by
    exact P.affineReindexedHamiltonian_isHermitian
      (pairQubitProjectivePauliSeed_isHermitian L p) (scale • x)
  have hcard : 0 < Fintype.card
      (FiniteQubitConfiguration (Fin (L * 2))) := Fintype.card_pos
  have hbridge :=
    norm_inner_staticSpectralChoiVector_zero_eq_norm_normalizedTrace_unitaryEvolution
      hcard hHfin t
  have hfin : Hfin =
      Matrix.reindexAlgEquiv ℂ ℂ
          (Fintype.equivFin (FiniteQubitConfiguration (Fin (L * 2))))
        (Matrix.reindexAlgEquiv ℂ ℂ (pairQubitPathConfigurationEquiv L) K) := by
    exact pairQubitProjective_finiteHamiltonian_eq_doubleReindex L p scale x
  have htrace :
      (Fintype.card (FiniteQubitConfiguration (Fin (L * 2))) : ℂ)⁻¹ *
          Matrix.trace (unitaryEvolution Hfin t) =
        (Fintype.card (Config (PairQubit L)) : ℂ)⁻¹ *
          Matrix.trace (unitaryEvolution K t) := by
    rw [hfin]
    have houter := normalizedTrace_unitaryEvolution_reindexAlgEquiv
      (Fintype.equivFin (FiniteQubitConfiguration (Fin (L * 2))))
      (Matrix.reindexAlgEquiv ℂ ℂ (pairQubitPathConfigurationEquiv L) K) t
    have hinner := normalizedTrace_unitaryEvolution_reindexAlgEquiv
      (pairQubitPathConfigurationEquiv L) K t
    simpa using houter.trans hinner
  have hphysical := norm_perturbedInverseSquareChain_normalizedTrace_le
    hL K (projectiveSeedWeakTwoLocalHamiltonian_isSelfAdjoint L p scale x)
      hguard ht
  have hdiff :=
    norm_projectiveSeedWeakTwoLocalHamiltonian_sub_inverseSquareChain_le
      hL (rho := rho) (scale := scale) hseed hx
  rw [show pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x =
      hHfin.eigenvalues by rfl]
  rw [hbridge, htrace]
  exact hphysical.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hdiff (abs_nonneg t)))

/-- One time-uniform scalar threshold controls the complete cubic window. -/
theorem pairQubitProjective_spectralChoiScalar_cubic_lt
    {L : ℕ} (hL : 2 ≤ L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    {rho scale guard eta : ℝ}
    (hseed : ‖nearestNeighborPathLocalHamiltonian L p -
        inverseSquareChainHamiltonian L‖ ≤
      rho * nearestNeighborPathLocalGeneratorMass L)
    (hguard : 0 ≤ guard)
    (hbudget :
      Real.sqrt (1 - inverseSquareChainCubicReturnSeparation L guard ^ 2 /
          (2 * (Fintype.card (Config (PairQubit L)) : ℝ) ^ 2)) +
        (2 * Real.pi * (L : ℝ) ^ 3) *
          (rho * nearestNeighborPathLocalGeneratorMass L +
            |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3)) < eta)
    {x : TwoLocalPauliCoefficientSpace (L * 2)}
    (hx : x ∈ weakTwoLocalPauliCertifiedGrowthSet L)
    {t : ℝ}
    (ht : t ∈ Icc guard (2 * Real.pi * (L : ℝ) ^ 3 - guard)) :
    ‖inner ℂ
        (staticSpectralChoiVector
          (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))) t
          (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x))
        (staticSpectralChoiVector
          (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))) 0
          (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x))‖ < eta := by
  let B := rho * nearestNeighborPathLocalGeneratorMass L +
    |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3)
  have hdiff :=
    norm_projectiveSeedWeakTwoLocalHamiltonian_sub_inverseSquareChain_le
      hL (rho := rho) (scale := scale) hseed hx
  have hB : 0 ≤ B := (norm_nonneg _).trans hdiff
  have ht0 : 0 ≤ t := hguard.trans ht.1
  have htmax : |t| ≤ 2 * Real.pi * (L : ℝ) ^ 3 := by
    rw [abs_of_nonneg ht0]
    exact ht.2.trans (sub_le_self _ hguard)
  have htime : |t| * B ≤ (2 * Real.pi * (L : ℝ) ^ 3) * B :=
    mul_le_mul_of_nonneg_right htmax hB
  have hpoint := pairQubitProjective_spectralChoiScalar_cubic_le
    hL (rho := rho) (scale := scale) (guard := guard) hseed hx hguard ht
  have hbudget' :
      Real.sqrt (1 - inverseSquareChainCubicReturnSeparation L guard ^ 2 /
          (2 * (Fintype.card (Config (PairQubit L)) : ℝ) ^ 2)) +
        (2 * Real.pi * (L : ℝ) ^ 3) * B < eta := by
    simpa [B] using hbudget
  exact hpoint.trans_lt ((add_le_add le_rfl htime).trans_lt hbudget')

end

end RHTower
