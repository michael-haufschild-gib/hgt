import GaloisForLFunctions.HTGeometry.FiniteBarycentricReader
import GaloisForLFunctions.RHTower.GammaJacobiEulerTailCyclicReaderNoGo
import GaloisForLFunctions.RHTower.VonMangoldtCounterreaderBarycentricAggregation
import GaloisForLFunctions.RHTower.XiPrimeSeamCofinalAnchoredCommutator

/-!
# Gamma--Jacobi barycentric pointed Euler reader

The surviving noncyclic Route M reader is an off-diagonal matrix coefficient of the commutator
between the FE--Schwarz functional calculus of the completed Euler clock and the exact
Gamma--Jacobi tail loss.  It retains an ordered prime edge and a spectral fibre before scalar
contraction.  The canonical counterreader coefficient supplies exact source-barycentric
normalization.

The construction is restriction-compatible, completed-Euler covariant, noncyclic, and odd under
centered FE--Schwarz reflection.  Its cofinal anchored flatness condition is equivalent to RH.
This is an exact connector, not an RH proof: no theorem below proves that flatness condition.
-/

open scoped BigOperators Matrix

namespace RHTower

noncomputable section

/-- Matrix-valued cyclicity predicate over `ℂ`, used only to state explicit noncyclicity of the
pointed reader. -/
def ComplexMatrixCyclicReader
    {I : Type*} [Fintype I] (reader : Matrix I I ℂ → ℂ) : Prop :=
  ∀ A B, reader (A * B) = reader (B * A)

/-- The canonical moment-normalized pointed matrix coefficient on one ordered edge. -/
def gammaJacobiBarycentricPointedReader
    {I : Type*} (moment : ℕ → ℝ) (i j : I) (A : Matrix I I ℂ) : ℂ :=
  (counterreaderFirstSymbolCoefficient moment : ℂ) * A i j

/-- The pointed reader is additive in the observed matrix. -/
theorem gammaJacobiBarycentricPointedReader_add
    {I : Type*} (moment : ℕ → ℝ) (i j : I) (A B : Matrix I I ℂ) :
    gammaJacobiBarycentricPointedReader moment i j (A + B) =
      gammaJacobiBarycentricPointedReader moment i j A +
        gammaJacobiBarycentricPointedReader moment i j B := by
  simp [gammaJacobiBarycentricPointedReader]
  ring

/-- The pointed reader is complex-linear in the observed matrix. -/
theorem gammaJacobiBarycentricPointedReader_smul
    {I : Type*} (moment : ℕ → ℝ) (i j : I) (z : ℂ) (A : Matrix I I ℂ) :
    gammaJacobiBarycentricPointedReader moment i j (z • A) =
      z * gammaJacobiBarycentricPointedReader moment i j A := by
  simp [gammaJacobiBarycentricPointedReader]
  ring

/-- Packet restriction preserves the corresponding marked reader value exactly. -/
theorem gammaJacobiBarycentricPointedReader_submatrix
    {I J : Type*} (moment : ℕ → ℝ) (f : I → J) (i j : I)
    (A : Matrix J J ℂ) :
    gammaJacobiBarycentricPointedReader moment i j (A.submatrix f f) =
      gammaJacobiBarycentricPointedReader moment (f i) (f j) A := by
  rfl

/-- Every nonzero off-diagonal pointed reader is genuinely noncyclic. -/
theorem gammaJacobiBarycentricPointedReader_not_cyclic
    {I : Type*} [Fintype I] [DecidableEq I]
    (moment : ℕ → ℝ) (i j : I) (hij : i ≠ j)
    (hcoefficient : counterreaderFirstSymbolCoefficient moment ≠ 0) :
    ¬ ComplexMatrixCyclicReader
        (gammaJacobiBarycentricPointedReader moment i j) := by
  classical
  intro hcyclic
  have h := hcyclic
    (Matrix.single i i (1 : ℂ)) (Matrix.single i j (1 : ℂ))
  have hleft :
      (Matrix.single i i (1 : ℂ) * Matrix.single i j (1 : ℂ)) i j = 1 := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp
    · intro k _ hki
      simp [Matrix.single, Ne.symm hki]
    · simp
  have hright :
      (Matrix.single i j (1 : ℂ) * Matrix.single i i (1 : ℂ)) i j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k = i
    · subst k
      simp [Matrix.single, hij, Ne.symm hij]
    · simp [Matrix.single, Ne.symm hki, hij]
  unfold gammaJacobiBarycentricPointedReader at h
  rw [hleft, hright, mul_one, mul_zero] at h
  exact (show (counterreaderFirstSymbolCoefficient moment : ℂ) ≠ 0 by
    exact_mod_cast hcoefficient) h

/-- **Reader-level barycentric aggregation.**  Accumulating marked source moments gives the
third-moment-weighted barycentre of the isolated pointed readers. -/
theorem gammaJacobiBarycentricPointedReader_finiteEdgeAccumulatedMoment
    {E I : Type*} [DecidableEq E]
    (edges : Finset E) (moment : E → ℕ → ℝ)
    (hedge3 : ∀ e ∈ edges, moment e 3 ≠ 0)
    (htotal3 : finiteEdgeAccumulatedMoment edges moment 3 ≠ 0)
    (i j : I) (A : Matrix I I ℂ) :
    gammaJacobiBarycentricPointedReader
        (finiteEdgeAccumulatedMoment edges moment) i j A =
      ∑ e ∈ edges,
        ((moment e 3 /
            finiteEdgeAccumulatedMoment edges moment 3 : ℝ) : ℂ) *
          gammaJacobiBarycentricPointedReader (moment e) i j A := by
  have hcoefficient :=
    counterreaderFirstSymbolCoefficient_finiteEdgeAccumulatedMoment
      edges moment hedge3 htotal3
  unfold gammaJacobiBarycentricPointedReader
  rw [hcoefficient]
  push_cast
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- **Route M dehomogenization.**  The barycentric reader is the projectivization of the additive
fourth-moment marked current. -/
theorem gammaJacobiBarycentricPointedReader_dehomogenization
    {I : Type*} (moment : ℕ → ℝ) (h3 : moment 3 ≠ 0)
    (i j : I) (A : Matrix I I ℂ) :
    (moment 3 : ℂ) * gammaJacobiBarycentricPointedReader moment i j A =
      -(moment 4 : ℂ) * A i j := by
  rw [gammaJacobiBarycentricPointedReader,
    counterreaderFirstSymbolCoefficient_eq moment h3]
  push_cast
  have h3c : (moment 3 : ℂ) ≠ 0 := by exact_mod_cast h3
  field_simp [h3c]

/-- Completed Euler multiplication on a finite integer-labelled packet. -/
def gammaJacobiCompletedEulerClock
    {I : Type*} [DecidableEq I] (p : I → ℕ) : Matrix I I ℂ :=
  Matrix.diagonal (fun i => (Real.log (p i : ℝ) : ℂ))

/-- The finite Gamma--Jacobi aperture loss, now on the complex matrix carrier used by the fibre
reader. -/
def gammaJacobiPrimeTailApertureLossComplex
    {I : Type*} (p : I → ℕ) (K : ℕ) : Matrix I I ℂ :=
  fun i j =>
    (gammaOddJacobiTailBoundaryReadout K (Real.log (p i : ℝ)) : ℂ) *
      (gammaOddJacobiTailBoundaryReadout K (Real.log (p j : ℝ)) : ℂ)

/-- Scalar FE--Schwarz functional calculus applied to a completed Euler label. -/
def completedEulerFESchwarzSymbol (rho : ℂ) (x : ℝ) : ℂ :=
  orbitwiseScaleSeamCharge (Real.exp x) rho

/-- At every positive integer scale, the Euler functional calculus is the canonical prime seam. -/
theorem completedEulerFESchwarzSymbol_log_eq_primeSeam
    {p : ℕ} (hp : 0 < p) (rho : ℂ) :
    completedEulerFESchwarzSymbol rho (Real.log (p : ℝ)) =
      orbitwiseNatPrimeSeamCharge p rho := by
  unfold completedEulerFESchwarzSymbol orbitwiseNatPrimeSeamCharge
  rw [Real.exp_log (by exact_mod_cast hp : (0 : ℝ) < (p : ℝ))]

/-- Diagonal FE--Schwarz functional calculus of the completed Euler clock. -/
def gammaJacobiPrimeSeamEulerFunctionalCalculus
    {I : Type*} [DecidableEq I] (p : I → ℕ) (rho : ℂ) : Matrix I I ℂ :=
  Matrix.diagonal (fun i => orbitwiseNatPrimeSeamCharge (p i) rho)

/-- The seam clock is literally scalar functional calculus of every completed Euler eigenvalue. -/
theorem gammaJacobiPrimeSeamEulerFunctionalCalculus_eq_symbol
    {I : Type*} [DecidableEq I] (p : I → ℕ) (hp : ∀ i, 0 < p i) (rho : ℂ) :
    gammaJacobiPrimeSeamEulerFunctionalCalculus p rho =
      Matrix.diagonal
        (fun i => completedEulerFESchwarzSymbol rho (Real.log (p i : ℝ))) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [gammaJacobiPrimeSeamEulerFunctionalCalculus,
      completedEulerFESchwarzSymbol_log_eq_primeSeam (hp i)]
  · simp [gammaJacobiPrimeSeamEulerFunctionalCalculus, Matrix.diagonal, hij]

/-- Edge/fibre-marked commutator between the Euler seam calculus and the exact tail loss. -/
def gammaJacobiPrimeSeamTailOrientation
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) (K : ℕ) (rho : ℂ) : Matrix I I ℂ :=
  gammaJacobiPrimeSeamEulerFunctionalCalculus p rho *
      gammaJacobiPrimeTailApertureLossComplex p K -
    gammaJacobiPrimeTailApertureLossComplex p K *
      gammaJacobiPrimeSeamEulerFunctionalCalculus p rho

/-- Exact ordered-edge value of the Gamma--Jacobi seam-tail orientation. -/
theorem gammaJacobiPrimeSeamTailOrientation_apply
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) (K : ℕ) (rho : ℂ) (i j : I) :
    gammaJacobiPrimeSeamTailOrientation p K rho i j =
      (orbitwiseNatPrimeSeamCharge (p i) rho -
          orbitwiseNatPrimeSeamCharge (p j) rho) *
        (gammaOddJacobiTailBoundaryReadout K (Real.log (p i : ℝ)) : ℂ) *
        (gammaOddJacobiTailBoundaryReadout K (Real.log (p j : ℝ)) : ℂ) := by
  unfold gammaJacobiPrimeSeamTailOrientation
    gammaJacobiPrimeSeamEulerFunctionalCalculus
  rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  unfold gammaJacobiPrimeTailApertureLossComplex
  ring

/-- The full marked orientation is compatible with restriction to a relabelled subpacket. -/
theorem gammaJacobiPrimeSeamTailOrientation_submatrix
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (p : J → ℕ) (f : I → J) (K : ℕ) (rho : ℂ) :
    (gammaJacobiPrimeSeamTailOrientation p K rho).submatrix f f =
      gammaJacobiPrimeSeamTailOrientation (p ∘ f) K rho := by
  ext i j
  change gammaJacobiPrimeSeamTailOrientation p K rho (f i) (f j) =
    gammaJacobiPrimeSeamTailOrientation (p ∘ f) K rho i j
  rw [gammaJacobiPrimeSeamTailOrientation_apply,
    gammaJacobiPrimeSeamTailOrientation_apply]
  rfl

/-- The pointed matrix coefficient intertwines the completed Euler derivation with the ordered
Euler-label difference. -/
theorem gammaJacobiBarycentricPointedReader_eulerCommutator
    {I : Type*} [Fintype I] [DecidableEq I]
    (moment : ℕ → ℝ) (p : I → ℕ) (i j : I) (A : Matrix I I ℂ) :
    gammaJacobiBarycentricPointedReader moment i j
        (gammaJacobiCompletedEulerClock p * A -
          A * gammaJacobiCompletedEulerClock p) =
      ((Real.log (p i : ℝ) - Real.log (p j : ℝ) : ℝ) : ℂ) *
        gammaJacobiBarycentricPointedReader moment i j A := by
  unfold gammaJacobiBarycentricPointedReader gammaJacobiCompletedEulerClock
  rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  push_cast
  ring

/-- Centered FE--Schwarz reflection reverses the full marked tail orientation. -/
theorem gammaJacobiPrimeSeamTailOrientation_lineReflect
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) (K : ℕ) (rho : ℂ) :
    gammaJacobiPrimeSeamTailOrientation p K
        (1 - starRingEnd ℂ rho) =
      -gammaJacobiPrimeSeamTailOrientation p K rho := by
  funext i j
  change gammaJacobiPrimeSeamTailOrientation p K
      (1 - starRingEnd ℂ rho) i j =
    -gammaJacobiPrimeSeamTailOrientation p K rho i j
  rw [gammaJacobiPrimeSeamTailOrientation_apply,
    gammaJacobiPrimeSeamTailOrientation_apply,
    orbitwiseNatPrimeSeamCharge_lineReflect,
    orbitwiseNatPrimeSeamCharge_lineReflect]
  ring

/-- Same-fibre pointed value form of the reflection-orientation law. -/
theorem gammaJacobiBarycentricPointedReader_orientation_lineReflect
    {I : Type*} [Fintype I] [DecidableEq I]
    (moment : ℕ → ℝ) (p : I → ℕ) (K : ℕ) (rho : ℂ) (i j : I) :
    gammaJacobiBarycentricPointedReader moment i j
        (gammaJacobiPrimeSeamTailOrientation p K
          (1 - starRingEnd ℂ rho)) =
      -gammaJacobiBarycentricPointedReader moment i j
        (gammaJacobiPrimeSeamTailOrientation p K rho) := by
  rw [gammaJacobiPrimeSeamTailOrientation_lineReflect]
  simp [gammaJacobiBarycentricPointedReader]

/-- Actual Gamma--Jacobi tail coordinates are nonzero at every prime label. -/
theorem gammaOddJacobiTailBoundaryReadout_natPrime_ne_zero
    {p K : ℕ} (hp : p.Prime) :
    (gammaOddJacobiTailBoundaryReadout K (Real.log (p : ℝ)) : ℂ) ≠ 0 := by
  let q : Nat.Primes := ⟨p, hp⟩
  exact_mod_cast gammaOddJacobiTailBoundaryReadout_prime_ne_zero q K

/-- A nonzero barycentric pointed reader detects exactly the difference of its two marked seam
values; no metric or cyclicity premise is involved. -/
theorem gammaJacobiBarycentricPointedReader_orientation_eq_zero_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    (moment : ℕ → ℝ) (hcoefficient : counterreaderFirstSymbolCoefficient moment ≠ 0)
    (p : I → ℕ) (hp : ∀ i, (p i).Prime) (K : ℕ) (rho : ℂ) (i j : I) :
    gammaJacobiBarycentricPointedReader moment i j
        (gammaJacobiPrimeSeamTailOrientation p K rho) = 0 ↔
      orbitwiseNatPrimeSeamCharge (p i) rho =
        orbitwiseNatPrimeSeamCharge (p j) rho := by
  rw [gammaJacobiBarycentricPointedReader,
    gammaJacobiPrimeSeamTailOrientation_apply]
  have hc : (counterreaderFirstSymbolCoefficient moment : ℂ) ≠ 0 := by
    exact_mod_cast hcoefficient
  have hi := gammaOddJacobiTailBoundaryReadout_natPrime_ne_zero (K := K) (hp i)
  have hj := gammaOddJacobiTailBoundaryReadout_natPrime_ne_zero (K := K) (hp j)
  simp [hc, hi, hj, sub_eq_zero]

/-- Every nonempty actual von-Mangoldt aperture gives a strictly negative, hence nonzero,
barycentric normalization. -/
theorem counterreaderFirstSymbolCoefficient_finiteVonMangoldt_neg
    (M : ℕ) (hM : 0 < M) :
    counterreaderFirstSymbolCoefficient
        (finiteVonMangoldtSuccessorRelativeMoment M) < 0 := by
  unfold counterreaderFirstSymbolCoefficient
  exact mul_neg_of_pos_of_neg (by norm_num)
    (finiteVonMangoldtHankelToeplitzCounterweight_one_neg M hM)

/-- Cofinal anchored flatness of the actual Route M pointed reader on every Xi divisor fibre. -/
def XiCofinalGammaJacobiBarycentricPointedReaderFlat
    (M K : ℕ) : Prop :=
  ∀ (rho : XiDivisorSupport) (N : ℕ), ∃ q : ℕ,
    q.Prime ∧ max N 2 < q ∧
      gammaJacobiBarycentricPointedReader
        (finiteVonMangoldtSuccessorRelativeMoment M)
        (0 : Fin 2) (1 : Fin 2)
        (gammaJacobiPrimeSeamTailOrientation
          (firstPrimeAnchoredPacket q) K (rho : ℂ)) = 0

/-- The finite pointed-reader condition is exactly the previously isolated cofinal Euler
compression condition.  The equivalence uses only nonvanishing source factors. -/
theorem xiCofinalGammaJacobiBarycentricPointedReaderFlat_iff_eulerCompression
    (M K : ℕ) (hM : 0 < M) (a : ℝ) (ha : 0 < a) :
    XiCofinalGammaJacobiBarycentricPointedReaderFlat M K ↔
      XiCofinalFirstPrimeEulerCompressionEssentiallyCommuting a := by
  have hcoefficient : counterreaderFirstSymbolCoefficient
      (finiteVonMangoldtSuccessorRelativeMoment M) ≠ 0 :=
    ne_of_lt (counterreaderFirstSymbolCoefficient_finiteVonMangoldt_neg M hM)
  constructor
  · intro hreader rho N
    obtain ⟨q, hq, hbound, hzero⟩ := hreader rho N
    have hq2 : 2 < q := (le_max_right N 2).trans_lt hbound
    have hp : ∀ i, (firstPrimeAnchoredPacket q i).Prime :=
      firstPrimeAnchoredPacket_prime hq
    have hseam :=
      (gammaJacobiBarycentricPointedReader_orientation_eq_zero_iff
        (finiteVonMangoldtSuccessorRelativeMoment M) hcoefficient
        (firstPrimeAnchoredPacket q) hp K (rho : ℂ)
        (0 : Fin 2) (1 : Fin 2)).mp hzero
    refine ⟨q, hq, hbound, ?_⟩
    apply (firstPrimeAnchoredEulerCompressionCommutator_isCompactOperator_iff
      ha hq hq2).mpr
    simpa [firstPrimeAnchoredPacket] using hseam
  · intro hcompression rho N
    obtain ⟨q, hq, hbound, hcompact⟩ := hcompression rho N
    have hq2 : 2 < q := (le_max_right N 2).trans_lt hbound
    have hp : ∀ i, (firstPrimeAnchoredPacket q i).Prime :=
      firstPrimeAnchoredPacket_prime hq
    have hseam :=
      (firstPrimeAnchoredEulerCompressionCommutator_isCompactOperator_iff
        ha hq hq2).mp hcompact
    refine ⟨q, hq, hbound, ?_⟩
    apply (gammaJacobiBarycentricPointedReader_orientation_eq_zero_iff
      (finiteVonMangoldtSuccessorRelativeMoment M) hcoefficient
      (firstPrimeAnchoredPacket q) hp K (rho : ℂ)
      (0 : Fin 2) (1 : Fin 2)).mpr
    simpa [firstPrimeAnchoredPacket] using hseam

/-- **Route M terminal connector.**  For every nonempty von-Mangoldt aperture and every
Gamma--Jacobi aperture, cofinal flatness of the explicit edge/fibre-marked barycentric pointed
reader is equivalent to RH.  This proves the connector, not its RH-bearing flatness premise. -/
theorem xiCofinalGammaJacobiBarycentricPointedReaderFlat_iff_riemannHypothesis
    (M K : ℕ) (hM : 0 < M) :
    XiCofinalGammaJacobiBarycentricPointedReaderFlat M K ↔
      RiemannHypothesis := by
  exact
    (xiCofinalGammaJacobiBarycentricPointedReaderFlat_iff_eulerCompression
      M K hM 1 (by norm_num)).trans
      (xiCofinalFirstPrimeEulerCompressionEssentiallyCommuting_iff_riemannHypothesis
        1 (by norm_num))

end

end RHTower
