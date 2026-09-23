import GaloisForLFunctions.HTGeometry.ContinuousPlateauGrid
import GaloisForLFunctions.HTGeometry.PauliPolynomialGridReturnLaw
import GaloisForLFunctions.HTGeometry.TracelessHermitianPauliSpan
import GaloisForLFunctions.HTGeometry.TwoLocalPauliGaussianEnergyCap

/-!
# Continuous laboratory-time avoidance of every Pauli return target

Fix any polynomial exponent `k` and any sequence of window origins.  Draw one
ordinary Gaussian two-local, time-independent Hamiltonian.  The probability
that its orbit enters the uniform return tube around any nonidentity Pauli
operator anywhere in the whole continuous window of length `n^k` tends to
zero.

The proof retains one quenched draw throughout.  Exact target incidence pays
the complete Pauli dictionary and a polynomial grid.  A high-probability
operator-norm cap controls interpolation between grid points.  Hilbert-space
dimension cancels between the return radius and the Schrödinger speed, leaving
a polynomial mesh.
-/

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Hilbert--Schmidt norm is at most square-root dimension times operator
norm. -/
theorem hsNorm_le_sqrt_card_mul_opNorm
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (A : Matrix d d ℂ) :
    hsNorm A ≤ Real.sqrt (Fintype.card d) * ‖A‖ := by
  have hsq : hsNorm A ^ (2 : ℕ) ≤ (Fintype.card d : ℝ) * ‖A‖ ^ (2 : ℕ) := by
    rw [← frobSq_eq_hsNorm_sq]
    exact frobSq_le_card_mul_opNorm_sq A
  calc
    hsNorm A = Real.sqrt (hsNorm A ^ (2 : ℕ)) :=
      (Real.sqrt_sq (hsNorm_nonneg A)).symm
    _ ≤ Real.sqrt ((Fintype.card d : ℝ) * ‖A‖ ^ (2 : ℕ)) :=
      Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (Fintype.card d) * ‖A‖ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg A)]

/-- Hilbert--Schmidt speed of a finite-dimensional static Hamiltonian orbit. -/
theorem hsNorm_unitaryEvolution_time_sub_le
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    {H : Matrix d d ℂ} (hH : IsSelfAdjoint H) (t u : ℝ) :
    hsNorm (unitaryEvolution H t - unitaryEvolution H u) ≤
      Real.sqrt (Fintype.card d) * ‖H‖ * |t - u| := by
  calc
    hsNorm (unitaryEvolution H t - unitaryEvolution H u) ≤
        Real.sqrt (Fintype.card d) *
          ‖unitaryEvolution H t - unitaryEvolution H u‖ :=
      hsNorm_le_sqrt_card_mul_opNorm _
    _ ≤ Real.sqrt (Fintype.card d) * (‖H‖ * |t - u|) := by
      gcongr
      exact norm_unitaryEvolution_time_sub_le hH t u
    _ = Real.sqrt (Fintype.card d) * ‖H‖ * |t - u| := by ring

/-- Return distance normalized by the commutator transfer factor used in the
fixed-time incidence law. -/
def twoLocalPauliScaledReturnDistance
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n) (t : ℝ)
    (P : NonzeroPauliCharacter (Fin n)) : ℝ :=
  2 * ‖realActivePauliHamiltonian x‖ *
    hsNorm (unitaryEvolution (realActivePauliHamiltonian x) t -
      (finitePauliUnitary P.1 :
        Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ))

/-- Uniform narrow return event.  Its squared radius is one quarter of the
smallest target-specific fixed-time tube. -/
def twoLocalPauliUniformNarrowReturnEvent (n : ℕ) (t : ℝ) :
    Set (TwoLocalPauliCoefficientSpace n) :=
  ⋃ P : NonzeroPauliCharacter (Fin n),
    {x | twoLocalPauliScaledReturnDistance x t P ^ (2 : ℕ) ≤
      gaussianIntervalActivationMass * (2 : ℝ) ^ n * n}

/-- Time variation of normalized return distance for one fixed draw and one
target. -/
theorem twoLocalPauliScaledReturnDistance_time_le
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n)
    (P : NonzeroPauliCharacter (Fin n)) (t u : ℝ) :
    twoLocalPauliScaledReturnDistance x u P ≤
      twoLocalPauliScaledReturnDistance x t P +
        2 * Real.sqrt ((2 : ℝ) ^ n) *
          ‖realActivePauliHamiltonian x‖ ^ (2 : ℕ) * |t - u| := by
  have hself := isSelfAdjoint_realActivePauliHamiltonian x
  have hdim : (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ) =
      (2 : ℝ) ^ n := by
    simp
  have htri := hsNorm_sub_le
    (unitaryEvolution (realActivePauliHamiltonian x) u)
    (unitaryEvolution (realActivePauliHamiltonian x) t)
    (finitePauliUnitary P.1 :
      Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ)
  have hspeed := hsNorm_unitaryEvolution_time_sub_le hself u t
  rw [hdim] at hspeed
  unfold twoLocalPauliScaledReturnDistance
  calc
    2 * ‖realActivePauliHamiltonian x‖ *
        hsNorm (unitaryEvolution (realActivePauliHamiltonian x) u -
          (finitePauliUnitary P.1 : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)) ≤
      2 * ‖realActivePauliHamiltonian x‖ *
        (hsNorm (unitaryEvolution (realActivePauliHamiltonian x) u -
            unitaryEvolution (realActivePauliHamiltonian x) t) +
          hsNorm (unitaryEvolution (realActivePauliHamiltonian x) t -
            (finitePauliUnitary P.1 : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ))) := by
        gcongr
    _ ≤ 2 * ‖realActivePauliHamiltonian x‖ *
        (Real.sqrt ((2 : ℝ) ^ n) * ‖realActivePauliHamiltonian x‖ * |u - t| +
          hsNorm (unitaryEvolution (realActivePauliHamiltonian x) t -
            (finitePauliUnitary P.1 : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ))) := by
        gcongr
    _ = 2 * ‖realActivePauliHamiltonian x‖ *
          hsNorm (unitaryEvolution (realActivePauliHamiltonian x) t -
            (finitePauliUnitary P.1 : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)) +
        2 * Real.sqrt ((2 : ℝ) ^ n) *
          ‖realActivePauliHamiltonian x‖ ^ (2 : ℕ) * |t - u| := by
      rw [abs_sub_comm]
      ring

/-- Every nonidentity Pauli target has at least the weight-one two-local
incidence. -/
theorem two_mul_n_le_twoLocalPauli_fullWeightPolynomial
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :
    2 * n ≤ 2 * pauliWeight P.1 * (3 * n - 2 * pauliWeight P.1) := by
  have hw1 : 1 ≤ pauliWeight P.1 := by
    have hw0 : pauliWeight P.1 ≠ 0 := by
      intro hzero
      exact P.2 ((pauliWeight_eq_zero_iff_eq_identity P.1).mp hzero)
    omega
  have hwn : pauliWeight P.1 ≤ n := pauliWeight_le P.1
  have hsub : n ≤ 3 * n - 2 * pauliWeight P.1 := by omega
  calc
    2 * n = 2 * (1 * n) := by ring
    _ ≤ 2 * (pauliWeight P.1 * n) := by gcongr
    _ ≤ 2 * (pauliWeight P.1 *
        (3 * n - 2 * pauliWeight P.1)) := by
      gcongr
    _ = 2 * pauliWeight P.1 *
        (3 * n - 2 * pauliWeight P.1) := by ring

/-- The uniform wide radius is below every target-specific incidence radius. -/
theorem twoLocalPauli_uniformWideThreshold_le_targetThreshold
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :
    4 * gaussianIntervalActivationMass * (2 : ℝ) ^ n * n ≤
      (gaussianIntervalActivationMass / 2) *
        (4 * (2 : ℝ) ^ n *
          (2 * pauliWeight P.1 *
            (3 * n - 2 * pauliWeight P.1) : ℕ)) := by
  have hinc := two_mul_n_le_twoLocalPauli_fullWeightPolynomial P
  have hincR : ((2 * n : ℕ) : ℝ) ≤
      ((2 * pauliWeight P.1 *
        (3 * n - 2 * pauliWeight P.1) : ℕ) : ℝ) := by
    exact_mod_cast hinc
  calc
    4 * gaussianIntervalActivationMass * (2 : ℝ) ^ n * n =
        (2 * gaussianIntervalActivationMass * (2 : ℝ) ^ n) *
          ((2 * n : ℕ) : ℝ) := by
      push_cast
      ring
    _ ≤ (2 * gaussianIntervalActivationMass * (2 : ℝ) ^ n) *
        ((2 * pauliWeight P.1 *
          (3 * n - 2 * pauliWeight P.1) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hincR
        (mul_nonneg
          (mul_nonneg (by norm_num) gaussianIntervalActivationMass_pos.le)
          (by positivity))
    _ = (gaussianIntervalActivationMass / 2) *
        (4 * (2 : ℝ) ^ n *
          (2 * pauliWeight P.1 *
            (3 * n - 2 * pauliWeight P.1) : ℕ)) := by ring

/-- On the quenched energy box, mesh `1/(648 n⁶)` changes normalized return
distance by at most square-root Hilbert dimension. -/
theorem twoLocalPauliScaledReturnDistance_increment_le_sqrtDimension
    {n : ℕ} (hn : 1 ≤ n) {x : TwoLocalPauliCoefficientSpace n}
    (hx : x ∈ twoLocalPauliCoefficientBox n) {t u : ℝ}
    (htu : |t - u| ≤ 1 / (648 * (n : ℝ) ^ (6 : ℕ)))
    (P : NonzeroPauliCharacter (Fin n)) :
    twoLocalPauliScaledReturnDistance x u P ≤
      twoLocalPauliScaledReturnDistance x t P +
        Real.sqrt ((2 : ℝ) ^ n) := by
  have hcap :=
    norm_realActivePauliHamiltonian_le_eighteen_mul_cube_of_mem_box hn hx
  have hbase := twoLocalPauliScaledReturnDistance_time_le x P t u
  refine hbase.trans ?_
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hnormsq : ‖realActivePauliHamiltonian x‖ ^ (2 : ℕ) ≤
      (18 * (n : ℝ) ^ (3 : ℕ)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (norm_nonneg _) hcap 2
  have hdelta :
      2 * Real.sqrt ((2 : ℝ) ^ n) *
          ‖realActivePauliHamiltonian x‖ ^ (2 : ℕ) * |t - u| ≤
        Real.sqrt ((2 : ℝ) ^ n) := by
    calc
      2 * Real.sqrt ((2 : ℝ) ^ n) *
          ‖realActivePauliHamiltonian x‖ ^ (2 : ℕ) * |t - u| ≤
        2 * Real.sqrt ((2 : ℝ) ^ n) *
          (18 * (n : ℝ) ^ (3 : ℕ)) ^ (2 : ℕ) *
            (1 / (648 * (n : ℝ) ^ (6 : ℕ))) := by
        gcongr
      _ = Real.sqrt ((2 : ℝ) ^ n) := by
        field_simp
        ring
  simpa [add_comm] using
    (add_le_add_left hdelta (twoLocalPauliScaledReturnDistance x t P))

/-- On the quenched energy box, a narrow return at one time forces a
target-specific fixed-time return at every nearby grid point. -/
theorem twoLocalPauli_uniformNarrowEvent_subset_wide
    {n : ℕ} (hn : 1 ≤ n)
    (hgn : 1 ≤ gaussianIntervalActivationMass * (n : ℝ))
    {t u : ℝ} (htu : |t - u| ≤ 1 / (648 * (n : ℝ) ^ (6 : ℕ))) :
    twoLocalPauliCoefficientBox n ∩
        twoLocalPauliUniformNarrowReturnEvent n t ⊆
      twoLocalPauliAllPauliReturnTubeEvent n u := by
  classical
  rintro x ⟨hxbox, hx⟩
  rw [twoLocalPauliUniformNarrowReturnEvent, Set.mem_iUnion] at hx
  obtain ⟨P, hP⟩ := hx
  rw [twoLocalPauliAllPauliReturnTubeEvent, Set.mem_iUnion]
  refine ⟨P, ?_⟩
  have hdist0 : 0 ≤ twoLocalPauliScaledReturnDistance x t P := by
    unfold twoLocalPauliScaledReturnDistance
    exact mul_nonneg
      (mul_nonneg (by norm_num) (norm_nonneg _)) (hsNorm_nonneg _)
  have hthreshold0 :
      0 ≤ gaussianIntervalActivationMass * (2 : ℝ) ^ n * n := by
    exact mul_nonneg
      (mul_nonneg gaussianIntervalActivationMass_pos.le (by positivity))
      (Nat.cast_nonneg n)
  have hnarrow : twoLocalPauliScaledReturnDistance x t P ≤
      Real.sqrt (gaussianIntervalActivationMass * (2 : ℝ) ^ n * n) := by
    calc
      twoLocalPauliScaledReturnDistance x t P =
          Real.sqrt (twoLocalPauliScaledReturnDistance x t P ^ (2 : ℕ)) :=
        (Real.sqrt_sq hdist0).symm
      _ ≤ Real.sqrt
          (gaussianIntervalActivationMass * (2 : ℝ) ^ n * n) :=
        Real.sqrt_le_sqrt hP
  have hsqrtDim : Real.sqrt ((2 : ℝ) ^ n) ≤
      Real.sqrt (gaussianIntervalActivationMass * (2 : ℝ) ^ n * n) := by
    apply Real.sqrt_le_sqrt
    nlinarith [show (0 : ℝ) ≤ (2 : ℝ) ^ n by positivity]
  have htime :=
    twoLocalPauliScaledReturnDistance_increment_le_sqrtDimension
      hn hxbox htu P
  have hwideDist : twoLocalPauliScaledReturnDistance x u P ≤
      2 * Real.sqrt
        (gaussianIntervalActivationMass * (2 : ℝ) ^ n * n) := by
    linarith
  have hwideSq : twoLocalPauliScaledReturnDistance x u P ^ (2 : ℕ) ≤
      4 * gaussianIntervalActivationMass * (2 : ℝ) ^ n * n := by
    have hnonneg : 0 ≤ twoLocalPauliScaledReturnDistance x u P := by
      unfold twoLocalPauliScaledReturnDistance
      exact mul_nonneg
        (mul_nonneg (by norm_num) (norm_nonneg _)) (hsNorm_nonneg _)
    have hsqrtNonneg := Real.sqrt_nonneg
      (gaussianIntervalActivationMass * (2 : ℝ) ^ n * n)
    have hsqrtSq := Real.sq_sqrt hthreshold0
    nlinarith
  exact hwideSq.trans
    (twoLocalPauli_uniformWideThreshold_le_targetThreshold P)

/-- Polynomial grid times for a continuous window of length `n^k`. -/
def twoLocalPauliContinuumGridTime
    (k n : ℕ) (A : ℝ) (j : Fin (649 * n ^ (k + 7))) : ℝ :=
  A + (j : ℕ) * (1 / (648 * (n : ℝ) ^ (6 : ℕ)))

/-- The explicit polynomial grid covers the entire continuous polynomial
window. -/
theorem exists_twoLocalPauliContinuumGridTime_near
    (k : ℕ) {n : ℕ} (hn : 1 ≤ n) (A : ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc A (A + (n : ℝ) ^ k)) :
    ∃ j : Fin (649 * n ^ (k + 7)),
      |t - twoLocalPauliContinuumGridTime k n A j| ≤
        1 / (648 * (n : ℝ) ^ (6 : ℕ)) := by
  let mesh : ℝ := 1 / (648 * (n : ℝ) ^ (6 : ℕ))
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hmesh : 0 < mesh := by
    unfold mesh
    positivity
  obtain ⟨j, hj⟩ := exists_plateauGrid_near hmesh A ht
  have hquot : (n : ℝ) ^ k / mesh =
      (648 * n ^ (k + 6) : ℕ) := by
    unfold mesh
    push_cast
    field_simp
    rw [pow_add]
  have hcountEq : plateauGridCount ((n : ℝ) ^ k) mesh =
      648 * n ^ (k + 6) + 1 := by
    unfold plateauGridCount
    rw [hquot, Nat.ceil_natCast]
  have hcountLe : plateauGridCount ((n : ℝ) ^ k) mesh ≤
      649 * n ^ (k + 7) := by
    rw [hcountEq]
    have hnPow : 1 ≤ n ^ (k + 6) := one_le_pow₀ hn
    have hpowLe : n ^ (k + 6) ≤ n ^ (k + 7) :=
      Nat.pow_le_pow_right hn (by omega)
    omega
  let j' : Fin (649 * n ^ (k + 7)) :=
    ⟨j, lt_of_lt_of_le j.isLt hcountLe⟩
  refine ⟨j', ?_⟩
  simpa [twoLocalPauliContinuumGridTime, plateauGridPoint, mesh, j'] using hj

/-- Event of entering any uniform nonidentity Pauli return tube anywhere in a
continuous polynomial window. -/
def twoLocalPauliPolynomialWindowReturnEvent
    (k n : ℕ) (A : ℝ) : Set (TwoLocalPauliCoefficientSpace n) :=
  {x | ∃ t ∈ Set.Icc A (A + (n : ℝ) ^ k),
    x ∈ twoLocalPauliUniformNarrowReturnEvent n t}

/-- A continuous-window return is either an energy-cap failure or a fixed-time
return at one point of the polynomial grid. -/
theorem twoLocalPauli_polynomialWindowReturnEvent_subset
    (k : ℕ) {n : ℕ} (hn : 1 ≤ n)
    (hgn : 1 ≤ gaussianIntervalActivationMass * (n : ℝ)) (A : ℝ) :
    twoLocalPauliPolynomialWindowReturnEvent k n A ⊆
      (twoLocalPauliCoefficientBox n)ᶜ ∪
        ⋃ j : Fin (649 * n ^ (k + 7)),
          twoLocalPauliAllPauliReturnTubeEvent n
            (twoLocalPauliContinuumGridTime k n A j) := by
  intro x hx
  rcases hx with ⟨t, ht, hreturn⟩
  by_cases hxbox : x ∈ twoLocalPauliCoefficientBox n
  · right
    obtain ⟨j, hj⟩ :=
      exists_twoLocalPauliContinuumGridTime_near k hn A ht
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    exact twoLocalPauli_uniformNarrowEvent_subset_wide
      hn hgn hj ⟨hxbox, hreturn⟩
  · exact Or.inl hxbox

/-- Explicit same-draw finite-`n` upper bound for the complete continuous
polynomial window. -/
theorem stdGaussian_twoLocalPauli_measure_polynomialWindowReturnEvent_le
    (k : ℕ) {n : ℕ} (hn : 1 ≤ n)
    (hgn : 1 ≤ gaussianIntervalActivationMass * (n : ℝ)) (A : ℝ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (twoLocalPauliPolynomialWindowReturnEvent k n A) ≤
      (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
          (twoLocalPauliCoefficientBox n)ᶜ +
        (649 : ℝ) * (n : ℝ) ^ (k + 7) *
          ((1 + 3 * Real.exp
            (-2 * (gaussianIntervalActivationMass ^ (2 : ℕ) / 2) * n)) ^ n - 1) := by
  have hsub := twoLocalPauli_polynomialWindowReturnEvent_subset k hn hgn A
  calc
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (twoLocalPauliPolynomialWindowReturnEvent k n A) ≤
      (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        ((twoLocalPauliCoefficientBox n)ᶜ ∪
          ⋃ j : Fin (649 * n ^ (k + 7)),
            twoLocalPauliAllPauliReturnTubeEvent n
              (twoLocalPauliContinuumGridTime k n A j)) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
          (twoLocalPauliCoefficientBox n)ᶜ +
        (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
          (⋃ j : Fin (649 * n ^ (k + 7)),
            twoLocalPauliAllPauliReturnTubeEvent n
              (twoLocalPauliContinuumGridTime k n A j)) :=
      measureReal_union_le _ _
    _ ≤ (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
          (twoLocalPauliCoefficientBox n)ᶜ +
        (Fintype.card (Fin (649 * n ^ (k + 7))) : ℝ) *
          ((1 + 3 * Real.exp
            (-2 * (gaussianIntervalActivationMass ^ (2 : ℕ) / 2) * n)) ^ n - 1) := by
      gcongr
      exact stdGaussian_twoLocalPauli_measure_iUnion_time_allPauliReturnTube_le
        (n := n) (twoLocalPauliContinuumGridTime k n A)
    _ = (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
          (twoLocalPauliCoefficientBox n)ᶜ +
        (649 : ℝ) * (n : ℝ) ^ (k + 7) *
          ((1 + 3 * Real.exp
            (-2 * (gaussianIntervalActivationMass ^ (2 : ℕ) / 2) * n)) ^ n - 1) := by
      simp [Nat.cast_mul, Nat.cast_pow]

/-- **Continuous polynomial-horizon Pauli return law.**  For every fixed
polynomial exponent and arbitrary sequence of window origins, one ordinary
time-independent Gaussian two-local Hamiltonian drawn once avoids every
nonidentity Pauli return tube throughout the complete continuous window with
probability tending to one. -/
theorem tendsto_stdGaussian_twoLocalPauli_polynomialWindowReturnProbability_atTop
    (k : ℕ) (A : ℕ → ℝ) :
    Tendsto
      (fun n =>
        (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
          (twoLocalPauliPolynomialWindowReturnEvent k n (A n)))
      atTop (nhds 0) := by
  have hgrid0 : Tendsto
      (fun n : ℕ =>
        (649 : ℝ) * (n : ℝ) ^ (k + 7) *
          ((1 + 3 * Real.exp
            (-2 * (gaussianIntervalActivationMass ^ (2 : ℕ) / 2) * n)) ^ n - 1))
      atTop (nhds 0) := by
    have hbase := tendsto_pow_mul_pauliIncidenceCompensatedBinomial_atTop
      (a := gaussianIntervalActivationMass ^ (2 : ℕ) / 2)
      (by nlinarith [gaussianIntervalActivationMass_pos]) (k + 7)
    convert hbase.const_mul 649 using 1 <;> simp
    funext n
    ring
  have hmajor0 : Tendsto
      (fun n : ℕ =>
        (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
            (twoLocalPauliCoefficientBox n)ᶜ +
          (649 : ℝ) * (n : ℝ) ^ (k + 7) *
            ((1 + 3 * Real.exp
              (-2 * (gaussianIntervalActivationMass ^ (2 : ℕ) / 2) * n)) ^ n - 1))
      atTop (nhds 0) := by
    simpa using
      tendsto_stdGaussian_twoLocalPauli_coefficientBox_compl_atTop.add hgrid0
  refine squeeze_zero'
    (f := fun n =>
      (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (twoLocalPauliPolynomialWindowReturnEvent k n (A n)))
    (g := fun n =>
      (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
          (twoLocalPauliCoefficientBox n)ᶜ +
        (649 : ℝ) * (n : ℝ) ^ (k + 7) *
          ((1 + 3 * Real.exp
            (-2 * (gaussianIntervalActivationMass ^ (2 : ℕ) / 2) * n)) ^ n - 1))
    (Filter.Eventually.of_forall fun _n => measureReal_nonneg) ?_ hmajor0
  obtain ⟨N, hN⟩ := exists_nat_gt
    (1 / gaussianIntervalActivationMass)
  filter_upwards [Filter.eventually_ge_atTop N,
    Filter.eventually_ge_atTop 1] with n hnN hn
  have hgn : 1 ≤ gaussianIntervalActivationMass * (n : ℝ) := by
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hnN
    have hlt : 1 / gaussianIntervalActivationMass < (n : ℝ) :=
      hN.trans_le hNn
    rw [div_lt_iff₀ gaussianIntervalActivationMass_pos] at hlt
    simpa [mul_comm] using hlt.le
  exact stdGaussian_twoLocalPauli_measure_polynomialWindowReturnEvent_le
    k hn hgn (A n)

end

end GaloisForLFunctions.HTGeometry
