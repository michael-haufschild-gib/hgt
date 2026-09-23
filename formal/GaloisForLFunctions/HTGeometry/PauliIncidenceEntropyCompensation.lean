import GaloisForLFunctions.HTGeometry.PauliCommutatorReturnTubeLaw
import GaloisForLFunctions.HTGeometry.PauliOperatorNormSandwich
import GaloisForLFunctions.HTGeometry.PolyExpDecayLimit

/-!
# Pauli entropy--incidence compensation

The exact two-local incidence polynomial permits a complete union over every
nonidentity Pauli target.  Weight-`w` targets have multiplicity
`3^w * n.choose w` but pay incidence `2w(3n-2w)`.  Summing target-specific
Gaussian tails therefore gives a binomial expression rather than the crude
cardinality times the weight-one exponent.
-/

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def finitePauliUnitary
    {n : ℕ} (P : Fin n → Option (Fin 3)) :
    Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ :=
  ⟨finitePauliMatrix P, finitePauliMatrix_mem_unitary P⟩

theorem pauliCoeff_finitePauliMatrix
    {n : ℕ} (P Q : Fin n → Option (Fin 3)) :
    pauliCoeff (finitePauliMatrix P) Q = if Q = P then 1 else 0 := by
  rw [pauliCoeff, ← finitePauliMatrixBasis_apply P,
    Module.Basis.repr_self, Finsupp.single_apply]
  simp [eq_comm]

theorem twoLocalPauliUnitaryFullWeightPolynomialMoment_finitePauliUnitary
    {n : ℕ} (P : NonzeroPauliCharacter (Fin n)) :
    twoLocalPauliUnitaryFullWeightPolynomialMoment (finitePauliUnitary P.1) =
      (2 * pauliWeight P.1 * (3 * n - 2 * pauliWeight P.1) : ℕ) := by
  rw [twoLocalPauliUnitaryFullWeightPolynomialMoment]
  rw [Finset.sum_eq_single P]
  · simp [finitePauliUnitary, pauliCoeff_finitePauliMatrix]
  · intro Q _ hQP
    have hval : Q.1 ≠ P.1 := by
      intro h
      exact hQP (Subtype.ext h)
    simp [finitePauliUnitary, pauliCoeff_finitePauliMatrix, hval]
  · intro hP
    exact absurd (Finset.mem_univ P) hP

/-- Regroup an arbitrary real Pauli-weight statistic by exact support shell. -/
theorem sum_pauliWeightFunction_eq_sum_choose_threePow
    {n : ℕ} (f : ℕ → ℝ) :
    (∑ P : Fin n → Option (Fin 3), f (pauliWeight P)) =
      ∑ k ∈ Finset.range (n + 1),
        ((n.choose k * 3 ^ k : ℕ) : ℝ) * f k := by
  have hmaps : ∀ P ∈ (Finset.univ : Finset (Fin n → Option (Fin 3))),
      pauliWeight P ∈ Finset.range (n + 1) := by
    intro P _
    rw [Finset.mem_range]
    have hle : (pauliSupport P).card ≤ n := by
      simpa using Finset.card_le_card
        (show pauliSupport P ⊆ (Finset.univ : Finset (Fin n)) from
          Finset.subset_univ _)
    rw [pauliWeight_eq_card_pauliSupport]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun P : Fin n → Option (Fin 3) => f (pauliWeight P))]
  apply Finset.sum_congr rfl
  intro k hk
  have hconst :
      (∑ P ∈ (Finset.univ : Finset (Fin n → Option (Fin 3))) with
          pauliWeight P = k, f (pauliWeight P)) =
        ((Finset.univ.filter fun P : Fin n → Option (Fin 3) =>
          pauliWeight P = k).card : ℝ) * f k := by
    rw [show (∑ P ∈ (Finset.univ : Finset (Fin n → Option (Fin 3))) with
        pauliWeight P = k, f (pauliWeight P)) =
      ∑ _P ∈ (Finset.univ.filter fun P : Fin n → Option (Fin 3) =>
        pauliWeight P = k), f k by
      apply Finset.sum_congr rfl
      intro P hP
      rw [Finset.mem_filter] at hP
      rw [hP.2]]
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hconst, card_filter_pauliWeight_eq]

/-- Closed partition function for all nonidentity Pauli support shells. -/
theorem sum_nonzeroPauli_weightPow_eq_binomial
    {n : ℕ} (z : ℝ) :
    (∑ P : NonzeroPauliCharacter (Fin n), z ^ pauliWeight P.1) =
      (1 + 3 * z) ^ n - 1 := by
  have hsub :
      (∑ P ∈ (Finset.univ.erase pauliCharacterZero :
          Finset (Fin n → Option (Fin 3))), z ^ pauliWeight P) =
        ∑ P : NonzeroPauliCharacter (Fin n), z ^ pauliWeight P.1 := by
    exact Finset.sum_subtype
      (Finset.univ.erase pauliCharacterZero)
      (by intro P; simp)
      (fun P : Fin n → Option (Fin 3) => z ^ pauliWeight P)
  have hall := sum_pauliWeightFunction_eq_sum_choose_threePow
    (n := n) (fun k => z ^ k)
  have hbinomial :
      (∑ k ∈ Finset.range (n + 1),
          ((n.choose k * 3 ^ k : ℕ) : ℝ) * z ^ k) =
        (1 + 3 * z) ^ n := by
    rw [show 1 + 3 * z = 3 * z + 1 by ring, add_pow]
    apply Finset.sum_congr rfl
    intro k hk
    norm_num [mul_pow]
    ring
  have hall' :
      (∑ P : Fin n → Option (Fin 3), z ^ pauliWeight P) =
        (1 + 3 * z) ^ n := hall.trans hbinomial
  have hsplit :
      (∑ P ∈ (Finset.univ.erase pauliCharacterZero :
          Finset (Fin n → Option (Fin 3))), z ^ pauliWeight P) + 1 =
        ∑ P : Fin n → Option (Fin 3), z ^ pauliWeight P := by
    calc
      (∑ P ∈ (Finset.univ.erase pauliCharacterZero :
          Finset (Fin n → Option (Fin 3))), z ^ pauliWeight P) + 1 =
        (∑ P ∈ (Finset.univ.erase pauliCharacterZero :
          Finset (Fin n → Option (Fin 3))), z ^ pauliWeight P) +
            z ^ pauliWeight pauliCharacterZero := by
              simp [pauliWeight, pauliCharacterZero]
      _ = ∑ P ∈ (Finset.univ : Finset (Fin n → Option (Fin 3))),
          z ^ pauliWeight P :=
        Finset.sum_erase_add _ _ (Finset.mem_univ pauliCharacterZero)
      _ = ∑ P : Fin n → Option (Fin 3), z ^ pauliWeight P := rfl
  have htotal :
      (∑ P ∈ (Finset.univ.erase pauliCharacterZero :
          Finset (Fin n → Option (Fin 3))), z ^ pauliWeight P) + 1 =
        (1 + 3 * z) ^ n := hsplit.trans hall'
  rw [hsub] at htotal
  linarith

/-- Incidence dominates shell entropy after summing the complete Pauli
dictionary. -/
theorem sum_nonzeroPauli_exp_neg_fullWeightPolynomial_le_binomial
    {n : ℕ} (a : ℝ) (ha : 0 ≤ a) :
    (∑ P : NonzeroPauliCharacter (Fin n),
        Real.exp (-a *
          (2 * pauliWeight P.1 *
            (3 * n - 2 * pauliWeight P.1) : ℕ))) ≤
      (1 + 3 * Real.exp (-2 * a * n)) ^ n - 1 := by
  calc
    (∑ P : NonzeroPauliCharacter (Fin n),
        Real.exp (-a *
          (2 * pauliWeight P.1 *
            (3 * n - 2 * pauliWeight P.1) : ℕ))) ≤
      ∑ P : NonzeroPauliCharacter (Fin n),
        (Real.exp (-2 * a * n)) ^ pauliWeight P.1 := by
      apply Finset.sum_le_sum
      intro P _
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hw : pauliWeight P.1 ≤ n := by
        rw [pauliWeight_eq_card_pauliSupport]
        simpa using Finset.card_le_card
          (show pauliSupport P.1 ⊆ (Finset.univ : Finset (Fin n)) from
            Finset.subset_univ _)
      have hnat :
          2 * pauliWeight P.1 * n ≤
            2 * pauliWeight P.1 *
              (3 * n - 2 * pauliWeight P.1) := by
        apply Nat.mul_le_mul_left (2 * pauliWeight P.1)
        omega
      have hreal :
          ((2 * pauliWeight P.1 * n : ℕ) : ℝ) ≤
            ((2 * pauliWeight P.1 *
              (3 * n - 2 * pauliWeight P.1) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      have hmul := mul_le_mul_of_nonpos_left hreal (neg_nonpos.mpr ha)
      push_cast at hmul ⊢
      nlinarith
    _ = (1 + 3 * Real.exp (-2 * a * n)) ^ n - 1 :=
      sum_nonzeroPauli_weightPow_eq_binomial _

/-- Complete all-Pauli entropy--incidence compensation at fixed Hamiltonian
time.  Exponentially many high-weight targets pay their quadratic incidence
instead of inheriting the weight-one exponent. -/
theorem stdGaussian_twoLocalPauli_measure_iUnion_allPauliCommutatorTube_le_binomial
    {n : ℕ} :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ P : NonzeroPauliCharacter (Fin n), {x |
          ‖twoLocalPauliUnitaryCommutatorMap (finitePauliUnitary P.1) x‖ ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                (2 * pauliWeight P.1 *
                  (3 * n - 2 * pauliWeight P.1) : ℕ))}) ≤
      (1 + 3 * Real.exp
        (-2 * (gaussianIntervalActivationMass ^ (2 : ℕ) / 2) * n)) ^ n - 1 := by
  let U : NonzeroPauliCharacter (Fin n) →
      Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ :=
    fun P => finitePauliUnitary P.1
  have hbase :=
    stdGaussian_twoLocalPauli_measure_iUnion_fullWeightPolynomialCommutatorTube_le U
  have hsum := sum_nonzeroPauli_exp_neg_fullWeightPolynomial_le_binomial
    (n := n) (gaussianIntervalActivationMass ^ (2 : ℕ) / 2) (by positivity)
  have hsum' :
      (∑ P : NonzeroPauliCharacter (Fin n),
        Real.exp (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryFullWeightPolynomialMoment (U P))) ≤
        (1 + 3 * Real.exp
          (-2 * (gaussianIntervalActivationMass ^ (2 : ℕ) / 2) * n)) ^ n - 1 := by
    simpa [U,
      twoLocalPauliUnitaryFullWeightPolynomialMoment_finitePauliUnitary] using hsum
  simpa [U,
    twoLocalPauliUnitaryFullWeightPolynomialMoment_finitePauliUnitary] using
      hbase.trans hsum'

/-- Same-draw dynamical version.  At every fixed laboratory time, return to
the complete nonidentity Pauli dictionary obeys the compensated binomial
bound for one ordinary static two-local Gaussian Hamiltonian draw. -/
theorem stdGaussian_twoLocalPauli_measure_iUnion_allPauliReturnTube_le_binomial
    {n : ℕ} (t : ℝ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ P : NonzeroPauliCharacter (Fin n), {x |
          (2 * ‖realActivePauliHamiltonian x‖ *
            hsNorm
              (unitaryEvolution (realActivePauliHamiltonian x) t -
                (finitePauliUnitary P.1 :
                  Matrix (FiniteQubitConfiguration (Fin n))
                    (FiniteQubitConfiguration (Fin n)) ℂ))) ^ (2 : ℕ) ≤
            (gaussianIntervalActivationMass / 2) *
              (4 * (2 : ℝ) ^ n *
                (2 * pauliWeight P.1 *
                  (3 * n - 2 * pauliWeight P.1) : ℕ))}) ≤
      (1 + 3 * Real.exp
        (-2 * (gaussianIntervalActivationMass ^ (2 : ℕ) / 2) * n)) ^ n - 1 := by
  let U : NonzeroPauliCharacter (Fin n) →
      Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ :=
    fun P => finitePauliUnitary P.1
  have hbase :=
    stdGaussian_twoLocalPauli_measure_iUnion_fullWeightPolynomialReturnTube_le U t
  have hsum := sum_nonzeroPauli_exp_neg_fullWeightPolynomial_le_binomial
    (n := n) (gaussianIntervalActivationMass ^ (2 : ℕ) / 2) (by positivity)
  have hsum' :
      (∑ P : NonzeroPauliCharacter (Fin n),
        Real.exp (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryFullWeightPolynomialMoment (U P))) ≤
        (1 + 3 * Real.exp
          (-2 * (gaussianIntervalActivationMass ^ (2 : ℕ) / 2) * n)) ^ n - 1 := by
    simpa [U,
      twoLocalPauliUnitaryFullWeightPolynomialMoment_finitePauliUnitary] using hsum
  simpa [U,
    twoLocalPauliUnitaryFullWeightPolynomialMoment_finitePauliUnitary] using
      hbase.trans hsum'

/-- For every positive fixed activation exponent, the compensated complete
Pauli union bound vanishes as qubit count tends to infinity. -/
theorem tendsto_pauliIncidenceCompensatedBinomial_atTop
    {a : ℝ} (ha : 0 < a) :
    Tendsto
      (fun n : ℕ =>
        (1 + 3 * Real.exp (-2 * a * n)) ^ n - 1)
      atTop (nhds 0) := by
  have hδ : 0 < 2 * a := by positivity
  have hdecayReal :=
    (tendsto_pow_mul_exp_neg_scaled 1 hδ).const_mul 3
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hdecay :
      Tendsto
        (fun n : ℕ =>
          3 * (n : ℝ) * Real.exp (-(2 * a * (n : ℝ))))
        atTop (nhds 0) := by
    have hcomp :
        Tendsto
          ((fun x : ℝ => 3 * (x ^ (1 : ℕ) * Real.exp (-(2 * a * x)))) ∘
            fun n : ℕ => (n : ℝ))
          atTop (nhds 0) := by
      simpa using hdecayReal.comp hcast
    apply hcomp.congr'
    exact Filter.Eventually.of_forall fun n => by
      simp [Function.comp_apply, pow_one]
      ring
  have hexp :
      Tendsto
        (fun n : ℕ =>
          Real.exp
            (3 * (n : ℝ) * Real.exp (-(2 * a * (n : ℝ)))) - 1)
        atTop (nhds 0) := by
    have hcontinuous := (Real.continuous_exp.tendsto 0).comp hdecay
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hsub := hcontinuous.sub hone
    simpa using hsub
  refine squeeze_zero
    (f := fun n : ℕ =>
      (1 + 3 * Real.exp (-2 * a * n)) ^ n - 1)
    (g := fun n : ℕ =>
      Real.exp
        (3 * (n : ℝ) * Real.exp (-(2 * a * (n : ℝ)))) - 1)
    ?_ ?_ hexp
  · intro n
    have hbase : (1 : ℝ) ≤ 1 + 3 * Real.exp (-2 * a * n) := by
      have hexpNonneg : 0 ≤ Real.exp (-2 * a * n) := (Real.exp_pos _).le
      nlinarith
    exact sub_nonneg.mpr (one_le_pow₀ hbase)
  · intro n
    apply sub_le_sub_right _ 1
    calc
      (1 + 3 * Real.exp (-2 * a * n)) ^ n ≤
          (Real.exp (3 * Real.exp (-2 * a * n))) ^ n := by
        apply pow_le_pow_left₀ (by positivity)
        linarith [Real.add_one_le_exp (3 * Real.exp (-2 * a * n))]
      _ = Real.exp
          (3 * (n : ℝ) * Real.exp (-(2 * a * (n : ℝ)))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring_nf

/-- Probability, for a static Gaussian two-local Pauli Hamiltonian, of lying
in the union of the exact return tubes around every nonidentity Pauli target. -/
noncomputable def twoLocalPauliAllPauliReturnTubeProbability
    (n : ℕ) (t : ℝ) : ℝ :=
  (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
    (⋃ P : NonzeroPauliCharacter (Fin n), {x |
      (2 * ‖realActivePauliHamiltonian x‖ *
        hsNorm
          (unitaryEvolution (realActivePauliHamiltonian x) t -
            (finitePauliUnitary P.1 :
              Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ))) ^ (2 : ℕ) ≤
        (gaussianIntervalActivationMass / 2) *
          (4 * (2 : ℝ) ^ n *
            (2 * pauliWeight P.1 *
              (3 * n - 2 * pauliWeight P.1) : ℕ))})

theorem twoLocalPauliAllPauliReturnTubeProbability_le_binomial
    (n : ℕ) (t : ℝ) :
    twoLocalPauliAllPauliReturnTubeProbability n t ≤
      (1 + 3 * Real.exp
        (-2 * (gaussianIntervalActivationMass ^ (2 : ℕ) / 2) * n)) ^ n - 1 := by
  exact stdGaussian_twoLocalPauli_measure_iUnion_allPauliReturnTube_le_binomial t

/-- Uniform-in-schedule asymptotic law. Along every chosen laboratory-time
schedule, probability of returning to any nonidentity Pauli target vanishes
with qubit count for the same static Hamiltonian draw at that size. -/
theorem tendsto_twoLocalPauliAllPauliReturnTubeProbability_atTop
    (time : ℕ → ℝ) :
    Tendsto
      (fun n => twoLocalPauliAllPauliReturnTubeProbability n (time n))
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact measureReal_nonneg
  · intro n
    exact twoLocalPauliAllPauliReturnTubeProbability_le_binomial n (time n)
  · exact tendsto_pauliIncidenceCompensatedBinomial_atTop
      (a := gaussianIntervalActivationMass ^ (2 : ℕ) / 2)
      (by nlinarith [gaussianIntervalActivationMass_pos])

end

end GaloisForLFunctions.HTGeometry
