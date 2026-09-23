import GaloisForLFunctions.HTGeometry.GridUnionOnset
import GaloisForLFunctions.HTGeometry.PauliIncidenceEntropyCompensation

/-!
# Polynomial laboratory-time grids for complete Pauli return tubes

Exact target-specific Pauli incidence absorbs both complete Pauli-dictionary
entropy and every fixed polynomial number of laboratory-time samples.  All
times use one static Gaussian two-local Hamiltonian draw.
-/

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def twoLocalPauliAllPauliReturnTubeEvent
    (n : ℕ) (t : ℝ) : Set (TwoLocalPauliCoefficientSpace n) :=
  ⋃ P : NonzeroPauliCharacter (Fin n), {x |
    (2 * ‖realActivePauliHamiltonian x‖ *
      hsNorm
        (unitaryEvolution (realActivePauliHamiltonian x) t -
          (finitePauliUnitary P.1 :
            Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ))) ^ (2 : ℕ) ≤
      (gaussianIntervalActivationMass / 2) *
        (4 * (2 : ℝ) ^ n *
          (2 * pauliWeight P.1 *
            (3 * n - 2 * pauliWeight P.1) : ℕ))}

theorem stdGaussian_twoLocalPauli_measure_allPauliReturnTubeEvent_le_binomial
    {n : ℕ} (t : ℝ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (twoLocalPauliAllPauliReturnTubeEvent n t) ≤
      (1 + 3 * Real.exp
        (-2 * (gaussianIntervalActivationMass ^ (2 : ℕ) / 2) * n)) ^ n - 1 := by
  simpa [twoLocalPauliAllPauliReturnTubeEvent] using
    stdGaussian_twoLocalPauli_measure_iUnion_allPauliReturnTube_le_binomial
      (n := n) t

/-- One static draw avoids the complete Pauli dictionary simultaneously on
any finite laboratory-time grid, paying exactly grid cardinality. -/
theorem stdGaussian_twoLocalPauli_measure_iUnion_time_allPauliReturnTube_le
    {n : ℕ} {iota : Type*} [Fintype iota] (time : iota → ℝ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ j : iota, twoLocalPauliAllPauliReturnTubeEvent n (time j)) ≤
      (Fintype.card iota : ℝ) *
        ((1 + 3 * Real.exp
          (-2 * (gaussianIntervalActivationMass ^ (2 : ℕ) / 2) * n)) ^ n - 1) := by
  apply measureReal_iUnion_le_card_mul
  intro j
  exact stdGaussian_twoLocalPauli_measure_allPauliReturnTubeEvent_le_binomial (time j)

theorem pauliIncidenceCompensatedBinomial_le_expEnvelope
    (a : ℝ) (n : ℕ) :
    (1 + 3 * Real.exp (-2 * a * n)) ^ n - 1 ≤
      Real.exp
        (3 * (n : ℝ) * Real.exp (-(2 * a * (n : ℝ)))) - 1 := by
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

/-- Every fixed polynomial number of laboratory-time samples is absorbed by
the exact Pauli incidence exponent. -/
theorem tendsto_pow_mul_pauliIncidenceCompensatedBinomial_atTop
    {a : ℝ} (ha : 0 < a) (d : ℕ) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) ^ d *
          ((1 + 3 * Real.exp (-2 * a * n)) ^ n - 1))
      atTop (nhds 0) := by
  let x : ℕ → ℝ := fun n =>
    3 * (n : ℝ) * Real.exp (-(2 * a * (n : ℝ)))
  have hx : Tendsto x atTop (nhds 0) := by
    have hreal :=
      (tendsto_pow_mul_exp_neg_scaled 1
        (by positivity : 0 < 2 * a)).const_mul 3
    have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hcomp : Tendsto
        ((fun y : ℝ => 3 * (y ^ (1 : ℕ) * Real.exp (-(2 * a * y)))) ∘
          fun n : ℕ => (n : ℝ)) atTop (nhds 0) := by
      simpa using hreal.comp hcast
    apply hcomp.congr'
    exact Filter.Eventually.of_forall fun n => by
      simp [x, Function.comp_apply, pow_one]
      ring
  have hxSmall : ∀ᶠ n in atTop, |x n| ≤ 1 := by
    have hlt : ∀ᶠ n in atTop, |x n| < 1 :=
      (tendsto_order.mp hx.norm).2 1 (by norm_num)
    filter_upwards [hlt] with n hn
    simpa [Real.norm_eq_abs] using hn.le
  have hmajorant :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) ^ d * (2 * x n))
        atTop (nhds 0) := by
    have hreal :=
      (tendsto_pow_mul_exp_neg_scaled (d + 1)
        (by positivity : 0 < 2 * a)).const_mul 6
    have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hcomp : Tendsto
        ((fun y : ℝ => 6 * (y ^ (d + 1) * Real.exp (-(2 * a * y)))) ∘
          fun n : ℕ => (n : ℝ)) atTop (nhds 0) := by
      simpa using hreal.comp hcast
    apply hcomp.congr'
    exact Filter.Eventually.of_forall fun n => by
      simp [x, Function.comp_apply, pow_succ]
      ring
  refine squeeze_zero' ?_ ?_ hmajorant
  · exact Filter.Eventually.of_forall fun n => by
      apply mul_nonneg (pow_nonneg (Nat.cast_nonneg n) d)
      apply sub_nonneg.mpr
      have hbase : (1 : ℝ) ≤ 1 + 3 * Real.exp (-2 * a * n) := by
        linarith [Real.exp_pos (-2 * a * n)]
      exact one_le_pow₀ hbase
  · filter_upwards [hxSmall] with n hn
    have hxNonneg : 0 ≤ x n := by positivity
    have henv := pauliIncidenceCompensatedBinomial_le_expEnvelope a n
    have habs := Real.abs_exp_sub_one_le hn
    have hsubNonneg : 0 ≤ Real.exp (x n) - 1 :=
      sub_nonneg.mpr (Real.one_le_exp hxNonneg)
    rw [abs_of_nonneg hsubNonneg, abs_of_nonneg hxNonneg] at habs
    exact mul_le_mul_of_nonneg_left (henv.trans habs)
      (pow_nonneg (Nat.cast_nonneg n) d)

/-- For every fixed polynomial grid degree and every choice of its laboratory
times, probability that one static draw returns to any nonidentity Pauli target
at any sampled time tends to zero. -/
theorem tendsto_stdGaussian_twoLocalPauli_polynomialGridReturnTubeProbability_atTop
    (d : ℕ) (time : (n : ℕ) → Fin (n ^ d) → ℝ) :
    Tendsto
      (fun n =>
        (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
          (⋃ j : Fin (n ^ d),
            twoLocalPauliAllPauliReturnTubeEvent n (time n j)))
      atTop (nhds 0) := by
  refine squeeze_zero
    (f := fun n =>
      (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (⋃ j : Fin (n ^ d),
          twoLocalPauliAllPauliReturnTubeEvent n (time n j)))
    (g := fun n =>
      (n : ℝ) ^ d *
        ((1 + 3 * Real.exp
          (-2 * (gaussianIntervalActivationMass ^ (2 : ℕ) / 2) * n)) ^ n - 1))
    ?_ ?_ ?_
  · intro n
    exact measureReal_nonneg
  · intro n
    simpa [Nat.cast_pow] using
      stdGaussian_twoLocalPauli_measure_iUnion_time_allPauliReturnTube_le
        (n := n) (time n)
  · exact tendsto_pow_mul_pauliIncidenceCompensatedBinomial_atTop
      (a := gaussianIntervalActivationMass ^ (2 : ℕ) / 2)
      (by nlinarith [gaussianIntervalActivationMass_pos]) d

end

end GaloisForLFunctions.HTGeometry
