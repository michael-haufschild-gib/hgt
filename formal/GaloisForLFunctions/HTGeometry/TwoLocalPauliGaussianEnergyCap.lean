import GaloisForLFunctions.HTGeometry.GaussianBoxMass
import GaloisForLFunctions.HTGeometry.GaussianRadialLaw
import GaloisForLFunctions.HTGeometry.PauliCommutatorGramStableRankFloor
import GaloisForLFunctions.HTGeometry.PauliCountOrderBounds
import GaloisForLFunctions.HTGeometry.PauliOperatorNormSandwich
import GaloisForLFunctions.HTGeometry.PolyExpDecayLimit

/-!
# A quenched polynomial energy cap for the Gaussian two-local ensemble

Every active coefficient of the ordinary two-local Pauli Hamiltonian is a
standard Gaussian coordinate.  A coordinate union bound gives a box whose
complement has vanishing mass.  On that same-draw box the operator norm of the
Hamiltonian is at most `18 n³`.

This is the energy input needed to turn fixed-time return-tube bounds into
continuous laboratory-time laws without replacing the static local ensemble by
a Haar or time-dependent ensemble.
-/

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every Euclidean coordinate of standard Gaussian measure is a standard
one-dimensional Gaussian. -/
theorem map_coordinate_stdGaussian {ι : Type*} [Fintype ι] (a : ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).map
      (fun x : EuclideanSpace ℝ ι => WithLp.ofLp x a) = gaussianReal 0 1 := by
  rw [← map_pi_eq_stdGaussian, Measure.map_map]
  · simpa [Function.comp_def] using
      (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) a).map_eq
  · exact (measurable_pi_apply a).comp
      (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurable
  · exact (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable

/-- Active traceless labels are counted by the nonidentity bounded-weight
Pauli polynomial. -/
theorem card_pauliTracelessLabel (n q : ℕ) :
    Fintype.card (PauliTracelessLabel n q) =
      Quantum.nonidentityPauliWeightCount n q := by
  rw [← card_nonidentityPauliWords]
  exact (Fintype.card_congr
    (boundedLocalPauliLabelEquivTraceless n q)).symm.trans
      (Fintype.card_coe (nonidentityPauliWords n q))

/-- The operator norm of the active Hamiltonian is at most its coefficient
`ℓ¹` norm. -/
theorem norm_realActivePauliHamiltonian_le_sum
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n) :
    ‖realActivePauliHamiltonian x‖ ≤
      ∑ Q : PauliTracelessLabel n 2, |WithLp.ofLp x Q| := by
  rw [realActivePauliHamiltonian, activePauliHamiltonian]
  refine le_trans (norm_sum_le _ _) ?_
  apply Finset.sum_le_sum
  intro Q _
  rw [norm_smul, norm_finitePauliMatrix, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

/-- A uniform coordinate bound gives the exact coefficient-count operator
norm bound. -/
theorem norm_realActivePauliHamiltonian_le_card_mul
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n) {B : ℝ}
    (hB : ∀ Q, |WithLp.ofLp x Q| ≤ B) :
    ‖realActivePauliHamiltonian x‖ ≤
      (Fintype.card (PauliTracelessLabel n 2) : ℝ) * B := by
  refine (norm_realActivePauliHamiltonian_le_sum x).trans ?_
  calc
    (∑ Q : PauliTracelessLabel n 2, |WithLp.ofLp x Q|) ≤
        ∑ _Q : PauliTracelessLabel n 2, B :=
      Finset.sum_le_sum fun Q _ => hB Q
    _ = (Fintype.card (PauliTracelessLabel n 2) : ℝ) * B := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The real active Pauli Hamiltonian is self-adjoint for every coefficient
draw. -/
theorem isSelfAdjoint_realActivePauliHamiltonian
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n) :
    IsSelfAdjoint (realActivePauliHamiltonian x) := by
  rw [← Matrix.isHermitian_iff_isSelfAdjoint]
  rw [realActivePauliHamiltonian, activePauliHamiltonian,
    Matrix.IsHermitian, Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro Q _
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
  congr 1
  exact finitePauliMatrix_isHermitian Q.1

/-- Same-draw Gaussian coefficient box at height `n`. -/
def twoLocalPauliCoefficientBox (n : ℕ) :
    Set (TwoLocalPauliCoefficientSpace n) :=
  {x | ∀ Q, |WithLp.ofLp x Q| ≤ n}

/-- Exact coordinate-union tail for the same-draw coefficient box. -/
theorem stdGaussian_twoLocalPauli_measure_coefficientBox_compl_le (n : ℕ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (twoLocalPauliCoefficientBox n)ᶜ ≤
      (Fintype.card (PauliTracelessLabel n 2) : ℝ) *
        (2 * Real.exp (-(n : ℝ) ^ (2 : ℕ) / 2)) := by
  classical
  have hcompl : (twoLocalPauliCoefficientBox n)ᶜ ⊆
      ⋃ Q : PauliTracelessLabel n 2,
        {x : TwoLocalPauliCoefficientSpace n |
          (n : ℝ) ≤ |WithLp.ofLp x Q|} := by
    intro x hx
    rw [twoLocalPauliCoefficientBox, Set.mem_compl_iff,
      Set.mem_setOf_eq] at hx
    push Not at hx
    obtain ⟨Q, hQ⟩ := hx
    exact Set.mem_iUnion.mpr ⟨Q, hQ.le⟩
  calc
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (twoLocalPauliCoefficientBox n)ᶜ ≤
        (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
          (⋃ Q : PauliTracelessLabel n 2,
            {x : TwoLocalPauliCoefficientSpace n |
              (n : ℝ) ≤ |WithLp.ofLp x Q|}) :=
      measureReal_mono hcompl (measure_ne_top _ _)
    _ ≤ ∑ Q : PauliTracelessLabel n 2,
        (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
          {x | (n : ℝ) ≤ |WithLp.ofLp x Q|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _Q : PauliTracelessLabel n 2,
        2 * Real.exp (-(n : ℝ) ^ (2 : ℕ) / 2) := by
      apply Finset.sum_le_sum
      intro Q _
      apply measureReal_abs_ge_le_of_standardGaussian
      · exact ((measurable_pi_apply Q).comp
          (MeasurableEquiv.toLp 2
            (PauliTracelessLabel n 2 → ℝ)).symm.measurable).aemeasurable
      · exact map_coordinate_stdGaussian Q
      · positivity
    _ = (Fintype.card (PauliTracelessLabel n 2) : ℝ) *
        (2 * Real.exp (-(n : ℝ) ^ (2 : ℕ) / 2)) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- On the coefficient box, one ordinary two-local Hamiltonian has the
deterministic polynomial energy cap `18 n³`. -/
theorem norm_realActivePauliHamiltonian_le_eighteen_mul_cube_of_mem_box
    {n : ℕ} (hn : 1 ≤ n) {x : TwoLocalPauliCoefficientSpace n}
    (hx : x ∈ twoLocalPauliCoefficientBox n) :
    ‖realActivePauliHamiltonian x‖ ≤ 18 * (n : ℝ) ^ (3 : ℕ) := by
  have hcard : Fintype.card (PauliTracelessLabel n 2) ≤ 18 * n ^ (2 : ℕ) := by
    rw [card_pauliTracelessLabel]
    simpa using Quantum.nonidentityPauliWeightCount_le n 2 hn
  have hbase := norm_realActivePauliHamiltonian_le_card_mul x
    (B := (n : ℝ)) hx
  calc
    ‖realActivePauliHamiltonian x‖ ≤
        (Fintype.card (PauliTracelessLabel n 2) : ℝ) * (n : ℝ) := hbase
    _ ≤ ((18 * n ^ (2 : ℕ) : ℕ) : ℝ) * (n : ℝ) := by
      gcongr
    _ = 18 * (n : ℝ) ^ (3 : ℕ) := by
      push_cast
      ring

/-- The same-draw polynomial energy cap holds with probability tending to
one. -/
theorem tendsto_stdGaussian_twoLocalPauli_coefficientBox_compl_atTop :
    Tendsto
      (fun n : ℕ =>
        (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
          (twoLocalPauliCoefficientBox n)ᶜ)
      atTop (nhds 0) := by
  have hmajorReal : Tendsto
      (fun y : ℝ => 36 * (y ^ (2 : ℕ) * Real.exp (-((1 / 2 : ℝ) * y))))
      atTop (nhds 0) := by
    simpa using
      (tendsto_pow_mul_exp_neg_scaled 2
        (by norm_num : (0 : ℝ) < 1 / 2)).const_mul 36
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hmajor : Tendsto
      (fun n : ℕ => 36 * ((n : ℝ) ^ (2 : ℕ) * Real.exp (-(n : ℝ) / 2)))
      atTop (nhds 0) := by
    have hcomp := hmajorReal.comp hcast
    apply hcomp.congr'
    exact Filter.Eventually.of_forall fun n => by
      simp only [Function.comp_apply]
      congr 2
      ring_nf
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun _n => measureReal_nonneg) ?_ hmajor
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hcard : Fintype.card (PauliTracelessLabel n 2) ≤ 18 * n ^ (2 : ℕ) := by
    rw [card_pauliTracelessLabel]
    simpa using Quantum.nonidentityPauliWeightCount_le n 2 hn
  have htail := stdGaussian_twoLocalPauli_measure_coefficientBox_compl_le n
  have hexp : Real.exp (-(n : ℝ) ^ (2 : ℕ) / 2) ≤
      Real.exp (-(n : ℝ) / 2) := by
    apply Real.exp_le_exp.mpr
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  calc
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (twoLocalPauliCoefficientBox n)ᶜ ≤
      (Fintype.card (PauliTracelessLabel n 2) : ℝ) *
        (2 * Real.exp (-(n : ℝ) ^ (2 : ℕ) / 2)) := htail
    _ ≤ ((18 * n ^ (2 : ℕ) : ℕ) : ℝ) *
        (2 * Real.exp (-(n : ℝ) / 2)) := by
      gcongr
    _ = 36 * ((n : ℝ) ^ (2 : ℕ) * Real.exp (-(n : ℝ) / 2)) := by
      push_cast
      ring

end

end GaloisForLFunctions.HTGeometry
