import GaloisForLFunctions.HTGeometry.FiniteQuantumOperationalMemoryLaw

open Filter
open scoped BigOperators ComplexOrder MatrixOrder Topology

noncomputable section

namespace RHTower

def resetKraus {m : ℕ} (i0 j : Fin m) : QuantumMatrix m :=
  Matrix.single i0 j 1

theorem sum_resetKraus_star_mul
    {m : ℕ} [Nonempty (Fin m)] (i0 : Fin m) :
    ∑ j : Fin m, (resetKraus i0 j).conjTranspose * resetKraus i0 j = 1 := by
  simp [resetKraus, Matrix.sum_single_eq_diagonal]

def resetMixedKrausOperator
    {m : ℕ} [Nonempty (Fin m)]
    (U : QuantumMatrix m) (r : ℝ) (a : Fin (m + 1)) : QuantumMatrix m :=
  Fin.cases ((Real.sqrt r : ℂ) • U)
    (fun j => (Real.sqrt (1 - r) : ℂ) • resetKraus (Classical.choice ‹Nonempty (Fin m)›) j) a

theorem sum_resetMixedKrausOperator_star_mul
    {m : ℕ} [Nonempty (Fin m)]
    (U : QuantumMatrix m) (hU : U.conjTranspose * U = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∑ a : Fin (m + 1),
      (resetMixedKrausOperator U r a).conjTranspose *
        resetMixedKrausOperator U r a = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [resetMixedKrausOperator, Fin.cases_zero, Fin.cases_succ]
  rw [Matrix.conjTranspose_smul, smul_mul_smul_comm]
  rw [hU]
  simp_rw [Matrix.conjTranspose_smul, smul_mul_smul_comm]
  have hcr :
      star (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by
    rw [show star (Real.sqrt r : ℂ) = (Real.sqrt r : ℂ) by simp]
    exact_mod_cast (by simpa [pow_two] using Real.sq_sqrt hr0)
  have hc1r :
      star (Real.sqrt (1 - r) : ℂ) *
        (Real.sqrt (1 - r) : ℂ) = ((1 - r : ℝ) : ℂ) := by
    rw [show star (Real.sqrt (1 - r) : ℂ) =
      (Real.sqrt (1 - r) : ℂ) by simp]
    exact_mod_cast (by simpa [pow_two] using
      (Real.sq_sqrt (sub_nonneg.mpr hr1)))
  rw [hcr]
  simp_rw [hc1r]
  rw [← Finset.smul_sum, sum_resetKraus_star_mul]
  ext a b
  by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

def resetMixedKrausChannel
    {m : ℕ} [Nonempty (Fin m)]
    (U : QuantumMatrix m) (hU : U.conjTranspose * U = 1)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    FiniteKrausChannel m (m + 1) where
  operator := resetMixedKrausOperator U r
  completeness := sum_resetMixedKrausOperator_star_mul U hU hr0 hr1

def resetStateMatrix {m : ℕ} (i0 : Fin m) : QuantumMatrix m :=
  Matrix.single i0 i0 1

theorem resetKraus_evolve_eq
    {m : ℕ} [Nonempty (Fin m)] (i0 j : Fin m) (ρ : QuantumMatrix m) :
    resetKraus i0 j * ρ * (resetKraus i0 j).conjTranspose =
      (ρ j j) • resetStateMatrix i0 := by
  simp [resetKraus, resetStateMatrix, Matrix.conjTranspose_single,
    Matrix.single_mul_mul_single, Matrix.smul_single]

theorem sum_resetKraus_evolve_eq
    {m : ℕ} [Nonempty (Fin m)] (i0 : Fin m) (ρ : QuantumMatrix m) :
    ∑ j : Fin m, resetKraus i0 j * ρ * (resetKraus i0 j).conjTranspose =
      (Matrix.trace ρ) • resetStateMatrix i0 := by
  simp_rw [resetKraus_evolve_eq]
  rw [← Finset.sum_smul]
  rfl

theorem resetMixedKrausChannel_evolveMatrix_eq
    {m : ℕ} [Nonempty (Fin m)]
    (U : QuantumMatrix m) (hU : U.conjTranspose * U = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ρ : QuantumMatrix m) :
    (resetMixedKrausChannel U hU r hr0 hr1).evolveMatrix ρ =
      (r : ℂ) • (U * ρ * U.conjTranspose) +
        ((1 - r : ℝ) : ℂ) •
          ((Matrix.trace ρ) • resetStateMatrix (Classical.choice ‹Nonempty (Fin m)›)) := by
  rw [FiniteKrausChannel.evolveMatrix, Fin.sum_univ_succ]
  simp only [resetMixedKrausChannel, resetMixedKrausOperator,
    Fin.cases_zero, Fin.cases_succ]
  rw [Matrix.conjTranspose_smul]
  simp only [mul_smul_comm, smul_smul]
  simp_rw [Matrix.conjTranspose_smul]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  have hcr :
      star (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by
    rw [show star (Real.sqrt r : ℂ) = (Real.sqrt r : ℂ) by simp]
    exact_mod_cast (by simpa [pow_two] using Real.sq_sqrt hr0)
  have hc1r :
      star (Real.sqrt (1 - r) : ℂ) * (Real.sqrt (1 - r) : ℂ) =
        ((1 - r : ℝ) : ℂ) := by
    rw [show star (Real.sqrt (1 - r) : ℂ) =
      (Real.sqrt (1 - r) : ℂ) by simp]
    exact_mod_cast (by simpa [pow_two] using
      (Real.sq_sqrt (sub_nonneg.mpr hr1)))
  rw [hcr]
  simp_rw [hc1r]
  rw [← Finset.smul_sum, sum_resetKraus_evolve_eq]
  simp only [smul_smul]

theorem resetMixedKrausChannel_evolveMatrix_sub_eq
    {m : ℕ} [Nonempty (Fin m)]
    (U : QuantumMatrix m) (hU : U.conjTranspose * U = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (ρ σ : QuantumMatrix m) (htrace : Matrix.trace ρ = Matrix.trace σ) :
    (resetMixedKrausChannel U hU r hr0 hr1).evolveMatrix ρ -
        (resetMixedKrausChannel U hU r hr0 hr1).evolveMatrix σ =
      (r : ℂ) • (U * (ρ - σ) * U.conjTranspose) := by
  rw [resetMixedKrausChannel_evolveMatrix_eq,
    resetMixedKrausChannel_evolveMatrix_eq, htrace]
  rw [mul_sub, sub_mul]
  module

def unitaryKrausChannel
    {m : ℕ} (U : QuantumMatrix m) (hU : U.conjTranspose * U = 1) :
    FiniteKrausChannel m 1 where
  operator := fun _ => U
  completeness := by simpa using hU

theorem unitaryKrausChannel_evolveMatrix_eq
    {m : ℕ} (U : QuantumMatrix m) (hU : U.conjTranspose * U = 1)
    (ρ : QuantumMatrix m) :
    (unitaryKrausChannel U hU).evolveMatrix ρ = U * ρ * U.conjTranspose := by
  simp [unitaryKrausChannel, FiniteKrausChannel.evolveMatrix]

theorem quantumProbability_resetMixed_sub_eq
    {m : ℕ} [Nonempty (Fin m)]
    (U : QuantumMatrix m) (hU : U.conjTranspose * U = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (E : QuantumEffect m) (ρ σ : DensityMatrix m) :
    quantumProbability E ((resetMixedKrausChannel U hU r hr0 hr1).evolve ρ) -
        quantumProbability E ((resetMixedKrausChannel U hU r hr0 hr1).evolve σ) =
      r * (quantumProbability E ((unitaryKrausChannel U hU).evolve ρ) -
        quantumProbability E ((unitaryKrausChannel U hU).evolve σ)) := by
  have htrace : Matrix.trace ρ.1 = Matrix.trace σ.1 := by
    rw [ρ.property.2, σ.property.2]
  have hmat := resetMixedKrausChannel_evolveMatrix_sub_eq
    U hU hr0 hr1 ρ.1 σ.1 htrace
  have hcomplex :
      Matrix.trace (E.1 *
          (resetMixedKrausChannel U hU r hr0 hr1).evolveMatrix ρ.1) -
        Matrix.trace (E.1 *
          (resetMixedKrausChannel U hU r hr0 hr1).evolveMatrix σ.1) =
      (r : ℂ) *
        (Matrix.trace (E.1 * (unitaryKrausChannel U hU).evolveMatrix ρ.1) -
          Matrix.trace (E.1 * (unitaryKrausChannel U hU).evolveMatrix σ.1)) := by
    rw [← Matrix.trace_sub, ← Matrix.mul_sub, hmat,
      Matrix.mul_smul, Matrix.trace_smul,
      unitaryKrausChannel_evolveMatrix_eq,
      unitaryKrausChannel_evolveMatrix_eq,
      ← Matrix.trace_sub, ← Matrix.mul_sub]
    rw [mul_sub, sub_mul]
    simp
  have hre := congrArg Complex.re hcomplex
  simpa [quantumProbability, FiniteKrausChannel.evolve,
    Complex.mul_re] using hre

theorem resetMixedKrausChannel_distance_evolve_le
    {m : ℕ} [Nonempty (Fin m)]
    (U : QuantumMatrix m) (hU : U.conjTranspose * U = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (ρ σ : DensityMatrix m) :
    (finiteQuantumOperationalTheory m).distance
        ((resetMixedKrausChannel U hU r hr0 hr1).toOperationalChannel.evolve ρ)
        ((resetMixedKrausChannel U hU r hr0 hr1).toOperationalChannel.evolve σ) ≤
      ENNReal.ofReal r * (finiteQuantumOperationalTheory m).distance ρ σ := by
  apply iSup_le
  intro E
  change ENNReal.ofReal
      |quantumProbability E ((resetMixedKrausChannel U hU r hr0 hr1).evolve ρ) -
        quantumProbability E ((resetMixedKrausChannel U hU r hr0 hr1).evolve σ)| ≤ _
  rw [quantumProbability_resetMixed_sub_eq U hU hr0 hr1 E ρ σ]
  rw [abs_mul, abs_of_nonneg hr0, ENNReal.ofReal_mul hr0]
  let Ψ := unitaryKrausChannel U hU
  rw [Ψ.quantumProbability_after E ρ, Ψ.quantumProbability_after E σ]
  exact mul_le_mul_right
    (le_iSup
      (fun F : QuantumEffect m =>
        ENNReal.ofReal
          |quantumProbability F ρ - quantumProbability F σ|)
      (Ψ.pullback E)) _

theorem resetMixedKrausChannel_distanceAt_le_ofReal_pow
    {m : ℕ} [Nonempty (Fin m)]
    (U : QuantumMatrix m) (hU : U.conjTranspose * U = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (ρ σ : DensityMatrix m) (n : ℕ) :
    (resetMixedKrausChannel U hU r hr0 hr1).toOperationalChannel.distanceAt
        ρ σ n ≤ ENNReal.ofReal (r ^ n) := by
  induction n with
  | zero =>
      simpa [OperationalTheory.Channel.distanceAt] using
        (finiteQuantumOperationalTheory m).distance_le_one ρ σ
  | succ n ih =>
      simp only [OperationalTheory.Channel.distanceAt,
        Function.iterate_succ_apply']
      calc
        _ ≤ ENNReal.ofReal r *
            (finiteQuantumOperationalTheory m).distance
              ((resetMixedKrausChannel U hU r hr0 hr1).evolve^[n] ρ)
              ((resetMixedKrausChannel U hU r hr0 hr1).evolve^[n] σ) :=
          resetMixedKrausChannel_distance_evolve_le U hU hr0 hr1 _ _
        _ ≤ ENNReal.ofReal r * ENNReal.ofReal (r ^ n) :=
          mul_le_mul_right ih _
        _ = ENNReal.ofReal (r ^ (n + 1)) := by
          rw [← ENNReal.ofReal_mul hr0]
          congr 1
          ring

theorem resetMixedKrausChannel_operationally_forgets
    {m : ℕ} [Nonempty (Fin m)]
    (U : QuantumMatrix m) (hU : U.conjTranspose * U = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ρ σ : DensityMatrix m) :
    Tendsto
      ((resetMixedKrausChannel U hU r hr0 hr1.le).toOperationalChannel.distanceAt
        ρ σ) atTop (𝓝 0) := by
  have hupper : Tendsto (fun n => ENNReal.ofReal (r ^ n)) atTop (𝓝 0) :=
    by
      simpa using
        (ENNReal.tendsto_ofReal
          (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
    (Filter.Eventually.of_forall fun _ => bot_le)
    (Filter.Eventually.of_forall fun n =>
      resetMixedKrausChannel_distanceAt_le_ofReal_pow
        U hU hr0 hr1.le ρ σ n)

def resetDensityMatrix {m : ℕ} [Nonempty (Fin m)] : DensityMatrix m where
  val := resetStateMatrix (Classical.choice ‹Nonempty (Fin m)›)
  property := by
    constructor
    · rw [resetStateMatrix, ← Matrix.diagonal_single]
      exact Matrix.PosSemidef.diagonal (fun i => by
        by_cases hi : i = Classical.choice ‹Nonempty (Fin m)› <;>
          simp [hi])
    · simp [resetStateMatrix, Matrix.trace]

theorem resetMixedKrausChannel_evolveMatrix_eq_convex
    {m : ℕ} [Nonempty (Fin m)]
    (U : QuantumMatrix m) (hU : U.conjTranspose * U = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ρ : DensityMatrix m) :
    (resetMixedKrausChannel U hU r hr0 hr1).evolveMatrix ρ.1 =
      (r : ℂ) • (unitaryKrausChannel U hU).evolveMatrix ρ.1 +
        ((1 - r : ℝ) : ℂ) • (resetDensityMatrix : DensityMatrix m).1 := by
  rw [resetMixedKrausChannel_evolveMatrix_eq,
    unitaryKrausChannel_evolveMatrix_eq, ρ.property.2]
  simp [resetDensityMatrix]

theorem quantumProbability_resetMixed_eq_convex
    {m : ℕ} [Nonempty (Fin m)]
    (U : QuantumMatrix m) (hU : U.conjTranspose * U = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (E : QuantumEffect m) (ρ : DensityMatrix m) :
    quantumProbability E ((resetMixedKrausChannel U hU r hr0 hr1).evolve ρ) =
      r * quantumProbability E ((unitaryKrausChannel U hU).evolve ρ) +
        (1 - r) * quantumProbability E (resetDensityMatrix : DensityMatrix m) := by
  unfold quantumProbability
  dsimp only [FiniteKrausChannel.evolve]
  rw [resetMixedKrausChannel_evolveMatrix_eq_convex]
  simp [Matrix.mul_add, Matrix.trace_add,
    Matrix.trace_smul, Complex.add_re, Complex.mul_re]

theorem resetMixedKrausChannel_oneStep_distance_unitary_le
    {m : ℕ} [Nonempty (Fin m)]
    (U : QuantumMatrix m) (hU : U.conjTranspose * U = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (ρ : DensityMatrix m) :
    (finiteQuantumOperationalTheory m).distance
        ((resetMixedKrausChannel U hU r hr0 hr1).evolve ρ)
        ((unitaryKrausChannel U hU).evolve ρ) ≤
      ENNReal.ofReal (1 - r) := by
  apply iSup_le
  intro E
  change ENNReal.ofReal
      |quantumProbability E ((resetMixedKrausChannel U hU r hr0 hr1).evolve ρ) -
        quantumProbability E ((unitaryKrausChannel U hU).evolve ρ)| ≤ _
  rw [quantumProbability_resetMixed_eq_convex]
  let pU := quantumProbability E ((unitaryKrausChannel U hU).evolve ρ)
  let pR := quantumProbability E (resetDensityMatrix : DensityMatrix m)
  have hpU0 : 0 ≤ pU := quantumProbability_nonneg _ _
  have hpU1 : pU ≤ 1 := quantumProbability_le_one _ _
  have hpR0 : 0 ≤ pR := quantumProbability_nonneg _ _
  have hpR1 : pR ≤ 1 := quantumProbability_le_one _ _
  have hgap : |r * pU + (1 - r) * pR - pU| ≤ 1 - r := by
    rw [show r * pU + (1 - r) * pR - pU =
      (1 - r) * (pR - pU) by ring, abs_mul,
      abs_of_nonneg (sub_nonneg.mpr hr1)]
    have habs : |pR - pU| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    nlinarith
  exact ENNReal.ofReal_le_ofReal hgap

theorem OperationalTheory.distance_triangle
    (Q : OperationalTheory) (ρ σ τ : Q.State) :
    Q.distance ρ τ ≤ Q.distance ρ σ + Q.distance σ τ := by
  apply iSup_le
  intro E
  let a := Q.probability E ρ
  let b := Q.probability E σ
  let c := Q.probability E τ
  have habs : |a - c| ≤ |a - b| + |b - c| := by
    calc
      |a - c| = |(a - b) + (b - c)| := by congr 1; ring
      _ ≤ |a - b| + |b - c| := abs_add_le _ _
  calc
    ENNReal.ofReal |a - c| ≤
        ENNReal.ofReal (|a - b| + |b - c|) :=
      ENNReal.ofReal_le_ofReal habs
    _ ≤ ENNReal.ofReal |a - b| + ENNReal.ofReal |b - c| :=
      ENNReal.ofReal_add_le
    _ ≤ Q.distance ρ σ + Q.distance σ τ :=
      add_le_add
        (le_iSup
          (fun F : Q.Effect =>
            ENNReal.ofReal |Q.probability F ρ - Q.probability F σ|) E)
        (le_iSup
          (fun F : Q.Effect =>
            ENNReal.ofReal |Q.probability F σ - Q.probability F τ|) E)

theorem resetMixedKrausChannel_iterate_distance_unitary_le
    {m : ℕ} [Nonempty (Fin m)]
    (U : QuantumMatrix m) (hU : U.conjTranspose * U = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (ρ : DensityMatrix m) (n : ℕ) :
    (finiteQuantumOperationalTheory m).distance
        ((resetMixedKrausChannel U hU r hr0 hr1).evolve^[n] ρ)
        ((unitaryKrausChannel U hU).evolve^[n] ρ) ≤
      ENNReal.ofReal ((n : ℝ) * (1 - r)) := by
  induction n with
  | zero => simp [OperationalTheory.distance]
  | succ n ih =>
      simp only [Function.iterate_succ_apply']
      let Φ := resetMixedKrausChannel U hU r hr0 hr1
      let Ψ := unitaryKrausChannel U hU
      calc
        (finiteQuantumOperationalTheory m).distance
            (Φ.evolve (Φ.evolve^[n] ρ))
            (Ψ.evolve (Ψ.evolve^[n] ρ)) ≤
          (finiteQuantumOperationalTheory m).distance
              (Φ.evolve (Φ.evolve^[n] ρ))
              (Φ.evolve (Ψ.evolve^[n] ρ)) +
            (finiteQuantumOperationalTheory m).distance
              (Φ.evolve (Ψ.evolve^[n] ρ))
              (Ψ.evolve (Ψ.evolve^[n] ρ)) :=
          OperationalTheory.distance_triangle _ _ _ _
        _ ≤ (finiteQuantumOperationalTheory m).distance
              (Φ.evolve^[n] ρ) (Ψ.evolve^[n] ρ) +
            ENNReal.ofReal (1 - r) :=
          add_le_add
            (Φ.toOperationalChannel.distance_evolve_le _ _)
            (resetMixedKrausChannel_oneStep_distance_unitary_le
              U hU hr0 hr1 (Ψ.evolve^[n] ρ))
        _ ≤ ENNReal.ofReal ((n : ℝ) * (1 - r)) +
            ENNReal.ofReal (1 - r) := add_le_add ih le_rfl
        _ = ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * (1 - r)) := by
          rw [← ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _)
            (sub_nonneg.mpr hr1)) (sub_nonneg.mpr hr1)]
          congr 1
          push_cast
          ring

/-- For every finite unitary channel and finite operational horizon, a
genuine reset-noise Kraus channel is uniformly indistinguishable below any
positive tolerance while forgetting every pair of initial states. -/
theorem exists_CPTP_finiteHorizon_close_unitary_and_forgetting
    {m : ℕ} [Nonempty (Fin m)]
    (U : QuantumMatrix m) (hU : U.conjTranspose * U = 1)
    (N : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1), 0 < r ∧ r < 1 ∧
      (∀ ρ : DensityMatrix m, ∀ n ≤ N,
        (finiteQuantumOperationalTheory m).distance
            ((resetMixedKrausChannel U hU r hr0 hr1).evolve^[n] ρ)
            ((unitaryKrausChannel U hU).evolve^[n] ρ) <
          ENNReal.ofReal η) ∧
      ∀ ρ σ : DensityMatrix m,
        Tendsto
          ((resetMixedKrausChannel U hU r hr0 hr1).toOperationalChannel.distanceAt
            ρ σ)
          atTop (𝓝 0) := by
  let δ : ℝ := min (1 / 2 : ℝ) (η / (2 * ((N : ℝ) + 1)))
  let r : ℝ := 1 - δ
  have hN1 : 0 < (N : ℝ) + 1 := by positivity
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min (by norm_num) (div_pos hη (mul_pos (by norm_num) hN1))
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδeta : δ ≤ η / (2 * ((N : ℝ) + 1)) := min_le_right _ _
  have hrpos : 0 < r := by dsimp [r]; linarith
  have hrlt : r < 1 := by dsimp [r]; linarith
  refine ⟨r, hrpos.le, hrlt.le, hrpos, hrlt, ?_, ?_⟩
  · intro ρ n hn
    have hbound := resetMixedKrausChannel_iterate_distance_unitary_le
      U hU hrpos.le hrlt.le ρ n
    have hncast : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
    have hreal : (n : ℝ) * (1 - r) < η := by
      have hgap : 1 - r = δ := by simp [r]
      rw [hgap]
      calc
        (n : ℝ) * δ ≤ (N : ℝ) * δ := by gcongr
        _ ≤ (N : ℝ) * (η / (2 * ((N : ℝ) + 1))) := by gcongr
        _ < η := by
          rw [div_eq_mul_inv]
          have hden : 0 < 2 * ((N : ℝ) + 1) := by positivity
          have hratio : (N : ℝ) * (2 * ((N : ℝ) + 1))⁻¹ < 1 := by
            rw [← div_eq_mul_inv, div_lt_one hden]
            nlinarith
          calc
            (N : ℝ) * (η * (2 * ((N : ℝ) + 1))⁻¹) =
                η * ((N : ℝ) * (2 * ((N : ℝ) + 1))⁻¹) := by ring
            _ < η * 1 := mul_lt_mul_of_pos_left hratio hη
            _ = η := mul_one η
    exact hbound.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hη).2 hreal)
  · intro ρ σ
    exact resetMixedKrausChannel_operationally_forgets
      U hU hrpos.le hrlt ρ σ

end RHTower

