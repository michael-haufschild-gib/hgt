import GaloisForLFunctions.HTGeometry.ExponentialSumDA
import GaloisForLFunctions.HTGeometry.FiniteKMSWightman
import GaloisForLFunctions.HTGeometry.MeromorphicSimplePoleDifferentialOperator

/-!
# Differential boundary of finite Gibbs realizations

A finite-level Hamiltonian has a complexified partition function

`Z(z) = sum_a exp(-z E_a)`.

Its complete derivative tower is the energy-moment tower, and the finite spectrum supplies the
nonzero constant-coefficient annihilator `prod_a (D + E_a)`.  Consequently every finite Gibbs
partition function is differentially algebraic.  A hypertranscendental function therefore cannot
be the partition function of any finite-level Hamiltonian.

The constant-coefficient conclusion is strictly the relevant realization boundary: it defines a
larger ambient class than hypertranscendence.  A function with no nonzero constant-coefficient
differential annihilator already has no finite spectral realization, even if it might satisfy a
nonlinear or variable-coefficient differential equation.

Physics provenance: finite Gibbs states use `Z(beta) = Tr exp(-beta H)`, while thermal Fisher
information and heat capacity are the variance of the energy score.  Complexifying `beta` gives
the Fisher-zero partition function.  The results here isolate the finite-spectrum differential
content of those standard value relations; they do not interpret the differential variable as an
external time.
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- A response has genuinely infinite constant-coefficient spectral complexity when no nonzero
polynomial in the differentiation operator annihilates it.  This condition is weaker than
hypertranscendence and therefore describes a larger ambient class. -/
def ConstantCoefficientDifferentiallyTranscendental (f : ℂ → ℂ) : Prop :=
  ∀ L : Polynomial ℂ,
    constantCoeffDifferentialOperator L f = 0 → L = 0

/-- Applying a constant-coefficient differential operator to a finite exponential spectrum
multiplies each spectral line by the operator symbol evaluated at its frequency. -/
theorem constantCoeffDifferentialOperator_finset_expSum
    {ι : Type*} [DecidableEq ι] (L : Polynomial ℂ) (s : Finset ι)
    (a c : ι → ℂ) (z : ℂ) :
    constantCoeffDifferentialOperator L
        (fun x => ∑ i ∈ s, a i * Complex.exp (c i * x)) z =
      ∑ i ∈ s, a i * L.eval (c i) * Complex.exp (c i * z) := by
  rw [constantCoeffDifferentialOperator]
  simp only [Polynomial.sum_def, iteratedDeriv_finset_expSum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- A vanishing nonzero constant-coefficient differential operator is already an algebraic
differential equation. -/
theorem differentiallyAlgebraic_of_constantCoeffDifferentialOperator_eq_zero
    {f : ℂ → ℂ} {L : Polynomial ℂ} (hL : L ≠ 0)
    (hzero : constantCoeffDifferentialOperator L f = 0) :
    DifferentiallyAlgebraic f := by
  let P : MvPolynomial (Fin (L.natDegree + 2)) ℂ :=
    ∑ j : Fin (L.natDegree + 1),
      MvPolynomial.C (L.coeff j) * MvPolynomial.X j.succ
  refine ⟨L.natDegree, P, ?_, ?_⟩
  · intro hP0
    have hlead : L.coeff L.natDegree ≠ 0 := Polynomial.coeff_natDegree hL
    have hev := congrArg (MvPolynomial.eval
      (fun v : Fin (L.natDegree + 2) =>
        if v = (Fin.last L.natDegree).succ then (1 : ℂ) else 0)) hP0
    rw [map_sum, map_zero] at hev
    rw [Finset.sum_eq_single (Fin.last L.natDegree)] at hev
    · apply hlead
      simpa only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
        if_pos, mul_one] using hev
    · intro b hb hblast
      simp [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, hblast]
    · intro h
      exact absurd (Finset.mem_univ (Fin.last L.natDegree)) h
  · intro z
    have hz := congrFun hzero z
    change L.sum (fun j coeff => coeff * iteratedDeriv j f z) = 0 at hz
    simp only [P, map_sum, map_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X, Fin.cons_succ]
    have hdegree : L.degree < (L.natDegree + 1 : ℕ) := by
      rw [Polynomial.degree_eq_natDegree hL, Nat.cast_lt]
      exact Nat.lt_succ_self _
    rw [Polynomial.sum_fin
      (fun j coeff => coeff * iteratedDeriv j f z) (by simp) hdegree]
    exact hz

/-- Hypertranscendence implies the weaker absence of a constant-coefficient spectral
annihilator. -/
theorem hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental
    {f : ℂ → ℂ} (hf : Hypertranscendental f) :
    ConstantCoefficientDifferentiallyTranscendental f := by
  intro L hzero
  by_contra hL
  exact hf
    (differentiallyAlgebraic_of_constantCoeffDifferentialOperator_eq_zero hL hzero)

/-- Complexified canonical partition function of a finite Hamiltonian spectrum. -/
def finiteComplexGibbsPartition {α : Type*} [Fintype α]
    (energy : α → ℝ) (z : ℂ) : ℂ :=
  ∑ a, Complex.exp (-(energy a : ℂ) * z)

/-- Every partition-function derivative is the corresponding signed energy moment. -/
theorem iteratedDeriv_finiteComplexGibbsPartition
    {α : Type*} [Fintype α] (energy : α → ℝ) (j : ℕ) (z : ℂ) :
    iteratedDeriv j (finiteComplexGibbsPartition energy) z =
      ∑ a, (-(energy a : ℂ)) ^ j *
        Complex.exp (-(energy a : ℂ) * z) := by
  classical
  simpa [finiteComplexGibbsPartition] using
    (iteratedDeriv_finset_expSum (Finset.univ : Finset α)
      (fun _ => (1 : ℂ)) (fun a => -(energy a : ℂ)) j z)

/-- Finite spectral partition functions are differentially algebraic. -/
theorem differentiallyAlgebraic_finiteComplexGibbsPartition
    {α : Type*} [Fintype α] (energy : α → ℝ) :
    DifferentiallyAlgebraic (finiteComplexGibbsPartition energy) := by
  classical
  simpa [finiteComplexGibbsPartition] using
    (differentiallyAlgebraic_finset_expSum_general
      (Finset.univ : Finset α) (fun _ => (1 : ℂ))
      (fun a => -(energy a : ℂ)))

/-- Characteristic differential polynomial of a finite Hamiltonian spectrum. -/
def finiteComplexGibbsAnnihilator {α : Type*} [Fintype α]
    (energy : α → ℝ) : Polynomial ℂ :=
  ∏ a, (Polynomial.X - Polynomial.C (-(energy a : ℂ)))

theorem finiteComplexGibbsAnnihilator_monic
    {α : Type*} [Fintype α] (energy : α → ℝ) :
    (finiteComplexGibbsAnnihilator energy).Monic := by
  classical
  exact Polynomial.monic_prod_of_monic _ _
    (fun a _ => Polynomial.monic_X_sub_C (-(energy a : ℂ)))

theorem finiteComplexGibbsAnnihilator_ne_zero
    {α : Type*} [Fintype α] (energy : α → ℝ) :
    finiteComplexGibbsAnnihilator energy ≠ 0 :=
  (finiteComplexGibbsAnnihilator_monic energy).ne_zero

@[simp]
theorem finiteComplexGibbsAnnihilator_eval_neg_energy
    {α : Type*} [Fintype α] (energy : α → ℝ) (a : α) :
    (finiteComplexGibbsAnnihilator energy).eval (-(energy a : ℂ)) = 0 := by
  classical
  rw [finiteComplexGibbsAnnihilator, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp)

/-- **Finite-spectrum annihilator law.**  The complex Gibbs partition function is killed by the
product of the first-order spectral factors `D + E_a`. -/
theorem constantCoeffDifferentialOperator_finiteComplexGibbsAnnihilator_eq_zero
    {α : Type*} [Fintype α] (energy : α → ℝ) :
    constantCoeffDifferentialOperator
      (finiteComplexGibbsAnnihilator energy)
      (finiteComplexGibbsPartition energy) = 0 := by
  classical
  funext z
  simpa [finiteComplexGibbsPartition] using
    (constantCoeffDifferentialOperator_finset_expSum
      (finiteComplexGibbsAnnihilator energy) (Finset.univ : Finset α)
      (fun _ => (1 : ℂ)) (fun a => -(energy a : ℂ)) z)

/-- A finite Gibbs partition function never has genuinely infinite constant-coefficient spectral
complexity. -/
theorem not_constantCoefficientDifferentiallyTranscendental_finiteComplexGibbsPartition
    {α : Type*} [Fintype α] (energy : α → ℝ) :
    ¬ ConstantCoefficientDifferentiallyTranscendental
      (finiteComplexGibbsPartition energy) := by
  intro h
  exact finiteComplexGibbsAnnihilator_ne_zero energy
    (h (finiteComplexGibbsAnnihilator energy)
      (constantCoeffDifferentialOperator_finiteComplexGibbsAnnihilator_eq_zero energy))

/-- Every response with infinite constant-coefficient spectral complexity is excluded from every
finite Hamiltonian partition-function realization. -/
theorem ne_finiteComplexGibbsPartition_of_constantCoefficientDifferentiallyTranscendental
    {f : ℂ → ℂ} (hf : ConstantCoefficientDifferentiallyTranscendental f)
    {α : Type*} [Fintype α] (energy : α → ℝ) :
    f ≠ finiteComplexGibbsPartition energy := by
  intro heq
  have hzero : constantCoeffDifferentialOperator
      (finiteComplexGibbsAnnihilator energy) f = 0 := by
    rw [heq]
    exact constantCoeffDifferentialOperator_finiteComplexGibbsAnnihilator_eq_zero energy
  exact finiteComplexGibbsAnnihilator_ne_zero energy
    (hf (finiteComplexGibbsAnnihilator energy) hzero)

/-- **Hypertranscendental finite-Hamiltonian no-go.**  No hypertranscendental function is the
complexified partition function of a finite-level Hamiltonian. -/
theorem ne_finiteComplexGibbsPartition_of_hypertranscendental
    {f : ℂ → ℂ} (hf : Hypertranscendental f)
    {α : Type*} [Fintype α] (energy : α → ℝ) :
    f ≠ finiteComplexGibbsPartition energy :=
  ne_finiteComplexGibbsPartition_of_constantCoefficientDifferentiallyTranscendental
    (hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental hf) energy

end

end HTGeometry
