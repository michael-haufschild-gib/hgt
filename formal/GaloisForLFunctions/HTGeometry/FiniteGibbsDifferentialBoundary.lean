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

open GaloisForLFunctions

/-- A response has genuinely infinite constant-coefficient spectral complexity when no nonzero
polynomial in the differentiation operator annihilates it.  This condition is weaker than
hypertranscendence and therefore describes a larger ambient class. -/
def ConstantCoefficientDifferentiallyTranscendental (f : ℂ → ℂ) : Prop :=
  ∀ L : Polynomial ℂ,
    constantCoeffDifferentialOperator L f = 0 → L = 0

/-- Polynomial application is the finite linear combination of the derivative-observable family
with the polynomial coefficient packet. -/
theorem constantCoeffDifferentialOperator_eq_linearCombination
    (L : Polynomial ℂ) (f : ℂ → ℂ) :
    constantCoeffDifferentialOperator L f =
      Finsupp.linearCombination ℂ (fun j : ℕ => iteratedDeriv j f)
        L.toFinsupp.coeff := by
  funext z
  rw [constantCoeffDifferentialOperator, Finsupp.linearCombination_apply,
    Finsupp.sum_apply']
  change (∑ j ∈ L.support, L.coeff j * iteratedDeriv j f z) =
    ∑ j ∈ L.toFinsupp.coeff.support,
      (L.toFinsupp.coeff j • iteratedDeriv j f) z
  rw [Polynomial.support_toFinsupp]
  apply Finset.sum_congr rfl
  intro j _
  simp [Polynomial.toFinsupp_apply]

/-- **Observable-clock characterization.**  Infinite constant-coefficient spectral complexity is
exactly linear independence of the complete derivative-observable family. -/
theorem constantCoefficientDifferentiallyTranscendental_iff_linearIndependent_iteratedDeriv
    (f : ℂ → ℂ) :
    ConstantCoefficientDifferentiallyTranscendental f ↔
      LinearIndependent ℂ (fun j : ℕ => iteratedDeriv j f) := by
  rw [linearIndependent_iff]
  constructor
  · intro hf l hl
    have hpoly :
        (⟨AddMonoidAlgebra.ofCoeff l⟩ : Polynomial ℂ) = 0 := by
      apply hf
      rw [constantCoeffDifferentialOperator_eq_linearCombination]
      simpa using hl
    have hcoeff :=
      congrArg (fun P : Polynomial ℂ => P.toFinsupp.coeff) hpoly
    simpa using hcoeff
  · intro hlin L hzero
    have hcoeff : L.toFinsupp.coeff = 0 := by
      apply hlin
      rw [← constantCoeffDifferentialOperator_eq_linearCombination]
      exact hzero
    apply Polynomial.toFinsupp_eq_zero.mp
    apply AddMonoidAlgebra.coeff_injective
    simpa using hcoeff

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

/-- A response with infinite constant-coefficient spectral complexity cannot be any finite
exponential spectrum.  This is the abstract finite-dimensional Hamiltonian-response no-go: after
spectral decomposition, every finite matrix coefficient has this exponential-sum shape. -/
theorem ne_finset_expSum_of_constantCoefficientDifferentiallyTranscendental
    {f : ℂ → ℂ} (hf : ConstantCoefficientDifferentiallyTranscendental f)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a c : ι → ℂ) :
    f ≠ fun z => ∑ i ∈ s, a i * Complex.exp (c i * z) := by
  intro heq
  let L : Polynomial ℂ :=
    ∏ i ∈ s, (Polynomial.X - Polynomial.C (c i))
  have hLmonic : L.Monic := by
    exact Polynomial.monic_prod_of_monic _ _
      (fun i _ => Polynomial.monic_X_sub_C (c i))
  have hroot : ∀ i ∈ s, L.eval (c i) = 0 := by
    intro i hi
    dsimp only [L]
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero hi (by simp)
  apply hLmonic.ne_zero
  apply hf L
  funext z
  rw [heq, constantCoeffDifferentialOperator_finset_expSum]
  exact Finset.sum_eq_zero fun i hi => by simp [hroot i hi]

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
    have hlead : L.coeff L.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hL
    have hev := congrArg (MvPolynomial.eval
      (fun v : Fin (L.natDegree + 2) =>
        if v = (Fin.last L.natDegree).succ then (1 : ℂ) else 0)) hP0
    rw [map_sum, map_zero] at hev
    rw [Finset.sum_eq_single (Fin.last L.natDegree)] at hev
    · apply hlead
      simpa only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
        Fin.val_last, if_pos, mul_one] using hev
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

/-- Hypertranscendence therefore excludes every finite exponential time-response, not merely finite
Gibbs partition functions. -/
theorem ne_finset_expSum_of_hypertranscendental
    {f : ℂ → ℂ} (hf : Hypertranscendental f)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a c : ι → ℂ) :
    f ≠ fun z => ∑ i ∈ s, a i * Complex.exp (c i * z) :=
  ne_finset_expSum_of_constantCoefficientDifferentiallyTranscendental
    (hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental hf) s a c

/-- A single meromorphic simple pole already excludes every finite constant-coefficient spectral
law.  The highest derivative creates a pole order that lower derivatives cannot cancel. -/
theorem constantCoefficientDifferentiallyTranscendental_of_meromorphic_simplePole
    {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p)
    (horder : meromorphicOrderAt f p = ((-1 : ℤ) : WithTop ℤ)) :
    ConstantCoefficientDifferentiallyTranscendental f := by
  intro L hzero
  by_contra hL
  have hoperator :=
    meromorphicOrderAt_constantCoeffDifferentialOperator_of_simplePole hL hf horder
  have hzeroOrder :
      meromorphicOrderAt (constantCoeffDifferentialOperator L f) p = ⊤ := by
    rw [hzero]
    simp
  rw [hzeroOrder] at hoperator
  have hfinite :
      (((-((L.natDegree + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ)) ≠ ⊤ :=
    WithTop.coe_ne_top
  exact hfinite hoperator.symm

/-- The total reciprocal function is differentially algebraic.  The factor `z` makes the ordinary
algebraic relation `z * z⁻¹ = 1` valid as a polynomial identity even at Lean's totalized value
`0⁻¹ = 0`. -/
theorem differentiallyAlgebraic_inv_id :
    DifferentiallyAlgebraic (fun z : ℂ => z⁻¹) := by
  let P : MvPolynomial (Fin 2) ℂ :=
    MvPolynomial.X 0 * (MvPolynomial.X 0 * MvPolynomial.X 1 - 1)
  refine ⟨0, P, ?_, ?_⟩
  · intro hP
    have hev := congrArg
      (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0)) hP
    norm_num [P] at hev
  · intro z
    simp only [P, map_mul, MvPolynomial.eval_X, map_sub, map_one, Fin.cons_zero]
    change z * (z * z⁻¹ - 1) = 0
    by_cases hz : z = 0
    · simp [hz]
    · simp [hz]

/-- The reciprocal has infinite constant-coefficient spectral complexity because of its simple
pole, despite being differentially algebraic. -/
theorem constantCoefficientDifferentiallyTranscendental_inv_id :
    ConstantCoefficientDifferentiallyTranscendental (fun z : ℂ => z⁻¹) := by
  apply constantCoefficientDifferentiallyTranscendental_of_meromorphic_simplePole (p := 0)
  · fun_prop
  · change meromorphicOrderAt (id : ℂ → ℂ)⁻¹ 0 = ((-1 : ℤ) : WithTop ℤ)
    rw [meromorphicOrderAt_inv, meromorphicOrderAt_id]
    rfl

/-- The constant-coefficient spectral boundary is strictly broader than hypertranscendence. -/
theorem exists_constantCoefficientDifferentiallyTranscendental_not_hypertranscendental :
    ∃ f : ℂ → ℂ,
      ConstantCoefficientDifferentiallyTranscendental f ∧ ¬ Hypertranscendental f := by
  refine ⟨fun z : ℂ => z⁻¹,
    constantCoefficientDifferentiallyTranscendental_inv_id, ?_⟩
  intro hht
  exact hht differentiallyAlgebraic_inv_id

/-! ### Static Fisher/energy-gap value relations -/

/-- For any normalized finite weight, the mean squared pairwise value gap is twice the variance.
No positivity is needed for the algebraic identity. -/
theorem normalizedWeight_pairwiseSqGap_eq_two_mul_variance
    {α : Type*} [Fintype α] (weight value : α → ℝ)
    (hweight : ∑ a, weight a = 1) :
    (∑ a, ∑ b, weight a * weight b * (value a - value b) ^ 2) =
      2 * ((∑ a, weight a * value a ^ 2) -
        (∑ a, weight a * value a) ^ 2) := by
  have hfirst :
      (∑ a, ∑ b, weight a * weight b * value a ^ 2) =
        (∑ a, weight a * value a ^ 2) * (∑ b, weight b) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hcross :
      (∑ a, ∑ b, weight a * weight b * value a * value b) =
        (∑ a, weight a * value a) * (∑ b, weight b * value b) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hlast :
      (∑ a, ∑ b, weight a * weight b * value b ^ 2) =
        (∑ a, weight a) * (∑ b, weight b * value b ^ 2) := by
    calc
      (∑ a, ∑ b, weight a * weight b * value b ^ 2) =
          ∑ b, ∑ a, weight b * weight a * value b ^ 2 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = (∑ b, weight b * value b ^ 2) * (∑ a, weight a) := hfirst
      _ = (∑ a, weight a) * (∑ b, weight b * value b ^ 2) := by ring
  calc
    (∑ a, ∑ b, weight a * weight b * (value a - value b) ^ 2) =
        (∑ a, ∑ b, weight a * weight b * value a ^ 2) -
          2 * (∑ a, ∑ b, weight a * weight b * value a * value b) +
        (∑ a, ∑ b, weight a * weight b * value b ^ 2) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = (∑ a, weight a * value a ^ 2) * (∑ b, weight b) -
          2 * ((∑ a, weight a * value a) * (∑ b, weight b * value b)) +
        (∑ a, weight a) * (∑ b, weight b * value b ^ 2) := by
      rw [hfirst, hcross, hlast]
    _ = 2 * ((∑ a, weight a * value a ^ 2) -
        (∑ a, weight a * value a) ^ 2) := by
      rw [hweight]
      ring

/-- Complexified canonical partition function of a finite Hamiltonian spectrum. -/
def finiteComplexGibbsPartition {α : Type*} [Fintype α]
    (energy : α → ℝ) (z : ℂ) : ℂ :=
  ∑ a, Complex.exp (-(energy a : ℂ) * z)

/-- Mean energy of the finite canonical Gibbs state. -/
def finiteGibbsEnergyMean {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) : ℝ :=
  ∑ a, finiteGibbsStateWeight β energy a * energy a

/-- Static Fisher information for inverse temperature, written as Gibbs energy variance. -/
def finiteGibbsEnergyVariance {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) : ℝ :=
  ∑ a, finiteGibbsStateWeight β energy a * energy a ^ 2 -
    finiteGibbsEnergyMean β energy ^ 2

/-- Product Gibbs intensity on ordered energy-level pairs. -/
def finiteGibbsProductGapIntensity {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (a b : α) : ℝ :=
  finiteGibbsStateWeight β energy a * finiteGibbsStateWeight β energy b

/-- The thermal Fisher information is half the second Liouvillian gap moment of two independent
Gibbs energy observations.  This turns the one-copy energy variance into an exact two-copy
observable-gap value. -/
theorem thermalGapMoment_finiteGibbsProduct_two_eq_two_mul_energyVariance
    {α : Type*} [Fintype α] [Nonempty α] (β : ℝ) (energy : α → ℝ) :
    thermalGapMoment (finiteGibbsProductGapIntensity β energy) energy 2 =
      2 * finiteGibbsEnergyVariance β energy := by
  simpa [thermalGapMoment, finiteGibbsProductGapIntensity,
    finiteGibbsEnergyVariance, finiteGibbsEnergyMean] using
    (normalizedWeight_pairwiseSqGap_eq_two_mul_variance
      (finiteGibbsStateWeight β energy) energy
      (sum_finiteGibbsStateWeight_eq_one β energy))

/-- Every partition-function derivative is the corresponding signed energy moment. -/
theorem iteratedDeriv_finiteComplexGibbsPartition
    {α : Type*} [Fintype α] (energy : α → ℝ) (j : ℕ) (z : ℂ) :
    iteratedDeriv j (finiteComplexGibbsPartition energy) z =
      ∑ a, (-(energy a : ℂ)) ^ j *
        Complex.exp (-(energy a : ℂ) * z) := by
  classical
  change iteratedDeriv j
      (fun x : ℂ => ∑ a, Complex.exp (-(energy a : ℂ) * x)) z = _
  simpa only [one_mul] using
    (iteratedDeriv_finset_expSum (Finset.univ : Finset α)
      (fun _ => (1 : ℂ)) (fun a => -(energy a : ℂ)) j z)

/-- Finite spectral partition functions are differentially algebraic. -/
theorem differentiallyAlgebraic_finiteComplexGibbsPartition
    {α : Type*} [Fintype α] (energy : α → ℝ) :
    DifferentiallyAlgebraic (finiteComplexGibbsPartition energy) := by
  classical
  change DifferentiallyAlgebraic
    (fun x : ℂ => ∑ a, Complex.exp (-(energy a : ℂ) * x))
  simpa only [one_mul] using
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
  change constantCoeffDifferentialOperator
      (finiteComplexGibbsAnnihilator energy)
      (fun x => ∑ a, Complex.exp (-(energy a : ℂ) * x)) z = 0
  simpa only [one_mul, finiteComplexGibbsAnnihilator_eval_neg_energy,
    zero_mul, Finset.sum_const_zero] using
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

/-- A single simple pole discharges the hypertranscendence hypothesis in the finite-Hamiltonian
no-go.  This is the direct interface for the many meromorphic clock/source functions already in the
corpus. -/
theorem ne_finiteComplexGibbsPartition_of_meromorphic_simplePole
    {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p)
    (horder : meromorphicOrderAt f p = ((-1 : ℤ) : WithTop ℤ))
    {α : Type*} [Fintype α] (energy : α → ℝ) :
    f ≠ finiteComplexGibbsPartition energy :=
  ne_finiteComplexGibbsPartition_of_constantCoefficientDifferentiallyTranscendental
    (constantCoefficientDifferentiallyTranscendental_of_meromorphic_simplePole hf horder) energy

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
