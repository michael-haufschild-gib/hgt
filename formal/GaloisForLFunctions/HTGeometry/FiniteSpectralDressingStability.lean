import GaloisForLFunctions.HTGeometry.FiniteGibbsDifferentialBoundary
import GaloisForLFunctions.HTGeometry.TaylorFormalBridge

/-!
# Stability of infinite spectral complexity under finite dressing

A response with no nonzero constant-coefficient differential annihilator remains in that class
after adding any finite exponential spectrum.  The positive mechanism is annihilator
multiplication: a hypothetical annihilator of the dressed response, composed with the finite
spectrum's characteristic annihilator, would annihilate the original response.

The meromorphic version is stronger for the source corpus.  A finite exponential response is
entire, so it cannot cancel a simple pole; the pole itself continues to certify infinite
constant-coefficient spectral complexity after arbitrary finite Gibbs dressing.

This is a static observer/clock statement.  The variable indexes derivative readings and the
finite spectrum supplies a finite recurrence; no temporal evolution is assumed.

Physics provenance: for a finite-dimensional Hamiltonian, the complex-temperature partition
function is a finite sum of spectral exponentials.  Complex-temperature quantum partition
functions and Fisher zeros are treated, for example, in A. Jackson, T. Kapourniotis, and
A. Datta, arXiv:2208.00930.  The formal result below isolates the exact differential value relation
and proves that coupling to such a finite sector cannot erase an infinite spectral clock.
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

open GaloisForLFunctions

/-- A constant-coefficient differential operator is additive on globally smooth responses. -/
theorem constantCoeffDifferentialOperator_add_smooth
    (L : Polynomial ℂ) {f g : ℂ → ℂ}
    (hf : ContDiff ℂ (⊤ : ℕ∞) f) (hg : ContDiff ℂ (⊤ : ℕ∞) g) :
    constantCoeffDifferentialOperator L (f + g) =
      constantCoeffDifferentialOperator L f +
        constantCoeffDifferentialOperator L g := by
  funext z
  unfold constantCoeffDifferentialOperator
  simp only [Polynomial.sum_def, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [iteratedDeriv_add
    (hf.contDiffAt.of_le (by exact_mod_cast le_top))
    (hg.contDiffAt.of_le (by exact_mod_cast le_top))]
  ring

/-- Constant-coefficient differential-operator application is additive in its polynomial
symbol. -/
theorem constantCoeffDifferentialOperator_add_operator
    (P Q : Polynomial ℂ) (f : ℂ → ℂ) :
    constantCoeffDifferentialOperator (P + Q) f =
      constantCoeffDifferentialOperator P f +
        constantCoeffDifferentialOperator Q f := by
  funext z
  unfold constantCoeffDifferentialOperator
  apply Polynomial.sum_add_index
  · intro n
    simp
  · intro n a b
    ring

/-- A monomial differential-operator symbol selects one derivative reading. -/
theorem constantCoeffDifferentialOperator_monomial
    (n : ℕ) (a : ℂ) (f : ℂ → ℂ) :
    constantCoeffDifferentialOperator (Polynomial.monomial n a) f =
      fun z => a * iteratedDeriv n f z := by
  funext z
  simp [constantCoeffDifferentialOperator]

/-- A constant-coefficient differential operator preserves global smoothness. -/
theorem contDiff_constantCoeffDifferentialOperator
    (L : Polynomial ℂ) {f : ℂ → ℂ}
    (hf : ContDiff ℂ (⊤ : ℕ∞) f) :
    ContDiff ℂ (⊤ : ℕ∞) (constantCoeffDifferentialOperator L f) := by
  rw [show constantCoeffDifferentialOperator L f =
      fun z => ∑ n ∈ L.support, L.coeff n * iteratedDeriv n f z by
    funext z
    rfl]
  apply ContDiff.sum
  intro n hn
  exact contDiff_const.mul
    (GaloisForLFunctions.contDiff_iteratedDeriv n hf)

/-- **Polynomial-symbol composition law.**  Composing two constant-coefficient differential
operators on a smooth response multiplies their polynomial symbols. -/
theorem constantCoeffDifferentialOperator_comp
    (P Q : Polynomial ℂ) {f : ℂ → ℂ}
    (hf : ContDiff ℂ (⊤ : ℕ∞) f) :
    constantCoeffDifferentialOperator P
        (constantCoeffDifferentialOperator Q f) =
      constantCoeffDifferentialOperator (P * Q) f := by
  induction P using Polynomial.induction_on' with
  | add P R hP hR =>
      rw [constantCoeffDifferentialOperator_add_operator, hP, hR, add_mul,
        constantCoeffDifferentialOperator_add_operator]
  | monomial n a =>
      induction Q using Polynomial.induction_on' with
      | add Q R hQ hR =>
          rw [constantCoeffDifferentialOperator_add_operator,
            constantCoeffDifferentialOperator_add_smooth
              (Polynomial.monomial n a)
              (contDiff_constantCoeffDifferentialOperator Q hf)
              (contDiff_constantCoeffDifferentialOperator R hf),
            hQ, hR, mul_add, constantCoeffDifferentialOperator_add_operator]
      | monomial m b =>
          rw [constantCoeffDifferentialOperator_monomial,
            constantCoeffDifferentialOperator_monomial]
          funext z
          rw [iteratedDeriv_const_mul b
            ((GaloisForLFunctions.contDiff_iteratedDeriv m hf).contDiffAt.of_le
              (by exact_mod_cast le_top)),
            iteratedDeriv_comp_iterate]
          rw [Polynomial.monomial_mul_monomial,
            constantCoeffDifferentialOperator_monomial]
          ring

/-- **Finite-spectral dressing stability.**  Infinite constant-coefficient spectral complexity
survives addition of an arbitrary finite exponential response. -/
theorem constantCoefficientDifferentiallyTranscendental_add_finset_expSum
    {f : ℂ → ℂ} (hf : ConstantCoefficientDifferentiallyTranscendental f)
    (hfSmooth : ContDiff ℂ (⊤ : ℕ∞) f)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a c : ι → ℂ) :
    ConstantCoefficientDifferentiallyTranscendental
      (f + fun z => ∑ i ∈ s, a i * Complex.exp (c i * z)) := by
  let g : ℂ → ℂ := fun z => ∑ i ∈ s, a i * Complex.exp (c i * z)
  let A : Polynomial ℂ := ∏ i ∈ s, (Polynomial.X - Polynomial.C (c i))
  have hgSmooth : ContDiff ℂ (⊤ : ℕ∞) g := by
    dsimp [g]
    fun_prop
  have hAmonic : A.Monic := by
    exact Polynomial.monic_prod_of_monic _ _
      (fun i _ => Polynomial.monic_X_sub_C (c i))
  have hAne : A ≠ 0 := hAmonic.ne_zero
  have hAroot : ∀ i ∈ s, A.eval (c i) = 0 := by
    intro i hi
    dsimp only [A]
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero hi (by simp)
  intro L hzero
  have hzero' : constantCoeffDifferentialOperator L (f + g) = 0 := by
    simpa [g] using hzero
  have hproductSum :
      constantCoeffDifferentialOperator (A * L) (f + g) = 0 := by
    change constantCoeffDifferentialOperator (A * L)
      (fun x => f x + g x) = 0
    change constantCoeffDifferentialOperator L
      (fun x => f x + g x) = 0 at hzero'
    rw [← constantCoeffDifferentialOperator_comp A L
      (hfSmooth.add hgSmooth), hzero']
    funext z
    unfold constantCoeffDifferentialOperator
    simp only [Pi.zero_apply, iteratedDeriv_const_zero, mul_zero]
    rw [Polynomial.sum_def]
    simp
  have hproductG : constantCoeffDifferentialOperator (A * L) g = 0 := by
    funext z
    rw [show g = fun z => ∑ i ∈ s, a i * Complex.exp (c i * z) by rfl,
      constantCoeffDifferentialOperator_finset_expSum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Polynomial.eval_mul, hAroot i hi]
    ring
  rw [constantCoeffDifferentialOperator_add_smooth (A * L)
    hfSmooth hgSmooth, hproductG, add_zero] at hproductSum
  have hproduct : A * L = 0 := hf (A * L) hproductSum
  exact (mul_eq_zero.mp hproduct).resolve_left hAne

/-- **Meromorphic dressing stability.**  A simple-pole source remains infinitely spectrally
complex after every finite exponential dressing, without a global smoothness assumption. -/
theorem constantCoefficientDifferentiallyTranscendental_add_finset_expSum_of_simplePole
    {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p)
    (horder : meromorphicOrderAt f p = ((-1 : ℤ) : WithTop ℤ))
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a c : ι → ℂ) :
    ConstantCoefficientDifferentiallyTranscendental
      (f + fun z => ∑ i ∈ s, a i * Complex.exp (c i * z)) := by
  let g : ℂ → ℂ := fun z => ∑ i ∈ s, a i * Complex.exp (c i * z)
  have hg : AnalyticAt ℂ g p := by
    dsimp [g]
    fun_prop
  apply constantCoefficientDifferentiallyTranscendental_of_meromorphic_simplePole
    (hf.add hg.meromorphicAt)
  have hlt : meromorphicOrderAt f p < meromorphicOrderAt g p := by
    rw [horder]
    apply lt_of_lt_of_le _ hg.meromorphicOrderAt_nonneg
    exact_mod_cast (show (-1 : ℤ) < 0 by omega)
  rw [meromorphicOrderAt_add_eq_left_of_lt hg.meromorphicAt hlt, horder]

/-- Infinite spectral complexity survives coupling to a finite-level Gibbs response. -/
theorem constantCoefficientDifferentiallyTranscendental_add_finiteComplexGibbsPartition
    {f : ℂ → ℂ} (hf : ConstantCoefficientDifferentiallyTranscendental f)
    (hfSmooth : ContDiff ℂ (⊤ : ℕ∞) f)
    {α : Type*} [Fintype α] (energy : α → ℝ) :
    ConstantCoefficientDifferentiallyTranscendental
      (f + finiteComplexGibbsPartition energy) := by
  classical
  simpa only [finiteComplexGibbsPartition, one_mul] using!
    (constantCoefficientDifferentiallyTranscendental_add_finset_expSum
      hf hfSmooth (Finset.univ : Finset α) (fun _ => (1 : ℂ))
      (fun a => -(energy a : ℂ)))

/-- A meromorphic simple-pole response remains infinitely spectrally complex after coupling to an
arbitrary finite Gibbs sector. -/
theorem constantCoefficientDifferentiallyTranscendental_add_finiteComplexGibbsPartition_of_simplePole
    {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p)
    (horder : meromorphicOrderAt f p = ((-1 : ℤ) : WithTop ℤ))
    {α : Type*} [Fintype α] (energy : α → ℝ) :
    ConstantCoefficientDifferentiallyTranscendental
      (f + finiteComplexGibbsPartition energy) := by
  classical
  simpa only [finiteComplexGibbsPartition, one_mul] using!
    (constantCoefficientDifferentiallyTranscendental_add_finset_expSum_of_simplePole
      hf horder (Finset.univ : Finset α) (fun _ => (1 : ℂ))
      (fun a => -(energy a : ℂ)))

/-- Finite spectral dressing cannot turn an infinitely complex smooth response into any other
finite-level Gibbs partition function. -/
theorem add_finiteComplexGibbsPartition_ne_finiteComplexGibbsPartition
    {f : ℂ → ℂ} (hf : ConstantCoefficientDifferentiallyTranscendental f)
    (hfSmooth : ContDiff ℂ (⊤ : ℕ∞) f)
    {α β : Type*} [Fintype α] [Fintype β]
    (dressing : α → ℝ) (target : β → ℝ) :
    f + finiteComplexGibbsPartition dressing ≠
      finiteComplexGibbsPartition target :=
  ne_finiteComplexGibbsPartition_of_constantCoefficientDifferentiallyTranscendental
    (constantCoefficientDifferentiallyTranscendental_add_finiteComplexGibbsPartition
      hf hfSmooth dressing) target

/-- A simple-pole response plus any finite Gibbs dressing cannot equal another finite Gibbs
partition function. -/
theorem add_finiteComplexGibbsPartition_ne_finiteComplexGibbsPartition_of_simplePole
    {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p)
    (horder : meromorphicOrderAt f p = ((-1 : ℤ) : WithTop ℤ))
    {α β : Type*} [Fintype α] [Fintype β]
    (dressing : α → ℝ) (target : β → ℝ) :
    f + finiteComplexGibbsPartition dressing ≠
      finiteComplexGibbsPartition target :=
  ne_finiteComplexGibbsPartition_of_constantCoefficientDifferentiallyTranscendental
    (constantCoefficientDifferentiallyTranscendental_add_finiteComplexGibbsPartition_of_simplePole
      hf horder dressing) target

end

end HTGeometry
