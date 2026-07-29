import GaloisForLFunctions.HTGeometry.GammaShiftCasoratian
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Algebra.Polynomial.SumIteratedDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Confluent Gamma-shift annihilator polynomials

This file constructs the canonical monic consecutive-shift coefficient polynomial for an
arbitrary finite packet of shifts with arbitrary multiplicities.  The construction is intrinsic:
it is the coordinate vector of the prescribed-root polynomial in the ascending-Pochhammer basis.
-/

open scoped BigOperators

namespace GaloisForLFunctions

open Module Polynomial

noncomputable section

variable (K : Type*) [CommRing K] [IsDomain K]

/-- The ascending-Pochhammer polynomials, regarded as a polynomial sequence. -/
def ascPochhammerSequence : Polynomial.Sequence K where
  elems' := ascPochhammer K
  degree_eq' i := by
    rw [Polynomial.degree_eq_natDegree (monic_ascPochhammer K i).ne_zero,
      ascPochhammer_natDegree]

/-- Ascending-Pochhammer polynomials form a basis of the polynomial ring over a field. -/
def ascPochhammerBasis : Module.Basis ℕ K K[X] :=
  (ascPochhammerSequence K).basis (fun i => by
    simpa only [ascPochhammerSequence, monic_ascPochhammer,
      Polynomial.Monic.leadingCoeff] using (isUnit_one : IsUnit (1 : K)))

@[simp]
theorem ascPochhammerBasis_apply (i : ℕ) :
    ascPochhammerBasis K i = ascPochhammer K i := by
  simp [ascPochhammerBasis, ascPochhammerSequence]

/-- The `i`-th ascending-Pochhammer coordinate of a polynomial. -/
def ascPochhammerCoeff (P : K[X]) (i : ℕ) : K :=
  (ascPochhammerBasis K).repr P i

/-- Reconstruction from the finitely supported ascending-Pochhammer coordinates. -/
theorem ascPochhammer_eq_finsupp_sum (P : K[X]) :
    P = ((ascPochhammerBasis K).repr P).sum
      (fun i c => c • ascPochhammer K i) := by
  calc
    P = (ascPochhammerBasis K).repr.symm ((ascPochhammerBasis K).repr P) :=
      ((ascPochhammerBasis K).repr.symm_apply_apply P).symm
    _ = ((ascPochhammerBasis K).repr P).sum
        (fun i c => c • ascPochhammer K i) := by
      rw [Module.Basis.repr_symm_apply, Finsupp.linearCombination_apply]
      apply Finsupp.sum_congr
      intro i _
      rw [ascPochhammerBasis_apply]

/-- Coordinates above the polynomial's degree vanish. -/
theorem ascPochhammerCoeff_eq_zero_of_natDegree_lt (P : K[X]) {N i : ℕ}
    (hdeg : P.natDegree ≤ N) (hi : N < i) :
    ascPochhammerCoeff K P i = 0 := by
  have hmem : P ∈ Submodule.span K ((ascPochhammerSequence K) '' Set.Iic N) := by
    rw [(ascPochhammerSequence K).span_degreeLE (fun j _ => by
      simpa only [ascPochhammerSequence, monic_ascPochhammer,
        Polynomial.Monic.leadingCoeff] using (isUnit_one : IsUnit (1 : K)))]
    rw [Polynomial.mem_degreeLE]
    exact Polynomial.degree_le_natDegree.trans (by exact_mod_cast hdeg)
  have hbmem : P ∈ Submodule.span K ((ascPochhammerBasis K) '' Set.Iic N) := by
    simpa only [ascPochhammerBasis_apply, ascPochhammerSequence] using hmem
  have hsupp : ↑((ascPochhammerBasis K).repr P).support ⊆ Set.Iic N :=
    (Module.Basis.mem_span_image (ascPochhammerBasis K)).mp hbmem
  by_contra hne
  have himem : i ∈ ((ascPochhammerBasis K).repr P).support :=
    Finsupp.mem_support_iff.mpr hne
  exact (Nat.not_le_of_lt hi) (hsupp himem)

/-- Finite reconstruction through any degree bound. -/
theorem ascPochhammer_finite_expansion (P : K[X]) (N : ℕ)
    (hdeg : P.natDegree ≤ N) :
    P = ∑ i ∈ Finset.range (N + 1),
      ascPochhammerCoeff K P i • ascPochhammer K i := by
  calc
    P = ((ascPochhammerBasis K).repr P).sum
        (fun i c => c • ascPochhammer K i) := ascPochhammer_eq_finsupp_sum K P
    _ = ∑ i ∈ Finset.range (N + 1),
        ascPochhammerCoeff K P i • ascPochhammer K i := by
      unfold Finsupp.sum
      apply Finset.sum_subset
      · intro i hi
        have hi0 : ((ascPochhammerBasis K).repr P) i ≠ 0 :=
          Finsupp.mem_support_iff.mp hi
        have hle : i ≤ N := by
          by_contra hnot
          exact hi0 (ascPochhammerCoeff_eq_zero_of_natDegree_lt K P hdeg
            (Nat.lt_of_not_ge hnot))
        simpa only [Finset.mem_range, Nat.lt_add_one_iff]
      · intro i _ hnot
        have hz : ((ascPochhammerBasis K).repr P) i = 0 :=
          Finsupp.notMem_support_iff.mp hnot
        rw [hz]
        simp

@[simp]
theorem ascPochhammerCoeff_ascPochhammer (i j : ℕ) :
    ascPochhammerCoeff K (ascPochhammer K i) j = if i = j then 1 else 0 := by
  classical
  simp [ascPochhammerCoeff, ← ascPochhammerBasis_apply, Module.Basis.repr_self,
    Finsupp.single_apply]

/-- A monic degree-`N` polynomial has top ascending-Pochhammer coordinate one. -/
theorem ascPochhammerCoeff_top_of_monic (P : K[X]) (N : ℕ)
    (hP : P.Monic) (hdeg : P.natDegree = N) :
    ascPochhammerCoeff K P N = 1 := by
  have hexp := ascPochhammer_finite_expansion K P N hdeg.le
  have hcoeff := congrArg (fun Q : K[X] => Q.coeff N) hexp
  rw [Finset.sum_range_succ] at hcoeff
  simp only [Polynomial.coeff_add, Polynomial.coeff_smul, smul_eq_mul] at hcoeff
  have hlower : ∑ i ∈ Finset.range N,
      ascPochhammerCoeff K P i * (ascPochhammer K i).coeff N = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hiN : i < N := Finset.mem_range.mp hi
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · simp
    · simpa only [ascPochhammer_natDegree] using hiN
  have hcoefflower :
      (∑ i ∈ Finset.range N,
        ascPochhammerCoeff K P i • ascPochhammer K i).coeff N = 0 := by
    simpa only [← Polynomial.lcoeff_apply, map_sum, map_smul, smul_eq_mul] using hlower
  rw [hcoefflower, zero_add] at hcoeff
  have hPcoeff : P.coeff N = 1 := by
    rw [← hdeg]
    exact hP.coeff_natDegree
  have hRcoeff : (ascPochhammer K N).coeff N = 1 := by
    simpa only [ascPochhammer_natDegree] using
      (monic_ascPochhammer K N).coeff_natDegree
  rw [hPcoeff, hRcoeff, mul_one] at hcoeff
  exact hcoeff.symm

/-- Evaluation at zero reads the zeroth ascending-Pochhammer coordinate. -/
theorem ascPochhammerCoeff_zero_eq_eval_zero (P : K[X]) :
    ascPochhammerCoeff K P 0 = P.eval 0 := by
  have hsum := ascPochhammer_eq_finsupp_sum K P
  have heval := congrArg (Polynomial.eval (0 : K)) hsum
  unfold Finsupp.sum at heval
  rw [Polynomial.eval_finsetSum] at heval
  simpa [Polynomial.eval_smul, ascPochhammer_eval_zero, smul_eq_mul,
    ascPochhammerCoeff] using heval.symm

section GammaJetRoot

variable {ι : Type*} [Fintype ι]

/-- The total number of jet values in a finite packet. -/
def gammaJetOrder (mult : ι → ℕ) : ℕ := ∑ i, mult i

/-- The monic polynomial with roots `s + shift i` and prescribed multiplicities `mult i`. -/
def gammaJetRootPolynomial (s : K) (shift : ι → K) (mult : ι → ℕ) : K[X] :=
  ∏ i, (Polynomial.X - Polynomial.C (s + shift i)) ^ mult i

omit [IsDomain K] in
theorem gammaJetRootPolynomial_monic (s : K) (shift : ι → K) (mult : ι → ℕ) :
    (gammaJetRootPolynomial K s shift mult).Monic := by
  classical
  apply Polynomial.monic_prod_of_monic
  intro i _
  exact (Polynomial.monic_X_sub_C (s + shift i)).pow (mult i)

theorem gammaJetRootPolynomial_natDegree (s : K) (shift : ι → K) (mult : ι → ℕ) :
    (gammaJetRootPolynomial K s shift mult).natDegree = gammaJetOrder mult := by
  classical
  rw [gammaJetRootPolynomial, Polynomial.natDegree_prod_of_monic]
  · rw [gammaJetOrder]
    apply Finset.sum_congr rfl
    intro i _
    rw [(Polynomial.monic_X_sub_C (s + shift i)).natDegree_pow,
      Polynomial.natDegree_X_sub_C, mul_one]
  · intro i _
    exact (Polynomial.monic_X_sub_C (s + shift i)).pow (mult i)

/-- Equation (3): the canonical finite ascending-factorial expansion. -/
theorem gammaJetRootPolynomial_expansion (s : K) (shift : ι → K) (mult : ι → ℕ) :
    gammaJetRootPolynomial K s shift mult =
      ∑ k ∈ Finset.range (gammaJetOrder mult + 1),
        ascPochhammerCoeff K (gammaJetRootPolynomial K s shift mult) k •
          ascPochhammer K k := by
  apply ascPochhammer_finite_expansion
  exact (gammaJetRootPolynomial_natDegree K s shift mult).le

/-- The canonical annihilator is monic in the shift coordinate. -/
theorem gammaJetRootPolynomial_topCoeff (s : K) (shift : ι → K) (mult : ι → ℕ) :
    ascPochhammerCoeff K (gammaJetRootPolynomial K s shift mult) (gammaJetOrder mult) = 1 := by
  apply ascPochhammerCoeff_top_of_monic
  · exact gammaJetRootPolynomial_monic K s shift mult
  · exact gammaJetRootPolynomial_natDegree K s shift mult

omit [IsDomain K] in
/-- Every prescribed root factor occurs with its requested multiplicity. -/
theorem gammaJetRootPolynomial_factor (s : K) (shift : ι → K) (mult : ι → ℕ) (i : ι) :
    (Polynomial.X - Polynomial.C (s + shift i)) ^ mult i ∣
      gammaJetRootPolynomial K s shift mult := by
  classical
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

omit [IsDomain K] in
/-- Every polynomial derivative below the prescribed multiplicity vanishes at that root. -/
theorem gammaJetRootPolynomial_iterate_derivative_eval_eq_zero
    (s : K) (shift : ι → K) (mult : ι → ℕ) (i : ι) {m : ℕ} (hm : m < mult i) :
    ((Polynomial.derivative^[m]) (gammaJetRootPolynomial K s shift mult)).eval
      (s + shift i) = 0 := by
  obtain ⟨Q, hQ⟩ := gammaJetRootPolynomial_factor K s shift mult i
  have hmap : (gammaJetRootPolynomial K s shift mult).map (algebraMap K K) =
      (Polynomial.X - Polynomial.C (s + shift i)) ^ mult i * Q := by
    simpa using hQ
  simpa [Polynomial.aeval_def] using
    Polynomial.aeval_iterate_derivative_of_lt
      (gammaJetRootPolynomial K s shift mult) (mult i) (s + shift i) hmap hm

/-- Analytic and formal iterated derivatives agree for complex polynomial evaluation. -/
theorem iteratedDeriv_complexPolynomial_eval (P : ℂ[X]) (m : ℕ) (x : ℂ) :
    iteratedDeriv m (fun z => P.eval z) x =
      ((Polynomial.derivative^[m]) P).eval x := by
  induction m generalizing P x with
  | zero => simp
  | succ m ih =>
      rw [iteratedDeriv_succ,
        show iteratedDeriv m (fun z => P.eval z) =
          fun z => ((Polynomial.derivative^[m]) P).eval z from funext (ih P)]
      rw [show deriv (fun z => ((Polynomial.derivative^[m]) P).eval z) =
          fun z => ((Polynomial.derivative^[m]) P).derivative.eval z by
        funext z
        exact (((Polynomial.derivative^[m]) P).hasDerivAt z).deriv,
        Function.iterate_succ_apply']

/-- Multiplying by the prescribed-root polynomial kills every jet below its local multiplicity. -/
theorem iteratedDeriv_gammaJetRoot_mul_eq_zero
    (s : ℂ) (shift : ι → ℂ) (mult : ι → ℕ) (i : ι)
    (g : ℂ → ℂ) {m : ℕ} (hm : m < mult i) (hg : ContDiffAt ℂ m g (s + shift i)) :
    iteratedDeriv m
      (fun z => (gammaJetRootPolynomial ℂ s shift mult).eval z * g z)
      (s + shift i) = 0 := by
  have hpoly : ContDiffAt ℂ m
      (fun z => (gammaJetRootPolynomial ℂ s shift mult).eval z) (s + shift i) :=
    (Polynomial.contDiff_aeval
      (gammaJetRootPolynomial ℂ s shift mult) (m : WithTop ℕ∞)).contDiffAt
  have hprod := iteratedDeriv_mul (n := m) (x := s + shift i) hpoly hg
  have hfun :
      (fun z => (gammaJetRootPolynomial ℂ s shift mult).eval z * g z) =
        (fun z => (gammaJetRootPolynomial ℂ s shift mult).eval z) * g := by
    funext z
    rfl
  rw [hfun, hprod]
  apply Finset.sum_eq_zero
  intro a ha
  have ham : a ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
  have hadi : a < mult i := ham.trans_lt hm
  rw [iteratedDeriv_complexPolynomial_eval,
    gammaJetRootPolynomial_iterate_derivative_eval_eq_zero ℂ s shift mult i hadi]
  ring

omit [IsDomain K] in
theorem gammaJetRootPolynomial_eval_zero (s : K) (shift : ι → K) (mult : ι → ℕ) :
    (gammaJetRootPolynomial K s shift mult).eval 0 =
      (-1 : K) ^ gammaJetOrder mult * ∏ i, (s + shift i) ^ mult i := by
  classical
  rw [gammaJetRootPolynomial, Polynomial.eval_prod]
  simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, zero_sub]
  have hfactor : ∀ i : ι, (-(s + shift i)) ^ mult i =
      (-1 : K) ^ mult i * (s + shift i) ^ mult i := by
    intro i
    rw [show -(s + shift i) = (-1 : K) * (s + shift i) by ring, mul_pow]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rfl

/-- Equation (17), exactly: the zeroth annihilator coefficient is the signed root product. -/
theorem gammaJetRootPolynomial_zeroCoeff (s : K) (shift : ι → K) (mult : ι → ℕ) :
    ascPochhammerCoeff K (gammaJetRootPolynomial K s shift mult) 0 =
      (-1 : K) ^ gammaJetOrder mult * ∏ i, (s + shift i) ^ mult i := by
  rw [ascPochhammerCoeff_zero_eq_eval_zero,
    gammaJetRootPolynomial_eval_zero]

end GammaJetRoot

end

end GaloisForLFunctions
