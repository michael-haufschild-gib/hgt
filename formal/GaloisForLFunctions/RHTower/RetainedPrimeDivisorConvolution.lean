import GaloisForLFunctions.RHTower.RetainedPrimeMobiusEulerIdentity
import GaloisForLFunctions.RHTower.MobiusHalfSelectionPoleObstruction

/-!
# Exact retained source and its divisor convolution

The full retained weighted source is the square-root Abel mean of its exact
Dirichlet convolution with the literal divisor increment. Möbius inversion
identifies the infinite series with the completed prime--polar--Gamma source.
The normalized series equals the finite Mellin expression on `Re s > 2`.
This module does not assert its integral representation or source-cone fullness.
-/

noncomputable section
open Complex Finset Filter Topology
open scoped BigOperators
namespace RHTower

/-- The literal retained-functional coefficient as an arithmetic function. -/
def retainedPrimeMobiusAF (P : Finset ℕ) (y : Finset ℕ → ℂ) : ArithmeticFunction ℂ :=
  ⟨retainedPrimeMobiusCoefficient P y, retainedPrimeMobiusCoefficient_zero P y⟩

/-- Complete convolution with the actual prime-free divisor increment. -/
def retainedPrimeDivisorConvolution (P : Finset ℕ) (y : Finset ℕ → ℂ) : ArithmeticFunction ℂ :=
  retainedPrimeMobiusAF P y * halfSelectionDivisorSourceAF

private lemma summable_divisor_source {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeriesSummable halfSelectionDivisorSourceAF s := by
  apply (LSeriesSummable_congr s (fun {n} hn => halfSelectionDivisorSourceAF_apply hn)).mpr
  exact LSeriesSummable_primeFreeDivisorIncrement hs

/-- Absolute convergence of the complete retained convolution on a safe half-plane. -/
lemma LSeriesSummable_retainedPrimeDivisorConvolution (P : Finset ℕ) (y : Finset ℕ → ℂ)
    {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeriesSummable (retainedPrimeDivisorConvolution P y) s :=
  ArithmeticFunction.LSeriesSummable_mul
    (LSeriesSummable_retainedPrimeMobiusCoefficient P y (by linarith)) (summable_divisor_source hs)

/-- Complete L-series product of the literal weighted source and divisor increment. -/
lemma LSeries_retainedPrimeDivisorConvolution_eq_product (P : Finset ℕ) (y : Finset ℕ → ℂ)
    {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeries (retainedPrimeDivisorConvolution P y) s =
      LSeries (retainedPrimeMobiusCoefficient P y) s * divisorSourceDirichlet s := by
  rw [retainedPrimeDivisorConvolution, ArithmeticFunction.LSeries_mul'
    (f := retainedPrimeMobiusAF P y) (g := halfSelectionDivisorSourceAF)
    (LSeriesSummable_retainedPrimeMobiusCoefficient P y (by linarith)) (summable_divisor_source hs),
    divisorSourceDirichlet_eq_LSeries hs]
  congr 1
  exact LSeries_congr (fun {n} hn => halfSelectionDivisorSourceAF_apply hn) s

private lemma sum_divisor_source (N : ℕ) :
    (∑ n ∈ Icc 1 N, halfSelectionDivisorSourceAF n) = (primeFreeDivisorDefect N : ℂ) := by
  rw [← sum_primeFreeDivisorIncrement N, Complex.ofReal_sum]
  apply sum_congr rfl
  intro n hn
  exact halfSelectionDivisorSourceAF_apply (by have := (mem_Icc.mp hn).1; omega)

/-- The convolution's summatory function is the exact retained floor-dilation source. -/
lemma sum_retainedPrimeDivisorConvolution (P : Finset ℕ) (y : Finset ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, retainedPrimeDivisorConvolution P y n) =
      ∑ d ∈ Icc 1 N, retainedPrimeMobiusCoefficient P y d * (primeFreeDivisorDefect (N / d) : ℂ) := by
  rw [retainedPrimeDivisorConvolution, sum_Icc_mul_apply]
  simp_rw [sum_divisor_source]
  rfl

/-- Actual source pairing with a functional on all retained prime subsets. -/
def retainedPrimeSourceMean (P : Finset ℕ) (y : Finset ℕ → ℂ) (M : ℕ) : ℂ :=
  ∑ d ∈ Icc 1 M, y (d.primeFactors ∩ P) * (mobiusDivisorDilationChannel M d : ℂ)

/-- The literal source pairing is the exact square-root Abel mean of the
complete convolution, including every clipped endpoint. -/
lemma retainedPrimeSourceMean_eq_convolution_abel (P : Finset ℕ) (y : Finset ℕ → ℂ) (M : ℕ) :
    retainedPrimeSourceMean P y M =
      ∑ k ∈ Icc 1 (M - 1), ((Real.sqrt (k + 1 : ℕ) - Real.sqrt k : ℝ) : ℂ) *
        ∑ n ∈ Icc 1 k, retainedPrimeDivisorConvolution P y n := by
  have hlast : mobiusDivisorDilationChannel M M = 0 := by
    by_cases hM : M = 0
    · subst M
      simp [mobiusDivisorDilationChannel]
    · simp [mobiusDivisorDilationChannel, Icc_eq_empty_of_lt (by omega : M - 1 < M)]
  have hdrop : (∑ d ∈ Icc 1 (M - 1),
      y (d.primeFactors ∩ P) * (mobiusDivisorDilationChannel M d : ℂ)) =
      retainedPrimeSourceMean P y M := by
    apply sum_subset
    · intro d hd
      obtain ⟨hl, hu⟩ := mem_Icc.mp hd
      exact mem_Icc.mpr ⟨hl, by omega⟩
    · intro d hd hn
      have he : d = M := by simp only [mem_Icc] at hd hn; omega
      subst d
      simp only [hlast, Complex.ofReal_zero, mul_zero]
  have hpoint (d : ℕ) : y (d.primeFactors ∩ P) * (mobiusDivisorDilationChannel M d : ℂ) =
      ∑ k ∈ Icc d (M - 1), ((Real.sqrt (k + 1 : ℕ) - Real.sqrt k : ℝ) : ℂ) *
        (retainedPrimeMobiusCoefficient P y d * (primeFreeDivisorDefect (k / d) : ℂ)) := by
    rw [mobiusDivisorDilationChannel, Complex.ofReal_mul, Complex.ofReal_sum,
      Finset.mul_sum, Finset.mul_sum]
    apply sum_congr rfl
    intro k hk
    rw [Complex.ofReal_mul, retainedPrimeMobiusCoefficient]
    push_cast
    ring
  rw [← hdrop]
  simp_rw [hpoint, sum_retainedPrimeDivisorConvolution, Finset.mul_sum]
  apply sum_comm'
  intro d k
  simp only [mem_Icc]
  omega

/-- The original prime--polar--Gamma atom has its exact logarithmic-derivative series. -/
lemma LSeries_completedPrimePolarGammaAtom {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (completedPrimePolarGammaAtom n : ℂ)) s =
      -deriv riemannZeta s / riemannZeta s - riemannZeta s + (2 * Real.eulerMascheroniConstant : ℂ) := by
  let c : ℂ := (2 * Real.eulerMascheroniConstant : ℝ)
  have hf : (fun n => (completedPrimePolarGammaAtom n : ℂ)) =
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) - (1 : ℕ → ℂ) + c • LSeries.delta := by
    ext n
    simp only [completedPrimePolarGammaAtom, Pi.add_apply, Pi.sub_apply, Pi.one_apply,
      Pi.smul_apply, smul_eq_mul, LSeries.delta]
    dsimp [c]
    split_ifs <;> push_cast <;> ring
  have hvm := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hone : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have hdelta : LSeriesSummable LSeries.delta s := by
    apply summable_of_ne_finset_zero (s := {1})
    intro n hn
    simp only [LSeries.term_delta, if_neg (show n ≠ 1 by simpa using hn)]
  rw [hf, LSeries_add (hvm.sub hone) (hdelta.smul c), LSeries_sub hvm hone,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    LSeries_one_eq_riemannZeta hs, LSeries_smul, LSeries_delta]
  simp [c]

/-- Möbius inversion of the actual divisor source gives the pole-filled
prime--polar--Gamma continuation on the initial half-plane. -/
lemma divisorSourceDirichlet_div_zeta_eq_completed_source
    {s : ℂ} (hs : 3 / 2 < s.re) :
    divisorSourceDirichlet s / riemannZeta s =
      simplePrimeDivisorContinuedSource (s + 1 / 2) + (2 * Real.eulerMascheroniConstant : ℂ) := by
  have hs1 : 1 < s.re := by linarith
  have hm := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs1
  have hb := LSeriesSummable_primeFreeDivisorIncrement hs
  have he : LSeries (LSeries.convolution (fun n => (ArithmeticFunction.moebius n : ℂ))
        (fun n => (primeFreeDivisorIncrement n : ℂ))) s =
      LSeries (fun n => (completedPrimePolarGammaAtom n : ℂ)) s := by
    apply LSeries_congr _ s
    intro n hn
    rw [LSeries.convolution_def]
    have h := congrArg Complex.ofReal (primeFreeDivisorIncrement_mobius_convolution_eq_atom hn)
    simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast] using h
  rw [LSeries_convolution' hm hb, LSeries_moebius_eq_inv_riemannZeta hs1,
    ← divisorSourceDirichlet_eq_LSeries hs, LSeries_completedPrimePolarGammaAtom hs1] at he
  rw [simplePrimeDivisorContinuedSource_eq_zetaLogDeriv (by
    simp only [Complex.add_re]; norm_num; linarith : 3 / 2 < (s + 1 / 2).re), add_sub_cancel_right]
  unfold zetaLogDeriv
  calc
    _ = (riemannZeta s)⁻¹ * divisorSourceDirichlet s := by ring
    _ = _ := by rw [he]; ring

/-- Exact initial-half-plane series of the complete retained source, with its
finite numerator and Euler denominator identified. -/
lemma LSeries_retainedPrimeDivisorConvolution_eq_completed_source
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (y : Finset ℕ → ℂ)
    {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeries (retainedPrimeDivisorConvolution P y) s =
      finiteDirichletPolynomial (retainedPrimeDirichletCoefficients P y) s *
        (simplePrimeDivisorContinuedSource (s + 1 / 2) + (2 * Real.eulerMascheroniConstant : ℂ)) /
        (∏ p ∈ P, (1 - (p : ℂ) ^ (-s))) := by
  rw [LSeries_retainedPrimeDivisorConvolution_eq_product P y hs,
    LSeries_retainedPrimeMobiusCoefficient_eq P hP y (by linarith),
    ← divisorSourceDirichlet_div_zeta_eq_completed_source hs]
  ring

end RHTower

namespace RHTower

/-- The exact series, after the two integration-clock factors, is the finite
retained Mellin expression. The integral representation is a separate theorem. -/
lemma retainedPrimeDivisor_normalized_LSeries_eq_Mellin
    (Q : Finset Nat.Primes) (y : Finset ℕ → ℂ) {s : ℂ} (hs : 2 < s.re) :
    LSeries (retainedPrimeDivisorConvolution (Q.image (fun p : Nat.Primes => (p : ℕ))) y) (s - 1 / 2) /
      (2 * s * (s - 1 / 2)) =
    finiteDirichletDivisorMellin
      (retainedPrimeDirichletCoefficients (Q.image (fun p : Nat.Primes => (p : ℕ))) y) Q
      (2 * Real.eulerMascheroniConstant : ℂ) s := by
  have hQ : ∀ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), p.Prime := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact q.property
  have hw : 3 / 2 < (s - 1 / 2).re := by
    simp only [Complex.sub_re]; norm_num; linarith
  rw [LSeries_retainedPrimeDivisorConvolution_eq_completed_source _ hQ y hw]
  have he : (∏ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), (1 - (p : ℂ) ^ (-(s - 1 / 2)))) =
      finitePrimeEulerDenominator Q (s - 1 / 2) := by
    rw [Finset.prod_image]
    · rfl
    · intro a ha b hb hab
      exact Subtype.ext hab
  rw [he]
  simp only [finiteDirichletDivisorMellin, finiteDirichletDivisorSource]
  rw [div_div]

end RHTower
