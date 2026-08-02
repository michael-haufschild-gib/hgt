import GaloisForLFunctions.RHTower.SemilocalProlateThirdEulerCriticalJet
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Odd harmonic first activations in the semilocal prolate source

The published rank-one Lambert decomposition contains one new source harmonic at every odd Euler
degree `d = 2ℓ + 1`.  Its polynomial is

`p_ℓ(n) = ∑_{k=0}^ℓ 2^(3k) (ℓ)_k (n)_k / (2k)!`.

This file proves its exact degree and leading coefficient, propagates the literal new trace atom
through the positive Jacobi-radius square root, and proves the sharp amplitude

`(-1)^n F_(ℓ,n) / n^(2ℓ+1/2) → -C_ℓ L_ℓ² / √π`.

It also formalizes the source-weight gap: every trace interaction containing at least two
rank-one atoms lies below the single-atom odd top weight.  Thus the new harmonic is the unique
possible top-weight term at its first activation.
-/

noncomputable section

open Filter Real
open scoped BigOperators Topology
open Polynomial

namespace RHTower.OddHarmonicActivation

open GaloisForLFunctions.HTGeometry
open RHTower.FirstEulerCriticalJet
open RHTower.SecondEulerCriticalJet

/-- Coefficient of the falling-factorial term in the published source polynomial `p_ℓ`. -/
def sourceActivationCoefficient (ell k : ℕ) : ℝ :=
  (2 : ℝ) ^ (3 * k) * (ell.descFactorial k : ℝ) /
    ((2 * k).factorial : ℝ)

/-- Polynomial `p_ℓ`, written in the descending-Pochhammer basis. -/
def sourceActivationPolynomial (ell : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (ell + 1),
    C (sourceActivationCoefficient ell k) * descPochhammer ℝ k

/-- Candidate top coefficient `L_ℓ=2^(3ℓ)ℓ!/(2ℓ)!`. -/
def sourceActivationLeadingCoefficient (ell : ℕ) : ℝ :=
  (2 : ℝ) ^ (3 * ell) * (ell.factorial : ℝ) /
    ((2 * ell).factorial : ℝ)

lemma sourceActivationCoefficient_self (ell : ℕ) :
    sourceActivationCoefficient ell ell =
      sourceActivationLeadingCoefficient ell := by
  simp [sourceActivationCoefficient, sourceActivationLeadingCoefficient,
    Nat.descFactorial_self]

lemma sourceActivationLeadingCoefficient_ne_zero (ell : ℕ) :
    sourceActivationLeadingCoefficient ell ≠ 0 := by
  unfold sourceActivationLeadingCoefficient
  positivity

lemma sourceActivationPolynomial_natDegree_le (ell : ℕ) :
    (sourceActivationPolynomial ell).natDegree ≤ ell := by
  unfold sourceActivationPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  simp only [Finset.mem_range] at hk
  by_cases hc : sourceActivationCoefficient ell k = 0
  · simp [hc]
  · rw [Polynomial.natDegree_C_mul hc, descPochhammer_natDegree]
    omega

lemma sourceActivationPolynomial_coeff_top (ell : ℕ) :
    (sourceActivationPolynomial ell).coeff ell =
      sourceActivationLeadingCoefficient ell := by
  unfold sourceActivationPolynomial
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single ell]
  · rw [Polynomial.coeff_C_mul]
    rw [show (descPochhammer ℝ ell).coeff ell = 1 by
      simpa [descPochhammer_natDegree] using
        (monic_descPochhammer ℝ ell).coeff_natDegree]
    simp [sourceActivationCoefficient_self]
  · intro k hk hne
    simp only [Finset.mem_range] at hk
    rw [Polynomial.coeff_C_mul]
    have hlt : k < ell := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · simp
    · simpa [descPochhammer_natDegree] using hlt
  · simp

lemma sourceActivationPolynomial_natDegree (ell : ℕ) :
    (sourceActivationPolynomial ell).natDegree = ell :=
  Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (sourceActivationPolynomial_natDegree_le ell)
    (by
      rw [sourceActivationPolynomial_coeff_top]
      exact sourceActivationLeadingCoefficient_ne_zero ell)

lemma sourceActivationPolynomial_leadingCoeff (ell : ℕ) :
    (sourceActivationPolynomial ell).leadingCoeff =
      sourceActivationLeadingCoefficient ell := by
  rw [Polynomial.leadingCoeff, sourceActivationPolynomial_natDegree,
    sourceActivationPolynomial_coeff_top]

lemma sourceActivationPolynomial_degree (ell : ℕ) :
    (sourceActivationPolynomial ell).degree = ell := by
  rw [Polynomial.degree_eq_natDegree
    (by
      intro h
      have hne := sourceActivationLeadingCoefficient_ne_zero ell
      have hlead := sourceActivationPolynomial_leadingCoeff ell
      rw [h, Polynomial.leadingCoeff_zero] at hlead
      exact hne hlead.symm)]
  exact_mod_cast sourceActivationPolynomial_natDegree ell

theorem tendsto_sourceActivationPolynomial_div_pow (ell : ℕ) :
    Tendsto
      (fun n : ℕ =>
        (sourceActivationPolynomial ell).eval (n : ℝ) /
          (n : ℝ) ^ ell)
      atTop (nhds (sourceActivationLeadingCoefficient ell)) := by
  have hreal :=
    Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq
      (sourceActivationPolynomial ell) (Polynomial.X ^ ell)
      (by simp [sourceActivationPolynomial_degree])
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  simpa [sourceActivationPolynomial_leadingCoeff, Function.comp_def] using hnat

/-- Evaluation of the published source polynomial at a natural Jacobi index. -/
def sourceActivationValue (ell n : ℕ) : ℝ :=
  (sourceActivationPolynomial ell).eval (n : ℝ)

theorem sourceActivationValue_eq_falling_sum (ell n : ℕ) :
    sourceActivationValue ell n =
      ∑ k ∈ Finset.range (ell + 1),
        (2 : ℝ) ^ (3 * k) *
          (ell.descFactorial k : ℝ) * (n.descFactorial k : ℝ) /
            ((2 * k).factorial : ℝ) := by
  unfold sourceActivationValue sourceActivationPolynomial
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.eval_mul, Polynomial.eval_C,
    descPochhammer_eval_eq_descFactorial]
  unfold sourceActivationCoefficient
  ring

theorem tendsto_sourceActivationValue_succ_div_pow (ell : ℕ) :
    Tendsto
      (fun n : ℕ =>
        sourceActivationValue ell (n + 1) /
          ((n : ℝ) + 1) ^ ell)
      atTop (nhds (sourceActivationLeadingCoefficient ell)) := by
  have h := (tendsto_sourceActivationPolynomial_div_pow ell).comp
    (tendsto_add_atTop_nat 1)
  simpa [sourceActivationValue, Function.comp_def] using h

theorem tendsto_sourceActivationValue_div_succ_pow (ell : ℕ) :
    Tendsto
      (fun n : ℕ =>
        sourceActivationValue ell n /
          ((n : ℝ) + 1) ^ ell)
      atTop (nhds (sourceActivationLeadingCoefficient ell)) := by
  let Q : ℝ[X] := (Polynomial.X + Polynomial.C 1) ^ ell
  have hdeg :
      (sourceActivationPolynomial ell).degree = Q.degree := by
    dsimp [Q]
    rw [sourceActivationPolynomial_degree, Polynomial.degree_pow,
      Polynomial.degree_X_add_C]
    simp
  have hreal :=
    Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq
      (sourceActivationPolynomial ell) Q hdeg
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  have hleadQ : Q.leadingCoeff = 1 := by
    dsimp [Q]
    rw [Polynomial.leadingCoeff_pow, Polynomial.leadingCoeff_X_add_C]
    simp
  rw [sourceActivationPolynomial_leadingCoeff, hleadQ, div_one] at hnat
  simpa [sourceActivationValue, Q, sourceActivationPolynomial_leadingCoeff,
    Polynomial.leadingCoeff_X_add_C, Function.comp_def] using hnat

/-- Source scalar `C_ℓ=(-1)^ℓ 2^(3/2-2ℓ) binom(2ℓ,ℓ)`. -/
def sourceHarmonicCoefficient (ell : ℕ) : ℝ :=
  (-1 : ℝ) ^ ell * 2 * Real.sqrt 2 * normalizedCentralBinom ell

/-- Literal contribution of the newly activated harmonic to the positive Jacobi radius. -/
def sourceFirstActivationRadiusCoefficient (ell n : ℕ) : ℝ :=
  semilocalArchimedeanJacobiCoefficient n *
    sourceHarmonicCoefficient ell *
    (((-1 : ℝ) ^ (n + 1) * normalizedCentralBinom (n + 1) *
        sourceActivationValue ell (n + 1) ^ 2) -
      ((-1 : ℝ) ^ n * normalizedCentralBinom n *
        sourceActivationValue ell n ^ 2)) / 2

/-- Signed nonoscillating amplitude of the same literal source contribution. -/
def sourceFirstActivationSignedAmplitude (ell n : ℕ) : ℝ :=
  -(sourceHarmonicCoefficient ell / 2) *
    semilocalArchimedeanJacobiCoefficient n *
    normalizedCentralBinom n *
    (centralBinomRatio n * sourceActivationValue ell (n + 1) ^ 2 +
      sourceActivationValue ell n ^ 2)

theorem sourceFirstActivationRadiusCoefficient_eq_signed
    (ell n : ℕ) :
    sourceFirstActivationRadiusCoefficient ell n =
      (-1 : ℝ) ^ n * sourceFirstActivationSignedAmplitude ell n := by
  unfold sourceFirstActivationRadiusCoefficient
    sourceFirstActivationSignedAmplitude
  rw [normalizedCentralBinom_succ_eq_ratio, pow_succ]
  ring

/-- Natural scale `n^(2ℓ+1/2)` of the first activation at Euler degree `2ℓ+1`. -/
def sourceFirstActivationScale (ell n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ (2 * ell) * Real.sqrt ((n : ℝ) + 1)

/-- Sharp signed radius amplitude `-C_ℓL_ℓ²/√π`. -/
def sourceFirstActivationAmplitudeLimit (ell : ℕ) : ℝ :=
  -sourceHarmonicCoefficient ell *
    sourceActivationLeadingCoefficient ell ^ 2 /
      Real.sqrt Real.pi

private theorem sourceFirstActivationSignedAmplitude_div_scale
    (ell n : ℕ) :
    sourceFirstActivationSignedAmplitude ell n /
        sourceFirstActivationScale ell n =
      -(sourceHarmonicCoefficient ell / 2) *
        (semilocalArchimedeanJacobiCoefficient n / ((n : ℝ) + 1)) *
        (Real.sqrt ((n : ℝ) + 1) * normalizedCentralBinom n) *
        ((centralBinomRatio n * sourceActivationValue ell (n + 1) ^ 2 +
            sourceActivationValue ell n ^ 2) /
          ((n : ℝ) + 1) ^ (2 * ell)) := by
  unfold sourceFirstActivationSignedAmplitude sourceFirstActivationScale
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hsqrt : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by positivity
  have hsqrt_sq :
      Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 := by
    rw [Real.sq_sqrt]
    positivity
  field_simp [hn, hsqrt]
  rw [hsqrt_sq]

private theorem tendsto_sourceFirstActivationBracket (ell : ℕ) :
    Tendsto
      (fun n : ℕ =>
        (centralBinomRatio n * sourceActivationValue ell (n + 1) ^ 2 +
            sourceActivationValue ell n ^ 2) /
          ((n : ℝ) + 1) ^ (2 * ell))
      atTop
      (nhds (2 * sourceActivationLeadingCoefficient ell ^ 2)) := by
  have hq := tendsto_centralBinomRatio
  have hsucc := tendsto_sourceActivationValue_succ_div_pow ell
  have hbase := tendsto_sourceActivationValue_div_succ_pow ell
  have h :=
    hq.mul (hsucc.pow 2) |>.add (hbase.pow 2)
  convert h using 1
  · funext n
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    rw [show ((n : ℝ) + 1) ^ (2 * ell) =
        (((n : ℝ) + 1) ^ ell) ^ 2 by
      rw [← pow_mul]
      congr 1
      omega]
    field_simp [hn]
  · ring

theorem tendsto_sourceFirstActivationSignedAmplitude (ell : ℕ) :
    Tendsto
      (fun n : ℕ =>
        sourceFirstActivationSignedAmplitude ell n /
          sourceFirstActivationScale ell n)
      atTop (nhds (sourceFirstActivationAmplitudeLimit ell)) := by
  have hr :=
    tendsto_semilocalArchimedeanJacobiCoefficient_div_succ
  have hc := tendsto_sqrt_succ_mul_normalizedCentralBinom
  have hb := tendsto_sourceFirstActivationBracket ell
  have h :=
    ((hr.mul hc).mul hb).const_mul
      (-(sourceHarmonicCoefficient ell / 2))
  convert h using 1
  · funext n
    rw [sourceFirstActivationSignedAmplitude_div_scale]
    ring_nf
  · unfold sourceFirstActivationAmplitudeLimit
    ring_nf

/-- Sharp four-radius constant forced by two-step regular variation of the odd activation. -/
def sourceCriticalBoundaryConstant (ell : ℕ) : ℝ :=
  -(8 * (ell : ℝ) + 2) * sourceFirstActivationAmplitudeLimit ell

theorem sourceCriticalBoundaryConstant_zero :
    sourceCriticalBoundaryConstant 0 =
      2 * positiveEulerBoundaryAmplitude := by
  unfold sourceCriticalBoundaryConstant
    sourceFirstActivationAmplitudeLimit sourceHarmonicCoefficient
    sourceActivationLeadingCoefficient positiveEulerBoundaryAmplitude
    normalizedCentralBinom
  norm_num [Nat.centralBinom]
  ring

theorem sourceCriticalBoundaryConstant_one :
    sourceCriticalBoundaryConstant 1 =
      -10 * RHTower.ThirdEulerCriticalJet.thirdRadiusBoundaryAmplitude := by
  unfold sourceCriticalBoundaryConstant
    sourceFirstActivationAmplitudeLimit sourceHarmonicCoefficient
    sourceActivationLeadingCoefficient
    RHTower.ThirdEulerCriticalJet.thirdRadiusBoundaryAmplitude
    positiveEulerBoundaryAmplitude normalizedCentralBinom
  norm_num [Nat.centralBinom]
  ring

/-- Twice radius-growth weight of a `k`-fold trace monomial whose harmonic indices sum to `s`. -/
def sourceTraceTwiceRadiusWeight (s k : ℕ) : ℕ :=
  4 * s + k

/-- Minimal Euler degree of the same source trace monomial. -/
def sourceTraceMinimalEulerDegree (s k : ℕ) : ℕ :=
  2 * s + k

theorem sourceTraceTwiceRadiusWeight_eq
    (s k : ℕ) :
    sourceTraceTwiceRadiusWeight s k =
      2 * sourceTraceMinimalEulerDegree s k - k := by
  unfold sourceTraceTwiceRadiusWeight sourceTraceMinimalEulerDegree
  omega

/-- Interactions containing at least two source atoms miss odd top weight by at least one half. -/
theorem sourceTraceInteraction_weight_gap
    {d s k : ℕ} (hk : 2 ≤ k)
    (hdegree : sourceTraceMinimalEulerDegree s k ≤ d) :
    sourceTraceTwiceRadiusWeight s k ≤ 2 * d - 2 := by
  unfold sourceTraceTwiceRadiusWeight
    sourceTraceMinimalEulerDegree at *
  omega

/-- Odd top-weight equality forces one atom and no Lambert repetition. -/
theorem sourceTraceTopWeight_unique
    {d s k : ℕ} (hk : 1 ≤ k)
    (hdegree : sourceTraceMinimalEulerDegree s k ≤ d)
    (htop : sourceTraceTwiceRadiusWeight s k = 2 * d - 1) :
    k = 1 ∧ d = 2 * s + 1 := by
  unfold sourceTraceTwiceRadiusWeight
    sourceTraceMinimalEulerDegree at *
  omega

end RHTower.OddHarmonicActivation
