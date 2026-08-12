import GaloisForLFunctions.RHTower.HedenmalmThetaMobiusPoleUnitPrimeCellGammaWindowProvenance
import GaloisForLFunctions.RHTower.MobiusGammaCoPoissonPrimePowerBoundary
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Full squarefree Gamma/co-Poisson current of a Route-P prime cell

P-G48 cancels the grade-one harmonic charge but leaves a positive complement.  This module tests
whether all prime-power grades supply a new coercive remainder.  Weighting the existing primitive
Gamma/co-Poisson term at `p^(n+1)` by `(-1)^n` sums exactly to the squarefree local current
`-log(1 + p^-sigma)`.

At the three forced Route-P source rates, the full alternating current has no residual term: its
multiplicative second difference is exactly the logarithm of the literal squarefree prime-cell
Gram.  Thus higher prime-power depth closes the grade-one complement into a conservative
free-energy law; it does not by itself force saturation.  The final theorem retains every
prime-power label before summation.
-/

open Complex Filter Set Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Alternating prime-power lift of the existing primitive Gamma/co-Poisson source. -/
def squarefreeGammaCoPoissonPrimePowerTerm
    (p : Nat.Primes) (n : ℕ) (s : ℂ) : ℂ :=
  (-1 : ℂ) ^ n *
    RHTower.eulerGammaCoPoissonPrimitiveTerm ((p : ℕ) ^ (n + 1)) s

/-- Exact labeled value before any infinite summation. -/
theorem squarefreeGammaCoPoissonPrimePowerTerm_eq
    (p : Nat.Primes) (n : ℕ) (s : ℂ) :
    squarefreeGammaCoPoissonPrimePowerTerm p n s =
      (-1 : ℂ) ^ (n + 1) * (((n + 1 : ℕ) : ℂ)⁻¹) *
        LSeries.term (fun _ => (1 : ℂ)) s ((p : ℕ) ^ (n + 1)) := by
  rw [squarefreeGammaCoPoissonPrimePowerTerm,
    RHTower.eulerGammaCoPoissonPrimitiveTerm_prime_pow p.prop
      (Nat.succ_ne_zero n) s]
  ring

/-- Real-rate value of the constant Dirichlet monomial at a prime power. -/
theorem one_LSeries_term_prime_pow_real
    (p k : ℕ) (sigma : ℝ) (hp : 0 < p) :
    LSeries.term (fun _ => (1 : ℂ)) (sigma : ℂ) (p ^ k) =
      (((p : ℝ) ^ (-sigma)) ^ k : ℝ) := by
  rw [LSeries.term_of_ne_zero (pow_ne_zero k (Nat.ne_of_gt hp))]
  simp only [one_div]
  rw [← Complex.cpow_neg]
  rw [show (((p ^ k : ℕ) : ℂ)) = ((((p ^ k : ℕ) : ℝ) : ℂ)) by norm_num]
  rw [← Complex.ofReal_neg]
  rw [← Complex.ofReal_cpow (by positivity)]
  congr 1
  rw [Nat.cast_pow]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by positivity)]
  rw [← Real.rpow_natCast ((p : ℝ) ^ (-sigma)) k]
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- The alternating primitive prime-power series sums to the negative squarefree local log. -/
theorem hasSum_squarefreeGammaCoPoissonPrimePowerTerm_real
    (p : Nat.Primes) {sigma : ℝ} (hsigma : 0 < sigma) :
    HasSum (fun n : ℕ => squarefreeGammaCoPoissonPrimePowerTerm p n (sigma : ℂ))
      (-(Real.log (1 + (p : ℝ) ^ (-sigma))) : ℝ) := by
  let a : ℝ := (p : ℝ) ^ (-sigma)
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have ha0 : 0 < a := Real.rpow_pos_of_pos (lt_trans zero_lt_one hp) _
  have ha1 : a < 1 := by
    dsimp [a]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos hsigma)
  have hreal := Real.hasSum_pow_div_log_of_abs_lt_one
    (x := -a) (by rw [abs_neg, abs_of_pos ha0]; exact ha1)
  have hcast : HasSum
      (fun n : ℕ => ((((-a) ^ (n + 1) / (n + 1)) : ℝ) : ℂ))
      (((-Real.log (1 - (-a))) : ℝ) : ℂ) := by
    convert hreal.map (Complex.ofRealCLM : ℝ →L[ℝ] ℂ)
        Complex.ofRealCLM.continuous using 1 <;>
      simp [Function.comp_def]
  have hterms : ∀ n : ℕ,
      squarefreeGammaCoPoissonPrimePowerTerm p n (sigma : ℂ) =
        ((((-a) ^ (n + 1) / (n + 1)) : ℝ) : ℂ) := by
    intro n
    rw [squarefreeGammaCoPoissonPrimePowerTerm_eq,
      one_LSeries_term_prime_pow_real (p : ℕ) (n + 1) sigma p.prop.pos]
    simp only [Nat.cast_add, Nat.cast_one, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_neg]
    push_cast
    dsimp [a]
    ring
  have hsum := hcast.congr_fun hterms
  simpa [a] using hsum

/-- Squarefree local Gamma/co-Poisson current. -/
def squarefreeGammaCoPoissonPrimeCurrent (p : Nat.Primes) (sigma : ℝ) : ℝ :=
  -Real.log (1 + (p : ℝ) ^ (-sigma))

theorem hasSum_squarefreeGammaCoPoissonPrimePowerTerm
    (p : Nat.Primes) {sigma : ℝ} (hsigma : 0 < sigma) :
    HasSum (fun n : ℕ => squarefreeGammaCoPoissonPrimePowerTerm p n (sigma : ℂ))
      (squarefreeGammaCoPoissonPrimeCurrent p sigma : ℝ) := by
  simpa [squarefreeGammaCoPoissonPrimeCurrent] using
    hasSum_squarefreeGammaCoPoissonPrimePowerTerm_real p hsigma

/-- Abstract free-energy law behind every Bernoulli midpoint cell. -/
theorem log_bernoulliMidpointGramSq_eq_squarefreeCurrentSecondDifference
    {A T : ℝ} (hA : 0 < A) (hT : 0 < T) :
    Real.log (bernoulliMidpointGramSq A T) =
      -Real.log (1 + A * T) - Real.log (1 + A / T) +
        2 * Real.log (1 + A) := by
  have hAT : 0 < 1 + A * T := by positivity
  have hAdT : 0 < 1 + A / T := by positivity
  have hA1 : 0 < 1 + A := by positivity
  rw [bernoulliMidpointGramSq,
    Real.log_div (pow_ne_zero 2 hA1.ne') (mul_ne_zero hAT.ne' hAdT.ne'),
    Real.log_pow, Real.log_mul hAT.ne' hAdT.ne']
  ring

/-- **Full-depth local source identity.**  The logarithm of a literal squarefree Route-P prime
cell is exactly the second difference of the full alternating primitive Gamma/co-Poisson current. -/
theorem log_squarefreeMobiusPrimeCellGramSq_eq_squarefreeGammaCoPoissonSecondDifference
    (p : Nat.Primes) (epsilon x z : ℝ) :
    Real.log (squarefreeMobiusPrimeCellGramSq p epsilon x z) =
      squarefreeGammaCoPoissonPrimeCurrent p (1 + x * epsilon) +
        squarefreeGammaCoPoissonPrimeCurrent p (1 + z * epsilon) -
          2 * squarefreeGammaCoPoissonPrimeCurrent p
            (1 + ((x + z) / 2) * epsilon) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hx : 0 < 1 + (p : ℝ) ^ (-(1 + x * epsilon)) := by positivity
  have hz : 0 < 1 + (p : ℝ) ^ (-(1 + z * epsilon)) := by positivity
  have hy : 0 < 1 + (p : ℝ) ^ (-(1 + ((x + z) / 2) * epsilon)) := by positivity
  rw [squarefreeMobiusPrimeCellGramSq]
  simp only [squarefreeGammaCoPoissonPrimeCurrent]
  rw [Real.log_div (pow_ne_zero 2 hy.ne') (mul_ne_zero hx.ne' hz.ne'),
    Real.log_pow, Real.log_mul hx.ne' hz.ne']
  ring

/-- Labeled prime-power source whose sum is the full squarefree second difference. -/
def squarefreeGammaCoPoissonPrimePowerSecondDifferenceTerm
    (p : Nat.Primes) (n : ℕ) (epsilon x z : ℝ) : ℂ :=
  squarefreeGammaCoPoissonPrimePowerTerm p n ((1 + x * epsilon : ℝ) : ℂ) +
    squarefreeGammaCoPoissonPrimePowerTerm p n ((1 + z * epsilon : ℝ) : ℂ) -
      2 * squarefreeGammaCoPoissonPrimePowerTerm p n
        ((1 + ((x + z) / 2) * epsilon : ℝ) : ℂ)

/-- Every prime-power label survives until the final convergent second-difference sum. -/
theorem hasSum_squarefreeGammaCoPoissonPrimePowerSecondDifferenceTerm
    (p : Nat.Primes) {epsilon x z : ℝ}
    (hx : 0 < 1 + x * epsilon) (hz : 0 < 1 + z * epsilon)
    (hy : 0 < 1 + ((x + z) / 2) * epsilon) :
    HasSum
      (fun n : ℕ => squarefreeGammaCoPoissonPrimePowerSecondDifferenceTerm
        p n epsilon x z)
      (Real.log (squarefreeMobiusPrimeCellGramSq p epsilon x z) : ℝ) := by
  have hsx := hasSum_squarefreeGammaCoPoissonPrimePowerTerm p hx
  have hsz := hasSum_squarefreeGammaCoPoissonPrimePowerTerm p hz
  have hsy := hasSum_squarefreeGammaCoPoissonPrimePowerTerm p hy
  have hsum := (hsx.add hsz).sub (hsy.mul_left (2 : ℂ))
  have hlog :=
    log_squarefreeMobiusPrimeCellGramSq_eq_squarefreeGammaCoPoissonSecondDifference
      p epsilon x z
  simpa [squarefreeGammaCoPoissonPrimePowerSecondDifferenceTerm, hlog] using hsum

end

end RHTower.HedenmalmThetaSource
