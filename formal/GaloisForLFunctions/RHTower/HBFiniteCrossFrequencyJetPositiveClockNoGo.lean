import GaloisForLFunctions.RHTower.HBFiniteCrossFrequencyCausalSchwarzAllPassNoGo
import GaloisForLFunctions.HTGeometry.ShiftedEulerTangentFiltration
import GaloisForLFunctions.HTGeometry.PolynomialSmoothApproximation

/-!
# Finite multipoint analytic jets do not identify HB all-pass phase

For every finite real frequency packet and every finite jet depth, this module constructs two
explicit, distinct entire zero-free responses with unit boundary modulus, exact FE--Schwarz
symmetry, and strictly positive boundary log-derivative clocks. Their analytic jets agree through
the prescribed depth at every sampled frequency.

Consequently, finite-depth local source data cannot supply the phase-identification arrow needed
by the current HB source-to-Ward route. The theorem deliberately does not address bounded
Hardy/Schur classes, infinite uniqueness sets, external bilocal phase references, or literal
source-derived global minimum-phase/winding hypotheses.
-/

open Complex Real Polynomial Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

def finiteJetOddFlatPolynomial (s : Finset ℝ) (N : ℕ) : Polynomial ℝ :=
  X * ∏ a ∈ s, (X ^ (2 : ℕ) - C (a ^ (2 : ℕ))) ^ (N + 1)

theorem evalRealPolynomial_finiteJetOddFlatPolynomial (s : Finset ℝ) (N : ℕ) (z : ℂ) :
    evalRealPolynomial (finiteJetOddFlatPolynomial s N) z =
      z * ∏ a ∈ s, (z ^ (2 : ℕ) - (a : ℂ) ^ (2 : ℕ)) ^ (N + 1) := by
  simp [finiteJetOddFlatPolynomial, evalRealPolynomial]

theorem evalRealPolynomial_finiteJetOddFlatPolynomial_neg
    (s : Finset ℝ) (N : ℕ) (z : ℂ) :
    evalRealPolynomial (finiteJetOddFlatPolynomial s N) (-z) =
      -evalRealPolynomial (finiteJetOddFlatPolynomial s N) z := by
  rw [evalRealPolynomial_finiteJetOddFlatPolynomial,
    evalRealPolynomial_finiteJetOddFlatPolynomial]
  simp only [neg_sq]
  ring

theorem evalRealPolynomial_derivative_finiteJetOddFlatPolynomial_neg
    (s : Finset ℝ) (N : ℕ) (z : ℂ) :
    evalRealPolynomial (derivative (finiteJetOddFlatPolynomial s N)) (-z) =
      evalRealPolynomial (derivative (finiteJetOddFlatPolynomial s N)) z := by
  let H := finiteJetOddFlatPolynomial s N
  have hleft := (hasDerivAt_evalRealPolynomial H (-z)).comp z (hasDerivAt_neg z)
  have hleft' :
      HasDerivAt (fun w : ℂ => evalRealPolynomial H (-w))
        (-evalRealPolynomial (derivative H) (-z)) z := by
    simpa [Function.comp_def] using hleft
  have hright' :
      HasDerivAt (fun w : ℂ => -evalRealPolynomial H w)
        (-evalRealPolynomial (derivative H) z) z := by
    exact (hasDerivAt_evalRealPolynomial H z).fun_neg
  have heq : (fun w : ℂ => evalRealPolynomial H (-w)) =
      fun w : ℂ => -evalRealPolynomial H w := by
    funext w
    exact evalRealPolynomial_finiteJetOddFlatPolynomial_neg s N w
  rw [heq] at hleft'
  exact neg_injective (hleft'.unique hright')

def finiteJetClockBasePolynomial (s : Finset ℝ) (N : ℕ) : Polynomial ℝ :=
  1 + derivative (finiteJetOddFlatPolynomial s N) ^ (2 : ℕ)

def finiteJetClockPrimitivePolynomial (s : Finset ℝ) (N : ℕ) : Polynomial ℝ :=
  Polynomial.realAntiderivative (finiteJetClockBasePolynomial s N)

def finiteJetOddClockPrimitive (s : Finset ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  (evalRealPolynomial (finiteJetClockPrimitivePolynomial s N) z -
    evalRealPolynomial (finiteJetClockPrimitivePolynomial s N) (-z)) / 2

def finiteJetPositivePhasePlus (s : Finset ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  finiteJetOddClockPrimitive s N z + evalRealPolynomial (finiteJetOddFlatPolynomial s N) z

def finiteJetPositivePhaseMinus (s : Finset ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  finiteJetOddClockPrimitive s N z - evalRealPolynomial (finiteJetOddFlatPolynomial s N) z

def finiteJetPositiveClockAllPassPlus (s : Finset ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (I * finiteJetPositivePhasePlus s N z)

def finiteJetPositiveClockAllPassMinus (s : Finset ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (I * finiteJetPositivePhaseMinus s N z)

theorem finiteJetOddClockPrimitive_neg (s : Finset ℝ) (N : ℕ) (z : ℂ) :
    finiteJetOddClockPrimitive s N (-z) = -finiteJetOddClockPrimitive s N z := by
  simp [finiteJetOddClockPrimitive]
  ring

theorem finiteJetPositivePhasePlus_neg (s : Finset ℝ) (N : ℕ) (z : ℂ) :
    finiteJetPositivePhasePlus s N (-z) = -finiteJetPositivePhasePlus s N z := by
  rw [finiteJetPositivePhasePlus, finiteJetOddClockPrimitive_neg,
    evalRealPolynomial_finiteJetOddFlatPolynomial_neg]
  simp only [finiteJetPositivePhasePlus]
  ring

theorem finiteJetPositivePhaseMinus_neg (s : Finset ℝ) (N : ℕ) (z : ℂ) :
    finiteJetPositivePhaseMinus s N (-z) = -finiteJetPositivePhaseMinus s N z := by
  rw [finiteJetPositivePhaseMinus, finiteJetOddClockPrimitive_neg,
    evalRealPolynomial_finiteJetOddFlatPolynomial_neg]
  simp only [finiteJetPositivePhaseMinus]
  ring

theorem finiteJetOddClockPrimitive_conj (s : Finset ℝ) (N : ℕ) (z : ℂ) :
    finiteJetOddClockPrimitive s N ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (finiteJetOddClockPrimitive s N z) := by
  change (evalRealPolynomial (finiteJetClockPrimitivePolynomial s N) ((starRingEnd ℂ) z) -
    evalRealPolynomial (finiteJetClockPrimitivePolynomial s N) (-((starRingEnd ℂ) z))) / 2 =
    (starRingEnd ℂ) ((evalRealPolynomial (finiteJetClockPrimitivePolynomial s N) z -
      evalRealPolynomial (finiteJetClockPrimitivePolynomial s N) (-z)) / 2)
  rw [evalRealPolynomial_conj]
  have hneg : -((starRingEnd ℂ) z) = (starRingEnd ℂ) (-z) := by simp
  rw [hneg, evalRealPolynomial_conj]
  simp only [map_div₀, map_sub]
  rw [map_ofNat]

theorem finiteJetPositivePhasePlus_conj (s : Finset ℝ) (N : ℕ) (z : ℂ) :
    finiteJetPositivePhasePlus s N ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (finiteJetPositivePhasePlus s N z) := by
  change finiteJetOddClockPrimitive s N ((starRingEnd ℂ) z) +
    evalRealPolynomial (finiteJetOddFlatPolynomial s N) ((starRingEnd ℂ) z) =
    (starRingEnd ℂ) (finiteJetPositivePhasePlus s N z)
  rw [finiteJetOddClockPrimitive_conj, evalRealPolynomial_conj]
  simp only [finiteJetPositivePhasePlus, map_add]

theorem finiteJetPositivePhaseMinus_conj (s : Finset ℝ) (N : ℕ) (z : ℂ) :
    finiteJetPositivePhaseMinus s N ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (finiteJetPositivePhaseMinus s N z) := by
  change finiteJetOddClockPrimitive s N ((starRingEnd ℂ) z) -
    evalRealPolynomial (finiteJetOddFlatPolynomial s N) ((starRingEnd ℂ) z) =
    (starRingEnd ℂ) (finiteJetPositivePhaseMinus s N z)
  rw [finiteJetOddClockPrimitive_conj, evalRealPolynomial_conj]
  simp only [finiteJetPositivePhaseMinus, map_sub]

theorem finiteJetPositiveClockAllPassPlus_neg_star (s : Finset ℝ) (N : ℕ) (z : ℂ) :
    finiteJetPositiveClockAllPassPlus s N (-((starRingEnd ℂ) z)) =
      (starRingEnd ℂ) (finiteJetPositiveClockAllPassPlus s N z) := by
  rw [finiteJetPositiveClockAllPassPlus, finiteJetPositivePhasePlus_neg,
    finiteJetPositivePhasePlus_conj]
  change Complex.exp (I * -((starRingEnd ℂ) (finiteJetPositivePhasePlus s N z))) =
    (starRingEnd ℂ) (Complex.exp (I * finiteJetPositivePhasePlus s N z))
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem finiteJetPositiveClockAllPassMinus_neg_star (s : Finset ℝ) (N : ℕ) (z : ℂ) :
    finiteJetPositiveClockAllPassMinus s N (-((starRingEnd ℂ) z)) =
      (starRingEnd ℂ) (finiteJetPositiveClockAllPassMinus s N z) := by
  rw [finiteJetPositiveClockAllPassMinus, finiteJetPositivePhaseMinus_neg,
    finiteJetPositivePhaseMinus_conj]
  change Complex.exp (I * -((starRingEnd ℂ) (finiteJetPositivePhaseMinus s N z))) =
    (starRingEnd ℂ) (Complex.exp (I * finiteJetPositivePhaseMinus s N z))
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem hasDerivAt_finiteJetOddClockPrimitive (s : Finset ℝ) (N : ℕ) (z : ℂ) :
    HasDerivAt (finiteJetOddClockPrimitive s N)
      (evalRealPolynomial (finiteJetClockBasePolynomial s N) z) z := by
  let K := finiteJetClockPrimitivePolynomial s N
  let Q := finiteJetClockBasePolynomial s N
  have hK : derivative K = Q := by
    simp [K, Q, finiteJetClockPrimitivePolynomial, Polynomial.derivative_realAntiderivative]
  have hpos := hasDerivAt_evalRealPolynomial K z
  have hneg0 := (hasDerivAt_evalRealPolynomial K (-z)).comp z (hasDerivAt_neg z)
  have hneg : HasDerivAt (fun w : ℂ => evalRealPolynomial K (-w))
      (-evalRealPolynomial Q (-z)) z := by
    rw [hK] at hneg0
    simpa [Function.comp_def] using hneg0
  have hsub := hpos.fun_sub hneg
  rw [hK] at hsub
  have hQneg : evalRealPolynomial Q (-z) = evalRealPolynomial Q z := by
    simp only [Q, finiteJetClockBasePolynomial, evalRealPolynomial_add_local,
      evalRealPolynomial_one, evalRealPolynomial_pow]
    rw [evalRealPolynomial_derivative_finiteJetOddFlatPolynomial_neg]
  have hdiv := hsub.div_const (2 : ℂ)
  change HasDerivAt (fun w : ℂ =>
    (evalRealPolynomial (finiteJetClockPrimitivePolynomial s N) w -
      evalRealPolynomial (finiteJetClockPrimitivePolynomial s N) (-w)) / 2)
    (evalRealPolynomial (finiteJetClockBasePolynomial s N) z) z
  simpa [K, Q, hQneg] using hdiv

theorem hasDerivAt_finiteJetPositivePhasePlus (s : Finset ℝ) (N : ℕ) (z : ℂ) :
    HasDerivAt (finiteJetPositivePhasePlus s N)
      (evalRealPolynomial (finiteJetClockBasePolynomial s N) z +
        evalRealPolynomial (derivative (finiteJetOddFlatPolynomial s N)) z) z := by
  change HasDerivAt (fun w : ℂ => finiteJetOddClockPrimitive s N w +
    evalRealPolynomial (finiteJetOddFlatPolynomial s N) w) _ z
  exact (hasDerivAt_finiteJetOddClockPrimitive s N z).fun_add
    (hasDerivAt_evalRealPolynomial (finiteJetOddFlatPolynomial s N) z)

theorem hasDerivAt_finiteJetPositivePhaseMinus (s : Finset ℝ) (N : ℕ) (z : ℂ) :
    HasDerivAt (finiteJetPositivePhaseMinus s N)
      (evalRealPolynomial (finiteJetClockBasePolynomial s N) z -
        evalRealPolynomial (derivative (finiteJetOddFlatPolynomial s N)) z) z := by
  change HasDerivAt (fun w : ℂ => finiteJetOddClockPrimitive s N w -
    evalRealPolynomial (finiteJetOddFlatPolynomial s N) w) _ z
  exact (hasDerivAt_finiteJetOddClockPrimitive s N z).fun_sub
    (hasDerivAt_evalRealPolynomial (finiteJetOddFlatPolynomial s N) z)

theorem analyticAt_finiteJetPositivePhasePlus (s : Finset ℝ) (N : ℕ) (z : ℂ) :
    AnalyticAt ℂ (finiteJetPositivePhasePlus s N) z := by
  apply GaloisForLFunctions.HTGeometry.analyticAt_of_differentiable_univariate
  exact fun w => (hasDerivAt_finiteJetPositivePhasePlus s N w).differentiableAt

theorem analyticAt_finiteJetPositivePhaseMinus (s : Finset ℝ) (N : ℕ) (z : ℂ) :
    AnalyticAt ℂ (finiteJetPositivePhaseMinus s N) z := by
  apply GaloisForLFunctions.HTGeometry.analyticAt_of_differentiable_univariate
  exact fun w => (hasDerivAt_finiteJetPositivePhaseMinus s N w).differentiableAt

theorem analyticAt_finiteJetPositiveClockAllPassPlus (s : Finset ℝ) (N : ℕ) (z : ℂ) :
    AnalyticAt ℂ (finiteJetPositiveClockAllPassPlus s N) z := by
  change AnalyticAt ℂ (fun w => Complex.exp (I * finiteJetPositivePhasePlus s N w)) z
  exact (analyticAt_const.mul (analyticAt_finiteJetPositivePhasePlus s N z)).cexp

theorem analyticAt_finiteJetPositiveClockAllPassMinus (s : Finset ℝ) (N : ℕ) (z : ℂ) :
    AnalyticAt ℂ (finiteJetPositiveClockAllPassMinus s N) z := by
  change AnalyticAt ℂ (fun w => Complex.exp (I * finiteJetPositivePhaseMinus s N w)) z
  exact (analyticAt_const.mul (analyticAt_finiteJetPositivePhaseMinus s N z)).cexp

theorem norm_finiteJetPositiveClockAllPassPlus (s : Finset ℝ) (N : ℕ) (x : ℝ) :
    ‖finiteJetPositiveClockAllPassPlus s N (x : ℂ)‖ = 1 := by
  rw [finiteJetPositiveClockAllPassPlus, Complex.norm_exp]
  have him : (finiteJetPositivePhasePlus s N (x : ℂ)).im = 0 := by
    have hneg : -((x : ℂ)) = ((-x : ℝ) : ℂ) := by norm_num
    rw [finiteJetPositivePhasePlus, finiteJetOddClockPrimitive, hneg,
      evalRealPolynomial_ofReal, evalRealPolynomial_ofReal, evalRealPolynomial_ofReal]
    norm_num
  rw [Complex.mul_re, him]
  norm_num

theorem norm_finiteJetPositiveClockAllPassMinus (s : Finset ℝ) (N : ℕ) (x : ℝ) :
    ‖finiteJetPositiveClockAllPassMinus s N (x : ℂ)‖ = 1 := by
  rw [finiteJetPositiveClockAllPassMinus, Complex.norm_exp]
  have him : (finiteJetPositivePhaseMinus s N (x : ℂ)).im = 0 := by
    have hneg : -((x : ℂ)) = ((-x : ℝ) : ℂ) := by norm_num
    rw [finiteJetPositivePhaseMinus, finiteJetOddClockPrimitive, hneg,
      evalRealPolynomial_ofReal, evalRealPolynomial_ofReal, evalRealPolynomial_ofReal]
    norm_num
  rw [Complex.mul_re, him]
  norm_num

def finiteJetPositiveClockAllPassPlusClock (s : Finset ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  (logDeriv (finiteJetPositiveClockAllPassPlus s N) (x : ℂ)).im

def finiteJetPositiveClockAllPassMinusClock (s : Finset ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  (logDeriv (finiteJetPositiveClockAllPassMinus s N) (x : ℂ)).im

theorem finiteJetPositiveClockAllPassPlusClock_eq (s : Finset ℝ) (N : ℕ) (x : ℝ) :
    finiteJetPositiveClockAllPassPlusClock s N x =
      1 + (derivative (finiteJetOddFlatPolynomial s N)).eval x ^ (2 : ℕ) +
        (derivative (finiteJetOddFlatPolynomial s N)).eval x := by
  let d : ℂ := evalRealPolynomial (finiteJetClockBasePolynomial s N) (x : ℂ) +
    evalRealPolynomial (derivative (finiteJetOddFlatPolynomial s N)) (x : ℂ)
  have hphase := hasDerivAt_finiteJetPositivePhasePlus s N (x : ℂ)
  have hexp := ((hphase.const_mul I).cexp)
  have hresp : HasDerivAt (finiteJetPositiveClockAllPassPlus s N)
      (finiteJetPositiveClockAllPassPlus s N (x : ℂ) * (I * d)) (x : ℂ) := by
    change HasDerivAt (fun w => Complex.exp (I * finiteJetPositivePhasePlus s N w))
      (Complex.exp (I * finiteJetPositivePhasePlus s N (x : ℂ)) * (I * d)) (x : ℂ)
    simpa [d] using hexp
  rw [finiteJetPositiveClockAllPassPlusClock, logDeriv_apply, hresp.deriv]
  have hne : finiteJetPositiveClockAllPassPlus s N (x : ℂ) ≠ 0 := by
    exact Complex.exp_ne_zero _
  have hcancel : finiteJetPositiveClockAllPassPlus s N (x : ℂ) * (I * d) /
      finiteJetPositiveClockAllPassPlus s N (x : ℂ) = I * d := by
    field_simp
  rw [hcancel]
  simp only [d, finiteJetClockBasePolynomial, evalRealPolynomial_ofReal]
  norm_num [pow_two]

theorem finiteJetPositiveClockAllPassMinusClock_eq (s : Finset ℝ) (N : ℕ) (x : ℝ) :
    finiteJetPositiveClockAllPassMinusClock s N x =
      1 + (derivative (finiteJetOddFlatPolynomial s N)).eval x ^ (2 : ℕ) -
        (derivative (finiteJetOddFlatPolynomial s N)).eval x := by
  let d : ℂ := evalRealPolynomial (finiteJetClockBasePolynomial s N) (x : ℂ) -
    evalRealPolynomial (derivative (finiteJetOddFlatPolynomial s N)) (x : ℂ)
  have hphase := hasDerivAt_finiteJetPositivePhaseMinus s N (x : ℂ)
  have hexp := ((hphase.const_mul I).cexp)
  have hresp : HasDerivAt (finiteJetPositiveClockAllPassMinus s N)
      (finiteJetPositiveClockAllPassMinus s N (x : ℂ) * (I * d)) (x : ℂ) := by
    change HasDerivAt (fun w => Complex.exp (I * finiteJetPositivePhaseMinus s N w))
      (Complex.exp (I * finiteJetPositivePhaseMinus s N (x : ℂ)) * (I * d)) (x : ℂ)
    simpa [d] using hexp
  rw [finiteJetPositiveClockAllPassMinusClock, logDeriv_apply, hresp.deriv]
  have hne : finiteJetPositiveClockAllPassMinus s N (x : ℂ) ≠ 0 := by
    exact Complex.exp_ne_zero _
  have hcancel : finiteJetPositiveClockAllPassMinus s N (x : ℂ) * (I * d) /
      finiteJetPositiveClockAllPassMinus s N (x : ℂ) = I * d := by
    field_simp
  rw [hcancel]
  simp only [d, finiteJetClockBasePolynomial, evalRealPolynomial_ofReal]
  norm_num [pow_two]

theorem finiteJetPositiveClockAllPassPlusClock_pos (s : Finset ℝ) (N : ℕ) (x : ℝ) :
    0 < finiteJetPositiveClockAllPassPlusClock s N x := by
  rw [finiteJetPositiveClockAllPassPlusClock_eq]
  nlinarith [sq_nonneg ((derivative (finiteJetOddFlatPolynomial s N)).eval x + 1 / 2)]

theorem finiteJetPositiveClockAllPassMinusClock_pos (s : Finset ℝ) (N : ℕ) (x : ℝ) :
    0 < finiteJetPositiveClockAllPassMinusClock s N x := by
  rw [finiteJetPositiveClockAllPassMinusClock_eq]
  nlinarith [sq_nonneg ((derivative (finiteJetOddFlatPolynomial s N)).eval x - 1 / 2)]

def finiteJetOddFlatUnit (s : Finset ℝ) (N : ℕ) (a : ℝ) (z : ℂ) : ℂ :=
  ((a : ℂ) + z) * (2 * (a : ℂ) + z) ^ (N + 1) *
    ∏ b ∈ s.erase a, (((a : ℂ) + z) ^ (2 : ℕ) - (b : ℂ) ^ (2 : ℕ)) ^ (N + 1)

theorem evalRealPolynomial_finiteJetOddFlatPolynomial_shift_factorization
    (s : Finset ℝ) (N : ℕ) {a : ℝ} (ha : a ∈ s) (z : ℂ) :
    evalRealPolynomial (finiteJetOddFlatPolynomial s N) ((a : ℂ) + z) =
      z ^ (N + 1) * finiteJetOddFlatUnit s N a z := by
  rw [evalRealPolynomial_finiteJetOddFlatPolynomial]
  rw [← Finset.prod_erase_mul _ _ ha]
  unfold finiteJetOddFlatUnit
  have hfactor : (((a : ℂ) + z) ^ (2 : ℕ) - (a : ℂ) ^ (2 : ℕ)) ^ (N + 1) =
      z ^ (N + 1) * (2 * (a : ℂ) + z) ^ (N + 1) := by
    rw [show ((a : ℂ) + z) ^ (2 : ℕ) - (a : ℂ) ^ (2 : ℕ) = z * (2 * (a : ℂ) + z) by ring,
      mul_pow]
  rw [hfactor]
  ring

theorem analyticAt_finiteJetOddFlatUnit (s : Finset ℝ) (N : ℕ) (a : ℝ) (z : ℂ) :
    AnalyticAt ℂ (finiteJetOddFlatUnit s N a) z := by
  unfold finiteJetOddFlatUnit
  fun_prop

theorem finiteJetPositivePhase_shift_sub_eq_flat
    (s : Finset ℝ) (N : ℕ) {a : ℝ} (ha : a ∈ s) (z : ℂ) :
    I * finiteJetPositivePhasePlus s N ((a : ℂ) + z) -
        I * finiteJetPositivePhaseMinus s N ((a : ℂ) + z) =
      z ^ (N + 1) * (2 * I * finiteJetOddFlatUnit s N a z) := by
  rw [finiteJetPositivePhasePlus, finiteJetPositivePhaseMinus,
    evalRealPolynomial_finiteJetOddFlatPolynomial_shift_factorization s N ha]
  ring

/-- Every finite analytic jet at every sampled frequency agrees for the two positive-clock
Schwarz all-pass responses. -/
theorem finiteJetPositiveClockAllPass_pair_iteratedDeriv_eq
    (s : Finset ℝ) (N : ℕ) {a : ℝ} (ha : a ∈ s) {j : ℕ} (hj : j ≤ N) :
    iteratedDeriv j (finiteJetPositiveClockAllPassPlus s N) (a : ℂ) =
      iteratedDeriv j (finiteJetPositiveClockAllPassMinus s N) (a : ℂ) := by
  let Lp : ℂ → ℂ := fun z => I * finiteJetPositivePhasePlus s N ((a : ℂ) + z)
  let Lm : ℂ → ℂ := fun z => I * finiteJetPositivePhaseMinus s N ((a : ℂ) + z)
  let W : ℂ → ℂ := fun z => 2 * I * finiteJetOddFlatUnit s N a z
  have hLp : ∀ z : ℂ, AnalyticAt ℂ Lp z := by
    intro z
    exact analyticAt_const.mul ((analyticAt_finiteJetPositivePhasePlus s N ((a : ℂ) + z)).comp
      (analyticAt_const.add analyticAt_id))
  have hLm : ∀ z : ℂ, AnalyticAt ℂ Lm z := by
    intro z
    exact analyticAt_const.mul ((analyticAt_finiteJetPositivePhaseMinus s N ((a : ℂ) + z)).comp
      (analyticAt_const.add analyticAt_id))
  have hW : AnalyticAt ℂ W 0 := by
    exact analyticAt_const.mul (analyticAt_finiteJetOddFlatUnit s N a 0)
  have hflat : ∀ᶠ z in 𝓝 (0 : ℂ), Lp z - Lm z = z ^ (N + 1) * W z := by
    filter_upwards [] with z
    exact finiteJetPositivePhase_shift_sub_eq_flat s N ha z
  have hjet := GaloisForLFunctions.HTGeometry.iteratedDeriv_exp_congr_of_flat
    hLp hLm hW hflat hj
  have hplusShift := GaloisForLFunctions.HTGeometry.iteratedDeriv_comp_const_add j
    (G := finiteJetPositiveClockAllPassPlus s N)
    (fun z => analyticAt_finiteJetPositiveClockAllPassPlus s N z) (a : ℂ) 0
  have hminusShift := GaloisForLFunctions.HTGeometry.iteratedDeriv_comp_const_add j
    (G := finiteJetPositiveClockAllPassMinus s N)
    (fun z => analyticAt_finiteJetPositiveClockAllPassMinus s N z) (a : ℂ) 0
  change iteratedDeriv j (fun z => finiteJetPositiveClockAllPassPlus s N ((a : ℂ) + z)) 0 =
    iteratedDeriv j (finiteJetPositiveClockAllPassPlus s N) ((a : ℂ) + 0) at hplusShift
  change iteratedDeriv j (fun z => finiteJetPositiveClockAllPassMinus s N ((a : ℂ) + z)) 0 =
    iteratedDeriv j (finiteJetPositiveClockAllPassMinus s N) ((a : ℂ) + 0) at hminusShift
  change iteratedDeriv j (fun z => finiteJetPositiveClockAllPassPlus s N ((a : ℂ) + z)) 0 =
    iteratedDeriv j (fun z => finiteJetPositiveClockAllPassMinus s N ((a : ℂ) + z)) 0 at hjet
  have hplusShift' : iteratedDeriv j
      (fun z => finiteJetPositiveClockAllPassPlus s N ((a : ℂ) + z)) 0 =
      iteratedDeriv j (finiteJetPositiveClockAllPassPlus s N) (a : ℂ) := by
    simpa using hplusShift
  have hminusShift' : iteratedDeriv j
      (fun z => finiteJetPositiveClockAllPassMinus s N ((a : ℂ) + z)) 0 =
      iteratedDeriv j (finiteJetPositiveClockAllPassMinus s N) (a : ℂ) := by
    simpa using hminusShift
  rw [← hplusShift', ← hminusShift']
  exact hjet

theorem monic_finiteJetOddFlatPolynomial (s : Finset ℝ) (N : ℕ) :
    (finiteJetOddFlatPolynomial s N).Monic := by
  classical
  unfold finiteJetOddFlatPolynomial
  apply monic_X.mul
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact ((monic_X_pow_sub_C (a ^ (2 : ℕ)) (by omega)).pow (N + 1)).mul ih

theorem finiteJetOddFlatPolynomial_ne_one (s : Finset ℝ) (N : ℕ) :
    finiteJetOddFlatPolynomial s N ≠ 1 := by
  intro h
  have heval := congrArg (fun p : Polynomial ℝ => p.eval 0) h
  simp [finiteJetOddFlatPolynomial] at heval

theorem derivative_finiteJetOddFlatPolynomial_ne_zero (s : Finset ℝ) (N : ℕ) :
    derivative (finiteJetOddFlatPolynomial s N) ≠ 0 := by
  rw [Polynomial.derivative_ne_zero]
  exact Nat.ne_of_gt ((monic_finiteJetOddFlatPolynomial s N).natDegree_pos.mpr
    (finiteJetOddFlatPolynomial_ne_one s N))

theorem exists_finiteJetOddFlatPolynomial_derivative_eval_ne_zero
    (s : Finset ℝ) (N : ℕ) :
    ∃ x : ℝ, (derivative (finiteJetOddFlatPolynomial s N)).eval x ≠ 0 := by
  let Q := derivative (finiteJetOddFlatPolynomial s N)
  have hQ : Q ≠ 0 := derivative_finiteJetOddFlatPolynomial_ne_zero s N
  by_contra h
  push Not at h
  have hroots : {x : ℝ | Q.IsRoot x} = Set.univ := by
    ext x
    have hx : Q.eval x = 0 := by
      simpa [Q] using h x
    simp [Polynomial.IsRoot, hx]
  apply hQ
  apply Polynomial.eq_zero_of_infinite_isRoot Q
  rw [hroots]
  exact Set.infinite_univ

theorem finiteJetPositiveClockAllPass_pair_ne (s : Finset ℝ) (N : ℕ) :
    finiteJetPositiveClockAllPassPlus s N ≠ finiteJetPositiveClockAllPassMinus s N := by
  obtain ⟨x, hx⟩ := exists_finiteJetOddFlatPolynomial_derivative_eval_ne_zero s N
  intro heq
  have hclock := congrArg
    (fun A : ℂ → ℂ => (logDeriv A (x : ℂ)).im) heq
  change finiteJetPositiveClockAllPassPlusClock s N x =
    finiteJetPositiveClockAllPassMinusClock s N x at hclock
  rw [finiteJetPositiveClockAllPassPlusClock_eq,
    finiteJetPositiveClockAllPassMinusClock_eq] at hclock
  have hzero : (derivative (finiteJetOddFlatPolynomial s N)).eval x = 0 := by
    linarith
  exact hx hzero

/-- Finite multipoint analytic-jet identifiability asserted by the killed HB producer class. -/
def HBFiniteCrossFrequencyJetAllPassUnique (s : Finset ℝ) (N : ℕ) : Prop :=
  ∀ A B : ℂ → ℂ,
    DifferentiableOn ℂ A {z : ℂ | 0 < z.im} →
    DifferentiableOn ℂ B {z : ℂ | 0 < z.im} →
    (∀ x : ℝ, ‖A (x : ℂ)‖ = 1) →
    (∀ x : ℝ, ‖B (x : ℂ)‖ = 1) →
    (∀ z : ℂ, A (-((starRingEnd ℂ) z)) = (starRingEnd ℂ) (A z)) →
    (∀ z : ℂ, B (-((starRingEnd ℂ) z)) = (starRingEnd ℂ) (B z)) →
    (∀ x : ℝ, 0 < (logDeriv A (x : ℂ)).im) →
    (∀ x : ℝ, 0 < (logDeriv B (x : ℂ)).im) →
    (∀ x ∈ s, ∀ j ≤ N,
      iteratedDeriv j A (x : ℂ) = iteratedDeriv j B (x : ℂ)) →
    A = B

/-- Strong obstruction: arbitrary finite multipoint jets are shared by two distinct entire,
zero-free, causal Schwarz all-pass responses whose boundary clocks are positive everywhere. -/
theorem exists_finiteJetSchwarzPositiveClockAllPass_pair
    (s : Finset ℝ) (N : ℕ) :
    ∃ A B : ℂ → ℂ,
      (∀ z : ℂ, AnalyticAt ℂ A z) ∧
      (∀ z : ℂ, AnalyticAt ℂ B z) ∧
      (∀ z : ℂ, A z ≠ 0) ∧
      (∀ z : ℂ, B z ≠ 0) ∧
      (∀ x : ℝ, ‖A (x : ℂ)‖ = 1) ∧
      (∀ x : ℝ, ‖B (x : ℂ)‖ = 1) ∧
      (∀ z : ℂ, A (-((starRingEnd ℂ) z)) = (starRingEnd ℂ) (A z)) ∧
      (∀ z : ℂ, B (-((starRingEnd ℂ) z)) = (starRingEnd ℂ) (B z)) ∧
      (∀ x : ℝ, 0 < (logDeriv A (x : ℂ)).im) ∧
      (∀ x : ℝ, 0 < (logDeriv B (x : ℂ)).im) ∧
      (∀ x ∈ s, ∀ j ≤ N,
        iteratedDeriv j A (x : ℂ) = iteratedDeriv j B (x : ℂ)) ∧
      A ≠ B := by
  refine ⟨finiteJetPositiveClockAllPassPlus s N,
    finiteJetPositiveClockAllPassMinus s N,
    analyticAt_finiteJetPositiveClockAllPassPlus s N,
    analyticAt_finiteJetPositiveClockAllPassMinus s N, ?_, ?_,
    norm_finiteJetPositiveClockAllPassPlus s N,
    norm_finiteJetPositiveClockAllPassMinus s N,
    finiteJetPositiveClockAllPassPlus_neg_star s N,
    finiteJetPositiveClockAllPassMinus_neg_star s N, ?_, ?_, ?_,
    finiteJetPositiveClockAllPass_pair_ne s N⟩
  · intro z
    exact Complex.exp_ne_zero _
  · intro z
    exact Complex.exp_ne_zero _
  · exact finiteJetPositiveClockAllPassPlusClock_pos s N
  · exact finiteJetPositiveClockAllPassMinusClock_pos s N
  · intro x hx j hj
    exact finiteJetPositiveClockAllPass_pair_iteratedDeriv_eq s N hx hj

/-- No finite packet of finite-depth analytic frequency jets identifies positive-clock Schwarz
all-pass phase in the current HB causal class. -/
theorem not_hbFiniteCrossFrequencyJetAllPassUnique (s : Finset ℝ) (N : ℕ) :
    ¬ HBFiniteCrossFrequencyJetAllPassUnique s N := by
  obtain ⟨A, B, hAanalytic, hBanalytic, _hAne0, _hBne0, hAnorm, hBnorm,
    hASchwarz, hBSchwarz, hAclock, hBclock, hjets, hne⟩ :=
      exists_finiteJetSchwarzPositiveClockAllPass_pair s N
  intro hunique
  apply hne
  exact hunique A B
    (fun z hz => (hAanalytic z).differentiableAt.differentiableWithinAt)
    (fun z hz => (hBanalytic z).differentiableAt.differentiableWithinAt)
    hAnorm hBnorm hASchwarz hBSchwarz hAclock hBclock hjets

end RHTower
