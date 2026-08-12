import GaloisForLFunctions.RHTower.HedenmalmThetaMobiusPoleUnitPrimeCellSquarefreeCurrent
import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicFockLocal

/-!
# Dyadic parity provenance of the Route-P squarefree prime cell

The corpus already proves probability/amplitude/Weyl factorization of a geometric exponent into
parity and residual valuation in `EulerSquarefreeDyadicFockLocal`.  P-G51 obtains the Route-P
squarefree current by alternating the existing primitive Gamma/co-Poisson prime-power source.  This
module welds those results: the sign is exactly the odd/even boundary of the full geometric
prime-valuation current.

The squarefree current is exactly the dyadic coboundary of the geometric current.  At Hellinger
level, full geometric affinity factors as parity affinity times the affinity of the discarded
halved valuation.  Data processing is strict unless the two source rates coincide.  Hence the
squarefree reporter is source-realized and has a sharp saturation condition, but the Markov law
does not force that condition.
-/

open Complex Filter Set Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Full geometric-valuation primitive source at a labeled prime-power depth. -/
def geometricGammaCoPoissonPrimePowerTerm
    (p : Nat.Primes) (n : ℕ) (s : ℂ) : ℂ :=
  RHTower.eulerGammaCoPoissonPrimitiveTerm ((p : ℕ) ^ (n + 1)) s

/-- Odd/even depth incidence on the full geometric primitive. -/
def geometricGammaCoPoissonParityBoundaryTerm
    (p : Nat.Primes) (n : ℕ) (s : ℂ) : ℂ :=
  geometricGammaCoPoissonPrimePowerTerm p n s -
    if Even (n + 1) then 2 * geometricGammaCoPoissonPrimePowerTerm p n s else 0

/-- P-G51's alternating source is exactly the valuation-parity boundary, label by label. -/
theorem squarefreeGammaCoPoissonPrimePowerTerm_eq_parityBoundary
    (p : Nat.Primes) (n : ℕ) (s : ℂ) :
    squarefreeGammaCoPoissonPrimePowerTerm p n s =
      geometricGammaCoPoissonParityBoundaryTerm p n s := by
  rw [squarefreeGammaCoPoissonPrimePowerTerm,
    geometricGammaCoPoissonParityBoundaryTerm,
    geometricGammaCoPoissonPrimePowerTerm, neg_one_pow_eq_ite]
  simp only [Nat.even_add_one]
  by_cases hn : Even n
  · simp [hn]
  · simp [hn]
    ring

/-- Log partition current of the full geometric prime-valuation source. -/
def geometricGammaCoPoissonPrimeCurrent (p : Nat.Primes) (sigma : ℝ) : ℝ :=
  Real.log (1 - (p : ℝ) ^ (-sigma))

/-- Existing unalternated primitive Gamma/co-Poisson source sums to the geometric current. -/
theorem hasSum_geometricGammaCoPoissonPrimePowerTerm
    (p : Nat.Primes) {sigma : ℝ} (hsigma : 0 < sigma) :
    HasSum (fun n : ℕ => geometricGammaCoPoissonPrimePowerTerm p n (sigma : ℂ))
      (geometricGammaCoPoissonPrimeCurrent p sigma : ℝ) := by
  let a : ℝ := (p : ℝ) ^ (-sigma)
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have ha0 : 0 < a := Real.rpow_pos_of_pos (lt_trans zero_lt_one hp) _
  have ha1 : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos hsigma)
  have hreal := (Real.hasSum_pow_div_log_of_abs_lt_one
    (x := a) (by rw [abs_of_pos ha0]; exact ha1)).neg
  have hcast : HasSum
      (fun n : ℕ => (((-(a ^ (n + 1) / (n + 1))) : ℝ) : ℂ))
      (((Real.log (1 - a)) : ℝ) : ℂ) := by
    convert hreal.map (Complex.ofRealCLM : ℝ →L[ℝ] ℂ)
        Complex.ofRealCLM.continuous using 1 <;>
      simp [Function.comp_def]
  have hterms : ∀ n : ℕ,
      geometricGammaCoPoissonPrimePowerTerm p n (sigma : ℂ) =
        (((-(a ^ (n + 1) / (n + 1))) : ℝ) : ℂ) := by
    intro n
    rw [geometricGammaCoPoissonPrimePowerTerm,
      RHTower.eulerGammaCoPoissonPrimitiveTerm_prime_pow p.prop
        (Nat.succ_ne_zero n),
      one_LSeries_term_prime_pow_real (p : ℕ) (n + 1) sigma p.prop.pos]
    simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_neg]
    push_cast
    dsimp [a]
    ring
  have hsum := hcast.congr_fun hterms
  simpa [geometricGammaCoPoissonPrimeCurrent, a] using hsum

/-- **Dyadic current coboundary.**  Parity current is full valuation current minus its doubled-rate
descendant. -/
theorem squarefreeGammaCoPoissonPrimeCurrent_eq_geometric_dyadicCoboundary
    (p : Nat.Primes) {sigma : ℝ} (hsigma : 0 < sigma) :
    squarefreeGammaCoPoissonPrimeCurrent p sigma =
      geometricGammaCoPoissonPrimeCurrent p sigma -
        geometricGammaCoPoissonPrimeCurrent p (2 * sigma) := by
  let a : ℝ := (p : ℝ) ^ (-sigma)
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hp0 : 0 < (p : ℝ) := lt_trans zero_lt_one hp
  have ha0 : 0 < a := Real.rpow_pos_of_pos hp0 _
  have ha1 : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos hsigma)
  have ha2 : (p : ℝ) ^ (-(2 * sigma)) = a ^ 2 := by
    dsimp [a]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hp0.le]
    congr 1
    ring
  rw [squarefreeGammaCoPoissonPrimeCurrent,
    geometricGammaCoPoissonPrimeCurrent, geometricGammaCoPoissonPrimeCurrent,
    ha2]
  rw [show 1 - a ^ 2 = (1 - a) * (1 + a) by ring,
    Real.log_mul (by linarith) (by linarith)]
  ring

/-- Geometric-valuation squared Hellinger Gram at endpoint rates. -/
def geometricPrimeValuationGramSq (p : Nat.Primes) (sigma tau : ℝ) : ℝ :=
  (1 - (p : ℝ) ^ (-sigma)) * (1 - (p : ℝ) ^ (-tau)) /
    (1 - (p : ℝ) ^ (-((sigma + tau) / 2))) ^ 2

/-- Squared Hellinger Gram after the valuation-parity Markov reporter. -/
def squarefreePrimeParityGramSq (p : Nat.Primes) (sigma tau : ℝ) : ℝ :=
  (1 + (p : ℝ) ^ (-((sigma + tau) / 2))) ^ 2 /
    ((1 + (p : ℝ) ^ (-sigma)) * (1 + (p : ℝ) ^ (-tau)))

private theorem prime_rpow_neg_two_mul
    (p : Nat.Primes) (sigma : ℝ) :
    (p : ℝ) ^ (-(2 * sigma)) = ((p : ℝ) ^ (-sigma)) ^ 2 := by
  have hp : 0 ≤ (p : ℝ) := by exact_mod_cast p.prop.pos.le
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hp]
  congr 1
  ring

private theorem geometric_parity_factor
    {a b m : ℝ} (ha0 : 0 < a) (hb0 : 0 < b) (hm0 : 0 < m) (hm1 : m < 1) :
    (1 - a) * (1 - b) / (1 - m) ^ 2 =
      (1 + m) ^ 2 / ((1 + a) * (1 + b)) *
        ((1 - a ^ 2) * (1 - b ^ 2) / (1 - m ^ 2) ^ 2) := by
  field_simp [show 1 - m ≠ 0 by linarith, show 1 + a ≠ 0 by linarith,
    show 1 + b ≠ 0 by linarith, show 1 + m ≠ 0 by linarith,
    show 1 - m ^ 2 ≠ 0 by nlinarith]
  ring

/-- Exact parity data-processing factorization: full valuation affinity is parity affinity times
the affinity of the discarded halved valuation. -/
theorem geometricPrimeValuationGramSq_eq_parity_mul_doubled
    (p : Nat.Primes) {sigma tau : ℝ} (hsigma : 0 < sigma) (htau : 0 < tau) :
    geometricPrimeValuationGramSq p sigma tau =
      squarefreePrimeParityGramSq p sigma tau *
        geometricPrimeValuationGramSq p (2 * sigma) (2 * tau) := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hmid : 0 < (sigma + tau) / 2 := by linarith
  have hm : (p : ℝ) ^ (-((sigma + tau) / 2)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos hmid)
  have hmidTwo : (2 * sigma + 2 * tau) / 2 = 2 * ((sigma + tau) / 2) := by ring
  rw [geometricPrimeValuationGramSq, squarefreePrimeParityGramSq,
    geometricPrimeValuationGramSq, hmidTwo,
    prime_rpow_neg_two_mul p sigma, prime_rpow_neg_two_mul p tau,
    prime_rpow_neg_two_mul p ((sigma + tau) / 2)]
  exact geometric_parity_factor (by positivity) (by positivity) (by positivity) hm

/-- Route-P literal squarefree cell is exactly the parity reporter at its endpoint rates. -/
theorem squarefreePrimeParityGramSq_eq_squarefreeMobiusPrimeCellGramSq
    (p : Nat.Primes) (epsilon x z : ℝ) :
    squarefreePrimeParityGramSq p (1 + x * epsilon) (1 + z * epsilon) =
      squarefreeMobiusPrimeCellGramSq p epsilon x z := by
  rw [squarefreePrimeParityGramSq, squarefreeMobiusPrimeCellGramSq]
  congr 1
  congr 2
  ring

/-- A nontrivial full valuation experiment has strictly subunit Hellinger Gram. -/
theorem geometricPrimeValuationGramSq_mem_Ioo_zero_one
    (p : Nat.Primes) {sigma tau : ℝ} (hsigma : 0 < sigma) (htau : 0 < tau)
    (hne : sigma ≠ tau) :
    geometricPrimeValuationGramSq p sigma tau ∈ Ioo 0 1 := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hp0 : 0 < (p : ℝ) := lt_trans zero_lt_one hp
  let a : ℝ := (p : ℝ) ^ (-sigma)
  let b : ℝ := (p : ℝ) ^ (-tau)
  let m : ℝ := (p : ℝ) ^ (-((sigma + tau) / 2))
  let u : ℝ := (p : ℝ) ^ (-(sigma / 2))
  let v : ℝ := (p : ℝ) ^ (-(tau / 2))
  have ha0 : 0 < a := by dsimp [a]; positivity
  have hb0 : 0 < b := by dsimp [b]; positivity
  have hm0 : 0 < m := by dsimp [m]; positivity
  have ha1 : a < 1 := by
    dsimp [a]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos hsigma)
  have hb1 : b < 1 := by
    dsimp [b]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos htau)
  have hm1 : m < 1 := by
    dsimp [m]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hu2 : u ^ 2 = a := by
    dsimp [u, a]
    symm
    simpa only [show 2 * (sigma / 2) = sigma by ring] using
      prime_rpow_neg_two_mul p (sigma / 2)
  have hv2 : v ^ 2 = b := by
    dsimp [v, b]
    symm
    simpa only [show 2 * (tau / 2) = tau by ring] using
      prime_rpow_neg_two_mul p (tau / 2)
  have huv : u * v = m := by
    dsimp [u, v, m]
    rw [← Real.rpow_add hp0]
    congr 1
    ring
  have huvNe : u ≠ v := by
    dsimp [u, v]
    apply (Real.strictMono_rpow_of_base_gt_one hp).injective.ne
    intro h
    apply hne
    linarith
  have hgap : 0 < (1 - m) ^ 2 - (1 - a) * (1 - b) := by
    rw [show (1 - m) ^ 2 - (1 - a) * (1 - b) = a + b - 2 * m by
      rw [← hu2, ← hv2, ← huv]
      ring]
    rw [← hu2, ← hv2, ← huv]
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr huvNe)]
  have hden : 0 < (1 - m) ^ 2 := sq_pos_of_pos (by linarith)
  change (1 - a) * (1 - b) / (1 - m) ^ 2 ∈ Ioo 0 1
  constructor
  · exact div_pos (mul_pos (by linarith) (by linarith)) hden
  · rw [div_lt_one hden]
    linarith

/-- Strict parity data processing: forgetting paired valuation strictly increases Hellinger
affinity unless endpoint rates coincide. -/
theorem geometricPrimeValuationGramSq_lt_squarefreePrimeParityGramSq
    (p : Nat.Primes) {sigma tau : ℝ} (hsigma : 0 < sigma) (htau : 0 < tau)
    (hne : sigma ≠ tau) :
    geometricPrimeValuationGramSq p sigma tau <
      squarefreePrimeParityGramSq p sigma tau := by
  have hdouble := geometricPrimeValuationGramSq_mem_Ioo_zero_one p
    (mul_pos two_pos hsigma) (mul_pos two_pos htau) (by
      intro h
      apply hne
      linarith)
  have hparityPos : 0 < squarefreePrimeParityGramSq p sigma tau := by
    rw [squarefreePrimeParityGramSq]
    positivity
  rw [geometricPrimeValuationGramSq_eq_parity_mul_doubled p hsigma htau]
  nlinarith [mul_lt_mul_of_pos_left hdouble.2 hparityPos]

/-- Sharp equality case for parity data processing. -/
theorem geometricPrimeValuationGramSq_eq_squarefreePrimeParityGramSq_iff
    (p : Nat.Primes) {sigma tau : ℝ} (hsigma : 0 < sigma) (htau : 0 < tau) :
    geometricPrimeValuationGramSq p sigma tau =
        squarefreePrimeParityGramSq p sigma tau ↔
      sigma = tau := by
  constructor
  · intro heq
    by_contra hne
    exact (ne_of_lt (geometricPrimeValuationGramSq_lt_squarefreePrimeParityGramSq
      p hsigma htau hne)) heq
  · intro h
    subst tau
    have hp : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    have ha : (p : ℝ) ^ (-sigma) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos hsigma)
    rw [geometricPrimeValuationGramSq, squarefreePrimeParityGramSq]
    rw [show -((sigma + sigma) / 2) = -sigma by ring]
    field_simp [show 1 - (p : ℝ) ^ (-sigma) ≠ 0 by linarith,
      show 1 + (p : ℝ) ^ (-sigma) ≠ 0 by positivity]

/-- Literal Route-P specialization of strict parity data processing. -/
theorem geometricRoutePPrimeCell_lt_squarefreeMobiusPrimeCellGramSq
    (p : Nat.Primes) {epsilon x z : ℝ}
    (hx : 0 < 1 + x * epsilon) (hz : 0 < 1 + z * epsilon)
    (hne : 1 + x * epsilon ≠ 1 + z * epsilon) :
    geometricPrimeValuationGramSq p (1 + x * epsilon) (1 + z * epsilon) <
      squarefreeMobiusPrimeCellGramSq p epsilon x z := by
  rw [← squarefreePrimeParityGramSq_eq_squarefreeMobiusPrimeCellGramSq]
  exact geometricPrimeValuationGramSq_lt_squarefreePrimeParityGramSq p hx hz hne

/-- Geometric free-energy curvature is the logarithm of its Hellinger Gram. -/
theorem log_geometricPrimeValuationGramSq_eq_currentSecondDifference
    (p : Nat.Primes) {sigma tau : ℝ} (hsigma : 0 < sigma) (htau : 0 < tau) :
    Real.log (geometricPrimeValuationGramSq p sigma tau) =
      geometricGammaCoPoissonPrimeCurrent p sigma +
        geometricGammaCoPoissonPrimeCurrent p tau -
          2 * geometricGammaCoPoissonPrimeCurrent p ((sigma + tau) / 2) := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hsigmaMid : 0 < (sigma + tau) / 2 := by linarith
  have hs : (p : ℝ) ^ (-sigma) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos hsigma)
  have ht : (p : ℝ) ^ (-tau) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos htau)
  have hm : (p : ℝ) ^ (-((sigma + tau) / 2)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos hsigmaMid)
  rw [geometricPrimeValuationGramSq,
    Real.log_div (mul_ne_zero (by linarith) (by linarith)) (pow_ne_zero 2 (by linarith)),
    Real.log_mul (by linarith) (by linarith), Real.log_pow]
  simp only [geometricGammaCoPoissonPrimeCurrent]
  ring

/-- P-G51 log-Gram is the cofiber of geometric free-energy curvature under dyadic descent. -/
theorem log_squarefreePrimeCell_eq_geometric_dyadicCofiber
    (p : Nat.Primes) {epsilon x z : ℝ}
    (hx : 0 < 1 + x * epsilon) (hz : 0 < 1 + z * epsilon)
    (hy : 0 < 1 + ((x + z) / 2) * epsilon) :
    Real.log (squarefreeMobiusPrimeCellGramSq p epsilon x z) =
      (geometricGammaCoPoissonPrimeCurrent p (1 + x * epsilon) +
        geometricGammaCoPoissonPrimeCurrent p (1 + z * epsilon) -
          2 * geometricGammaCoPoissonPrimeCurrent p
            (1 + ((x + z) / 2) * epsilon)) -
      (geometricGammaCoPoissonPrimeCurrent p (2 * (1 + x * epsilon)) +
        geometricGammaCoPoissonPrimeCurrent p (2 * (1 + z * epsilon)) -
          2 * geometricGammaCoPoissonPrimeCurrent p
            (2 * (1 + ((x + z) / 2) * epsilon))) := by
  rw [log_squarefreeMobiusPrimeCellGramSq_eq_squarefreeGammaCoPoissonSecondDifference]
  rw [squarefreeGammaCoPoissonPrimeCurrent_eq_geometric_dyadicCoboundary p hx,
    squarefreeGammaCoPoissonPrimeCurrent_eq_geometric_dyadicCoboundary p hz,
    squarefreeGammaCoPoissonPrimeCurrent_eq_geometric_dyadicCoboundary p hy]
  ring

end

end RHTower.HedenmalmThetaSource
