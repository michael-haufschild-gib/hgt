import GaloisForLFunctions.RHTower.GammaSewnFourRateSynchronizedEulerFisher
import GaloisForLFunctions.RHTower.GammaSewnXiShiftTangentHilbertKernel
import GaloisForLFunctions.RHTower.SoninSemilocalJacobiTransform

/-!
# The Gamma-Jordan / Xi-tangent response-gap Laplacian

The signed `-1/2,+3/2` boundary law is the closed-form decomposition of one normalized
variance-biased Gamma response.  On the source-forced inverse-prime Fisher chamber, that response
strictly exceeds the correlation of the actual all-depth Xi-shift endpoint tangents away from the
diagonal.  Their difference is therefore a positive complete-graph edge weight and produces a
strict slope-dispersion Laplacian on every nonconstant finite prime packet.

This is a source-side response converter.  It uses neither a Xi zero, an RH-equivalent sign
assumption, a source-span closure, nor an ambient inverse resolution operator.
-/

noncomputable section

open Complex Filter MeasureTheory Polynomial Real Set
open scoped BigOperators

namespace RHTower

/-! ## The joined Gamma-Jordan response -/

/-- The negative regularized height component of the Gamma response. -/
def gammaJordanHeightResponse (t : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * semilocalArchimedeanCharacteristic t

/-- The positive sewing component of the Gamma response. -/
def gammaJordanSewingResponse (t : ℝ) : ℝ :=
  (3 / 2 : ℝ) * semilocalArchimedeanCharacteristic t ^ 5

/-- The invariant joined response.  Its two summands must remain correlated. -/
def gammaJordanJoinedResponse (t : ℝ) : ℝ :=
  gammaJordanHeightResponse t + gammaJordanSewingResponse t

theorem semilocalArchimedeanCharacteristic_pow_four_add_tanh_sq (t : ℝ) :
    semilocalArchimedeanCharacteristic t ^ 4 + Real.tanh t ^ 2 = 1 := by
  rw [show semilocalArchimedeanCharacteristic t ^ 4 =
    (semilocalArchimedeanCharacteristic t ^ 2) ^ 2 by ring,
    semilocalArchimedeanCharacteristic_sq, Real.tanh_eq_sinh_div_cosh]
  have hcosh : Real.cosh t ≠ 0 := (Real.cosh_pos t).ne'
  field_simp [hcosh]
  nlinarith [Real.cosh_sq_sub_sinh_sq t]

/-- The signed closed form is the characteristic plus twice the centered second-moment
covariance. -/
theorem gammaJordanJoinedResponse_eq_characteristic_add_two_covariance (t : ℝ) :
    gammaJordanJoinedResponse t =
      semilocalArchimedeanCharacteristic t +
        2 * semilocalArchimedeanSecondMomentCovarianceKernel t := by
  have hunit := semilocalArchimedeanCharacteristic_pow_four_add_tanh_sq t
  unfold gammaJordanJoinedResponse gammaJordanHeightResponse gammaJordanSewingResponse
    semilocalArchimedeanSecondMomentCovarianceKernel
  rw [show semilocalArchimedeanCharacteristic t ^ 5 =
    semilocalArchimedeanCharacteristic t *
      semilocalArchimedeanCharacteristic t ^ 4 by ring]
  linear_combination
    (3 / 2 * semilocalArchimedeanCharacteristic t) * hunit

theorem gammaJordanHeightResponse_zero :
    gammaJordanHeightResponse 0 = -(1 / 2 : ℝ) := by
  simp [gammaJordanHeightResponse, semilocalArchimedeanCharacteristic]

theorem gammaJordanSewingResponse_zero :
    gammaJordanSewingResponse 0 = (3 / 2 : ℝ) := by
  simp [gammaJordanSewingResponse, semilocalArchimedeanCharacteristic]

theorem gammaJordanJoinedResponse_zero :
    gammaJordanJoinedResponse 0 = 1 := by
  rw [gammaJordanJoinedResponse, gammaJordanHeightResponse_zero,
    gammaJordanSewingResponse_zero]
  ring

private theorem gammaJordanPolynomialFourier_add
    (P Q : ℝ[X]) (t : ℝ) :
    semilocalArchimedeanPolynomialFourier (P + Q) t =
      semilocalArchimedeanPolynomialFourier P t +
        semilocalArchimedeanPolynomialFourier Q t := by
  unfold semilocalArchimedeanPolynomialFourier
  rw [show (fun s : ℝ => (((P + Q).eval s : ℝ) : ℂ) *
      Complex.exp (((t * s : ℝ) : ℂ) * I)) =
      fun s : ℝ => (((P.eval s : ℝ) : ℂ) *
          Complex.exp (((t * s : ℝ) : ℂ) * I)) +
        (((Q.eval s : ℝ) : ℂ) *
          Complex.exp (((t * s : ℝ) : ℂ) * I)) by
    funext s
    simp
    ring]
  exact integral_add
    (integrable_semilocalArchimedeanPolynomialFourier_integrand P t)
    (integrable_semilocalArchimedeanPolynomialFourier_integrand Q t)

private theorem gammaJordanPolynomialFourier_const_mul
    (r : ℝ) (P : ℝ[X]) (t : ℝ) :
    semilocalArchimedeanPolynomialFourier (C r * P) t =
      (r : ℂ) * semilocalArchimedeanPolynomialFourier P t := by
  unfold semilocalArchimedeanPolynomialFourier
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  simp
  ring

private theorem gammaJacobiPolynomial_two_recurrence (s : ℝ) :
    semilocalArchimedeanJacobiCoefficient 0 *
        semilocalArchimedeanJacobiCoefficient 1 *
          (semilocalArchimedeanJacobiPolynomial 2).eval s =
      s ^ 2 - semilocalArchimedeanJacobiCoefficient 0 ^ 2 := by
  have hrec := semilocalArchimedeanJacobiPolynomial_eval_recurrence 0 s
  rw [semilocalArchimedeanJacobiPolynomial_eval_zero,
    semilocalArchimedeanJacobiPolynomial_eval_one] at hrec
  have ha0 : semilocalArchimedeanJacobiCoefficient 0 ≠ 0 :=
    (semilocalArchimedeanJacobiCoefficient_pos 0).ne'
  field_simp [ha0] at hrec
  nlinarith

private theorem two_mul_X_sq_eq_gammaJacobi_zero_add_two :
    C (2 : ℝ) * X ^ 2 =
      semilocalArchimedeanJacobiPolynomial 0 +
        C (2 * semilocalArchimedeanJacobiCoefficient 0 *
          semilocalArchimedeanJacobiCoefficient 1) *
            semilocalArchimedeanJacobiPolynomial 2 := by
  apply Polynomial.funext
  intro s
  have hrec := gammaJacobiPolynomial_two_recurrence s
  have ha0 := semilocalArchimedeanJacobiCoefficient_sq 0
  norm_num at ha0
  simp only [eval_mul, eval_C, eval_pow, eval_X,
    semilocalArchimedeanJacobiPolynomial_eval_zero, eval_add]
  nlinarith

/-- The joined response is literally the Fourier transform of the nonnegative density multiplier
`2s²` against the normalized Gamma measure.  In particular its signed closed form is one positive
correlation, not a difference of two target norms. -/
theorem semilocalArchimedeanPolynomialFourier_two_mul_X_sq_eq_gammaJordanJoinedResponse
    (t : ℝ) :
    semilocalArchimedeanPolynomialFourier (C (2 : ℝ) * X ^ 2) t =
      (gammaJordanJoinedResponse t : ℂ) := by
  rw [two_mul_X_sq_eq_gammaJacobi_zero_add_two,
    gammaJordanPolynomialFourier_add,
    gammaJordanPolynomialFourier_const_mul]
  change semilocalArchimedeanJacobiFourier 0 t +
      ((2 * semilocalArchimedeanJacobiCoefficient 0 *
        semilocalArchimedeanJacobiCoefficient 1 : ℝ) : ℂ) *
          semilocalArchimedeanJacobiFourier 2 t = _
  have hnormZero : semilocalArchimedeanJacobiNormalization 0 = 1 := by
    norm_num [semilocalArchimedeanJacobiNormalization]
  have hnormOne :=
    semilocalArchimedeanJacobiNormalization_succ_mul_coefficient 0
  have hnormTwo :=
    semilocalArchimedeanJacobiNormalization_succ_mul_coefficient 1
  norm_num [hnormZero] at hnormOne hnormTwo
  have hprod :
      (2 * semilocalArchimedeanJacobiCoefficient 0 *
          semilocalArchimedeanJacobiCoefficient 1) *
        semilocalArchimedeanJacobiNormalization 2 = 3 / 2 := by
    calc
      (2 * semilocalArchimedeanJacobiCoefficient 0 *
          semilocalArchimedeanJacobiCoefficient 1) *
          semilocalArchimedeanJacobiNormalization 2 =
        2 * (semilocalArchimedeanJacobiNormalization 2 *
          semilocalArchimedeanJacobiCoefficient 1) *
            semilocalArchimedeanJacobiCoefficient 0 := by ring
      _ = 2 * (semilocalArchimedeanJacobiNormalization 1 * (3 / 2)) *
          semilocalArchimedeanJacobiCoefficient 0 := by rw [hnormTwo]
      _ = 3 * (semilocalArchimedeanJacobiNormalization 1 *
          semilocalArchimedeanJacobiCoefficient 0) := by ring
      _ = 3 / 2 := by rw [hnormOne]; ring
  have hzero : semilocalArchimedeanJacobiFourier 0 t =
      (semilocalArchimedeanCharacteristic t : ℂ) := by
    rw [semilocalArchimedeanJacobiFourier_eq_closedForm,
      semilocalArchimedeanJacobiFourierClosedForm]
    simp [hnormZero]
  have htwo :
      ((2 * semilocalArchimedeanJacobiCoefficient 0 *
          semilocalArchimedeanJacobiCoefficient 1 : ℝ) : ℂ) *
          semilocalArchimedeanJacobiFourier 2 t =
        -((3 / 2 : ℝ) : ℂ) *
          (semilocalArchimedeanCharacteristic t : ℂ) *
            (Real.tanh t : ℂ) ^ 2 := by
    rw [semilocalArchimedeanJacobiFourier_eq_closedForm,
      semilocalArchimedeanJacobiFourierClosedForm]
    have hprodC := congrArg Complex.ofReal hprod
    push_cast at hprodC
    norm_num only [Complex.I_sq]
    calc
      _ = -(2 * (semilocalArchimedeanJacobiCoefficient 0 : ℂ) *
            (semilocalArchimedeanJacobiCoefficient 1 : ℂ) *
            (semilocalArchimedeanJacobiNormalization 2 : ℂ)) *
          (semilocalArchimedeanCharacteristic t : ℂ) *
            (Real.tanh t : ℂ) ^ 2 := by push_cast; ring
      _ = -((3 / 2 : ℝ) : ℂ) *
          (semilocalArchimedeanCharacteristic t : ℂ) *
            (Real.tanh t : ℂ) ^ 2 := by rw [hprodC]; norm_num
  rw [hzero, htwo, gammaJordanJoinedResponse_eq_characteristic_add_two_covariance]
  unfold semilocalArchimedeanSecondMomentCovarianceKernel
  push_cast
  ring

/-- Integral form of the variance-biased response. -/
theorem integral_two_mul_sq_cexp_semilocalArchimedeanGammaMeasure (t : ℝ) :
    (∫ s : ℝ, ((2 * s ^ 2 : ℝ) : ℂ) *
        Complex.exp (((t * s : ℝ) : ℂ) * Complex.I)
          ∂semilocalArchimedeanGammaMeasure) =
      (gammaJordanJoinedResponse t : ℂ) := by
  simpa [semilocalArchimedeanPolynomialFourier] using
    semilocalArchimedeanPolynomialFourier_two_mul_X_sq_eq_gammaJordanJoinedResponse t

/-- The source's negative four-rate mass is the zero-frequency height response times the same
complementary Fisher mean. -/
theorem gammaSewnFourRateBoundaryComplementaryEulerHeightFiniteMass_eq_response_zero_mul_fisher
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) :
    gammaSewnFourRateBoundaryComplementaryEulerHeightFiniteMass a rate cell =
      gammaJordanHeightResponse 0 *
        complementaryFisherMean
          (gammaSewnFourRateBoundaryPairProbability a rate cell)
          (gammaSewnFourRateComplementaryFisher cell) := by
  rw [gammaSewnFourRateBoundaryComplementaryEulerHeightFiniteMass_eq_neg_half_fisher,
    gammaJordanHeightResponse_zero]

/-- The source's positive four-rate sewing mass is the zero-frequency sewing response times the
same complementary Fisher mean. -/
theorem gammaSewnFourRateBoundaryComplementarySewingMass_eq_response_zero_mul_fisher
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) :
    gammaSewnFourRateBoundaryComplementarySewingMass a rate cell =
      gammaJordanSewingResponse 0 *
        complementaryFisherMean
          (gammaSewnFourRateBoundaryPairProbability a rate cell)
          (gammaSewnFourRateComplementaryFisher cell) := by
  rw [gammaSewnFourRateBoundaryComplementarySewingMass_eq_three_halves_fisher,
    gammaJordanSewingResponse_zero]

/-- The invariant source join is multiplication by the normalized joined response at zero. -/
theorem gammaSewnFourRateBoundaryComplementary_join_eq_response_zero_mul_fisher
    (a : ℝ) (rate : Fin 4 → ℝ) (cell : Fin 4 → Nat.Primes × ℕ) :
    gammaSewnFourRateBoundaryComplementaryEulerHeightFiniteMass a rate cell +
        gammaSewnFourRateBoundaryComplementarySewingMass a rate cell =
      gammaJordanJoinedResponse 0 *
        complementaryFisherMean
          (gammaSewnFourRateBoundaryPairProbability a rate cell)
          (gammaSewnFourRateComplementaryFisher cell) := by
  rw [gammaSewnFourRateBoundaryComplementary_heightFinite_add_sewing_eq_fisher,
    gammaJordanJoinedResponse_zero, one_mul]

/-! ## The common Gamma / Xi Fisher correlation -/

/-- The overlap of the two unit geometric depth states in inverse-prime coordinates. -/
def gammaXiFisherBaseCorrelation (p q : Nat.Primes) : ℝ :=
  let a := (p : ℝ)⁻¹
  let b := (q : ℝ)⁻¹
  Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) / (1 - a * b)

/-- The variance-biased Gamma response written as a function of its base correlation. -/
def gammaJordanResponseFromBase (k : ℝ) : ℝ :=
  Real.sqrt k * (3 * k ^ 2 - 1) / 2

/-- The Fisher tangent response of the unit geometric depth curve. -/
def xiShiftTangentResponseFromBase (k : ℝ) : ℝ :=
  k * (2 * k ^ 2 - 1)

/-- The joined-Gamma surplus over the Xi-shift Fisher tangent response. -/
def gammaJordanXiResponseGapFromBase (k : ℝ) : ℝ :=
  gammaJordanResponseFromBase k - xiShiftTangentResponseFromBase k

private theorem inversePrime_pos (p : Nat.Primes) :
    0 < ((p : ℝ)⁻¹) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  exact inv_pos.mpr hp0

private theorem inversePrime_le_half (p : Nat.Primes) :
    ((p : ℝ)⁻¹) ≤ 1 / 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.2.two_le
  rw [inv_eq_one_div, div_le_iff₀ hp0]
  nlinarith

private theorem fisherBaseCorrelation_data
    {a b : ℝ} (ha0 : 0 < a) (hb0 : 0 < b)
    (haHalf : a ≤ 1 / 2) (hbHalf : b ≤ 1 / 2) :
    let k := Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) / (1 - a * b)
    0 < k ∧ k ≤ 1 ∧ 3 / 4 < k ^ 2 ∧ (k = 1 ↔ a = b) := by
  let A := (1 - a ^ 2) * (1 - b ^ 2)
  let d := 1 - a * b
  let k := Real.sqrt A / d
  have ha1 : a < 1 := lt_of_le_of_lt haHalf (by norm_num)
  have hb1 : b < 1 := lt_of_le_of_lt hbHalf (by norm_num)
  have habHalf : a * b ≤ 1 / 4 := by
    calc
      a * b ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) :=
        mul_le_mul haHalf hbHalf hb0.le (by norm_num)
      _ = 1 / 4 := by norm_num
  have hd : 0 < d := by dsimp only [d]; nlinarith
  have haSq : 0 < 1 - a ^ 2 := by
    nlinarith [(sq_lt_sq₀ ha0.le (by norm_num)).2 ha1]
  have hbSq : 0 < 1 - b ^ 2 := by
    nlinarith [(sq_lt_sq₀ hb0.le (by norm_num)).2 hb1]
  have hA : 0 < A := by exact mul_pos haSq hbSq
  have hk0 : 0 < k := div_pos (Real.sqrt_pos.2 hA) hd
  have hupper : 2 * (a - b) < d := by
    have h2a : 2 * a ≤ 1 := by nlinarith
    have ha2 : a < 2 := ha1.trans (by norm_num)
    have hablt : a * b < 2 * b := by
      simpa [mul_comm] using mul_lt_mul_of_pos_left ha2 hb0
    dsimp only [d]
    nlinarith
  have hlower : -d < 2 * (a - b) := by
    have h2b : 2 * b ≤ 1 := by nlinarith
    have hb2 : b < 2 := hb1.trans (by norm_num)
    have hablt : a * b < 2 * a := by
      simpa [mul_comm] using mul_lt_mul_of_pos_left hb2 ha0
    dsimp only [d]
    nlinarith
  have habs : |2 * (a - b)| < d := (abs_lt).2 ⟨hlower, hupper⟩
  have hsquare : (2 * (a - b)) ^ 2 < d ^ 2 := by
    have hs := (sq_lt_sq₀ (abs_nonneg (2 * (a - b))) hd.le).2 habs
    nlinarith [sq_abs (a - b)]
  have hratio : ((a - b) / d) ^ 2 < 1 / 4 := by
    rw [div_pow, div_lt_iff₀ (sq_pos_of_pos hd)]
    nlinarith
  have hksq : k ^ 2 = 1 - ((a - b) / d) ^ 2 := by
    dsimp only [k]
    rw [div_pow, Real.sq_sqrt hA.le]
    field_simp [hd.ne']
    dsimp only [A, d]
    ring
  have hkSqLower : 3 / 4 < k ^ 2 := by rw [hksq]; nlinarith
  have hk1 : k ≤ 1 := by
    have hratio0 : 0 ≤ ((a - b) / d) ^ 2 := sq_nonneg _
    have hkSqLe : k ^ 2 ≤ 1 := by rw [hksq]; nlinarith
    nlinarith
  have hkEq : k = 1 ↔ a = b := by
    constructor
    · intro hk
      rw [hk, one_pow] at hksq
      have : ((a - b) / d) ^ 2 = 0 := by linarith
      have : (a - b) / d = 0 := sq_eq_zero_iff.mp this
      exact sub_eq_zero.mp ((div_eq_zero_iff).mp this |>.resolve_right hd.ne')
    · intro hab
      rw [hab, sub_self, zero_div, zero_pow (by norm_num)] at hksq
      nlinarith
  exact ⟨hk0, hk1, hkSqLower, hkEq⟩

theorem gammaXiFisherBaseCorrelation_pos (p q : Nat.Primes) :
    0 < gammaXiFisherBaseCorrelation p q := by
  simpa only [gammaXiFisherBaseCorrelation] using
    (fisherBaseCorrelation_data (inversePrime_pos p) (inversePrime_pos q)
      (inversePrime_le_half p) (inversePrime_le_half q)).1

theorem gammaXiFisherBaseCorrelation_le_one (p q : Nat.Primes) :
    gammaXiFisherBaseCorrelation p q ≤ 1 := by
  simpa only [gammaXiFisherBaseCorrelation] using
    (fisherBaseCorrelation_data (inversePrime_pos p) (inversePrime_pos q)
      (inversePrime_le_half p) (inversePrime_le_half q)).2.1

/-- Prime localization is substantially narrower than the full Fisher line: the squared base
correlation is uniformly greater than `3/4`. -/
theorem gammaXiFisherBaseCorrelation_sq_gt_three_fourths (p q : Nat.Primes) :
    3 / 4 < gammaXiFisherBaseCorrelation p q ^ 2 := by
  simpa only [gammaXiFisherBaseCorrelation] using
    (fisherBaseCorrelation_data (inversePrime_pos p) (inversePrime_pos q)
      (inversePrime_le_half p) (inversePrime_le_half q)).2.2.1

theorem gammaXiFisherBaseCorrelation_eq_one_iff (p q : Nat.Primes) :
    gammaXiFisherBaseCorrelation p q = 1 ↔ p = q := by
  have hraw :=
    (fisherBaseCorrelation_data (inversePrime_pos p) (inversePrime_pos q)
      (inversePrime_le_half p) (inversePrime_le_half q)).2.2.2
  change gammaXiFisherBaseCorrelation p q = 1 ↔
    ((p : ℝ)⁻¹) = (q : ℝ)⁻¹ at hraw
  constructor
  · intro h
    have hinv : ((p : ℝ)⁻¹) = (q : ℝ)⁻¹ := hraw.mp h
    have hcast : (p : ℝ) = q := inv_injective hinv
    exact Subtype.ext (by exact_mod_cast hcast)
  · intro hpq
    subst q
    exact hraw.mpr rfl

/-- The all-depth normalized Xi-shift tangent kernel is exactly the Fisher derivative response of
the common geometric-state overlap. -/
theorem gammaSewnXiShiftEndpointUnitTangentKernel_eq_responseFromBase
    (p q : Nat.Primes) :
    gammaSewnXiShiftEndpointUnitTangentKernel p q =
      xiShiftTangentResponseFromBase (gammaXiFisherBaseCorrelation p q) := by
  let a := (p : ℝ)⁻¹
  let b := (q : ℝ)⁻¹
  let A := (1 - a ^ 2) * (1 - b ^ 2)
  let d := 1 - a * b
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast q.2.ne_zero
  have ha0 : 0 < a := inversePrime_pos p
  have hb0 : 0 < b := inversePrime_pos q
  have haHalf : a ≤ 1 / 2 := inversePrime_le_half p
  have hbHalf : b ≤ 1 / 2 := inversePrime_le_half q
  have habHalf : a * b ≤ 1 / 4 := by
    calc
      a * b ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) :=
        mul_le_mul haHalf hbHalf hb0.le (by norm_num)
      _ = 1 / 4 := by norm_num
  have hd : 0 < d := by dsimp only [d]; nlinarith
  have hA : 0 ≤ A := by
    dsimp only [A]
    have haSq : 0 ≤ 1 - a ^ 2 := by nlinarith [sq_nonneg (a - 1 / 2)]
    have hbSq : 0 ≤ 1 - b ^ 2 := by nlinarith [sq_nonneg (b - 1 / 2)]
    exact mul_nonneg haSq hbSq
  rw [gammaSewnXiShiftEndpointUnitTangentKernel,
    gammaSewnXiShiftEndpointTangentKernel_eq_closed]
  change (p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
      (a ^ 2 * b ^ 2 * Real.sqrt A *
        ((1 + a * b) ^ 2 - 2 * (a ^ 2 + b ^ 2)) / d ^ 3) = _
  have hpa : (p : ℝ) ^ 2 * a ^ 2 = 1 := by
    dsimp only [a]
    field_simp [hp0]
  have hqb : (q : ℝ) ^ 2 * b ^ 2 = 1 := by
    dsimp only [b]
    field_simp [hq0]
  rw [show (p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
      (a ^ 2 * b ^ 2 * Real.sqrt A *
        ((1 + a * b) ^ 2 - 2 * (a ^ 2 + b ^ 2)) / d ^ 3) =
      Real.sqrt A * ((1 + a * b) ^ 2 - 2 * (a ^ 2 + b ^ 2)) / d ^ 3 by
    calc
      _ = (((p : ℝ) ^ 2 * a ^ 2) * ((q : ℝ) ^ 2 * b ^ 2)) *
          (Real.sqrt A * ((1 + a * b) ^ 2 - 2 * (a ^ 2 + b ^ 2)) / d ^ 3) := by
            ring
      _ = _ := by rw [hpa, hqb]; ring]
  unfold xiShiftTangentResponseFromBase gammaXiFisherBaseCorrelation
  change Real.sqrt A * ((1 + a * b) ^ 2 - 2 * (a ^ 2 + b ^ 2)) / d ^ 3 =
    (Real.sqrt A / d) * (2 * (Real.sqrt A / d) ^ 2 - 1)
  rw [div_pow, Real.sq_sqrt hA]
  field_simp [hd.ne']
  dsimp only [A, d]
  ring

/-! ## Strict response gap and its finite Laplacian -/

/-- Algebraic factorization of the Gamma/Xi response gap on its natural nonnegative domain. -/
theorem gammaJordanXiResponseGapFromBase_factor {k : ℝ} (hk : 0 ≤ k) :
    gammaJordanXiResponseGapFromBase k =
      Real.sqrt k / 2 * (1 - Real.sqrt k) *
        (4 * Real.sqrt k ^ 4 + Real.sqrt k ^ 3 +
          Real.sqrt k ^ 2 + Real.sqrt k - 1) := by
  let x := Real.sqrt k
  have hxSq : x ^ 2 = k := Real.sq_sqrt hk
  unfold gammaJordanXiResponseGapFromBase gammaJordanResponseFromBase
    xiShiftTangentResponseFromBase
  change x * (3 * k ^ 2 - 1) / 2 - k * (2 * k ^ 2 - 1) =
    x / 2 * (1 - x) * (4 * x ^ 4 + x ^ 3 + x ^ 2 + x - 1)
  rw [← hxSq]
  ring

theorem gammaJordanXiResponseGapFromBase_pos
    {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hkLoc : 3 / 4 < k ^ 2) :
    0 < gammaJordanXiResponseGapFromBase k := by
  let x := Real.sqrt k
  have hx0 : 0 < x := Real.sqrt_pos.2 hk0
  have hxSq : x ^ 2 = k := Real.sq_sqrt hk0.le
  have hxSqLt : x ^ 2 < 1 := by rw [hxSq]; exact hk1
  have hx1 : x < 1 :=
    (sq_lt_sq₀ hx0.le (by norm_num)).mp (by simpa using hxSqLt)
  have hxFourth : 3 / 4 < x ^ 4 := by
    rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, hxSq]
    exact hkLoc
  have hbracket : 0 < 4 * x ^ 4 + x ^ 3 + x ^ 2 + x - 1 := by
    nlinarith [pow_nonneg hx0.le 3, sq_nonneg x]
  rw [gammaJordanXiResponseGapFromBase_factor hk0.le]
  change 0 < x / 2 * (1 - x) * (4 * x ^ 4 + x ^ 3 + x ^ 2 + x - 1)
  positivity

theorem gammaJordanXiResponseGapFromBase_nonneg
    {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (hkLoc : 3 / 4 < k ^ 2) :
    0 ≤ gammaJordanXiResponseGapFromBase k := by
  rcases hk1.eq_or_lt with rfl | hklt
  · norm_num [gammaJordanXiResponseGapFromBase, gammaJordanResponseFromBase,
      xiShiftTangentResponseFromBase]
  · exact (gammaJordanXiResponseGapFromBase_pos hk0 hklt hkLoc).le

theorem gammaJordanXiResponseGapFromBase_eq_zero_iff
    {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (hkLoc : 3 / 4 < k ^ 2) :
    gammaJordanXiResponseGapFromBase k = 0 ↔ k = 1 := by
  constructor
  · intro hzero
    by_contra hkne
    have hklt : k < 1 := lt_of_le_of_ne hk1 hkne
    exact (ne_of_gt (gammaJordanXiResponseGapFromBase_pos hk0 hklt hkLoc)) hzero
  · rintro rfl
    norm_num [gammaJordanXiResponseGapFromBase, gammaJordanResponseFromBase,
      xiShiftTangentResponseFromBase]

/-- The source-defined prime response-gap edge weight. -/
def gammaJordanXiPrimeResponseGap (p q : Nat.Primes) : ℝ :=
  gammaJordanXiResponseGapFromBase (gammaXiFisherBaseCorrelation p q)

theorem gammaJordanXiPrimeResponseGap_nonneg (p q : Nat.Primes) :
    0 ≤ gammaJordanXiPrimeResponseGap p q := by
  apply gammaJordanXiResponseGapFromBase_nonneg
  · exact gammaXiFisherBaseCorrelation_pos p q
  · exact gammaXiFisherBaseCorrelation_le_one p q
  · exact gammaXiFisherBaseCorrelation_sq_gt_three_fourths p q

/-- The gap vanishes exactly on the prime diagonal. -/
theorem gammaJordanXiPrimeResponseGap_eq_zero_iff (p q : Nat.Primes) :
    gammaJordanXiPrimeResponseGap p q = 0 ↔ p = q := by
  rw [gammaJordanXiPrimeResponseGap,
    gammaJordanXiResponseGapFromBase_eq_zero_iff
      (gammaXiFisherBaseCorrelation_pos p q)
      (gammaXiFisherBaseCorrelation_le_one p q)
      (gammaXiFisherBaseCorrelation_sq_gt_three_fourths p q),
    gammaXiFisherBaseCorrelation_eq_one_iff]

theorem gammaJordanXiPrimeResponseGap_pos_iff (p q : Nat.Primes) :
    0 < gammaJordanXiPrimeResponseGap p q ↔ p ≠ q := by
  constructor
  · intro h hpq
    subst q
    have hz := (gammaJordanXiPrimeResponseGap_eq_zero_iff p p).2 rfl
    linarith
  · intro hpq
    have hnonneg := gammaJordanXiPrimeResponseGap_nonneg p q
    have hne : gammaJordanXiPrimeResponseGap p q ≠ 0 := by
      intro hzero
      exact hpq ((gammaJordanXiPrimeResponseGap_eq_zero_iff p q).mp hzero)
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- The gap is exactly the joined prime-local Gamma response minus the actual all-depth Xi-shift
tangent correlation. -/
theorem gammaJordanXiPrimeResponseGap_eq_joined_sub_tangent
    (p q : Nat.Primes) :
    gammaJordanXiPrimeResponseGap p q =
      gammaJordanResponseFromBase (gammaXiFisherBaseCorrelation p q) -
        gammaSewnXiShiftEndpointUnitTangentKernel p q := by
  rw [gammaJordanXiPrimeResponseGap, gammaJordanXiResponseGapFromBase,
    gammaSewnXiShiftEndpointUnitTangentKernel_eq_responseFromBase]

/-- On the localized Fisher chamber the response gap controls at least one quarter of the actual
tangent correlation defect. -/
theorem one_fourth_tangentResponseDefect_lt_gammaJordanXiResponseGapFromBase
    {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (hkLoc : 3 / 4 < k ^ 2) :
    (1 / 4 : ℝ) * (1 - xiShiftTangentResponseFromBase k) <
      gammaJordanXiResponseGapFromBase k := by
  let x := Real.sqrt k
  have hx0 : 0 < x := Real.sqrt_pos.2 hk0
  have hxSq : x ^ 2 = k := Real.sq_sqrt hk0.le
  have hxSqLt : x ^ 2 < 1 := by rw [hxSq]; exact hk1
  have hx1 : x < 1 :=
    (sq_lt_sq₀ hx0.le (by norm_num)).mp (by simpa using hxSqLt)
  have hxFourth : 3 / 4 < x ^ 4 := by
    rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, hxSq]
    exact hkLoc
  have hxTwoThirds : 2 / 3 < x := by
    by_contra h
    have hxle : x ≤ 2 / 3 := le_of_not_gt h
    have hsquare := (sq_le_sq₀ hx0.le (by norm_num : (0 : ℝ) ≤ 2 / 3)).2 hxle
    have hfourth : x ^ 4 ≤ (2 / 3 : ℝ) ^ 4 := by
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg ((2 / 3 : ℝ) ^ 2)]
    norm_num at hfourth
    nlinarith
  have hscaled : (9 / 2 : ℝ) * x < 6 * x ^ 5 := by
    have h := mul_lt_mul_of_pos_left hxFourth (show 0 < 6 * x by positivity)
    nlinarith
  have hfactor : 0 < 6 * x ^ 5 - 3 * x - 1 := by nlinarith
  have hid :
      4 * gammaJordanXiResponseGapFromBase k -
          (1 - xiShiftTangentResponseFromBase k) =
        (1 - x) * (6 * x ^ 5 - 3 * x - 1) := by
    unfold gammaJordanXiResponseGapFromBase gammaJordanResponseFromBase
      xiShiftTangentResponseFromBase
    change 4 * (x * (3 * k ^ 2 - 1) / 2 -
        k * (2 * k ^ 2 - 1)) - (1 - k * (2 * k ^ 2 - 1)) = _
    rw [← hxSq]
    ring
  nlinarith [mul_pos (sub_pos.mpr hx1) hfactor]

/-- The same gap is strictly less than one third of the tangent correlation defect. -/
theorem gammaJordanXiResponseGapFromBase_lt_one_third_tangentResponseDefect
    {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    gammaJordanXiResponseGapFromBase k <
      (1 / 3 : ℝ) * (1 - xiShiftTangentResponseFromBase k) := by
  let x := Real.sqrt k
  have hx0 : 0 < x := Real.sqrt_pos.2 hk0
  have hxSq : x ^ 2 = k := Real.sq_sqrt hk0.le
  have hxSqLt : x ^ 2 < 1 := by rw [hxSq]; exact hk1
  have hx1 : x < 1 :=
    (sq_lt_sq₀ hx0.le (by norm_num)).mp (by simpa using hxSqLt)
  have hx1le : x ≤ 1 := hx1.le
  have hxFourthLe : x ^ 4 ≤ 1 := by
    nlinarith [(sq_le_sq₀ hx0.le (by norm_num)).2 hx1le,
      sq_nonneg (x ^ 2), sq_nonneg (1 - x ^ 2)]
  have hpow : 8 * x ^ 5 ≤ 8 * x := by
    calc
      8 * x ^ 5 = (8 * x) * x ^ 4 := by ring
      _ ≤ (8 * x) * 1 :=
        mul_le_mul_of_nonneg_left hxFourthLe (by positivity)
      _ = 8 * x := by ring
  have hpoly : 0 < x ^ 4 + x ^ 3 + x ^ 2 + 2 - 3 * x := by
    nlinarith [sq_nonneg (x - 1), pow_nonneg hx0.le 3, pow_nonneg hx0.le 4,
      sub_pos.mpr hx1]
  have hfactor : 0 < -8 * x ^ 5 + x ^ 4 + x ^ 3 + x ^ 2 + 5 * x + 2 := by
    nlinarith
  have hid :
      2 * ((1 - xiShiftTangentResponseFromBase k) -
          3 * gammaJordanXiResponseGapFromBase k) =
        (1 - x) *
          (-8 * x ^ 5 + x ^ 4 + x ^ 3 + x ^ 2 + 5 * x + 2) := by
    unfold gammaJordanXiResponseGapFromBase gammaJordanResponseFromBase
      xiShiftTangentResponseFromBase
    change 2 * ((1 - k * (2 * k ^ 2 - 1)) -
      3 * (x * (3 * k ^ 2 - 1) / 2 - k * (2 * k ^ 2 - 1))) = _
    rw [← hxSq]
    ring
  nlinarith [mul_pos (sub_pos.mpr hx1) hfactor]

/-- **Quantitative response metric.**  Off the prime diagonal the Gamma/Xi response gap lies
strictly between one eighth and one sixth of the squared all-depth tangent Hilbert distance. -/
theorem gammaJordanXiPrimeResponseGap_bilipschitz_tangentDistanceSq
    {p q : Nat.Primes} (hpq : p ≠ q) :
    (1 / 8 : ℝ) * gammaSewnXiShiftEndpointUnitTangentDistanceSq p q <
        gammaJordanXiPrimeResponseGap p q ∧
      gammaJordanXiPrimeResponseGap p q <
        (1 / 6 : ℝ) * gammaSewnXiShiftEndpointUnitTangentDistanceSq p q := by
  let k := gammaXiFisherBaseCorrelation p q
  have hk0 : 0 < k := gammaXiFisherBaseCorrelation_pos p q
  have hkle : k ≤ 1 := gammaXiFisherBaseCorrelation_le_one p q
  have hkne : k ≠ 1 := by
    exact fun h => hpq ((gammaXiFisherBaseCorrelation_eq_one_iff p q).mp h)
  have hk1 : k < 1 := lt_of_le_of_ne hkle hkne
  have hkLoc : 3 / 4 < k ^ 2 :=
    gammaXiFisherBaseCorrelation_sq_gt_three_fourths p q
  have hlower :=
    one_fourth_tangentResponseDefect_lt_gammaJordanXiResponseGapFromBase
      hk0 hk1 hkLoc
  have hupper :=
    gammaJordanXiResponseGapFromBase_lt_one_third_tangentResponseDefect
      hk0 hk1
  rw [gammaJordanXiPrimeResponseGap,
    gammaSewnXiShiftEndpointUnitTangentDistanceSq_eq,
    gammaSewnXiShiftEndpointUnitTangentKernel_eq_responseFromBase]
  change (1 / 8 : ℝ) * (2 * (1 - xiShiftTangentResponseFromBase k)) <
      gammaJordanXiResponseGapFromBase k ∧
    gammaJordanXiResponseGapFromBase k <
      (1 / 6 : ℝ) * (2 * (1 - xiShiftTangentResponseFromBase k))
  constructor <;> nlinarith

/-- Finite response-gap graph-Laplacian energy. -/
def gammaJordanXiFiniteResponseGapLaplacian
    (S : Finset Nat.Primes) (slope : Nat.Primes → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ p ∈ S, ∑ q ∈ S,
    gammaJordanXiPrimeResponseGap p q * (slope p - slope q) ^ 2

theorem gammaJordanXiFiniteResponseGapLaplacian_nonneg
    (S : Finset Nat.Primes) (slope : Nat.Primes → ℝ) :
    0 ≤ gammaJordanXiFiniteResponseGapLaplacian S slope := by
  unfold gammaJordanXiFiniteResponseGapLaplacian
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro p _hp
  apply Finset.sum_nonneg
  intro q _hq
  exact mul_nonneg (gammaJordanXiPrimeResponseGap_nonneg p q) (sq_nonneg _)

/-- Every nonconstant finite prime slope has strictly positive response-gap dispersion. -/
theorem gammaJordanXiFiniteResponseGapLaplacian_pos
    {S : Finset Nat.Primes} {slope : Nat.Primes → ℝ}
    (hnonconstant : ∃ p ∈ S, ∃ q ∈ S, slope p ≠ slope q) :
    0 < gammaJordanXiFiniteResponseGapLaplacian S slope := by
  rcases hnonconstant with ⟨p, hp, q, hq, hpqSlope⟩
  have hpq : p ≠ q := by
    intro hpq
    apply hpqSlope
    rw [hpq]
  have hterm : 0 <
      gammaJordanXiPrimeResponseGap p q * (slope p - slope q) ^ 2 :=
    mul_pos ((gammaJordanXiPrimeResponseGap_pos_iff p q).2 hpq)
      (sq_pos_of_ne_zero (sub_ne_zero.mpr hpqSlope))
  unfold gammaJordanXiFiniteResponseGapLaplacian
  apply mul_pos (by norm_num)
  apply Finset.sum_pos'
  · intro i _hi
    apply Finset.sum_nonneg
    intro j _hj
    exact mul_nonneg (gammaJordanXiPrimeResponseGap_nonneg i j) (sq_nonneg _)
  · refine ⟨p, hp, ?_⟩
    apply Finset.sum_pos'
    · intro j _hj
      exact mul_nonneg (gammaJordanXiPrimeResponseGap_nonneg p j) (sq_nonneg _)
    · exact ⟨q, hq, hterm⟩

end RHTower
