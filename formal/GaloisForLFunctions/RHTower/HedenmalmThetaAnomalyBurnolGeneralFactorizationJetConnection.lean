import GaloisForLFunctions.RHTower.HedenmalmThetaAnomalyBurnolMultiplicativeJetConnection

/-!
# General Burnol factorization-jet connection

The completed Burnol cells satisfy a multiplicative sine-addition law for every factorization
`m * n`, not only `6 = 2 * 3`.  Differentiating its two coefficients and contracting their jets
against the opposite cells gives the full spectral coordinate times the pair-frame energy.

The construction is symmetric under exchange of the two factors.  Wherever a pair frame is
nonzero, its normalized connection equals the spectral coordinate and therefore agrees with every
other nondegenerate factorization frame.  This closes prime-swap sign holonomy for the Hermitian
connection: determinant-line gauges are oriented, but the multiplicative jet connection is
commutative.
-/

open Complex Real Filter Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Sine-addition coefficient carrying the `m` cell into the `m*n` cell. -/
def burnolFactorizationLeftCoefficient (m n : ℕ) (z : ℂ) : ℂ :=
  thetaIntegerShiftScale (m * n) / thetaIntegerShiftScale m *
    Complex.cos (z * ((Real.log n / 2 : ℝ) : ℂ))

/-- Sine-addition coefficient carrying the `n` cell into the `m*n` cell. -/
def burnolFactorizationRightCoefficient (m n : ℕ) (z : ℂ) : ℂ :=
  thetaIntegerShiftScale (m * n) / thetaIntegerShiftScale n *
    Complex.cos (z * ((Real.log m / 2 : ℝ) : ℂ))

/-- **General completed Burnol factorization syzygy.** -/
theorem burnolCompletedCenteredMultiplier_mul_eq_factorization
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) (z : ℂ) :
    burnolCompletedCenteredMultiplier (m * n) z =
      burnolFactorizationLeftCoefficient m n z *
          burnolCompletedCenteredMultiplier m z +
        burnolFactorizationRightCoefficient m n z *
          burnolCompletedCenteredMultiplier n z := by
  have hm0 : 0 < m := Nat.zero_lt_of_lt hm
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hmn0 : 0 < m * n := Nat.mul_pos hm0 hn0
  have hsm : thetaIntegerShiftScale m ≠ 0 := thetaIntegerShiftScale_ne_zero hm0
  have hsn : thetaIntegerShiftScale n ≠ 0 := thetaIntegerShiftScale_ne_zero hn0
  have hsmn : thetaIntegerShiftScale (m * n) ≠ 0 :=
    thetaIntegerShiftScale_ne_zero hmn0
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hlog : Real.log ((m * n : ℕ) : ℝ) = Real.log m + Real.log n := by
    rw [Nat.cast_mul, Real.log_mul hmR.ne' hnR.ne']
  rcases eq_or_ne z 0 with rfl | hz
  · rw [burnolCompletedCenteredMultiplier_zero,
      burnolCompletedCenteredMultiplier_zero,
      burnolCompletedCenteredMultiplier_zero,
      burnolFactorizationLeftCoefficient, burnolFactorizationRightCoefficient]
    simp only [zero_mul, Complex.cos_zero, mul_one]
    rw [hlog]
    push_cast
    field_simp [hsm, hsn, hsmn]
  · rw [burnolCompletedCenteredMultiplier_eq_scale_sin_div (m * n) hz,
      burnolCompletedCenteredMultiplier_eq_scale_sin_div m hz,
      burnolCompletedCenteredMultiplier_eq_scale_sin_div n hz,
      burnolFactorizationLeftCoefficient, burnolFactorizationRightCoefficient]
    have hphase :
        z * ((Real.log ((m * n : ℕ) : ℝ) / 2 : ℝ) : ℂ) =
          z * ((Real.log m / 2 : ℝ) : ℂ) +
            z * ((Real.log n / 2 : ℝ) : ℂ) := by
      rw [hlog]
      push_cast
      ring
    rw [hphase, Complex.sin_add]
    field_simp [hsm, hsn, hsmn, hz]

/-- Literal derivative of the coefficient carrying the `m` cell into the product cell. -/
def burnolFactorizationLeftCoefficientJet (m n : ℕ) (z : ℂ) : ℂ :=
  -(thetaIntegerShiftScale (m * n) / thetaIntegerShiftScale m) *
    ((Real.log n / 2 : ℝ) : ℂ) *
      Complex.sin (z * ((Real.log n / 2 : ℝ) : ℂ))

/-- Literal derivative of the coefficient carrying the `n` cell into the product cell. -/
def burnolFactorizationRightCoefficientJet (m n : ℕ) (z : ℂ) : ℂ :=
  -(thetaIntegerShiftScale (m * n) / thetaIntegerShiftScale n) *
    ((Real.log m / 2 : ℝ) : ℂ) *
      Complex.sin (z * ((Real.log m / 2 : ℝ) : ℂ))

theorem hasDerivAt_burnolFactorizationLeftCoefficient (m n : ℕ) (z : ℂ) :
    HasDerivAt (burnolFactorizationLeftCoefficient m n)
      (burnolFactorizationLeftCoefficientJet m n z) z := by
  have h := (((hasDerivAt_id z).mul_const
    ((Real.log n / 2 : ℝ) : ℂ)).ccos).const_mul
      (thetaIntegerShiftScale (m * n) / thetaIntegerShiftScale m)
  convert h using 1 <;>
    first | rfl | (rw [burnolFactorizationLeftCoefficientJet]; simp only [id_eq]; ring)

theorem hasDerivAt_burnolFactorizationRightCoefficient (m n : ℕ) (z : ℂ) :
    HasDerivAt (burnolFactorizationRightCoefficient m n)
      (burnolFactorizationRightCoefficientJet m n z) z := by
  have h := (((hasDerivAt_id z).mul_const
    ((Real.log m / 2 : ℝ) : ℂ)).ccos).const_mul
      (thetaIntegerShiftScale (m * n) / thetaIntegerShiftScale n)
  convert h using 1 <;>
    first | rfl | (rw [burnolFactorizationRightCoefficientJet]; simp only [id_eq]; ring)

/-- Literal first-jet form of the general multiplicative factorization syzygy. -/
theorem deriv_burnolCompletedCenteredMultiplier_mul_eq_factorization
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) (z : ℂ) :
    deriv (burnolCompletedCenteredMultiplier (m * n)) z =
      burnolFactorizationLeftCoefficientJet m n z *
          burnolCompletedCenteredMultiplier m z +
        burnolFactorizationLeftCoefficient m n z *
          deriv (burnolCompletedCenteredMultiplier m) z +
      (burnolFactorizationRightCoefficientJet m n z *
          burnolCompletedCenteredMultiplier n z +
        burnolFactorizationRightCoefficient m n z *
          deriv (burnolCompletedCenteredMultiplier n) z) := by
  have hmn := (differentiable_burnolCompletedCenteredMultiplier (m * n) z).hasDerivAt
  have hm' := (differentiable_burnolCompletedCenteredMultiplier m z).hasDerivAt
  have hn' := (differentiable_burnolCompletedCenteredMultiplier n z).hasDerivAt
  have hright :=
    ((hasDerivAt_burnolFactorizationLeftCoefficient m n z).mul hm').add
      ((hasDerivAt_burnolFactorizationRightCoefficient m n z).mul hn')
  have heq : (fun w => burnolCompletedCenteredMultiplier (m * n) w) =ᶠ[nhds z]
      fun w => burnolFactorizationLeftCoefficient m n w *
          burnolCompletedCenteredMultiplier m w +
        burnolFactorizationRightCoefficient m n w *
          burnolCompletedCenteredMultiplier n w := by
    filter_upwards with w
    exact burnolCompletedCenteredMultiplier_mul_eq_factorization hm hn w
  exact (hmn.congr_of_eventuallyEq heq.symm).unique hright

/-- Weight converting the left coefficient jet into spectral multiplication by the `n` cell. -/
def burnolFactorizationLeftJetWeight (m n : ℕ) : ℂ :=
  ((thetaIntegerShiftScale (m * n) / thetaIntegerShiftScale m) *
      ((Real.log n / 2 : ℝ) : ℂ)) /
    (2 * thetaIntegerShiftScale n)

/-- Weight converting the right coefficient jet into spectral multiplication by the `m` cell. -/
def burnolFactorizationRightJetWeight (m n : ℕ) : ℂ :=
  ((thetaIntegerShiftScale (m * n) / thetaIntegerShiftScale n) *
      ((Real.log m / 2 : ℝ) : ℂ)) /
    (2 * thetaIntegerShiftScale m)

theorem burnolFactorizationLeftJetWeight_ne_zero
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) :
    burnolFactorizationLeftJetWeight m n ≠ 0 := by
  have hm0 : 0 < m := Nat.zero_lt_of_lt hm
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hlog : ((Real.log n / 2 : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (div_ne_zero (Real.log_pos (by exact_mod_cast hn)).ne' (by norm_num))
  exact div_ne_zero
    (mul_ne_zero
      (div_ne_zero (thetaIntegerShiftScale_ne_zero (Nat.mul_pos hm0 hn0))
        (thetaIntegerShiftScale_ne_zero hm0)) hlog)
    (mul_ne_zero (by norm_num) (thetaIntegerShiftScale_ne_zero hn0))

theorem burnolFactorizationRightJetWeight_ne_zero
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) :
    burnolFactorizationRightJetWeight m n ≠ 0 := by
  have hm0 : 0 < m := Nat.zero_lt_of_lt hm
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hlog : ((Real.log m / 2 : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (div_ne_zero (Real.log_pos (by exact_mod_cast hm)).ne' (by norm_num))
  exact div_ne_zero
    (mul_ne_zero
      (div_ne_zero (thetaIntegerShiftScale_ne_zero (Nat.mul_pos hm0 hn0))
        (thetaIntegerShiftScale_ne_zero hn0)) hlog)
    (mul_ne_zero (by norm_num) (thetaIntegerShiftScale_ne_zero hm0))

/-- Left coefficient jet is division-free spectral multiplication by the opposite factor cell. -/
theorem burnolFactorizationLeftCoefficientJet_eq
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) (z : ℂ) :
    burnolFactorizationLeftCoefficientJet m n z =
      -burnolFactorizationLeftJetWeight m n * z *
        burnolCompletedCenteredMultiplier n z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [burnolFactorizationLeftCoefficientJet]
  · rw [burnolCompletedCenteredMultiplier_eq_scale_sin_div n hz]
    rw [burnolFactorizationLeftCoefficientJet, burnolFactorizationLeftJetWeight]
    have hm0 : 0 < m := Nat.zero_lt_of_lt hm
    have hn0 : 0 < n := Nat.zero_lt_of_lt hn
    field_simp [thetaIntegerShiftScale_ne_zero hm0,
      thetaIntegerShiftScale_ne_zero hn0,
      thetaIntegerShiftScale_ne_zero (Nat.mul_pos hm0 hn0), hz]

/-- Right coefficient jet is division-free spectral multiplication by the opposite factor cell. -/
theorem burnolFactorizationRightCoefficientJet_eq
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) (z : ℂ) :
    burnolFactorizationRightCoefficientJet m n z =
      -burnolFactorizationRightJetWeight m n * z *
        burnolCompletedCenteredMultiplier m z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [burnolFactorizationRightCoefficientJet]
  · rw [burnolCompletedCenteredMultiplier_eq_scale_sin_div m hz]
    rw [burnolFactorizationRightCoefficientJet, burnolFactorizationRightJetWeight]
    have hm0 : 0 < m := Nat.zero_lt_of_lt hm
    have hn0 : 0 < n := Nat.zero_lt_of_lt hn
    field_simp [thetaIntegerShiftScale_ne_zero hm0,
      thetaIntegerShiftScale_ne_zero hn0,
      thetaIntegerShiftScale_ne_zero (Nat.mul_pos hm0 hn0), hz]

/-- Hermitian energy of the two factor cells. -/
def burnolFactorizationPairFrameEnergy (m n : ℕ) (z : ℂ) : ℝ :=
  Complex.normSq (burnolCompletedCenteredMultiplier m z) +
    Complex.normSq (burnolCompletedCenteredMultiplier n z)

/-- Hermitian contraction of the two general factorization coefficient jets. -/
def burnolFactorizationJetConnectionNumerator (m n : ℕ) (z : ℂ) : ℂ :=
  (burnolFactorizationLeftCoefficientJet m n z /
      burnolFactorizationLeftJetWeight m n) *
        (starRingEnd ℂ) (burnolCompletedCenteredMultiplier n z) +
    (burnolFactorizationRightCoefficientJet m n z /
      burnolFactorizationRightJetWeight m n) *
        (starRingEnd ℂ) (burnolCompletedCenteredMultiplier m z)

/-- **Universal division-free multiplicative-jet connection law.** -/
theorem burnolFactorizationJetConnectionNumerator_eq
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) (z : ℂ) :
    burnolFactorizationJetConnectionNumerator m n z =
      -z * (burnolFactorizationPairFrameEnergy m n z : ℂ) := by
  rw [burnolFactorizationJetConnectionNumerator,
    burnolFactorizationLeftCoefficientJet_eq hm hn,
    burnolFactorizationRightCoefficientJet_eq hm hn,
    burnolFactorizationPairFrameEnergy]
  push_cast
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  field_simp [burnolFactorizationLeftJetWeight_ne_zero hm hn,
    burnolFactorizationRightJetWeight_ne_zero hm hn]
  ring

/-- Normalized connection of one multiplicative factorization frame. -/
def burnolFactorizationJetSpectralConnection (m n : ℕ) (z : ℂ) : ℂ :=
  -burnolFactorizationJetConnectionNumerator m n z /
    (burnolFactorizationPairFrameEnergy m n z : ℂ)

/-- Every nondegenerate factorization frame reconstructs the full spectral coordinate. -/
theorem burnolFactorizationJetSpectralConnection_eq
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) {z : ℂ}
    (hE : burnolFactorizationPairFrameEnergy m n z ≠ 0) :
    burnolFactorizationJetSpectralConnection m n z = z := by
  rw [burnolFactorizationJetSpectralConnection,
    burnolFactorizationJetConnectionNumerator_eq hm hn]
  have hEC : (burnolFactorizationPairFrameEnergy m n z : ℂ) ≠ 0 := by
    exact_mod_cast hE
  field_simp [hEC]

/-! ## Commutativity and factorization independence -/

theorem burnolFactorizationLeftCoefficient_swap (m n : ℕ) (z : ℂ) :
    burnolFactorizationLeftCoefficient m n z =
      burnolFactorizationRightCoefficient n m z := by
  simp only [burnolFactorizationLeftCoefficient, burnolFactorizationRightCoefficient,
    Nat.mul_comm]

theorem burnolFactorizationLeftCoefficientJet_swap (m n : ℕ) (z : ℂ) :
    burnolFactorizationLeftCoefficientJet m n z =
      burnolFactorizationRightCoefficientJet n m z := by
  simp only [burnolFactorizationLeftCoefficientJet, burnolFactorizationRightCoefficientJet,
    Nat.mul_comm]

theorem burnolFactorizationLeftJetWeight_swap (m n : ℕ) :
    burnolFactorizationLeftJetWeight m n = burnolFactorizationRightJetWeight n m := by
  simp only [burnolFactorizationLeftJetWeight, burnolFactorizationRightJetWeight, Nat.mul_comm]

theorem burnolFactorizationPairFrameEnergy_swap (m n : ℕ) (z : ℂ) :
    burnolFactorizationPairFrameEnergy m n z =
      burnolFactorizationPairFrameEnergy n m z := by
  rw [burnolFactorizationPairFrameEnergy, burnolFactorizationPairFrameEnergy]
  ring

/-- Hermitian jet connection is commutative in the two multiplicative factors. -/
theorem burnolFactorizationJetConnectionNumerator_swap
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) (z : ℂ) :
    burnolFactorizationJetConnectionNumerator m n z =
      burnolFactorizationJetConnectionNumerator n m z := by
  rw [burnolFactorizationJetConnectionNumerator_eq hm hn,
    burnolFactorizationJetConnectionNumerator_eq hn hm,
    burnolFactorizationPairFrameEnergy_swap]

/-- Any two nondegenerate multiplicative factorizations yield the same normalized connection. -/
theorem burnolFactorizationJetSpectralConnection_independent
    {m n r s : ℕ} (hm : 1 < m) (hn : 1 < n) (hr : 1 < r) (hs : 1 < s)
    {z : ℂ} (hEmn : burnolFactorizationPairFrameEnergy m n z ≠ 0)
    (hErs : burnolFactorizationPairFrameEnergy r s z ≠ 0) :
    burnolFactorizationJetSpectralConnection m n z =
      burnolFactorizationJetSpectralConnection r s z := by
  rw [burnolFactorizationJetSpectralConnection_eq hm hn hEmn,
    burnolFactorizationJetSpectralConnection_eq hr hs hErs]

/-! ## Recovery of P-G118 -/

theorem burnolFactorizationJetConnectionNumerator_two_three (z : ℂ) :
    burnolFactorizationJetConnectionNumerator 2 3 z =
      burnolMultiplicativeJetConnectionNumerator z := rfl

theorem burnolFactorizationPairFrameEnergy_two_three (z : ℂ) :
    burnolFactorizationPairFrameEnergy 2 3 z = burnolTwoPrimeFrameEnergy z := rfl

theorem burnolFactorizationJetSpectralConnection_two_three (z : ℂ) :
    burnolFactorizationJetSpectralConnection 2 3 z =
      burnolMultiplicativeJetSpectralConnection z := rfl

end

end RHTower.HedenmalmThetaSource
