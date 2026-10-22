import GaloisForLFunctions.RHTower.HardyZThetaTrace
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmLocalFrameObstruction
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspInversionBoundaryValue
import GaloisForLFunctions.RHTower.XiHedenmalmDeBrangesSeam
import GaloisForLFunctions.RHTower.XiHedenmalmValueConstraint
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangleExhaustion

/-!
# Xi Hedenmalm divided jets as explicit theta-source moments

Every center value in the removable Hedenmalm divided chain is the corresponding factorially
normalized Xi jet, and every such jet in the zero strip is an explicit theta-cusp
Fourier--Laplace moment.  This gives an exact all-order source classification of analytic
multiplicity together with functional and Schwarz value reflections.

At first order, the exact Xi/Hardy jet identifies simplicity of a real centered Xi zero with
nonvanishing of the positive theta source's first sine moment.  Under RH every centered Xi divisor
is real, so this pointwise law is equivalent to global Xi simplicity and to the Hedenmalm first
quotient value constraint.  These are unconditional equivalences; they prove neither RH nor
simplicity.
-/

open Complex Real MeasureTheory Set

noncomputable section

namespace RHTower

/-- Every centered Xi zero lies in the theta-cusp Fourier--Laplace strip, discharging the strip
premise needed to identify both values and first derivatives with `XiC`. -/
theorem xiC_zero_mem_thetaCuspFourierLaplaceStrip {alpha : ℂ}
    (halpha : XiC alpha = 0) :
    alpha ∈ thetaCuspFourierLaplaceStrip := by
  have hhalf := xiC_zero_im_mem_openHalf halpha
  rw [thetaCuspFourierLaplaceStrip]
  constructor <;> linarith [hhalf.1, hhalf.2]

/-- Every centered Xi divisor support point lies in the theta Fourier--Laplace strip.  This
packages both the multiplicity-copy witness and the zero-to-strip discharge. -/
theorem xiSpectralPointSupport_mem_thetaCuspFourierLaplaceStrip
    (rho : XiDivisorSupport) :
    xiSpectralPointSupport rho ∈ thetaCuspFourierLaplaceStrip := by
  let q : XiZeroCopy :=
    ⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩
  apply xiC_zero_mem_thetaCuspFourierLaplaceStrip
  simpa only [q, xiSpectralPoint_eq_support] using XiC_xiSpectralPoint_eq_zero q

/-- **All-order Hedenmalm/source reflection.**  At every point of the theta Fourier--Laplace
strip, the center value after `k` removable Xi quotients is the explicit `(-i x)^k` source
moment divided by `k!`.  The first-quotient identity below is its `k = 1` specialization. -/
theorem xiThetaDividedChain_self_eq_integral_thetaCuspFourierLaplaceJet_div_factorial
    {alpha : ℂ} (halpha : alpha ∈ thetaCuspFourierLaplaceStrip) (k : ℕ) :
    xiThetaDividedChain alpha k alpha =
      (∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand k alpha x) /
        k.factorial := by
  rw [xiThetaDividedChain_self_eq_iteratedDeriv_div_factorial,
    iteratedDeriv_XiC_eq_integral_thetaCuspFourierLaplaceJet k halpha]

/-- Every centered Xi divisor satisfies the all-order divided-chain/source law with no remaining
strip hypothesis. -/
theorem
    xiThetaDividedChain_self_eq_integral_thetaCuspFourierLaplaceJet_div_factorial_of_zero
    {alpha : ℂ} (halpha : XiC alpha = 0) (k : ℕ) :
    xiThetaDividedChain alpha k alpha =
      (∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand k alpha x) /
        k.factorial :=
  xiThetaDividedChain_self_eq_integral_thetaCuspFourierLaplaceJet_div_factorial
    (xiC_zero_mem_thetaCuspFourierLaplaceStrip halpha) k

/-- **Exact Xi multiplicity-by-source classification.**  A divisor support point has analytic
multiplicity `k` exactly when its explicit theta Fourier--Laplace moments of orders below `k`
vanish and its order-`k` moment does not.  This removes both analytic derivatives and abstract
divided quotients from the multiplicity interface. -/
theorem xiSupportMultiplicity_eq_iff_thetaCuspFourierLaplaceJet
    (rho : XiDivisorSupport) (k : ℕ) :
    xiSupportMultiplicity rho = k ↔
      (∀ j < k,
        (∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand j
          (xiSpectralPointSupport rho) x) = 0) ∧
      (∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand k
        (xiSpectralPointSupport rho) x) ≠ 0 := by
  have hstrip := xiSpectralPointSupport_mem_thetaCuspFourierLaplaceStrip rho
  have hjet (j : ℕ) :
      iteratedDeriv j XiC (xiSpectralPointSupport rho) =
        ∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand j
          (xiSpectralPointSupport rho) x :=
    iteratedDeriv_XiC_eq_integral_thetaCuspFourierLaplaceJet j hstrip
  simpa only [hjet] using xiSupportMultiplicity_eq_iff_iteratedDeriv rho k

/-- Every jet of the unnormalized one-sided theta reflection defect below the Xi multiplicity
vanishes, for every logarithmic cut. -/
theorem iteratedDeriv_thetaCuspBoundaryReflectionDefect_eq_zero_before_supportMultiplicity
    (rho : XiDivisorSupport) {k : ℕ}
    (hk : k < xiSupportMultiplicity rho) (x : ℝ) :
    iteratedDeriv k (thetaCuspBoundaryReflectionDefect x)
      (xiSpectralPointSupport rho) = 0 := by
  have hstrip := xiSpectralPointSupport_mem_thetaCuspFourierLaplaceStrip rho
  have habs : |(xiSpectralPointSupport rho).im| < 1 := abs_lt.mpr hstrip
  rw [iteratedDeriv_thetaCuspBoundaryReflectionDefect k habs x]
  apply Finset.sum_eq_zero
  intro i hi
  have hsub : k - i < xiSupportMultiplicity rho :=
    lt_of_le_of_lt (Nat.sub_le k i) hk
  rw [iteratedDeriv_XiC_eq_zero_before_supportMultiplicity rho hsub]
  ring

/-- At the exact Xi multiplicity, the first surviving boundary-reflection jet is the nonvanishing
cut exponential times the corresponding explicit theta Fourier--Laplace moment. -/
theorem iteratedDeriv_thetaCuspBoundaryReflectionDefect_at_supportMultiplicity
    (rho : XiDivisorSupport) (x : ℝ) :
    iteratedDeriv (xiSupportMultiplicity rho)
        (thetaCuspBoundaryReflectionDefect x)
        (xiSpectralPointSupport rho) =
      Complex.exp (I * xiSpectralPointSupport rho * (x : ℂ)) *
        ∫ y : ℝ, thetaCuspFourierLaplaceJetIntegrand
          (xiSupportMultiplicity rho) (xiSpectralPointSupport rho) y := by
  have hpos := xiSupportMultiplicity_pos rho
  have hstrip := xiSpectralPointSupport_mem_thetaCuspFourierLaplaceStrip rho
  have habs : |(xiSpectralPointSupport rho).im| < 1 := abs_lt.mpr hstrip
  rw [iteratedDeriv_thetaCuspBoundaryReflectionDefect
    (xiSupportMultiplicity rho) habs x]
  rw [Finset.sum_eq_single 0]
  · simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul,
      Nat.sub_zero]
    rw [iteratedDeriv_XiC_eq_integral_thetaCuspFourierLaplaceJet
      (xiSupportMultiplicity rho) hstrip]
  · intro i hi hi0
    have hi : 0 < i := Nat.pos_of_ne_zero hi0
    have hsub : xiSupportMultiplicity rho - i < xiSupportMultiplicity rho :=
      Nat.sub_lt hpos hi
    rw [iteratedDeriv_XiC_eq_zero_before_supportMultiplicity rho hsub]
    ring
  · simp

/-- The boundary-reflection jet at the exact Xi multiplicity never vanishes, independently of
the logarithmic cut. -/
theorem iteratedDeriv_thetaCuspBoundaryReflectionDefect_ne_zero_at_supportMultiplicity
    (rho : XiDivisorSupport) (x : ℝ) :
    iteratedDeriv (xiSupportMultiplicity rho)
      (thetaCuspBoundaryReflectionDefect x)
      (xiSpectralPointSupport rho) ≠ 0 := by
  rw [iteratedDeriv_thetaCuspBoundaryReflectionDefect_at_supportMultiplicity]
  exact mul_ne_zero (Complex.exp_ne_zero _)
    ((xiSupportMultiplicity_eq_iff_thetaCuspFourierLaplaceJet rho
      (xiSupportMultiplicity rho)).mp rfl).2

/-- **Boundary-reflection multiplicity classification.**  For every logarithmic cut, a centered
Xi divisor has multiplicity `k` exactly when the unnormalized one-sided source reflection defect
has vanishing jets below `k` and a nonzero `k`-th jet.  Thus cut covariance changes the terminal
value only by a nonzero exponential gauge and cannot alter the detected multiplicity. -/
theorem xiSupportMultiplicity_eq_iff_thetaCuspBoundaryReflectionDefectJet
    (rho : XiDivisorSupport) (x : ℝ) (k : ℕ) :
    xiSupportMultiplicity rho = k ↔
      (∀ j < k,
        iteratedDeriv j (thetaCuspBoundaryReflectionDefect x)
          (xiSpectralPointSupport rho) = 0) ∧
      iteratedDeriv k (thetaCuspBoundaryReflectionDefect x)
        (xiSpectralPointSupport rho) ≠ 0 := by
  constructor
  · intro hm
    subst k
    exact ⟨fun _ hj =>
      iteratedDeriv_thetaCuspBoundaryReflectionDefect_eq_zero_before_supportMultiplicity
        rho hj x,
      iteratedDeriv_thetaCuspBoundaryReflectionDefect_ne_zero_at_supportMultiplicity rho x⟩
  · rintro ⟨hvanish, hnonzero⟩
    apply Nat.le_antisymm
    · by_contra hle
      have hk : k < xiSupportMultiplicity rho := Nat.lt_of_not_ge hle
      exact hnonzero
        (iteratedDeriv_thetaCuspBoundaryReflectionDefect_eq_zero_before_supportMultiplicity
          rho hk x)
    · by_contra hle
      have hk : xiSupportMultiplicity rho < k := Nat.lt_of_not_ge hle
      exact iteratedDeriv_thetaCuspBoundaryReflectionDefect_ne_zero_at_supportMultiplicity rho x
        (hvanish (xiSupportMultiplicity rho) hk)

/-- **Graded source-moment reflection.**  The explicit order-`k` theta Fourier--Laplace moment
at `-alpha` is `(-1)^k` times its value at `alpha`. -/
theorem integral_thetaCuspFourierLaplaceJet_neg
    (k : ℕ) {alpha : ℂ} (halpha : alpha ∈ thetaCuspFourierLaplaceStrip) :
    (∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand k (-alpha) x) =
      (-1 : ℂ) ^ k *
        ∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand k alpha x := by
  have hneg : -alpha ∈ thetaCuspFourierLaplaceStrip := by
    change -1 < alpha.im ∧ alpha.im < 1 at halpha
    change -1 < (-alpha).im ∧ (-alpha).im < 1
    simp only [neg_im]
    constructor <;> linarith [halpha.1, halpha.2]
  rw [← iteratedDeriv_XiC_eq_integral_thetaCuspFourierLaplaceJet k hneg,
    ← iteratedDeriv_XiC_eq_integral_thetaCuspFourierLaplaceJet k halpha,
    iteratedDeriv_XiC_neg]

/-- Every centered Xi jet is Schwarz-real: conjugating the base point conjugates the value. -/
theorem iteratedDeriv_XiC_conj (k : ℕ) (z : ℂ) :
    iteratedDeriv k XiC ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (iteratedDeriv k XiC z) := by
  have hreal : (starRingEnd ℂ) ∘ XiC ∘ (starRingEnd ℂ) = XiC := by
    funext w
    simp only [Function.comp_apply, xiHedenmalm_XiC_conj]
    simp
  calc
    iteratedDeriv k XiC ((starRingEnd ℂ) z) =
        iteratedDeriv k ((starRingEnd ℂ) ∘ XiC ∘ (starRingEnd ℂ))
          ((starRingEnd ℂ) z) := by rw [hreal]
    _ = (starRingEnd ℂ) (iteratedDeriv k XiC z) := by
      rw [iteratedDeriv_conj_conj]
      simp

/-- Schwarz conjugation of the spectral point conjugates every explicit theta source moment. -/
theorem integral_thetaCuspFourierLaplaceJet_conj
    (k : ℕ) {alpha : ℂ} (halpha : alpha ∈ thetaCuspFourierLaplaceStrip) :
    (∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand k
      ((starRingEnd ℂ) alpha) x) =
      (starRingEnd ℂ)
        (∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand k alpha x) := by
  have hconj : (starRingEnd ℂ) alpha ∈ thetaCuspFourierLaplaceStrip := by
    change -1 < alpha.im ∧ alpha.im < 1 at halpha
    change -1 < ((starRingEnd ℂ) alpha).im ∧
      ((starRingEnd ℂ) alpha).im < 1
    simp only [conj_im]
    constructor <;> linarith [halpha.1, halpha.2]
  rw [← iteratedDeriv_XiC_eq_integral_thetaCuspFourierLaplaceJet k hconj,
    ← iteratedDeriv_XiC_eq_integral_thetaCuspFourierLaplaceJet k halpha,
    iteratedDeriv_XiC_conj]

/-- The combined centered functional and Schwarz reflection sends the order-`k` source moment to
`(-1)^k` times its conjugate. -/
theorem integral_thetaCuspFourierLaplaceJet_neg_conj
    (k : ℕ) {alpha : ℂ} (halpha : alpha ∈ thetaCuspFourierLaplaceStrip) :
    (∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand k
      (-(starRingEnd ℂ) alpha) x) =
      (-1 : ℂ) ^ k * (starRingEnd ℂ)
        (∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand k alpha x) := by
  have hconj : (starRingEnd ℂ) alpha ∈ thetaCuspFourierLaplaceStrip := by
    change -1 < alpha.im ∧ alpha.im < 1 at halpha
    change -1 < ((starRingEnd ℂ) alpha).im ∧
      ((starRingEnd ℂ) alpha).im < 1
    simp only [conj_im]
    constructor <;> linarith [halpha.1, halpha.2]
  rw [integral_thetaCuspFourierLaplaceJet_neg k hconj,
    integral_thetaCuspFourierLaplaceJet_conj k halpha]

/-- **Complex/real all-order source seam.**  On the real spectral axis, the two-sided complex
Fourier--Laplace jet moment is exactly the complexification of the existing positive-half-line
cosine-phase derivative integral.  This simultaneously subsumes the cosine value identity and
the first sine-moment derivative identity. -/
theorem integral_thetaCuspFourierLaplaceJet_ofReal
    (k : ℕ) (t : ℝ) :
    (∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand k (t : ℂ) x) =
      (thetaCuspCosineDerivativeIntegral k t : ℂ) := by
  have hstrip : (t : ℂ) ∈ thetaCuspFourierLaplaceStrip := by
    change -1 < (0 : ℝ) ∧ (0 : ℝ) < 1
    norm_num
  have hreal : iteratedDeriv k Xi t =
      thetaCuspCosineDerivativeIntegral k t := by
    rw [show Xi = thetaCuspCosineRepresentation by
      funext u
      exact Xi_eq_thetaCuspCosineRepresentation u,
      iteratedDeriv_thetaCuspCosineRepresentation_eq_integral]
  rw [← iteratedDeriv_XiC_eq_integral_thetaCuspFourierLaplaceJet k hstrip,
    iteratedDeriv_XiC_ofReal, hreal]

/-- **Real positive-half multiplicity interface.**  If a centered Xi divisor support point is
real, its exact analytic multiplicity is the first order at which the existing positive-half
cosine-phase derivative integral is nonzero. -/
theorem xiSupportMultiplicity_eq_iff_thetaCuspCosineDerivativeIntegral
    (rho : XiDivisorSupport) {t : ℝ}
    (ht : xiSpectralPointSupport rho = (t : ℂ)) (k : ℕ) :
    xiSupportMultiplicity rho = k ↔
      (∀ j < k, thetaCuspCosineDerivativeIntegral j t = 0) ∧
        thetaCuspCosineDerivativeIntegral k t ≠ 0 := by
  have hreal (j : ℕ) : iteratedDeriv j Xi t =
      thetaCuspCosineDerivativeIntegral j t := by
    rw [show Xi = thetaCuspCosineRepresentation by
      funext u
      exact Xi_eq_thetaCuspCosineRepresentation u,
      iteratedDeriv_thetaCuspCosineRepresentation_eq_integral]
  have hjet (j : ℕ) :
      iteratedDeriv j XiC (xiSpectralPointSupport rho) =
        (thetaCuspCosineDerivativeIntegral j t : ℂ) := by
    rw [ht, iteratedDeriv_XiC_ofReal, hreal]
  simpa only [hjet, ne_eq, Complex.ofReal_eq_zero] using
    xiSupportMultiplicity_eq_iff_iteratedDeriv rho k

/-- Under RH, every centered Xi divisor support point is canonically the complexification of its
real part.  This support-level form discharges the multiplicity-copy witness required by the
underlying RH spectral-reality theorem. -/
theorem xiSpectralPointSupport_eq_ofReal_of_rh
    (hRH : RiemannHypothesis) (rho : XiDivisorSupport) :
    xiSpectralPointSupport rho = ((xiSpectralPointSupport rho).re : ℂ) := by
  let q : XiZeroCopy :=
    ⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩
  obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
  have hs : xiSpectralPointSupport rho = (t : ℂ) := by
    simpa only [q, xiSpectralPoint_eq_support] using ht
  rw [hs]
  simp

/-- **RH-discharged real source multiplicity law.**  Under RH, the exact multiplicity of every
centered Xi divisor is the first nonzero member of the positive-half cosine-phase derivative
hierarchy evaluated at the support point's canonical real coordinate.  No existential copy or
coordinate-identification hypothesis remains. -/
theorem xiSupportMultiplicity_eq_iff_thetaCuspCosineDerivativeIntegral_of_rh
    (hRH : RiemannHypothesis) (rho : XiDivisorSupport) (k : ℕ) :
    xiSupportMultiplicity rho = k ↔
      (∀ j < k, thetaCuspCosineDerivativeIntegral j
        (xiSpectralPointSupport rho).re = 0) ∧
      thetaCuspCosineDerivativeIntegral k
        (xiSpectralPointSupport rho).re ≠ 0 := by
  exact xiSupportMultiplicity_eq_iff_thetaCuspCosineDerivativeIntegral rho
    (xiSpectralPointSupport_eq_ofReal_of_rh hRH rho) k

/-- **General Hedenmalm/source value reflection.**  At every point of the theta-cusp
Fourier--Laplace strip, the self-value of the first removable Hedenmalm quotient is `i` times the
explicit differentiated source integral. -/
theorem xiThetaEigenFourier_self_eq_I_mul_thetaCuspFourierLaplaceFirstMoment
    {alpha : ℂ} (halpha : alpha ∈ thetaCuspFourierLaplaceStrip) :
    xiThetaEigenFourier alpha alpha =
      I * ∫ x : ℝ, thetaCuspFourierLaplaceDerivativeIntegrand alpha x := by
  rw [xiThetaEigenFourier_eq_I_mul_dividedChain_one,
    xiThetaDividedChain_self_eq_integral_thetaCuspFourierLaplaceJet_div_factorial
      halpha 1]
  simp only [Nat.factorial_one, Nat.cast_one, div_one,
    thetaCuspFourierLaplaceJetIntegrand_one]

/-- Every centered Xi divisor automatically satisfies the general Hedenmalm/source self-value
law; no strip premise remains. -/
theorem xiThetaEigenFourier_self_eq_I_mul_thetaCuspFourierLaplaceFirstMoment_of_zero
    {alpha : ℂ} (halpha : XiC alpha = 0) :
    xiThetaEigenFourier alpha alpha =
      I * ∫ x : ℝ, thetaCuspFourierLaplaceDerivativeIntegrand alpha x :=
  xiThetaEigenFourier_self_eq_I_mul_thetaCuspFourierLaplaceFirstMoment
    (xiC_zero_mem_thetaCuspFourierLaplaceStrip halpha)

/-- **Unconditional Hedenmalm/source first-jet law.**  The first removable Hedenmalm quotient is
nonzero at every centered Xi divisor exactly when the derivative of the theta-cusp
Fourier--Laplace transform is nonzero there. -/
theorem xiThetaFirstQuotientValueConstraint_iff_thetaCuspFourierLaplace_deriv_ne_zero :
    XiThetaFirstQuotientValueConstraint ↔
      ∀ alpha : ℂ, XiC alpha = 0 → deriv thetaCuspFourierLaplace alpha ≠ 0 := by
  rw [xiThetaFirstQuotientValueConstraint_iff_simple]
  constructor
  · intro hsimple alpha halpha
    rw [deriv_thetaCuspFourierLaplace_eq_deriv_XiC
      (xiC_zero_mem_thetaCuspFourierLaplaceStrip halpha)]
    exact hsimple halpha
  · intro hsource alpha halpha
    rw [← deriv_thetaCuspFourierLaplace_eq_deriv_XiC
      (xiC_zero_mem_thetaCuspFourierLaplaceStrip halpha)]
    exact hsource alpha halpha

/-- **Explicit complex source-moment form.**  Hedenmalm's first quotient value constraint is
exactly nonvanishing, at every centered Xi divisor, of the differentiated theta-cusp
Fourier--Laplace integral.  This removes both the abstract quotient and its strip hypothesis. -/
theorem
    xiThetaFirstQuotientValueConstraint_iff_thetaCuspFourierLaplaceFirstMoment_ne_zero :
    XiThetaFirstQuotientValueConstraint ↔
      ∀ alpha : ℂ, XiC alpha = 0 →
        (∫ x : ℝ, thetaCuspFourierLaplaceDerivativeIntegrand alpha x) ≠ 0 := by
  rw [xiThetaFirstQuotientValueConstraint_iff_thetaCuspFourierLaplace_deriv_ne_zero]
  constructor
  · intro hsource alpha halpha
    have hstrip := xiC_zero_mem_thetaCuspFourierLaplaceStrip halpha
    have habs : |alpha.im| < 1 := by
      rw [abs_lt]
      exact hstrip
    rw [← deriv_thetaCuspFourierLaplace_eq_integral habs]
    exact hsource alpha halpha
  · intro hmoment alpha halpha
    have hstrip := xiC_zero_mem_thetaCuspFourierLaplaceStrip halpha
    have habs : |alpha.im| < 1 := by
      rw [abs_lt]
      exact hstrip
    rw [deriv_thetaCuspFourierLaplace_eq_integral habs]
    exact hmoment alpha halpha

/-- The continued prime--Gamma RH value condition and the explicit complex theta source moment are
exactly `RH + simplicity`, with no Hedenmalm quotient in the statement. -/
theorem continuedPrimeArchUpperCauchy_and_thetaCuspFourierLaplaceFirstMoment_iff_rh_and_simple :
    (ContinuedPrimeArchUpperCauchyDiagonalNonnegative ∧
      ∀ alpha : ℂ, XiC alpha = 0 →
        (∫ x : ℝ, thetaCuspFourierLaplaceDerivativeIntegrand alpha x) ≠ 0) ↔
      RiemannHypothesis ∧ XiZerosSimple := by
  rw [← xiThetaFirstQuotientValueConstraint_iff_thetaCuspFourierLaplaceFirstMoment_ne_zero,
    continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_riemannHypothesis,
    xiThetaFirstQuotientValueConstraint_iff_simple]

/-- **Complex source-to-metric interface.**  The continued prime--Gamma value condition and the
explicit complex theta first moment are equivalent to existence of the conservative Xi divisor
metric. -/
theorem
    continuedPrimeArchUpperCauchy_and_thetaCuspFourierLaplaceFirstMoment_iff_exists_conservative_metric :
    (ContinuedPrimeArchUpperCauchyDiagonalNonnegative ∧
      ∀ alpha : ℂ, XiC alpha = 0 →
        (∫ x : ℝ, thetaCuspFourierLaplaceDerivativeIntegrand alpha x) ≠ 0) ↔
      ∃ c : XiRealDivisorWeight, XiThetaMetricConservative c :=
  continuedPrimeArchUpperCauchy_and_thetaCuspFourierLaplaceFirstMoment_iff_rh_and_simple.trans
    exists_conservative_xiThetaMetric_iff_rh_and_simple.symm

/-- **RH-localized source simplicity law.**  Under the common RH conjunct, global simplicity of
all centered Xi zeros is equivalent to nonvanishing of the positive-theta first sine moment at
every real Xi zero. -/
theorem riemannHypothesis_and_xiZerosSimple_iff_thetaCuspFirstSineMoment :
    (RiemannHypothesis ∧ XiZerosSimple) ↔
      (RiemannHypothesis ∧
        ∀ t : ℝ, Xi t = 0 →
          (∫ x : ℝ in Ioi 0,
            x * thetaCuspFullSource x * Real.sin (t * x)) ≠ 0) := by
  constructor
  · rintro ⟨hRH, hsimple⟩
    refine ⟨hRH, ?_⟩
    intro t hXi
    have hXiC : XiC (t : ℂ) = 0 := by
      rw [XiC_ofReal, hXi]
      norm_num
    have hderivReal : deriv Xi t ≠ 0 := by
      intro hderiv
      exact hsimple hXiC (by rw [XiC_deriv_ofReal, hderiv]; norm_num)
    exact (deriv_Xi_ne_zero_iff_thetaCuspFirstSineMoment_ne_zero t).mp hderivReal
  · rintro ⟨hRH, hmoment⟩
    refine ⟨hRH, ?_⟩
    intro alpha halpha
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy alpha).mp halpha
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    have halphaReal : alpha = (t : ℂ) := hq.symm.trans ht
    have hXi : Xi t = 0 := by
      have hreal : XiC (t : ℂ) = 0 := by
        rw [← halphaReal]
        exact halpha
      rw [XiC_ofReal] at hreal
      simpa using congrArg Complex.re hreal
    have hderivReal : deriv Xi t ≠ 0 :=
      (deriv_Xi_ne_zero_iff_thetaCuspFirstSineMoment_ne_zero t).mpr (hmoment t hXi)
    rw [halphaReal, XiC_deriv_ofReal]
    exact Complex.ofReal_ne_zero.mpr hderivReal

/-- **Hedenmalm/source value reflection.**  Under RH, the first removable Hedenmalm quotient is
nonzero at every divisor point exactly when the explicit positive-theta first sine moment is
nonzero at every real Xi zero. -/
theorem
    riemannHypothesis_and_xiThetaFirstQuotientValueConstraint_iff_thetaCuspFirstSineMoment :
    (RiemannHypothesis ∧ XiThetaFirstQuotientValueConstraint) ↔
      (RiemannHypothesis ∧
        ∀ t : ℝ, Xi t = 0 →
          (∫ x : ℝ in Ioi 0,
            x * thetaCuspFullSource x * Real.sin (t * x)) ≠ 0) := by
  rw [xiThetaFirstQuotientValueConstraint_iff_simple]
  exact riemannHypothesis_and_xiZerosSimple_iff_thetaCuspFirstSineMoment

/-- The continued prime--Gamma RH value condition together with the explicit positive-theta
first-moment law is exactly `RH + simplicity`.  No Hedenmalm completion hypothesis remains. -/
theorem continuedPrimeArchUpperCauchy_and_thetaCuspFirstSineMoment_iff_rh_and_simple :
    (ContinuedPrimeArchUpperCauchyDiagonalNonnegative ∧
      ∀ t : ℝ, Xi t = 0 →
        (∫ x : ℝ in Ioi 0,
          x * thetaCuspFullSource x * Real.sin (t * x)) ≠ 0) ↔
      RiemannHypothesis ∧ XiZerosSimple := by
  rw [continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_riemannHypothesis]
  exact riemannHypothesis_and_xiZerosSimple_iff_thetaCuspFirstSineMoment.symm

/-- **Source-to-metric Prop interface.**  The continued prime--Gamma value condition and the
positive-theta first-moment law are equivalent to existence of the conservative Xi divisor
metric. -/
theorem continuedPrimeArchUpperCauchy_and_thetaCuspFirstSineMoment_iff_exists_conservative_metric :
    (ContinuedPrimeArchUpperCauchyDiagonalNonnegative ∧
      ∀ t : ℝ, Xi t = 0 →
        (∫ x : ℝ in Ioi 0,
          x * thetaCuspFullSource x * Real.sin (t * x)) ≠ 0) ↔
      ∃ c : XiRealDivisorWeight, XiThetaMetricConservative c :=
  continuedPrimeArchUpperCauchy_and_thetaCuspFirstSineMoment_iff_rh_and_simple.trans
    exists_conservative_xiThetaMetric_iff_rh_and_simple.symm

end RHTower
