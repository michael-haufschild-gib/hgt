import GaloisForLFunctions.RHTower.HeatApertureEchoTomography
import GaloisForLFunctions.RHTower.EulerUnitTangent
import GaloisForLFunctions.RHTower.XiPrimeSeamCoherenceCollapse
import GaloisForLFunctions.HTGeometry.PolygammaReflection

/-!
# The reflected heat-aperture prime tail is the canonical prime seam

The prime coefficient of the canonical heat-aperture logarithmic echo at a parameter `s` is

`p^(conj s - 1)`.

Evaluating this coefficient at the functional-equation and Schwarz images `1 - rho` and
`conj rho`, respectively, gives the two terms of the canonical prime seam.  Thus their difference,
multiplied by `log p`, is exactly `orbitwiseNatPrimeSeamCharge p rho`.

This is an interface collapse, not a source-side proof of RH.  It shows that reflection-fixing the
whole heat-aperture prime tail asks for no more and no less orientation data than the already
isolated first-prime seam; in fact its scale-two coefficient alone detects the critical line.
-/

open Complex Real

namespace GaloisForLFunctions

noncomputable section

/-- At a prime index, the heat-aperture Euler-log coefficient is the bare power twist. -/
theorem heatAperturePrimePowerCoeff_prime
    (s : ℂ) (p : ℕ) (hp : p.Prime) :
    heatAperturePrimePowerCoeff s p =
      (p : ℂ) ^ ((starRingEnd ℂ) s - 1) := by
  have hcoeff : RHTower.eulerLogDirichletCoeff p = 1 := by
    simpa using (RHTower.eulerLogDirichletCoeff_prime_pow_succ p 0 hp)
  simp [heatAperturePrimePowerCoeff, lseriesPowerTwistCoeff, hcoeff]

/-- **Heat/seam value relation.**  The FE--Schwarz difference of one prime coefficient is exactly
the canonical prime seam after multiplication by `log p`. -/
theorem log_mul_heatAperturePrimePowerCoeff_FE_sub_Schwarz_eq_seam
    (rho : ℂ) (p : ℕ) (hp : p.Prime) :
    (Real.log p : ℂ) *
        (heatAperturePrimePowerCoeff (1 - rho) p -
          heatAperturePrimePowerCoeff ((starRingEnd ℂ) rho) p) =
      RHTower.orbitwiseNatPrimeSeamCharge p rho := by
  rw [heatAperturePrimePowerCoeff_prime (1 - rho) p hp,
    heatAperturePrimePowerCoeff_prime ((starRingEnd ℂ) rho) p hp]
  have hFE :
      (starRingEnd ℂ) (1 - rho) - 1 = -((starRingEnd ℂ) rho) := by
    apply Complex.ext <;> simp
  have hSchwarz :
      (starRingEnd ℂ) ((starRingEnd ℂ) rho) - 1 = -(1 - rho) := by
    apply Complex.ext <;> simp
  rw [hFE, hSchwarz]
  simp [RHTower.orbitwiseNatPrimeSeamCharge, RHTower.orbitwiseScaleSeamCharge]

/-- Equality of the scale-two heat coefficients at the FE and Schwarz images is already a faithful
detector of the critical line. -/
theorem heatAperturePrimeTwoCoeff_FE_eq_Schwarz_iff_re_eq_half (rho : ℂ) :
    heatAperturePrimePowerCoeff (1 - rho) 2 =
        heatAperturePrimePowerCoeff ((starRingEnd ℂ) rho) 2 ↔
      rho.re = 1 / 2 := by
  have hlog : (Real.log 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  constructor
  · intro hcoeff
    apply (RHTower.orbitwiseFirstPrimeSeamCharge_eq_zero_iff rho).mp
    rw [← RHTower.orbitwiseNatPrimeSeamCharge_two_eq_firstPrime]
    rw [← log_mul_heatAperturePrimePowerCoeff_FE_sub_Schwarz_eq_seam rho 2 (by norm_num)]
    simp [hcoeff]
  · intro hre
    have hseam : RHTower.orbitwiseNatPrimeSeamCharge 2 rho = 0 := by
      rw [RHTower.orbitwiseNatPrimeSeamCharge_two_eq_firstPrime]
      exact (RHTower.orbitwiseFirstPrimeSeamCharge_eq_zero_iff rho).mpr hre
    have hmul :
        (Real.log 2 : ℂ) *
            (heatAperturePrimePowerCoeff (1 - rho) 2 -
              heatAperturePrimePowerCoeff ((starRingEnd ℂ) rho) 2) = 0 :=
      (log_mul_heatAperturePrimePowerCoeff_FE_sub_Schwarz_eq_seam
        rho 2 (by norm_num)).trans hseam
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hlog)

/-- The reflected heat-aperture prime coefficient family at one strip parameter. -/
def HeatAperturePrimeCoefficientsFESchwarzFixed (rho : ℂ) : Prop :=
  ∀ p : ℕ, p.Prime →
    heatAperturePrimePowerCoeff (1 - rho) p =
      heatAperturePrimePowerCoeff ((starRingEnd ℂ) rho) p

/-- The whole reflected prime family is fixed exactly on the critical line. -/
theorem heatAperturePrimeCoefficientsFESchwarzFixed_iff_re_eq_half (rho : ℂ) :
    HeatAperturePrimeCoefficientsFESchwarzFixed rho ↔ rho.re = 1 / 2 := by
  constructor
  · intro h
    exact (heatAperturePrimeTwoCoeff_FE_eq_Schwarz_iff_re_eq_half rho).mp
      (h 2 (by norm_num))
  · intro hre
    have horbit : (starRingEnd ℂ) rho = 1 - rho := by
      apply Complex.ext
      · simp only [Complex.conj_re, Complex.sub_re, Complex.one_re]
        linarith
      · simp only [Complex.conj_im, Complex.sub_im, Complex.one_im]
        ring
    intro p _
    rw [horbit]

/-- Checking the whole prime family gives no stronger condition than checking its first member. -/
theorem heatAperturePrimeCoefficientsFESchwarzFixed_iff_primeTwo (rho : ℂ) :
    HeatAperturePrimeCoefficientsFESchwarzFixed rho ↔
      heatAperturePrimePowerCoeff (1 - rho) 2 =
        heatAperturePrimePowerCoeff ((starRingEnd ℂ) rho) 2 := by
  rw [heatAperturePrimeCoefficientsFESchwarzFixed_iff_re_eq_half,
    heatAperturePrimeTwoCoeff_FE_eq_Schwarz_iff_re_eq_half]

/-- **Connection/seam factorization.**  On the open strip, the difference of the actual local
Euler connection values at the Schwarz and FE images, multiplied by its two nonzero Euler
denominators, is exactly the canonical prime seam. -/
theorem degreeOneEulerLocalFlux_Schwarz_sub_FE_mul_denominators_eq_seam
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (p : ℕ) (hp : p.Prime) :
    (RHTower.degreeOneEulerLocalFlux p 1 ((starRingEnd ℂ) rho) -
        RHTower.degreeOneEulerLocalFlux p 1 (1 - rho)) *
        ((1 - (p : ℂ) ^ (-((starRingEnd ℂ) rho))) *
          (1 - (p : ℂ) ^ (-(1 - rho)))) =
      RHTower.orbitwiseNatPrimeSeamCharge p rho := by
  let q : ℂ := (p : ℂ) ^ (-((starRingEnd ℂ) rho))
  let r : ℂ := (p : ℂ) ^ (-(1 - rho))
  have hq : 1 - q ≠ 0 := by
    dsimp only [q]
    exact RHTower.one_sub_prime_cpow_neg_ne_zero hp.two_le (by
      simpa using hstrip.1)
  have hr : 1 - r ≠ 0 := by
    dsimp only [r]
    apply RHTower.one_sub_prime_cpow_neg_ne_zero hp.two_le
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hseam :
      RHTower.orbitwiseNatPrimeSeamCharge p rho =
        (Real.log p : ℂ) * (q - r) := by
    simp [q, r, RHTower.orbitwiseNatPrimeSeamCharge,
      RHTower.orbitwiseScaleSeamCharge]
  rw [hseam]
  simp only [RHTower.degreeOneEulerLocalFlux, one_mul]
  change
    ((Real.log p : ℂ) * q / (1 - q) -
        (Real.log p : ℂ) * r / (1 - r)) *
        ((1 - q) * (1 - r)) =
      (Real.log p : ℂ) * (q - r)
  field_simp [hq, hr]
  ring

/-- Vanishing of the actual FE--Schwarz local connection difference is equivalent to the critical
line.  This is the value-level, rather than infinitesimal, version of the heat/seam collapse. -/
theorem degreeOneEulerLocalFlux_primeTwo_Schwarz_eq_FE_iff_re_eq_half
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    RHTower.degreeOneEulerLocalFlux 2 1 ((starRingEnd ℂ) rho) =
        RHTower.degreeOneEulerLocalFlux 2 1 (1 - rho) ↔
      rho.re = 1 / 2 := by
  constructor
  · intro hconnection
    apply (RHTower.orbitwiseFirstPrimeSeamCharge_eq_zero_iff rho).mp
    have hseam :=
      degreeOneEulerLocalFlux_Schwarz_sub_FE_mul_denominators_eq_seam
        hstrip 2 (by norm_num)
    rw [hconnection, sub_self, zero_mul] at hseam
    simpa [RHTower.orbitwiseNatPrimeSeamCharge_two_eq_firstPrime] using hseam.symm
  · intro hre
    have horbit : (starRingEnd ℂ) rho = 1 - rho := by
      apply Complex.ext
      · simp only [Complex.conj_re, Complex.sub_re, Complex.one_re]
        linarith
      · simp only [Complex.conj_im, Complex.sub_im, Complex.one_im]
        ring
    rw [horbit]

/-- The actual local Euler connection equality and the heat-tail coefficient equality have exactly
the same zero locus. -/
theorem degreeOneEulerLocalFlux_Schwarz_eq_FE_iff_heatPrimeTwoCoeff_eq
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    RHTower.degreeOneEulerLocalFlux 2 1 ((starRingEnd ℂ) rho) =
        RHTower.degreeOneEulerLocalFlux 2 1 (1 - rho) ↔
      heatAperturePrimePowerCoeff (1 - rho) 2 =
        heatAperturePrimePowerCoeff ((starRingEnd ℂ) rho) 2 := by
  rw [degreeOneEulerLocalFlux_primeTwo_Schwarz_eq_FE_iff_re_eq_half hstrip,
    heatAperturePrimeTwoCoeff_FE_eq_Schwarz_iff_re_eq_half]

private theorem hasDerivAt_natPrime_cpow_neg
    (p : ℕ) (hp : p.Prime) (s : ℂ) :
    HasDerivAt (fun z : ℂ => (p : ℂ) ^ (-z))
      (-(Real.log p : ℂ) * (p : ℂ) ^ (-s)) s := by
  have h := ((hasDerivAt_id s).neg).const_cpow
    (c := (p : ℂ)) (Or.inl (Nat.cast_ne_zero.mpr hp.ne_zero))
  convert h using 1
  all_goals try rfl
  all_goals
    simp [Complex.ofReal_log (show (0 : ℝ) ≤ p by positivity),
      Function.id_def]
  all_goals ring

/-- **Connection-curvature/tangent identity.**  Spectral differentiation of the genuine local
Euler connection returns the actual Euler-parameter tangent, up to the nonzero factor `-log p`. -/
theorem hasDerivAt_degreeOneEulerLocalFlux_spectral
    {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (RHTower.degreeOneEulerLocalFlux p 1)
      (-(Real.log p : ℂ) * RHTower.primeEulerUnitTangent p s) s := by
  let q : ℂ := (p : ℂ) ^ (-s)
  have hq : HasDerivAt (fun z : ℂ => (p : ℂ) ^ (-z))
      (-(Real.log p : ℂ) * q) s := by
    simpa only [q] using hasDerivAt_natPrime_cpow_neg p hp s
  have hden : 1 - q ≠ 0 := by
    dsimp only [q]
    exact RHTower.one_sub_prime_cpow_neg_ne_zero hp.two_le hs
  have hdenDeriv : HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z))
      ((Real.log p : ℂ) * q) s := by
    simpa using! hq.const_sub 1
  have hquot := hq.div hdenDeriv hden
  have hscaled := hquot.const_mul (Real.log p : ℂ)
  convert hscaled using 1
  all_goals try rfl
  · funext z
    simp only [RHTower.degreeOneEulerLocalFlux, one_mul]
    simp only [div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply]
    ring
  · try dsimp only [q]
    unfold RHTower.primeEulerUnitTangent
    field_simp [hden]
    ring

/-- **Actual-tangent/seam factorization.**  The FE--Schwarz difference of the genuine Euler-point
parameter tangents is the canonical seam times an explicit rational factor. -/
theorem primeEulerUnitTangent_Schwarz_sub_FE_mul_denominator_sq_eq_seam_mul_cross
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (p : ℕ) (hp : p.Prime) :
    (RHTower.primeEulerUnitTangent p ((starRingEnd ℂ) rho) -
        RHTower.primeEulerUnitTangent p (1 - rho)) *
        ((1 - (p : ℂ) ^ (-((starRingEnd ℂ) rho))) ^ 2 *
          (1 - (p : ℂ) ^ (-(1 - rho))) ^ 2) =
      RHTower.orbitwiseNatPrimeSeamCharge p rho *
        (1 - (p : ℂ) ^ (-((starRingEnd ℂ) rho)) *
          (p : ℂ) ^ (-(1 - rho))) := by
  let q : ℂ := (p : ℂ) ^ (-((starRingEnd ℂ) rho))
  let r : ℂ := (p : ℂ) ^ (-(1 - rho))
  have hq : 1 - q ≠ 0 := by
    dsimp only [q]
    exact RHTower.one_sub_prime_cpow_neg_ne_zero hp.two_le (by
      simpa using hstrip.1)
  have hr : 1 - r ≠ 0 := by
    dsimp only [r]
    apply RHTower.one_sub_prime_cpow_neg_ne_zero hp.two_le
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hseam :
      RHTower.orbitwiseNatPrimeSeamCharge p rho =
        (Real.log p : ℂ) * (q - r) := by
    simp [q, r, RHTower.orbitwiseNatPrimeSeamCharge,
      RHTower.orbitwiseScaleSeamCharge]
  rw [hseam]
  change
    ((Real.log p : ℂ) * q / (1 - q) ^ 2 -
        (Real.log p : ℂ) * r / (1 - r) ^ 2) *
        ((1 - q) ^ 2 * (1 - r) ^ 2) =
      ((Real.log p : ℂ) * (q - r)) * (1 - q * r)
  field_simp [hq, hr]
  ring

/-- Every single prime seam is already faithful to the critical line.  The earlier scale-two
statement is the first member of this prime-independent rigidity law. -/
theorem orbitwiseNatPrimeSeamCharge_eq_zero_iff_re_eq_half
    (rho : ℂ) (p : ℕ) (hp : p.Prime) :
    RHTower.orbitwiseNatPrimeSeamCharge p rho = 0 ↔
      rho.re = 1 / 2 := by
  constructor
  · intro hzero
    have hlog : (Real.log p : ℂ) ≠ 0 := by
      exact_mod_cast (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    have hcpow :
        (p : ℂ) ^ (-((starRingEnd ℂ) rho)) =
          (p : ℂ) ^ (-(1 - rho)) := by
      change
        (Real.log p : ℂ) *
          ((p : ℂ) ^ (-((starRingEnd ℂ) rho)) -
            (p : ℂ) ^ (-(1 - rho))) = 0 at hzero
      exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hlog)
    have hnorm := congrArg norm hcpow
    change ‖((p : ℝ) : ℂ) ^ (-((starRingEnd ℂ) rho))‖ =
      ‖((p : ℝ) : ℂ) ^ (-(1 - rho))‖ at hnorm
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp.pos),
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp.pos)] at hnorm
    have hre :=
      (Real.strictMono_rpow_of_base_gt_one (by exact_mod_cast hp.one_lt)).injective hnorm
    simp only [Complex.neg_re, Complex.conj_re, Complex.one_re, Complex.sub_re] at hre
    linarith
  · intro hre
    have horbit : (starRingEnd ℂ) rho = 1 - rho := by
      apply Complex.ext
      · simp only [Complex.conj_re, Complex.sub_re, Complex.one_re]
        linarith
      · simp only [Complex.conj_im, Complex.sub_im, Complex.one_im]
        ring
    simp [RHTower.orbitwiseNatPrimeSeamCharge,
      RHTower.orbitwiseScaleSeamCharge, horbit]

/-- The heat-aperture coefficient at any one prime, rather than specifically the first prime,
detects the critical line. -/
theorem heatAperturePrimeCoeff_FE_eq_Schwarz_iff_re_eq_half
    (rho : ℂ) (p : ℕ) (hp : p.Prime) :
    heatAperturePrimePowerCoeff (1 - rho) p =
        heatAperturePrimePowerCoeff ((starRingEnd ℂ) rho) p ↔
      rho.re = 1 / 2 := by
  have hlog : (Real.log p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  constructor
  · intro hcoeff
    apply (orbitwiseNatPrimeSeamCharge_eq_zero_iff_re_eq_half rho p hp).mp
    rw [← log_mul_heatAperturePrimePowerCoeff_FE_sub_Schwarz_eq_seam rho p hp]
    simp [hcoeff]
  · intro hre
    have hseam : RHTower.orbitwiseNatPrimeSeamCharge p rho = 0 :=
      (orbitwiseNatPrimeSeamCharge_eq_zero_iff_re_eq_half rho p hp).mpr hre
    have hmul :
        (Real.log p : ℂ) *
            (heatAperturePrimePowerCoeff (1 - rho) p -
              heatAperturePrimePowerCoeff ((starRingEnd ℂ) rho) p) = 0 :=
      (log_mul_heatAperturePrimePowerCoeff_FE_sub_Schwarz_eq_seam
        rho p hp).trans hseam
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hlog)

/-- The actual local Euler connection at any single prime is a faithful orientation coordinate. -/
theorem degreeOneEulerLocalFlux_Schwarz_eq_FE_iff_re_eq_half
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (p : ℕ) (hp : p.Prime) :
    RHTower.degreeOneEulerLocalFlux p 1 ((starRingEnd ℂ) rho) =
        RHTower.degreeOneEulerLocalFlux p 1 (1 - rho) ↔
      rho.re = 1 / 2 := by
  constructor
  · intro hconnection
    apply (orbitwiseNatPrimeSeamCharge_eq_zero_iff_re_eq_half rho p hp).mp
    have hseam :=
      degreeOneEulerLocalFlux_Schwarz_sub_FE_mul_denominators_eq_seam
        hstrip p hp
    rw [hconnection, sub_self, zero_mul] at hseam
    exact hseam.symm
  · intro hre
    have horbit : (starRingEnd ℂ) rho = 1 - rho := by
      apply Complex.ext
      · simp only [Complex.conj_re, Complex.sub_re, Complex.one_re]
        linarith
      · simp only [Complex.conj_im, Complex.sub_im, Complex.one_im]
        ring
    rw [horbit]

/-- The extra cross factor in the actual-tangent comparison cannot vanish: both Euler characters
have norm strictly below one throughout the open strip. -/
theorem one_sub_prime_FESchwarz_character_product_ne_zero
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (p : ℕ) (hp : p.Prime) :
    1 - (p : ℂ) ^ (-((starRingEnd ℂ) rho)) *
        (p : ℂ) ^ (-(1 - rho)) ≠ 0 := by
  let q : ℂ := (p : ℂ) ^ (-((starRingEnd ℂ) rho))
  let r : ℂ := (p : ℂ) ^ (-(1 - rho))
  have hqnorm : ‖q‖ < 1 := by
    dsimp only [q]
    apply RHTower.norm_natCast_cpow_neg_lt_one hp.two_le
    simpa using hstrip.1
  have hrnorm : ‖r‖ < 1 := by
    dsimp only [r]
    apply RHTower.norm_natCast_cpow_neg_lt_one hp.two_le
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hproduct : ‖q * r‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg q, norm_nonneg r]
  intro hzero
  have heq : q * r = 1 :=
    (sub_eq_zero.mp (by simpa [q, r] using hzero)).symm
  rw [heq, norm_one] at hproduct
  exact (lt_irrefl 1) hproduct

/-- Equality of the genuine Euler-point tangents at the Schwarz and FE images for any one prime is
already equivalent to the critical line.  No extraction of an empty-parameter coefficient and no
all-prime limiting argument are required. -/
theorem primeEulerUnitTangent_Schwarz_eq_FE_iff_re_eq_half
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (p : ℕ) (hp : p.Prime) :
    RHTower.primeEulerUnitTangent p ((starRingEnd ℂ) rho) =
        RHTower.primeEulerUnitTangent p (1 - rho) ↔
      rho.re = 1 / 2 := by
  constructor
  · intro htangent
    have hfactor :=
      primeEulerUnitTangent_Schwarz_sub_FE_mul_denominator_sq_eq_seam_mul_cross
        hstrip p hp
    rw [htangent, sub_self, zero_mul] at hfactor
    have hcross := one_sub_prime_FESchwarz_character_product_ne_zero hstrip p hp
    have hseam : RHTower.orbitwiseNatPrimeSeamCharge p rho = 0 :=
      (mul_eq_zero.mp hfactor.symm).resolve_right hcross
    exact (orbitwiseNatPrimeSeamCharge_eq_zero_iff_re_eq_half rho p hp).mp hseam
  · intro hre
    have horbit : (starRingEnd ℂ) rho = 1 - rho := by
      apply Complex.ext
      · simp only [Complex.conj_re, Complex.sub_re, Complex.one_re]
        linarith
      · simp only [Complex.conj_im, Complex.sub_im, Complex.one_im]
        ring
    rw [horbit]

/-- Equality of the spectral connection curvatures at the FE and Schwarz images is equivalent to
the critical line at every one prime.  This exposes the same finite orientation coordinate to a
normal-curvature reader without passing through an Euler-parameter chart. -/
theorem degreeOneEulerLocalFlux_spectralDeriv_Schwarz_eq_FE_iff_re_eq_half
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (p : ℕ) (hp : p.Prime) :
    deriv (RHTower.degreeOneEulerLocalFlux p 1) ((starRingEnd ℂ) rho) =
        deriv (RHTower.degreeOneEulerLocalFlux p 1) (1 - rho) ↔
      rho.re = 1 / 2 := by
  have hleft := hasDerivAt_degreeOneEulerLocalFlux_spectral hp (s := (starRingEnd ℂ) rho)
    (by simpa using hstrip.1)
  have hright := hasDerivAt_degreeOneEulerLocalFlux_spectral hp (s := 1 - rho) (by
    simp only [Complex.sub_re, Complex.one_re]
    linarith)
  rw [hleft.deriv, hright.deriv]
  have hlog : (Real.log p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  constructor
  · intro hcurvature
    apply (primeEulerUnitTangent_Schwarz_eq_FE_iff_re_eq_half hstrip p hp).mp
    exact mul_left_cancel₀ (neg_ne_zero.mpr hlog) hcurvature
  · intro hre
    have htangent :=
      (primeEulerUnitTangent_Schwarz_eq_FE_iff_re_eq_half hstrip p hp).mpr hre
    rw [htangent]

/-- At any one prime, equality of the actual Euler-point tangents and equality of the actual
connection values are equivalent. -/
theorem primeEulerUnitTangent_Schwarz_eq_FE_iff_degreeOneEulerLocalFlux_Schwarz_eq_FE
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (p : ℕ) (hp : p.Prime) :
    (RHTower.primeEulerUnitTangent p ((starRingEnd ℂ) rho) =
        RHTower.primeEulerUnitTangent p (1 - rho)) ↔
      (RHTower.degreeOneEulerLocalFlux p 1 ((starRingEnd ℂ) rho) =
        RHTower.degreeOneEulerLocalFlux p 1 (1 - rho)) := by
  rw [primeEulerUnitTangent_Schwarz_eq_FE_iff_re_eq_half hstrip p hp,
    degreeOneEulerLocalFlux_Schwarz_eq_FE_iff_re_eq_half hstrip p hp]

/-- At any one prime, the actual Euler-point tangent and the heat-aperture coefficient are
faithful coordinates on the same FE--Schwarz defect. -/
theorem primeEulerUnitTangent_Schwarz_eq_FE_iff_heatAperturePrimeCoeff_eq
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (p : ℕ) (hp : p.Prime) :
    (RHTower.primeEulerUnitTangent p ((starRingEnd ℂ) rho) =
        RHTower.primeEulerUnitTangent p (1 - rho)) ↔
      (heatAperturePrimePowerCoeff (1 - rho) p =
        heatAperturePrimePowerCoeff ((starRingEnd ℂ) rho) p) := by
  rw [primeEulerUnitTangent_Schwarz_eq_FE_iff_re_eq_half hstrip p hp,
    heatAperturePrimeCoeff_FE_eq_Schwarz_iff_re_eq_half rho p hp]

/-- Scale two is the canonical named specialization of the any-prime actual-tangent theorem. -/
theorem primeEulerUnitTangent_two_Schwarz_eq_FE_iff_re_eq_half
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    RHTower.primeEulerUnitTangent 2 ((starRingEnd ℂ) rho) =
        RHTower.primeEulerUnitTangent 2 (1 - rho) ↔
      rho.re = 1 / 2 :=
  primeEulerUnitTangent_Schwarz_eq_FE_iff_re_eq_half hstrip 2 (by norm_num)

/-- The actual Euler-point tangent equality, actual connection equality, and heat-tail first
coefficient equality are three value coordinates on the same FE--Schwarz defect. -/
theorem primeEulerUnitTangent_two_Schwarz_eq_FE_iff_heatPrimeTwoCoeff_eq
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    RHTower.primeEulerUnitTangent 2 ((starRingEnd ℂ) rho) =
        RHTower.primeEulerUnitTangent 2 (1 - rho) ↔
      heatAperturePrimePowerCoeff (1 - rho) 2 =
        heatAperturePrimePowerCoeff ((starRingEnd ℂ) rho) 2 := by
  rw [primeEulerUnitTangent_two_Schwarz_eq_FE_iff_re_eq_half hstrip,
    heatAperturePrimeTwoCoeff_FE_eq_Schwarz_iff_re_eq_half]

/-! ## Koebe and trigamma coordinates of the actual Euler tangent -/

/-- The rational Koebe coordinate used by one actual Euler character. -/
def koebeRational (q : ℂ) : ℂ := q / (1 - q) ^ 2

/-- The Koebe coordinate is invariant under reciprocal reflection. -/
theorem koebeRational_inv {q : ℂ} (hq : q ≠ 0) :
    koebeRational q⁻¹ = koebeRational q := by
  by_cases hqone : q = 1
  · subst q
    simp [koebeRational]
  · have hqden : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hqone)
    unfold koebeRational
    field_simp [hq, hqden]
    ring

/-- Exact Koebe collision classification away from the pole: two values agree precisely for
equal or reciprocal arguments. -/
theorem koebeRational_eq_iff {q r : ℂ} (hq : q ≠ 1) (hr : r ≠ 1) :
    koebeRational q = koebeRational r ↔ q = r ∨ q * r = 1 := by
  have hqden : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  have hrden : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
  constructor
  · intro h
    unfold koebeRational at h
    field_simp [hqden, hrden] at h
    have hfactor : (q - r) * (1 - q * r) = 0 := by
      calc
        (q - r) * (1 - q * r) = q * (1 - r) ^ 2 - r * (1 - q) ^ 2 := by ring
        _ = 0 := by rw [h]; ring
    rcases mul_eq_zero.mp hfactor with hqr | hprod
    · exact Or.inl (sub_eq_zero.mp hqr)
    · exact Or.inr (sub_eq_zero.mp hprod).symm
  · rintro (rfl | hprod)
    · rfl
    · unfold koebeRational
      field_simp [hqden, hrden]
      have hdifference : q * (1 - r) ^ 2 - r * (1 - q) ^ 2 = 0 := by
        calc
          q * (1 - r) ^ 2 - r * (1 - q) ^ 2 = (q - r) * (1 - q * r) := by ring
          _ = 0 := by rw [hprod]; ring
      exact (sub_eq_zero.mp hdifference).trans (mul_comm _ _)

/-- The reciprocal branch is excluded inside the open unit disk, so the Koebe coordinate is
injective there. -/
theorem koebeRational_injectiveOn_unitDisk {q r : ℂ}
    (hqnorm : ‖q‖ < 1) (hrnorm : ‖r‖ < 1) :
    koebeRational q = koebeRational r ↔ q = r := by
  have hq : q ≠ 1 := by
    intro h
    rw [h, norm_one] at hqnorm
    exact (lt_irrefl 1) hqnorm
  have hr : r ≠ 1 := by
    intro h
    rw [h, norm_one] at hrnorm
    exact (lt_irrefl 1) hrnorm
  rw [koebeRational_eq_iff hq hr]
  constructor
  · rintro (h | hprod)
    · exact h
    · have hnorm : ‖q * r‖ < 1 := by
        rw [norm_mul]
        nlinarith [norm_nonneg q, norm_nonneg r]
      rw [hprod, norm_one] at hnorm
      exact (lt_irrefl 1 hnorm).elim
  · exact Or.inl

/-- The actual Euler tangent is the logarithmic prime weight times the Koebe coordinate. -/
theorem primeEulerUnitTangent_eq_log_mul_koebeRational (p : ℕ) (s : ℂ) :
    RHTower.primeEulerUnitTangent p s =
      (Real.log p : ℂ) * koebeRational ((p : ℂ) ^ (-s)) := by
  unfold RHTower.primeEulerUnitTangent koebeRational
  ring

/-- Canonical imaginary-slope Gamma coordinate of a prime Euler factor. -/
def primeEulerGammaCoordinate (p : ℕ) (s : ℂ) : ℂ :=
  Complex.I * (Real.log p : ℂ) * s / (2 * (Real.pi : ℂ))

private theorem exp_neg_two_mul_div_one_sub_sq_eq_inv_four_sinh_sq
    (x : ℂ) (hden : 1 - Complex.exp (-2 * x) ≠ 0) :
    Complex.exp (-2 * x) / (1 - Complex.exp (-2 * x)) ^ 2 =
      1 / (4 * Complex.sinh x ^ 2) := by
  have hpow : Complex.exp (-2 * x) = Complex.exp (-x) ^ 2 := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  have hpos : Complex.exp x = (Complex.exp (-x))⁻¹ := by
    simpa using Complex.exp_neg (-x)
  have hE0 : Complex.exp (-x) ≠ 0 := Complex.exp_ne_zero _
  have hden' : 1 - Complex.exp (-x) ^ 2 ≠ 0 := by
    rwa [hpow] at hden
  rw [hpow, Complex.sinh, hpos]
  field_simp [hE0, hden']
  ring

/-- **Euler tangent/trigamma-reflection weld.**  On the open Euler half-plane, the actual
Euler-point tangent is exactly the imaginary-slope trigamma-reflection curvature. -/
theorem primeEulerUnitTangent_eq_trigammaReflection
    {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    RHTower.primeEulerUnitTangent p s =
      -(Real.log p : ℂ) / (4 * (Real.pi : ℂ) ^ 2) *
        (deriv Complex.digamma (primeEulerGammaCoordinate p s) +
          deriv Complex.digamma (1 - primeEulerGammaCoordinate p s)) := by
  let L : ℂ := (Real.log p : ℂ)
  let x : ℂ := L * s / 2
  let u : ℂ := primeEulerGammaCoordinate p s
  have hlogpos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have huim : 0 < u.im := by
    have hueq : (2 * (Real.pi : ℂ)) * u = Complex.I * L * s := by
      dsimp only [u, primeEulerGammaCoordinate]
      field_simp [hpi]
      ring
    have him := congrArg Complex.im hueq
    have hLre : L.re = Real.log p := rfl
    have hLim : L.im = 0 := rfl
    have him' : 2 * Real.pi * u.im = Real.log p * s.re := by
      simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, hLre, hLim, zero_mul, one_mul] at him
      norm_num at him
      exact him
    nlinarith [Real.pi_pos]
  have hunot : ∀ m : ℤ, u ≠ (m : ℂ) := by
    intro m hm
    have him := congrArg Complex.im hm
    have hmim : ((m : ℂ)).im = 0 := by simp
    rw [hmim] at him
    linarith
  have href := RHTower.trigamma_reflection hunot
  have harg : (Real.pi : ℂ) * u = x * Complex.I := by
    dsimp only [u, x, primeEulerGammaCoordinate, L]
    field_simp [hpi]
  rw [harg, Complex.sin_mul_I] at href
  have hq : (p : ℂ) ^ (-s) = Complex.exp (-2 * x) := by
    rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hp.ne_zero)]
    rw [← Complex.natCast_log]
    dsimp only [x, L]
    congr 1
    ring
  have hden : 1 - Complex.exp (-2 * x) ≠ 0 := by
    rw [← hq]
    exact RHTower.one_sub_prime_cpow_neg_ne_zero hp.two_le hs
  have hexpsinh := exp_neg_two_mul_div_one_sub_sq_eq_inv_four_sinh_sq x hden
  have hsinh : Complex.sinh x ≠ 0 := by
    intro hzero
    have htwo := Complex.two_sinh x
    rw [hzero, mul_zero] at htwo
    have hexpeq : Complex.exp x = Complex.exp (-x) := sub_eq_zero.mp htwo.symm
    have hpow : Complex.exp (-2 * x) = Complex.exp (-x) ^ 2 := by
      rw [pow_two, ← Complex.exp_add]
      congr 1
      ring
    apply hden
    rw [hpow]
    apply sub_eq_zero.mpr
    symm
    calc
      Complex.exp (-x) ^ 2 = Complex.exp x * Complex.exp (-x) := by
        rw [pow_two, hexpeq]
      _ = Complex.exp (x + -x) := by rw [Complex.exp_add]
      _ = 1 := by simp
  unfold RHTower.primeEulerUnitTangent
  rw [hq, href]
  calc
    (Real.log p : ℂ) * Complex.exp (-2 * x) /
        (1 - Complex.exp (-2 * x)) ^ 2 =
        (Real.log p : ℂ) *
          (Complex.exp (-2 * x) / (1 - Complex.exp (-2 * x)) ^ 2) := by ring
    _ = (Real.log p : ℂ) * (1 / (4 * Complex.sinh x ^ 2)) := by rw [hexpsinh]
    _ = -(Real.log p : ℂ) / (4 * (Real.pi : ℂ) ^ 2) *
        ((Real.pi : ℂ) ^ 2 / (Complex.sinh x * Complex.I) ^ 2) := by
      field_simp [hsinh, hpi]
      rw [Complex.I_sq]
      ring

end

end GaloisForLFunctions
