import GaloisForLFunctions.RHTower.XiMassBesselConeTail
import GaloisForLFunctions.RHTower.XiMassPrimeGradedOpenCore
import GaloisForLFunctions.RHTower.XiMassCriticalOutgoingOpenCore
import GaloisForLFunctions.RHTower.XiMassCriticalDiscreteRemainderSymmetry

/-!
# The graded Bessel cone / vertical type phase diagram

The exterior tail of a slope-`κ` cone decays at the exact rate

`Γ_a(κ) = κ/2 − a√(κ²−1)`,

which is strictly decreasing from `1/2` at the light cone `κ = 1` to `−∞`.  Solving `Γ_a(κ) = λ`
gives the graded cone slope

`κ_{a,λ} = (a√(4a²+4λ²−1) − λ) / (2(a²−1/4))`,

with `κ_{a,0} = κ_B` and `κ_{a,1/2} = 1`.  Above that slope the exterior tail is a type-`λ`
family, so the cone and the outgoing current have the same vertical type.  The corpus source-type
law then converts the type of the cone into a transverse displacement bound on the mass-shifted
Xi divisor: allowed vertical type and minimal raw cone slope are two coordinates of one phase
diagram, and `λ = 0` recovers the Riemann hypothesis.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-! ## The graded cone slope -/

/-- The slope whose exterior Bessel tail has exactly vertical type `λ`. -/
def xiMassGradedConeSlope (a lam : ℝ) : ℝ :=
  (a * Real.sqrt (4 * a ^ 2 + 4 * lam ^ 2 - 1) - lam) / (2 * (a ^ 2 - 1 / 4))

theorem one_le_xiMassGradedConeSlope {a lam : ℝ} (ha : 1 / 2 < a) (hlam : 0 ≤ lam) :
    1 ≤ xiMassGradedConeSlope a lam := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hden : (0 : ℝ) < 2 * (a ^ 2 - 1 / 4) := by nlinarith
  have harg : (0 : ℝ) ≤ 4 * a ^ 2 + 4 * lam ^ 2 - 1 := by nlinarith
  have hsq : Real.sqrt (4 * a ^ 2 + 4 * lam ^ 2 - 1) ^ 2 = 4 * a ^ 2 + 4 * lam ^ 2 - 1 :=
    Real.sq_sqrt harg
  have hnn : 0 ≤ Real.sqrt (4 * a ^ 2 + 4 * lam ^ 2 - 1) := Real.sqrt_nonneg _
  rw [xiMassGradedConeSlope, le_div_iff₀ hden]
  have hkey : (2 * (a ^ 2 - 1 / 4) + lam) ^ 2
      ≤ (a * Real.sqrt (4 * a ^ 2 + 4 * lam ^ 2 - 1)) ^ 2 := by
    have hexp : (a * Real.sqrt (4 * a ^ 2 + 4 * lam ^ 2 - 1)) ^ 2
        = a ^ 2 * (4 * a ^ 2 + 4 * lam ^ 2 - 1) := by rw [mul_pow, hsq]
    rw [hexp]
    nlinarith [sq_nonneg (lam - 1 / 2), sq_nonneg a]
  nlinarith [mul_nonneg ha0.le hnn]

theorem one_lt_xiMassGradedConeSlope {a lam : ℝ} (ha : 1 / 2 < a) (hlam : 0 ≤ lam)
    (hlamhalf : lam < 1 / 2) : 1 < xiMassGradedConeSlope a lam := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hden : (0 : ℝ) < 2 * (a ^ 2 - 1 / 4) := by nlinarith
  have harg : (0 : ℝ) ≤ 4 * a ^ 2 + 4 * lam ^ 2 - 1 := by nlinarith
  have hsq : Real.sqrt (4 * a ^ 2 + 4 * lam ^ 2 - 1) ^ 2 = 4 * a ^ 2 + 4 * lam ^ 2 - 1 :=
    Real.sq_sqrt harg
  have hnn : 0 ≤ Real.sqrt (4 * a ^ 2 + 4 * lam ^ 2 - 1) := Real.sqrt_nonneg _
  rw [xiMassGradedConeSlope, lt_div_iff₀ hden]
  have hpos : (0 : ℝ) < (4 * a ^ 2 - 1) * (lam - 1 / 2) ^ 2 := by
    have h1 : (0 : ℝ) < 4 * a ^ 2 - 1 := by nlinarith
    have h2 : (0 : ℝ) < (lam - 1 / 2) ^ 2 := by nlinarith
    positivity
  have hkey : (2 * (a ^ 2 - 1 / 4) + lam) ^ 2
      < (a * Real.sqrt (4 * a ^ 2 + 4 * lam ^ 2 - 1)) ^ 2 := by
    have hexp : (a * Real.sqrt (4 * a ^ 2 + 4 * lam ^ 2 - 1)) ^ 2
        = a ^ 2 * (4 * a ^ 2 + 4 * lam ^ 2 - 1) := by rw [mul_pow, hsq]
    rw [hexp]
    nlinarith [hpos]
  nlinarith [mul_nonneg ha0.le hnn]

/-- **(20.2) The graded slope realizes the prescribed vertical type.** -/
theorem xiMassBesselConeExponent_gradedConeSlope {a lam : ℝ} (ha : 1 / 2 < a) (hlam : 0 ≤ lam)
    (hlamhalf : lam ≤ 1 / 2) :
    -(xiMassBesselConeExponent a (xiMassGradedConeSlope a lam)) = lam := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hden : (0 : ℝ) < 2 * (a ^ 2 - 1 / 4) := by nlinarith
  have harg : (0 : ℝ) ≤ 4 * a ^ 2 + 4 * lam ^ 2 - 1 := by nlinarith
  have hsq : Real.sqrt (4 * a ^ 2 + 4 * lam ^ 2 - 1) ^ 2 = 4 * a ^ 2 + 4 * lam ^ 2 - 1 :=
    Real.sq_sqrt harg
  set kappa : ℝ := xiMassGradedConeSlope a lam with hkappa
  have hone : 1 ≤ kappa := one_le_xiMassGradedConeSlope ha hlam
  have hDne : (2 * (a ^ 2 - 1 / 4)) ≠ 0 := ne_of_gt hden
  have hkD : kappa * (2 * (a ^ 2 - 1 / 4))
      = a * Real.sqrt (4 * a ^ 2 + 4 * lam ^ 2 - 1) - lam := by
    rw [hkappa, xiMassGradedConeSlope, div_mul_cancel₀ _ hDne]
  have hmul : (kappa ^ 2 * (a ^ 2 - 1 / 4) + lam * kappa - (lam ^ 2 + a ^ 2))
      * (4 * (a ^ 2 - 1 / 4)) = 0 := by
    linear_combination (kappa * (2 * (a ^ 2 - 1 / 4))
      + (a * Real.sqrt (4 * a ^ 2 + 4 * lam ^ 2 - 1) - lam) + 2 * lam) * hkD + a ^ 2 * hsq
  have hquad : kappa ^ 2 * (a ^ 2 - 1 / 4) + lam * kappa - (lam ^ 2 + a ^ 2) = 0 := by
    rcases mul_eq_zero.1 hmul with h | h
    · exact h
    · exact absurd h (ne_of_gt (by nlinarith : (0:ℝ) < 4 * (a ^ 2 - 1 / 4)))
  have hhalfnn : 0 ≤ kappa / 2 - lam := by linarith
  have hgap : (0 : ℝ) ≤ kappa ^ 2 - 1 := by nlinarith
  have hval : Real.sqrt (kappa ^ 2 - 1) = (kappa / 2 - lam) / a := by
    rw [show kappa ^ 2 - 1 = ((kappa / 2 - lam) / a) ^ 2 by field_simp; nlinarith [hquad]]
    exact Real.sqrt_sq (by positivity)
  rw [xiMassBesselConeExponent, hval]
  field_simp
  ring

/-- At vertical type zero the graded slope is the Bessel balance slope. -/
theorem xiMassGradedConeSlope_zero {a : ℝ} (ha : 1 / 2 < a) :
    xiMassGradedConeSlope a 0 = xiMassSpacelikeSharpSlope a := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hden : (0 : ℝ) < a ^ 2 - 1 / 4 := by nlinarith
  have hkpos : (0 : ℝ) < Real.sqrt (a ^ 2 - 1 / 4) := Real.sqrt_pos.2 hden
  have hksq : Real.sqrt (a ^ 2 - 1 / 4) ^ 2 = a ^ 2 - 1 / 4 := Real.sq_sqrt hden.le
  have hfac : Real.sqrt (4 * a ^ 2 + 4 * (0 : ℝ) ^ 2 - 1) = 2 * Real.sqrt (a ^ 2 - 1 / 4) := by
    rw [show 4 * a ^ 2 + 4 * (0 : ℝ) ^ 2 - 1 = 2 ^ 2 * (a ^ 2 - 1 / 4) by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [xiMassGradedConeSlope, xiMassSpacelikeSharpSlope, hfac,
    div_eq_div_iff (ne_of_gt (by nlinarith : (0:ℝ) < 2 * (a ^ 2 - 1 / 4))) (ne_of_gt hkpos)]
  linear_combination 2 * a * hksq

/-- At the continuum pole type `1/2` the graded slope is the physical light cone. -/
theorem xiMassGradedConeSlope_half {a : ℝ} (ha : 1 / 2 < a) :
    xiMassGradedConeSlope a (1 / 2) = 1 := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hden : (0 : ℝ) < 2 * (a ^ 2 - 1 / 4) := by nlinarith
  have hfac : Real.sqrt (4 * a ^ 2 + 4 * (1 / 2 : ℝ) ^ 2 - 1) = 2 * a := by
    rw [show 4 * a ^ 2 + 4 * (1 / 2 : ℝ) ^ 2 - 1 = (2 * a) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  rw [xiMassGradedConeSlope, hfac, div_eq_one_iff_eq (ne_of_gt hden)]
  ring

/-- The exterior exponent is antitone in the slope: a larger cone has a smaller vertical type. -/
theorem xiMassBesselConeExponent_mono {a kappa kappa' : ℝ} (ha : 1 / 2 < a) (hkappa : 1 < kappa)
    (hkk : kappa ≤ kappa') :
    xiMassBesselConeExponent a kappa ≤ xiMassBesselConeExponent a kappa' := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hkappa2 : (0 : ℝ) ≤ kappa ^ 2 - 1 := by nlinarith
  have hkappa2' : (0 : ℝ) ≤ kappa' ^ 2 - 1 := by nlinarith
  have hs : Real.sqrt (kappa ^ 2 - 1) ^ 2 = kappa ^ 2 - 1 := Real.sq_sqrt hkappa2
  have hs' : Real.sqrt (kappa' ^ 2 - 1) ^ 2 = kappa' ^ 2 - 1 := Real.sq_sqrt hkappa2'
  have hsnn : 0 ≤ Real.sqrt (kappa ^ 2 - 1) := Real.sqrt_nonneg _
  have hsnn' : 0 ≤ Real.sqrt (kappa' ^ 2 - 1) := Real.sqrt_nonneg _
  have hsk : Real.sqrt (kappa ^ 2 - 1) < kappa := by nlinarith
  have hmono : Real.sqrt (kappa ^ 2 - 1) ≤ Real.sqrt (kappa' ^ 2 - 1) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hsk' : Real.sqrt (kappa' ^ 2 - 1) < kappa' := by nlinarith
  have hdiff : kappa' - kappa
      ≤ 2 * a * (Real.sqrt (kappa' ^ 2 - 1) - Real.sqrt (kappa ^ 2 - 1)) := by
    have hchord : (kappa' - kappa) * (kappa' + kappa)
        = (Real.sqrt (kappa' ^ 2 - 1) - Real.sqrt (kappa ^ 2 - 1))
          * (Real.sqrt (kappa' ^ 2 - 1) + Real.sqrt (kappa ^ 2 - 1)) := by
      nlinarith [hs, hs']
    have hprod := mul_le_mul_of_nonneg_left
      (show Real.sqrt (kappa' ^ 2 - 1) + Real.sqrt (kappa ^ 2 - 1) ≤ kappa' + kappa by linarith)
      (sub_nonneg.2 hmono)
    have hstep : kappa' - kappa
        ≤ Real.sqrt (kappa' ^ 2 - 1) - Real.sqrt (kappa ^ 2 - 1) := by
      nlinarith [hchord, hprod]
    nlinarith [hstep, sub_nonneg.2 hmono]
  rw [xiMassBesselConeExponent, xiMassBesselConeExponent]
  linarith

/-! ## The graded outgoing type -/

/-- Vertical type `λ` of the outgoing Chebyshev current. -/
def XiMassCriticalOutgoingFluxLineGrowth (a sigma lam : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, ‖xiMassCriticalOutgoingFlux a sigma u‖ ≤ C * Real.exp (lam * |u|)

/-- Vertical type `λ` of the outgoing current on the nonnegative half-line. -/
def XiMassCriticalOutgoingFluxNonnegativeLineGrowth (a sigma lam : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → ‖xiMassCriticalOutgoingFlux a sigma u‖ ≤ C * Real.exp (lam * u)

/-- **The graded source law transported to the outgoing current.**  The complete literal prime
source and the outgoing current differ by one uniformly bounded explicit face, so they have the
same vertical type. -/
theorem xiMassBottomPrimeLineGrowth_iff_outgoingFluxLineGrowth {a c sigma lam : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma) (hlam : 0 ≤ lam) :
    XiMassBottomPrimeLineGrowth a c sigma lam
      ↔ XiMassCriticalOutgoingFluxLineGrowth a sigma lam := by
  set B : ℝ := 2 * Real.pi * Real.exp (-sigma * xiMassArchPoleFrequency a) +
    3 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) with hBdef
  have hface : ∀ u : ℝ, ‖xiMassCriticalOutgoingExplicitFace a sigma u‖ ≤ B :=
    fun u => norm_xiMassCriticalOutgoingExplicitFace_le (lt_trans hhalf hca) hsigma u
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hface 0)
  have hexp : ∀ u : ℝ, (1 : ℝ) ≤ Real.exp (lam * |u|) :=
    fun u => Real.one_le_exp (mul_nonneg hlam (abs_nonneg u))
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + B, fun u => ?_⟩
    have heq := xiMassBottomPrimeIntegral_eq_explicitFace_add_outgoingFlux hhalf hca hsigma u
    have hout : xiMassCriticalOutgoingFlux a sigma u =
        xiMassBottomPrimeIntegral a c ((sigma : ℂ) + u * I) -
          xiMassCriticalOutgoingExplicitFace a sigma u := by
      rw [heq]; ring
    rw [hout]
    refine (norm_sub_le _ _).trans ?_
    have hB : B ≤ B * Real.exp (lam * |u|) := by
      nlinarith [hexp u, hB0]
    have := hC u
    nlinarith [hface u]
  · rintro ⟨C, hC⟩
    refine ⟨B + C, fun u => ?_⟩
    rw [xiMassBottomPrimeIntegral_eq_explicitFace_add_outgoingFlux hhalf hca hsigma u]
    refine (norm_add_le _ _).trans ?_
    have := hC u
    nlinarith [hface u, hexp u, hB0]

/-- Negative vertical heights are redundant for the graded outgoing current as well. -/
theorem xiMassCriticalOutgoingFluxLineGrowth_iff_nonnegative {a sigma lam : ℝ}
    (ha : 1 / 2 < a) (hsigma : 0 < sigma) (hlam : 0 ≤ lam) :
    XiMassCriticalOutgoingFluxLineGrowth a sigma lam
      ↔ XiMassCriticalOutgoingFluxNonnegativeLineGrowth a sigma lam := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  set Z : ℝ := xiMassCriticalOutgoingZeroShiftBound sigma with hZ
  have hZ0 : 0 ≤ Z := xiMassCriticalOutgoingZeroShiftBound_nonneg sigma
  have hsaw : ∀ u : ℝ, ‖xiMassCriticalFloorSawtoothFlux a sigma u‖ ≤ 2 * Z :=
    fun u => norm_xiMassCriticalFloorSawtoothFlux_le ha0 hsigma u
  have hreflect : ∀ u : ℝ, ‖xiMassCriticalOutgoingFlux a sigma (-u)‖
      ≤ ‖xiMassCriticalOutgoingFlux a sigma u‖ + 4 * Z := by
    intro u
    have hsplitu := xiMassCriticalOutgoingFlux_eq_discrete_add_floor ha hsigma u
    have hsplitn := xiMassCriticalOutgoingFlux_eq_discrete_add_floor ha hsigma (-u)
    have hDneg : ‖xiMassCriticalDiscreteRemainderFlux a sigma (-u)‖
        = ‖xiMassCriticalDiscreteRemainderFlux a sigma u‖ :=
      norm_xiMassCriticalDiscreteRemainderFlux_neg ha0 u
    have hD : ‖xiMassCriticalDiscreteRemainderFlux a sigma u‖
        ≤ ‖xiMassCriticalOutgoingFlux a sigma u‖ + 2 * Z := by
      have hsolve : xiMassCriticalDiscreteRemainderFlux a sigma u
          = xiMassCriticalOutgoingFlux a sigma u
            - xiMassCriticalFloorSawtoothFlux a sigma u := by
        rw [hsplitu]; ring
      rw [hsolve]
      exact (norm_sub_le _ _).trans (add_le_add le_rfl (hsaw u))
    rw [hsplitn]
    refine (norm_add_le _ _).trans ?_
    rw [hDneg]
    have := hsaw (-u)
    linarith
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun u hu => ?_⟩
    have := hC u
    rwa [abs_of_nonneg hu] at this
  · rintro ⟨C, hC⟩
    refine ⟨C + 4 * Z, fun u => ?_⟩
    have hexpone : (1 : ℝ) ≤ Real.exp (lam * |u|) :=
      Real.one_le_exp (mul_nonneg hlam (abs_nonneg u))
    by_cases hu : 0 ≤ u
    · have h := hC u hu
      rw [abs_of_nonneg hu]
      nlinarith [Real.one_le_exp (mul_nonneg hlam hu), hZ0]
    · have hnegu : 0 ≤ -u := by linarith
      have h := hC (-u) hnegu
      have hrefl := hreflect (-u)
      rw [neg_neg] at hrefl
      rw [abs_of_nonpos (by linarith : u ≤ 0)]
      nlinarith [Real.one_le_exp (mul_nonneg hlam hnegu), hZ0]

/-- **The graded outgoing type law.**  The outgoing current has vertical type `λ` exactly when
every mass-shifted Xi point has transverse displacement at most `λ`. -/
theorem xiMassCriticalOutgoingFluxLineGrowth_iff_mass_displacement_le {a c sigma lam : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma) (hlam : 0 ≤ lam) :
    XiMassCriticalOutgoingFluxLineGrowth a sigma lam ↔
      ∀ q : XiZeroCopy, |((xiMassFamily (show 1 / 2 ≤ a by linarith)).pt q).im| ≤ lam :=
  (xiMassBottomPrimeLineGrowth_iff_outgoingFluxLineGrowth hhalf hca hsigma hlam).symm.trans
    (xiMassBottomPrimeLineGrowth_iff_mass_displacement_le hhalf hca hsigma hlam)

/-! ## The graded cone criterion -/

/-- Vertical type `λ` of the slope-`κ` true-prime cone. -/
def XiMassCriticalBesselConeLineGrowth (a sigma kappa lam : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    ‖xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u‖
      ≤ C * Real.exp (lam * u)

/-- The slope-`κ` cone and the outgoing current differ by a type-`λ` family whenever the exterior
exponent of the cone is at most `λ`. -/
theorem exists_norm_besselCone_sub_outgoingFlux_type_le {a sigma kappa lam : ℝ}
    (ha : 1 / 2 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hlam : 0 ≤ lam)
    (hslope : -(xiMassBesselConeExponent a kappa) ≤ lam) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ, 0 ≤ u →
      ‖xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u
        - xiMassCriticalOutgoingFlux a sigma u‖
        ≤ K * Real.exp (lam * u) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  set kappa' : ℝ := max kappa (a / (a - 1 / 2)) + 1 with hkappa'def
  have hkk : kappa ≤ kappa' := by
    rw [hkappa'def]
    have := le_max_left kappa (a / (a - 1 / 2))
    linarith
  have hkappa' : 1 < kappa' := lt_of_lt_of_le hkappa hkk
  have hslopelt : a / (a - 1 / 2) < kappa' := by
    rw [hkappa'def]
    have := le_max_right kappa (a / (a - 1 / 2))
    linarith
  set d' : ℝ := xiMassConeDepthOfSlope kappa' with hd'
  have hd'half : 1 / 2 < d' := xiMassConeDepthOfSlope_half_lt hkappa'
  have hd'a : d' < a := (xiMassConeDepthOfSlope_lt_iff ha hkappa').2 hslopelt
  obtain ⟨B, hB⟩ := exists_norm_truePrimeCone_sub_outgoingFlux_bound hd'half hd'a hsigma
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 le_rfl)
  have hT0 : 0 ≤ xiMassBesselExteriorTailConstant a sigma kappa := by
    rw [xiMassBesselExteriorTailConstant]
    have h1 : 0 ≤ xiMassBesselExteriorConstant a sigma kappa :=
      xiMassBesselExteriorConstant_nonneg ha0 hsigma hkappa
    have h2 : 0 ≤ primeLogRpowTailConstant (a - 1 / 2) :=
      primeLogRpowTailConstant_nonneg (by linarith)
    have h3 : (0 : ℝ) < (2 : ℝ) ^ (a - 1 / 2) := Real.rpow_pos_of_pos (by norm_num) _
    exact mul_nonneg h1 (mul_nonneg h3.le h2)
  refine ⟨xiMassBesselExteriorTailConstant a sigma kappa + B, by linarith, fun u hu => ?_⟩
  have hann := norm_xiMassCriticalTruePrimeCone_slope_difference_le ha hsigma hkappa hkk hu
  have hout := hB u hu
  have hsolve : xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u
      - xiMassCriticalOutgoingFlux a sigma u
      = -(xiMassCriticalTruePrimeCone a sigma d' u
          - xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u)
        + (xiMassCriticalTruePrimeCone a sigma d' u
          - xiMassCriticalOutgoingFlux a sigma u) := by ring
  rw [hsolve]
  have htri := norm_add_le
    (-(xiMassCriticalTruePrimeCone a sigma d' u
        - xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u))
    (xiMassCriticalTruePrimeCone a sigma d' u - xiMassCriticalOutgoingFlux a sigma u)
  rw [norm_neg] at htri
  have hexpone : (1 : ℝ) ≤ Real.exp (lam * u) := Real.one_le_exp (mul_nonneg hlam hu)
  have hexpmono : Real.exp (-(xiMassBesselConeExponent a kappa * u)) ≤ Real.exp (lam * u) := by
    refine Real.exp_le_exp.2 ?_
    nlinarith
  nlinarith [hann, hout, htri, hexpone, hexpmono, hT0, hB0]

/-- **(20.3) The graded Bessel cone criterion.**  For every vertical type `0 ≤ λ < 1/2` and every
slope at or above the graded slope `κ_{a,λ}`, the slope-`κ` true-prime cone has vertical type `λ`
exactly when every mass-shifted Xi point has transverse displacement at most `λ`.  At `λ = 0` this
is the closed sharp Bessel cone criterion, hence the Riemann hypothesis. -/
theorem xiMassCriticalBesselConeLineGrowth_iff_mass_displacement_le {a c sigma kappa lam : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa)
    (hlam : 0 ≤ lam)
    (hslope : -(xiMassBesselConeExponent a kappa) ≤ lam) :
    XiMassCriticalBesselConeLineGrowth a sigma kappa lam ↔
      ∀ q : XiZeroCopy, |((xiMassFamily (show 1 / 2 ≤ a by linarith)).pt q).im| ≤ lam := by
  have ha : 1 / 2 < a := lt_trans hhalf hca
  obtain ⟨K, hK0, hK⟩ := exists_norm_besselCone_sub_outgoingFlux_type_le ha hsigma hkappa hlam
    hslope
  rw [← xiMassCriticalOutgoingFluxLineGrowth_iff_mass_displacement_le hhalf hca hsigma hlam,
    xiMassCriticalOutgoingFluxLineGrowth_iff_nonnegative ha hsigma hlam]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + K, fun u hu => ?_⟩
    have hsolve : xiMassCriticalOutgoingFlux a sigma u
        = xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u
          - (xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u
              - xiMassCriticalOutgoingFlux a sigma u) := by ring
    rw [hsolve]
    refine (norm_sub_le _ _).trans ?_
    have := hC u hu
    have := hK u hu
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨C + K, fun u hu => ?_⟩
    have hsolve : xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u
        = xiMassCriticalOutgoingFlux a sigma u
          + (xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u
              - xiMassCriticalOutgoingFlux a sigma u) := by ring
    rw [hsolve]
    refine (norm_add_le _ _).trans ?_
    have := hC u hu
    have := hK u hu
    linarith

/-- **(20.3) at the graded slope.**  The graded slope itself is admissible for its own type. -/
theorem xiMassCriticalBesselConeLineGrowth_gradedSlope_iff {a c sigma lam : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma)
    (hlam : 0 ≤ lam) (hlamhalf : lam < 1 / 2) :
    XiMassCriticalBesselConeLineGrowth a sigma (xiMassGradedConeSlope a lam) lam ↔
      ∀ q : XiZeroCopy, |((xiMassFamily (show 1 / 2 ≤ a by linarith)).pt q).im| ≤ lam := by
  have ha : 1 / 2 < a := lt_trans hhalf hca
  have hone : 1 < xiMassGradedConeSlope a lam :=
    one_lt_xiMassGradedConeSlope ha hlam hlamhalf
  have hval := xiMassBesselConeExponent_gradedConeSlope ha hlam hlamhalf.le
  exact xiMassCriticalBesselConeLineGrowth_iff_mass_displacement_le hhalf hca hsigma hone hlam
    (le_of_eq hval)

end

end RHTower
