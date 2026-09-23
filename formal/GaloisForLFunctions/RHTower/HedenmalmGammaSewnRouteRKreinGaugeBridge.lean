import GaloisForLFunctions.RHTower.HedenmalmGammaSewnRouteRCriticalWallBridge
import GaloisForLFunctions.RHTower.FisherDeconvolvedSameCarrierOrientationLaw

/-!
# Route N / Route R exact Krein-gauge bridge

The positive Route N critical-horizon energy loses orientation by adding the squared masses of its
two marked channels.  Retaining their canonical indefinite difference exposes the signed source
current.  Prime by prime, this Route N Krein charge becomes the exact Route R critical-wall Gamma
Bockstein after multiplication by one grade-independent Fisher gauge

`g(p) = p * d(p) = p^(2 : ℕ) / (p + 1)^(2 : ℕ)`.

The gauge lies uniformly in `[1/4, 1]`; its reciprocal is uniformly bounded.  Hence it induces a
canonical automorphism of the fixed all-prime quotient by `ell^(1 : ℕ)`, and the Route N Krein class and
Route R wall class are exactly gauge-conjugate there.  No Xi value, zero, or RH hypothesis occurs.
-/

open Complex

namespace RHTower

noncomputable section

def hedenmalmMarkedPrimeKreinCharge (v : ℂ × ℂ) : ℝ :=
  Complex.normSq v.1 - Complex.normSq v.2

def routeNGammaSewnCriticalHorizonKreinCharge
    (t : ℝ) (p : Nat.Primes) : ℝ :=
  hedenmalmMarkedPrimeKreinCharge
    (gammaSewnHedenmalmDampedMarkedCharacter |t| p ((t : ℂ) * I))

theorem routeNGammaSewnCriticalHorizonKreinCharge_eq
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnCriticalHorizonKreinCharge t p =
      (p.1 : ℝ) ^ (-|t|) *
        ((p.1 : ℝ) ^ (-t) - (p.1 : ℝ) ^ t) / (p.1 : ℝ) := by
  have hp0 : (0 : ℝ) < p.1 := by exact_mod_cast p.2.pos
  rw [routeNGammaSewnCriticalHorizonKreinCharge,
    hedenmalmMarkedPrimeKreinCharge,
    gammaSewnHedenmalmDampedMarkedCharacter]
  dsimp only
  rw [Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_ofReal,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    Complex.norm_exp, Complex.norm_exp]
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
    zero_mul, mul_zero, one_mul, zero_sub, neg_im, neg_one_mul]
  ring_nf
  rw [gammaSewnHedenmalmFisherHalfDensity_sq]
  rw [Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hp0,
    Real.rpow_def_of_pos hp0]
  rw [show -|t| * Real.log (p.1 : ℝ) =
      (-|t|) * Real.log (p.1 : ℝ) by ring]
  rw [show ((p.1 : ℝ))⁻¹ = Real.exp (-Real.log (p.1 : ℝ)) by
    rw [Real.exp_neg, Real.exp_log hp0]]
  ring_nf
  have hminus :
      Real.exp (Real.log (p.1 : ℝ) * t * (-1 / 2)) ^ 2 =
        Real.exp (-(Real.log (p.1 : ℝ) * t)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hplus :
      Real.exp (Real.log (p.1 : ℝ) * t * (1 / 2)) ^ 2 =
        Real.exp (Real.log (p.1 : ℝ) * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hminus, hplus]
  rw [show ((p.1 : ℝ))⁻¹ = Real.exp (-Real.log (p.1 : ℝ)) by
    rw [Real.exp_neg, Real.exp_log hp0]]
  ring

def routeNGammaSewnFisherGauge (p : Nat.Primes) : ℝ :=
  (p.1 : ℝ) * primeActivationOccupancyFisherDensity p

theorem routeR_eq_fisherGauge_mul_routeNKrein
    (t : ℝ) (p : Nat.Primes) :
    primeGammaCofinalBocksteinCriticalWallCoefficient t p =
      routeNGammaSewnFisherGauge p *
        routeNGammaSewnCriticalHorizonKreinCharge t p := by
  rw [primeGammaCofinalBocksteinCriticalWallCoefficient,
    primeActivationOccupancyFisherTwist,
    primeActivationOccupancyFisherTwist,
    routeNGammaSewnFisherGauge,
    routeNGammaSewnCriticalHorizonKreinCharge_eq]
  have hp0 : (0 : ℝ) < p.1 := by exact_mod_cast p.2.pos
  field_simp [hp0.ne']

theorem routeNGammaSewnFisherGauge_bounds (p : Nat.Primes) :
    (1 / 4 : ℝ) ≤ routeNGammaSewnFisherGauge p ∧
      routeNGammaSewnFisherGauge p ≤ 1 := by
  have hp0 : (0 : ℝ) < p.1 := by exact_mod_cast p.2.pos
  have hbounds := primeActivationOccupancyFisherDensity_bounds p
  rw [routeNGammaSewnFisherGauge]
  constructor
  · calc
      (1 / 4 : ℝ) = (p.1 : ℝ) * (1 / (4 * (p.1 : ℝ))) := by
        field_simp [hp0.ne']
      _ ≤ (p.1 : ℝ) * primeActivationOccupancyFisherDensity p :=
        mul_le_mul_of_nonneg_left hbounds.1 hp0.le
  · calc
      (p.1 : ℝ) * primeActivationOccupancyFisherDensity p ≤
          (p.1 : ℝ) * (1 / (p.1 : ℝ)) :=
        mul_le_mul_of_nonneg_left hbounds.2 hp0.le
      _ = 1 := by field_simp [hp0.ne']

theorem routeNGammaSewnFisherGauge_pos (p : Nat.Primes) :
    0 < routeNGammaSewnFisherGauge p := by
  linarith [(routeNGammaSewnFisherGauge_bounds p).1]

def routeNGammaSewnFisherGaugeSequence : AllPrimeComplexSequence :=
  fun p => (routeNGammaSewnFisherGauge p : ℂ)

def routeNGammaSewnCriticalHorizonKreinPrimeSequence
    (t : ℝ) : AllPrimeComplexSequence :=
  fun p => (routeNGammaSewnCriticalHorizonKreinCharge t p : ℂ)

def routeRPrimeGammaCriticalWallPrimeSequence
    (t : ℝ) : AllPrimeComplexSequence :=
  fun p => (primeGammaCofinalBocksteinCriticalWallCoefficient t p : ℂ)

theorem routeRPrimeGammaCriticalWallPrimeSequence_eq_gauge_mul_routeNKrein
    (t : ℝ) :
    routeRPrimeGammaCriticalWallPrimeSequence t =
      primeDiagonalMultiplier routeNGammaSewnFisherGaugeSequence
        (routeNGammaSewnCriticalHorizonKreinPrimeSequence t) := by
  funext p
  change
    (primeGammaCofinalBocksteinCriticalWallCoefficient t p : ℂ) =
      (routeNGammaSewnFisherGauge p : ℂ) *
        (routeNGammaSewnCriticalHorizonKreinCharge t p : ℂ)
  exact_mod_cast routeR_eq_fisherGauge_mul_routeNKrein t p

theorem summable_routeRPrimeGammaCriticalWallPrimeSequence_iff (t : ℝ) :
    Summable (routeRPrimeGammaCriticalWallPrimeSequence t) ↔ t = 0 := by
  rw [← nthPrimeEquiv.summable_iff]
  have hsequence :
      (routeRPrimeGammaCriticalWallPrimeSequence t) ∘ nthPrimeEquiv =
        routeRPrimeGammaCriticalWallSequence t := by
    funext n
    rw [Function.comp_apply, routeRPrimeGammaCriticalWallPrimeSequence,
      routeRPrimeGammaCriticalWallSequence_apply]
  rw [hsequence, summable_routeRPrimeGammaCriticalWallSequence_iff]

theorem routeNGammaSewnFisherGaugeSequence_isBounded :
    Bornology.IsBounded (Set.range routeNGammaSewnFisherGaugeSequence) := by
  refine isBounded_iff_forall_norm_le.mpr ⟨1, ?_⟩
  intro z hz
  obtain ⟨p, rfl⟩ := hz
  rw [routeNGammaSewnFisherGaugeSequence, Complex.norm_real,
    Real.norm_of_nonneg (routeNGammaSewnFisherGauge_pos p).le]
  exact (routeNGammaSewnFisherGauge_bounds p).2

theorem routeNGammaSewnFisherGaugeSequence_inv_isBounded :
    Bornology.IsBounded
      (Set.range (fun p : Nat.Primes =>
        (routeNGammaSewnFisherGaugeSequence p)⁻¹)) := by
  refine isBounded_iff_forall_norm_le.mpr ⟨4, ?_⟩
  intro z hz
  obtain ⟨p, rfl⟩ := hz
  rw [norm_inv, routeNGammaSewnFisherGaugeSequence, Complex.norm_real,
    Real.norm_of_nonneg (routeNGammaSewnFisherGauge_pos p).le]
  rw [inv_le_comm₀ (routeNGammaSewnFisherGauge_pos p) (by norm_num : (0 : ℝ) < 4)]
  nlinarith [(routeNGammaSewnFisherGauge_bounds p).1]

theorem routeNGammaSewnFisherGaugeSequence_preservesL1 :
    PrimeDiagonalPreservesL1 routeNGammaSewnFisherGaugeSequence :=
  primeDiagonalPreservesL1_of_isBounded
    routeNGammaSewnFisherGaugeSequence_isBounded

theorem routeNGammaSewnFisherGaugeSequence_inv_preservesL1 :
    PrimeDiagonalPreservesL1
      (fun p : Nat.Primes =>
        (routeNGammaSewnFisherGaugeSequence p)⁻¹) :=
  primeDiagonalPreservesL1_of_isBounded
    routeNGammaSewnFisherGaugeSequence_inv_isBounded

theorem summable_routeNGammaSewnCriticalHorizonKreinPrimeSequence_iff
    (t : ℝ) :
    Summable (routeNGammaSewnCriticalHorizonKreinPrimeSequence t) ↔
      t = 0 := by
  constructor
  · intro hq
    have hr := routeNGammaSewnFisherGaugeSequence_preservesL1 hq
    change Summable
      (primeDiagonalMultiplier routeNGammaSewnFisherGaugeSequence
        (routeNGammaSewnCriticalHorizonKreinPrimeSequence t)) at hr
    rw [← routeRPrimeGammaCriticalWallPrimeSequence_eq_gauge_mul_routeNKrein] at hr
    exact (summable_routeRPrimeGammaCriticalWallPrimeSequence_iff t).mp hr
  · rintro rfl
    have hzero :
        routeNGammaSewnCriticalHorizonKreinPrimeSequence 0 = 0 := by
      funext p
      change (routeNGammaSewnCriticalHorizonKreinCharge 0 p : ℂ) = 0
      rw [routeNGammaSewnCriticalHorizonKreinCharge_eq]
      norm_num
    rw [hzero]
    exact summable_zero

def routeNGammaSewnFisherGaugeQuotientMap :
    AllPrimeL1Quotient →ₗ[ℂ] AllPrimeL1Quotient :=
  primeDiagonalQuotientMap routeNGammaSewnFisherGaugeSequence
    routeNGammaSewnFisherGaugeSequence_preservesL1

def routeNGammaSewnFisherGaugeInverseQuotientMap :
    AllPrimeL1Quotient →ₗ[ℂ] AllPrimeL1Quotient :=
  primeDiagonalQuotientMap
    (fun p : Nat.Primes =>
      (routeNGammaSewnFisherGaugeSequence p)⁻¹)
    routeNGammaSewnFisherGaugeSequence_inv_preservesL1

theorem routeNGammaSewnFisherGaugeInverseQuotientMap_comp :
    routeNGammaSewnFisherGaugeInverseQuotientMap.comp
        routeNGammaSewnFisherGaugeQuotientMap =
      LinearMap.id := by
  apply LinearMap.ext
  intro q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective primeL1Submodule q
  rw [LinearMap.comp_apply, routeNGammaSewnFisherGaugeInverseQuotientMap,
    routeNGammaSewnFisherGaugeQuotientMap,
    primeDiagonalQuotientMap_mk, primeDiagonalQuotientMap_mk,
    LinearMap.id_apply]
  congr 1
  funext p
  simp only [primeDiagonalMultiplier, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← mul_assoc, inv_mul_cancel₀]
  · exact one_mul (f p)
  · rw [routeNGammaSewnFisherGaugeSequence]
    exact_mod_cast (routeNGammaSewnFisherGauge_pos p).ne'

theorem routeNGammaSewnFisherGaugeQuotientMap_comp_inverse :
    routeNGammaSewnFisherGaugeQuotientMap.comp
        routeNGammaSewnFisherGaugeInverseQuotientMap =
      LinearMap.id := by
  apply LinearMap.ext
  intro q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective primeL1Submodule q
  rw [LinearMap.comp_apply, routeNGammaSewnFisherGaugeInverseQuotientMap,
    routeNGammaSewnFisherGaugeQuotientMap,
    primeDiagonalQuotientMap_mk, primeDiagonalQuotientMap_mk,
    LinearMap.id_apply]
  congr 1
  funext p
  simp only [primeDiagonalMultiplier, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← mul_assoc, mul_inv_cancel₀]
  · exact one_mul (f p)
  · rw [routeNGammaSewnFisherGaugeSequence]
    exact_mod_cast (routeNGammaSewnFisherGauge_pos p).ne'

def routeNGammaSewnFisherGaugeQuotientEquiv :
    AllPrimeL1Quotient ≃ₗ[ℂ] AllPrimeL1Quotient :=
  LinearEquiv.ofLinear
    routeNGammaSewnFisherGaugeQuotientMap
    routeNGammaSewnFisherGaugeInverseQuotientMap
    routeNGammaSewnFisherGaugeQuotientMap_comp_inverse
    routeNGammaSewnFisherGaugeInverseQuotientMap_comp

theorem routeRPrimeGammaCriticalWallClass_eq_gauge_routeNKreinClass
    (t : ℝ) :
    Submodule.Quotient.mk (routeRPrimeGammaCriticalWallPrimeSequence t) =
      routeNGammaSewnFisherGaugeQuotientEquiv
        (Submodule.Quotient.mk
          (routeNGammaSewnCriticalHorizonKreinPrimeSequence t)) := by
  rw [routeNGammaSewnFisherGaugeQuotientEquiv,
    LinearEquiv.ofLinear_apply,
    routeNGammaSewnFisherGaugeQuotientMap,
    primeDiagonalQuotientMap_mk,
    ← routeRPrimeGammaCriticalWallPrimeSequence_eq_gauge_mul_routeNKrein]

end

end RHTower
