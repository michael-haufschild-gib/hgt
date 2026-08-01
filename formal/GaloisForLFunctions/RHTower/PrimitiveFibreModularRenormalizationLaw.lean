import GaloisForLFunctions.RHTower.EulerActivationSquarefreeDisintegration
import GaloisForLFunctions.RHTower.CCMFirstClockPrimePowerTowerCollapse

/-!
# Primitive--fibre modular renormalization

The local activation source, its Fisher-damped Gamma valuation fibre, and the critical
von-Mangoldt prime-power current are not the same depth profile.  This file gives their exact
factorization.  Rare-prime Fisher whitening is followed by an independent, exponentially
depth-growing primitive promotion.  Functional-equation reflection then acts by a third modular
tilt whose two reflected currents have fixed geometric mean and agree only at the half-density.

At a rational prime these abstract profiles are identified with the existing activation atom,
Möbius Fisher damping, Gamma valuation coordinate, and critical Mellin atom.  No zero hypothesis,
RH assumption, numerical computation, or new axiom is used.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower

/-- Positive activation mass at valuation depth `e + 1`, written in the square-root coordinate
`r`, so the ordinary local Euler parameter is `q = r²`. -/
def primitiveFibreActivationAtom (r : ℝ) (e : ℕ) : ℝ :=
  diagonalActivationPositiveValuationMass (r ^ 2) e

/-- Square root of the local occupancy Fisher information in the coordinate `q = r²`. -/
def primitiveFibreFisherDamping (r : ℝ) : ℝ :=
  r / (1 + r ^ 2)

/-- Half-shifted conditional valuation coordinate. -/
def primitiveFibreGammaAtom (r : ℝ) (e : ℕ) : ℝ :=
  r * (1 - r ^ 2) * (r ^ 2) ^ e

/-- Half-density primitive current with logarithmic primitive weight `ell`. -/
def primitiveFibreCriticalCurrent (ell r : ℝ) (e : ℕ) : ℝ :=
  ell * r ^ (e + 1)

/-- Exact depth gauge promoting the conditional Gamma fibre to the primitive half-density
current. -/
def primitiveFibrePromotionGauge (ell r : ℝ) (e : ℕ) : ℝ :=
  ell / (1 - r ^ 2) * (r⁻¹) ^ e

/-- Direct gauge from the positive activation atom to the primitive current. -/
def primitiveFibreActivationToCurrentGauge (ell r : ℝ) (e : ℕ) : ℝ :=
  ell * (1 + r ^ 2) / (1 - r ^ 2) * (r⁻¹) ^ (e + 1)

/-- Modular tilt away from the reflection-balanced half-density.  If `r = p⁻¹/²` and
`a = sigma - 1/2`, this is `p^(-(sigma-1/2)(e+1))`. -/
def primitiveFibreModularTilt (r a : ℝ) (e : ℕ) : ℝ :=
  Real.exp (2 * a * (e + 1) * Real.log r)

/-- Primitive current after modular tilt by centered exponent `a`. -/
def primitiveFibreModularCurrent (ell r a : ℝ) (e : ℕ) : ℝ :=
  primitiveFibreCriticalCurrent ell r e * primitiveFibreModularTilt r a e

/-- The activation atom is exactly the occupancy-Fisher damping times the conditional Gamma
valuation atom. -/
theorem primitiveFibreActivationAtom_eq_fisher_mul_gamma
    {r : ℝ} (hr0 : 0 < r) (_hr1 : r < 1) (e : ℕ) :
    primitiveFibreActivationAtom r e =
      primitiveFibreFisherDamping r * primitiveFibreGammaAtom r e := by
  have hden : 1 + r ^ 2 ≠ 0 := by positivity
  simp only [primitiveFibreActivationAtom, diagonalActivationPositiveValuationMass,
    primitiveFibreFisherDamping, primitiveFibreGammaAtom, pow_succ]
  field_simp [hden]

/-- The critical primitive current is exactly the Gamma valuation atom multiplied by the
primitive depth-promotion gauge. -/
theorem primitiveFibreCriticalCurrent_eq_promotion_mul_gamma
    {ell r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (e : ℕ) :
    primitiveFibreCriticalCurrent ell r e =
      primitiveFibrePromotionGauge ell r e * primitiveFibreGammaAtom r e := by
  have hr : r ≠ 0 := ne_of_gt hr0
  have hsub : 1 - r ^ 2 ≠ 0 := by nlinarith
  simp only [primitiveFibreCriticalCurrent, primitiveFibrePromotionGauge,
    primitiveFibreGammaAtom, pow_succ]
  field_simp [hr, hsub]
  have hpow : (r⁻¹) ^ e * (r ^ 2) ^ e = r ^ e := by
    rw [← mul_pow]
    congr 1
    field_simp [hr]
  simp only [one_div]
  calc
    ell * r ^ e = ell * ((r⁻¹) ^ e * (r ^ 2) ^ e) := by rw [hpow]
    _ = ell * (r⁻¹) ^ e * (r ^ 2) ^ e := by ring

/-- Direct activation-to-current factorization.  Its gauge includes both Fisher whitening and
primitive depth promotion. -/
theorem primitiveFibreCriticalCurrent_eq_activationGauge_mul_atom
    {ell r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (e : ℕ) :
    primitiveFibreCriticalCurrent ell r e =
      primitiveFibreActivationToCurrentGauge ell r e *
        primitiveFibreActivationAtom r e := by
  have hr : r ≠ 0 := ne_of_gt hr0
  have hsub : 1 - r ^ 2 ≠ 0 := by nlinarith
  have hplus : 1 + r ^ 2 ≠ 0 := by positivity
  simp only [primitiveFibreCriticalCurrent, primitiveFibreActivationToCurrentGauge,
    primitiveFibreActivationAtom, diagonalActivationPositiveValuationMass]
  field_simp [hr, hsub, hplus]
  have hpow : (r⁻¹) ^ (e + 1) * (r ^ 2) ^ (e + 1) = r ^ (e + 1) := by
    rw [← mul_pow]
    congr 1
    field_simp [hr]
  simp only [one_div]
  calc
    ell * r ^ (e + 1) =
        ell * ((r⁻¹) ^ (e + 1) * (r ^ 2) ^ (e + 1)) := by rw [hpow]
    _ = ell * (r⁻¹) ^ (e + 1) * (r ^ 2) ^ (e + 1) := by ring

/-- Opposite modular tilts are reciprocal at every depth. -/
theorem primitiveFibreModularTilt_mul_reflection
    (r a : ℝ) (e : ℕ) :
    primitiveFibreModularTilt r a e *
        primitiveFibreModularTilt r (-a) e = 1 := by
  simp only [primitiveFibreModularTilt, ← Real.exp_add]
  ring_nf
  exact Real.exp_zero

/-- Reflected primitive currents have the critical half-density current as exact geometric
mean. -/
theorem primitiveFibreModularCurrent_mul_reflection
    (ell r a : ℝ) (e : ℕ) :
    primitiveFibreModularCurrent ell r a e *
        primitiveFibreModularCurrent ell r (-a) e =
      primitiveFibreCriticalCurrent ell r e ^ 2 := by
  rw [primitiveFibreModularCurrent, primitiveFibreModularCurrent]
  rw [show primitiveFibreCriticalCurrent ell r e * primitiveFibreModularTilt r a e *
      (primitiveFibreCriticalCurrent ell r e * primitiveFibreModularTilt r (-a) e) =
      primitiveFibreCriticalCurrent ell r e ^ 2 *
        (primitiveFibreModularTilt r a e * primitiveFibreModularTilt r (-a) e) by ring]
  rw [primitiveFibreModularTilt_mul_reflection]
  ring

/-- The half-density is the unique pointwise reflection-balanced primitive current. -/
theorem primitiveFibreModularCurrent_eq_reflection_iff
    {ell r a : ℝ} (hell : 0 < ell) (hr0 : 0 < r) (hr1 : r < 1) (e : ℕ) :
    primitiveFibreModularCurrent ell r a e =
        primitiveFibreModularCurrent ell r (-a) e ↔ a = 0 := by
  have hcurrent : primitiveFibreCriticalCurrent ell r e ≠ 0 := by
    unfold primitiveFibreCriticalCurrent
    exact mul_ne_zero hell.ne' (pow_ne_zero _ hr0.ne')
  constructor
  · intro h
    simp only [primitiveFibreModularCurrent] at h
    apply mul_left_cancel₀ hcurrent at h
    unfold primitiveFibreModularTilt at h
    apply Real.exp_injective at h
    have hlog : Real.log r ≠ 0 := (Real.log_neg hr0 hr1).ne
    have hk : (e + 1 : ℝ) ≠ 0 := by positivity
    have hz : a * ((e + 1 : ℝ) * Real.log r) = 0 := by
      nlinarith
    exact (mul_eq_zero.mp hz).resolve_right (mul_ne_zero hk hlog)
  · rintro rfl
    simp [primitiveFibreModularCurrent, primitiveFibreModularTilt]

/-- Exact scalar sewing cost from centered rate `a` to its reflection. -/
def primitiveFibreReflectedSewingRatio (r a : ℝ) (e : ℕ) : ℝ :=
  Real.exp (-4 * a * (e + 1) * Real.log r)

/-- The reflected-current quotient is the explicit sewing ratio. -/
theorem primitiveFibreReflectedSewingRatio_eq
    {ell r a : ℝ} (hell : 0 < ell) (hr0 : 0 < r) (e : ℕ) :
    primitiveFibreModularCurrent ell r (-a) e /
        primitiveFibreModularCurrent ell r a e =
      primitiveFibreReflectedSewingRatio r a e := by
  have hcurrent : primitiveFibreCriticalCurrent ell r e ≠ 0 := by
    unfold primitiveFibreCriticalCurrent
    exact mul_ne_zero hell.ne' (pow_ne_zero _ hr0.ne')
  have htilt : primitiveFibreModularTilt r a e ≠ 0 := Real.exp_ne_zero _
  simp only [primitiveFibreModularCurrent, primitiveFibreModularTilt,
    primitiveFibreReflectedSewingRatio]
  field_simp [hcurrent, htilt]
  rw [← Real.exp_add]
  congr 1
  ring

/-- A positive off-center rate makes the reflected sewing cost diverge exponentially in valuation
depth. -/
theorem tendsto_primitiveFibreReflectedSewingRatio_of_pos
    {r a : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (ha : 0 < a) :
    Tendsto (primitiveFibreReflectedSewingRatio r a) atTop atTop := by
  let b : ℝ := Real.exp (-4 * a * Real.log r)
  have hb : 1 < b := by
    rw [Real.one_lt_exp_iff]
    have hlog := Real.log_neg hr0 hr1
    nlinarith
  have hpow := tendsto_pow_atTop_atTop_of_one_lt hb
  have hb0 : 0 < b := Real.exp_pos _
  have hmul := hpow.atTop_mul_const hb0
  convert hmul using 1
  funext e
  simp only [primitiveFibreReflectedSewingRatio, b]
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

/-- At every nonzero centered rate, one direction of reflected sewing has exponentially
unbounded depth cost. -/
theorem primitiveFibreReflectedSewingRatio_unbounded
    {r a : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (ha : a ≠ 0) :
    Tendsto (primitiveFibreReflectedSewingRatio r a) atTop atTop ∨
      Tendsto (primitiveFibreReflectedSewingRatio r (-a)) atTop atTop := by
  rcases lt_or_gt_of_ne ha with haNeg | haPos
  · exact Or.inr
      (tendsto_primitiveFibreReflectedSewingRatio_of_pos hr0 hr1 (neg_pos.mpr haNeg))
  · exact Or.inl
      (tendsto_primitiveFibreReflectedSewingRatio_of_pos hr0 hr1 haPos)

/-- Primitive promotion from the Gamma valuation fibre is necessarily unbounded in depth, even
at the reflection-balanced half-density. -/
theorem tendsto_primitiveFibrePromotionGauge
    {ell r : ℝ} (hell : 0 < ell) (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto (primitiveFibrePromotionGauge ell r) atTop atTop := by
  have hbase : 1 < r⁻¹ := (one_lt_inv₀ hr0).mpr hr1
  have hconst : 0 < ell / (1 - r ^ 2) := by
    have hs : r ^ 2 < 1 := by
      nlinarith [mul_pos hr0 (sub_pos.mpr hr1)]
    exact div_pos hell (sub_pos.mpr hs)
  exact (tendsto_pow_atTop_atTop_of_one_lt hbase).const_mul_atTop hconst

/-- The direct activation-to-current gauge is also necessarily unbounded in depth. -/
theorem tendsto_primitiveFibreActivationToCurrentGauge
    {ell r : ℝ} (hell : 0 < ell) (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto (primitiveFibreActivationToCurrentGauge ell r) atTop atTop := by
  have hbase : 1 < r⁻¹ := (one_lt_inv₀ hr0).mpr hr1
  have hs : r ^ 2 < 1 := by
    nlinarith [mul_pos hr0 (sub_pos.mpr hr1)]
  have hconst : 0 < ell * (1 + r ^ 2) / (1 - r ^ 2) * r⁻¹ := by
    positivity
  have hpow := (tendsto_pow_atTop_atTop_of_one_lt hbase).const_mul_atTop hconst
  convert hpow using 1
  funext e
  rw [primitiveFibreActivationToCurrentGauge, pow_succ]
  ring

/-! ### Literal prime specializations -/

/-- The abstract activation atom becomes the literal diagonal Euler activation mass. -/
theorem primitiveFibreActivationAtom_prime
    (p : Nat.Primes) (e : ℕ) :
    primitiveFibreActivationAtom (criticalPrimeTowerRadius p) e =
      diagonalActivationPositiveValuationMass ((p : ℝ)⁻¹) e := by
  rw [primitiveFibreActivationAtom, criticalPrimeTowerRadius_sq]

/-- The abstract Fisher factor becomes the literal Möbius Schur damping. -/
theorem primitiveFibreFisherDamping_prime
    (p : Nat.Primes) :
    primitiveFibreFisherDamping (criticalPrimeTowerRadius p) =
      xiMobiusPrimeSchurValuationDamping p := by
  rw [primitiveFibreFisherDamping, xiMobiusPrimeSchurValuationDamping,
    xiTransversePrimeApertureDiskNode_one_eq_inv, ← criticalPrimeTowerRadius_sq]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (criticalPrimeTowerRadius_pos p.property.pos)]

/-- The abstract Gamma atom becomes the literal half-shifted Gamma valuation coordinate. -/
theorem primitiveFibreGammaAtom_prime
    (p : Nat.Primes) (e : ℕ) :
    primitiveFibreGammaAtom (criticalPrimeTowerRadius p) e =
      xiTransversePrimeHalfShiftedValuationCoordinate p e := by
  simp only [primitiveFibreGammaAtom,
    xiTransversePrimeHalfShiftedValuationCoordinate,
    xiTransversePrimeValuationIncrement]
  rw [xiTransversePrimeApertureDiskNode_one_eq_inv, ← criticalPrimeTowerRadius_sq]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (criticalPrimeTowerRadius_pos p.property.pos)]
  ring

/-- The abstract primitive half-density becomes the literal critical Mellin/von-Mangoldt atom. -/
theorem primitiveFibreCriticalCurrent_prime
    (p : Nat.Primes) (e : ℕ) :
    primitiveFibreCriticalCurrent (Real.log (p : ℝ))
        (criticalPrimeTowerRadius p) e =
      criticalMellinAtomWeight ((p : ℕ) ^ (e + 1)) := by
  rw [primitiveFibreCriticalCurrent,
    criticalMellinAtomWeight_prime_pow p.property (by omega)]

/-- Exact local certificate collecting Fisher disintegration, primitive promotion, and modular
reflection. -/
structure PrimitiveFibreRenormalizationCertificate
    (ell r : ℝ) (e : ℕ) : Prop where
  activationToGamma :
    primitiveFibreActivationAtom r e =
      primitiveFibreFisherDamping r * primitiveFibreGammaAtom r e
  gammaToPrimitive :
    primitiveFibreCriticalCurrent ell r e =
      primitiveFibrePromotionGauge ell r e * primitiveFibreGammaAtom r e
  activationToPrimitive :
    primitiveFibreCriticalCurrent ell r e =
      primitiveFibreActivationToCurrentGauge ell r e *
        primitiveFibreActivationAtom r e
  reflectionProduct : ∀ a : ℝ,
    primitiveFibreModularCurrent ell r a e *
        primitiveFibreModularCurrent ell r (-a) e =
      primitiveFibreCriticalCurrent ell r e ^ 2
  reflectionBalance : ∀ a : ℝ,
    primitiveFibreModularCurrent ell r a e =
        primitiveFibreModularCurrent ell r (-a) e ↔ a = 0

/-- **Primitive--fibre modular renormalization law.**  Positive activation reaches the Gamma
valuation fibre by Fisher damping, the Gamma fibre reaches the logarithmically primitive
half-density only through an unbounded depth promotion, and reflected modular currents agree
only at the half-density. -/
theorem primitiveFibreRenormalization_law
    {ell r : ℝ} (hell : 0 < ell) (hr0 : 0 < r) (hr1 : r < 1) (e : ℕ) :
    PrimitiveFibreRenormalizationCertificate ell r e where
  activationToGamma := primitiveFibreActivationAtom_eq_fisher_mul_gamma hr0 hr1 e
  gammaToPrimitive := primitiveFibreCriticalCurrent_eq_promotion_mul_gamma hr0 hr1 e
  activationToPrimitive :=
    primitiveFibreCriticalCurrent_eq_activationGauge_mul_atom hr0 hr1 e
  reflectionProduct := fun a => primitiveFibreModularCurrent_mul_reflection ell r a e
  reflectionBalance := fun a =>
    primitiveFibreModularCurrent_eq_reflection_iff (a := a) hell hr0 hr1 e

end RHTower
