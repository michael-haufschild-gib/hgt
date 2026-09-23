import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekSingularFlatReflectionCarrier

/-!
# Singular PW reflection is an algebraic rescaling gauge

The unique positive-ray singular Parikh--Wilczek carrier has gain

`a(x) = x⁻¹ exp(x - x⁻¹)`.

This module proves that `a(x) a(x⁻¹) = 1` and, more strongly, that this positive reciprocal
cocycle is the explicit coboundary `g(x) / g(x⁻¹)` for `g = sqrt a`. Therefore its weighted
reciprocal reflection is globally conjugate, by multiplication with `g`, to bare reciprocal
reflection. On every two-channel orbit the same statement is diagonal similarity to channel
exchange.

Consequently no predicate invariant under positive channel rescaling can distinguish the
self-dual scale from any other positive scale. Involutivity, algebraic conservation, spectrum,
and existence of some positive conserved energy cannot force the missing PW partner balance.

The strongest positive survivor is exact. The source-adapted positive energy is conserved at
every scale, whereas fixed neutral-channel energy is conserved exactly at `x = 1`. Moreover the
trivializing gauge tends to zero, and its inverse to infinity, at the singular Borel boundary.
Thus a surviving PW-B route must supply source-independent channel calibration or use operator
domains/connections sensitive to that boundary singularity.

This kills the algebraic/rescaling-invariant singular-carrier sewing class in

`PW endpoint winding -> singular FE partner -> partner balance -> Deninger Ward -> RH`.

`[NEW] [PW-B ROUTE-CLASS NO-GO] [COBOUNDARY] [EXACT POSITIVE SURVIVOR] [LEAN-PROVED]`
-/

open Complex Real Filter Set Topology

namespace RHTower

noncomputable section

/-- Exact singular PW gain in the positive square-root coordinate. -/
def pwSingularReflectionGain (x : ℝ) : ℝ :=
  schwarzschildParikhWilczekSingularFlatMultiplier (x ^ (2 : ℕ))

theorem pwSingularReflectionGain_eq
    {x : ℝ} (hx : 0 < x) :
    pwSingularReflectionGain x = x⁻¹ * Real.exp (x - x⁻¹) := by
  exact schwarzschildParikhWilczekSingularFlatMultiplier_of_sq hx

theorem pwSingularReflectionGain_pos
    {x : ℝ} (hx : 0 < x) :
    0 < pwSingularReflectionGain x := by
  rw [pwSingularReflectionGain_eq hx]
  positivity

theorem pwSingularReflectionGain_one :
    pwSingularReflectionGain 1 = 1 := by
  rw [pwSingularReflectionGain_eq zero_lt_one]
  norm_num

/-- The forced singular multiplier is a positive reciprocal cocycle. -/
theorem pwSingularReflectionGain_mul_inv
    {x : ℝ} (hx : 0 < x) :
    pwSingularReflectionGain x * pwSingularReflectionGain x⁻¹ = 1 := by
  rw [pwSingularReflectionGain_eq hx,
    pwSingularReflectionGain_eq (inv_pos.mpr hx), inv_inv]
  calc
    x⁻¹ * Real.exp (x - x⁻¹) *
          (x * Real.exp (x⁻¹ - x)) =
        (x⁻¹ * x) *
          (Real.exp (x - x⁻¹) * Real.exp (x⁻¹ - x)) := by ring
    _ = Real.exp (x - x⁻¹) * Real.exp (x⁻¹ - x) := by
      rw [inv_mul_cancel₀ hx.ne', one_mul]
    _ = Real.exp ((x - x⁻¹) + (x⁻¹ - x)) := by
      rw [Real.exp_add]
    _ = 1 := by ring_nf; exact Real.exp_zero

theorem pwSingularReflectionGain_inv_eq
    {x : ℝ} (hx : 0 < x) :
    pwSingularReflectionGain x⁻¹ = (pwSingularReflectionGain x)⁻¹ := by
  apply (mul_left_cancel₀ (pwSingularReflectionGain_pos hx).ne')
  rw [pwSingularReflectionGain_mul_inv hx]
  exact (mul_inv_cancel₀ (pwSingularReflectionGain_pos hx).ne').symm

/-- Positive square-root gauge trivializing the reciprocal cocycle. -/
def pwSingularReflectionGauge (x : ℝ) : ℝ :=
  Real.sqrt (pwSingularReflectionGain x)

theorem pwSingularReflectionGauge_pos
    {x : ℝ} (hx : 0 < x) :
    0 < pwSingularReflectionGauge x := by
  exact Real.sqrt_pos.mpr (pwSingularReflectionGain_pos hx)

theorem pwSingularReflectionGauge_inv
    {x : ℝ} (hx : 0 < x) :
    pwSingularReflectionGauge x⁻¹ =
      (pwSingularReflectionGauge x)⁻¹ := by
  simp only [pwSingularReflectionGauge,
    pwSingularReflectionGain_inv_eq hx, Real.sqrt_inv]

/-- Global coboundary identity for the exact singular PW carrier. -/
theorem pwSingularReflectionGain_eq_gauge_div_reflected
    {x : ℝ} (hx : 0 < x) :
    pwSingularReflectionGain x =
      pwSingularReflectionGauge x /
        pwSingularReflectionGauge x⁻¹ := by
  rw [pwSingularReflectionGauge_inv hx, div_eq_mul_inv, inv_inv,
    pwSingularReflectionGauge, ← pow_two,
    Real.sq_sqrt (pwSingularReflectionGain_pos hx).le]

def pwBareReciprocalReflection (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f x⁻¹

def pwSingularWeightedReflection (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  pwSingularReflectionGain x * f x⁻¹

def pwSingularGaugeMultiplication (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  pwSingularReflectionGauge x * f x

def pwSingularGaugeInverseMultiplication (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (pwSingularReflectionGauge x)⁻¹ * f x

/-- The entire weighted reciprocal reflection is multiplication-conjugate to bare reflection. -/
theorem pwSingularWeightedReflection_gauge_conjugacy
    (f : ℝ → ℝ) {x : ℝ} (hx : 0 < x) :
    pwSingularGaugeMultiplication
        (pwBareReciprocalReflection
          (pwSingularGaugeInverseMultiplication f)) x =
      pwSingularWeightedReflection f x := by
  rw [pwSingularGaugeMultiplication, pwBareReciprocalReflection,
    pwSingularGaugeInverseMultiplication, pwSingularWeightedReflection,
    ← mul_assoc, ← div_eq_mul_inv,
    ← pwSingularReflectionGain_eq_gauge_div_reflected hx]

abbrev PWReflectionPair := ℝ × ℝ

def pwSingularReflectionBlock (x : ℝ) (w : PWReflectionPair) : PWReflectionPair :=
  (pwSingularReflectionGain x * w.2,
    (pwSingularReflectionGain x)⁻¹ * w.1)

def pwPositiveChannelScale (c : ℝ) (w : PWReflectionPair) : PWReflectionPair :=
  (c * w.1, w.2)

def pwPositiveChannelScaleInv (c : ℝ) (w : PWReflectionPair) : PWReflectionPair :=
  (c⁻¹ * w.1, w.2)

/-- Every exact singular block is diagonally conjugate to bare channel exchange. -/
theorem pwSingularReflectionBlock_eq_scale_conjugate
    (x : ℝ) :
    pwSingularReflectionBlock x =
      pwPositiveChannelScale (pwSingularReflectionGain x) ∘
        pwSingularReflectionBlock 1 ∘
          pwPositiveChannelScaleInv (pwSingularReflectionGain x) := by
  funext w
  rcases w with ⟨u, v⟩
  simp [pwSingularReflectionBlock, pwPositiveChannelScale,
    pwPositiveChannelScaleInv, pwSingularReflectionGain_one,
    Function.comp_apply]

/-- Each positive singular block remains an involution. -/
theorem pwSingularReflectionBlock_involutive
    {x : ℝ} (hx : 0 < x) (w : PWReflectionPair) :
    pwSingularReflectionBlock x (pwSingularReflectionBlock x w) = w := by
  rcases w with ⟨u, v⟩
  ext <;>
    simp [pwSingularReflectionBlock,
      (pwSingularReflectionGain_pos hx).ne']

/-- Predicate uses no fixed normalization of the two reflected channels. -/
def PWChannelRescalingInvariant
    (P : (PWReflectionPair → PWReflectionPair) → Prop) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ T : PWReflectionPair → PWReflectionPair,
    P (pwPositiveChannelScale c ∘ T ∘ pwPositiveChannelScaleInv c) ↔ P T

/-- Predicate selects precisely the self-dual PW scale. -/
def PWSingularWallSelector
    (P : (PWReflectionPair → PWReflectionPair) → Prop) : Prop :=
  ∀ x : ℝ, 0 < x → (P (pwSingularReflectionBlock x) ↔ x = 1)

/-- Universal route-class no-go: no rescaling-blind block criterion can select the wall. -/
theorem no_pwChannelRescalingInvariant_singularWallSelector :
    ¬ ∃ P : (PWReflectionPair → PWReflectionPair) → Prop,
      PWChannelRescalingInvariant P ∧ PWSingularWallSelector P := by
  rintro ⟨P, hrescale, hselect⟩
  have hPone : P (pwSingularReflectionBlock 1) :=
    (hselect 1 zero_lt_one).2 rfl
  have hPtwoConj :
      P (pwPositiveChannelScale (pwSingularReflectionGain 2) ∘
        pwSingularReflectionBlock 1 ∘
          pwPositiveChannelScaleInv (pwSingularReflectionGain 2)) :=
    (hrescale (pwSingularReflectionGain 2)
      (pwSingularReflectionGain_pos (by norm_num))
      (pwSingularReflectionBlock 1)).2 hPone
  have hPtwo : P (pwSingularReflectionBlock 2) := by
    rw [pwSingularReflectionBlock_eq_scale_conjugate]
    exact hPtwoConj
  have htwo : (2 : ℝ) = 1 := (hselect 2 (by norm_num)).1 hPtwo
  norm_num at htwo

/-- Source-adapted positive quadratic energy. -/
def pwSingularReflectionEnergy (x : ℝ) (w : PWReflectionPair) : ℝ :=
  (pwSingularReflectionGain x)⁻¹ * w.1 ^ (2 : ℕ) +
    pwSingularReflectionGain x * w.2 ^ (2 : ℕ)

theorem pwSingularReflectionEnergy_pos
    {x : ℝ} (hx : 0 < x) {w : PWReflectionPair} (hw : w ≠ 0) :
    0 < pwSingularReflectionEnergy x w := by
  rcases w with ⟨u, v⟩
  by_cases hu : u = 0
  · have hv : v ≠ 0 := by
      intro hv
      apply hw
      simp [hu, hv]
    simpa [pwSingularReflectionEnergy, hu] using
      mul_pos (pwSingularReflectionGain_pos hx) (sq_pos_of_ne_zero hv)
  · have hleft :
        0 < (pwSingularReflectionGain x)⁻¹ * u ^ (2 : ℕ) :=
      mul_pos (inv_pos.mpr (pwSingularReflectionGain_pos hx))
        (sq_pos_of_ne_zero hu)
    have hright : 0 ≤ pwSingularReflectionGain x * v ^ (2 : ℕ) :=
      mul_nonneg (pwSingularReflectionGain_pos hx).le (sq_nonneg v)
    exact add_pos_of_pos_of_nonneg hleft hright

theorem pwSingularReflectionEnergy_invariant
    {x : ℝ} (hx : 0 < x) (w : PWReflectionPair) :
    pwSingularReflectionEnergy x (pwSingularReflectionBlock x w) =
      pwSingularReflectionEnergy x w := by
  rcases w with ⟨u, v⟩
  simp only [pwSingularReflectionEnergy, pwSingularReflectionBlock]
  field_simp [(pwSingularReflectionGain_pos hx).ne']
  ring

def pwNeutralChannelEnergy (w : PWReflectionPair) : ℝ :=
  w.1 ^ (2 : ℕ) + w.2 ^ (2 : ℕ)

theorem pwSingularReflectionGain_ne_one_of_one_lt
    {x : ℝ} (hx : 1 < x) :
    pwSingularReflectionGain x ≠ 1 := by
  intro hgain
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  rw [pwSingularReflectionGain_eq hxpos] at hgain
  have hexp : Real.exp (x - x⁻¹) = x := by
    have hmul := congrArg (fun t : ℝ => x * t) hgain
    simpa [mul_assoc, hxpos.ne'] using hmul
  have hlog := congrArg Real.log hexp
  have hlogeq : x - x⁻¹ = Real.log x := by
    simpa using hlog
  have hinvpos : 0 < x⁻¹ := inv_pos.mpr hxpos
  have hmul : x * x⁻¹ = 1 := mul_inv_cancel₀ hxpos.ne'
  have hinvlt : x⁻¹ < 1 := by nlinarith
  have hloglt : Real.log x < x - 1 :=
    Real.log_lt_sub_one_of_pos hxpos hx.ne'
  linarith

theorem pwSingularReflectionGain_eq_one_iff
    {x : ℝ} (hx : 0 < x) :
    pwSingularReflectionGain x = 1 ↔ x = 1 := by
  constructor
  · intro hgain
    rcases lt_trichotomy x 1 with hlt | heq | hgt
    · have hinvpos : 0 < x⁻¹ := inv_pos.mpr hx
      have hmul : x * x⁻¹ = 1 := mul_inv_cancel₀ hx.ne'
      have hinvgt : 1 < x⁻¹ := by nlinarith
      have hrec := pwSingularReflectionGain_mul_inv hx
      rw [hgain, one_mul] at hrec
      exact False.elim
        (pwSingularReflectionGain_ne_one_of_one_lt hinvgt hrec)
    · exact heq
    · exact False.elim
        (pwSingularReflectionGain_ne_one_of_one_lt hgt hgain)
  · rintro rfl
    exact pwSingularReflectionGain_one

/-- Fixed neutral energy breaks the rescaling gauge exactly at the self-dual scale. -/
theorem pwNeutralChannelEnergy_block_invariant_iff
    {x : ℝ} (hx : 0 < x) :
    (∀ w : PWReflectionPair,
      pwNeutralChannelEnergy (pwSingularReflectionBlock x w) =
        pwNeutralChannelEnergy w) ↔ x = 1 := by
  constructor
  · intro hinv
    have htest := hinv (0, 1)
    simp [pwNeutralChannelEnergy, pwSingularReflectionBlock] at htest
    have hgainpos := pwSingularReflectionGain_pos hx
    have hgain : pwSingularReflectionGain x = 1 := by
      rcases htest with htest | htest
      · exact htest
      · exfalso
        linarith
    exact (pwSingularReflectionGain_eq_one_iff hx).mp hgain
  · rintro rfl
    intro w
    rcases w with ⟨u, v⟩
    simp [pwNeutralChannelEnergy, pwSingularReflectionBlock,
      pwSingularReflectionGain_one, add_comm]

/-- Trivializing gauge vanishes at the singular Borel boundary. -/
theorem tendsto_pwSingularReflectionGauge_zero :
    Tendsto pwSingularReflectionGauge (𝓝[>] 0) (𝓝 0) := by
  have hsquareNhds : Tendsto (fun x : ℝ => x ^ (2 : ℕ)) (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun x : ℝ => x ^ (2 : ℕ)) 0 :=
      continuousAt_id.pow 2
    simpa using hcont.tendsto
  have hsquare : Tendsto (fun x : ℝ => x ^ (2 : ℕ)) (𝓝[>] 0) (𝓝 0) :=
    hsquareNhds.mono_left inf_le_left
  have hgain : Tendsto pwSingularReflectionGain (𝓝[>] 0) (𝓝 0) := by
    have h :=
      continuousAt_schwarzschildParikhWilczekSingularFlatMultiplier_zero.tendsto.comp
        hsquare
    change Tendsto
      (fun x : ℝ => schwarzschildParikhWilczekSingularFlatMultiplier (x ^ (2 : ℕ)))
      (𝓝[>] 0) (𝓝 0)
    simpa only [Function.comp_def,
      schwarzschildParikhWilczekSingularFlatMultiplier_zero] using h
  change Tendsto (fun x : ℝ => Real.sqrt (pwSingularReflectionGain x))
    (𝓝[>] 0) (𝓝 0)
  simpa only [Real.sqrt_zero] using hgain.sqrt

/-- The inverse trivializing gauge diverges at the singular Borel boundary. -/
theorem tendsto_pwSingularReflectionGauge_inv_atTop :
    Tendsto (fun x : ℝ => (pwSingularReflectionGauge x)⁻¹)
      (𝓝[>] 0) atTop := by
  apply tendsto_inv_nhdsGT_zero.comp
  rw [tendsto_nhdsWithin_iff]
  refine ⟨tendsto_pwSingularReflectionGauge_zero, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact pwSingularReflectionGauge_pos hx

/-- Closed certificate killing algebraic/rescaling-invariant singular-carrier sewing. -/
def PWSingularCarrierRescalingGaugeNoGo : Prop :=
  (∀ x : ℝ, 0 < x →
    pwSingularReflectionGain x * pwSingularReflectionGain x⁻¹ = 1) ∧
  (∀ f : ℝ → ℝ, ∀ x : ℝ, 0 < x →
    pwSingularGaugeMultiplication
        (pwBareReciprocalReflection
          (pwSingularGaugeInverseMultiplication f)) x =
      pwSingularWeightedReflection f x) ∧
  (¬ ∃ P : (PWReflectionPair → PWReflectionPair) → Prop,
    PWChannelRescalingInvariant P ∧ PWSingularWallSelector P) ∧
  (∀ x : ℝ, 0 < x → ∀ w : PWReflectionPair,
    pwSingularReflectionBlock x (pwSingularReflectionBlock x w) = w ∧
    (w ≠ 0 → 0 < pwSingularReflectionEnergy x w) ∧
    pwSingularReflectionEnergy x (pwSingularReflectionBlock x w) =
      pwSingularReflectionEnergy x w) ∧
  (∀ x : ℝ, 0 < x →
    ((∀ w : PWReflectionPair,
      pwNeutralChannelEnergy (pwSingularReflectionBlock x w) =
        pwNeutralChannelEnergy w) ↔ x = 1)) ∧
  Tendsto pwSingularReflectionGauge (𝓝[>] 0) (𝓝 0) ∧
  Tendsto (fun x : ℝ => (pwSingularReflectionGauge x)⁻¹)
    (𝓝[>] 0) atTop

/-- **[PW-B ROUTE-CLASS NO-GO].** The exact singular PW carrier is algebraically gauge-trivial,
no positive channel-rescaling-invariant criterion can select the wall, and neutral calibration is
the exact surviving selector. The trivializing gauge is necessarily singular at the Borel edge. -/
theorem pwSingularCarrier_rescalingGauge_noGo :
    PWSingularCarrierRescalingGaugeNoGo := by
  refine ⟨?_, ?_, no_pwChannelRescalingInvariant_singularWallSelector,
    ?_, ?_, tendsto_pwSingularReflectionGauge_zero,
    tendsto_pwSingularReflectionGauge_inv_atTop⟩
  · intro x hx
    exact pwSingularReflectionGain_mul_inv hx
  · intro f x hx
    exact pwSingularWeightedReflection_gauge_conjugacy f hx
  · intro x hx w
    exact ⟨pwSingularReflectionBlock_involutive hx w,
      fun hw => pwSingularReflectionEnergy_pos hx hw,
      pwSingularReflectionEnergy_invariant hx w⟩
  · intro x hx
    exact pwNeutralChannelEnergy_block_invariant_iff hx

end

end RHTower
