import GaloisForLFunctions.HTGeometry.QuenchedReplicaAction
import GaloisForLFunctions.HTGeometry.PowerMeanEssSupLimit

/-!
# Rare-carrier amortization of the quenched replica mass

The quenched replica mass of a unit-bounded accessibility decreases in the replica order and is
logarithmically convex, by Hölder's inequality.  Its normalized action, the negative logarithm of
the replica-order root, therefore decreases and converges to the essential infimum of the
preparation action.

A positive-mass carrier of bounded action forces the normalized action below its own action plus
the amortized source rarity, which caps the replica orders that can carry a positive certificate
exponent.  The certificate criterion itself is the Gibbs duality read as an inequality between the
replica mass and an exponential threshold.
-/

open MeasureTheory Real Filter Topology

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section ReplicaLimits

variable {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]

/-- The normalized quenched replica action: the negative logarithm of the replica-order root of
the replica mass. -/
def quenchedReplicaAction (ρ : Measure Ω) (F : Ω → ℝ) (r : ℕ) : ℝ :=
  -Real.log (quenchedActionReplicaMass ρ F r ^ ((r : ℝ)⁻¹))

theorem quenchedReplicaAction_eq (F : Ω → ℝ) {r : ℕ}
    (hZ : 0 < quenchedActionReplicaMass ρ F r) :
    quenchedReplicaAction ρ F r = -((r : ℝ)⁻¹ * Real.log (quenchedActionReplicaMass ρ F r)) := by
  rw [quenchedReplicaAction, Real.log_rpow hZ, mul_comm]

theorem quenchedActionReplicaMass_nonneg' {F : Ω → ℝ} (h0 : ∀ x, 0 ≤ F x) (r : ℕ) :
    0 ≤ quenchedActionReplicaMass ρ F r :=
  integral_nonneg fun x => pow_nonneg (h0 x) r

/-- **Unit ceiling.**  The replica mass never exceeds one. -/
theorem quenchedActionReplicaMass_le_one' {F : Ω → ℝ} (hF : Measurable F) (h0 : ∀ x, 0 ≤ F x)
    (h1 : ∀ x, F x ≤ 1) (r : ℕ) : quenchedActionReplicaMass ρ F r ≤ 1 :=
  quenchedActionReplicaMass_le_one ρ h0 h1 r (integrable_pow_of_unit ρ hF h0 h1 r)

/-- **Replica monotonicity.**  The replica mass decreases in the replica order. -/
theorem quenchedActionReplicaMass_antitone' {F : Ω → ℝ} (hF : Measurable F) (h0 : ∀ x, 0 ≤ F x)
    (h1 : ∀ x, F x ≤ 1) (r : ℕ) :
    quenchedActionReplicaMass ρ F (r + 1) ≤ quenchedActionReplicaMass ρ F r :=
  quenchedActionReplicaMass_antitone ρ h0 h1 (integrable_pow_of_unit ρ hF h0 h1 r)
    (integrable_pow_of_unit ρ hF h0 h1 (r + 1))

/-- **Logarithmic convexity.**  Cauchy--Schwarz makes the replica masses logarithmically convex in
the replica order. -/
theorem quenchedActionReplicaMass_sq_le {F : Ω → ℝ} (hF : Measurable F) (h0 : ∀ x, 0 ≤ F x)
    (h1 : ∀ x, F x ≤ 1) (r : ℕ) :
    quenchedActionReplicaMass ρ F (r + 1) ^ 2 ≤
      quenchedActionReplicaMass ρ F r * quenchedActionReplicaMass ρ F (r + 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hmem : ∀ k : ℕ, MemLp (fun x => Real.sqrt (F x ^ k)) (ENNReal.ofReal 2) ρ := by
    intro k
    refine MemLp.of_bound ((hF.pow_const k).sqrt).aestronglyMeasurable 1 ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (pow_le_one₀ (h0 x) (h1 x))
  have hbase := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := ρ) hpq
    (f := fun x => Real.sqrt (F x ^ r)) (g := fun x => Real.sqrt (F x ^ (r + 2)))
    (Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _)
    (Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _) (hmem r) (hmem (r + 2))
  have hsq : ∀ k : ℕ, ∀ x : Ω, (Real.sqrt (F x ^ k)) ^ (2 : ℝ) = F x ^ k := by
    intro k x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.sq_sqrt (pow_nonneg (h0 x) k)]
  have hprod : ∀ x : Ω, Real.sqrt (F x ^ r) * Real.sqrt (F x ^ (r + 2)) = F x ^ (r + 1) := by
    intro x
    rw [← Real.sqrt_mul (pow_nonneg (h0 x) r)]
    rw [show F x ^ r * F x ^ (r + 2) = (F x ^ (r + 1)) ^ 2 by ring]
    exact Real.sqrt_sq (pow_nonneg (h0 x) (r + 1))
  rw [integral_congr_ae (Filter.Eventually.of_forall hprod),
    integral_congr_ae (Filter.Eventually.of_forall (hsq r)),
    integral_congr_ae (Filter.Eventually.of_forall (hsq (r + 2)))] at hbase
  have hA : (0 : ℝ) ≤ (∫ x, F x ^ r ∂ρ) ^ (1 / (2 : ℝ)) :=
    Real.rpow_nonneg (integral_pow_nonneg ρ h0 r) _
  have hB : (0 : ℝ) ≤ (∫ x, F x ^ (r + 2) ∂ρ) ^ (1 / (2 : ℝ)) :=
    Real.rpow_nonneg (integral_pow_nonneg ρ h0 (r + 2)) _
  have hsquare := pow_le_pow_left₀ (integral_pow_nonneg ρ h0 (r + 1)) hbase 2
  rw [mul_pow] at hsquare
  have hrw : ∀ (a : ℝ), 0 ≤ a → (a ^ (1 / (2 : ℝ))) ^ 2 = a := by
    intro a ha
    rw [← Real.rpow_natCast (a ^ (1 / (2 : ℝ))) 2, ← Real.rpow_mul ha]
    norm_num
  rw [hrw _ (integral_pow_nonneg ρ h0 r), hrw _ (integral_pow_nonneg ρ h0 (r + 2))] at hsquare
  exact hsquare

/-- **Normalized replica-action monotonicity.**  The normalized replica action decreases in the
replica order. -/
theorem quenchedReplicaAction_antitone {F : Ω → ℝ} (hF : Measurable F) (h0 : ∀ x, 0 ≤ F x)
    (h1 : ∀ x, F x ≤ 1) {r : ℕ} (hr : 0 < r)
    (hZ : 0 < quenchedActionReplicaMass ρ F r) :
    quenchedReplicaAction ρ F (r + 1) ≤ quenchedReplicaAction ρ F r := by
  have hroot := rpow_inv_integral_pow_monotone ρ hF h0 h1 hr
  have hpos : (0 : ℝ) < quenchedActionReplicaMass ρ F r ^ ((r : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos hZ _
  have hcast : ((r : ℝ) + 1)⁻¹ = (((r + 1 : ℕ) : ℝ))⁻¹ := by push_cast; ring
  rw [hcast] at hroot
  rw [quenchedReplicaAction, quenchedReplicaAction, neg_le_neg_iff]
  exact Real.log_le_log hpos hroot

/-- **Replica-mass root limit.**  The replica-order roots of the replica masses converge to the
essential supremum of the accessibility. -/
theorem tendsto_quenchedActionReplicaMass_rpow {F : Ω → ℝ} (hF : Measurable F) (h0 : ∀ x, 0 ≤ F x)
    (h1 : ∀ x, F x ≤ 1) :
    Tendsto (fun r : ℕ => quenchedActionReplicaMass ρ F r ^ ((r : ℝ)⁻¹)) atTop (𝓝 (essSup F ρ)) :=
  tendsto_rpow_inv_integral_pow ρ hF h0 h1

theorem essSup_pos_of_pos {F : Ω → ℝ} (h1 : ∀ x, F x ≤ 1) (hpos : ∀ x, 0 < F x) :
    0 < essSup F ρ := by
  rcases lt_or_ge 0 (essSup F ρ) with h | h
  · exact h
  · exfalso
    have hfalse : ∀ᵐ _x ∂ρ, False := by
      filter_upwards [ae_le_essSup_of_le_one ρ h1] with x hx
      exact absurd (lt_of_lt_of_le (hpos x) hx) (not_lt.mpr h)
    rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at hfalse
    exact (IsProbabilityMeasure.ne_zero ρ) hfalse

/-- **Normalized replica-action limit.**  The normalized replica action converges to the negative
logarithm of the essential supremum of the accessibility. -/
theorem tendsto_quenchedReplicaAction {F : Ω → ℝ} (hF : Measurable F) (h0 : ∀ x, 0 ≤ F x)
    (h1 : ∀ x, F x ≤ 1) (hpos : ∀ x, 0 < F x) :
    Tendsto (fun r : ℕ => quenchedReplicaAction ρ F r) atTop (𝓝 (-Real.log (essSup F ρ))) := by
  have hM := essSup_pos_of_pos ρ h1 hpos
  exact ((Real.continuousAt_log hM.ne').tendsto.comp
    (tendsto_quenchedActionReplicaMass_rpow ρ hF h0 h1)).neg

/-- The essential infimum of the preparation action is the negative logarithm of the essential
supremum of the accessibility. -/
theorem essInf_preparationActionOf {F : Ω → ℝ} (h1 : ∀ x, F x ≤ 1) (hpos : ∀ x, 0 < F x) :
    essInf (preparationActionOf F) ρ = -Real.log (essSup F ρ) := by
  have hM := essSup_pos_of_pos ρ h1 hpos
  have hM1 : essSup F ρ ≤ 1 := essSup_le_one_of_le_one ρ (fun x => (hpos x).le) h1
  have hJnonneg : ∀ x, 0 ≤ preparationActionOf F x := by
    intro x
    rw [preparationActionOf, neg_nonneg]
    exact Real.log_nonpos (hpos x).le (h1 x)
  have hbdd : IsBoundedUnder (· ≥ ·) (ae ρ) (preparationActionOf F) :=
    Filter.isBoundedUnder_of (r := (· ≥ ·)) ⟨0, hJnonneg⟩
  have hcob : IsCoboundedUnder (· ≥ ·) (ae ρ) (preparationActionOf F) := by
    refine ⟨-Real.log (essSup F ρ), fun a ha => ?_⟩
    have hae : F ≤ᵐ[ρ] fun _ => Real.exp (-a) := by
      filter_upwards [ha] with x hx
      have hxa : a ≤ -Real.log (F x) := hx
      have : Real.log (F x) ≤ -a := by linarith
      calc F x = Real.exp (Real.log (F x)) := (Real.exp_log (hpos x)).symm
        _ ≤ Real.exp (-a) := Real.exp_le_exp.mpr this
    have hle : essSup F ρ ≤ Real.exp (-a) :=
      essSup_le_of_ae_le _ hae (isCoboundedUnder_of_nonneg ρ fun x => (hpos x).le)
    have := Real.log_le_log hM hle
    rw [Real.log_exp] at this
    linarith
  refine le_antisymm ?_ ?_
  · by_contra hcon
    have hlt : -Real.log (essSup F ρ) < essInf (preparationActionOf F) ρ := not_le.mp hcon
    obtain ⟨c, hc1, hc2⟩ := exists_between hlt
    have hae := ae_lt_of_lt_essInf hc2 hbdd
    have haeF : F ≤ᵐ[ρ] fun _ => Real.exp (-c) := by
      filter_upwards [hae] with x hx
      have hxc : c < -Real.log (F x) := hx
      have hlog : Real.log (F x) ≤ -c := by linarith
      calc F x = Real.exp (Real.log (F x)) := (Real.exp_log (hpos x)).symm
        _ ≤ Real.exp (-c) := Real.exp_le_exp.mpr hlog
    have hle : essSup F ρ ≤ Real.exp (-c) :=
      essSup_le_of_ae_le _ haeF (isCoboundedUnder_of_nonneg ρ fun x => (hpos x).le)
    have hlog := Real.log_le_log hM hle
    rw [Real.log_exp] at hlog
    linarith
  · refine le_essInf_of_ae_le _ ?_ hcob
    filter_upwards [ae_le_essSup_of_le_one ρ h1] with x hx
    have : Real.log (F x) ≤ Real.log (essSup F ρ) := Real.log_le_log (hpos x) hx
    show -Real.log (essSup F ρ) ≤ -Real.log (F x)
    linarith

/-- **Essential supremum as an exponential action.** -/
theorem essSup_eq_exp_neg_essInf {F : Ω → ℝ} (h1 : ∀ x, F x ≤ 1) (hpos : ∀ x, 0 < F x) :
    essSup F ρ = Real.exp (-(essInf (preparationActionOf F) ρ)) := by
  rw [essInf_preparationActionOf ρ h1 hpos, neg_neg,
    Real.exp_log (essSup_pos_of_pos ρ h1 hpos)]

/-- **Rare-carrier amortization.**  A positive-mass carrier of bounded preparation action caps the
normalized replica action by its own action plus the amortized source rarity. -/
theorem quenchedReplicaAction_le_of_carrier {F : Ω → ℝ} (hF : Measurable F) (h0 : ∀ x, 0 ≤ F x)
    (h1 : ∀ x, F x ≤ 1) {B : Set Ω} (hB : MeasurableSet B) {j : ℝ}
    (hlow : ∀ H ∈ B, Real.exp (-j) ≤ F H) (hmass : 0 < ρ.real B) {r : ℕ} (hr : 0 < r) :
    quenchedReplicaAction ρ F r ≤ j + (r : ℝ)⁻¹ * Real.log (ρ.real B)⁻¹ := by
  have hr0 : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr0
  have hbase := quenchedActionReplicaMass_ge_of_carrier ρ h0 hB hlow r
    (integrable_pow_of_unit ρ hF h0 h1 r)
  have hlhs : 0 ≤ ρ.real B * Real.exp (-((r : ℝ) * j)) :=
    mul_nonneg hmass.le (Real.exp_pos _).le
  have hstep : (ρ.real B * Real.exp (-((r : ℝ) * j))) ^ ((r : ℝ)⁻¹) ≤
      quenchedActionReplicaMass ρ F r ^ ((r : ℝ)⁻¹) :=
    Real.rpow_le_rpow hlhs hbase (by positivity)
  have hcompute : (ρ.real B * Real.exp (-((r : ℝ) * j))) ^ ((r : ℝ)⁻¹) =
      ρ.real B ^ ((r : ℝ)⁻¹) * Real.exp (-j) := by
    rw [Real.mul_rpow hmass.le (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2
    field_simp
  rw [hcompute] at hstep
  have hposl : (0 : ℝ) < ρ.real B ^ ((r : ℝ)⁻¹) * Real.exp (-j) :=
    mul_pos (Real.rpow_pos_of_pos hmass _) (Real.exp_pos _)
  have hlog := Real.log_le_log hposl hstep
  rw [Real.log_mul (Real.rpow_pos_of_pos hmass _).ne' (Real.exp_pos _).ne',
    Real.log_rpow hmass, Real.log_exp] at hlog
  rw [quenchedReplicaAction, neg_le_iff_add_nonneg']
  rw [Real.log_inv]
  linarith

/-- **Schedule ceiling.**  If a positive-mass carrier has preparation action below the depth
threshold, then only finitely many replica orders can carry a positive certificate exponent, and
the ceiling is the amortized source rarity divided by the threshold gap. -/
theorem lt_of_pos_certificate_exponent {F : Ω → ℝ} (hF : Measurable F) (h0 : ∀ x, 0 ≤ F x)
    (h1 : ∀ x, F x ≤ 1) {B : Set Ω} (hB : MeasurableSet B) {j θ : ℝ}
    (hlow : ∀ H ∈ B, Real.exp (-j) ≤ F H) (hmass : 0 < ρ.real B) (hgap : j < θ)
    {r : ℕ} (hr : 0 < r) (hcert : θ < quenchedReplicaAction ρ F r) :
    (r : ℝ) < Real.log (ρ.real B)⁻¹ / (θ - j) := by
  have hr0 : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hbound := quenchedReplicaAction_le_of_carrier ρ hF h0 h1 hB hlow hmass hr
  have hstep : θ < j + (r : ℝ)⁻¹ * Real.log (ρ.real B)⁻¹ := lt_of_lt_of_le hcert hbound
  rw [lt_div_iff₀ (by linarith : (0 : ℝ) < θ - j)]
  have hkey : (r : ℝ) * (θ - j) < (r : ℝ) * ((r : ℝ)⁻¹ * Real.log (ρ.real B)⁻¹) := by
    apply mul_lt_mul_of_pos_left _ hr0
    linarith
  rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hr0), one_mul] at hkey

end ReplicaLimits

section Certificate

variable {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]

/-- **Exact causal-replica certificate criterion.**  The replica mass falls below an exponential
threshold exactly when every tilted source law pays at least that threshold in source rarity plus
replicated preparation action. -/
theorem quenchedActionReplicaMass_le_exp_iff {F : Ω → ℝ} (hFpos : ∀ H, 0 < F H) (r : ℕ)
    (hZ : 0 < quenchedActionReplicaMass ρ F r)
    (hint : Integrable (fun H => Real.exp (-((r : ℝ) * preparationActionOf F H))) ρ)
    (hmeas : AEMeasurable (fun H => -((r : ℝ) * preparationActionOf F H)) ρ)
    (htilt : Integrable (fun H => -((r : ℝ) * preparationActionOf F H))
      (ρ.tilted fun H => -((r : ℝ) * preparationActionOf F H))) (L : ℝ) :
    quenchedActionReplicaMass ρ F r ≤ Real.exp (-L) ↔
      ∀ q : Measure Ω, ∀ _ : IsProbabilityMeasure q, q ≪ ρ →
        Integrable (llr q ρ) q →
        Integrable (fun H => -((r : ℝ) * preparationActionOf F H)) q →
        Integrable (llr q (ρ.tilted fun H => -((r : ℝ) * preparationActionOf F H))) q →
        L ≤ (∫ H, llr q ρ H ∂q) + (r : ℝ) * ∫ H, preparationActionOf F H ∂q := by
  have hbase := isLeast_quenchedReplicaAction ρ hFpos r hint hmeas htilt
  have hthreshold : quenchedActionReplicaMass ρ F r ≤ Real.exp (-L) ↔
      L ≤ -Real.log (quenchedActionReplicaMass ρ F r) := by
    rw [← Real.log_le_iff_le_exp hZ]
    constructor <;> intro h <;> linarith
  rw [hthreshold]
  constructor
  · intro h q hq hac h1 h2 h3
    exact le_trans h (hbase.2 ⟨q, hq, hac, h1, h2, h3, rfl⟩)
  · intro h
    obtain ⟨q, hq, hac, h1, h2, h3, heq⟩ := hbase.1
    rw [heq]
    exact h q hq hac h1 h2 h3

/-- **Normalized certificate criterion.**  Dividing the certificate criterion by the replica order
exhibits the desired depth-`θ` bound as a source--preparation separation inequality. -/
theorem quenchedActionReplicaMass_le_exp_iff_normalized {F : Ω → ℝ} (hFpos : ∀ H, 0 < F H) {r : ℕ}
    (hr : 0 < r) (hZ : 0 < quenchedActionReplicaMass ρ F r)
    (hint : Integrable (fun H => Real.exp (-((r : ℝ) * preparationActionOf F H))) ρ)
    (hmeas : AEMeasurable (fun H => -((r : ℝ) * preparationActionOf F H)) ρ)
    (htilt : Integrable (fun H => -((r : ℝ) * preparationActionOf F H))
      (ρ.tilted fun H => -((r : ℝ) * preparationActionOf F H))) (θ : ℝ) :
    quenchedActionReplicaMass ρ F r ≤ Real.exp (-((r : ℝ) * θ)) ↔
      ∀ q : Measure Ω, ∀ _ : IsProbabilityMeasure q, q ≪ ρ →
        Integrable (llr q ρ) q →
        Integrable (fun H => -((r : ℝ) * preparationActionOf F H)) q →
        Integrable (llr q (ρ.tilted fun H => -((r : ℝ) * preparationActionOf F H))) q →
        θ ≤ (r : ℝ)⁻¹ * (∫ H, llr q ρ H ∂q) + ∫ H, preparationActionOf F H ∂q := by
  have hr0 : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  rw [quenchedActionReplicaMass_le_exp_iff ρ hFpos r hZ hint hmeas htilt ((r : ℝ) * θ)]
  constructor
  · intro h q hq hac h1 h2 h3
    have := h q hq hac h1 h2 h3
    have hmul := mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hr0.le)
    calc θ = (r : ℝ)⁻¹ * ((r : ℝ) * θ) := by field_simp
      _ ≤ (r : ℝ)⁻¹ * ((∫ H, llr q ρ H ∂q) + (r : ℝ) * ∫ H, preparationActionOf F H ∂q) := hmul
      _ = (r : ℝ)⁻¹ * (∫ H, llr q ρ H ∂q) + ∫ H, preparationActionOf F H ∂q := by field_simp
  · intro h q hq hac h1 h2 h3
    have := h q hq hac h1 h2 h3
    have hmul := mul_le_mul_of_nonneg_left this hr0.le
    calc (r : ℝ) * θ ≤ (r : ℝ) *
        ((r : ℝ)⁻¹ * (∫ H, llr q ρ H ∂q) + ∫ H, preparationActionOf F H ∂q) := hmul
      _ = (∫ H, llr q ρ H ∂q) + (r : ℝ) * ∫ H, preparationActionOf F H ∂q := by field_simp

end Certificate

end

end GaloisForLFunctions.HTGeometry
