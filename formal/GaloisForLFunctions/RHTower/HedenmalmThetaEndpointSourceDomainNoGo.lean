import GaloisForLFunctions.RHTower.HedenmalmContinuousApertureEndpointDoublet
import GaloisForLFunctions.RHTower.HedenmalmThetaKernelEnergy

/-!
# Canonical source-domain obstruction for aperture endpoints
-/

open Filter Topology MeasureTheory Set

namespace RHTower

noncomputable section

namespace HedenmalmThetaSource

open HedenmalmContinuousAperture

/-- Weighted-source energy density of one endpoint translated by half-aperture `a`. -/
def thetaEndpointShiftEnergyDensity (a x : ℝ) : ℝ :=
  thetaSource.k (x - a) ^ (2 : ℕ) / thetaSource.k x

/-- Exact double-exponential ratio of the model theta envelopes. -/
theorem thetaEnvelope_shift_sq_div (a x : ℝ) :
    thetaEnvelope (x - a) ^ (2 : ℕ) / thetaEnvelope x =
      Real.exp (9 * x / 2 - 9 * a +
        Real.pi * (1 - 2 * Real.exp (-2 * a)) * Real.exp (2 * x)) := by
  rw [thetaEnvelope, thetaEnvelope, mul_pow, ← Real.exp_nat_mul,
    ← Real.exp_nat_mul]
  have hshift : Real.exp (2 * (x - a)) =
      Real.exp (2 * x) * Real.exp (-2 * a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hshift]
  rw [div_eq_iff (mul_ne_zero (Real.exp_ne_zero _) (Real.exp_ne_zero _))]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [Real.exp_add]
  ring

lemma one_sub_two_mul_exp_neg_two_mul_nonneg {a : ℝ}
    (ha : Real.log 2 / 2 ≤ a) :
    0 ≤ 1 - 2 * Real.exp (-2 * a) := by
  have hlog : Real.log 2 ≤ 2 * a := by linarith
  have hneg : -2 * a ≤ -Real.log 2 := by linarith
  have he : Real.exp (-2 * a) ≤ Real.exp (-Real.log 2) :=
    Real.exp_le_exp.mpr hneg
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
  norm_num at he ⊢
  linarith

/-- At and beyond half of `log 2`, the squared shifted envelope overwhelms the original envelope. -/
theorem tendsto_thetaEnvelope_shift_sq_div_atTop {a : ℝ}
    (ha : Real.log 2 / 2 ≤ a) :
    Tendsto (fun x : ℝ => thetaEnvelope (x - a) ^ (2 : ℕ) / thetaEnvelope x) atTop atTop := by
  have hc := one_sub_two_mul_exp_neg_two_mul_nonneg ha
  have hlinear : Tendsto (fun x : ℝ => 9 * x / 2 - 9 * a) atTop atTop := by
    refine Filter.tendsto_atTop.mpr ?_
    intro M
    filter_upwards [eventually_ge_atTop (2 * (M + 9 * a) / 9)] with x hx
    linarith
  have hexponent : Tendsto
      (fun x : ℝ => 9 * x / 2 - 9 * a +
        Real.pi * (1 - 2 * Real.exp (-2 * a)) * Real.exp (2 * x))
      atTop atTop := by
    refine Filter.tendsto_atTop.mpr ?_
    intro M
    filter_upwards [Filter.tendsto_atTop.mp hlinear M] with x hx
    have hterm : 0 ≤ Real.pi * (1 - 2 * Real.exp (-2 * a)) * Real.exp (2 * x) := by
      positivity
    linarith
  apply (Real.tendsto_exp_atTop.comp hexponent).congr'
  filter_upwards with x
  exact (thetaEnvelope_shift_sq_div a x).symm

/-- The actual weighted endpoint density diverges pointwise along the positive source horizon. -/
theorem tendsto_thetaEndpointShiftEnergyDensity_atTop {a : ℝ}
    (ha : Real.log 2 / 2 ≤ a) :
    Tendsto (thetaEndpointShiftEnergyDensity a) atTop atTop := by
  let C : ℝ := thetaEnvelopeLower ^ (2 : ℕ) / thetaEnvelopeUpper
  have hC : 0 < C := div_pos (sq_pos_of_pos thetaEnvelopeLower_pos) thetaEnvelopeUpper_pos
  have hlowerT : Tendsto
      (fun x : ℝ => C * (thetaEnvelope (x - a) ^ (2 : ℕ) / thetaEnvelope x)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hC (tendsto_thetaEnvelope_shift_sq_div_atTop ha)
  refine Filter.tendsto_atTop.mpr ?_
  intro M
  filter_upwards [Filter.tendsto_atTop.mp hlowerT M,
    eventually_ge_atTop (a + 1), eventually_ge_atTop (0 : ℝ)] with x hM hx h0
  apply hM.trans
  have hxa : 0 < x - a := by linarith
  have hnumLower := thetaCuspFullSource_ge_envelope hxa
  have hdenUpper := thetaCuspFullSource_le_envelope h0
  have hk : 0 < thetaSource.k x := thetaSource.pos_k x
  have henv : 0 < thetaEnvelope x := thetaEnvelope_pos x
  have hUenv : 0 < thetaEnvelopeUpper * thetaEnvelope x :=
    mul_pos thetaEnvelopeUpper_pos henv
  have hshiftNonneg : 0 ≤ thetaEnvelopeLower * thetaEnvelope (x - a) :=
    mul_nonneg thetaEnvelopeLower_pos.le (thetaEnvelope_pos _).le
  have hkshiftNonneg : 0 ≤ thetaSource.k (x - a) := (thetaSource.pos_k _).le
  apply (le_div_iff₀ hk).2
  calc
    C * (thetaEnvelope (x - a) ^ (2 : ℕ) / thetaEnvelope x) * thetaSource.k x
        ≤ C * (thetaEnvelope (x - a) ^ (2 : ℕ) / thetaEnvelope x) *
            (thetaEnvelopeUpper * thetaEnvelope x) := by
          gcongr
          simpa only [thetaSource_k] using hdenUpper
    _ = (thetaEnvelopeLower * thetaEnvelope (x - a)) ^ (2 : ℕ) := by
          dsimp [C]
          field_simp [thetaEnvelopeUpper_pos.ne']
    _ ≤ thetaSource.k (x - a) ^ (2 : ℕ) := by
          have hle : thetaEnvelopeLower * thetaEnvelope (x - a) ≤
              thetaSource.k (x - a) := by
            simpa only [thetaSource_k] using hnumLower
          nlinarith

/-- One translated theta endpoint is outside the canonical source Hilbert domain as soon as its
half-aperture reaches `log 2 / 2`. -/
theorem not_integrable_thetaEndpointShiftEnergyDensity {a : ℝ}
    (ha : Real.log 2 / 2 ≤ a) :
    ¬ Integrable (thetaEndpointShiftEnergyDensity a) (volume : Measure ℝ) := by
  intro hint
  have hlarge := Filter.tendsto_atTop.mp
    (tendsto_thetaEndpointShiftEnergyDensity_atTop ha) 1
  obtain ⟨R, hR⟩ := eventually_atTop.1 hlarge
  have htail := hint.integrableOn (s := Ioi R)
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi R) := by
    refine MeasureTheory.Integrable.mono htail continuous_const.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1),
      Real.norm_eq_abs, abs_of_nonneg ?_]
    · exact hR x hx.le
    · rw [thetaEndpointShiftEnergyDensity]
      exact div_nonneg (sq_nonneg _) (thetaSource.pos_k x).le
  simp [integrableOn_const_iff, Real.volume_Ioi] at hconst

/-- Every prime aperture lies beyond the canonical source-domain endpoint threshold. -/
theorem not_integrable_primeThetaEndpointShiftEnergyDensity (p : Nat.Primes) :
    ¬ Integrable
      (thetaEndpointShiftEnergyDensity (Real.log (p.1 : ℕ) / 2))
      (volume : Measure ℝ) := by
  apply not_integrable_thetaEndpointShiftEnergyDensity
  have hp2 : 2 ≤ p.1 := p.2.two_le
  have hlog : Real.log 2 ≤ Real.log (p.1 : ℕ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hp2)
  linarith

/-- Canonical source-Hilbert energy density of the actual even aperture endpoint. -/
def thetaApertureEvenEnergyDensity (L x : ℝ) : ℝ :=
  centeredApertureEvenEndpoint thetaSource L x ^ (2 : ℕ) / thetaSource.k x

theorem continuous_thetaEndpointShiftEnergyDensity (a : ℝ) :
    Continuous (thetaEndpointShiftEnergyDensity a) := by
  unfold thetaEndpointShiftEnergyDensity
  refine ((thetaSource.continuous_k.comp
    (continuous_id.sub continuous_const)).pow 2).div thetaSource.continuous_k ?_
  intro x
  exact (thetaSource.pos_k x).ne'

theorem continuous_thetaApertureEvenEnergyDensity (L : ℝ) :
    Continuous (thetaApertureEvenEnergyDensity L) := by
  unfold thetaApertureEvenEnergyDensity centeredApertureEvenEndpoint
  refine ((continuous_const.mul
    ((thetaSource.continuous_k.comp (continuous_id.add continuous_const)).add
      (thetaSource.continuous_k.comp (continuous_id.sub continuous_const)))).pow 2).div
      thetaSource.continuous_k ?_
  intro x
  exact (thetaSource.pos_k x).ne'

/-- **Raw endpoint landing is impossible in canonical `H_k`.** Once aperture reaches `log 2`,
the actual even endpoint has infinite canonical weighted source energy. -/
theorem not_integrable_thetaApertureEvenEnergyDensity {L : ℝ}
    (hL : Real.log 2 ≤ L) :
    ¬ Integrable (thetaApertureEvenEnergyDensity L) (volume : Measure ℝ) := by
  intro heven
  let a : ℝ := L / 2
  let c : ℝ := Real.exp (-L / 2)
  have ha : Real.log 2 / 2 ≤ a := by dsimp [a]; linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hscaled : Integrable
      (fun x : ℝ => c ^ (2 : ℕ) * thetaEndpointShiftEnergyDensity a x)
      (volume : Measure ℝ) := by
    refine MeasureTheory.Integrable.mono heven
      ((continuous_thetaEndpointShiftEnergyDensity a).const_mul (c ^ (2 : ℕ))).aestronglyMeasurable ?_
    filter_upwards with x
    have hkx : 0 < thetaSource.k x := thetaSource.pos_k x
    have hkm : 0 < thetaSource.k (x - a) := thetaSource.pos_k _
    have hkp : 0 < thetaSource.k (x + a) := thetaSource.pos_k _
    have hevenNonneg : 0 ≤ centeredApertureEvenEndpoint thetaSource L x := by
      rw [centeredApertureEvenEndpoint]
      positivity
    have hcomponent : c * thetaSource.k (x - a) ≤
        centeredApertureEvenEndpoint thetaSource L x := by
      rw [centeredApertureEvenEndpoint]
      dsimp [a, c]
      rw [mul_add]
      exact le_add_of_nonneg_left (mul_nonneg (Real.exp_pos _).le hkp.le)
    have hsquare : (c * thetaSource.k (x - a)) ^ (2 : ℕ) ≤
        centeredApertureEvenEndpoint thetaSource L x ^ (2 : ℕ) := by
      exact (sq_le_sq₀ (mul_nonneg hc.le hkm.le) hevenNonneg).2 hcomponent
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (by
        rw [thetaEndpointShiftEnergyDensity]
        exact div_nonneg (sq_nonneg _) hkx.le)),
      Real.norm_eq_abs, abs_of_nonneg (by
        rw [thetaApertureEvenEnergyDensity]
        exact div_nonneg (sq_nonneg _) hkx.le)]
    rw [thetaEndpointShiftEnergyDensity, thetaApertureEvenEnergyDensity]
    calc
      c ^ (2 : ℕ) * (thetaSource.k (x - a) ^ (2 : ℕ) / thetaSource.k x) =
          (c * thetaSource.k (x - a)) ^ (2 : ℕ) / thetaSource.k x := by ring
      _ ≤ centeredApertureEvenEndpoint thetaSource L x ^ (2 : ℕ) / thetaSource.k x :=
        (div_le_div_iff_of_pos_right hkx).2 hsquare
  have hc2 : c ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hc.ne'
  have hunscaled := hscaled.const_mul (c ^ (2 : ℕ))⁻¹
  apply not_integrable_thetaEndpointShiftEnergyDensity ha
  refine hunscaled.congr ?_
  filter_upwards with x
  field_simp [hc2]

/-- Every literal prime even endpoint is excluded from canonical `H_k`. -/
theorem not_integrable_primeThetaApertureEvenEnergyDensity (p : Nat.Primes) :
    ¬ Integrable
      (thetaApertureEvenEnergyDensity (Real.log (p.1 : ℕ)))
      (volume : Measure ℝ) := by
  apply not_integrable_thetaApertureEvenEnergyDensity
  exact Real.log_le_log (by norm_num) (by exact_mod_cast p.2.two_le)

end HedenmalmThetaSource

end

end RHTower
