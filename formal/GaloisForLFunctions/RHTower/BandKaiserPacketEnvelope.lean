import GaloisForLFunctions.RHTower.BandKaiserPacketRayleigh
import GaloisForLFunctions.HTGeometry.RpowExpAsymptotics

/-!
# Subexponential envelope for conditioned Kaiser packet spans

The translated inner-edge cost on the `c^(3/4)` angular grid has depth `O(c^(7/4))`; its square
root is therefore `O(c^(7/8))`.  This file turns that observation into an explicit finite-envelope
bound and then absorbs the entire Rayleigh prefactor into `exp(epsilon*c)` for every positive
`epsilon`.
-/

open MeasureTheory Set intervalIntegral FourierTransform Filter
open scoped BigOperators Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

theorem kaiserPacketAngularStep_eq_rpow {c : ℝ} (hc : 0 < c) :
    kaiserPacketAngularStep c = c ^ (3 / 4 : ℝ) := by
  rw [kaiserPacketAngularStep]
  calc
    Real.sqrt (c * Real.sqrt c) = Real.sqrt (c * c ^ (1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow c]
    _ = Real.sqrt (c ^ (1 + 1 / 2 : ℝ)) := by
      rw [Real.rpow_add hc, Real.rpow_one]
    _ = (c ^ (1 + 1 / 2 : ℝ)) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
    _ = c ^ ((1 + 1 / 2 : ℝ) * (1 / 2 : ℝ)) := by
      rw [Real.rpow_mul hc.le]
    _ = c ^ (3 / 4 : ℝ) := by norm_num

theorem sqrt_two_mul_card_mul_c_mul_kaiserPacketAngularStep {m : ℕ} {c : ℝ}
    (hc : 0 < c) :
    Real.sqrt (2 * (m : ℝ) * c * kaiserPacketAngularStep c) =
      Real.sqrt (2 * (m : ℝ)) * c ^ (7 / 8 : ℝ) := by
  rw [kaiserPacketAngularStep_eq_rpow hc]
  have hm0 : 0 ≤ 2 * (m : ℝ) := by positivity
  calc
    Real.sqrt (2 * (m : ℝ) * c * c ^ (3 / 4 : ℝ)) =
        Real.sqrt ((2 * (m : ℝ)) * (c * c ^ (3 / 4 : ℝ))) := by ring
    _ = ((2 * (m : ℝ)) * (c * c ^ (3 / 4 : ℝ))) ^ (1 / 2 : ℝ) :=
      Real.sqrt_eq_rpow _
    _ = (2 * (m : ℝ)) ^ (1 / 2 : ℝ) *
        (c * c ^ (3 / 4 : ℝ)) ^ (1 / 2 : ℝ) := by
      rw [Real.mul_rpow hm0 (mul_nonneg hc.le (Real.rpow_nonneg hc.le _))]
    _ = Real.sqrt (2 * (m : ℝ)) *
        (c ^ (1 + 3 / 4 : ℝ)) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_add hc, Real.rpow_one]
    _ = Real.sqrt (2 * (m : ℝ)) * c ^ ((1 + 3 / 4 : ℝ) * (1 / 2 : ℝ)) := by
      rw [Real.rpow_mul hc.le]
    _ = Real.sqrt (2 * (m : ℝ)) * c ^ (7 / 8 : ℝ) := by norm_num

theorem kaiserBandRadius_add_abs_packetFrequency_le_c {m : ℕ} {c : ℝ}
    (hc : 1 ≤ c) (hscale : 8 * (m : ℝ) ^ 2 ≤ Real.sqrt c) (j : Fin m) :
    kaiserBandRadius c + |kaiserPacketFrequency c j| ≤ c := by
  have hcpos : 0 < c := one_pos.trans_le hc
  have hq0 : 0 ≤ kaiserPacketAngularFrequency c j :=
    (kaiserPacketAngularFrequency_pos hcpos j).le
  have hq := kaiserPacketAngularFrequency_le_c hc hscale j
  have hden : 0 < 2 * Real.pi := by positivity
  rw [kaiserBandRadius, kaiserPacketFrequency, abs_div, abs_of_pos hden,
    abs_of_nonneg hq0, ← add_div]
  rw [div_le_iff₀ hden]
  nlinarith [Real.pi_gt_three]

/-- Explicit stretched-exponential upper bound for the complete finite edge envelope. -/
theorem kaiserGridTailEnvelope_le_stretched {m : ℕ} {c : ℝ}
    (hc : 1 ≤ c) (hscale : 8 * (m : ℝ) ^ 2 ≤ Real.sqrt c) :
    kaiserGridTailEnvelope (m := m) c ≤
      (m : ℝ) * (8 + 8 * c * Real.exp
        (2 + 2 * Real.sqrt (2 * (m : ℝ) * c * kaiserPacketAngularStep c))) := by
  have hcpos : 0 < c := one_pos.trans_le hc
  have hc0 : 0 ≤ c := hcpos.le
  have hterm : ∀ j : Fin m,
      8 + 2 * (kaiserBandRadius c + |kaiserPacketFrequency c j|) *
          kaiserEdgeTransformBoundAt
            (2 * c * |2 * Real.pi * kaiserPacketFrequency c j|) ^ 2 ≤
        8 + 8 * c * Real.exp
          (2 + 2 * Real.sqrt (2 * (m : ℝ) * c * kaiserPacketAngularStep c)) := by
    intro j
    let D : ℝ := 2 * c * |2 * Real.pi * kaiserPacketFrequency c j|
    let Dmax : ℝ := 2 * (m : ℝ) * c * kaiserPacketAngularStep c
    have hqcard := kaiserPacketAngularFrequency_le_card_mul hc0 j
    have hD0 : 0 ≤ D := by positivity
    have hDle : D ≤ Dmax := by
      change 2 * c * |2 * Real.pi * kaiserPacketFrequency c j| ≤
        2 * (m : ℝ) * c * kaiserPacketAngularStep c
      rw [abs_two_pi_mul_kaiserPacketFrequency hcpos j]
      nlinarith [mul_le_mul_of_nonneg_left hqcard hc0]
    have hsqrt := Real.sqrt_le_sqrt hDle
    have hB0 : 0 ≤ kaiserEdgeTransformBoundAt D :=
      kaiserEdgeTransformBoundAt_nonneg hD0
    have hB := kaiserEdgeTransformBoundAt_le_exp hD0
    have hBsq : kaiserEdgeTransformBoundAt D ^ 2 ≤
        4 * Real.exp (2 + 2 * Real.sqrt Dmax) := by
      calc
        kaiserEdgeTransformBoundAt D ^ 2 ≤
            (2 * Real.exp (1 + Real.sqrt D)) ^ 2 :=
          pow_le_pow_left₀ hB0 hB 2
        _ = 4 * Real.exp (2 + 2 * Real.sqrt D) := by
          calc
            (2 * Real.exp (1 + Real.sqrt D)) ^ 2 =
                4 * (Real.exp (1 + Real.sqrt D) *
                  Real.exp (1 + Real.sqrt D)) := by ring
            _ = 4 * Real.exp ((1 + Real.sqrt D) + (1 + Real.sqrt D)) := by
              congr 1
              exact (Real.exp_add (1 + Real.sqrt D) (1 + Real.sqrt D)).symm
            _ = 4 * Real.exp (2 + 2 * Real.sqrt D) := by ring
        _ ≤ 4 * Real.exp (2 + 2 * Real.sqrt Dmax) := by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
          norm_num
    have hradius := kaiserBandRadius_add_abs_packetFrequency_le_c hc hscale j
    have hradius0 : 0 ≤ kaiserBandRadius c + |kaiserPacketFrequency c j| := by
      rw [kaiserBandRadius]
      positivity
    change 8 + 2 * (kaiserBandRadius c + |kaiserPacketFrequency c j|) *
        kaiserEdgeTransformBoundAt D ^ 2 ≤
      8 + 8 * c * Real.exp (2 + 2 * Real.sqrt Dmax)
    have hproduct := mul_le_mul hradius hBsq (sq_nonneg _) hc0
    nlinarith
  calc
    kaiserGridTailEnvelope (m := m) c ≤ ∑ _j : Fin m,
        (8 + 8 * c * Real.exp
          (2 + 2 * Real.sqrt (2 * (m : ℝ) * c * kaiserPacketAngularStep c))) :=
      Finset.sum_le_sum fun j _ => hterm j
    _ = (m : ℝ) * (8 + 8 * c * Real.exp
        (2 + 2 * Real.sqrt (2 * (m : ℝ) * c * kaiserPacketAngularStep c))) := by
      simp [Fintype.card_fin]
      ring

/-- Every fixed packet-depth Rayleigh prefactor is subexponential in the aperture. -/
theorem eventually_kaiserGridRayleighPrefactor_le_exp {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c : ℝ in atTop,
      128 * (m : ℝ) * c ^ 2 * kaiserGridTailEnvelope (m := m) c ≤
        Real.exp (ε * c) := by
  let A : ℝ := 2 + 2 * Real.sqrt (2 * (m : ℝ))
  have hApos : 0 < A := by positivity
  have hrootGrow := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 8 by norm_num)).eventually_ge_atTop
    (2 * A / ε)
  have hscaleGrow := Real.tendsto_sqrt_atTop.eventually_ge_atTop (8 * (m : ℝ) ^ 2)
  have hpoly := GaloisForLFunctions.HTGeometry.eventually_mul_rpow_le_exp_rpow
    (2048 * (m : ℝ) ^ 2) (c := ε / 2) (δ := 1) (p := 3)
    (by positivity) (by norm_num)
  filter_upwards [hrootGrow, hscaleGrow, hpoly, eventually_ge_atTop (1 : ℝ)] with
    c hroot hscale hpoly hc
  have hcpos : 0 < c := one_pos.trans_le hc
  have henvelope := kaiserGridTailEnvelope_le_stretched hc hscale
  rw [sqrt_two_mul_card_mul_c_mul_kaiserPacketAngularStep hcpos] at henvelope
  have hseven : 1 ≤ c ^ (7 / 8 : ℝ) := by
    simpa using Real.rpow_le_rpow (show (0 : ℝ) ≤ 1 by norm_num) hc
      (show (0 : ℝ) ≤ 7 / 8 by norm_num)
  have hphase : 2 + 2 * Real.sqrt (2 * (m : ℝ)) * c ^ (7 / 8 : ℝ) ≤
      ε * c / 2 := by
    have hfactor : A * c ^ (7 / 8 : ℝ) ≤ ε * c / 2 := by
      have hmul := mul_le_mul_of_nonneg_right hroot
        (show 0 ≤ ε / 2 * c ^ (7 / 8 : ℝ) by positivity)
      calc
        A * c ^ (7 / 8 : ℝ) =
            (2 * A / ε) * (ε / 2 * c ^ (7 / 8 : ℝ)) := by field_simp
        _ ≤ c ^ (1 / 8 : ℝ) * (ε / 2 * c ^ (7 / 8 : ℝ)) := hmul
        _ = ε * c / 2 := by
          calc
            c ^ (1 / 8 : ℝ) * (ε / 2 * c ^ (7 / 8 : ℝ)) =
                ε / 2 * (c ^ (1 / 8 : ℝ) * c ^ (7 / 8 : ℝ)) := by ring
            _ = ε / 2 * c ^ ((1 / 8 : ℝ) + 7 / 8) := by
              rw [Real.rpow_add hcpos]
            _ = ε * c / 2 := by norm_num; ring
    calc
      2 + 2 * Real.sqrt (2 * (m : ℝ)) * c ^ (7 / 8 : ℝ) ≤
          A * c ^ (7 / 8 : ℝ) := by
        simp only [A]
        nlinarith
      _ ≤ ε * c / 2 := hfactor
  have hexpPhase := Real.exp_le_exp.mpr hphase
  have hpoly' : 2048 * (m : ℝ) ^ 2 * c ^ 3 ≤ Real.exp (ε * c / 2) := by
    rw [show c ^ (3 : ℕ) = c ^ (3 : ℝ) by norm_num [Real.rpow_natCast]]
    convert hpoly using 1
    rw [Real.rpow_one]
    ring
  have henvelope' : kaiserGridTailEnvelope (m := m) c ≤
      (m : ℝ) * (8 + 8 * c * Real.exp
        (2 + 2 * Real.sqrt (2 * (m : ℝ)) * c ^ (7 / 8 : ℝ))) := by
    simpa only [mul_assoc] using henvelope
  have henvCrude : 128 * (m : ℝ) * c ^ 2 *
      kaiserGridTailEnvelope (m := m) c ≤
      2048 * (m : ℝ) ^ 2 * c ^ 3 *
        Real.exp (2 + 2 * Real.sqrt (2 * (m : ℝ)) * c ^ (7 / 8 : ℝ)) := by
    have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have hexpone : 1 ≤ Real.exp
        (2 + 2 * Real.sqrt (2 * (m : ℝ)) * c ^ (7 / 8 : ℝ)) := by
      apply Real.one_le_exp
      positivity
    have hsum : 8 + 8 * c * Real.exp
        (2 + 2 * Real.sqrt (2 * (m : ℝ)) * c ^ (7 / 8 : ℝ)) ≤
        16 * c * Real.exp
          (2 + 2 * Real.sqrt (2 * (m : ℝ)) * c ^ (7 / 8 : ℝ)) := by
      nlinarith
    calc
      128 * (m : ℝ) * c ^ 2 * kaiserGridTailEnvelope (m := m) c ≤
          128 * (m : ℝ) * c ^ 2 *
            ((m : ℝ) * (8 + 8 * c * Real.exp
              (2 + 2 * Real.sqrt (2 * (m : ℝ)) * c ^ (7 / 8 : ℝ)))) :=
        mul_le_mul_of_nonneg_left henvelope' (by positivity)
      _ ≤ 128 * (m : ℝ) * c ^ 2 *
          ((m : ℝ) * (16 * c * Real.exp
            (2 + 2 * Real.sqrt (2 * (m : ℝ)) * c ^ (7 / 8 : ℝ)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsum hm0) (by positivity)
      _ = 2048 * (m : ℝ) ^ 2 * c ^ 3 *
          Real.exp (2 + 2 * Real.sqrt (2 * (m : ℝ)) * c ^ (7 / 8 : ℝ)) := by ring
  calc
    128 * (m : ℝ) * c ^ 2 * kaiserGridTailEnvelope (m := m) c ≤
        2048 * (m : ℝ) ^ 2 * c ^ 3 *
          Real.exp (2 + 2 * Real.sqrt (2 * (m : ℝ)) * c ^ (7 / 8 : ℝ)) := henvCrude
    _ ≤ Real.exp (ε * c / 2) * Real.exp (ε * c / 2) :=
      mul_le_mul hpoly' hexpPhase (Real.exp_pos _).le (by positivity)
    _ = Real.exp (ε * c) := by rw [← Real.exp_add]; ring_nf

/-- Uniform fixed-depth leakage exponent: every vector in the packet span has spectral leakage at
most `exp(-(2-epsilon)c)` times its physical energy, eventually in the aperture. -/
theorem eventually_exp_mul_kaiserGridSpectralTail_le_energy {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c : ℝ in atTop, ∀ b : Fin m → ℝ,
      Real.exp ((2 - ε) * c) *
          (∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
            ‖𝓕 (bandTrunc (kaiserGridCombination c b)) ξ‖ ^ 2) ≤
        ∫ x in (-1 : ℝ)..1, kaiserGridCombination c b x ^ 2 := by
  have hprefactor := eventually_kaiserGridRayleighPrefactor_le_exp hm hε
  have hscale := Real.tendsto_sqrt_atTop.eventually_ge_atTop (8 * (m : ℝ) ^ 2)
  have hsqrtDiv : Tendsto (fun c : ℝ => Real.sqrt c / 2) atTop atTop :=
    Real.tendsto_sqrt_atTop.atTop_div_const (by norm_num)
  have hnegSqrt : Tendsto (fun c : ℝ => -(Real.sqrt c / 2)) atTop atBot := by
    simpa only [Function.comp_def] using
      Filter.tendsto_neg_atTop_atBot.comp hsqrtDiv
  have hexpSqrt : Tendsto (fun c : ℝ => Real.exp (-(Real.sqrt c / 2)))
      atTop (nhds 0) := Real.tendsto_exp_atBot.comp hnegSqrt
  have hsmallTendsto : Tendsto
      (fun c : ℝ => 32 * (m : ℝ) * Real.exp (-(Real.sqrt c / 2))) atTop (nhds 0) := by
    convert (tendsto_const_nhds.mul hexpSqrt : Tendsto
      (fun c : ℝ => (32 * (m : ℝ)) * Real.exp (-(Real.sqrt c / 2))) atTop
        (nhds ((32 * (m : ℝ)) * 0))) using 1 <;> norm_num
  have hsmall : ∀ᶠ c : ℝ in atTop,
      32 * (m : ℝ) * Real.exp (-(Real.sqrt c / 2)) ≤ 1 :=
    ((tendsto_order.1 hsmallTendsto).2 1 (by norm_num)).mono fun _ h => h.le
  filter_upwards [hprefactor, hscale, hsmall, eventually_ge_atTop (1 : ℝ)] with
    c hprefactor hscale hsmall hc
  intro b
  let Q : ℝ := ∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
    ‖𝓕 (bandTrunc (kaiserGridCombination c b)) ξ‖ ^ 2
  let E : ℝ := ∫ x in (-1 : ℝ)..1, kaiserGridCombination c b x ^ 2
  let P : ℝ := 128 * (m : ℝ) * c ^ 2 * kaiserGridTailEnvelope (m := m) c
  have hrayleigh : Real.exp c ^ 2 * Q ≤ P * E := by
    simpa only [P, Q, E, mul_assoc] using
      exp_sq_mul_kaiserGridSpectralTail_le hm hc hscale hsmall b
  have hE0 : 0 ≤ E :=
    intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _
  change Real.exp ((2 - ε) * c) * Q ≤ E
  apply le_of_mul_le_mul_left _ (Real.exp_pos (ε * c))
  have hexpClock : Real.exp (ε * c) * Real.exp ((2 - ε) * c) =
      Real.exp c ^ 2 := by
    calc
      Real.exp (ε * c) * Real.exp ((2 - ε) * c) =
          Real.exp (ε * c + (2 - ε) * c) :=
        (Real.exp_add (ε * c) ((2 - ε) * c)).symm
      _ = Real.exp (c + c) := by congr 1; ring
      _ = Real.exp c * Real.exp c := Real.exp_add c c
      _ = Real.exp c ^ 2 := by rw [pow_two]
  calc
    Real.exp (ε * c) * (Real.exp ((2 - ε) * c) * Q) =
        Real.exp c ^ 2 * Q := by
      rw [← mul_assoc, hexpClock]
    _ ≤ P * E := hrayleigh
    _ ≤ Real.exp (ε * c) * E :=
      mul_le_mul_of_nonneg_right hprefactor hE0

end GaloisForLFunctions.RHTower

end
