import GaloisForLFunctions.HTGeometry.ConstitutiveLocalRenewalActionThreshold

/-!
# Extended-real local renewal threshold

This module preserves infinite KL coordinates in the CRG liminf law.  It removes coordinatewise
finiteness assumptions by working with the canonical `ENNReal`-to-`EReal` embedding.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Real InformationTheory Set ProbabilityTheory Filter Topology
open scoped ENNReal Topology

noncomputable section

/-- Pointwise scaled KL lower bound in `EReal`, retaining infinite KL coordinates exactly. -/
theorem exponentialAperture_scaledAction_lower_ennreal
    {Omega : Type*} [MeasurableSpace Omega]
    (mu nu : Measure Omega) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (A : Set Omega) (hA : MeasurableSet A) (W C beta K c d lambda : ℝ) (n : ℕ)
    (hC : 0 < C) (hK : 0 < K) (hc : 0 < c) (hlambda : 0 < lambda)
    (hmass : mu.real A ≤ C * Real.exp (-beta * ((n + 1 : ℕ) : ℝ)))
    (hwork : W ≤ K * ((n + 1 : ℕ) : ℝ) ^ d)
    (hcurrent : c ≤ nu.real A * W) :
    ((c * lambda / K - C * ((n + 1 : ℕ) : ℝ) ^ (d - 1) *
        Real.exp (-(beta - lambda) * ((n + 1 : ℕ) : ℝ)) : ℝ) : EReal) ≤
      (((ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ (d - 1)) *
        klDiv nu mu : ℝ≥0∞) : EReal)) := by
  by_cases hfin : klDiv nu mu = ⊤
  · rw [hfin, ENNReal.mul_top]
    · rw [EReal.coe_ennreal_top]
      exact le_top
    · exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)).ne'
  · have hlocal := exponentialAperture_localAction_lower
      mu nu A hA C (beta * ((n + 1 : ℕ) : ℝ))
      ((beta - lambda) * ((n + 1 : ℕ) : ℝ))
      (lambda * ((n + 1 : ℕ) : ℝ)) hC.le (by ring)
      (by simpa [mul_assoc] using hmass) hfin
    have harg : -((beta - lambda) * ((n + 1 : ℕ) : ℝ)) =
        (lambda - beta) * ((n + 1 : ℕ) : ℝ) := by ring
    rw [harg] at hlocal
    have hscaled := polynomialCurrent_scaledAction_lower
      (fun _ => nu.real A) (fun _ => W) (fun _ => (klDiv nu mu).toReal)
      K c d lambda C beta n hK hc hlambda measureReal_nonneg hwork hcurrent
      (by simpa [mul_assoc] using hlocal)
    calc
      ((c * lambda / K - C * ((n + 1 : ℕ) : ℝ) ^ (d - 1) *
          Real.exp (-(beta - lambda) * ((n + 1 : ℕ) : ℝ)) : ℝ) : EReal) ≤
          ((((n + 1 : ℕ) : ℝ) ^ (d - 1) * (klDiv nu mu).toReal : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.mpr hscaled
      _ = (((ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ (d - 1)) *
          klDiv nu mu : ℝ≥0∞) : EReal)) := by
        rw [EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal,
          max_eq_left (Real.rpow_nonneg (by positivity) _),
          ← EReal.coe_ennreal_toReal hfin]
        norm_cast

/-- Every strict tilt rate lower-bounds the extended-real liminf, without coordinate finiteness. -/
theorem exponentialAperture_polynomialCurrent_action_liminf_ennreal_of_rate
    {Omega : ℕ → Type*} [∀ n, MeasurableSpace (Omega n)]
    (mu nu : ∀ n, Measure (Omega n))
    (hmu : ∀ n, IsProbabilityMeasure (mu n))
    (hnu : ∀ n, IsProbabilityMeasure (nu n))
    (A : ∀ n, Set (Omega n)) (hA : ∀ n, MeasurableSet (A n))
    (W : ℕ → ℝ) (C beta K c d lambda : ℝ)
    (hC : 0 < C) (hK : 0 < K) (hc : 0 < c)
    (hlambda : 0 < lambda) (hlt : lambda < beta)
    (hmass : ∀ n, (mu n).real (A n) ≤
      C * Real.exp (-beta * ((n + 1 : ℕ) : ℝ)))
    (hwork : ∀ n, W n ≤ K * ((n + 1 : ℕ) : ℝ) ^ d)
    (hcurrent : ∀ n, c ≤ (nu n).real (A n) * W n) :
    ((c * lambda / K : ℝ) : EReal) ≤
      liminf (fun n =>
        (((ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ (d - 1)) *
          klDiv (nu n) (mu n) : ℝ≥0∞) : EReal))) atTop := by
  let L : EReal := liminf (fun n =>
    (((ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ (d - 1)) *
      klDiv (nu n) (mu n) : ℝ≥0∞) : EReal))) atTop
  have hcast : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hdecay : Tendsto
      (fun n : ℕ => C * ((n + 1 : ℕ) : ℝ) ^ (d - 1) *
        Real.exp (-(beta - lambda) * ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 0) := by
    have hraw := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (d - 1) (beta - lambda) (sub_pos.mpr hlt)).comp hcast
    simpa only [Function.comp_apply, mul_assoc, mul_zero] using
      ((tendsto_const_nhds (x := C)).mul hraw)
  by_contra hbound
  have hLlt : L < ((c * lambda / K : ℝ) : EReal) := lt_of_not_ge hbound
  obtain ⟨a, hLa, hacoeff⟩ := EReal.exists_between_coe_real hLlt
  have hacoeffReal : a < c * lambda / K := EReal.coe_lt_coe_iff.mp hacoeff
  have hgap : 0 < c * lambda / K - a := sub_pos.mpr hacoeffReal
  have heventError : ∀ᶠ n : ℕ in atTop,
      C * ((n + 1 : ℕ) : ℝ) ^ (d - 1) *
        Real.exp (-(beta - lambda) * ((n + 1 : ℕ) : ℝ)) <
          c * lambda / K - a := hdecay.eventually_lt_const hgap
  have heventLower : ∀ᶠ n : ℕ in atTop,
      (a : EReal) ≤ (((ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ (d - 1)) *
        klDiv (nu n) (mu n) : ℝ≥0∞) : EReal)) := by
    filter_upwards [heventError] with n hn
    letI : IsProbabilityMeasure (mu n) := hmu n
    letI : IsProbabilityMeasure (nu n) := hnu n
    have hscaled := exponentialAperture_scaledAction_lower_ennreal
      (mu n) (nu n) (A n) (hA n) (W n) C beta K c d lambda n
      hC hK hc hlambda (hmass n) (hwork n) (hcurrent n)
    have hareal : a ≤ c * lambda / K -
        C * ((n + 1 : ℕ) : ℝ) ^ (d - 1) *
          Real.exp (-(beta - lambda) * ((n + 1 : ℕ) : ℝ)) := by linarith
    exact (EReal.coe_le_coe_iff.mpr hareal).trans hscaled
  have haL : (a : EReal) ≤ L :=
    Filter.le_liminf_of_le (by isBoundedDefault) heventLower
  exact (not_lt_of_ge haL hLa)

/-- Exact CRG.5 coefficient in extended-real form, with no finite-KL premise. -/
theorem exponentialAperture_polynomialCurrent_action_liminf_ennreal
    {Omega : ℕ → Type*} [∀ n, MeasurableSpace (Omega n)]
    (mu nu : ∀ n, Measure (Omega n))
    (hmu : ∀ n, IsProbabilityMeasure (mu n))
    (hnu : ∀ n, IsProbabilityMeasure (nu n))
    (A : ∀ n, Set (Omega n)) (hA : ∀ n, MeasurableSet (A n))
    (W : ℕ → ℝ) (C beta K c d : ℝ)
    (hC : 0 < C) (hbeta : 0 < beta) (hK : 0 < K) (hc : 0 < c)
    (hmass : ∀ n, (mu n).real (A n) ≤
      C * Real.exp (-beta * ((n + 1 : ℕ) : ℝ)))
    (hwork : ∀ n, W n ≤ K * ((n + 1 : ℕ) : ℝ) ^ d)
    (hcurrent : ∀ n, c ≤ (nu n).real (A n) * W n) :
    ((c * beta / K : ℝ) : EReal) ≤
      liminf (fun n =>
        (((ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ (d - 1)) *
          klDiv (nu n) (mu n) : ℝ≥0∞) : EReal))) atTop := by
  let L : EReal := liminf (fun n =>
    (((ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ (d - 1)) *
      klDiv (nu n) (mu n) : ℝ≥0∞) : EReal))) atTop
  by_contra hbound
  have hLlt : L < ((c * beta / K : ℝ) : EReal) := lt_of_not_ge hbound
  obtain ⟨a, hLa, hatarget⟩ := EReal.exists_between_coe_real hLlt
  have hatargetReal : a < c * beta / K := EReal.coe_lt_coe_iff.mp hatarget
  have haK : a * K < c * beta := by
    calc
      a * K < (c * beta / K) * K := mul_lt_mul_of_pos_right hatargetReal hK
      _ = c * beta := by field_simp
  have hqbeta : a * K / c < beta :=
    (div_lt_iff₀ hc).2 (by simpa [mul_comm] using haK)
  let q : ℝ := max 0 (a * K / c)
  have hqbeta' : q < beta := max_lt hbeta hqbeta
  let lambda : ℝ := (q + beta) / 2
  have hqlambda : q < lambda := by dsimp [lambda]; linarith
  have hlambdabeta : lambda < beta := by dsimp [lambda]; linarith
  have hlambda0 : 0 < lambda := lt_of_le_of_lt (le_max_left 0 (a * K / c)) hqlambda
  have hratio : a * K / c < lambda :=
    (le_max_right 0 (a * K / c)).trans_lt hqlambda
  have haKlambda : a * K < lambda * c := (div_lt_iff₀ hc).1 hratio
  have halambda : a < c * lambda / K := (lt_div_iff₀ hK).2 (by
    simpa [mul_comm] using haKlambda)
  have hrate := exponentialAperture_polynomialCurrent_action_liminf_ennreal_of_rate
    mu nu hmu hnu A hA W C beta K c d lambda hC hK hc hlambda0 hlambdabeta
      hmass hwork hcurrent
  have hrateL : ((c * lambda / K : ℝ) : EReal) ≤ L := hrate
  have haRate : (a : EReal) < ((c * lambda / K : ℝ) : EReal) :=
    EReal.coe_lt_coe_iff.mpr halambda
  exact (not_lt_of_ge (haRate.le.trans hrateL) hLa)

end

end GaloisForLFunctions.HTGeometry
