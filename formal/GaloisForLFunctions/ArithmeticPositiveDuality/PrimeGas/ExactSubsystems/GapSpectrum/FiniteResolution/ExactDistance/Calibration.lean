import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.FiniteResolution.ExactDistance.Measurement

/-! # Strict calibration of the Laplace approximation by collision probability -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open Set Filter MeasureTheory Topology GibbsTail

/-- Integrating a strictly convex Gibbs weight gives strictly less than the symmetrized discrete mass. -/
theorem rowIntegralFactor_lt_half (h : Ioi (0:ℝ)) : rowIntegralFactor h < 1/2 := by
  have H (n : ℕ+) : weighted h n (primitive h (n.val:ℝ)) <
      tailRow h 0 n+weighted h n (density h (n.val:ℝ)/2) := by
    have hl := (integer_tail_bounds h n).1
    have hw := weighted_strictMono h n (show primitive h (n.val:ℝ) < tail h n.val+density h (n.val:ℝ)/2 by linarith only [hl])
    simpa only [tailRow,Real.exp_zero,one_mul,Nat.floor_natCast,weighted_add] using hw
  have hI := weighted_integral_hasSum h
  have hD := weighted_diagonal_hasSum h
  have hR := tailRow_summable h 0
  have hs := Summable.tsum_lt_tsum (fun n => (H n).le) (H 1) hI.summable (hR.add hD.summable)
  rw [hI.tsum_eq,hR.tsum_add hD.summable,hD.tsum_eq,← gap_tail_eq_tsum,mul_zero,gapCDF_zero] at hs
  linarith only [hs]

/-- The half-cell correction controls every upper-tail event at nonnegative cutoff. -/
theorem gap_tail_half_collision (h : Ioi (0:ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    1-gapCDF h t ≤ rowIntegralFactor h*Real.exp (-t)+collisionMass h/2 := by
  let u := t/h.val
  have hh : 0 < h.val := h.property
  have hE : 1 ≤ Real.exp u := Real.one_le_exp (div_nonneg ht hh.le)
  have hs : h.val*u = t := by dsimp [u]; field_simp [hh.ne']
  have hneg : -h.val*u = -t := by rw [neg_mul,hs]
  have H (n : ℕ+) : tailRow h u n ≤ weighted h n (primitive h (n.val:ℝ))*Real.exp (-t)+
      weighted h n (density h (n.val:ℝ)/2) := by
    have hb := real_tail_bound h n (le_mul_of_one_le_left (Nat.cast_nonneg n.val) hE)
    have he := (weighted_strictMono h n).monotone hb
    rwa [weighted_add,primitive_dilation,weighted_mul,hneg] at he
  have hI := (weighted_integral_hasSum h).mul_right (Real.exp (-t))
  have hD := weighted_diagonal_hasSum h
  have he := (tailRow_summable h u).tsum_le_tsum H (hI.summable.add hD.summable)
  rw [← gap_tail_eq_tsum,hs,hI.summable.tsum_add hD.summable,hI.tsum_eq,hD.tsum_eq] at he
  exact he

/-- Positive cutoffs retain explicit strict margins from both collision extremals. -/
theorem gap_positive_margins (h : Ioi (0:ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    let δ := 1/2-rowIntegralFactor h
    (-(collisionMass h/2)+δ*Real.exp (-t) ≤ gapCDF h t-laplaceCDF t) ∧
    gapCDF h t-laplaceCDF t ≤ collisionMass h/2-δ*(1-Real.exp (-t)) := by
  have hl := gap_tail_half_collision h ht
  have hu := (positive_band_sandwich h ht).1
  rw [real_band_eq_cdf_sub _ ht] at hu
  change gapCDF h t-gapCDF h 0 ≤ _ at hu
  rw [gapCDF_zero] at hu
  dsimp only
  rw [laplaceCDF_positive ht]
  exact ⟨by linarith only [hl],by linarith only [hu]⟩

#print axioms rowIntegralFactor_lt_half
#print axioms gap_tail_half_collision
#print axioms gap_positive_margins

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
