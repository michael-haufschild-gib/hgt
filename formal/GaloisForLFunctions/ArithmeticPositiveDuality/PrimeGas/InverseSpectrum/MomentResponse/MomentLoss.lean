import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockGrowth.HeightIndex

/-! # Relative heat moments and their monotone roots -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Finset Set

/-- Loss in the q-th moment of the squared heat levels. Interlacing makes the relative sum finite at every positive q. -/
def momentLoss (q : GibbsExponent) {r : ℕ} (b : SpectralBand r) : ℝ := relativeReading (powerResponse q) b

theorem momentLoss_nonneg (q : GibbsExponent) {r : ℕ} (b : SpectralBand r) : 0 ≤ momentLoss q b :=
  (relativeReading_bounds _ b).1

/-- In the trace half-plane the relative series is the difference of convergent spectral traces. -/
theorem momentLoss_eq_trace_difference (q : GibbsExponent) (hq : 1 < q.val) {r : ℕ} (b : SpectralBand r) :
    momentLoss q b = (riemannZeta (q.val:ℂ)).re - ∑' n, (b n).val^q.val := by
  have he := survivingPartition_eq_tsum b (z := (q.val:ℂ)) hq
  rw [survivingPartition,relativePartition_real b q] at he
  simp_rw [← Complex.ofReal_cpow (band_pos b _).le] at he
  rw [← Complex.ofReal_tsum] at he
  have hr := congrArg Complex.re he
  change (riemannZeta (q.val:ℂ)).re - momentLoss q b = ∑' n, (b n).val^q.val at hr
  change _ = _ - (∑' n, (b n).val^q.val)
  linarith only [hr]

/-- The squared heat spectrum gives the ordinary fourth-trace loss at order two. -/
theorem momentLoss_two (P : Projection) {r : ℕ} (hd : MissingDimension P r) (hc : Conserving (projected P)) :
    momentLoss ⟨2,by norm_num⟩ (physicalSpectrum P hd hc) = traceLoss (projected P) := by
  rw [← quadratic_physicalReading P hd hc]
  apply tsum_congr
  intro k
  simp only [spectralDrop,powerResponse,quadraticResponse,Real.rpow_two]

theorem momentLoss_transfer (a q : GibbsExponent) (ha : a ≤ q) (b : SpectralBand 1) :
    momentLoss a b^(q.val/a.val) ≤ momentLoss q b := by
  let p : Ici (1:ℝ) := ⟨q.val/a.val,(one_le_div (show 0 < a.val from a.property)).mpr (show a.val ≤ q.val from ha)⟩
  have ha' : 0 < a.val := a.property
  have he : scaledExponent a p = q := Subtype.ext (by change a.val*(q.val/a.val)=q.val; rw [mul_comm,div_mul_cancel₀ _ ha'.ne'])
  change relativeReading (powerResponse a) b^p.val ≤ relativeReading (powerResponse q) b
  simpa only [reference_error_eq_reading,he,Nat.cast_one,Real.one_rpow,one_mul] using
    detector_power_transfer a p (hotEdge 1) b

/-- Rank-one moment loss in units of energy weight increases with the moment order. -/
theorem moment_root_monotone (b : SpectralBand 1) :
    Monotone (fun q : GibbsExponent => momentLoss q b^q.val⁻¹) := by
  intro a q haq
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg (momentLoss_nonneg a b) _)
    (momentLoss_transfer a q haq b) (inv_nonneg.mpr q.property.le)
  have hq' : 0 < q.val := q.property
  have ha' : 0 < a.val := a.property
  rw [← Real.rpow_mul (momentLoss_nonneg a b),show q.val/a.val*q.val⁻¹ = a.val⁻¹ by field_simp [hq'.ne',ha'.ne']] at hp
  exact hp

/-- Fixing the first N levels bounds every positive moment by the first remaining level to that power. -/
theorem momentLoss_le_tail (q : GibbsExponent) (b : SpectralBand 1) (N : ℕ)
    (h : ∀ k < N, (b k).val = occupationWeight k) : momentLoss q b ≤ occupationWeight N^q.val := by
  let f := powerResponse q
  have hz : (∑ k ∈ range N, levelError f (hotEdge 1) b k) = 0 := sum_eq_zero (fun k hk => by
    change |f.value (occupationWeight k) - f.value (b k).val| = 0
    rw [h k (mem_range.mp hk),sub_self,abs_zero])
  have he := detectorError_eq_prefix_add_tail f (hotEdge 1) b N
  rw [reference_error_eq_reading,hz,zero_add] at he
  exact he.trans_le ((detectorTail_le _ _ _ _).trans ((power_tailCeiling_le q 1 N).trans_eq (by rw [Nat.cast_one,one_mul])))

#print axioms momentLoss_eq_trace_difference
#print axioms momentLoss_two
#print axioms momentLoss_transfer
#print axioms moment_root_monotone
#print axioms momentLoss_le_tail

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
