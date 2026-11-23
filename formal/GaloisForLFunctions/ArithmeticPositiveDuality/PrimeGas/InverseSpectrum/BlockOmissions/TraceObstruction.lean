import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.BlockOmissions.BlockPartition
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.BlockOmissions.BlockClosure

/-! # Physical lower bounds on trace-control exponents at fixed complex temperature -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology

/-- At fixed height, exponent and missing dimension, a single fourth-trace deficit controls all physical complex losses. -/
def traceControlsAt (r : ℕ) (z : ℂ) (p K : ℝ) : Prop :=
  ∀ (P : Projection) (hd : MissingDimension P r) (hc : Conserving (projected P)),
    ‖relativePartition (physicalSpectrum P hd hc) z‖^p ≤ K * traceLoss (projected P)

private def traceExponent : GibbsExponent := ⟨2,by norm_num⟩

private theorem quadratic_block (N r : ℕ) : relativeReading quadraticResponse (blockSpectrum N r) =
    occupationWeight N ^ (2:ℝ) * normalizedBlock traceExponent r N := by
  have h := power_tailCeiling_eq_scaled traceExponent r N
  rw [relativeReading_block]
  simpa only [tailCeiling,powerResponse,traceExponent,Real.rpow_two,quadraticResponse] using h

private theorem normalized_trace_bound {r : ℕ} {z : ℂ} (hz : 0 < z.re) (p : GibbsExponent) {K : ℝ}
    (h : traceControlsAt r z p.val K) (N : ℕ) :
    ‖complexBlock z r N‖^p.val ≤ K * occupationWeight N^(2-z.re*p.val) * normalizedBlock traceExponent r N := by
  let S := {b : SpectralBand r | ‖relativePartition b z‖^p.val ≤ K*relativeReading quadraticResponse b}
  have hs : IsClosed S := isClosed_le ((Real.continuous_rpow_const p.property.le).comp
    (continuous_relativePartition_spectrum hz r).norm) (continuous_const.mul (continuous_relativeReading _ r))
  have hsub : physicalSpectra r ⊆ S := by
    rintro _ ⟨P,hd,hc,rfl⟩
    change _ ≤ K*relativeReading quadraticResponse _
    rw [quadratic_physicalReading]
    exact h P hd hc
  have hb := closure_minimal hsub hs (blockSpectrum_mem_closure N r)
  change ‖relativePartition (blockSpectrum N r) z‖^p.val ≤ K*relativeReading quadraticResponse (blockSpectrum N r) at hb
  rw [relativePartition_block_scaled N r hz,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (occupationWeight_pos N),
    Real.mul_rpow (Real.rpow_nonneg (occupationWeight_pos N).le _) (norm_nonneg _),
    ← Real.rpow_mul (occupationWeight_pos N).le,quadratic_block] at hb
  have hw : occupationWeight N^(2:ℝ) = occupationWeight N^(z.re*p.val) * occupationWeight N^(2-z.re*p.val) := by
    rw [← Real.rpow_add (occupationWeight_pos N)]
    congr 1
    ring
  rw [hw] at hb
  apply le_of_mul_le_mul_left (a := occupationWeight N^(z.re*p.val)) _ (Real.rpow_pos_of_pos (occupationWeight_pos N) _)
  exact hb.trans_eq (by ring)

private theorem norm_complexBlock_tendsto (z : ℂ) (r : ℕ) (p : GibbsExponent) :
    Tendsto (fun N => ‖complexBlock z r N‖^p.val) atTop (𝓝 ((r:ℝ)^p.val)) := by
  have ht : Tendsto (fun N => ‖complexBlock z r N‖^p.val) atTop (𝓝 (‖(r:ℂ)‖^p.val)) :=
    ((Real.continuous_rpow_const p.property.le).tendsto ‖(r:ℂ)‖).comp (complexBlock_tendsto z r).norm
  simpa only [Complex.norm_natCast] using ht

/-- No finite physical bound is possible when the vanishing power of the loss falls short of the fourth trace. -/
theorem trace_control_forces_exponent (r : ℕ) {z : ℂ} (hz : 0 < z.re) (p : GibbsExponent) {K : ℝ}
    (h : traceControlsAt (r+1) z p.val K) : 2 ≤ z.re*p.val := by
  by_contra! hlt
  have he : 0 < 2-z.re*p.val := sub_pos.mpr hlt
  have ht : Tendsto (fun N => occupationWeight N^(2-z.re*p.val)) atTop (𝓝 0) := by
    have ht' : Tendsto (fun N => occupationWeight N^(2-z.re*p.val)) atTop (𝓝 ((0:ℝ)^(2-z.re*p.val))) :=
      ((Real.continuous_rpow_const he.le).tendsto 0).comp occupationWeight_tendsto
    simpa only [Real.zero_rpow he.ne'] using ht'
  have hR := (ht.const_mul K).mul (normalizedBlock_tendsto traceExponent (r+1))
  have hb := le_of_tendsto_of_tendsto (norm_complexBlock_tendsto z (r+1) p) hR
    (Eventually.of_forall (normalized_trace_bound hz p h))
  rw [mul_zero,zero_mul] at hb
  exact (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.succ_pos r)) p.val).not_ge hb

/-- Below the necessary exponent, actual systems violate any proposed bound with an arbitrarily small positive trace deficit. -/
theorem exists_small_trace_violation (r : ℕ) {z : ℂ} (hz : 0 < z.re) (p : GibbsExponent)
    (hp : z.re*p.val < 2) (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : Projection) (hd : MissingDimension P (r+1)) (hc : Conserving (projected P)),
      0 < traceLoss (projected P) ∧ traceLoss (projected P) < ε ∧
      K * traceLoss (projected P) < ‖relativePartition (physicalSpectrum P hd hc) z‖^p.val := by
  let δ : GibbsExponent := ⟨z.re,hz⟩
  let B := (‖z‖/δ.val * relativeHead (powerResponse δ) (r+1))^p.val
  have hb (b : SpectralBand (r+1)) : ‖relativePartition b z‖^p.val ≤ B :=
    Real.rpow_le_rpow (norm_nonneg _) ((relativePartition_norm_le b δ le_rfl).trans
      (mul_le_mul_of_nonneg_left (relativeReading_bounds _ b).2 (div_nonneg (norm_nonneg _) hz.le))) p.property.le
  let A := max K ((B+1)/ε)
  have hn : ¬ traceControlsAt (r+1) z p.val A := fun h => hp.not_ge (trace_control_forces_exponent r hz p h)
  unfold traceControlsAt at hn
  push Not at hn
  obtain ⟨P,hd,hc,hw⟩ := hn
  let b := physicalSpectrum P hd hc
  have hD := (physical_reading_interior quadraticResponse P (Nat.succ_pos r) hd hc).1
  rw [quadratic_physicalReading] at hD
  refine ⟨P,hd,hc,hD,?_,(mul_le_mul_of_nonneg_right (le_max_left _ _) hD.le).trans_lt hw⟩
  by_contra! hbig
  have hzero : 0 ≤ B := (Real.rpow_nonneg (norm_nonneg _) _).trans (hb b)
  have hA : 0 ≤ A := (div_nonneg (by linarith only [hzero] : 0 ≤ B+1) hε.le).trans (le_max_right _ _)
  have hlt := hw.trans_le (hb b)
  have hle := (mul_le_mul_of_nonneg_right (le_max_right K ((B+1)/ε)) hε.le).trans (mul_le_mul_of_nonneg_left hbig hA)
  rw [div_mul_cancel₀ _ hε.ne'] at hle
  linarith only [hle,hlt]

/-- At a matching exponent, high occupations impose the finite-dimensional sharpness bound even at nonzero height. -/
theorem trace_control_forces_factor (r : ℕ) {z : ℂ} (hz : 0 < z.re) (p : GibbsExponent) {K : ℝ}
    (hp : z.re*p.val = 2) (h : traceControlsAt r z p.val K) : (r:ℝ)^p.val ≤ K*(r:ℝ) := by
  have he (N : ℕ) : ‖complexBlock z r N‖^p.val ≤ K*normalizedBlock traceExponent r N := by
    simpa only [hp,sub_self,Real.rpow_zero,mul_one] using normalized_trace_bound hz p h N
  exact le_of_tendsto_of_tendsto (norm_complexBlock_tendsto z r p)
    ((normalizedBlock_tendsto traceExponent r).const_mul K) (Eventually.of_forall he)

#print axioms trace_control_forces_exponent
#print axioms exists_small_trace_violation
#print axioms trace_control_forces_factor

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
