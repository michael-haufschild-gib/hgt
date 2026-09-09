import GaloisForLFunctions.RHTower.FokasLenellsCauchyCoreEncoding
import GaloisForLFunctions.RHTower.HardyBlaschkeMultiplier

/-!
# Concrete holes in the Cauchy-encoded entire core

Every upper-pole rational Hardy vector lies outside the encoded core range.
A matching inner Blaschke factor cancels its pole. An alleged core preimage
would then become a Hardy vector with a real gap, contradicting gap uniqueness.
Thus the actual encoded range is a proper dense, nonclosed lower Hardy subspace.
-/

open MeasureTheory Complex Filter Topology Metric Set
open scoped ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The matching inner factor cancels every actual upper rational pole. -/
theorem blaschkeMulInv_upperPoleProbe (r a : ℝ) :
    blaschkeMulInv ((r:ℂ)+(Real.exp a:ℂ)*I) (upperPoleProbe r a) = lowerPoleProbe r a := by
  have hw : 0 < ((r:ℂ)+(Real.exp a:ℂ)*I).im := by
    simpa only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_one,mul_zero,zero_mul,add_zero,zero_add] using Real.exp_pos a
  have hc : ((r:ℂ)-(Real.exp a:ℂ)*I).im ≠ 0 := by
    simpa only [Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_one,mul_zero,zero_mul,add_zero,zero_add,zero_sub,
      neg_ne_zero] using Real.exp_ne_zero a
  have hu := (memLp_cauchyKernel (ne_of_gt hw)).coeFn_toLp
  have hl := (memLp_cauchyKernel hc).coeFn_toLp
  change (upperPoleProbe r a : ℝ → ℂ) =ᵐ[volume]
    (fun x : ℝ => ((x:ℂ)-((r:ℂ)+(Real.exp a:ℂ)*I))⁻¹) at hu
  change (lowerPoleProbe r a : ℝ → ℂ) =ᵐ[volume]
    (fun x : ℝ => ((x:ℂ)-((r:ℂ)-(Real.exp a:ℂ)*I))⁻¹) at hl
  apply Lp.ext
  filter_upwards [coeFn_blaschkeMulInv ((r:ℂ)+(Real.exp a:ℂ)*I) (upperPoleProbe r a),hu,hl]
    with x hx hux hlx
  rw [hx,hux,hlx]
  have hd := ofReal_sub_ne_zero (ne_of_gt hw) x
  have hdc := ofReal_sub_ne_zero hc x
  simp only [blaschkeSymbolInv,map_add,map_mul,Complex.conj_ofReal,Complex.conj_I,mul_neg,
    ← sub_eq_add_neg]
  field_simp

/-- Every upper-pole probe is nonzero in the actual L² carrier. -/
theorem upperPoleProbe_ne_zero (r a : ℝ) : upperPoleProbe r a ≠ 0 := by
  intro h
  have he := blaschkeMulInv_upperPoleProbe r a
  rw [h,map_zero] at he
  exact lowerPoleProbe_ne_zero r a he.symm

/-- No upper-pole rational datum has a preimage in the actual spectral-gap entire core. -/
theorem upperPoleProbe_not_mem_rawComplexCauchyCoreRange (r a : ℝ) :
    upperPoleProbe r a ∉ rawComplexCauchyCoreRange := by
  rintro ⟨u,hu⟩
  change negativeCauchy u.val = upperPoleProbe r a at hu
  let w : ℂ := (r:ℂ)+(Real.exp a:ℂ)*I
  have hw : 0 < w.im := by
    simpa only [w,Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_one,mul_zero,zero_mul,add_zero,zero_add] using Real.exp_pos a
  have hk : u.val + upperPoleProbe r a ∈ hardyL2 := by
    apply (negativeCauchy_eq_zero_iff _).1
    rw [map_add,negativeCauchy_upperPoleProbe,hu,add_neg_cancel]
  have hb : blaschkeMulInv w u.val ∈ hardyL2 := by
    have hm := blaschkeMulInv_mem_hardyL2 hw hk
    rw [map_add,blaschkeMulInv_upperPoleProbe] at hm
    have hl := (negativeCauchy_eq_zero_iff _).1 (negativeCauchy_lowerPoleProbe r a)
    simpa only [add_sub_cancel_right] using hardyL2.sub_mem hm hl
  obtain ⟨b,hgap⟩ := rawComplexEntireCore_exists_zeroGap u
  have hg : ∀ᵐ x ∂(volume : Measure ℝ), dist x 0 < Real.exp b →
      (blaschkeMulInv w u.val : ℝ → ℂ) x = 0 := by
    filter_upwards [coeFn_blaschkeMulInv w u.val,hgap] with x hx hg
    intro hxb
    rw [hx,hg hxb,mul_zero]
  have hz := (upperHardyL2_gap_zero_iff ⟨blaschkeMulInv w u.val,hb⟩ 0 b).1 hg
  have hv : blaschkeMulInv w u.val = 0 := congrArg (fun v : UpperHardyL2 => v.val) hz
  have hn := norm_blaschkeMulInv (ne_of_gt hw) u.val
  rw [hv,norm_zero] at hn
  have hu0 : u.val = 0 := norm_eq_zero.mp hn.symm
  rw [hu0,map_zero] at hu
  exact upperPoleProbe_ne_zero r a hu.symm

/-- The encoded core misses actual lower Hardy data despite its density there. -/
theorem rawComplexCauchyCoreRange_ne_lowerHardy : rawComplexCauchyCoreRange ≠ hardyL2ᗮ := by
  intro he
  apply upperPoleProbe_not_mem_rawComplexCauchyCoreRange 0 0
  rw [he]
  exact (negativeCauchy_eq_neg_iff _).1 (negativeCauchy_upperPoleProbe 0 0)

/-- The literal encoded core range is not closed in the ambient L² topology. -/
theorem rawComplexCauchyCoreRange_not_closed : ¬ IsClosed (rawComplexCauchyCoreRange : Set SoninL2) := by
  intro hc
  apply rawComplexCauchyCoreRange_ne_lowerHardy
  apply SetLike.coe_injective
  calc
    (rawComplexCauchyCoreRange : Set SoninL2) = closure (rawComplexCauchyCoreRange : Set SoninL2) :=
      hc.closure_eq.symm
    _ = (hardyL2ᗮ : Set SoninL2) := closure_rawComplexCauchyCoreRange

end
end RHTower.FokasLenells
