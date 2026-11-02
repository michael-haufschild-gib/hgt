import GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.CutoffDilation

/-!
# The residual gap for finite cusp packets

All coefficients and cutoff interference are retained by putting the entire
packet in `L²(ℝ)`. Its two height shifts are the two inverse unitary dilations.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

noncomputable section

/-- A finite cusp packet, with unrestricted complex coefficients. -/
def cuspPacket {ι : Type*} (S : Finset ι) (u : ℂ)
    (Y : ι → ℝ) (c : ι → ℂ) (y : ℝ) : ℂ :=
  ∑ i ∈ S, c i * cuspCutoff u (Y i) y

theorem cuspPacket_memLp {ι : Type*} (S : Finset ι) {u : ℂ} (hur : u.re < 0)
    (Y : ι → ℝ) (c : ι → ℂ) (hY : ∀ i ∈ S, 0 ≤ Y i) :
    MemLp (cuspPacket S u Y c) 2 volume :=
  memLp_finset_sum S fun i hi => (cuspCutoff_memLp hur (hY i hi)).const_mul (c i)

private theorem dilation_packet_ae {ι : Type*} (S : Finset ι) (u : ℂ)
    (Y : ι → ℝ) (c : ι → ℂ) (f : SoninL2)
    (hf : (f : ℝ → ℂ) =ᵐ[volume] cuspPacket S u Y c) {r : ℝ} (hr : 0 < r) :
    (dilation r hr f : ℝ → ℂ) =ᵐ[volume]
      fun y => (r : ℂ) ^ (-u) * cuspPacket S u (fun i => Y i / r) c y := by
  have hcomp := hf.comp_tendsto (realMul_quasiMeasurePreserving r hr.ne').tendsto_ae
  filter_upwards [dilation_ae r hr f, hcomp] with y hd hf'
  rw [hd, hf']
  simp only [cuspPacket, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = c i * ((Real.sqrt r : ℂ) * cuspCutoff u (Y i) (r * y)) := by ring
    _ = _ := by rw [cuspCutoff_dilation u (Y i) hr y]; ring

private theorem inverse_two_power (u : ℂ) :
    (((2 : ℝ)⁻¹ : ℝ) : ℂ) ^ (-u) = (2 : ℂ) ^ u := by
  have hq : (2 : ℂ) ^ u ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hn : (2 : ℂ) ^ (-u) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  apply mul_right_cancel₀ hn
  calc
    _ = ((((2 : ℝ)⁻¹ : ℝ) : ℂ) * (2 : ℂ)) ^ (-u) :=
      (Complex.mul_cpow_ofReal_nonneg (by norm_num) (by norm_num) (-u)).symm
    _ = 1 := by norm_num
    _ = _ := by rw [Complex.cpow_neg, mul_inv_cancel₀ hq]

/-- The whole cusp packet has a positive residual gap, independently of frequency and coefficients. -/
theorem cuspPacket_residual_gap {ι : Type*} (S : Finset ι) {u : ℂ} (hur : u.re < 0)
    (Y : ι → ℝ) (c : ι → ℂ) (hY : ∀ i ∈ S, 0 ≤ Y i) :
    ((2 : ℝ) ^ u.re + (2 : ℝ) ^ (-u.re) - 2) ^ 2 *
        (∫ y, ‖cuspPacket S u Y c y‖ ^ 2) ≤
      ∫ y, ‖∑ i ∈ S, c i *
        ((2 : ℂ) ^ u * cuspCutoff u (Y i * 2) y +
          (2 : ℂ) ^ (-u) * cuspCutoff u (Y i / 2) y -
            ((2 : ℂ) ^ u + (2 : ℂ) ^ (-u)) * cuspCutoff u (Y i) y)‖ ^ 2 := by
  have hf := cuspPacket_memLp S hur Y c hY
  let f : SoninL2 := hf.toLp _
  let U := dilationUnitary 2 (by norm_num : (0 : ℝ) < 2)
  let q : ℂ := (2 : ℂ) ^ u
  let R : SoninL2 := U f + U.symm f - (q + q⁻¹) • f
  have hq : q ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hfn : (f : ℝ → ℂ) =ᵐ[volume] cuspPacket S u Y c := hf.coeFn_toLp
  have hd := dilation_packet_ae S u Y c f hfn (r := 2) (by norm_num)
  have hi := dilation_packet_ae S u Y c f hfn (r := (2 : ℝ)⁻¹) (by norm_num)
  have hR : (R : ℝ → ℂ) =ᵐ[volume] fun y => ∑ i ∈ S, c i *
      ((2 : ℂ) ^ u * cuspCutoff u (Y i * 2) y +
        (2 : ℂ) ^ (-u) * cuspCutoff u (Y i / 2) y -
          ((2 : ℂ) ^ u + (2 : ℂ) ^ (-u)) * cuspCutoff u (Y i) y) := by
    have hdf : (U f : ℝ → ℂ) =ᵐ[volume]
        fun y => (2 : ℂ) ^ (-u) * cuspPacket S u (fun i => Y i / 2) c y := hd
    have hif : (U.symm f : ℝ → ℂ) =ᵐ[volume]
        fun y => (2 : ℂ) ^ u * cuspPacket S u (fun i => Y i * 2) c y := by
      simpa only [U, dilationUnitary_symm_apply, inverse_two_power, div_inv_eq_mul] using hi
    filter_upwards [Lp.coeFn_sub (U f + U.symm f) ((q + q⁻¹) • f),
      Lp.coeFn_add (U f) (U.symm f), Lp.coeFn_smul (q + q⁻¹) f,
      hdf, hif, hfn] with y hs ha hm hd' hi' hf'
    change (U f + U.symm f - (q + q⁻¹) • f : SoninL2) y = _
    rw [hs, ha, hm]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hd', hi', hf',
      cuspPacket, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hiS
    simp only [q, ← Complex.cpow_neg]
    ring
  have hn : ‖R‖ ^ 2 = ∫ y, ‖∑ i ∈ S, c i *
      ((2 : ℂ) ^ u * cuspCutoff u (Y i * 2) y +
        (2 : ℂ) ^ (-u) * cuspCutoff u (Y i / 2) y -
          ((2 : ℂ) ^ u + (2 : ℂ) ^ (-u)) * cuspCutoff u (Y i) y)‖ ^ 2 := by
    rw [norm_sq_lp_eq_integral_norm_sq]
    exact integral_congr_ae (hR.fun_comp fun z => ‖z‖ ^ 2)
  have hg := unitary_pair_gap U hq f
  have hnorm : ‖q‖ = (2 : ℝ) ^ u.re := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) u
  have hcoef : ‖q‖ + ‖q‖⁻¹ - 2 = (2 : ℝ) ^ u.re + (2 : ℝ) ^ (-u.re) - 2 := by
    rw [hnorm, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have hr : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hnonneg : 0 ≤ ‖q‖ + ‖q‖⁻¹ - 2 := by
    have he : ‖q‖ + ‖q‖⁻¹ - 2 = (‖q‖ - 1) ^ 2 / ‖q‖ := by
      field_simp
      ring
    rw [he]
    exact div_nonneg (sq_nonneg _) hr.le
  have hsq := pow_le_pow_left₀ (mul_nonneg hnonneg (norm_nonneg f)) hg 2
  rw [mul_pow, hcoef, norm_sq_toLp_eq_integral_norm_sq hf, hn] at hsq
  exact hsq

end

end GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates
