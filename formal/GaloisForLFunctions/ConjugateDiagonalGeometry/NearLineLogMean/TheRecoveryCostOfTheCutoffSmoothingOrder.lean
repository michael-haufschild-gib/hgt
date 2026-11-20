import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheEndpointScalesOfTheSmoothedMoebiusTail
import GaloisForLFunctions.RHTower.Sieve.HarmonicDyadicBlock
import GaloisForLFunctions.RHTower.Sieve.MoebiusDoubleLogRealCutoff

/-!
# The recovery cost of the logarithmic cutoff order

One removed integration pays a power of the logarithmic height. For a
length T^θ and cutoff penalty fraction α, the normalized exponent paid
by the integer order tends to α. Its first correction changes sign at
θ = log 2. Both the integer cutoff and the ceiling in the order are retained.
-/

noncomputable section
open Filter Topology
open _root_.RHTower.Sieve
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

/-- Cost in units of the logarithm of the polynomial length. -/
def cutoffRecoveryFraction (α θ T : ℝ) :=
  (cutoffLogarithmicOrder α ⌊T^θ⌋₊:ℝ)*Real.log (1+Real.log T)/(θ*Real.log T)

private def lengthAt (θ u : ℝ) := ⌊Real.exp (θ*u)⌋₊

private theorem logarithmic_floor_error {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun u => Real.log (lengthAt θ u)-θ*u) atTop (𝓝 0) ∧
    Tendsto (fun u => Real.log (lengthAt θ u)/u) atTop (𝓝 θ) := by
  have hid : Tendsto (fun u : ℝ => u) atTop atTop := tendsto_id
  have hx := Real.tendsto_exp_atTop.comp (hid.const_mul_atTop hθ)
  have hn := tendsto_nat_floor_atTop.comp hx
  have hf := (tendsto_nat_floor_div_atTop (R:=ℝ)).comp hx
  have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hf
  have he : Tendsto (fun u => Real.log (lengthAt θ u)-θ*u) atTop (𝓝 0) := by
    rw [←Real.log_one]
    apply hlog.congr'
    filter_upwards [hn.eventually_ge_atTop 1] with u hu
    change Real.log ((lengthAt θ u:ℝ)/Real.exp (θ*u))=_
    rw [Real.log_div (Nat.cast_ne_zero.mpr (by change 1 ≤ lengthAt θ u at hu; omega))
      (Real.exp_pos _).ne',Real.log_exp]
  refine ⟨he,?_⟩
  have hr := (tendsto_log_natFloor_div_log_one.comp hx).mul_const θ
  rw [one_mul] at hr
  apply hr.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
  change Real.log (lengthAt θ u)/Real.log (Real.exp (θ*u))*θ=_
  rw [Real.log_exp]
  field_simp [hθ.ne',hu.ne']

private theorem correction_in_log_height {α θ : ℝ} (hα : 0 ≤ α) (hθ : 0 < θ) :
    let m := fun u => cutoffLogarithmicOrder α (lengthAt θ u)
    let l := fun u => Real.log (1+u)
    Tendsto (fun u : ℝ => l u*(α-(m u:ℝ)*l u/(θ*u))) atTop (𝓝 (α*Real.log (θ/Real.log 2))) := by
  intro m l
  let y (u : ℝ) := Real.log (lengthAt θ u)
  let A (u : ℝ) := 1+u
  let B (u : ℝ) := y u/Real.log 2
  let L (u : ℝ) := Real.log (B u)
  let U (u : ℝ) := θ*u
  let k := Real.log (θ/Real.log 2)
  have hlog2 := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hid : Tendsto (fun u : ℝ => u) atTop atTop := tendsto_id
  have hA : Tendsto A atTop atTop := tendsto_atTop_mono (fun u => le_add_of_nonneg_left zero_le_one) hid
  have hl : Tendsto l atTop atTop := Real.tendsto_log_atTop.comp hA
  have hx := Real.tendsto_exp_atTop.comp (hid.const_mul_atTop hθ)
  have hn : Tendsto (lengthAt θ) atTop atTop := tendsto_nat_floor_atTop.comp hx
  have hy := Real.tendsto_log_atTop.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp hn)
  have hB : Tendsto B atTop atTop := hy.atTop_div_const hlog2
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp hB
  obtain ⟨hyerr,hyr⟩ := logarithmic_floor_error hθ
  have ha : Tendsto (fun u => A u/u) atTop (𝓝 1) := by
    have h := hid.inv_tendsto_atTop.add_const 1
    rw [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
    change u⁻¹+1=(1+u)/u
    rw [add_div,one_div,div_self hu.ne']
  have hb : Tendsto (fun u => B u/u) atTop (𝓝 (θ/Real.log 2)) := by
    exact (hyr.div_const (Real.log 2)).congr fun u => by dsimp only [B,y]; ring
  have hg : Tendsto (fun u => L u-l u) atTop (𝓝 k) := by
    simpa only [div_one] using tendsto_log_sub_log_of_ratio zero_lt_one (div_pos hθ hlog2)
      ha hb (hA.eventually_gt_atTop 0) (hB.eventually_gt_atTop 0)
  have hrel : Tendsto (fun u => l u/L u) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x:=(1:ℝ))).sub (hg.mul hL.inv_tendsto_atTop)
    simp only [mul_zero,sub_zero] at h
    apply h.congr'
    filter_upwards [hL.eventually_gt_atTop 0] with u hu
    change 1-(L u-l u)*(L u)⁻¹=l u/L u
    field_simp [hu.ne']
    ring
  have hlU : Tendsto (fun u => l u/U u) atTop (𝓝 0) := by
    have h := ((Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hA).mul ha).div_const θ
    simpa only [zero_mul,zero_div] using h.congr' (by
      filter_upwards [hA.eventually_gt_atTop 0] with u hu
      change Real.log (A u)/A u*(A u/u)/θ=l u/(θ*u)
      change Real.log (A u)/A u*(A u/u)/θ=Real.log (A u)/(θ*u)
      field_simp [hu.ne',hθ.ne'])
  have hl2U : Tendsto (fun u => (l u)^2/U u) atTop (𝓝 0) := by
    have hsq : Tendsto (fun v : ℝ => (Real.log v)^2/v) atTop (𝓝 0) := by
      simpa only [Real.rpow_two,Real.rpow_one] using
        (isLittleO_log_rpow_rpow_atTop 2 (zero_lt_one : (0:ℝ)<1)).tendsto_div_nhds_zero
    have h := ((hsq.comp hA).mul ha).div_const θ
    simpa only [zero_mul,zero_div] using h.congr' (by
      filter_upwards [hA.eventually_gt_atTop 0] with u hu
      change (Real.log (A u))^2/A u*(A u/u)/θ=(Real.log (A u))^2/(θ*u)
      field_simp [hu.ne',hθ.ne'])
  let r (u : ℝ) := (m u:ℝ)-α*y u/L u
  have hr : Tendsto (fun u => r u*((l u)^2/U u)) atTop (𝓝 0) := by
    have hround : ∀ᶠ u in atTop, 0 ≤ r u ∧ r u < 1 := by
      filter_upwards [hn.eventually_ge_atTop 3,hL.eventually_gt_atTop 0] with u hu hLu
      obtain ⟨ha',hb'⟩ := cutoff_penalty_rounding hα hu
      change 0 ≤ (m u:ℝ)*L u-α*y u at ha'
      change (m u:ℝ)*L u-α*y u < L u at hb'
      dsimp only [r]
      constructor
      · exact sub_nonneg.mpr ((div_le_iff₀ hLu).mpr (by linarith only [ha']))
      · have h := (lt_div_iff₀ hLu).mpr
          (show ((m u:ℝ)-1)*L u < α*y u by linarith only [hb'])
        linarith only [h]
    apply squeeze_zero' _ _ hl2U
    · filter_upwards [hround,eventually_gt_atTop (0:ℝ)] with u hu hu0
      exact mul_nonneg hu.1 (div_nonneg (sq_nonneg _) (mul_pos hθ hu0).le)
    filter_upwards [hround,eventually_gt_atTop (0:ℝ)] with u hu hu0
    exact mul_le_of_le_one_left (div_nonneg (sq_nonneg _) (mul_pos hθ hu0).le) hu.2.le
  have H := (((hrel.mul hg).const_mul α).sub (((hyerr.mul hlU).mul hrel).const_mul α)).sub hr
  simp only [one_mul,zero_mul,mul_zero,sub_zero] at H
  apply H.congr'
  filter_upwards [hL.eventually_gt_atTop 0,eventually_gt_atTop (0:ℝ)] with u hLu hu
  change α*(l u/L u*(L u-l u))-α*((y u-U u)*(l u/U u)*(l u/L u))-
    ((m u:ℝ)-α*y u/L u)*((l u)^2/U u) = l u*(α-(m u:ℝ)*l u/U u)
  have hU : U u ≠ 0 := (mul_pos hθ hu).ne'
  field_simp [hLu.ne',hU]
  ring

/-- First correction to the normalized recovery cost. Its sign depends
on the length exponent, and the limit includes the integer rounding. -/
theorem cutoff_recovery_first_correction {α θ : ℝ} (hα : 0 ≤ α) (hθ : 0 < θ) :
    Tendsto (fun T : ℝ => Real.log (1+Real.log T)*(α-cutoffRecoveryFraction α θ T))
      atTop (𝓝 (α*Real.log (θ/Real.log 2))) := by
  have h := (correction_in_log_height hα hθ).comp Real.tendsto_log_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  simp only [Function.comp_apply,lengthAt,cutoffRecoveryFraction,Real.rpow_def_of_pos hT,mul_comm θ (Real.log T)]

/-- The actual order costs an asymptotic fraction α of the logarithmic length. -/
theorem cutoff_recovery_fraction_limit {α θ : ℝ} (hα : 0 ≤ α) (hθ : 0 < θ) :
    Tendsto (cutoffRecoveryFraction α θ) atTop (𝓝 α) := by
  let l (T : ℝ) := Real.log (1+Real.log T)
  have hA : Tendsto (fun T : ℝ => 1+Real.log T) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_add_of_nonneg_left zero_le_one) Real.tendsto_log_atTop
  have hl : Tendsto l atTop atTop := Real.tendsto_log_atTop.comp hA
  have h := (tendsto_const_nhds (x:=α)).sub ((cutoff_recovery_first_correction hα hθ).mul hl.inv_tendsto_atTop)
  simp only [mul_zero,sub_zero] at h
  apply h.congr'
  filter_upwards [hl.eventually_gt_atTop 0] with T hT
  change α-l T*(α-cutoffRecoveryFraction α θ T)*(l T)⁻¹=cutoffRecoveryFraction α θ T
  field_simp [hT.ne']
  ring

/-- The smallest slope in a bound uniform for all large polynomial
length exponents is α. The endpoint slope itself is admissible. -/
theorem affine_cutoff_recovery_iff {α c d : ℝ} (hα : 0 ≤ α) (hc : 0 ≤ c) :
    (∀ᶠ θ : ℝ in atTop, ∀ᶠ T : ℝ in atTop,
      (cutoffLogarithmicOrder α ⌊T^θ⌋₊:ℝ)*Real.log (1+Real.log T) ≤ (c+d*θ)*Real.log T) ↔ α ≤ d := by
  constructor
  · intro H
    by_contra! hd
    have hb : ∀ᶠ θ : ℝ in atTop, c/θ+d < α := by
      have hl := (tendsto_id : Tendsto (fun θ : ℝ => θ) atTop atTop).inv_tendsto_atTop.const_mul c
      have h := (hl.add_const d).eventually_lt_const (show c*0+d < α by simpa using hd)
      simpa only [div_eq_mul_inv,Pi.inv_apply,id_eq] using h
    obtain ⟨θ,hθ⟩ := (H.and (hb.and (eventually_gt_atTop (0:ℝ)))).exists
    obtain ⟨hord,hlt,hpos⟩ := hθ
    have hu : ∀ᶠ T : ℝ in atTop, cutoffRecoveryFraction α θ T ≤ c/θ+d := by
      filter_upwards [hord,eventually_gt_atTop (1:ℝ)] with T hT h1
      apply (div_le_iff₀ (mul_pos hpos (Real.log_pos h1))).mpr
      have hcancel : (c/θ+d)*(θ*Real.log T)=(c+d*θ)*Real.log T := by field_simp [hpos.ne']
      rwa [hcancel]
    exact (not_le.mpr hlt) (le_of_tendsto (cutoff_recovery_fraction_limit hα hpos) hu)
  · intro hd
    by_cases hz : α=0
    · subst α
      filter_upwards [eventually_gt_atTop (0:ℝ)] with θ hθ
      filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
      simpa [cutoffLogarithmicOrder] using mul_nonneg (add_nonneg hc (mul_nonneg hd hθ.le)) (Real.log_nonneg hT)
    have ha := lt_of_le_of_ne hα (Ne.symm hz)
    filter_upwards [eventually_gt_atTop (Real.log 2)] with θ hθ
    have hL := Real.log_pos (by norm_num : (1:ℝ)<2)
    have ht := hL.trans hθ
    have hpos := mul_pos ha (Real.log_pos ((one_lt_div hL).mpr hθ))
    have hs := (cutoff_recovery_first_correction hα ht).eventually_const_lt hpos
    filter_upwards [hs,eventually_gt_atTop (1:ℝ)] with T hcon hT
    have hl := Real.log_pos (show 1 < 1+Real.log T from lt_add_of_pos_right _ (Real.log_pos hT))
    have hr := (sub_pos.mp (pos_of_mul_pos_right hcon hl.le))
    have hu := (div_lt_iff₀ (mul_pos ht (Real.log_pos hT))).mp hr
    have he := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd ht.le) (Real.log_pos hT).le
    linarith only [hu,he,mul_nonneg hc (Real.log_pos hT).le]

/-- Within the cutoff family, only the unsmoothed order meets the
sublinear length dependence of the exact zero-width recovery criterion. -/
theorem cutoff_sublinear_recovery_iff {α : ℝ} (hα : 0 ≤ α) :
    (∀ d : ℝ, 0 < d → ∀ᶠ θ : ℝ in atTop, ∀ᶠ T : ℝ in atTop,
      (cutoffLogarithmicOrder α ⌊T^θ⌋₊:ℝ)*Real.log (1+Real.log T) ≤ d*θ*Real.log T) ↔ α=0 := by
  constructor
  · intro h
    by_contra ha
    have hp := half_pos (lt_of_le_of_ne hα (Ne.symm ha))
    have hb := (affine_cutoff_recovery_iff (c:=0) (d:=α/2) hα le_rfl).mp
      (by simpa only [zero_add] using h (α/2) hp)
    linarith only [hb,hp]
  · rintro rfl d hd
    simpa only [zero_add] using
      (affine_cutoff_recovery_iff (α:=0) (c:=0) (d:=d) le_rfl le_rfl).mpr hd.le

#print axioms cutoff_sublinear_recovery_iff
#print axioms cutoff_recovery_first_correction
#print axioms cutoff_recovery_fraction_limit
#print axioms affine_cutoff_recovery_iff

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
