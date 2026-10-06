import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticBoundaryProjection
import GaloisForLFunctions.RHTower.ThetaCuspRatioQuadraticBarrierStrict
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open RHTower RHTower.ThetaCuspModularRatio

theorem actual_nonlinearCone_bounds {x : ℝ} (hx : 0 < x) :
    0 < (k x)⁻¹ ∧ (k x)⁻¹ ≤ 4/5 ∧
    0 < kineticGap x ∧ kineticGap x ≤ 361/25 ∧
    0 < 9-kineticGap x*((k x)⁻¹)^2 ∧
    0 < kineticGap x*boundaryRatio x ∧
    (k x)⁻¹*(kineticGap x*boundaryRatio x) < 1 ∧
    kineticGap x*ThetaCriticalBarrier.b ((k x)⁻¹) <
      kineticGap x*boundaryRatio x-((k x)⁻¹)^2*(kineticGap x*boundaryRatio x)^2 ∧
    (1-(k x)⁻¹*(kineticGap x*boundaryRatio x))/3=J x/u x := by
  let h := (k x)⁻¹
  let r := kineticGap x
  let q := boundaryRatio x
  let a := r*q
  change 0 < h ∧ h ≤ 4/5 ∧ 0 < r ∧ r ≤ 361/25 ∧
    0 < 9-r*h^2 ∧ 0 < a ∧ h*a < 1 ∧
    r*ThetaCriticalBarrier.b h < a-h^2*a^2 ∧ (1-h*a)/3=J x/u x
  have hk : 0 < k x := lt_trans (by norm_num) (k_gt hx.le)
  have hu : 0 < u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
  have ht := t_pos hx.le
  have hh := criticalClock_bounds hx
  have hr : 0 < r := by
    dsimp [r,kineticGap]
    exact mul_pos (sq_pos_of_pos hk) ht
  have hr1 : r ≤ 361/25 := (kineticGap_lt hx.le).le
  have hscale : h^2*r=t x := by
    dsimp [h,r,kineticGap]
    field_simp [hk.ne']
  have hhr : h*r=k x*t x := by
    dsimp [h,r,kineticGap]
    field_simp [hk.ne']
  have hV : 9-r*h^2=u x^2 := by
    rw [mul_comm r,hscale]
    unfold t
    ring
  have hb : 0 < ThetaCriticalBarrier.b h := by
    unfold ThetaCriticalBarrier.b
    change 0 < 1/12-7*((k x)⁻¹)/72
    linarith only [hh.2]
  have hbar : ThetaCriticalBarrier.b h < q-t x*q^2 := by
    have he := quadraticSourceError_pos hx
    rw [quadraticSourceError,criticalError_eq] at he
    change 0 < q-ThetaCriticalBarrier.b h-t x*q^2 at he
    linarith only [he]
  have hq : 0 < q := by
    have hn := mul_nonneg ht.le (sq_nonneg q)
    linarith only [hb,hbar,hn]
  have ha : 0 < a := mul_pos hr hq
  have hha : h*a=k x*(t x*q) := by
    dsimp only [a]
    rw [←mul_assoc,hhr]
    ring
  have hgap : h*a < 1 := by
    have hg := mul_lt_mul_of_pos_left (source_ratio_gap hx) hk
    have hid : k x*(k x)⁻¹=1 := by field_simp [hk.ne']
    rw [hha]
    simpa only [hid] using hg
  have hbscaled : r*ThetaCriticalBarrier.b h < a-h^2*a^2 := by
    have hg := mul_lt_mul_of_pos_left hbar hr
    have he : r*(q-t x*q^2)=a-h^2*a^2 := by
      rw [←hscale]
      dsimp only [a]
      ring
    rwa [he] at hg
  have hz : (1-h*a)/3=J x/u x := by
    rw [hha,J_boundaryRatio hx]
    dsimp only [q]
    field_simp [hu.ne']
  exact ⟨hh.1,hh.2,hr,hr1,hV.symm ▸ sq_pos_of_pos hu,ha,hgap,hbscaled,hz⟩

theorem actual_kinetic_boundary_projection {x : ℝ} (hx : 0 < x) :
    ∃ s : ℝ, 0 < s ∧ s < (6/5)*(361/25) ∧
      kineticBoundaryV ((k x)⁻¹) s=u x^2 ∧
      0 < J x/u x ∧ J x/u x < kineticBoundaryZ ((k x)⁻¹) s ∧
      kineticBoundaryZ ((k x)⁻¹) s < 1/3 := by
  obtain ⟨hh0,hh1,hr0,hr1,hv,ht,hht,hbar,hz⟩ := actual_nonlinearCone_bounds hx
  obtain ⟨s,hs0,hs1,hV,hz0,hz1,hz2⟩ := nonlinearCone_boundary_projection
    hh0 hh1 hr0 hr1 hv ht hht hbar
  have hk : k x ≠ 0 := (lt_trans (by norm_num) (k_gt hx.le)).ne'
  have hvEq : 9-kineticGap x*((k x)⁻¹)^2=u x^2 := by
    unfold kineticGap t
    field_simp [hk]
    ring
  rw [hz] at hz0 hz1
  exact ⟨s,hs0,hs1,hV.trans hvEq,hz0,hz1,hz2⟩

end
end HTGeometry.ThetaRatioKineticContraction
