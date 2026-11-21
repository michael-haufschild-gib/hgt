import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.HarmonicRuns.ReboundWindows
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.HarmonicRuns.RecordPacking

/-! # Long hard windows at doubled dates of counted first returns -/
open Set MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.HarmonicRuns
noncomputable section
open SharpOccupation

/-- Count each successive first affordable visit after the unit exclusion
period once. For all origins and all s≤j, a fraction at most 4(17/18)ᴰ
has another j-gate visit within (17/16)ᴰ after twice its date. -/
theorem gaussian_counted_return_rebound :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let j := D/(256*(N+1))
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ s ≤ j, ∀ a : ℝ, ∃ t, records H s (1/10) a t ∧ ∀ᶠ n : ℕ in atTop,
        (markedReturns t {r | 2*r ∈ windowHits H j (1/10) ((17/16:ℝ)^D)} n : ℝ)/n ≤
          4*(17/18:ℝ)^D := by
  have hrad : (1/10:ℝ) < Real.sqrt 2 := by
    have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    nlinarith only [h,Real.sqrt_nonneg 2]
  obtain ⟨hx,htol⟩ := physicalArc_spec (by norm_num : (0:ℝ)<1/10) hrad
  filter_upwards [paired_window_mass,gaussian_unit_hit_enlargement,gaussian_path_all_prefixes_maximally_projective]
    with ω hp hloc hω
  filter_upwards [hp,hloc (1/1000) (by norm_num),(tendsto_add_atTop_nat 3).eventually unit_budget]
    with k hk hs hbud
  intro N D j H s hsj a
  let J := D/(128*(N+1))
  let W := (17/16:ℝ)^D
  let B := {r | 2*r ∈ windowHits H j (1/10) W}
  let S := {u | u ∈ visitSet H J (101/1000) ∧ 2*u ∈ windowHits H j (1/10) (W+2)}
  have hW : 1 ≤ W := one_le_pow₀ (by norm_num)
  obtain ⟨t,ht⟩ := exists_records H s ⟨_,hx⟩ a
  change records H s (zeroGateArcTolerance (physicalArc (1/10))) a t at ht
  rw [htol] at ht
  refine ⟨t,ht,?_⟩
  have hstep := hs s (1/10)
  rw [show (1/10:ℝ)+1/1000=101/1000 by norm_num] at hstep
  have hpay : s+N^4 ≤ J := (Nat.add_le_add_right hsj _).trans hbud
  have sweep (r : ℝ) (hr : r ∈ visitSet H s (1/10)) (hmark : r ∈ B) : Ioc (r-1) r ⊆ S := by
    intro u hu
    have hwin : u ∈ windowHits H s (1/10) 1 := ⟨r,⟨hu.2,by linarith only [hu.1]⟩,hr⟩
    obtain ⟨v,hv,hcheap⟩ := hmark
    exact ⟨visit_mono H _ hpay (hstep hwin),v,
      ⟨by linarith only [hu.2,hv.1],by linarith only [hu.1,hv.2]⟩,hcheap⟩
  have htime : Tendsto t atTop atTop := by
    have h (i : ℕ) : a+(i:ℝ) ≤ t i := by
      induction i with
      | zero => simp [ht.1]
      | succ i ih => rw [Nat.cast_succ]; linarith only [ih,(ht.2 i).1.1]
    exact tendsto_atTop_mono h (tendsto_atTop_add_const_left atTop a tendsto_natCast_atTop_atTop)
  filter_upwards [htime.eventually (hk (W+2) (by linarith only [hW]) a),
    htime.eventually (affordable_lower H (hω k) a),htime.eventually (eventually_gt_atTop a)]
    with n hhi hlo htna
  have hd := sub_pos.mpr htna
  have hnum : (markedReturns t B n : ℝ)/(t n-a) ≤ 4*W*(1/36:ℝ)^D :=
    (div_le_div_of_nonneg_right (markedReturns_le_volume ht B S n sweep) hd.le).trans
      (hhi.trans (mul_le_mul_of_nonneg_right (by linarith only [hW]) (by positivity)))
  have cover := (resolved_visit_occupation_bounds _ t a 1 1 zero_lt_one le_rfl ht.1 ht.2 n).1
  rw [mul_one] at cover
  have hl : (1/32:ℝ)^D ≤ (n:ℝ)/(t n-a) :=
    (hlo s).le.trans (div_le_div_of_nonneg_right cover hd.le)
  have hlp : 0 < (1/32:ℝ)^D := by positivity
  rw [←div_div_div_cancel_right₀ hd.ne']
  apply (div_le_div_of_nonneg_right hnum (hlp.trans_le hl).le).trans
  apply (div_le_div_of_nonneg_left (by positivity) hlp hl).trans_eq
  dsimp only [W]
  rw [mul_assoc,←mul_pow,mul_div_assoc,←div_pow]
  norm_num

#print axioms gaussian_counted_return_rebound
end
end GaloisForLFunctions.HTGeometry.HarmonicRuns
