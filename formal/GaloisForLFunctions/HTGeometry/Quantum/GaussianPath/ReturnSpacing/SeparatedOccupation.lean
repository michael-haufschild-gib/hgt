import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.AffordableAnnulus
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance

/-! # Sharp occupation of intervals of intermediate gate cost -/
open MeasureTheory Filter Set Topology
open scoped Pointwise Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing
noncomputable section
open SharpOccupation
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- Centers of intervals with a physical-error upper budget and a uniform
3/20 lower separation from all budgets strictly below l. -/
def intermediateCenters {N : ℕ} (H : selfAdjoint (Reg N)) (l : ℝ) (J : ℕ) (W : ℝ) : Set ℝ :=
  ⋂ h : Icc (-W) W, {t | orbitCircuitDistance H J (t+h.val) ≤ 1/10} ∩
    ⋂ s : {s : ℕ // (s:ℝ)<l}, {t | 3/20 ≤ orbitCircuitDistance H s.val (t+h.val)}

private theorem closed_visits {N : ℕ} (H : selfAdjoint (Reg N)) (j : ℕ) (η : ℝ) :
    IsClosed (visitSet H j η) := by
  have he : visitSet H j η={t | orbitCircuitDistance H j t ≤ η} := by
    ext t
    exact hasProjectiveCircuitApproximation_iff_infDist _ j η
  rw [he]
  exact isClosed_le (orbitCircuitDistance_lipschitz H j).continuous continuous_const

/-- Both distance inequalities are closed, including after imposing them at
every lag and every low budget. -/
theorem isClosed_intermediateCenters {N : ℕ} (H : selfAdjoint (Reg N)) (l : ℝ) (J : ℕ) (W : ℝ) :
    IsClosed (intermediateCenters H l J W) := by
  have h (s : ℕ) (u : ℝ) : Continuous (fun t => orbitCircuitDistance H s (t+u)) :=
    (orbitCircuitDistance_lipschitz H s).continuous.comp (continuous_id.add continuous_const)
  exact isClosed_iInter fun y => (isClosed_le (h J y) continuous_const).inter
    (isClosed_iInter fun s => isClosed_le continuous_const (h s.val y))

theorem mem_intermediateCenters {N : ℕ} (H : selfAdjoint (Reg N)) (l : ℝ) (J : ℕ) (W t : ℝ) :
    t∈intermediateCenters H l J W ↔ ∀ u : ℝ, |u-t| ≤ W →
      u∈visitSet H J (1/10) ∧ ∀ s : ℕ, (s:ℝ)<l → 3/20 ≤ orbitCircuitDistance H s u := by
  constructor
  · intro ht u hu
    have he := mem_iInter.mp ht (⟨u-t,abs_le.mp hu⟩ : Icc (-W) W)
    have h₁ : orbitCircuitDistance H J (t+(u-t)) ≤ 1/10 := he.1
    have h₂ (s : ℕ) (hs : (s:ℝ)<l) : 3/20 ≤ orbitCircuitDistance H s (t+(u-t)) :=
      mem_iInter.mp he.2 (⟨s,hs⟩ : {s : ℕ // (s:ℝ)<l})
    have heq : t+(u-t)=u := by ring
    rw [heq] at h₁
    exact ⟨(hasProjectiveCircuitApproximation_iff_infDist _ J _).mpr h₁,
      fun s hs => by simpa only [heq] using h₂ s hs⟩
  · intro h
    apply mem_iInter.mpr
    intro y
    have hh := h (t+y) (by rw [show t+y.val-t=y.val by ring,abs_le]; exact y.property)
    exact ⟨(hasProjectiveCircuitApproximation_iff_infDist _ J _).mp hh.1,mem_iInter.mpr fun s => hh.2 s.val s.property⟩

/-- Both offsets of size R/2 from a sufficiently deep scalar visit are centers
of closed cost bands of radius R/8. -/
theorem gaussian_deep_visit_centers :
    ∃ c : ℝ, ∃ J : ℕ, 0<c ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
      let R := (N:ℝ)^((48:ℝ)⁻¹)/4
      ∀ v η : ℝ, η+1/(N:ℝ) ≤ 1/10 → v∈visitSet H 0 η →
        ∀ d : ℝ, |d|=R/2 → v+d∈intermediateCenters H (c*Real.sqrt N) (J*N^2) (R/8) := by
  obtain ⟨c,J,hc,hh⟩ := gaussian_affordable_intervals_separated_from_low_visits
  refine ⟨c,J,hc,?_⟩
  filter_upwards [hh] with ω hω
  filter_upwards [hω] with n ha
  intro N H R v η hη hv d hd
  apply (mem_intermediateCenters _ _ _ _ _).mpr
  intro u hdist
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have h₁ := abs_add_le (u-v) (v+d-u)
  have h₂ := abs_add_le (u-(v+d)) d
  rw [show u-v+(v+d-u)=d by ring,hd,abs_sub_comm (v+d) u] at h₁
  rw [show u-(v+d)+d=u-v by ring,hd] at h₂
  have hlo : R/3 ≤ |u-v| := by linarith only [h₁,hdist,hR]
  have hhi : |u-v| ≤ 2*R/3 := by linarith only [h₂,hdist,hR]
  have he := ha v η hη hv (u-v) hlo hhi
  rw [show v+(u-v)=u by ring] at he
  refine ⟨he.1,fun s hs => le_of_not_gt ?_⟩
  intro hnear
  have hcost := he.2 u (by rw [sub_self,abs_zero]; positivity) s
    ((hasProjectiveCircuitApproximation_iff_infDist _ s _).mpr hnear.le)
  exact hs.not_ge hcost

/-- A translation of visit times gives the same finite-window fraction after
translating both observation dates. -/
private theorem shift_fraction_le {N : ℕ} (H : selfAdjoint (Reg N)) (η d a T : ℝ)
    (hT : a ≤ T) {S : Set ℝ} (hs : ∀ v ∈ visitSet H 0 η, v+d∈S) :
    visitFraction H 0 η (a-d) (T-d) ≤ volume.real (S∩Icc a T)/(T-a) := by
  rw [visitFraction,show T-d-(a-d)=T-a by ring]
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hT)
  let V := visitSet H 0 η ∩ Icc (a-d) (T-d)
  have hm : MeasurableSet V := (closed_visits H 0 η).measurableSet.inter measurableSet_Icc
  have he := (measurePreserving_sub_right volume d).measureReal_preimage hm.nullMeasurableSet
  change volume.real V ≤ _
  rw [←he]
  apply measureReal_mono _ (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  intro t ht
  change t-d∈V at ht
  exact ⟨by simpa only [sub_add_cancel] using hs (t-d) ht.1,
    by constructor <;> linarith only [ht.2.1,ht.2.2]⟩

/-- Requiring a full interval of radius N^(1/48)/32 to have gate cost between
c√N and JN² preserves the leading occupation exponent at error 1/10. -/
theorem gaussian_intermediate_interval_rate :
    ∃ c : ℝ, ∃ J : ℕ, 0<c ∧ ∀ᵐ ω ∂pathPauliDisorderLaw,
      ∀ l b : ℝ, 0<l → l<physicalArc (1/10) → physicalArc (1/10)<b →
      ∀ᶠ k : ℕ in atTop, let N := k+3
                          let D := 2^N
                          let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
                            isSelfAdjoint_pathHamiltonian _⟩
                          let W := (N:ℝ)^((48:ℝ)⁻¹)/32
                          let S := intermediateCenters H (c*Real.sqrt N) (J*N^2) W
                          ∀ a : ℝ, ∀ᶠ T : ℝ in atTop, l^D < volume.real (S∩Icc a T)/(T-a) ∧
                            volume.real (S∩Icc a T)/(T-a)<b^D := by
  obtain ⟨c,J,hc,hann⟩ := gaussian_deep_visit_centers
  refine ⟨c,J,hc,?_⟩
  filter_upwards [hann,gaussian_polynomial_occupation_rate] with ω hω hrate
  intro l b hl hx hb
  let x := physicalArc (1/10)
  have hh := physicalArc_spec (by norm_num : (0:ℝ)<1/10)
    (by nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg 2] : (1/10:ℝ)<Real.sqrt 2)
  obtain ⟨z,hlz,hzx⟩ := exists_between hx
  have hz : z∈Ioo (0:ℝ) (1/2) := ⟨hl.trans hlz,hzx.trans hh.1.2⟩
  let η := zeroGateArcTolerance z
  have hη : η<1/10 := (strictMonoOn_zeroGateArcTolerance ⟨hz.1.le,hz.2.le⟩
    ⟨hh.1.1.le,hh.1.2.le⟩ hzx).trans_eq hh.2
  obtain ⟨m,hm⟩ := exists_nat_gt (1/(1/10-η))
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hω,hrate 3 x hh.1 l b hl.le hx hb,
    hrate 3 z hz l b hl.le hlz (hzx.trans hb),eventually_ge_atTop J,eventually_ge_atTop m]
    with k ha hu hd hJ hsize
  intro N D H W S a
  let R := (N:ℝ)^((48:ℝ)⁻¹)/4
  let d := R/2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hW : W=R/8 := by dsimp [W,R]; ring
  have hN : (0:ℝ)<N := by dsimp [N]; positivity
  have hsmall : η+1/(N:ℝ) ≤ 1/10 := by
    have hmn : (m:ℝ) ≤ N := by exact_mod_cast (show m ≤ N by dsimp [N]; omega)
    have h := (div_lt_iff₀ (sub_pos.mpr hη)).mp (hm.trans_le hmn)
    exact (le_sub_iff_add_le').mp ((div_le_iff₀ hN).mpr (by linarith only [h,mul_comm (N:ℝ) (1/10-η)]))
  have hsub (v : ℝ) (hv : v∈visitSet H 0 η) : v+d∈S := by
    change v+d∈intermediateCenters H _ _ W
    rw [hW]
    exact ha v η hsmall hv d (abs_of_nonneg (div_nonneg hR (by norm_num)))
  have hj : J*N^2 ≤ N^3 := by
    rw [pow_succ]
    exact (Nat.mul_le_mul_right _ (hJ.trans (Nat.le_add_right k 3))).trans_eq (Nat.mul_comm _ _)
  have hshift : Tendsto (fun T : ℝ => T-d) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using (tendsto_atTop_add_const_right atTop (-d) (tendsto_id (α:=ℝ)))
  filter_upwards [hu a,hshift.eventually (hd (a-d)),eventually_gt_atTop a] with T hupper hlower hT
  refine ⟨(hlower 0 (Nat.zero_le _)).1.trans_le (shift_fraction_le H η d a T hT.le hsub),?_⟩
  have hupp := (hupper (J*N^2) hj).2
  rw [hh.2] at hupp
  apply lt_of_le_of_lt _ hupp
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hT.le)
  apply measureReal_mono _ (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  exact inter_subset_inter_left _ fun t ht => ((mem_intermediateCenters _ _ _ _ _).mp ht t
    (by rw [sub_self,abs_zero,hW]; positivity)).1

#print axioms gaussian_intermediate_interval_rate
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing
