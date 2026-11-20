import GaloisForLFunctions.GaloisTheoryOfZeros.Analysis.MultiplicityStrataOfTheHeatWinding
import GaloisForLFunctions.ExceptionalLayerTheory.TheHighDerivativeAreasOfAWholeObservationDisk
import GaloisForLFunctions.RHTower.CarrierBoxCount
import Mathlib.Data.Nat.Choose.Cast

/-!
# Area excess at simultaneous heat collisions

On projecting a real-time heat box to its time coordinate, all spatial
collision multiplicities at one time add before their contribution to an
area moment is taken. Reflection makes every projected mass even. If
those masses are 2k, the quadratic time-area exceeds twice the winding
by eight times the sum of k choose 2. The first nonempty box has limiting
quadratic area at least four.
-/

noncomputable section
open Complex Filter Metric Set Topology RHTower
open GaloisForLFunctions.ExceptionalLayerTheory
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
open scoped Classical
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- Sum of the spatial intersection multiplicities above one time. -/
def projectedTimeMass (C : Finset (ℂ × ℂ)) (τ : ℂ) :=
  ∑ p ∈ C with p.1=τ, heatIntersectionMultiplicity p

private theorem projected_analytic (C : Finset (ℂ × ℂ)) (τ : ℂ) :
    AnalyticAt ℂ (projectedHeatDiscriminant C) τ :=
  Finset.analyticAt_fun_prod C (fun p _ => (analyticAt_id.sub analyticAt_const).pow (heatIntersectionMultiplicity p))

theorem projected_order_at_time (C : Finset (ℂ × ℂ)) (τ : ℂ) :
    analyticOrderAt (projectedHeatDiscriminant C) τ=(projectedTimeMass C τ:ℕ∞) := by
  have hlin : analyticOrderAt (fun z : ℂ => z-τ) τ=1 := by
    have h : AnalyticAt ℂ (fun z : ℂ => z-τ) τ := analyticAt_id.sub analyticAt_const
    have he := h.analyticOrderAt_eq_natCast (n:=1)
    rw [Nat.cast_one] at he
    exact he.mpr ⟨fun _ => 1,analyticAt_const,one_ne_zero,Eventually.of_forall fun z => by simp⟩
  let f (p : ℂ × ℂ) := (fun z : ℂ => z-p.1)^heatIntersectionMultiplicity p
  have hf : projectedHeatDiscriminant C=∏ p ∈ C, f p := by funext z; rw [Finset.prod_apply]; rfl
  have ha (p : ℂ × ℂ) (_ : p∈C) : AnalyticAt ℂ (f p) τ :=
    (analyticAt_id.sub analyticAt_const).pow _
  rw [hf,analyticOrderAt_finset_prod C f τ ha,projectedTimeMass,Finset.sum_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [show f p=(fun z : ℂ => z-p.1)^heatIntersectionMultiplicity p from rfl,
    analyticOrderAt_pow (analyticAt_id.sub analyticAt_const)]
  by_cases he : p.1=τ
  · rw [if_pos he,he,hlin,nsmul_eq_mul,mul_one]
  · have hz : analyticOrderAt (fun z : ℂ => z-p.1) τ=0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (sub_ne_zero.mpr he.symm))
    rw [if_neg he,hz,nsmul_zero,Nat.cast_zero]

/-- A single time-plane disk reads the entire projected divisor of the
real-time box. Each simultaneous collection contributes a power of its
combined multiplicity. -/
theorem projected_heat_area_moments (r : ℝ) (hr : 0<r) (j : ℕ) :
    let C := heatBoxSites r
    Tendsto (logDerivativeDiskArea (projectedHeatDiscriminant C) j 0 (r+1)) atTop
      (𝓝 (∑ τ ∈ C.image Prod.fst, (projectedTimeMass C τ:ℝ)^(2/((j+1:ℕ):ℝ)))) := by
  let C := heatBoxSites r
  have ht (τ : ℂ) (hτ : τ∈C.image Prod.fst) : τ∈ball 0 (r+1) := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hτ
    obtain ⟨t,ht,he⟩ := (mem_heatBoxSites.mp hp).1.1
    rw [←he,mem_ball_zero_iff,Complex.norm_real,Real.norm_of_nonneg ((one_div_pos.mpr hr).le.trans ht.1)]
    exact ht.2.trans_lt (lt_add_one r)
  have h := analytic_disk_fractional_moment (projectedHeatDiscriminant C) (projected_analytic C)
    (fun τ => by rw [projected_order_at_time]; exact ENat.coe_ne_top _) j 0 (r+1)
    (C.image Prod.fst) ht (fun z _ hz => Finset.prod_ne_zero_iff.mpr fun p hp =>
      pow_ne_zero _ (sub_ne_zero.mpr (fun he => hz (by rw [he]; exact Finset.mem_image_of_mem Prod.fst hp))))
  simpa only [projected_order_at_time,ENat.toNat_coe] using h

/-- At each individual time, real pairs contribute twice their mass and
nonreal quartets four times theirs, even if different orbits collide together. -/
theorem projected_heat_mass_by_orbit (r : ℝ) (τ : ℂ) :
    projectedTimeMass (heatBoxSites r) τ =
      2*(projectedTimeMass (heatRealPairs r) τ + 2*projectedTimeMass (heatNonrealQuartets r) τ) := by
  have hreal {S : Finset (ℂ × ℂ)} (hs : S ⊆ heatBoxSites r) (t : ℂ) :
      heatTimeProduct S (fun a : ℝ => t-a) = projectedHeatDiscriminant S t := by
    apply Finset.prod_congr rfl
    intro p hp
    obtain ⟨a,_,he⟩ := (mem_heatBoxSites.mp (hs hp)).1.1
    simp only [←he,Complex.ofReal_re]
  have hsubR : heatRealPairs r ⊆ heatBoxSites r :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hsubQ : heatNonrealQuartets r ⊆ heatBoxSites r :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have he : projectedHeatDiscriminant (heatBoxSites r) =
      (projectedHeatDiscriminant (heatRealPairs r) * projectedHeatDiscriminant (heatNonrealQuartets r)^2)^2 := by
    funext t
    simpa only [Pi.pow_apply,Pi.mul_apply,hreal hsubR,hreal hsubQ] using projectedHeatDiscriminant_realBox r t
  have h := congrArg (fun f : ℂ → ℂ => analyticOrderAt f τ) he
  have hR := projected_analytic (heatRealPairs r) τ
  have hQ := projected_analytic (heatNonrealQuartets r) τ
  change analyticOrderAt _ τ = analyticOrderAt _ τ at h
  rw [analyticOrderAt_pow (hR.mul (hQ.pow 2)),analyticOrderAt_mul hR (hQ.pow 2),
    analyticOrderAt_pow hQ] at h
  simp only [projected_order_at_time,two_smul] at h
  simp only [two_mul]
  exact_mod_cast h

theorem projected_real_heat_mass_even (r : ℝ) (τ : ℂ) : Even (projectedTimeMass (heatBoxSites r) τ) :=
  ⟨_,(projected_heat_mass_by_orbit r τ).trans (two_mul _)⟩

private theorem time_slice_card_le_mass {r : ℝ} {S : Finset (ℂ × ℂ)}
    (hs : S ⊆ heatBoxSites r) (τ : ℂ) :
    (S.filter (·.1=τ)).card ≤ projectedTimeMass S τ := by
  calc
    _ = ∑ _p ∈ S.filter (·.1=τ), 1 := by simp
    _ ≤ _ := Finset.sum_le_sum fun p hp => Nat.one_le_iff_ne_zero.mpr
      ((heatIntersectionMultiplicity_ne_zero_iff p).mpr (mem_heatBoxSites.mp (hs (Finset.mem_filter.mp hp).1)).2)

/-- Mass two at a given time identifies exactly one reflected real pair
of double zeros, with no nonreal quartet at that time in the box. -/
theorem minimum_projected_heat_mass_iff (r : ℝ) (τ : ℂ) :
    projectedTimeMass (heatBoxSites r) τ=2 ↔
      ((heatNonrealQuartets r).filter (·.1=τ))=∅ ∧
        ∃ p, ((heatRealPairs r).filter (·.1=τ))={p} ∧ heatSpatialOrder p=2 := by
  let R := (heatRealPairs r).filter (·.1=τ)
  let Q := (heatNonrealQuartets r).filter (·.1=τ)
  have h := projected_heat_mass_by_orbit r τ
  constructor
  · intro htwo
    have hr : projectedTimeMass (heatRealPairs r) τ=1 := by omega
    have hq : projectedTimeMass (heatNonrealQuartets r) τ=0 := by omega
    have hcR : R.card≤1 := (time_slice_card_le_mass (S:=heatRealPairs r)
      ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _)) τ).trans_eq hr
    have hcQ : Q.card≤0 := (time_slice_card_le_mass (S:=heatNonrealQuartets r)
      ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _)) τ).trans_eq hq
    refine ⟨Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcQ),?_⟩
    have hn : R≠∅ := by
      intro hR
      change ∑ p ∈ R, heatIntersectionMultiplicity p = 1 at hr
      simp [hR] at hr
    obtain ⟨p,hp⟩ := Finset.card_eq_one.mp (le_antisymm hcR (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hn)))
    refine ⟨p,hp,?_⟩
    change ∑ p ∈ R, heatIntersectionMultiplicity p = 1 at hr
    rw [hp,Finset.sum_singleton] at hr
    change (heatSpatialOrder p).choose 2=1 at hr
    have hlow : 2≤heatSpatialOrder p := Nat.choose_ne_zero_iff.mp (hr.trans_ne one_ne_zero)
    by_contra he
    have hh := Nat.choose_le_choose 2 (by omega : 3≤heatSpatialOrder p)
    rw [hr] at hh
    norm_num [Nat.choose] at hh
  · rintro ⟨hQ,p,hR,hp⟩
    have hm : heatIntersectionMultiplicity p=1 := by
      change (heatSpatialOrder p).choose 2=1
      rw [hp,Nat.choose_self]
    simpa only [projectedTimeMass,hQ,hR,Finset.sum_singleton,Finset.sum_empty,hm,
      mul_zero,add_zero,mul_one] using h

private theorem projected_winding (r : ℝ) :
    ∑ τ ∈ (heatBoxSites r).image Prod.fst, projectedTimeMass (heatBoxSites r) τ=heatBoxWinding r := by
  exact Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem Prod.fst hp) _

private theorem time_mass_pos {r : ℝ} {τ : ℂ} (hτ : τ∈(heatBoxSites r).image Prod.fst) :
    0<projectedTimeMass (heatBoxSites r) τ := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hτ
  have hpos := Nat.pos_of_ne_zero ((heatIntersectionMultiplicity_ne_zero_iff p).mpr
    (mem_heatBoxSites.mp hp).2)
  exact hpos.trans_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_filter.mpr ⟨hp,rfl⟩))

/-- The quadratic area excess over twice the winding counts coincident
pairs of projected half-masses, each with coefficient eight. -/
theorem projected_heat_area_excess (r : ℝ) (hr : 0<r) :
    let C := heatBoxSites r
    Tendsto (fun u => logDerivativeDiskArea (projectedHeatDiscriminant C) 0 0 (r+1) u-
      2*(heatBoxWinding r:ℝ)) atTop
        (𝓝 (8*∑ τ ∈ C.image Prod.fst, (((projectedTimeMass C τ/2).choose 2):ℝ))) := by
  let C := heatBoxSites r
  have h := projected_heat_area_moments r hr 0
  norm_num only [Nat.zero_add,Nat.cast_one,div_one,Real.rpow_two] at h
  have he : (∑ τ ∈ C.image Prod.fst, (projectedTimeMass C τ:ℝ)^2)-2*(heatBoxWinding r:ℝ)=
      8*∑ τ ∈ C.image Prod.fst, (((projectedTimeMass C τ/2).choose 2):ℝ) := by
    rw [←projected_winding,Nat.cast_sum,Finset.mul_sum,←Finset.sum_sub_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ _
    obtain ⟨k,hk⟩ := projected_real_heat_mass_even r τ
    have hm : projectedTimeMass C τ=2*k := by simpa only [two_mul] using hk
    rw [hm,show 2*k/2=k by omega,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_choose_two]
    ring
  exact he ▸ h.sub_const (2*(heatBoxWinding r:ℝ))

/-- An observed excess strictly below eight certifies that every
occupied time contains exactly one real double pair. -/
theorem projected_excess_below_eight_iff (r : ℝ) (hr : 0<r) :
    (∃ b : ℝ, b<8 ∧ Tendsto (fun u =>
      logDerivativeDiskArea (projectedHeatDiscriminant (heatBoxSites r)) 0 0 (r+1) u-
        2*(heatBoxWinding r:ℝ)) atTop (𝓝 b)) ↔
    ∀ τ ∈ (heatBoxSites r).image Prod.fst,
      ((heatNonrealQuartets r).filter (·.1=τ))=∅ ∧
        ∃ p, ((heatRealPairs r).filter (·.1=τ))={p} ∧ heatSpatialOrder p=2 := by
  let C := heatBoxSites r
  let E := ∑ τ ∈ C.image Prod.fst, (projectedTimeMass C τ/2).choose 2
  have h := projected_heat_area_excess r hr
  change Tendsto _ _ (𝓝 (8*∑ τ ∈ C.image Prod.fst, (((projectedTimeMass C τ/2).choose 2):ℝ))) at h
  rw [←Nat.cast_sum] at h
  change Tendsto _ _ (𝓝 (8*(E:ℝ))) at h
  constructor
  · rintro ⟨b,hb,hb'⟩ τ hτ
    have he : 8*(E:ℝ)=b := tendsto_nhds_unique h hb'
    have hsmall : (E:ℝ)<1 := by linarith only [he,hb]
    have he0 : E=0 := Nat.lt_one_iff.mp (by exact_mod_cast hsmall)
    have hl : (projectedTimeMass C τ/2).choose 2 ≤ E :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hτ
    have hk := Nat.choose_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (hl.trans_eq he0))
    have hpos := time_mass_pos hτ
    obtain ⟨k,hk₂⟩ := projected_real_heat_mass_even r τ
    apply (minimum_projected_heat_mass_iff r τ).mp
    change projectedTimeMass C τ = k+k at hk₂
    change 0<projectedTimeMass C τ at hpos
    change projectedTimeMass C τ=2
    omega
  · intro H
    have hE : E=0 := Finset.sum_eq_zero fun τ hτ => by
      rw [(minimum_projected_heat_mass_iff r τ).mpr (H τ hτ)]
      decide
    exact ⟨0,by norm_num,by simpa only [hE,Nat.cast_zero,mul_zero] using h⟩

/-- The first possible nonzero normalized quadratic area is at least
four. Staying strictly below four on every positive box is equivalent
to absence of positive-real-time collisions. -/
theorem rh_iff_projected_heat_area_below_four :
    RiemannHypothesis ↔ ∀ r : ℝ, 0<r → ∃ b : ℝ, b<4 ∧
      Tendsto (logDerivativeDiskArea (projectedHeatDiscriminant (heatBoxSites r)) 0 0 (r+1))
        atTop (𝓝 b) := by
  constructor
  · intro h r hr
    have hempty : heatBoxSites r=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨⟨⟨t,ht,he⟩,_⟩,hcol⟩ := mem_heatBoxSites.mp hp
      exact riemannHypothesis_iff_forall_pos_not_mem_branchTimes.mp h t
        ((one_div_pos.mpr hr).trans_le ht.1) ⟨p,hcol,he.symm⟩
    refine ⟨0,by norm_num,?_⟩
    simpa only [hempty,Finset.image_empty,Finset.sum_empty] using projected_heat_area_moments r hr 0
  · intro H
    apply heatBoxWinding_le_one_iff_rh.mp
    intro r hr
    obtain ⟨b,hb,hl⟩ := H r hr
    have he := tendsto_nhds_unique (projected_heat_area_moments r hr 0) hl
    norm_num only [Nat.zero_add,Nat.cast_one,div_one,Real.rpow_two] at he
    have hnone : heatBoxSites r=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have ht := Finset.mem_image_of_mem Prod.fst hp
      have hpos := time_mass_pos ht
      obtain ⟨k,hk⟩ := projected_real_heat_mass_even r p.1
      have htwo : 2≤projectedTimeMass (heatBoxSites r) p.1 := by omega
      have hfour : (4:ℝ)≤(projectedTimeMass (heatBoxSites r) p.1:ℝ)^2 := by
        have hreal : (2:ℝ)≤projectedTimeMass (heatBoxSites r) p.1 := by exact_mod_cast htwo
        simpa only [show (2:ℝ)^2=4 by norm_num] using pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) hreal 2
      exact hb.not_ge (hfour.trans ((Finset.single_le_sum
        (fun τ (_ : τ∈(heatBoxSites r).image Prod.fst) => sq_nonneg (projectedTimeMass (heatBoxSites r) τ:ℝ)) ht).trans_eq he))
    simp [heatBoxWinding,hnone]

#print axioms projected_order_at_time
#print axioms projected_heat_area_moments
#print axioms projected_heat_mass_by_orbit
#print axioms minimum_projected_heat_mass_iff
#print axioms projected_real_heat_mass_even
#print axioms projected_heat_area_excess
#print axioms projected_excess_below_eight_iff
#print axioms rh_iff_projected_heat_area_below_four
end GaloisForLFunctions.GaloisTheoryOfZeros
