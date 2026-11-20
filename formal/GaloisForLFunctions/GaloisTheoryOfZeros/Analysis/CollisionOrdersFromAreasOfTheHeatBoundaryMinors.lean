import GaloisForLFunctions.GaloisTheoryOfZeros.Analysis.ThreeBoundaryMomentsDetectEveryHeatCollision
import GaloisForLFunctions.ExceptionalLayerTheory.TheHighDerivativeAreasOfAWholeObservationDisk

/-!
# Collision orders from the areas of heat boundary minors

The size-q determinant of spatial contour moments, viewed in physical time,
has order q choose 2 when 2 ≤ q ≤ m, where m is the spatial order. Larger
minors vanish throughout a neighborhood. The time-plane areas of their
large logarithmic derivatives thus give threshold tests for every collision
order. The size-two minor alone has the same unit signal at all collisions.
-/

noncomputable section
open Complex Filter Topology Metric RHTower RHTower.DeBruijn
open scoped Classical
open GaloisForLFunctions.ExceptionalLayerTheory
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- Area measured in a time disk from one minor of spatial contour moments. -/
def heatMinorArea (τ z : ℂ) (d : ℝ) (q j : ℕ) (s u : ℝ) : ℝ :=
  logDerivativeDiskArea (fun w => localHeatMomentMinor z d q (τ+w)) j 0 s u

/-- At every sufficiently small spatial width, the area at every order j
and minor size q ≥ 2 separates spatial multiplicities below q from those
at least q. The former give an identically empty high-level region. -/
theorem IsCollision.contour_minor_area_laws {τ z : ℂ} {m : ℕ} (hc : IsCollision τ z m) :
    ∀ᶠ d in 𝓝[>] (0:ℝ), ∀ q : ℕ, 2≤q → ∀ j : ℕ,
      ∃ r : ℝ, 0<r ∧ ∀ s : ℝ, 0<s → s≤r →
        Tendsto (heatMinorArea τ z d q j s) atTop
          (𝓝 (if q ≤ m then (q.choose 2:ℝ)^(2/((j+1:ℕ):ℝ)) else 0)) := by
  filter_upwards [hc.contourMinor_orders] with d hd q hq j
  let F := fun w : ℂ => localHeatMomentMinor z d q (τ+w)
  by_cases hm : q ≤ m
  · have hord := (hd q).1 hm
    have ha : AnalyticAt ℂ F 0 := by
      by_contra hn
      have he : (q.choose 2:ℕ∞)=0 := hord.symm.trans (analyticOrderAt_of_not_analyticAt hn)
      exact (Nat.choose_pos hq).ne' (by exact_mod_cast he)
    have hn : analyticOrderAt F 0≠⊤ := by rw [show analyticOrderAt F 0=_ from hord]; exact ENat.coe_ne_top _
    obtain ⟨r,hr,h⟩ := analytic_germ_derivative_disk_area ha hn j
    refine ⟨r,hr,fun s hs hsr => ?_⟩
    rw [if_pos hm]
    simpa only [hord,ENat.toNat_coe] using h s hs hsr
  · obtain ⟨r,hr,he⟩ := zero_germ_derivative_disk_area ((hd q).2 (lt_of_not_ge hm)) j
    refine ⟨r,hr,fun s _ hs => ?_⟩
    rw [if_neg hm]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
    exact (he s hs u hu).symm

/-- Any derivative order of the three-moment minor gives the same unit
limiting area at a multiple zero, and zero at every other marked place. -/
theorem heat_three_moment_area_at_place (τ z : ℂ) :
    ∀ᶠ d in 𝓝[>] (0:ℝ), ∀ j : ℕ, ∃ r : ℝ, 0<r ∧ ∀ s : ℝ, 0<s → s≤r →
      Tendsto (heatMinorArea τ z d 2 j s) atTop
        (𝓝 (if (τ,z) ∈ multipleZeros then (1:ℝ) else 0)) := by
  classical
  let m := analyticOrderNatAt (complexHeat τ) z
  have hc : IsCollision τ z m := isCollision_iff_analyticOrderAt.mpr
    (Nat.cast_analyticOrderNatAt (analyticOrderAt_complexHeat_ne_top τ z)).symm
  have hm : (τ,z) ∈ multipleZeros ↔ 2 ≤ m := by
    rw [←heatIntersectionMultiplicity_ne_zero_iff,hc.heatIntersectionMultiplicity_eq,Nat.choose_ne_zero_iff]
  filter_upwards [hc.contour_minor_area_laws] with d hd j
  simpa only [hm,Nat.choose_self,Nat.cast_one,Real.one_rpow] using hd 2 le_rfl j

/-- RH is equivalent to vanishing of the three-moment area signal at
every positive real time. A single fixed derivative order suffices.
Arbitrarily small spatial squares and time disks give the same test. -/
theorem rh_iff_vanishing_three_moment_areas (j : ℕ) :
    RiemannHypothesis ↔ ∀ t : ℝ, 0<t → ∀ z : ℂ, ∃ᶠ d in 𝓝[>] (0:ℝ),
      ∃ᶠ s in 𝓝[>] (0:ℝ), Tendsto (heatMinorArea t z d 2 j s) atTop (𝓝 0) := by
  classical
  rw [riemannHypothesis_iff_forall_pos_not_mem_branchTimes]
  constructor
  · intro h t ht z
    have hn : ((t:ℂ),z) ∉ multipleZeros := fun hp => h t ht ⟨_,hp,rfl⟩
    apply Filter.Eventually.frequently
    filter_upwards [heat_three_moment_area_at_place (t:ℂ) z] with d hd
    obtain ⟨r,hr,hs⟩ := hd j
    apply Filter.Eventually.frequently
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds]
      with s hpos hsr
    simpa only [if_neg hn] using hs s hpos hsr.le
  · rintro H t ht ⟨⟨τ,z⟩,hp,he⟩
    change τ=(t:ℂ) at he
    subst τ
    obtain ⟨d,hd,hzero⟩ := ((H t ht z).and_eventually
      (heat_three_moment_area_at_place (t:ℂ) z)).exists
    obtain ⟨r,hr,hs⟩ := hzero j
    have hsmall : ∀ᶠ s in 𝓝[>] (0:ℝ), 0<s ∧ s<r :=
      eventually_mem_nhdsWithin.and ((eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds)
    obtain ⟨s,hs0,hpos,hsr⟩ := (hd.and_eventually hsmall).exists
    have h₁ := hs s hpos hsr.le
    rw [if_pos hp] at h₁
    exact zero_ne_one (tendsto_nhds_unique hs0 h₁)

#print axioms IsCollision.contour_minor_area_laws
#print axioms heat_three_moment_area_at_place
#print axioms rh_iff_vanishing_three_moment_areas
end GaloisForLFunctions.GaloisTheoryOfZeros
