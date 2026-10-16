import GaloisForLFunctions.RHTower.CHMDStationaryGenerators

/-!
# The stationary theta pullback has no zero mode

Zero stationary jump energy forces theta times the source to be constant.
That product belongs to ordinary Lebesgue L2, so the constant is zero. This
proves strict positivity on every nonzero operator-domain vector, without
asserting a uniform spectral gap.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDPolar

theorem stationaryGround_edge_zero_iff (p : stationaryGroundGraph) :
    p.val.snd = 0 ↔ p = 0 := by
  constructor
  · intro hp
    have he : ∀ᵐ e ∂stationaryMeasure,
        thetaProduct p.val.fst (left e) = thetaProduct p.val.fst (right e) := by
      filter_upwards [p.property, Lp.coeFn_zero ℝ 2 stationaryMeasure] with e he hz
      rw [hp, hz] at he
      exact sub_eq_zero.mp he.symm
    have hb : ∀ᵐ e ∂archBase,
        thetaProduct p.val.fst (left e) = thetaProduct p.val.fst (right e) := by
      change ∀ᵐ e ∂archBase.withDensity (fun e => ENNReal.ofReal (archLevyDensity e.1)),
        thetaProduct p.val.fst (left e) = thetaProduct p.val.fst (right e) at he
      rw [ae_withDensity_iff (show Measurable
        (fun e : ℝ × ℝ => ENNReal.ofReal (archLevyDensity e.1)) from
          (measurable_archLevyDensity.comp measurable_fst).ennreal_ofReal)] at he
      have ht : ∀ᵐ e ∂archBase, 0 < e.1 :=
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
      filter_upwards [he, ht] with e he ht
      exact he (ENNReal.ofReal_pos.mpr (archLevyDensity_pos ht)).ne'
    have ha : ∀ᵐ e ∂archMeasure,
        thetaProduct p.val.fst (left e) = thetaProduct p.val.fst (right e) :=
      hb.filter_mono (withDensity_absolutelyContinuous archBase
        (fun e => ENNReal.ofReal (archWeight e))).ae_le
    have hm := (Lp.stronglyMeasurable p.val.fst).measurable
    obtain ⟨c, hc⟩ := constant_of_arch_zero (thetaProduct p.val.fst) (measurable_thetaProduct hm) ha
    have hc2 : MemLp (fun _ : ℝ => c) 2 volume :=
      (memLp_thetaProduct hm (Lp.memLp p.val.fst)).ae_eq hc
    have hc0 : c = 0 := by
      have h := (memLp_const_iff (by norm_num : (2 : ENNReal) ≠ 0)
        (by norm_num : (2 : ENNReal) ≠ ⊤)).mp hc2
      simpa [Real.volume_univ] using h
    subst c
    apply stationaryGroundSourceMap_injective
    rw [map_zero]
    apply Lp.ext
    have hz := (withDensity_absolutelyContinuous volume
      (fun x => ENNReal.ofReal (massDensity x))).ae_eq hc
    filter_upwards [hz, Lp.coeFn_zero ℝ 2 massMeasure] with x hx hx0
    change p.val.fst x = (0 : Lp ℝ 2 massMeasure) x
    rw [hx0]
    change riemannKernelReal x * p.val.fst x = 0 at hx
    exact (mul_eq_zero.mp hx).resolve_left (riemannKernelReal_pos x).ne'
  · rintro rfl
    rfl

/-- Strict quadratic positivity; no uniform lower bound is introduced. -/
theorem stationaryGenerator_strictly_positive (u : stationaryGenerator.domain)
    (hu : (u : MassSpace) ≠ 0) : 0 < ⟪stationaryGenerator u, (u : MassSpace)⟫_ℝ := by
  rcases u with ⟨u, hu'⟩
  obtain ⟨w, rfl⟩ := hu'
  have hp : stationaryRieszLift w ≠ 0 := by
    intro hp
    apply hu
    change stationaryGroundSourceMap (stationaryRieszLift w) = 0
    rw [hp, map_zero]
  have he : (stationaryRieszLift w).val.snd ≠ 0 :=
    fun h => hp ((stationaryGround_edge_zero_iff _).mp h)
  have h := stationaryGenerator_form w (stationaryRieszLift w)
  change ⟪stationaryGenerator ⟨stationaryResolvent w, _⟩, stationaryResolvent w⟫_ℝ = _ at h
  erw [h, real_inner_self_eq_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr he)

theorem stationaryGenerator_zero_iff (u : stationaryGenerator.domain) :
    stationaryGenerator u = 0 ↔ (u : MassSpace) = 0 := by
  constructor
  · intro h
    by_contra hu
    have hp := stationaryGenerator_strictly_positive u hu
    rw [h, inner_zero_left] at hp
    exact (lt_irrefl 0) hp
  · intro h
    have hu : u = 0 := Subtype.ext h
    subst u
    exact map_zero stationaryGenerator.toFun

end RHTower.CHMDDoobGraph
