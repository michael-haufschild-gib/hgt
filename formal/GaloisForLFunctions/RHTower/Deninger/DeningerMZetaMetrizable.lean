import GaloisForLFunctions.RHTower.Deninger.DeningerFrechetProperties

/-!
# The cokernel of the Poisson operator is metrizable

The radial space is metrizable, hence first countable, and a quotient of a first countable
topological group is first countable because the projection is open.  The left uniformity of a
topological group is the pullback of the neighbourhood filter of zero, so it is countably generated,
and a separated uniform space with countably generated uniformity is metrizable.

With completeness and nuclearity this finishes the assertion that the cokernel of the Poisson
operator is a nuclear Fréchet space.

* `deningerMZeta_firstCountable` : the cokernel is first countable.
* `deningerMZeta_metrizableSpace` : **the cokernel is metrizable.**
-/

open Filter TopologicalSpace
open scoped Topology Uniformity

noncomputable section

namespace RHTower

instance deningerMZeta_firstCountable : FirstCountableTopology DeningerMZeta := by
  haveI : FirstCountableTopology deningerRadialCompat := inferInstance
  have hcont : Continuous (deningerMZetaMk) := continuous_quot_mk
  refine ⟨fun x => ?_⟩
  obtain ⟨y, rfl⟩ := deningerMZetaMk_surjective x
  rw [← deningerMZetaMk_isOpenMap.map_nhds_eq (x := y) hcont.continuousAt]
  infer_instance

/-- **The cokernel of the Poisson operator is metrizable.** -/
theorem deningerMZeta_metrizableSpace : MetrizableSpace DeningerMZeta := by
  letI : UniformSpace DeningerMZeta := IsTopologicalAddGroup.leftUniformSpace DeningerMZeta
  haveI : T2Space DeningerMZeta := deningerMZeta_t2Space
  haveI hcg : IsCountablyGenerated (𝓤 DeningerMZeta) := by
    have huni : (𝓤 DeningerMZeta)
        = comap (fun p : DeningerMZeta × DeningerMZeta => -p.1 + p.2) (𝓝 (0 : DeningerMZeta)) :=
      rfl
    rw [huni]
    infer_instance
  exact UniformSpace.metrizableSpace

end RHTower

end
