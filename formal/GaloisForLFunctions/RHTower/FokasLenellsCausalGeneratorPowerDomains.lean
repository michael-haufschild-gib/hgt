import GaloisForLFunctions.RHTower.FokasLenellsCausalResolventPowers

/-! The actual domains of repeated maximal-generator applications, classified exactly by
ranges of the existing resolvent powers. No artificial extension of the generator is used. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- Domain of k genuine applications of the maximal causal generator. Each successor requires
actual first-generator membership and membership of its actual output in the preceding domain. -/
def causalGeneratorPowerDomain : ℕ → Submodule ℂ (hardyL2ᗮ)
  | 0 => ⊤
  | k+1 => ((causalGeneratorPowerDomain k).comap causalGenerator).map causalGeneratorDomain.subtype

/-- Successor regularity is exactly the existence of an actual domain element with regular output. -/
theorem causalGeneratorPowerDomain_mem_succ (k : ℕ) (u : hardyL2ᗮ) :
    u ∈ causalGeneratorPowerDomain (k+1) ↔
      ∃ v : causalGeneratorDomain, causalGenerator v ∈ causalGeneratorPowerDomain k ∧ v.val = u := Iff.rfl

/-- The recursive first domain is precisely the existing actual maximal-generator domain. -/
theorem causalGeneratorPowerDomain_one : causalGeneratorPowerDomain 1 = causalGeneratorDomain := by
  apply le_antisymm
  · rintro u ⟨v, _, rfl⟩
    exact v.property
  · intro u hu
    exact ⟨⟨u, hu⟩, Submodule.mem_top, rfl⟩

/-- Each additional genuine generator application imposes at least the preceding regularity. -/
theorem causalGeneratorPowerDomain_succ_le (k : ℕ) :
    causalGeneratorPowerDomain (k+1) ≤ causalGeneratorPowerDomain k := by
  induction k with
  | zero => exact le_top
  | succ k ih => exact Submodule.map_mono (Submodule.comap_mono ih)

private theorem resolvent_gains_order (z : {z : ℂ // 0 < z.re}) (k : ℕ)
    (u : hardyL2ᗮ) (hu : u ∈ causalGeneratorPowerDomain k) :
    (causalComplexResolvent z u).val ∈ causalGeneratorPowerDomain (k+1) := by
  induction k generalizing u with
  | zero => exact ⟨causalComplexResolvent z u, Submodule.mem_top, rfl⟩
  | succ k ih =>
    have hr := ih u (causalGeneratorPowerDomain_succ_le k hu)
    refine ⟨causalComplexResolvent z u, ?_, rfl⟩
    change causalGenerator (causalComplexResolvent z u) ∈ causalGeneratorPowerDomain (k+1)
    rw [causalGenerator_complexResolvent]
    exact (causalGeneratorPowerDomain (k+1)).sub_mem
      ((causalGeneratorPowerDomain (k+1)).smul_mem z.val hr) hu

/-- The actual resolvent raises genuine generator regularity by one order. -/
theorem causalComplexResolvent_mem_powerDomain (z : {z : ℂ // 0 < z.re}) (k : ℕ)
    (u : causalGeneratorPowerDomain k) :
    (causalComplexResolvent z u.val).val ∈ causalGeneratorPowerDomain (k+1) :=
  resolvent_gains_order z k u.val u.property

/-- Every k-th resolvent output permits k actual generator applications. -/
theorem causalResolventPower_mem_powerDomain (z : {z : ℂ // 0 < z.re}) (k : ℕ) (u : hardyL2ᗮ) :
    causalResolventPower z k u ∈ causalGeneratorPowerDomain k := by
  induction k with
  | zero => exact Submodule.mem_top
  | succ k ih => exact resolvent_gains_order z k _ ih

/-- Every genuinely k-times-regular input is exactly a k-th resolvent output. -/
theorem causalResolventPower_range_eq_powerDomain (z : {z : ℂ // 0 < z.re}) (k : ℕ) :
    (causalResolventPower z k).toLinearMap.range = causalGeneratorPowerDomain k := by
  apply le_antisymm
  · rintro u ⟨v, rfl⟩
    exact causalResolventPower_mem_powerDomain z k v
  · induction k with
    | zero => intro u _; exact ⟨u, rfl⟩
    | succ k ih =>
      rintro u ⟨v, hv, rfl⟩
      have hu := causalGeneratorPowerDomain_succ_le k
        (show v.val ∈ causalGeneratorPowerDomain (k+1) from ⟨v, hv, rfl⟩)
      have hs : causalComplexGeneratorShift z.val v ∈ causalGeneratorPowerDomain k :=
        (causalGeneratorPowerDomain k).sub_mem ((causalGeneratorPowerDomain k).smul_mem z.val hu) hv
      obtain ⟨w, hw⟩ := ih hs
      change causalResolventPower z k w = causalComplexGeneratorShift z.val v at hw
      refine ⟨w, ?_⟩
      change causalResolventPower z (k+1) w = v.val
      rw [causalResolventPower_succ, hw, causalComplexResolvent_generatorShift]

/-- The exact k-th resolvent range is independent of the right-half-plane spectral parameter. -/
theorem causalResolventPower_range_independent (z w : {z : ℂ // 0 < z.re}) (k : ℕ) :
    (causalResolventPower z k).toLinearMap.range = (causalResolventPower w k).toLinearMap.range := by
  rw [causalResolventPower_range_eq_powerDomain, causalResolventPower_range_eq_powerDomain]

/-- Every rational Cauchy eigenvector permits arbitrarily many actual generator applications. -/
theorem causalCauchyEigenvector_mem_powerDomain (w : {z : ℂ // 0 < z.im}) (k : ℕ) :
    causalCauchyEigenvector w ∈ causalGeneratorPowerDomain k := by
  induction k with
  | zero => exact Submodule.mem_top
  | succ k ih =>
    refine ⟨causalCauchyEigenDomain w, ?_, rfl⟩
    change causalGenerator (causalCauchyEigenDomain w) ∈ causalGeneratorPowerDomain k
    rw [causalGenerator_cauchyEigenDomain]
    exact (causalGeneratorPowerDomain k).smul_mem _ ih

/-- Every actual finite-order generator domain is dense in the underlying lower Hardy space. -/
theorem dense_causalGeneratorPowerDomain (k : ℕ) :
    Dense (causalGeneratorPowerDomain k : Set (hardyL2ᗮ)) := by
  have hs : Submodule.span ℂ (Set.range causalCauchyEigenvector) ≤ causalGeneratorPowerDomain k := by
    apply Submodule.span_le.2
    rintro u ⟨w, rfl⟩
    exact causalCauchyEigenvector_mem_powerDomain w k
  have hc := Submodule.topologicalClosure_mono hs
  rw [topologicalClosure_span_causalCauchyEigenvector_eq_top] at hc
  have he : (causalGeneratorPowerDomain k).topologicalClosure = ⊤ := top_unique hc
  intro u
  change u ∈ (causalGeneratorPowerDomain k).topologicalClosure
  rw [he]
  exact Submodule.mem_top

end
end RHTower.FokasLenells
