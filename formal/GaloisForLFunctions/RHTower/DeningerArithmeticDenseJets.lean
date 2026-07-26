import GaloisForLFunctions.RHTower.DeningerArithmeticFiniteJetInterpolation
import GaloisForLFunctions.RHTower.DeningerArithmeticGlobalDivision

/-!
# Dense jet realization of compact-open arithmetic cohomology

Finite Hermite interpolation already implies that the simultaneous Xi-jet observation has dense
range in the full product topology; infinite interpolation is needed only to upgrade density to
surjectivity.  Exact global Xi division identifies its kernel with the Xi coboundaries, so the
observation descends to a continuous injective map

`O(ℂ) / XiC O(ℂ) ↪ ∏ rho, ℂ^(m_rho)`

with dense range.

This is the unconditional source-side Gelfand-triple boundary: the compact-open quotient is a
dense distributional jet realization even before a self-dual Hilbert completion or Hodge
positivity is constructed.
-/

open Filter Set Topology

namespace RHTower

noncomputable section

/--
A map to a product has dense range if it realizes arbitrary values on every finite set of outer
coordinates.
-/
theorem denseRange_pi_of_finiteInterpolation
    {X : Type*} {ι : Type*} {Y : ι → Type*}
    [∀ i, TopologicalSpace (Y i)]
    (f : X → (∀ i, Y i))
    (hfinite :
      ∀ (s : Finset ι) (y : ∀ i, Y i),
        ∃ x, ∀ i ∈ s, f x i = y i) :
    DenseRange f := by
  rw [DenseRange, dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨y, hyU⟩ := hUne
  have hUnhds : U ∈ 𝓝 y :=
    hU.mem_nhds hyU
  rw [nhds_pi, Filter.mem_pi, exists_finite_iff_finset] at hUnhds
  obtain ⟨s, V, hV, hVU⟩ := hUnhds
  obtain ⟨x, hx⟩ := hfinite s y
  have hfxV : f x ∈ Set.pi (s : Set ι) V := by
    intro i hi
    rw [hx i hi]
    exact mem_of_mem_nhds (hV i)
  have hfxU : f x ∈ U :=
    hVU hfxV
  exact ⟨f x, Set.mem_inter hfxU (Set.mem_range_self x)⟩

/-- Finite Xi Hermite interpolation makes the all-jets observation dense in the full product. -/
theorem denseRange_deningerCompactOpenAllJets :
    DenseRange deningerCompactOpenAllJets := by
  apply denseRange_pi_of_finiteInterpolation
  intro S target
  obtain ⟨F, hF⟩ :=
    exists_deningerCompactOpenPolynomial_finiteXiScalarJets
      S (fun rho k => target rho.1 k)
  refine ⟨F, ?_⟩
  intro rho hrho
  funext k
  exact hF ⟨rho, hrho⟩ k

/-- The all-jets observation descends continuously through compact-open middle cohomology. -/
def deningerCompactOpenH1AllJets :
    DeningerArithmeticCompactOpenH1 →L[ℂ]
      DeningerArithmeticJetProduct :=
  DeningerCompactOpenQuotient.liftL
    deningerCompactOpenXiRange
    deningerCompactOpenAllJets
    (fun {F} hF => by
      exact
        LinearMap.mem_ker.mp
          (deningerCompactOpenXiRange_le_allJets_ker hF))

@[simp]
theorem deningerCompactOpenH1AllJets_class
    (F : DeningerCompactOpenEntire) :
    deningerCompactOpenH1AllJets
        (deningerArithmeticCompactOpenH1Class F) =
      deningerCompactOpenAllJets F :=
  rfl

/-- Global Xi division makes the descended dense jet realization injective. -/
theorem deningerCompactOpenH1AllJets_injective :
    Function.Injective deningerCompactOpenH1AllJets := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨F, rfl⟩ := Quotient.exists_rep x
  apply
    (DeningerCompactOpenQuotient.mk_eq_zero_iff_mem
      deningerCompactOpenXiRange F).mpr
  rw [deningerCompactOpenXiRange_eq_allJets_ker]
  exact LinearMap.mem_ker.mpr hx

/-- The descended injective source realization remains dense in the full local jet product. -/
theorem denseRange_deningerCompactOpenH1AllJets :
    DenseRange deningerCompactOpenH1AllJets := by
  apply DenseRange.of_comp
    (g := deningerArithmeticCompactOpenH1Class)
  simpa only [Function.comp_def,
    deningerCompactOpenH1AllJets_class] using
      denseRange_deningerCompactOpenAllJets

end

end RHTower
