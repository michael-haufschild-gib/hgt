import GaloisForLFunctions.RHTower.FieldOneFiniteAdeleSigmaCompact
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Separation.Profinite

/-!
# Compact-open basis of the rational finite adeles

Each local rational adic completion is homeomorphic to a `p`-adic field and
is therefore Hausdorff and totally disconnected.  The restricted product
embeds continuously and injectively in the product of its local completions,
so the rational finite adeles inherit these separation properties.

Local compactness then refines the clopen basis to a compact-open basis.  A
compact subset of an open set is consequently contained in a compact-open
set still lying inside that open set.

These are topological approximation lemmas; no measure estimate, density
claim, numerical computation, trace, spectral assertion, or RH premise is
used.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open Filter Function IsDedekindDomain Set TopologicalSpace Topology
open scoped RestrictedProduct

/-- Rational finite adeles are Hausdorff. -/
noncomputable instance fieldOneFiniteAdeleT2Space :
    T2Space FieldOneFiniteAdele := by
  letI (v : HeightOneSpectrum ℤ) :
      T2Space (v.adicCompletion ℚ) :=
    Homeomorph.t2Space
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.symm
  exact .of_injective_continuous
    DFunLike.coe_injective RestrictedProduct.continuous_coe

/-- Rational finite adeles are totally disconnected. -/
noncomputable instance fieldOneFiniteAdeleTotallyDisconnectedSpace :
    TotallyDisconnectedSpace FieldOneFiniteAdele := by
  letI (v : HeightOneSpectrum ℤ) :
      TotallyDisconnectedSpace (v.adicCompletion ℚ) :=
    Homeomorph.totallyDisconnectedSpace
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.symm
  constructor
  exact isTotallyDisconnected_of_image
    RestrictedProduct.continuous_coe.continuousOn
    DFunLike.coe_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/-- Compact-open subsets form a basis of the rational finite-adele topology. -/
theorem fieldOneFiniteAdele_compactOpen_basis :
    IsTopologicalBasis
      {s : Set FieldOneFiniteAdele | IsCompact s ∧ IsOpen s} := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · intro s hs
    exact hs.2
  · intro x U hxU hU
    obtain ⟨K, hKc, hxK, hKU⟩ := exists_compact_subset hU hxU
    obtain ⟨V, hVcl, hxV, hVK⟩ :=
      loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1
        (isOpen_interior.mem_nhds hxK)
    refine
      ⟨V, ⟨?_, hVcl.2⟩, hxV,
        (hVK.trans interior_subset).trans hKU⟩
    exact hKc.of_isClosed_subset hVcl.1
      (hVK.trans interior_subset)

/-- Compact-open interpolation between a compact set and an open
neighborhood. -/
theorem fieldOneFiniteAdele_exists_compactOpen_between
    {K U : Set FieldOneFiniteAdele}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ C : Set FieldOneFiniteAdele,
      IsCompact C ∧ IsOpen C ∧ K ⊆ C ∧ C ⊆ U := by
  choose V hV using fun (x : K) =>
    fieldOneFiniteAdele_compactOpen_basis.mem_nhds_iff.1
      (hU.mem_nhds (hKU x.property))
  have hcover : K ⊆ ⋃ x : K, V x := by
    intro x hx
    exact Set.mem_iUnion.2
      ⟨⟨x, hx⟩, (hV ⟨x, hx⟩).2.1⟩
  choose I hI using
    hK.elim_finite_subcover V
      (fun x => (hV x).1.2) hcover
  refine
    ⟨⋃ x ∈ I, V x,
      I.isCompact_biUnion (fun x _ => (hV x).1.1),
      isOpen_biUnion (fun x _ => (hV x).1.2),
      hI, ?_⟩
  exact iUnion₂_subset fun x _ => (hV x).2.2

end

end GaloisForLFunctions.RHTower
