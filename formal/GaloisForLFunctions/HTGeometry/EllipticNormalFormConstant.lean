import GaloisForLFunctions.HTGeometry.EllipticClearedOrders
import GaloisForLFunctions.HTGeometry.EllipticThetaLogComparisonRigidity

/-!
# A pole-free lattice-periodic function is constant where it is regular

The counting argument produces a combination with no poles at all.  Its canonical normal form is
then entire, inherits the lattice periods, and is constant by Liouville; and wherever the
combination itself is analytic it agrees with that normal form.  So the combination takes a single
value on its whole regular locus.

* **`eq_of_nonneg_order_of_lattice_periodic`**.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **A pole-free lattice-periodic meromorphic function takes one value on its regular locus.** -/
theorem eq_of_nonneg_order_of_lattice_periodic (L : PeriodPair) {G : ℂ → ℂ}
    (hmer : MeromorphicOn G Set.univ)
    (h₁ : Function.Periodic G L.ω₁) (h₂ : Function.Periodic G L.ω₂)
    (hord : ∀ z, 0 ≤ meromorphicOrderAt G z)
    {x y : ℂ} (hx : AnalyticAt ℂ G x) (hy : AnalyticAt ℂ G y) :
    G x = G y := by
  set F := toMeromorphicNFOn G Set.univ with hF
  have hNF : MeromorphicNFOn F Set.univ := meromorphicNFOn_toMeromorphicNFOn _ _
  have hordF : ∀ z, 0 ≤ meromorphicOrderAt F z := by
    intro z
    rw [hF, meromorphicOrderAt_toMeromorphicNFOn hmer (Set.mem_univ z)]
    exact hord z
  have hFan : ∀ z, AnalyticAt ℂ F z := fun z =>
    (hNF (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp (hordF z)
  have hFanOn : AnalyticOnNhd ℂ F Set.univ := fun z _ => hFan z
  have hper : ∀ w : ℂ, Function.Periodic G w → Function.Periodic F w := fun w hw =>
    periodic_toMeromorphicNFOn_of_eventually_punctured hmer hF hFanOn w
      (fun _ => Filter.Eventually.of_forall (fun u => hw u))
  have hlat : ∀ p ∈ L.lattice, Function.Periodic F p := by
    intro p hp
    refine periodic_of_mem_span_range ![L.ω₁, L.ω₂] (fun i => ?_) p ?_
    · fin_cases i
      · exact hper _ h₁
      · exact hper _ h₂
    · rw [range_cons_two]
      exact hp
  have hconst := const_of_lattice_periodic_analytic L hFan hlat
  have hGF : ∀ z, AnalyticAt ℂ G z → G z = F z := by
    intro z hz
    have heq : F =ᶠ[𝓝[≠] z] G := by
      rw [hF]
      exact hmer.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
    have hfull := eventuallyEq_nhds_of_nhdsNE_of_continuousAt heq (hFan z).continuousAt
      hz.continuousAt
    exact hfull.eq_of_nhds.symm
  rw [hGF x hx, hGF y hy]
  exact hconst x y

end GaloisForLFunctions.HTGeometry
