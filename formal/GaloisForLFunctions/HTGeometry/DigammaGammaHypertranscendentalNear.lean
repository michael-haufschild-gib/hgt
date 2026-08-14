import GaloisForLFunctions.HTGeometry.DigammaGammaLocalHypertranscendence
import GaloisForLFunctions.HTGeometry.MeromorphicPoleJetCertificate
import GaloisForLFunctions.HTGeometry.TripticGermConstraint

/-!
# Local hypertranscendence connector for `digamma ∘ Gamma`

The existing open-set no-relation theorem and the pole-jet germ interface used separate proposition
types.  A punctured-neighbourhood relation holds on a nonempty open punctured set; intersecting that
set with the open regular locus transports the former theorem into `HypertranscendentalNear`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

/-- `digamma ∘ Gamma` is hypertranscendental near every point where its composition is analytic. -/
theorem hypertranscendentalNear_digamma_comp_Gamma
    {a : ℂ} (ha : a ∈ GaloisForLFunctions.digammaGammaRegularSet) :
    HypertranscendentalNear (fun z => Complex.digamma (Complex.Gamma z)) a := by
  rintro ⟨n, P, hP, hrel⟩
  have hregFull : ∀ᶠ z in nhds a,
      z ∈ GaloisForLFunctions.digammaGammaRegularSet :=
    GaloisForLFunctions.isOpen_digammaGammaRegularSet.mem_nhds ha
  have hregNhds : ∀ᶠ z in nhdsWithin a {a}ᶜ,
      z ∈ GaloisForLFunctions.digammaGammaRegularSet :=
    hregFull.filter_mono nhdsWithin_le_nhds
  obtain ⟨W, hWopen, hWmem, hW⟩ :=
    exists_isOpen_of_eventually_nhdsNE (hrel.and hregNhds)
  have hWne : W.Nonempty :=
    Filter.NeBot.nonempty_of_mem (f := nhdsWithin a {a}ᶜ) inferInstance hWmem
  apply GaloisForLFunctions.no_local_differential_relation_digamma_comp_Gamma
    hWopen hWne (fun z hz => (hW z hz).2)
  exact ⟨n, P, hP, fun z hz => (hW z hz).1⟩

/-- The point `1` belongs to the regular locus of `digamma ∘ Gamma`. -/
theorem one_mem_digammaGammaRegularSet :
    (1 : ℂ) ∈ GaloisForLFunctions.digammaGammaRegularSet := by
  intro m hm
  have hre := congrArg Complex.re hm
  simp only [Complex.Gamma_one, Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
  have hmnonneg : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

/-- A concrete premise-free local hypertranscendence witness. -/
theorem hypertranscendentalNear_digamma_comp_Gamma_one :
    HypertranscendentalNear (fun z => Complex.digamma (Complex.Gamma z)) 1 :=
  hypertranscendentalNear_digamma_comp_Gamma one_mem_digammaGammaRegularSet

end GaloisForLFunctions.HTGeometry
