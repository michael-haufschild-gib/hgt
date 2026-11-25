import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactLevels.VisitParameter

/-! # Stability of a first physical dip under lower robust crossing heights -/

open Set Metric Filter
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactLevels.CrossingHeights
open PrecisionReturns
noncomputable section

/-- All sufficiently close lower record levels first occur within any
prescribed window before the original crossing. Both origins have the
same first dip at every gate budget through the crossing budget. -/
theorem stable_dip_below_crossing {N : ℕ} (H : selfAdjoint (Register N)) (P : ℕ)
    {ε r σ : ℝ} (hε : 0<ε) (her : ε<r) (hσ : 0<σ) (hc : orbitCircuitDistance H P σ=r)
    (hprior : ∀ t∈Ico 0 σ, orbitCircuitDistance H P t<r) {h : ℝ} (hh : 0<h) :
    ∃ b∈Ico ε r, ∀ η∈Ioo b r, ∀ u>0, orbitCircuitDistance H P u=η →
      (∀ t∈Ico 0 u, orbitCircuitDistance H P t<η) →
      u∈Ioo (σ-h) σ ∧ ∀ s≤P, firstVisit H u s ε=firstVisit H σ s ε := by
  let f := orbitCircuitDistance H P
  have hcont : Continuous f := (orbitCircuitDistance_lipschitz H P).continuous
  have hfar : ∀ᶠ t in 𝓝 σ, ε<f t :=
    hcont.continuousAt.eventually (lt_mem_nhds (her.trans_eq hc.symm))
  obtain ⟨ρ,hρ,hr⟩ := Metric.eventually_nhds_iff.mp hfar
  let d := min (σ/2) (min (h/2) (ρ/2))
  have hd : 0<d := lt_min (half_pos hσ) (lt_min (half_pos hh) (half_pos hρ))
  have hdσ : d≤σ/2 := min_le_left ..
  have hdh : d≤h/2 := (min_le_right ..).trans (min_le_left ..)
  have hdρ : d≤ρ/2 := (min_le_right ..).trans (min_le_right ..)
  have h0 : 0≤σ-d := by linarith only [hdσ,hσ]
  obtain ⟨m,hm,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr h0) hcont.continuousOn
  have hmσ : m<σ := hm.2.trans_lt (sub_lt_self _ hd)
  refine ⟨max ε (f m),⟨le_max_left ..,max_lt her (hprior m ⟨hm.1,hmσ⟩)⟩,?_⟩
  intro η hη u hu he hfirst
  have hus : u<σ := by
    rcases lt_trichotomy u σ with h|h|h
    · exact h
    · subst u
      exact (hη.2.ne (he.symm.trans hc)).elim
    · have hbad := hfirst σ ⟨hσ.le,h⟩
      rw [hc] at hbad
      exact (hη.2.asymm hbad).elim
  have hlu : σ-d<u := by
    by_contra! h
    have hle : orbitCircuitDistance H P u ≤ max ε (f m) :=
      (hmax ⟨hu.le,h⟩).trans (le_max_right ε (f m))
    rw [he] at hle
    exact hη.1.not_ge hle
  refine ⟨⟨by linarith only [hlu,hdh,hh],hus⟩,?_⟩
  intro s hs
  have hv := firstVisit_isLeast H u s hε
  have hw := firstVisit_isLeast H σ s hε
  have hvσ : σ≤firstVisit H u s ε := by
    by_contra! h
    let v := firstVisit H u s ε
    have huv : u≤v := hv.1.1
    have hdist : dist v σ<ρ := by
      rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr h.le)]
      linarith only [hlu,huv,hdρ,hρ]
    obtain ⟨z,hz,C,hC,hfit⟩ := hv.1.2
    exact (hr hdist).not_ge ((hasProjectiveCircuitApproximation_iff_infDist _ P _).mp
      ⟨z,hz,C,hC.trans hs,hfit⟩)
  exact le_antisymm (hv.2 ⟨hus.le.trans hw.1.1,hw.1.2⟩) (hw.2 ⟨hvσ,hv.1.2⟩)

#print axioms stable_dip_below_crossing
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactLevels.CrossingHeights
