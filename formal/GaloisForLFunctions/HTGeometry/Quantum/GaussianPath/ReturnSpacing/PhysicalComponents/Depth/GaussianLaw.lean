import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.Rate
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.CrossingRecords

/-! # Depth distribution of continuous empty-circuit visits after the first crossing -/
open Filter MeasureTheory Real Set Topology
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
open SharpOccupation EmptyVisitFlux
noncomputable section

/-- Physical tolerance corresponding to logarithmic depth z at an entry of
angular width x. -/
def depthCutoff (x : ℝ) (d : ℕ) (z : ℝ) :=
  zeroGateArcTolerance (x*exp (-z/(d:ℝ)))

private theorem cutoff_spec {ε z : ℝ} {d : ℕ} (hε : 0<ε) (hsmall : ε<sqrt 2)
    (hd : 0<d) (hz : 0≤z) :
    let x := physicalArc ε
    let δ := depthCutoff x d z
    δ∈Ioc (0:ℝ) ε ∧ (physicalArc δ/x)^d=exp (-z) := by
  intro x δ
  obtain ⟨hx,htol⟩ := physicalArc_spec hε hsmall
  let y := x*exp (-z/(d:ℝ))
  have hd' : 0<(d:ℝ) := Nat.cast_pos.mpr hd
  have hy : 0<y := mul_pos hx.1 (exp_pos _)
  have hyx : y≤x := mul_le_of_le_one_right hx.1.le (exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz) hd'.le))
  have hy' : y∈Icc (0:ℝ) (1/2) := ⟨hy.le,hyx.trans hx.2.le⟩
  have hδ : 0<δ := by
    change 0<zeroGateArcTolerance y
    rw [show (0:ℝ)=zeroGateArcTolerance 0 by simp [zeroGateArcTolerance]]
    exact strictMonoOn_zeroGateArcTolerance (by norm_num : (0:ℝ)∈Icc (0:ℝ) (1/2)) hy' hy
  have hδε : δ≤ε := (strictMonoOn_zeroGateArcTolerance.monotoneOn hy' (Ioo_subset_Icc_self hx) hyx).trans_eq htol
  obtain ⟨hδx,hδe⟩ := physicalArc_spec hδ (hδε.trans_lt hsmall)
  have he : physicalArc δ=y := strictMonoOn_zeroGateArcTolerance.injOn (Ioo_subset_Icc_self hδx) hy' hδe
  refine ⟨⟨hδ,hδε⟩,?_⟩
  have hn : x≠0 := hx.1.ne'
  rw [he,show y/x=exp (-z/(d:ℝ)) by dsimp only [y]; field_simp [hn],←exp_nat_mul]
  congr 1
  field_simp [hd'.ne']

/-- Count each distinct continuous visit once. The fraction reaching any
smaller tolerance is a power of the ratio of their enclosing arc lengths.
The exponent is two below the Hilbert dimension. -/
theorem gaussian_crossing_visit_depth :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let energy := fun j => -H.2.isHermitian.eigenvalues j
      ∃ σ > 0, orbitCircuitDistance H P σ = 9/80 ∧
        (∀ v ∈ Ico 0 σ, orbitCircuitDistance H P v < 9/80) ∧
        ∀ ε ∈ Ioc (0:ℝ) (1/10), let d : ℕ := 2^N-2
          let A := entriesAfter energy (physicalArc ε) σ
          let fraction := fun δ T => ((marked (visitSet H 0 ε) (visitSet H 0 δ) (A T)).card:ℝ)/(A T).card
          (∀ δ ∈ Ioc (0:ℝ) ε, Tendsto (fraction δ) atTop (𝓝 ((physicalArc δ/physicalArc ε)^d))) ∧
            ∀ z : ℝ, 0≤z → Tendsto (fraction (depthCutoff (physicalArc ε) d z)) atTop (𝓝 (exp (-z))) := by
  filter_upwards [eventual_unit_separation,gaussian_first_crossing_flux,gaussian_empty_visit_flux] with ω hs hc hp
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hs,hc] with k hs hc
  intro N H P energy
  obtain ⟨σ,hσ,he,hfirst,hflux⟩ := hc
  refine ⟨σ,hσ,he,hfirst,?_⟩
  intro ε hε d A fraction
  have hsmall : ε<sqrt 2 := hε.2.trans_lt (by nlinarith only [sq_sqrt (show (0:ℝ)≤2 by norm_num),sqrt_nonneg 2])
  suffices law : ∀ δ ∈ Ioc (0:ℝ) ε, Tendsto (fraction δ) atTop (𝓝 ((physicalArc δ/physicalArc ε)^d)) by
    refine ⟨law,fun z hz => ?_⟩
    have hN : 4≤2^N := Nat.pow_le_pow_right (by decide : 0<2) (show 2≤N by dsimp only [N]; omega)
    have hd : 0<d := by dsimp only [d]; omega
    obtain ⟨hδ,hr⟩ := cutoff_spec hε.1 hsmall hd hz
    simpa only [hr] using law _ hδ
  intro δ hδ
  have hδ' : δ∈Ioc (0:ℝ) (1/10) := ⟨hδ.1,hδ.2.trans hε.2⟩
  let B := entriesAfter energy (physicalArc δ) σ
  have closed (r : ℝ) : IsClosed (visitSet H 0 r) := by
    simp only [visitSet,hasProjectiveCircuitApproximation_iff_infDist]
    exact isClosed_le (orbitCircuitDistance_lipschitz H 0).continuous continuous_const
  have ha : σ∉visitSet H 0 ε := by
    intro h
    obtain ⟨z,hz,C,hC,hfit⟩ := h
    have h' := (hasProjectiveCircuitApproximation_iff_infDist _ P ε).mp
      ⟨z,hz,C,hC.trans (Nat.zero_le P),hfit⟩
    change orbitCircuitDistance H P σ≤ε at h'
    linarith only [he,h',hε.2]
  have sub : visitSet H 0 δ ⊆ visitSet H 0 ε := by
    rintro u ⟨z,hz,C,hC,h⟩
    exact ⟨z,hz,C,hC,h.trans hδ.2⟩
  obtain ⟨hae,hag⟩ := hs ε hε
  have hbg := (hs δ hδ').2
  obtain ⟨hA,hlA⟩ := hflux ε hε.1 hsmall
  obtain ⟨hB,hlB⟩ := hflux δ hδ.1 (hδ.2.trans_lt hsmall)
  have hpos := (hp k ε hε.1 hsmall).2.1
  have hh := fraction_of_count_bounds (fun T => (A T).card) (fun T => (B T).card)
    (fun T => (marked (visitSet H 0 ε) (visitSet H 0 δ) (A T)).card) σ _ _ hpos hlA hlB
    (count_bounds (closed ε) (closed δ) sub ha hae hag hbg A B hA hB)
  have hn : pairTurnRate energy ≠ 0 := (mul_ne_zero_iff.mp hpos.ne').2
  rwa [mul_div_mul_right _ _ hn,←div_pow] at hh

#print axioms gaussian_crossing_visit_depth
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
