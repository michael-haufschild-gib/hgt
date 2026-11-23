import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.DurationCharge
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.LimitLaw.EntryFlux

/-! # Upper residence tail at the physical mean time scale -/
open MeasureTheory Filter Set Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
open EmptyVisitFlux SharpOccupation SpectralGapMass.Bulk
noncomputable section

/-- Counting each connected visit once, the scaled duration has the uniform
Markov upper tail given by its physical mean. The observation starts at
the first near-Hilbert crossing on each frozen prefix. -/
theorem gaussian_residence_tail_upper :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ a λ : ℝ, 0<a → sqrt (48*π)/(24*a)<λ →
      ∀ᶠ k : ℕ in atTop, let N := k+3
        let D : ℕ := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
        let P := nearHilbertContinuousCircuitBudget N
        let E := fun i => -H.2.isHermitian.eigenvalues i
        ∃ σ>0, orbitCircuitDistance H P σ=9/80 ∧
          (∀ t∈Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
          ∀ ρ∈Ioo (0:ℝ) (sqrt 2), let r := physicalArc ρ
            let L := 2*π*r*a/((D:ℝ)*sqrt N)
            let A := entriesAfter E r σ
            ∀ᶠ T : ℝ in atTop, ((longVisits (visitSet H 0 ρ) L (A T)).card:ℝ)/(A T).card<λ := by
  filter_upwards [gaussian_first_crossing_entry_constant,gaussian_empty_visit_flux] with ω hc he
  obtain ⟨R,hR,hc⟩ := hc
  intro a λ ha hλ
  have hp : 0<12/(π*sqrt (48*π)) := by positivity
  have hh := (hR.const_mul (2*π*a)).inv₀ (mul_pos (by positivity) hp).ne'
  have hlim : (2*π*a*(12/(π*sqrt (48*π))))⁻¹=sqrt (48*π)/(24*a) := by
    field_simp [pi_ne_zero,ha.ne',(by positivity : sqrt (48*π)≠0)]
    <;> ring
  rw [hlim] at hh
  filter_upwards [hc,hR.eventually_const_lt hp,hh.eventually_lt_const hλ] with k hk hpos hλ'
  intro N D H P E
  obtain ⟨σ,hσ,hcross,hbefore,hstats⟩ := hk
  refine ⟨σ,hσ,hcross,hbefore,?_⟩
  intro ρ hρ r L A
  have hr := (physicalArc_spec hρ.1 hρ.2).1.1
  have hD : 0<(D:ℝ) := by dsimp only [D]; positivity
  have hv : 0<sqrt (N:ℝ) := by dsimp only [N]; positivity
  have hL : 0<L := by dsimp only [L]; positivity
  obtain ⟨hrate,hres⟩ := hstats ρ hρ
  have htime : Tendsto (fun T : ℝ => T-σ) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-σ) tendsto_id
  have hf := (htime.const_div_atTop L).div hrate
    (mul_pos (pow_pos hr _) (mul_pos (mul_pos (pow_pos hD 2) hv) hpos)).ne'
  rw [zero_div] at hf
  have hzero : Tendsto (fun T : ℝ => L/(A T).card) atTop (𝓝 0) := by
    refine hf.congr' ?_
    filter_upwards [eventually_gt_atTop σ] with T hT
    exact div_div_div_cancel_right₀ (sub_pos.mpr hT).ne' _ _
  have hupper := (hres.add hzero).div_const L
  have hscale : r/((D:ℝ)*sqrt N*R k)/L=(2*π*a*R k)⁻¹ := by
    dsimp only [L]
    field_simp [hD.ne',hv.ne',hpos.ne',hr.ne',ha.ne',pi_ne_zero]
    <;> ring
  rw [add_zero,hscale] at hupper
  filter_upwards [hupper.eventually_lt_const hλ'] with T ht
  let V := visitSet H 0 ρ
  have hmem (u : ℝ) (hu : u∈A T) : u∈Icc σ T ∧ Entry V u := by
    obtain ⟨hnew,hold⟩ := Finset.mem_sdiff.mp hu
    have hm := (he k ρ hρ.1 hρ.2).1
    obtain ⟨hu₀,huT,he'⟩ := (hm u T).mp hnew
    exact ⟨⟨le_of_not_gt (fun h => hold ((hm u σ).mpr ⟨hu₀,h.le,he'⟩)),huT⟩,he'⟩
  have hb := duration_charge V σ T L hL.le (A T) hmem
  apply lt_of_le_of_lt _ ht
  change ((longVisits V L (A T)).card:ℝ)/(A T).card ≤
    (volume.real (V∩Icc σ T)/(A T).card+L/(A T).card)/L
  rw [le_div_iff₀ hL,←add_div,div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hb (Nat.cast_nonneg _)

#print axioms gaussian_residence_tail_upper
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
