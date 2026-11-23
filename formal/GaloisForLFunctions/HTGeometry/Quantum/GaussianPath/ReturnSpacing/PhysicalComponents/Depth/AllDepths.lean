import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.NestedEntries
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.ComponentCounts
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.CrossingWindows

/-! # Depth distribution at every scalar tolerance below the semicircle -/
open Filter MeasureTheory Real Set Topology
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
open EmptyVisitFlux SharpOccupation
noncomputable section

private theorem fraction_of_unit_error (A B M : ℝ → ℕ) {a p q : ℝ} (hp : 0<p)
    (hA : Tendsto (fun T => (A T:ℝ)/(T-a)) atTop (𝓝 p))
    (hB : Tendsto (fun T => (B T:ℝ)/(T-a)) atTop (𝓝 q))
    (hb : ∀ T, B T≤M T+1 ∧ M T≤B T+1) :
    Tendsto (fun T => (M T:ℝ)/(A T:ℝ)) atTop (𝓝 (q/p)) := by
  have ht : Tendsto (fun T : ℝ => T-a) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-a) tendsto_id
  have hc := ht.const_div_atTop 1
  have hlo := hB.sub hc
  have hhi := hB.add hc
  rw [sub_zero] at hlo
  rw [add_zero] at hhi
  have hm : Tendsto (fun T => (M T:ℝ)/(T-a)) atTop (𝓝 q) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    · filter_upwards [eventually_gt_atTop a] with T hT
      change (B T:ℝ)/(T-a)-1/(T-a)≤_
      rw [←sub_div]
      apply div_le_div_of_nonneg_right _ (sub_pos.mpr hT).le
      exact sub_le_iff_le_add.mpr (by exact_mod_cast (hb T).1)
    · filter_upwards [eventually_gt_atTop a] with T hT
      change _≤(B T:ℝ)/(T-a)+1/(T-a)
      rw [←add_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast (hb T).2) (sub_pos.mpr hT).le
  refine (hm.div hA hp.ne').congr' ?_
  filter_upwards [eventually_gt_atTop a] with T hT
  exact div_div_div_cancel_right₀ (sub_pos.mpr hT).ne' _ _

/-- On each Gaussian prefix the proportion of genuine scalar entries whose
connected visit reaches a smaller tolerance is the ratio of the two arc
lengths to the power D−2. The observation origin may lie inside a visit. -/
theorem gaussian_scalar_component_depth :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let E := fun j => -H.2.isHermitian.eigenvalues j
      ∀ a : ℝ, 0≤a → ∀ ρ∈Ioo (0:ℝ) (sqrt 2), ∀ δ∈Ioc (0:ℝ) ρ,
        let A := entriesAfter E (physicalArc ρ) a
        Tendsto (fun T => ((reached (visitSet H 0 ρ) (visitSet H 0 δ) (A T)).card:ℝ)/(A T).card)
          atTop (𝓝 ((physicalArc δ/physicalArc ρ)^(2^N-2:ℕ))) := by
  classical
  filter_upwards [gaussian_empty_visit_flux,gaussian_path_all_prefixes_maximally_projective] with ω hf hi k
  intro N H E a ha ρ hρ δ hδ A
  let B := entriesAfter E (physicalArc δ) a
  have hδ' : δ∈Ioo (0:ℝ) (sqrt 2) := ⟨hδ.1,hδ.2.trans_lt hρ.2⟩
  have hx := (physicalArc_spec hρ.1 hρ.2).1
  have hy := (physicalArc_spec hδ'.1 hδ'.2).1
  have hyx : physicalArc δ≤physicalArc ρ := by
    by_contra! h
    have he := strictMonoOn_zeroGateArcTolerance (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy) h
    rw [(physicalArc_spec hρ.1 hρ.2).2,(physicalArc_spec hδ'.1 hδ'.2).2] at he
    exact he.not_ge hδ.2
  have closed (r : ℝ) : IsClosed (visitSet H 0 r) := by
    simp only [visitSet,hasProjectiveCircuitApproximation_iff_infDist]
    exact isClosed_le (orbitCircuitDistance_lipschitz H 0).continuous continuous_const
  have sub : visitSet H 0 δ ⊆ visitSet H 0 ρ := by
    rintro t ⟨z,hz,C,hC,h⟩
    exact ⟨z,hz,C,hC,h.trans hδ.2⟩
  have mem (r : ℝ) (hr : r∈Ioo (0:ℝ) (sqrt 2)) (u T : ℝ) :
      u∈entriesAfter E (physicalArc r) a T ↔ a<u ∧ u≤T ∧ Entry (visitSet H 0 r) u := by
    have h := (hf k r hr.1 hr.2).1
    rw [entriesAfter,Finset.mem_sdiff,h,h]
    constructor
    · rintro ⟨⟨hu,hT,he⟩,hn⟩
      exact ⟨lt_of_not_ge (fun hl => hn ⟨hu,hl,he⟩),hT,he⟩
    · rintro ⟨hu,hT,he⟩
      exact ⟨⟨ha.trans_lt hu,hT,he⟩,fun h => hu.not_ge h.2.1⟩
  let w := fun j => E j/(2*π)
  have sep (u : ℝ) (hu : u∈visitSet H 0 δ) (v : ℝ) (hv : Entry (visitSet H 0 δ) v) (huv : u<v) :
      ∃ z∈Ioo u v, z∉visitSet H 0 ρ := by
    have he : visitEntry w (physicalArc δ) v := by
      simpa only [Entry,visitEntry,w,E,physical_visit H hδ'.1 hδ'.2] using hv
    obtain ⟨z,hz,hn⟩ := outer_absence_before_inner_entry w hy.1.le hyx hx.2 huv
      ((physical_visit H hδ'.1 hδ'.2 u).mpr hu) he
    exact ⟨z,hz,fun h => hn ((physical_visit H hρ.1 hρ.2 z).mpr h)⟩
  have hR := (hf k ρ hρ.1 hρ.2).2.1
  have rate (r : ℝ) (hr : r∈Ioo (0:ℝ) (sqrt 2)) := by
    have hx' := (physicalArc_spec hr.1 hr.2).1
    exact entries_after_rate E (maximallyProjectiveEnergy_neg (hi k)) hx'.1 hx'.2 a
  have hcard : Fintype.card (Fin N→Bool)=2^N := by simp
  have hp := rate ρ hρ
  have hq := rate δ hδ'
  rw [hcard] at hp hq
  have hne : pairTurnRate E≠0 := (mul_ne_zero_iff.mp hR.ne').2
  have h := fraction_of_unit_error (fun T => (A T).card) (fun T => (B T).card)
    (fun T => (reached (visitSet H 0 ρ) (visitSet H 0 δ) (A T)).card) hR hp hq
    (component_count_bounds (closed ρ) (closed δ) sub sep A B (mem ρ hρ) (mem δ hδ'))
  rwa [mul_div_mul_right _ _ hne,←div_pow] at h

#print axioms gaussian_scalar_component_depth
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
