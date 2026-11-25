import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.ReturnObservations
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.FullRange.PhysicalRates
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.PrefixDeadlines.DifferenceWindows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EntrySensitivity.PrescribedCharacters.VisitIndices.Counting

/-! # Entire forward windows after smaller-register return records -/

open MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
open PrescribedTimes SharpOccupation
noncomputable section

private theorem shifted_window_bound {N q l : ℕ} (H : selfAdjoint (Register N)) (t : ℕ → ℝ)
    {ε η p W : ℝ} (hp : 0≤p) (hW : 0≤W) (hunit : windowHits H q ε 1⊆visitSet H l η)
    (hshift : ∀ i : ℕ, ∀ᶠ M : ℕ in atTop,
      (integerClockPrefixLaw (fun n => t n+(i:ℝ)) M : Measure ℝ).real (visitSet H l η)≤p) :
    ∀ᶠ M : ℕ in atTop,
      (integerClockPrefixLaw t M : Measure ℝ).real (windowHits H q ε W)≤(W+1)*p := by
  classical
  let L := ⌊W⌋₊+1
  let A := visitSet H l η
  let B (i : Fin L) := (fun u : ℝ => u+(i.val:ℝ)) ⁻¹' A
  have hA : MeasurableSet A := (ReturnExcursions.PrefixDeadlines.closed_visits H l η).measurableSet
  have hB (i : Fin L) : MeasurableSet (B i) := hA.preimage (measurable_id.add_const _)
  have hsub : windowHits H q ε W⊆⋃ i : Fin L, B i := by
    rintro u ⟨v,hv,hfit⟩
    let i : Fin L := ⟨⌊v-u⌋₊,Nat.lt_succ_of_le (Nat.floor_mono (by linarith only [hv.2]))⟩
    have hl : (i.val:ℝ)≤v-u := Nat.floor_le (sub_nonneg.mpr hv.1)
    have hr : v-u<(i.val:ℝ)+1 := Nat.lt_floor_add_one _
    exact mem_iUnion.mpr ⟨i,hunit ⟨v,⟨by linarith only [hl],by linarith only [hr]⟩,hfit⟩⟩
  have hb (i : Fin L) : ∀ᶠ M : ℕ in atTop, (integerClockPrefixLaw t M : Measure ℝ).real (B i)≤p := by
    filter_upwards [hshift i.val] with M hm
    rw [EntrySensitivity.PrescribedCharacters.VisitIndices.prefix_count _ _ hA] at hm
    rw [EntrySensitivity.PrescribedCharacters.VisitIndices.prefix_count _ _ (hB i)]
    exact hm
  filter_upwards [Filter.eventually_all.mpr hb] with M hm
  refine (measureReal_mono hsub).trans ((measureReal_iUnion_fintype_le B).trans
    ((Finset.sum_le_sum fun i _ => hm i).trans ?_))
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hp
  dsimp only [L]
  rw [Nat.cast_add_one]
  exact add_le_add (Nat.floor_le hW) (le_refl 1)

/-- After most genuine smaller-register dips, the whole next length-W
window avoids every affordable visit of the larger register. For any
b above the physical angular width, the exceptional fraction is at most
(W+1)b^D at every subcritical gate budget. -/
theorem gaussian_nested_forward_windows :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ g : ℕ → ℕ, subcriticalBudget g →
      ∀ ε∈Ioo (0:ℝ) 2, ∀ b : ℝ, physicalArc ε<b →
      ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
          isSelfAdjoint_pathHamiltonian _⟩
        ∀ j : ℕ, j<k → ∀ P s q : ℕ, q≤g N →
          let x := fun i => pathPauliDisorderShell ω (j+1) (pathCoeffEquiv (j+1) i)
          let t := returnClock (j+1) P s x
          ∀ W≥(0:ℝ), ∀ᶠ M : ℕ in atTop,
            (integerClockPrefixLaw t M : Measure ℝ).real (windowHits H q ε W)≤(W+1)*b^D := by
  obtain ⟨c,hc⟩ := FiniteRecords.gaussian_finite_occupation_full
  filter_upwards [hc,gaussian_shifted_return_observations,gaussian_unit_hit_enlargement] with ω hocc hrec hunit
  intro g hg ε hε b hxb
  obtain ⟨hx,htol⟩ := FiniteRecords.physicalArc_full hε
  obtain ⟨z,hxz,hzb⟩ := exists_between hxb
  obtain ⟨y,hxy,hymax⟩ := exists_between (lt_min hxz hx.2)
  have hy : y∈Ioo (0:ℝ) 1 := ⟨hx.1.trans hxy,hymax.trans_le (min_le_right ..)⟩
  have hδ : 0<zeroGateArcTolerance y-ε := by
    rw [←htol]
    exact sub_pos.mpr (strictMonoOn_zeroGateArcTolerance_full ⟨hx.1.le,hx.2.le⟩ ⟨hy.1.le,hy.2.le⟩ hxy)
  filter_upwards [hocc (fun n => g n+n^4) (subcritical_add_pow_four hg) y hy
    (physicalArc ε) z hx.1 hxy (hymax.trans_le (min_le_left ..)),hunit _ hδ] with k hhi hunit'
  intro N D H j hj P s q hq x t W hW
  have hw := hunit' q ε
  rw [show ε+(zeroGateArcTolerance y-ε)=zeroGateArcTolerance y by ring] at hw
  apply shifted_window_bound H t (pow_pos (hx.1.trans hxb) D).le hW hw
  intro i
  obtain ⟨p,htime,htick⟩ := hrec k j P s i hj (q+N^4) (zeroGateArcTolerance y)
  have hp : p≤z^D := le_of_tendsto (htime (fun _ => 0))
    ((eventually_ge_atTop _).mono fun T hT => (hhi (q+N^4) (Nat.add_le_add_right hq _) 0 T hT).2.le)
  have hD : D≠0 := (Nat.two_pow_pos N).ne'
  exact (htick.eventually_lt_const (hp.trans_lt (pow_lt_pow_left₀ hzb (hx.1.trans hxz).le hD))).mono
    fun _ h => h.le

#print axioms gaussian_nested_forward_windows
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
