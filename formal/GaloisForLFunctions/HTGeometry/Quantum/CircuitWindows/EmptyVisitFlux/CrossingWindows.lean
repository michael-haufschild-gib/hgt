import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.GaussianLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.CrossingWidth

/-! # Continuous empty-circuit entry statistics from the first robust crossing -/
open Matrix MeasureTheory Filter Topology Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux
noncomputable section
open SharpOccupation

/-- Entry after an origin counts a fresh arrival, even if that origin lies
inside an existing visit interval. -/
def entriesAfter {I : Type*} [Fintype I] (E : I → ℝ) (x a T : ℝ) : Finset ℝ := by
  classical
  exact entryDates E x T \ entryDates E x a

theorem entries_after_rate {I : Type*} [Fintype I] [DecidableEq I] (E : I → ℝ)
    (hi : MaximallyProjectiveEnergy E) {x : ℝ} (hx : 0<x) (hs : x<1/2) (a : ℝ) :
    Tendsto (fun T : ℝ => ((entriesAfter E x a T).card:ℝ)/(T-a)) atTop
      (𝓝 (x^(Fintype.card I-2)*pairTurnRate E)) := by
  classical
  have h := entry_count_rate E hi hx hs
  let C := ((entryDates E x a).card:ℝ)
  have hc := (tendsto_id (x := (atTop : Filter ℝ))).const_div_atTop C
  have ha := (tendsto_id (x := (atTop : Filter ℝ))).const_div_atTop a
  have hh := (h.sub hc).div (ha.const_sub 1) (by norm_num : (1:ℝ)-0≠0)
  rw [sub_zero,sub_zero,div_one] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (max a 0)] with T hT
  have h0 := (le_max_right a 0).trans_lt hT
  have hT' := (le_max_left a 0).trans_lt hT
  have hsub : entryDates E x a ⊆ entryDates E x T := by
    intro t ht
    obtain ⟨ht,ha',he⟩ := (mem_entryDates E hx.le hs t a).mp ht
    exact (mem_entryDates E hx.le hs t T).mpr ⟨ht,ha'.trans hT'.le,he⟩
  change (((entryDates E x T).card:ℝ)/T-C/T)/(1-a/T) = ((entriesAfter E x a T).card:ℝ)/(T-a)
  dsimp only [entriesAfter]
  rw [Finset.card_sdiff_of_subset hsub,Nat.cast_sub (Finset.card_le_card hsub)]
  dsimp only [C]
  field_simp [h0.ne',(sub_pos.mpr hT').ne']

/-- At the first robust near-Hilbert-budget crossing on the same actual
draw, the limiting count per unit time of continuous empty-circuit entries
is the exact spectral flux at every physical error below √2. -/
theorem gaussian_first_crossing_flux :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let E := fun j => -H.2.isHermitian.eigenvalues j
      ∃ σ > 0, orbitCircuitDistance H P σ = 9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        ∀ ε : ℝ, 0<ε → ε<sqrt 2 →
          let x := physicalArc ε
          let F := entriesAfter E x σ
          (∀ t T, t∈F T ↔ σ<t ∧ t≤T ∧ t∈visitSet H 0 ε ∧
              ∃ d>0, ∀ u ∈ Ioo (t-d) t, u∉visitSet H 0 ε) ∧
          Tendsto (fun T : ℝ => ((F T).card:ℝ)/(T-σ)) atTop (𝓝 (x^(2^N-2:ℕ)*pairTurnRate E)) := by
  filter_upwards [gaussian_empty_visit_flux,gaussian_path_all_prefixes_maximally_projective,
    LocalPatches.gaussian_first_crossing_local_width] with ω hF hω hw
  filter_upwards [hw] with k hk
  intro N H P E
  obtain ⟨σ,hσ,he,hbefore,_⟩ := hk
  have hpos := (show 0 ≤ LocalPatches.localCrossingWidth N by unfold LocalPatches.localCrossingWidth; positivity).trans_lt hσ
  refine ⟨σ,hpos,he,hbefore,?_⟩
  intro ε hε hsmall x F
  have hmem := (hF k ε hε hsmall).1
  obtain ⟨hx,_⟩ := physicalArc_spec hε hsmall
  constructor
  · intro t T
    change t ∈ entryDates E x T \ entryDates E x σ ↔ _
    rw [Finset.mem_sdiff,hmem,hmem]
    constructor
    · rintro ⟨⟨ht,hT,hv⟩,hnot⟩
      exact ⟨lt_of_not_ge (fun hl => hnot ⟨ht,hl,hv⟩),hT,hv⟩
    · rintro ⟨ht,hT,hv⟩
      exact ⟨⟨hpos.trans ht,hT,hv⟩,fun h => ht.not_ge h.2.1⟩
  · simpa only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] using
      entries_after_rate E (maximallyProjectiveEnergy_neg (hω k)) hx.1 hx.2 σ

#print axioms entries_after_rate
#print axioms gaussian_first_crossing_flux
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux
