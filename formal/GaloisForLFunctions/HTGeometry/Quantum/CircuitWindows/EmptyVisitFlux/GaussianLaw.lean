import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.EntryCount
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ShortTimeProducts.ScalarDensity

/-! # Entry frequency and mean duration of actual Gaussian empty-circuit visits -/
open Matrix MeasureTheory Filter Topology Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux
noncomputable section
open SharpOccupation

private theorem physical_visit {N : ℕ} (H : selfAdjoint (Register N)) {ε : ℝ}
    (hε : 0<ε) (hsmall : ε<sqrt 2) (t : ℝ) :
    flow (fun j => -H.2.isHermitian.eigenvalues j/(2*π)) t ∈ enclosingUnitArc (physicalArc ε) ↔
    t ∈ visitSet H 0 ε := by
  let θ := fun j => -(t*H.2.isHermitian.eigenvalues j)
  obtain ⟨hx,_⟩ := physicalArc_spec hε hsmall
  have hroot : sqrt 2 ≤ 2 := by nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2]
  have he : flow (fun j => -H.2.isHermitian.eigenvalues j/(2*π)) t =
      fun j => ((θ j/(2*π):ℝ):UnitAddCircle) := by
    funext j
    unfold flow
    congr 1
    dsimp only [θ]
    ring
  let r : Icc (0:ℝ) (1/2) := ⟨_,hx.1.le,hx.2.le⟩
  rw [he,mem_enclosingUnitArc_iff_spectralEnclosingArcLength θ r]
  change _ ↔ HasProjectiveCircuitApproximation N ε 0 (unitaryEvolution H.val t)
  rw [zeroGateApproximation_iff_enclosingArc H t ⟨ε,hε.le,(hsmall.le.trans hroot)⟩]
  change spectralEnclosingArcLength θ ≤ 2*π*(physicalArc ε) ↔ spectralEnclosingArcLength θ ≤ 4*arcsin (ε/2)
  rw [show 2*π*physicalArc ε=4*arcsin (ε/2) by unfold physicalArc; field_simp; ring]

private theorem pair_rate_pos {I : Type*} [Fintype I] [Nontrivial I] (E : I → ℝ)
    (hi : MaximallyProjectiveEnergy E) : 0 < pairTurnRate E := by
  classical
  obtain ⟨i,j,hij⟩ := exists_pair_ne I
  have hx (b c : I) (he : E c < E b) : 0 < pairTurnRate E := by
    apply Finset.sum_pos' (fun p _ => div_nonneg (le_max_left _ _) (by positivity))
    exact ⟨(b,c),Finset.mem_univ _,div_pos ((sub_pos.mpr he).trans_le (le_max_right _ _)) (by positivity)⟩
  rcases lt_or_gt_of_ne (hi.injective.ne hij) with h | h
  · exact hx j i h
  · exact hx i j h

/-- For every tolerance and every fixed Gaussian prefix, positive-time
entry dates count the first visit following a genuine continuous absence.
The occupation divided by their count gives the mean time per visit. -/
theorem gaussian_empty_visit_flux :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let D := 2^N
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let E := fun j => -H.2.isHermitian.eigenvalues j
      ∀ ε : ℝ, 0<ε → ε<sqrt 2 →
        let x := physicalArc ε
        let F := entryDates E x
        let rate := x^(D-2)*pairTurnRate E
        (∀ t T, t∈F T ↔ 0<t ∧ t≤T ∧ t∈visitSet H 0 ε ∧
          ∃ d>0, ∀ u ∈ Ioo (t-d) t, u∉visitSet H 0 ε) ∧
        0<rate ∧ Tendsto (fun T : ℝ => ((F T).card:ℝ)/T) atTop (𝓝 rate) ∧
        Tendsto (fun T : ℝ => volume.real (visitSet H 0 ε ∩ Icc 0 T)/(F T).card) atTop
          (𝓝 ((D:ℝ)*x^(D-1)/rate)) := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω k
  intro N D H E ε hε hsmall x F rate
  have hi := maximallyProjectiveEnergy_neg (hω k)
  have hx := (physicalArc_spec hε hsmall).1
  have hdim : Fintype.card (Fin N → Bool)=D := by simp [D]
  have hh := entry_count_rate E hi hx.1 hx.2
  rw [hdim] at hh
  have hpos : 0<rate := mul_pos (pow_pos hx.1 _) (pair_rate_pos E hi)
  refine ⟨?_,hpos,hh,?_⟩
  · intro t T
    rw [mem_entryDates E hx.1.le hx.2]
    simp only [visitEntry,E,physical_visit H hε hsmall]
  · have hp := ShortTimeProducts.scalar_fraction H (hω k) hε hsmall 0
    have h := hp.div hh hpos.ne'
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    change volume.real (visitSet H 0 ε ∩ Icc 0 T)/(T-0)/(((F T).card:ℝ)/T) = _
    rw [sub_zero,div_div_div_cancel_right₀ hT.ne']

#print axioms gaussian_empty_visit_flux
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux
