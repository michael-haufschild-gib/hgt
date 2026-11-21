import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.Weyl

/-! # Sampling the other phases whenever one energy gap completes a turn -/
open MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux
noncomputable section
open AdaptiveSampling

/-- If one coordinate winds an integer number of turns per tick, that
coordinate is exactly the one to delete to recover a nonresonant clock. -/
theorem free_when_pinned {I : Type*} [Fintype I] [DecidableEq I] (ω : I → ℝ)
    (hi : RationallyIndependentFrequency ω) (b : I) {τ : ℝ} (hτ : τ ≠ 0)
    (l : ℤ) (hl : τ*ω b=(l:ℝ)*(2*Real.pi)) :
    FreeAtStep (fun j : {j : I // j≠b} => ω j) τ := by
  classical
  letI : Nonempty I := ⟨b⟩
  obtain ⟨s,hs⟩ := exists_free_deletion ω hi τ hτ
  by_cases he : s=b
  · exact he ▸ hs
  let j : {i : I // i ≠ s} := ⟨b,Ne.symm he⟩
  let c (i : {i : I // i ≠ s}) : ℤ := if i=j then 1 else 0
  have hdet : finiteTorusCharacterDetuning c (fun i : {i : I // i ≠ s} => ω i) = ω b := by
    unfold finiteTorusCharacterDetuning
    rw [Finset.sum_eq_single j (fun i _ hij => by simp only [c,if_neg hij,Int.cast_zero,zero_mul])
      (fun hj => (hj (Finset.mem_univ j)).elim)]
    simp only [c,if_pos rfl,Int.cast_one,one_mul]
  have hz := hs c l (hdet.symm ▸ hl)
  have hfalse := congrFun hz j
  simp [c] at hfalse

/-- Exact relative-phase sampling law on every arithmetic clock that
marks the prescribed phase of one nonzero coordinate. -/
theorem pinned_phase_law {I : Type*} [Fintype I] [DecidableEq I] (ω : I → ℝ)
    (hi : RationallyIndependentFrequency ω) (b : I) {τ : ℝ} (hτ : τ ≠ 0)
    (l : ℤ) (hl : τ*ω b=(l:ℝ)*(2*Real.pi)) (a : ℝ) :
    Tendsto (integerClockPrefixLaw (fun k : ℕ => finiteClockPhasePoint
      (fun j : {j : I // j ≠ b} => ω j) (a+(k:ℝ)*τ))) atTop
      (𝓝 (finiteTorusHaarProbabilityMeasure {j : I // j ≠ b})) :=
  affine_phaseLaw _ τ a (free_when_pinned ω hi b hτ l hl)

#print axioms free_when_pinned
#print axioms pinned_phase_law
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux
