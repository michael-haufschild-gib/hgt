import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralEnclosingArc

/-! # Optimal division of a spectral arc between two observation dates -/
open Real Set
namespace GaloisForLFunctions.HTGeometry.SpectralArcs
noncomputable section
variable {I : Type*} [Fintype I] [Nonempty I]

/-- Lifting a shortest enclosing arc at its midpoint divides the angular
cost in any prescribed proportion, with one common scalar at each end. -/
theorem split_arc (θ : I → ℝ) {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) :
    ∃ (ψ : I → ℝ) (c : ℝ), ∀ i,
      circDist (ψ i) 0 ≤ r*(spectralEnclosingArcLength θ/2) ∧
      circDist (ψ i+θ i) c ≤ (1-r)*(spectralEnclosingArcLength θ/2) := by
  obtain ⟨c,hc⟩ := exists_spectralEnclosingArc_center θ
  let d (i : I) := phaseGap (θ i) c
  let ψ (i : I) := -(r*d i)
  refine ⟨ψ,c,fun i => ?_⟩
  have hd : |d i| ≤ spectralEnclosingArcLength θ/2 := hc i
  obtain ⟨k,hk⟩ := exists_int_phaseGap (θ i) c
  change d i=θ i-c+2*π*(k:ℝ) at hk
  constructor
  · apply (circDist_le (ψ i) 0 0).trans
    simpa only [Int.cast_zero,mul_zero,add_zero,sub_zero,ψ,abs_neg,abs_mul,abs_of_nonneg hr.1]
      using mul_le_mul_of_nonneg_left hd hr.1
  · apply (circDist_le (ψ i+θ i) c k).trans
    have he : ψ i+θ i-c+2*π*(k:ℝ)=(1-r)*d i := by dsimp only [ψ]; linarith only [hk]
    rw [he,abs_mul,abs_of_nonneg (sub_nonneg.mpr hr.2)]
    exact mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr hr.2)

/-- The two enclosing lengths cannot sum to less than that of their
lag, regardless of the chosen starting phase configuration. -/
theorem lag_arc_le_sum (θ ψ : I → ℝ) : spectralEnclosingArcLength θ ≤
    spectralEnclosingArcLength ψ+spectralEnclosingArcLength (fun i => ψ i+θ i) := by
  let χ (i : I) := ψ i+θ i
  obtain ⟨a,ha⟩ := exists_spectralEnclosingArc_center ψ
  obtain ⟨b,hb⟩ := exists_spectralEnclosingArc_center χ
  let R := spectralEnclosingArcLength ψ/2+spectralEnclosingArcLength χ/2
  have hθ (i : I) : circDist (θ i) (b-a) ≤ R := by
    obtain ⟨j,hj⟩ := exists_int_phaseGap (ψ i) a
    obtain ⟨k,hk⟩ := exists_int_phaseGap (χ i) b
    apply (circDist_le _ _ (k-j)).trans
    have he : θ i-(b-a)+2*π*((k-j:ℤ):ℝ)=phaseGap (χ i) b-phaseGap (ψ i) a := by
      rw [hj,hk]
      dsimp only [χ]
      push_cast
      ring
    rw [he]
    exact (abs_sub _ _).trans ((add_le_add (hb i) (ha i)).trans_eq (add_comm ..))
  exact (spectralEnclosingArcLength_le_twice_radius θ (b-a) R hθ).trans_eq (by dsimp only [R,χ]; ring)

/-- Half the enclosing arc length of the lag is the attained minimum of
the larger enclosing length at two dates in the full phase torus. -/
theorem half_arc_isLeast (θ : I → ℝ) : IsLeast
    (range (fun ψ : I → ℝ => max (spectralEnclosingArcLength ψ)
      (spectralEnclosingArcLength (fun i => ψ i+θ i)))) (spectralEnclosingArcLength θ/2) := by
  have hl (ψ : I → ℝ) : spectralEnclosingArcLength θ/2 ≤ max (spectralEnclosingArcLength ψ)
      (spectralEnclosingArcLength (fun i => ψ i+θ i)) := by
    let a := spectralEnclosingArcLength ψ
    let b := spectralEnclosingArcLength (fun i => ψ i+θ i)
    have h : spectralEnclosingArcLength θ ≤ a+b := lag_arc_le_sum θ ψ
    linarith only [h,le_max_left a b,le_max_right a b]
  obtain ⟨ψ,c,hψ⟩ := split_arc θ (r:=1/2) (by constructor <;> norm_num)
  have h₁ := spectralEnclosingArcLength_le_twice_radius ψ 0 _ (fun i => (hψ i).1)
  have h₂ := spectralEnclosingArcLength_le_twice_radius (fun i => ψ i+θ i) c _ (fun i => (hψ i).2)
  exact ⟨⟨ψ,le_antisymm (max_le (by linarith only [h₁]) (by linarith only [h₂])) (hl ψ)⟩,
    fun y ⟨v,hv⟩ => hv ▸ hl v⟩

#print axioms half_arc_isLeast
end
end GaloisForLFunctions.HTGeometry.SpectralArcs
