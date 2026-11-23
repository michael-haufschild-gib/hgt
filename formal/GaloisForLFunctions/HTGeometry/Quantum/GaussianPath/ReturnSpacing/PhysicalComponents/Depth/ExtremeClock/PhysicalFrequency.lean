import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.ExtremeClock.BoxFrequency
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.ExtremeClock.FirstCell

/-! # Maximum residence after the physical first crossing has a positive clock frequency -/
open Filter MeasureTheory Finset Set Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux.ExtremeClock
open SharpOccupation
noncomputable section

/-- At the ticks aligning the extreme phases after the first crossing,
the entire maximum-duration interval is affordable at a strictly positive
frequency. Each spectator contributes its own exact angular width. -/
theorem gaussian_maximum_cell_frequency :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let w := fun i => -H.2.isHermitian.eigenvalues i/(2*π)
      ∃ σ>0, orbitCircuitDistance H P σ=9/80 ∧ (∀ t∈Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        ∃ p q, ∃ he : w q < w p, (∀ i, w q≤w i ∧ w i≤w p) ∧
          let W := w p-w q
          let θ := fun i => (w i-w q)/W
          let b : {i // i≠q} := ⟨p,fun h => he.ne (congrArg w h.symm)⟩
          ∀ ε∈Ioo (0:ℝ) (sqrt 2), let r := physicalArc ε
            let shift := ⌊σ*W+r⌋₊+1
            let mass := ∏ i : {j : {i // i≠q} // j≠b}, 2*(r*min (θ i.val.val) (1-θ i.val.val))
            0 < mass ∧ Tendsto (fun M : ℕ => (countTicks (fun m =>
              ∀ z∈Icc (-r) r, (((shift+m:ℕ):ℝ)+z)/W∈visitSet H 0 ε) (M+1):ℝ)/(M+1))
              atTop (𝓝 mass) := by
  filter_upwards [gaussian_first_return_cell,gaussian_path_all_prefixes_maximally_projective] with ω hw hi
  filter_upwards [hw] with k hk
  intro N H P w
  obtain ⟨σ,hσ,hc,hb,p,q,he,hspan,_⟩ := hk
  refine ⟨σ,hσ,hc,hb,p,q,he,hspan,?_⟩
  intro W θ b ε hε r shift mass
  let E := fun i => -H.2.isHermitian.eigenvalues i
  have hE : MaximallyProjectiveEnergy E := maximallyProjectiveEnergy_neg (hi k)
  have hπ : 0<2*π := by positivity
  have hpq : E q < E p := (div_lt_div_iff_of_pos_right hπ).mp he
  have bound (i) : E q≤E i ∧ E i≤E p :=
    ⟨(div_le_div_iff_of_pos_right hπ).mp (hspan i).1,(div_le_div_iff_of_pos_right hπ).mp (hspan i).2⟩
  have hr : r∈Ioo (0:ℝ) (1/2) := (physicalArc_spec hε.1 hε.2).1
  have hW : 0<W := sub_pos.mpr he
  have hθ : (fun i => (E i-E q)/(E p-E q))=θ := by
    funext i
    change _=(E i/(2*π)-E q/(2*π))/(E p/(2*π)-E q/(2*π))
    rw [←sub_div,←sub_div,div_div_div_cancel_right₀ hπ.ne']
  have hp : θ p=1 := div_self hW.ne'
  have hq : θ q=0 := by simp only [θ,sub_self,zero_div]
  have hne (i j) (h : i≠j) : w i≠w j := fun hh =>
    h (hE.injective ((div_left_inj' hπ.ne').mp hh))
  constructor
  · apply prod_pos
    intro i _
    have h₁ := lt_of_le_of_ne (hspan i.val.val).1 (hne q i.val.val i.val.property.symm)
    have h₂ := lt_of_le_of_ne (hspan i.val.val).2 (hne i.val.val p (fun he => i.property (Subtype.ext he)))
    have hpos : 0 < θ i.val.val := div_pos (sub_pos.mpr h₁) hW
    have hone : θ i.val.val < 1 := (div_lt_one hW).mpr (sub_lt_sub_right h₂ _)
    exact mul_pos two_pos (mul_pos hr.1 (lt_min hpos (sub_pos.mpr hone)))
  · have hfreq := maximum_cell_frequency E hE p q hpq bound shift hr
    rw [hθ] at hfreq
    have eqTest (m : ℕ) : (∀ z∈Icc (-r) r, (((shift+m:ℕ):ℝ)+z)/W∈visitSet H 0 ε) ↔
        offsets θ ((shift+m:ℕ):ℤ) r=Icc (-r) r := by
      have hh (z) (hz : z∈Icc (-r) r) :
          (((shift+m:ℕ):ℝ)+z)/W∈visitSet H 0 ε ↔ z∈offsets θ ((shift+m:ℕ):ℤ) r := by
        rw [←physical_visit H hε.1 hε.2]
        exact_mod_cast visit_iff_offsets w p q he hspan hr.1.le hr.2 ((shift+m:ℕ):ℤ)
          (show z∈Ico (-(1/2):ℝ) (1/2) from ⟨(neg_le_neg hr.2.le).trans hz.1,hz.2.trans_lt hr.2⟩)
      constructor
      · intro h
        exact Subset.antisymm (offsets_bound hp hq _ _) (fun z hz => (hh z hz).mp (h z hz))
      · intro h z hz
        exact (hh z hz).mpr (h.symm ▸ hz)
    simpa only [funext (fun m => propext (eqTest m))] using hfreq

#print axioms gaussian_maximum_cell_frequency
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux.ExtremeClock
