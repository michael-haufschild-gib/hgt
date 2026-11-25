import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactRecurrence.ClosingGap.PreviousContact
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactRecurrence.PhysicalClock

/-! # An elapsed first-wait bound from the terminal spectral configuration -/

open Finset Set Filter Real MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.ClosingGap
open EmptyVisitFlux PrecisionReturns
noncomputable section

/-- The age in units of the closing-gap period is strictly less than
the product of inverse interior clearances rounded upward. -/
def clearanceBound {I : Type} [Fintype I] [DecidableEq I] (w : I → ℝ) (r v a : ℝ) : Prop :=
  ∃ i j, inwardFace w r v i j ∧ ∃ y : InteriorLevel i j → ℝ,
    (∀ k, y k∈Ioo 0 r ∧ (y k:UnitAddCircle)=flow w v k.val-flow w v i) ∧
    (v-a)*(w i-w j)<((∏ k, ⌈1/min (y k) (r-y k)⌉₊ : ℕ):ℝ)

/-- On every typical prefix the spectral clearance bound holds
simultaneously from all positive outside origins at each prescribed error. -/
theorem gaussian_scalar_wait_clearance (ε : ℝ) (hε : 0<ε) (hs : ε<sqrt 2) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let w (j : Fin N → Bool) := -H.2.isHermitian.eigenvalues j/(2*π)
      ∀ a > (0:ℝ), ε<orbitCircuitDistance H 0 a →
        clearanceBound w (SharpOccupation.physicalArc ε) (firstVisit H a 0 ε) a := by
  filter_upwards [EntrySensitivity.gaussian_first_empty_inward_face ε hε hs] with ω hω k
  intro N H w a ha hout
  let v := firstVisit H a 0 ε
  let r := SharpOccupation.physicalArc ε
  obtain ⟨i,j,hf⟩ := hω k a ha hout
  have hints (k : InteriorLevel i j) : ∃ t∈Ioo 0 r, (t:UnitAddCircle)=flow w v k.val-flow w v i :=
    hf.2.2 k.val k.property.1 k.property.2
  choose y hy he using hints
  let m (k : InteriorLevel i j) := min (y k) (r-y k)
  let Q (k : InteriorLevel i j) := ⌈1/m k⌉₊
  have hm (k : InteriorLevel i j) : 0 < m k := lt_min (hy k).1 (sub_pos.mpr (hy k).2)
  have hQ (k) : 0<Q k := Nat.ceil_pos.mpr (one_div_pos.mpr (hm k))
  have Hm (k) : 1/(Q k:ℝ) ≤ m k := by
    rw [div_le_iff₀ (Nat.cast_pos.mpr (hQ k)),mul_comm]
    exact (div_le_iff₀ (hm k)).mp (Nat.le_ceil (1/m k))
  obtain ⟨q,hq,hb,hprev⟩ := previous_contact w (SharpOccupation.physicalArc_spec hε hs).1.1 hf y he Q hQ Hm
  let t := (q:ℝ)/(w i-w j)
  have hg : 0<w i-w j := sub_pos.mpr hf.1
  have ht : 0<t := div_pos (Nat.cast_pos.mpr hq) hg
  have hback := (physical_visit H hε hs (v-t)).mp (mem_iUnion.mpr ⟨i,hprev⟩)
  have hbefore : v-t<a := by
    by_contra! h
    exact (sub_lt_self v ht).not_ge ((firstVisit_isLeast H a 0 hε).2 ⟨h,hback⟩)
  refine ⟨i,j,hf,y,fun k => ⟨hy k,he k⟩,?_⟩
  have hwidth : v-a<t := by linarith only [hbefore]
  exact ((lt_div_iff₀ hg).mp hwidth).trans_le (Nat.cast_le.mpr hb)

/-- At error one tenth this bounds the actual elapsed wait from the
first robust crossing of the near-Hilbert circuit budget. -/
theorem gaussian_first_crossing_wait_clearance :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let w (j : Fin N → Bool) := -H.2.isHermitian.eigenvalues j/(2*π)
      ∃ σ > (0:ℝ), orbitCircuitDistance H P σ=9/80 ∧
        (∀ t∈Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
        clearanceBound w (SharpOccupation.physicalArc (1/10)) (firstVisit H σ 0 (1/10)) σ := by
  have hs : (1/10:ℝ)<sqrt 2 := by nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg 2]
  filter_upwards [gaussian_scalar_wait_clearance (1/10) (by norm_num) hs,
    gaussian_unshifted_first_excursion_tick_gaps] with ω hh hc
  filter_upwards [hc] with k hk
  intro N H P w
  obtain ⟨σ,hσ,hc,hb,_⟩ := hk
  refine ⟨σ,hσ,hc,hb,hh k σ hσ ?_⟩
  by_contra! h
  obtain ⟨z,hz,C,hC,he⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ 0 (1/10:ℝ)).mpr h
  have hle : orbitCircuitDistance H P σ≤1/10 := (hasProjectiveCircuitApproximation_iff_infDist ..).mp
    ⟨z,hz,C,hC.trans (Nat.zero_le _),he⟩
  rw [hc] at hle
  norm_num at hle

#print axioms gaussian_first_crossing_wait_clearance
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.ClosingGap
