import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnLevels.FirstContactOrder.WordAdvance
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.ContactStability.RationalOrder.FirstReturn

/-! # A shared first return forces high contact order for the larger budget -/

open Set Filter Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnLevels.FirstContactOrder
open LocalPatches (Register)
open PrecisionReturns (firstVisit firstVisit_isLeast)
open PhaseBoundary.FiniteCertificates
open PhaseBoundary.FiniteCertificates.ContactStability.RationalOrder
noncomputable section

/-- At any prescribed error the larger budget can fit already at the
origin. Otherwise its first contact has a rational order. If its first date
coincides with the smaller budget's, that order is at least the order of
the word purchased with the extra gates. -/
theorem tied_first_visit_order {n : ℕ} (x : PathShell n) (j s : ℕ) (a : ℝ) {e : ℝ} (he : 0 < e) :
    let H : selfAdjoint (Register (n+2)) := ⟨pathHamiltonian x,isSelfAdjoint_pathHamiltonian _⟩
    let S := s + 3^j*Fintype.card (PathLabel n)
    let d := orbitCircuitDistance H S
    let w := firstVisit H a S
    let v := w e
    v=a ∨ ∃ q p : ℕ, 0 < q ∧ q ≤ p ∧ ∃ c>0,
      Tendsto (fun t => (d t-e)^q/(v-t)^p) (𝓝[<] v) (𝓝 c) ∧
      Tendsto (fun u => (v-w u)^p/(u-e)^q) (𝓝[>] e) (𝓝 c⁻¹) ∧
      (v < firstVisit H a s e ∨ (j+2)*q ≤ p) := by
  intro H S d w v
  have hlarge := firstVisit_isLeast H a S he
  by_cases ha : e < d a
  · right
    obtain ⟨q,p,hq,hqp,c,hc,hd,hw⟩ := first_return_contact_order H S a he ha
    refine ⟨q,p,hq,hqp,c,hc,hd,hw,?_⟩
    have hs := firstVisit_isLeast H a s he
    obtain ⟨z,hz,C,hC,hfit⟩ := hs.1.2
    have hle : v ≤ firstVisit H a s e := hlarge.2 ⟨hs.1.1,z,hz,C,hC.trans (Nat.le_add_right ..),hfit⟩
    rcases hle.lt_or_eq with hlt|heq
    · exact Or.inl hlt
    right
    obtain ⟨hav,_,hpre⟩ := firstVisit_left_contact H S a he ha
    obtain ⟨B,hB⟩ := higher_increment x j
    have hsmall : orbitCircuitDistance H s v ≤ e := by
      rw [heq]
      exact (hasProjectiveCircuitApproximation_iff_infDist ..).mp hs.1.2
    apply order_ge_of_power_bound hc hd (K:=(B:ℝ))
    · filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (lt_mem_nhds hav)] with t htv hat
      exact sub_nonneg.mpr (hpre t ⟨hat,htv⟩).le
    · filter_upwards [self_mem_nhdsWithin] with t htv
      have h := hB s t v
      rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr htv.le)] at h
      exact sub_le_iff_le_add'.mpr (h.trans (add_le_add_right hsmall _))
  · exact Or.inl (le_antisymm (hlarge.2 ⟨le_rfl,(hasProjectiveCircuitApproximation_iff_infDist ..).mpr
      (le_of_not_gt ha)⟩) hlarge.1.1)

#print axioms tied_first_visit_order
end
end GaloisForLFunctions.HTGeometry.ReturnLevels.FirstContactOrder
