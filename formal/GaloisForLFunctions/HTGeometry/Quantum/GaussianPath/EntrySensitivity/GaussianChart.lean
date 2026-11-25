import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EntrySensitivity.StableFace
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.FirstVisit

/-! # Exact local energy-gap law for the first Gaussian empty return -/
open Matrix MeasureTheory Filter Set Topology Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EntrySensitivity
noncomputable section
open EmptyVisitFlux PrecisionReturns FirstGate
private abbrev State (n : ℕ) := Fin n→Bool

private theorem regular_contact {I : Type*} [Fintype I] {E : I→ℝ} {r t : ℝ} {i j : I}
    (hi : Function.Injective E) (hpos : AvoidsTie E r) (hneg : AvoidsTie E (-r))
    (ht : 0 < t) (h : pairFace (forwardUnitArc r) (fun k => E k/(2*π)) r t i j) :
    inwardFace (fun k => E k/(2*π)) r t i j := by
  let w (k : I) := E k/(2*π)
  have hji : j≠i := fun hji => h.1.ne (congrArg w hji)
  have hreverse : flow w t i-flow w t j=((-r:ℝ):UnitAddCircle) := by
    rw [AddCircle.coe_neg,←h.2.1,neg_sub]
  refine ⟨h.1,h.2.1,?_⟩
  intro k hki hkj
  obtain ⟨x,hx,he⟩ := h.2.2 k hki hkj
  have hlo : x≠0 := by
    intro hz
    have he0 : flow w t k-flow w t i=0 := by rw [←he,hz,AddCircle.coe_zero]
    exact simple_contact E hi hpos ht i k j hki.symm hji hkj.symm h.2.1 (sub_eq_zero.mp he0)
  have hhi : x≠r := by
    intro hx'
    have ht' : flow w t k-flow w t i=flow w t j-flow w t i := by rw [←he,hx',h.2.1]
    exact simple_contact E hi hneg ht j k i hkj.symm hji.symm hki.symm hreverse (sub_left_inj.mp ht')
  exact ⟨x,⟨lt_of_le_of_ne hx.1 hlo.symm,lt_of_le_of_ne hx.2 hhi⟩,he⟩

/-- At a prescribed tolerance, every first scalar visit from a positive
outside origin lies on a face with just two endpoint levels. -/
theorem gaussian_first_empty_inward_face (ε : ℝ) (hε : 0 < ε) (hs : ε < sqrt 2) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let w (j : State N) := -H.2.isHermitian.eigenvalues j/(2*π)
      ∀ a > (0:ℝ), ε < orbitCircuitDistance H 0 a →
        ∃ i j : State N, inwardFace w (SharpOccupation.physicalArc ε) (firstVisit H a 0 ε) i j := by
  filter_upwards [gaussian_fixed_contacts (SharpOccupation.physicalArc ε),
    gaussian_path_all_prefixes_maximally_projective] with ω hties hind k
  intro N H w a ha hout
  obtain ⟨hav,hentry⟩ := first_empty_entry_of_outside H hε hs hout
  have hx := (SharpOccupation.physicalArc_spec hε hs).1
  obtain ⟨i,j,hface⟩ := (entry_iff_closed_face w hx.1.le hx.2).mp hentry
  exact ⟨i,j,regular_contact (maximallyProjectiveEnergy_neg (hind k)).injective
    (hties k).1 (hties k).2 (ha.trans hav) hface⟩

/-- At every positive outside origin, the first scalar return is locally
a reciprocal of one spectral gap in the full space of labeled phase
velocities. The same pair works for every nearby perturbation. -/
theorem gaussian_first_empty_gap_chart (ε : ℝ) (hε : 0 < ε) (hs : ε < sqrt 2) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let w (j : State N) := -H.2.isHermitian.eigenvalues j/(2*π)
      let r := SharpOccupation.physicalArc ε
      ∀ a > (0:ℝ), ε < orbitCircuitDistance H 0 a →
        let v := firstVisit H a 0 ε
        ∃ i j : State N, w j < w i ∧ ∀ᶠ w' : State N→ℝ in 𝓝 w,
          IsLeast {t : ℝ | a ≤ t ∧ flow w' t∈enclosingUnitArc r} (v*(w i-w j)/(w' i-w' j)) := by
  filter_upwards [gaussian_first_empty_inward_face ε hε hs] with ω hω
  intro k N H w r a ha hout v
  have hav := (first_empty_entry_of_outside H hε hs hout).1
  have hx := (SharpOccupation.physicalArc_spec hε hs).1
  obtain ⟨i,j,hreg⟩ := hω k a ha hout
  refine ⟨i,j,hreg.1,first_face_stable hx.1.le hx.2 hav hreg ?_⟩
  intro t ht hf
  exact ht.2.not_ge ((firstVisit_isLeast H a 0 hε).2 ⟨ht.1,(physical_visit H hε hs t).mp hf⟩)

#print axioms gaussian_first_empty_gap_chart
end
end GaloisForLFunctions.HTGeometry.EntrySensitivity
