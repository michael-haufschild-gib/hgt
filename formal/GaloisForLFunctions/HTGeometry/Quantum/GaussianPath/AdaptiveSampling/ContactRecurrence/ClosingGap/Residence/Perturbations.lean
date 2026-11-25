import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactRecurrence.ClosingGap.Residence.Transport

/-! # Nonlinear spectral phase shifts throughout an empty-circuit visit -/

open Set
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.ClosingGap.Residence
open EmptyVisitFlux
noncomputable section
variable {I : Type*} [Fintype I] [Nonempty I]

/-- A scalar visit of duration h permits every midpoint phase shift
whose pairwise increments are bounded by h/2 times the energy spacings.
The linear shifts recover the entire original interval. -/
theorem residence_iff_lipschitz_shifts (w : I → ℝ) {r v h : ℝ} (hr : 0≤r) (hs : r<1/2) (hh : 0≤h) :
    (∀ u∈Icc (0:ℝ) h, flow w (v+u)∈enclosingUnitArc r) ↔
      ∀ f : I → ℝ, (∀ i j, |f i-f j|≤h/2*|w i-w j|) →
        (fun i => flow w (v+h/2) i+(f i:UnitAddCircle))∈enclosingUnitArc r := by
  constructor
  · intro hv f hf
    have hv0 := hv 0 ⟨le_rfl,hh⟩
    rw [add_zero] at hv0
    obtain ⟨y,b,hy,hw⟩ := (arc_iff_lifts _ hr).mp hv0
    have hend := end_span w hr hs hh hv hy hw
    let z (i : I) := y i+h/2*w i+f i
    refine (arc_iff_lifts _ hr).mpr ⟨z,b,?_,?_⟩
    · intro i
      simp only [z,AddCircle.coe_add,hy,flow]
      rw [add_mul,AddCircle.coe_add]
      abel
    · intro i j
      have ha := (abs_le.mp (hf i j)).2
      rcases le_total (w i) (w j) with hij|hji
      · rw [abs_of_nonpos (sub_nonpos.mpr hij)] at ha
        dsimp only [z]
        linarith only [hw i j,ha]
      · rw [abs_of_nonneg (sub_nonneg.mpr hji)] at ha
        dsimp only [z]
        linarith only [hend i j,ha]
  · intro hv u hu
    let f (i : I) := (u-h/2)*w i
    have hf (i j) : |f i-f j|≤h/2*|w i-w j| := by
      rw [show f i-f j=(u-h/2)*(w i-w j) by dsimp only [f]; ring,abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      exact abs_le.mpr ⟨by linarith only [hu.1],by linarith only [hu.2]⟩
    have he (i) : flow w (v+h/2) i+(f i:UnitAddCircle)=flow w (v+u) i := by
      simp only [flow,f,←AddCircle.coe_add]
      congr 1
      ring
    simpa only [he] using hv f hf

#print axioms residence_iff_lipschitz_shifts
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.ClosingGap.Residence
