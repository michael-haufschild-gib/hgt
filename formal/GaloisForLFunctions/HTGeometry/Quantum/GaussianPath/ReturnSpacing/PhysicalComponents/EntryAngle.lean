import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.GaussianLaw
import GaloisForLFunctions.HTGeometry.ArcsineSeries

/-! # A genuine empty-circuit entry requires nearly one turn since any previous visit -/
open Matrix Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
open EmptyVisitFlux SharpOccupation
noncomputable section

/-- At every error up to 1/10, the entry pair must travel at least nine
tenths of a turn from any preceding affordable date. -/
theorem entry_angle {N : ℕ} (H : selfAdjoint (Register N)) {ε v w : ℝ} (hε : ε ∈ Ioc 0 (1/10)) (hvw : v<w)
    (hv : v ∈ visitSet H 0 ε) (hw : w ∈ visitSet H 0 ε)
    (hgap : ∃ δ : ℝ, 0<δ ∧ ∀ t ∈ Ioo (w-δ) w, t ∉ visitSet H 0 ε) :
    9*π/5 ≤ (w-v)*circuitHamiltonianSpectralWidth H := by
  let E := H.2.isHermitian.eigenvalues
  let f (i) := -E i/(2*π)
  let x := physicalArc ε
  have hsmall : ε<sqrt 2 := hε.2.trans_lt (by nlinarith only [sq_sqrt (show (0:ℝ)≤2 by norm_num),sqrt_nonneg 2])
  obtain ⟨hx,_⟩ := physicalArc_spec hε.1 hsmall
  have hvisit (t) : flow f t ∈ enclosingUnitArc x ↔ t ∈ visitSet H 0 ε := physical_visit H hε.1 hsmall t
  have he : visitEntry f x w := by
    obtain ⟨δ,hδ,h⟩ := hgap
    exact ⟨(hvisit w).2 hw,δ,hδ,fun t ht h' => h t ht ((hvisit t).1 h')⟩
  obtain ⟨i,j,hf⟩ := (entry_iff_closed_face f hx.1.le hx.2).mp he
  have ht := gap_before_contact f hx.1.le hvw ((hvisit v).2 hv) hf.1 hf.2.1
  have hx' : x ≤ 1/20 := by
    have h := GaloisForLFunctions.arcsin_le_pi_half_mul (ε/2) (half_pos hε.1).le (by linarith only [hε.2])
    change 2*arcsin (ε/2)/π ≤ 1/20
    rw [div_le_iff₀ pi_pos]
    have hprod := mul_le_mul_of_nonneg_right hε.2 pi_pos.le
    linarith only [h,hprod]
  have hE : E j-E i ≤ circuitHamiltonianSpectralWidth H :=
    sub_le_sub (Finset.le_sup' E (Finset.mem_univ j)) (Finset.inf'_le E (Finset.mem_univ i))
  have hscale : (w-v)*(f i-f j)*(2*π) = (w-v)*(E j-E i) := by
    dsimp only [f]
    field_simp
    ring
  have h₁ := mul_le_mul_of_nonneg_right ht (show 0 ≤ 2*π by positivity)
  rw [hscale] at h₁
  have h₂ := mul_le_mul_of_nonneg_left hE (sub_nonneg.mpr hvw.le)
  have h₃ := mul_le_mul_of_nonneg_right hx' pi_pos.le
  linarith only [h₁,h₂,h₃]

end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
