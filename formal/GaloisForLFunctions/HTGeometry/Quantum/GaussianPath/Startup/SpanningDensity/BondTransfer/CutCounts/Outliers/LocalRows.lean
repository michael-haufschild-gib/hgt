import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Disorder.Rows.Incidence
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.Calibration.RotatedDraw

/-! # Local coefficient outliers in the two physical Pauli frames -/
open Finset
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open WeakBondDeficit
open private wordSign abs_sign from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Frames.RotatedShell
noncomputable section
variable {n : ℕ}

/-- Path coefficients whose magnitude exceeds the local transfer cap. -/
def largeLabels (u : PathShell n) (B : ℝ) :=
  univ.filter fun l : PathLabel n => B < |u l|

private def nearRow (n r : ℕ) :=
  univ.filter fun e : Fin (n+1) => r≤e.val+1 ∧ e.val≤r+1

/-- A large coordinate can spoil transfer on at most three central edges. -/
def exceptionalEdges (u : PathShell n) (B : ℝ) :=
  (largeLabels u B).biUnion fun l => nearRow n (pathPauliSourceCoordinate l).1

theorem exceptionalEdges_card (u : PathShell n) (B : ℝ) :
    (exceptionalEdges u B).card≤3*(largeLabels u B).card := by
  classical
  have hrow (r : ℕ) : (nearRow n r).card≤3 := by
    have hsub : (nearRow n r).image Fin.val⊆Finset.Ico (r-1) (r+2) := by
      intro v hv
      obtain ⟨e,he,rfl⟩ := mem_image.mp hv
      have h := (mem_filter.mp he).2
      exact mem_Ico.mpr ⟨by omega,by omega⟩
    have h := Finset.card_le_card hsub
    rw [card_image_of_injective _ Fin.val_injective,Nat.card_Ico] at h
    omega
  apply (Finset.card_biUnion_le ..).trans
  apply (sum_le_sum (fun l (_ : l∈largeLabels u B) => hrow (pathPauliSourceCoordinate l).1)).trans_eq
  simp only [sum_const,smul_eq_mul,mul_comm]

private theorem cap_at_row (u : PathShell n) {B : ℝ} {e : Fin (n+1)} (he : e∉exceptionalEdges u B)
    (l : PathLabel n) (hl : (pathPauliSourceCoordinate l).1≤e.val+1 ∧
      e.val≤(pathPauliSourceCoordinate l).1+1) : |u l|≤B := by
  by_contra! hh
  exact he (mem_biUnion.mpr ⟨l,mem_filter.mpr ⟨mem_univ _,hh⟩,mem_filter.mpr ⟨mem_univ _,hl⟩⟩)

/-- Rotating the Pauli axes only permutes coordinates within their own
source row, so a nonexceptional edge retains its cap in both frames. -/
theorem rotated_cap_at_row (a : Fin (n+2)→Fin 3) (u : PathShell n) {B : ℝ} {e : Fin (n+1)}
    (he : e∉exceptionalEdges u B) (l : PathLabel n)
    (hl : (pathPauliSourceCoordinate l).1≤e.val+1 ∧ e.val≤(pathPauliSourceCoordinate l).1+1) :
    |rotatedShell a u l|≤B := by
  rcases l with ⟨v,q⟩|⟨r,q⟩
  · change |wordSign a _*u _|≤B
    rw [abs_mul,abs_sign,one_mul]
    exact cap_at_row u he _ hl
  · rw [rotated_bond_magnitude]
    exact cap_at_row u he _ hl

#print axioms exceptionalEdges_card
#print axioms rotated_cap_at_row
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
