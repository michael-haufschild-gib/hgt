import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ShortArcHaar

/-! # Energy bands at the earliest scalar return from an extremal antipode -/

open Real Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.FiniteWindings
noncomputable section

/-- The extremal pair pins the phase interval to [0,x]. At its first
closing date the normalized energy y has phase -(M-x)y turns. -/
def closingBand (M : ℕ) (x y : ℝ) : Prop :=
  ((-(((M:ℝ)-x)*y):ℝ):UnitAddCircle)∈forwardUnitArc x

theorem closingBand_iff (M : ℕ) (x y : ℝ) :
    closingBand M x y ↔ ∃ k : ℤ, ((M:ℝ)-x)*y∈Icc ((k:ℝ)-x) k := by
  let z := ((M:ℝ)-x)*y
  constructor
  · rintro ⟨u,hu,he⟩
    change (u:UnitAddCircle)=((-z:ℝ):UnitAddCircle) at he
    have hzero : ((z+u:ℝ):UnitAddCircle)=0 := by
      rw [AddCircle.coe_add,he,AddCircle.coe_neg,add_neg_cancel]
    obtain ⟨k,hk⟩ := (AddCircle.coe_eq_zero_iff 1).mp hzero
    rw [zsmul_eq_mul,mul_one] at hk
    change ∃ k : ℤ, z∈Icc ((k:ℝ)-x) k
    exact ⟨k,by linarith only [hk,hu.2],by linarith only [hk,hu.1]⟩
  · rintro ⟨k,hk⟩
    change z∈Icc ((k:ℝ)-x) k at hk
    have hz : (((k:ℝ):UnitAddCircle))=0 := (AddCircle.coe_eq_zero_iff 1).mpr ⟨k,by simp⟩
    refine ⟨(k:ℝ)-z,⟨sub_nonneg.mpr hk.2,by linarith only [hk.1]⟩,?_⟩
    change (((k:ℝ)-z:ℝ):UnitAddCircle)=((-z:ℝ):UnitAddCircle)
    rw [AddCircle.coe_sub,hz,zero_sub,AddCircle.coe_neg]

/-- Every strictly interior energy that fits the closing arc is separated
from both extremal energies by at least (1-x)/(M-x) of the spectral width. -/
theorem closingBand_edge_gaps {M : ℕ} {x y : ℝ} (hM : x<(M:ℝ)) (hy : y∈Ioo (0:ℝ) 1)
    (h : closingBand M x y) :
    (1-x)/((M:ℝ)-x)≤y ∧ (1-x)/((M:ℝ)-x)≤1-y := by
  obtain ⟨k,hk⟩ := (closingBand_iff M x y).mp h
  have hp := sub_pos.mpr hM
  have hpos : (0:ℝ)<k := (mul_pos hp hy.1).trans_le hk.2
  have hlt : (k:ℝ)<M := by
    have hh := mul_lt_mul_of_pos_left hy.2 hp
    rw [mul_one] at hh
    linarith only [hh,hk.1]
  have hpos' : (0:ℤ)<k := by exact_mod_cast hpos
  have hlt' : k<(M:ℤ) := by exact_mod_cast hlt
  have hlo : (1:ℝ)≤k := by exact_mod_cast (show (1:ℤ)≤k by omega)
  have hhi : (k:ℝ)≤(M:ℝ)-1 := by exact_mod_cast (show k≤(M:ℤ)-1 by omega)
  constructor <;> apply (div_le_iff₀ hp).mpr
  · linarith only [hk.1,hlo]
  · linarith only [hk.2,hhi]

/-- Strict interior lattice levels have an explicit clearance from both
ends of their closing band. This also allows perturbing their energies. -/
theorem closingBand_of_lattice_near {M j : ℕ} (hj : 0<j) (hjM : j<M)
    {x y : ℝ} (hx : 0≤x)
    (h : |((M:ℝ)-x)*y-((j:ℝ)-x*j/M)|≤x/M) : closingBand M x y := by
  have hM : (0:ℝ)<M := Nat.cast_pos.mpr (hj.trans hjM)
  have hj₁ : (1:ℝ)≤j := by exact_mod_cast hj
  have hj₂ : (j:ℝ)+1≤M := by exact_mod_cast Nat.succ_le_of_lt hjM
  have hlo : x/M≤x*j/M := div_le_div_of_nonneg_right (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hj₁ hx) hM.le
  have hhi : x*j/M+x/M≤x := by
    rw [←add_div,div_le_iff₀ hM]
    linarith only [mul_le_mul_of_nonneg_left hj₂ hx]
  apply (closingBand_iff M x y).mpr
  refine ⟨(j:ℤ),?_⟩
  simp only [Int.cast_natCast]
  exact ⟨by linarith only [(abs_le.mp h).1,hhi],by linarith only [(abs_le.mp h).2,hlo]⟩

#print axioms closingBand_iff
#print axioms closingBand_edge_gaps
#print axioms closingBand_of_lattice_near
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.FiniteWindings
