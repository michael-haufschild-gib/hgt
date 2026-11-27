import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.Physical.CapMass
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Subregister.ApproximateProduct
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.SingleCut.HalfBudget

/-! # Cheap increments through a weak seam between two capped physical blocks -/
open Matrix Set Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
open FirstAscent.ThermodynamicEdges PrescribedTimes
open private polynomial_room from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.SingleCut.HalfBudget
noncomputable section

/-- The sum of the two linear-in-dimension child caps fits below half
the original near-Hilbert crossing budget. -/
theorem balanced_increment_budget (l r : ℕ) (hl : l ≤ r) (hr : r ≤ l+1) (hlarge : 128 ≤ l+2) :
    2*(213*2^(l+2)+213*2^(r+2)) ≤ nearHilbertContinuousCircuitBudget (l+r+4) := by
  let h := l+2
  have hg := polynomial_room h (by dsimp only [h]; omega)
  have hr' : 2^(r+2) ≤ 2^h*2 := (Nat.pow_le_pow_right (by decide : 0 < 2) (by dsimp only [h]; omega : r+2 ≤ h+1)).trans_eq (pow_succ _ _)
  have hreg : l+r+4+1 ≤ 2*h+2 := by dsimp only [h]; omega
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 64*(l+r+4+1))).mpr
  calc _ ≤ (2*(213*2^h+213*(2^h*2)))*(64*(2*h+2)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.add_le_add_left (Nat.mul_le_mul_left _ hr') _))
            (Nat.mul_le_mul_left _ hreg)
       _ = (81792*(2*h+2))*2^h := by ring
       _ ≤ (4096*(h+2)^2)*2^h := by
          apply Nat.mul_le_mul_right
          have hh : 128 ≤ h := hlarge
          nlinarith only [hh,Nat.mul_le_mul_left h hh]
       _ ≤ 2^h*2^h := Nat.mul_le_mul_right _ hg
       _ = 2^(h+h) := (pow_add ..).symm
       _ ≤ 2^(l+r+4) := Nat.pow_le_pow_right (by decide) (by dsimp only [h]; omega)

/-- Uniform child approximations cost 1/200 together. The deleted
seam contributes at most another 1/200 over the signed lag window. -/
theorem capped_increment (l r : ℕ) (x : PathLabel (l+r+2)→ℝ) {T : ℝ} (hT : 0 < T)
    (hblocks : (extractBlocks l r x).1 ∈ capEvent l (1/400) ×ˢ capEvent r (1/400))
    (hseam : ∀ i, |(extractBlocks l r x).2 i| ≤ 1/(1800*T)) (t : ℝ) (ht : |t| ≤ T) :
    HasProjectiveCircuitApproximation (l+r+4) (1/100) (213*2^(l+2)+213*2^(r+2))
      (unitaryEvolution (pathHamiltonian (WithLp.toLp 2 x : PathShell (l+r+2))) t) := by
  let m := l+r+2
  let u : PathShell m := WithLp.toLp 2 x
  let S := intervalWires (m+2) 0 (l+2)
  let R := intervalWires (m+2) (l+2) (r+2)
  have hST : Disjoint S R := by
    apply Finset.disjoint_left.mpr
    intro i hs hr
    have h₁ := (mem_filter.mp hs).2.2
    have h₂ := (mem_filter.mp hr).2.1
    omega
  let e := numberWires (B:=0) (m:=l) (n:=m) (by dsimp only [m]; omega)
  let f := numberWires (B:=l+2) (m:=r) (n:=m) (by dsimp only [m]; omega)
  let A : PathShell l := WithLp.toLp 2 (extractBlocks l r x).1.1
  let B : PathShell r := WithLp.toLp 2 (extractBlocks l r x).1.2
  have hfit {n : ℕ} (v : PathShell n) (h : (fun i => v i) ∈ capEvent n (1/400)) :
      HasProjectiveCircuitApproximation (n+2) (1/400) (213*2^(n+2)) (unitaryEvolution (pathHamiltonian v) t) := by
    have hh := h t
    change pathGateDistance n _ (fun i => v (pathCoeffEquiv n i)) t ≤ _ at hh
    rw [pathGateDistance,numberedGenerator_shell] at hh
    exact (hasProjectiveCircuitApproximation_iff_infDist ..).mpr hh
  obtain ⟨z,hz,C,hC,he⟩ := Subregister.disjoint_evolution_approximation e f hST
    ⟨_,isSelfAdjoint_pathHamiltonian A⟩ ⟨_,isSelfAdjoint_pathHamiltonian B⟩ t
    (hfit A hblocks.1) (hfit B hblocks.2)
  have hsum : IsSelfAdjoint (blockSum l r x) := (isHermitian_liftLocalMatrix S
    (isHermitian_reindex _ (isSelfAdjoint_pathHamiltonian A).isHermitian)).add
    (isHermitian_liftLocalMatrix R (isHermitian_reindex _ (isSelfAdjoint_pathHamiltonian B).isHermitian)) |>.isSelfAdjoint
  have h := norm_unitaryEvolution_sub_le _ _ (isSelfAdjoint_pathHamiltonian u) hsum t
  rw [norm_sub_rev (pathHamiltonian u) (blockSum l r x)] at h
  have h₁ := h.trans (mul_le_mul ht (seam_error l r x hseam) (norm_nonneg _) hT.le)
  have hc : T*(9*(1/(1800*T)))=(1/200:ℝ) := by field_simp; ring
  rw [hc] at h₁
  exact ⟨z,hz,C,hC,(norm_sub_le_norm_sub_add_norm_sub _ (unitaryEvolution (blockSum l r x) t) _).trans
    ((add_le_add h₁ he).trans_eq (by norm_num))⟩

#print axioms balanced_increment_budget
#print axioms capped_increment
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
