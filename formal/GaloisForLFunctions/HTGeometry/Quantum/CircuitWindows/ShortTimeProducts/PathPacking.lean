import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ShortTimeProducts.ShiftPacking
import GaloisForLFunctions.HTGeometry.Quantum.SparsePathCircuitCompiler

/-! # Finite-window occupation gain from one path product step -/
open Matrix MeasureTheory Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ShortTimeProducts
noncomputable section
open SharpOccupation

private theorem width_bound {N : ℕ} (H : selfAdjoint (Register N)) (t : ℝ)
    (h : |t| *circuitHamiltonianSpectralWidth H ≤ π) :
    |t| *circuitHamiltonianSpectralWidth H/π ≤ orbitCircuitDistance H 0 t := by
  let W := circuitHamiltonianSpectralWidth H
  have hw := circuitHamiltonianSpectralWidth_nonneg H
  have hθ : 0 ≤ |t| *(W/4) := mul_nonneg (abs_nonneg _) (div_nonneg hw (by norm_num))
  have hh := Real.mul_le_sin hθ (show |t| *(W/4) ≤ π/2 by dsimp only [W]; linarith only [h,Real.pi_pos])
  rw [orbitCircuitDistance_zeroGate_eq_spectralArc H ⟨t,h⟩]
  exact (show |t| *W/π = 2*(2/π*(|t| *(W/4))) by ring).trans_le (mul_le_mul_of_nonneg_left hh zero_le_two)

private theorem grid_separation {m : ℕ} {i j : Fin m} (hij : i ≠ j) {τ : ℝ} (hτ : 0 < τ) :
    τ ≤ |(j.val:ℝ)*τ-i.val*τ| := by
  have h (a b : Fin m) (hab : a < b) : τ ≤ (b.val:ℝ)*τ-a.val*τ := by
    have hn : (a.val:ℝ)+1 ≤ b.val := by exact_mod_cast (show a.val+1 ≤ b.val from hab)
    linarith only [mul_le_mul_of_nonneg_right hn hτ.le]
  rcases lt_or_gt_of_ne hij with hlt|hgt
  · exact (h i j hlt).trans (le_abs_self _)
  · rw [abs_sub_comm]
    exact (h j i hgt).trans (le_abs_self _)

/-- Each affordable path-product lag adds a disjoint copy of the empty
returns at radius r. All m copies are counted even on a finite window. -/
theorem path_grid {n : ℕ} (u : PathShell n) (m : ℕ) {τ r : ℝ} (hτ : 0 < τ) (a T : ℝ) :
    let H : selfAdjoint (Register (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
    ((m:ℝ)*τ)*circuitHamiltonianSpectralWidth H ≤ π →
    2*r < τ*circuitHamiltonianSpectralWidth H/π →
    (m:ℝ)*volume.real (visitSet H 0 r ∩ Icc a T) ≤
      volume.real (visitSet H (Fintype.card (PathLabel n))
        (r+(∑ l, |u l|)^2*((m:ℝ)*τ)^2) ∩ Icc a (T+m*τ)) := by
  intro H hsmall hsep
  let lag (i : Fin m) := (i.val:ℝ)*τ
  have hb (i : Fin m) : lag i ∈ Icc 0 ((m:ℝ)*τ) := ⟨mul_nonneg (Nat.cast_nonneg _) hτ.le,
    mul_le_mul_of_nonneg_right (by exact_mod_cast i.isLt.le) hτ.le⟩
  have cheap (i : Fin m) : lag i ∈ visitSet H (Fintype.card (PathLabel n)) ((∑ l, |u l|)^2*((m:ℝ)*τ)^2) := by
    obtain ⟨z,hz,C,hC,herr⟩ := exists_sparse_path_circuit u (lag i) 1 (by decide)
    simp only [one_mul,Nat.cast_one,div_one,abs_of_nonneg (hb i).1] at hC herr
    exact ⟨z,hz,C,hC.le,herr.trans (mul_le_mul_of_nonneg_left
      (sq_le_sq' (by linarith only [(hb i).1,(hb i).2]) (hb i).2) (sq_nonneg _))⟩
  have sep (i j : Fin m) (hij : i ≠ j) : 2*r < orbitCircuitDistance H 0 (lag j-lag i) := by
    have hupper : |lag j-lag i| ≤ (m:ℝ)*τ := abs_le.mpr
      ⟨by linarith only [(hb i).2,(hb j).1],by linarith only [(hb j).2,(hb i).1]⟩
    have hw := circuitHamiltonianSpectralWidth_nonneg H
    exact hsep.trans_le ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (grid_separation hij hτ) hw) Real.pi_pos.le).trans
        (width_bound H _ ((mul_le_mul_of_nonneg_right hupper hw).trans hsmall)))
  simpa only [Fintype.card_fin] using translated_returns H _ r _ _ lag hb cheap sep a T

#print axioms path_grid

/-- At radii proportional to m⁻², one step of the product formula contains
m disjoint translates of the scalar returns. The enlargement in time
is only π/(mW), with W the spectral width. -/
theorem inverse_square_packing {n : ℕ} (u : PathShell n) (m : ℕ) (hm : 0 < m) (a T : ℝ) :
    let H : selfAdjoint (Register (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
    let W := circuitHamiltonianSpectralWidth H
    let B := 1/4+((∑ l, |u l|)*π/W)^2
    0 < W →
      (m:ℝ)*volume.real (visitSet H 0 (1/(4*(m:ℝ)^2)) ∩ Icc a T) ≤
      volume.real (visitSet H (Fintype.card (PathLabel n)) (B/(m:ℝ)^2) ∩ Icc a (T+π/(W*m))) := by
  intro H W B hW
  have hm' : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hone : (1:ℝ) ≤ m := by exact_mod_cast hm
  let τ := π/(W*(m:ℝ)^2)
  have hτ : 0<τ := by dsimp only [τ]; positivity
  have ht : (m:ℝ)*τ=π/(W*m) := by dsimp only [τ]; field_simp
  have hwidth : ((m:ℝ)*τ)*W ≤ π := by
    rw [ht,div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
    have h := mul_le_mul_of_nonneg_left hone (mul_nonneg Real.pi_pos.le hW.le)
    linarith only [h]
  have hr : 2*(1/(4*(m:ℝ)^2)) < τ*W/π := by
    have he : τ*W/π = 1/(m:ℝ)^2 := by dsimp only [τ]; field_simp
    rw [he]
    have hp : 0 < 1/(m:ℝ)^2 := by positivity
    rw [show 2*(1/(4*(m:ℝ)^2)) = (1/(m:ℝ)^2)/2 by ring]
    exact half_lt_self hp
  have hcost : 1/(4*(m:ℝ)^2)+(∑ l, |u l|)^2*((m:ℝ)*τ)^2 = B/(m:ℝ)^2 := by
    rw [ht]
    dsimp only [B]
    field_simp
  have h := path_grid u m hτ a T hwidth hr
  rw [hcost,ht] at h
  exact h

#print axioms inverse_square_packing
end
end GaloisForLFunctions.HTGeometry.ShortTimeProducts
