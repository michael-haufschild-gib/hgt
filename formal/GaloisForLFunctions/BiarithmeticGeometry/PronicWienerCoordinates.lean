import GaloisForLFunctions.BiarithmeticGeometry.PronicDilationOperators

/-!
# The completed pronic action has the exact arithmetic coordinates

Undoing the pronic normalization is a continuous functional at each integer.
It intertwines completed dilation with floor division. Applying this functional
to the absolutely convergent Wiener series leaves exactly the finite cofactor sum.
-/

noncomputable section
open Finset
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticOrientationTheory
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Recover one unnormalized arithmetic row coordinate from the completed pronic space. -/
def pronicRowCoordinate (n : ℕ) : PronicHilbertSpace →L[ℂ] ℂ :=
  if hn : 0 < n then
    (pronicCoordinateRoot n : ℂ) •
      lp.evalCLM (𝕜 := ℂ) (E := fun _ : ℕ+ => ℂ) (p := 2) ⟨n, hn⟩
  else 0

theorem pronicRowCoordinate_zero : pronicRowCoordinate 0 = 0 := by
  exact dif_neg (Nat.not_lt_zero 0)

theorem pronicRowCoordinate_apply (n : ℕ) (f : PronicHilbertSpace) :
    pronicRowCoordinate n f = (pronicCoordinateRoot n : ℂ) * PNatBlock.extZero f n := by
  unfold pronicRowCoordinate PNatBlock.extZero
  split_ifs with hn
  · rfl
  · simp

/-- Completed dilation has the exact floor-division action in arithmetic coordinates. -/
theorem pronicRowCoordinate_dilation {j : ℕ} (hj : 0 < j)
    (n : ℕ) (f : PronicHilbertSpace) :
    pronicRowCoordinate n (pronicDilationOp j f) = pronicRowCoordinate (n / j) f := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.zero_div, pronicRowCoordinate_zero, ContinuousLinearMap.zero_apply]
  have hnroot : (pronicCoordinateRoot n : ℂ) ≠ 0 := by
    exact_mod_cast (pronicCoordinateRoot_pos hn).ne'
  rw [pronicRowCoordinate_apply, pronicRowCoordinate_apply, pronicDilationOp,
    PNatBlock.extZero_divBlockOp hj (norm_pronicDilationWeight_le j),
    pronicDilationWeight, Complex.ofReal_div]
  field_simp [hnroot]

/-- The complete Wiener action agrees with the finite arithmetic cofactor formula at every cell. -/
theorem pronicRowCoordinate_wiener (a : WienerAlgebraAt (1 / 2))
    (f : PronicHilbertSpace) (n : ℕ) :
    pronicRowCoordinate n (pronicWienerRepresentation a f) =
      ∑ j ∈ Icc 1 n, a.toFn j * pronicRowCoordinate (n / j) f := by
  have hs := WienerAlgebraAt.summable_coefficient_smul pronicDilationOp
    pronicDilationOp_zero norm_pronicDilationOp_le_wienerWeight a
  have he := (hs.hasSum.mapL (ContinuousLinearMap.apply ℂ PronicHilbertSpace f)).mapL
    (pronicRowCoordinate n)
  have htail (j : ℕ) (hj : j ∉ Icc 1 n) :
      pronicRowCoordinate n ((a.toFn j • pronicDilationOp j) f) = 0 := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp only [pronicDilationOp_zero, smul_zero, ContinuousLinearMap.zero_apply, map_zero]
    · have hnj : n < j := by simp only [mem_Icc] at hj; omega
      rw [_root_.smul_apply, map_smul, pronicRowCoordinate_dilation hj0,
        Nat.div_eq_of_lt hnj, pronicRowCoordinate_zero, ContinuousLinearMap.zero_apply, smul_zero]
  calc
    _ = ∑' j : ℕ, pronicRowCoordinate n ((a.toFn j • pronicDilationOp j) f) :=
      he.tsum_eq.symm
    _ = ∑ j ∈ Icc 1 n, pronicRowCoordinate n ((a.toFn j • pronicDilationOp j) f) :=
      tsum_eq_sum htail
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      rw [_root_.smul_apply, map_smul,
        pronicRowCoordinate_dilation (mem_Icc.mp hj).1, smul_eq_mul]

end GaloisForLFunctions.BiarithmeticGeometry
