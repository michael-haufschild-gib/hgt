import GaloisForLFunctions.RHTower.WeilLogShiftSignedDistortion
import GaloisForLFunctions.RHTower.WeilLogShiftMidpointProfile

/-! The signed canonical annihilator retains the arithmetic binomial parity at every node. -/

noncomputable section
namespace RHTower

def finiteWeilBinomialParity (r : ℕ) (i : Fin (r + 2)) : ℝ :=
  (-1 : ℝ) ^ ((r + 1) - (i : ℕ))

theorem finiteWeilBinomialParity_abs (r : ℕ) (i : Fin (r + 2)) :
    |finiteWeilBinomialParity r i| = 1 := by
  simp only [finiteWeilBinomialParity, abs_pow, abs_neg, abs_one, one_pow]

theorem finiteWeilBinomialParity_sq (r : ℕ) (i : Fin (r + 2)) :
    finiteWeilBinomialParity r i ^ 2 = 1 := by
  rw [← sq_abs, finiteWeilBinomialParity_abs, one_pow]

theorem finiteWeilBinomialDual_eq_parity (r : ℕ) (i : Fin (r + 2)) :
    finiteWeilBinomialDual r i =
      finiteWeilBinomialParity r i * ((r + 1).choose (i : ℕ) : ℝ) := rfl

/-- The positive local distortion changes magnitudes while retaining exact binomial parity. -/
theorem finiteWeilCanonicalCluster_parity (r k : ℕ) (i : Fin (r + 2)) :
    finiteWeilCanonicalCluster r k i =
      finiteWeilBinomialParity r i * |finiteWeilCanonicalCluster r k i| := by
  let N := ‖finiteWeilMomentWeights (finiteWeilClusterLogNodes r k)‖
  let B := N⁻¹ * finiteWeilCanonicalRawDistortion r k i * ((r + 1).factorial : ℝ)⁻¹
  have hN : 0 < N := finiteWeilMomentWeights_norm_pos _
    (finiteWeilClusterLogNodes_injective r k)
  have hF : 0 < ((r + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (r + 1)
  have hB : 0 < B := mul_pos
    (mul_pos (inv_pos.mpr hN) (finiteWeilCanonicalRawDistortion_pos r k i)) (inv_pos.mpr hF)
  have hci : finiteWeilCanonicalCluster r k i = B * finiteWeilBinomialDual r i := by
    change N⁻¹ * finiteWeilMomentWeights (finiteWeilClusterLogNodes r k) i = _
    rw [finiteWeilCanonicalRawDistortion_weights, finiteWeilArithmeticWeights_eq_binomial]
    simp only [Pi.smul_apply, smul_eq_mul]
    dsimp [B]
    ring
  calc
    _ = B * finiteWeilBinomialDual r i := hci
    _ = finiteWeilBinomialParity r i * (B * ((r + 1).choose (i : ℕ) : ℝ)) := by
      rw [finiteWeilBinomialDual_eq_parity]
      ring
    _ = _ := by
      rw [hci, abs_mul, abs_of_pos hB, finiteWeilBinomialDual_abs]

end RHTower
