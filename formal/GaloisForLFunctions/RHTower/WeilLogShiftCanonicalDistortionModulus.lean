import GaloisForLFunctions.RHTower.WeilLogShiftLocalDistortionModulus
import GaloisForLFunctions.RHTower.WeilLogShiftArithmeticBinomial

/-! Local raw-weight distortion on the canonical logarithmic grid. -/

noncomputable section
namespace RHTower

def finiteWeilClusterPositiveNodes (r k : ℕ) (i : Fin (r + 2)) : ℝ :=
  ((k + 2 : ℕ) : ℝ) + (i : ℕ)

theorem finiteWeilClusterPositiveNodes_pos (r k : ℕ) (i : Fin (r + 2)) :
    0 < finiteWeilClusterPositiveNodes r k i := by
  unfold finiteWeilClusterPositiveNodes
  positivity

theorem finiteWeilClusterPositiveNodes_injective (r k : ℕ) :
    Function.Injective (finiteWeilClusterPositiveNodes r k) := by
  intro i j hij
  apply Fin.ext
  have heq : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by
    dsimp [finiteWeilClusterPositiveNodes] at hij
    linarith only [hij]
  exact_mod_cast heq

theorem finiteWeilClusterPositiveNodes_gap (r k : ℕ) (i j : Fin (r + 2)) :
    finiteWeilClusterPositiveNodes r k i - finiteWeilClusterPositiveNodes r k j =
      ((i : ℕ) : ℝ) - ((j : ℕ) : ℝ) := by
  unfold finiteWeilClusterPositiveNodes
  ring

def finiteWeilCanonicalRawDistortion (r k : ℕ) (i : Fin (r + 2)) : ℝ :=
  finiteWeilLogNodalDistortion (finiteWeilClusterPositiveNodes r k) i

/-- Centering the logarithms and translating the arithmetic nodes do not change raw weights. -/
theorem finiteWeilCanonicalRawDistortion_eq_weight_ratio (r k : ℕ) (i : Fin (r + 2)) :
    finiteWeilCanonicalRawDistortion r k i =
      |finiteWeilMomentWeights (finiteWeilClusterLogNodes r k) i| /
        |finiteWeilMomentWeights (finiteWeilArithmeticNodes r) i| := by
  let x := finiteWeilClusterPositiveNodes r k
  have hlog : |finiteWeilMomentWeights (fun j => Real.log (x j)) i| =
      |finiteWeilMomentWeights (finiteWeilClusterLogNodes r k) i| := by
    rw [finiteWeilMomentWeights_abs_product, finiteWeilMomentWeights_abs_product]
    apply Finset.prod_congr rfl
    intro j hj
    have hgap : Real.log (x i) - Real.log (x j) =
        finiteWeilClusterLogNodes r k i - finiteWeilClusterLogNodes r k j := by
      rw [finiteWeilClusterLogNodes_apply, finiteWeilClusterLogNodes_apply]
      dsimp [x, finiteWeilClusterPositiveNodes]
      push_cast
      ring
    rw [hgap]
  have harith : |finiteWeilMomentWeights x i| =
      |finiteWeilMomentWeights (finiteWeilArithmeticNodes r) i| := by
    rw [finiteWeilMomentWeights_abs_product, finiteWeilMomentWeights_abs_product]
    apply Finset.prod_congr rfl
    intro j hj
    change |finiteWeilClusterPositiveNodes r k i - finiteWeilClusterPositiveNodes r k j|⁻¹ = _
    rw [finiteWeilClusterPositiveNodes_gap]
    rfl
  change finiteWeilLogNodalDistortion x i = _
  rw [finiteWeilLogNodalDistortion_eq_weight_ratio x
    (finiteWeilClusterPositiveNodes_pos r k) (finiteWeilClusterPositiveNodes_injective r k) i,
    hlog, harith]

/-- The entire grid obeys the local modulus at quadratic starts. -/
theorem finiteWeilCanonicalRawDistortion_quadratic_modulus (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) (i j : Fin (r + 2)) :
    ((k + 2 : ℕ) : ℝ) *
        |finiteWeilCanonicalRawDistortion r k i / finiteWeilCanonicalRawDistortion r k j - 1| ≤
      2 * (r : ℝ) * |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
  have hD : |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| ≤ ((r + 1 : ℕ) : ℝ) := by
    have hi : ((i : ℕ) : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show (i : ℕ) ≤ r + 1 by omega)
    have hj : ((j : ℕ) : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show (j : ℕ) ≤ r + 1 by omega)
    have hi0 : 0 ≤ ((i : ℕ) : ℝ) := by positivity
    have hj0 : 0 ≤ ((j : ℕ) : ℝ) := by positivity
    exact abs_le.mpr ⟨by linarith only [hj, hi0], by linarith only [hi, hj0]⟩
  have hr : (r : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (show r ≤ r + 1 by omega)
  have hmul : (r : ℝ) * |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| ≤ ((r + 1 : ℕ) : ℝ) ^ 2 := by
    calc
      _ ≤ ((r + 1 : ℕ) : ℝ) * |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| :=
        mul_le_mul_of_nonneg_right hr (abs_nonneg _)
      _ ≤ ((r + 1 : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hD (by positivity)
      _ = _ := by ring
  have hw : 2 * (r : ℝ) *
      |finiteWeilClusterPositiveNodes r k i - finiteWeilClusterPositiveNodes r k j| ≤
        ((k + 2 : ℕ) : ℝ) := by
    rw [finiteWeilClusterPositiveNodes_gap]
    nlinarith only [hmul, hwidth]
  have hAi : ((k + 2 : ℕ) : ℝ) ≤ finiteWeilClusterPositiveNodes r k i := by
    dsimp [finiteWeilClusterPositiveNodes]
    have hi0 : 0 ≤ ((i : ℕ) : ℝ) := by positivity
    linarith only [hi0]
  have hAj : ((k + 2 : ℕ) : ℝ) ≤ finiteWeilClusterPositiveNodes r k j := by
    dsimp [finiteWeilClusterPositiveNodes]
    have hj0 : 0 ≤ ((j : ℕ) : ℝ) := by positivity
    linarith only [hj0]
  have h := finiteWeilLogNodalDistortion_relative_modulus (finiteWeilClusterPositiveNodes r k)
    (finiteWeilClusterPositiveNodes_pos r k) (finiteWeilClusterPositiveNodes_injective r k)
    ((k + 2 : ℕ) : ℝ) i j hAi hAj hw
  change ((k + 2 : ℕ) : ℝ) *
      |finiteWeilCanonicalRawDistortion r k i / finiteWeilCanonicalRawDistortion r k j - 1| ≤
    2 * (r : ℝ) * |finiteWeilClusterPositiveNodes r k i - finiteWeilClusterPositiveNodes r k j| at h
  simpa only [finiteWeilClusterPositiveNodes_gap] using h

/-- Nearby indices have close relative distortion, uniformly over the canonical grid. -/
theorem finiteWeilCanonicalRawDistortion_index_modulus (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) (i j : Fin (r + 2)) :
    |finiteWeilCanonicalRawDistortion r k i / finiteWeilCanonicalRawDistortion r k j - 1| ≤
      |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| / ((r + 1 : ℕ) : ℝ) := by
  let E := |finiteWeilCanonicalRawDistortion r k i / finiteWeilCanonicalRawDistortion r k j - 1|
  let D := |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|
  let n : ℝ := ((r + 1 : ℕ) : ℝ)
  let A : ℝ := ((k + 2 : ℕ) : ℝ)
  have hn : 0 < n := by dsimp [n]; positivity
  have hc := finiteWeilCanonicalRawDistortion_quadratic_modulus r k hwidth i j
  change A * E ≤ 2 * (r : ℝ) * D at hc
  change 2 * n ^ 2 ≤ A at hwidth
  change E ≤ D / n
  apply (le_div_iff₀ hn).mpr
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * n by positivity)).mp
  calc
    _ = 2 * n ^ 2 * E := by ring
    _ ≤ A * E := mul_le_mul_of_nonneg_right hwidth (abs_nonneg _)
    _ ≤ 2 * (r : ℝ) * D := hc
    _ ≤ (2 * n) * D := mul_le_mul_of_nonneg_right
      (show 2 * (r : ℝ) ≤ 2 * n by dsimp [n]; push_cast; linarith) (abs_nonneg _)

end RHTower
