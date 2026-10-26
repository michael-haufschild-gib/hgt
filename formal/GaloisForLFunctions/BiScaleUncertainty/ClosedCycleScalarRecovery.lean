import GaloisForLFunctions.BiScaleUncertainty.EnergyControlledClosedCycleRecovery

/-!
# Arbitrary positive collars and literal finite closed observations

Two scalar products recover a signed outer value with the exact collar
conditioning. A concrete pair/spoke family uses at most twice the ceiling
mesh size and has the stated maximum cycle order.
-/

noncomputable section
open MeasureTheory Set
open scoped CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.EnergyCycle
set_option autoImplicit false

/-- The exact scalar recovery inequality for every positive collar height. -/
theorem scalar_cycle_recovery {a b u v κ : ℝ} (hκ : 0 < κ) (hu : κ ≤ u) (hv : κ ≤ v)
    (hu1 : |u| ≤ 1) (hv1 : |v| ≤ 1) (hb : |b| ≤ 1) (n : ℕ) :
    |a - b| ≤ (|a * u ^ n - b * v ^ n| + (n : ℝ) * |u ^ 2 - v ^ 2| / (2 * κ)) / κ ^ n := by
  have hu0 := hκ.le.trans hu
  have hv0 := hκ.le.trans hv
  have h2κ : 0 < 2 * κ := mul_pos (by norm_num) hκ
  have hs : |u - v| ≤ |u ^ 2 - v ^ 2| / (2 * κ) := by
    apply (le_div_iff₀ h2κ).mpr
    calc
      _ ≤ |u - v| * (u + v) :=
        mul_le_mul_of_nonneg_left (by linarith only [hu, hv]) (abs_nonneg _)
      _ = |u ^ 2 - v ^ 2| := by
        rw [← abs_of_nonneg (add_nonneg hu0 hv0), ← abs_mul]
        congr 1
        ring
  have hmax : 0 ≤ max |u| |v| := (abs_nonneg u).trans (le_max_left _ _)
  have hmaxpow : max |u| |v| ^ (n - 1) ≤ (1 : ℝ) := by
    simpa only [one_pow] using pow_le_pow_left₀ hmax (max_le hu1 hv1) (n - 1)
  have hp : |u ^ n - v ^ n| ≤ (n : ℝ) * |u ^ 2 - v ^ 2| / (2 * κ) := by
    calc
      _ ≤ |u - v| * (n : ℝ) * max |u| |v| ^ (n - 1) := abs_pow_sub_pow_le u v n
      _ ≤ |u - v| * (n : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hmaxpow (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
      _ ≤ (|u ^ 2 - v ^ 2| / (2 * κ)) * (n : ℝ) := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg n)
      _ = _ := by ring
  have hbound : κ ^ n * |a - b| ≤
      |a * u ^ n - b * v ^ n| + (n : ℝ) * |u ^ 2 - v ^ 2| / (2 * κ) := by
    calc
      _ ≤ u ^ n * |a - b| := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hκ.le hu n) (abs_nonneg _)
      _ = |(a * u ^ n - b * v ^ n) + b * (v ^ n - u ^ n)| := by
        rw [show (a * u ^ n - b * v ^ n) + b * (v ^ n - u ^ n) =
          u ^ n * (a - b) by ring, abs_mul, abs_of_nonneg (pow_nonneg hu0 n)]
      _ ≤ |a * u ^ n - b * v ^ n| + |b * (v ^ n - u ^ n)| := abs_add_le _ _
      _ ≤ |a * u ^ n - b * v ^ n| + |u ^ n - v ^ n| := by
        rw [abs_mul, abs_sub_comm (v ^ n)]
        exact add_le_add le_rfl (mul_le_of_le_one_left (abs_nonneg _) hb)
      _ ≤ _ := add_le_add le_rfl hp
  exact (le_div_iff₀ (pow_pos hκ n)).mpr (by simpa only [mul_comm] using hbound)

/-- Actual normalized correlations satisfy recovery from their literal pair and spoke products. -/
theorem correlation_recovery_of_collar {E κ : ℝ} (f g : LevyEnergySource E) (n : ℕ) (x : ℝ)
    (hκ : 0 < κ) (hf : κ ≤ f.correlation (x / ((n : ℝ) + 1)))
    (hg : κ ≤ g.correlation (x / ((n : ℝ) + 1))) :
    |f.correlation x - g.correlation x| ≤
      (|value f (spoke n x) - value g (spoke n x)| + ((n : ℝ) + 1) *
        |value f [x / ((n : ℝ) + 1), -(x / ((n : ℝ) + 1))] -
          value g [x / ((n : ℝ) + 1), -(x / ((n : ℝ) + 1))]| / (2 * κ)) / κ ^ (n + 1) := by
  simp only [value_pair, value_spoke]
  simpa only [Nat.cast_add, Nat.cast_one] using scalar_cycle_recovery hκ hf hg
    (f.abs_correlation_le_one _) (g.abs_correlation_le_one _) (g.abs_correlation_le_one x) (n + 1)

/-- The finite observation family consists literally of one pair and one spoke at each mesh point. -/
def literalObservationCycle (R η : ℝ) (n : ℕ) (i : Bool × Fin (meshLength R η)) : List ℝ :=
  let x := meshPoint R η i.2
  let y := x / ((n : ℝ) + 1)
  if i.1 then [y, -y] else spoke n x

/-- Every member of the finite family is a closed cycle. -/
theorem literalObservationCycle_sum (R η : ℝ) (n : ℕ) (i : Bool × Fin (meshLength R η)) :
    (literalObservationCycle R η n i).sum = 0 := by
  rcases i with ⟨b, i⟩
  cases b <;> simp [literalObservationCycle, spoke_sum]

/-- The family uses exactly two labels per mesh node. -/
theorem literalObservationCycle_count (R η : ℝ) :
    Fintype.card (Bool × Fin (meshLength R η)) = 2 * meshLength R η := by simp

/-- The literal observation count obeys the specified ceiling bound, including radius zero. -/
theorem literalObservationCycle_count_le {R η : ℝ} (hR : 0 ≤ R) (hη : 0 < η) :
    Fintype.card (Bool × Fin (meshLength R η)) ≤ 2 * (⌈2 * R / η⌉₊ + 1) := by
  have hf : ⌊2 * R / η⌋₊ ≤ ⌈2 * R / η⌉₊ := by
    have h := (Nat.floor_le (by positivity : 0 ≤ 2 * R / η)).trans (Nat.le_ceil (2 * R / η))
    exact_mod_cast h
  rw [literalObservationCycle_count, meshLength]
  exact Nat.mul_le_mul_left 2 (Nat.add_le_add_right hf 1)

/-- The exact largest required order is at most the maximum of two and the spoke order. -/
theorem literalObservationCycle_length_le (R η : ℝ) (n : ℕ)
    (i : Bool × Fin (meshLength R η)) :
    (literalObservationCycle R η n i).length ≤ max 2 (n + 2) := by
  rcases i with ⟨b, i⟩
  cases b
  · change (spoke n (meshPoint R η i)).length ≤ max 2 (n + 2)
    rw [spoke_length]
    exact le_max_right 2 (n + 2)
  · change 2 ≤ max 2 (n + 2)
    exact le_max_left 2 (n + 2)

end GaloisForLFunctions.BiScaleUncertainty.EnergyCycle
