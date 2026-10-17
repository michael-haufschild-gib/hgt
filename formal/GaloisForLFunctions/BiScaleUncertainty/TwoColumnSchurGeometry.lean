import GaloisForLFunctions.BiScaleUncertainty.CollarAllocationDuality
import GaloisForLFunctions.BiScaleUncertainty.AbstractBiScaleSystemAndSchurKreinCoupling
import Mathlib.Topology.Order.IntermediateValue

/-!
# Two-column Schur geometry and simultaneous rotations

The residual determinant controls every linear combination of two collar columns.
Unit rotations preserve the zero-lag Schur domain. A polynomial intermediate-value
argument constructs an orthogonalizing rotation of arbitrary weight columns.
-/

set_option autoImplicit false
open Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.TwoColumnSchur
noncomputable section
variable {ι : Type*}

def energy (M : Finset ι) (u : ι → ℝ) : ℝ := ∑ i ∈ M, u i ^ 2
def pairing (M : Finset ι) (u v : ι → ℝ) : ℝ := ∑ i ∈ M, u i * v i
def rotateLeft (r s : ℝ) (u v : ι → ℝ) (i : ι) : ℝ := r * u i + s * v i
def rotateRight (r s : ℝ) (u v : ι → ℝ) (i : ι) : ℝ := -s * u i + r * v i

theorem energy_nonneg (M : Finset ι) (u : ι → ℝ) : 0 ≤ energy M u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem pairing_comm (M : Finset ι) (u v : ι → ℝ) : pairing M u v = pairing M v u := by
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem energy_rotateLeft (M : Finset ι) (u v : ι → ℝ) (r s : ℝ) :
    energy M (rotateLeft r s u v) =
      r ^ 2 * energy M u + s ^ 2 * energy M v + 2 * r * s * pairing M u v := by
  unfold energy pairing rotateLeft
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem energy_rotateRight (M : Finset ι) (u v : ι → ℝ) (r s : ℝ) :
    energy M (rotateRight r s u v) =
      s ^ 2 * energy M u + r ^ 2 * energy M v - 2 * r * s * pairing M u v := by
  change energy M (rotateLeft (-s) r u v) = _
  rw [energy_rotateLeft]
  ring

theorem pairing_rotate (M : Finset ι) (u v : ι → ℝ) (r s : ℝ) :
    pairing M (rotateLeft r s u v) (rotateRight r s u v) =
      -r * s * energy M u + r * s * energy M v + (r ^ 2 - s ^ 2) * pairing M u v := by
  unfold energy pairing rotateLeft rotateRight
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem energy_rotation_sum (M : Finset ι) (u v : ι → ℝ) {r s : ℝ}
    (hrs : r ^ 2 + s ^ 2 = 1) :
    energy M (rotateLeft r s u v) + energy M (rotateRight r s u v) =
      energy M u + energy M v := by
  rw [energy_rotateLeft, energy_rotateRight]
  calc
    _ = (r ^ 2 + s ^ 2) * (energy M u + energy M v) := by ring
    _ = _ := by rw [hrs, one_mul]

theorem gram_rotation_determinant (M : Finset ι) (u v : ι → ℝ) {r s : ℝ}
    (hrs : r ^ 2 + s ^ 2 = 1) :
    energy M (rotateLeft r s u v) * energy M (rotateRight r s u v) -
        pairing M (rotateLeft r s u v) (rotateRight r s u v) ^ 2 =
      energy M u * energy M v - pairing M u v ^ 2 := by
  rw [energy_rotateLeft, energy_rotateRight, pairing_rotate]
  calc
    _ = (r ^ 2 + s ^ 2) ^ 2 * (energy M u * energy M v - pairing M u v ^ 2) := by ring
    _ = _ := by rw [hrs]; ring

/-- Every coefficient direction is controlled by the residual determinant. -/
theorem residual_quadratic_nonneg {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : C ^ 2 ≤ A * B) (r s : ℝ) : 0 ≤ A * r ^ 2 + 2 * C * r * s + B * s ^ 2 := by
  rcases eq_or_lt_of_le hA with hA0 | hAp
  · have hC0 : C = 0 := by rw [← hA0] at hC; nlinarith [sq_nonneg C]
    rw [← hA0, hC0]
    simpa using mul_nonneg hB (sq_nonneg s)
  · have h : 0 ≤ A * (A * r ^ 2 + 2 * C * r * s + B * s ^ 2) := by
      nlinarith [sq_nonneg (A * r + C * s),
        mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hC)]
    exact nonneg_of_mul_nonneg_right h hAp

/-- General measured-lag form; no zero-lag assumption is used here. -/
theorem rotated_energy_le (M : Finset ι) (u v : ι → ℝ) (R c r s : ℝ)
    (hu : energy M u ≤ R ^ 2) (hv : energy M v ≤ R ^ 2)
    (hschur : (R * c - pairing M u v) ^ 2 ≤ (R ^ 2 - energy M u) * (R ^ 2 - energy M v)) :
    energy M (rotateLeft r s u v) ≤ R ^ 2 * (r ^ 2 + s ^ 2) + 2 * R * c * r * s := by
  have h := residual_quadratic_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hv) hschur r s
  rw [energy_rotateLeft]
  nlinarith

/-- The exact zero-lag contraction domain, including its two diagonal conditions. -/
def Feasible (M : Finset ι) (u v : ι → ℝ) (R : ℝ) : Prop :=
  energy M u ≤ R ^ 2 ∧ energy M v ≤ R ^ 2 ∧
    pairing M u v ^ 2 ≤ (R ^ 2 - energy M u) * (R ^ 2 - energy M v)

theorem feasible_rotate (M : Finset ι) (u v : ι → ℝ) (R : ℝ)
    (h : Feasible M u v R) {r s : ℝ} (hrs : r ^ 2 + s ^ 2 = 1) :
    Feasible M (rotateLeft r s u v) (rotateRight r s u v) R := by
  have hc : (R * 0 - pairing M u v) ^ 2 ≤
      (R ^ 2 - energy M u) * (R ^ 2 - energy M v) := by simpa using h.2.2
  have hl := rotated_energy_le M u v R 0 r s h.1 h.2.1 hc
  have hr := rotated_energy_le M u v R 0 (-s) r h.1 h.2.1 hc
  have hrs' : (-s) ^ 2 + r ^ 2 = 1 := by nlinarith
  simp only [hrs, mul_one, mul_zero, zero_mul, add_zero] at hl
  simp only [hrs', mul_one, mul_zero, zero_mul, add_zero] at hr
  refine ⟨hl, hr, ?_⟩
  have ht := energy_rotation_sum M u v hrs
  have hd := gram_rotation_determinant M u v hrs
  have he : (R ^ 2 - energy M (rotateLeft r s u v)) *
        (R ^ 2 - energy M (rotateRight r s u v)) -
        pairing M (rotateLeft r s u v) (rotateRight r s u v) ^ 2 =
      (R ^ 2 - energy M u) * (R ^ 2 - energy M v) - pairing M u v ^ 2 := by
    calc
      _ = R ^ 4 - R ^ 2 * (energy M (rotateLeft r s u v) + energy M (rotateRight r s u v)) +
          (energy M (rotateLeft r s u v) * energy M (rotateRight r s u v) -
            pairing M (rotateLeft r s u v) (rotateRight r s u v) ^ 2) := by ring
      _ = _ := by rw [ht, hd]; ring
  linarith [h.2.2]

theorem pairing_rotation_invariant (M : Finset ι) (a b u v : ι → ℝ)
    {r s : ℝ} (hrs : r ^ 2 + s ^ 2 = 1) :
    pairing M (rotateLeft r s a b) (rotateLeft r s u v) +
        pairing M (rotateRight r s a b) (rotateRight r s u v) =
      pairing M a u + pairing M b v := by
  unfold pairing
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold rotateLeft rotateRight
  calc
    _ = (r ^ 2 + s ^ 2) * (a i * u i + b i * v i) := by ring
    _ = _ := by rw [hrs, one_mul]

theorem inverse_rotateLeft (u v : ι → ℝ) {r s : ℝ} (hrs : r ^ 2 + s ^ 2 = 1) :
    rotateLeft r s (rotateLeft r (-s) u v) (rotateRight r (-s) u v) = u := by
  funext i
  unfold rotateLeft rotateRight
  calc
    _ = (r ^ 2 + s ^ 2) * u i := by ring
    _ = _ := by rw [hrs, one_mul]

theorem inverse_rotateRight (u v : ι → ℝ) {r s : ℝ} (hrs : r ^ 2 + s ^ 2 = 1) :
    rotateRight r s (rotateLeft r (-s) u v) (rotateRight r (-s) u v) = v := by
  funext i
  unfold rotateLeft rotateRight
  calc
    _ = (r ^ 2 + s ^ 2) * v i := by ring
    _ = _ := by rw [hrs, one_mul]

/-- Polynomial IVT supplies a real unit rotation with orthogonal weight columns. -/
theorem exists_orthogonal_rotation (M : Finset ι) (a b : ι → ℝ) :
    ∃ r s : ℝ, r ^ 2 + s ^ 2 = 1 ∧
      pairing M (rotateLeft r s a b) (rotateRight r s a b) = 0 := by
  let q : ℝ → ℝ := fun t => (1 - t ^ 2) * pairing M a b + t * (energy M b - energy M a)
  have hc : Continuous q := by fun_prop
  have hm : q (-1) = energy M a - energy M b := by dsimp [q]; ring
  have hp : q 1 = energy M b - energy M a := by dsimp [q]; ring
  have hex : ∃ t ∈ Icc (-1 : ℝ) 1, q t = 0 := by
    by_cases h : energy M a ≤ energy M b
    · exact intermediate_value_Icc (by norm_num) hc.continuousOn
        (show (0 : ℝ) ∈ Icc (q (-1)) (q 1) by rw [hm, hp]; constructor <;> linarith)
    · exact intermediate_value_Icc' (by norm_num) hc.continuousOn
        (show (0 : ℝ) ∈ Icc (q 1) (q (-1)) by rw [hm, hp]; constructor <;> linarith)
  obtain ⟨t, _, ht⟩ := hex
  let D := Real.sqrt (1 + t ^ 2)
  have hDp : 0 < D := Real.sqrt_pos.2 (by positivity)
  have hD : D ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  refine ⟨1 / D, t / D, ?_, ?_⟩
  · rw [div_pow, div_pow, ← add_div, one_pow, ← hD, div_self (pow_ne_zero _ hDp.ne')]
  · rw [pairing_rotate]
    calc
      _ = q t / D ^ 2 := by dsimp [q]; field_simp; ring
      _ = 0 := by rw [ht, zero_div]

end
end GaloisForLFunctions.BiScaleUncertainty.TwoColumnSchur
