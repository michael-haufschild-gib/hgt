import GaloisForLFunctions.BiScaleUncertainty.TwoColumnSchurGeometry

/-!
# Exact support of two zero-lag Schur columns

The closed support is the sum of the two singular values, expressed using only
the trace and determinant of the two-column Gram matrix. The proof constructs
finite-vector maximizers; it does not assert autocorrelation realization.
-/

set_option autoImplicit false
open Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.TwoColumnSchur
noncomputable section
variable {ι : Type*}

def support (M : Finset ι) (a b : ι → ℝ) : ℝ :=
  Real.sqrt (energy M a + energy M b +
    2 * Real.sqrt (energy M a * energy M b - pairing M a b ^ 2))

theorem gram_determinant_nonneg (M : Finset ι) (a b : ι → ℝ) :
    0 ≤ energy M a * energy M b - pairing M a b ^ 2 :=
  sub_nonneg.mpr (Finset.sum_mul_sq_le_sq_mul_sq M a b)

theorem blockSize_sq (M : Finset ι) (a : ι → ℝ) :
    collarBlockSize M a ^ 2 = energy M a := Real.sq_sqrt (energy_nonneg M a)

theorem pairing_le_radius (M : Finset ι) (a u : ι → ℝ) {R : ℝ}
    (hR : 0 ≤ R) (hu : energy M u ≤ R ^ 2) :
    pairing M a u ≤ collarBlockSize M a * R := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq M a u
  change pairing M a u ^ 2 ≤ energy M a * energy M u at hc
  have hb := mul_le_mul_of_nonneg_left hu (energy_nonneg M a)
  have hs := blockSize_sq M a
  have hn : 0 ≤ collarBlockSize M a * R := mul_nonneg (Real.sqrt_nonneg _) hR
  nlinarith

theorem support_nonneg (M : Finset ι) (a b : ι → ℝ) : 0 ≤ support M a b :=
  Real.sqrt_nonneg _

theorem support_sq (M : Finset ι) (a b : ι → ℝ) :
    support M a b ^ 2 = energy M a + energy M b +
      2 * Real.sqrt (energy M a * energy M b - pairing M a b ^ 2) :=
  Real.sq_sqrt (by positivity [energy_nonneg M a, energy_nonneg M b])

theorem support_eq_rotated_sizes (M : Finset ι) (a b : ι → ℝ)
    {r s : ℝ} (hrs : r ^ 2 + s ^ 2 = 1)
    (ho : pairing M (rotateLeft r s a b) (rotateRight r s a b) = 0) :
    support M a b = collarBlockSize M (rotateLeft r s a b) +
      collarBlockSize M (rotateRight r s a b) := by
  have ht := energy_rotation_sum M a b hrs
  have hd := gram_rotation_determinant M a b hrs
  rw [ho, zero_pow (by decide), sub_zero] at hd
  have hl := blockSize_sq M (rotateLeft r s a b)
  have hr := blockSize_sq M (rotateRight r s a b)
  have hnL : 0 ≤ collarBlockSize M (rotateLeft r s a b) := Real.sqrt_nonneg _
  have hnR : 0 ≤ collarBlockSize M (rotateRight r s a b) := Real.sqrt_nonneg _
  have hp : collarBlockSize M (rotateLeft r s a b) *
      collarBlockSize M (rotateRight r s a b) =
      Real.sqrt (energy M a * energy M b - pairing M a b ^ 2) := by
    have hs := Real.sq_sqrt (gram_determinant_nonneg M a b)
    have hprod : (collarBlockSize M (rotateLeft r s a b) *
        collarBlockSize M (rotateRight r s a b)) ^ 2 =
        energy M a * energy M b - pairing M a b ^ 2 := by
      rw [mul_pow, hl, hr, hd]
    nlinarith [Real.sqrt_nonneg (energy M a * energy M b - pairing M a b ^ 2),
      mul_nonneg hnL hnR]
  nlinarith [support_sq M a b, support_nonneg M a b]

/-- Sharp upper bound, including singular Gram matrices and zero radius. -/
theorem pairing_le_support (M : Finset ι) (a b u v : ι → ℝ) {R : ℝ}
    (hR : 0 ≤ R) (h : Feasible M u v R) :
    pairing M a u + pairing M b v ≤ R * support M a b := by
  obtain ⟨r, s, hrs, ho⟩ := exists_orthogonal_rotation M a b
  have hf := feasible_rotate M u v R h hrs
  have hl := pairing_le_radius M (rotateLeft r s a b) (rotateLeft r s u v) hR hf.1
  have hr := pairing_le_radius M (rotateRight r s a b) (rotateRight r s u v) hR hf.2.1
  rw [support_eq_rotated_sizes M a b hrs ho]
  rw [← pairing_rotation_invariant M a b u v hrs]
  nlinarith

theorem orthogonal_direction_pairing (M : Finset ι) (a b : ι → ℝ)
    (ho : pairing M a b = 0) :
    pairing M (collarBlockDirection M a) (collarBlockDirection M b) = 0 := by
  unfold pairing collarBlockDirection
  simp_rw [div_mul_div_comm]
  rw [← Finset.sum_div]
  change pairing M a b / _ = 0
  rw [ho, zero_div]

theorem scaled_directions_feasible (M : Finset ι) (a b : ι → ℝ) (R : ℝ)
    (ho : pairing M a b = 0) :
    Feasible M (fun i => R * collarBlockDirection M a i)
      (fun i => R * collarBlockDirection M b i) R := by
  have he (c : ι → ℝ) : energy M (fun i => R * collarBlockDirection M c i) ≤ R ^ 2 := by
    unfold energy
    simp_rw [mul_pow, ← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (collarBlockDirection_sq_sum_le M c) (sq_nonneg R)).trans_eq (mul_one _)
  have hp : pairing M (fun i => R * collarBlockDirection M a i)
      (fun i => R * collarBlockDirection M b i) = 0 := by
    unfold pairing
    simp_rw [show ∀ i, (R * collarBlockDirection M a i) * (R * collarBlockDirection M b i) =
      R ^ 2 * (collarBlockDirection M a i * collarBlockDirection M b i) by intro i; ring]
    rw [← Finset.mul_sum]
    change R ^ 2 * pairing M (collarBlockDirection M a) (collarBlockDirection M b) = 0
    rw [orthogonal_direction_pairing M a b ho, mul_zero]
  refine ⟨he a, he b, ?_⟩
  rw [hp, zero_pow (by decide)]
  exact mul_nonneg (sub_nonneg.mpr (he a)) (sub_nonneg.mpr (he b))

theorem pairing_scaled_direction (M : Finset ι) (a : ι → ℝ) (R : ℝ) :
    pairing M a (fun i => R * collarBlockDirection M a i) = R * collarBlockSize M a := by
  unfold pairing
  simp_rw [show ∀ i, a i * (R * collarBlockDirection M a i) =
    R * (a i * collarBlockDirection M a i) by intro i; ring]
  rw [← Finset.mul_sum, collarBlockDirection_pairing]

/-- Attainment is in the finite Schur domain, not in the class of physical sources. -/
theorem support_attained (M : Finset ι) (a b : ι → ℝ) (R : ℝ) :
    ∃ u v, Feasible M u v R ∧ pairing M a u + pairing M b v = R * support M a b := by
  obtain ⟨r, s, hrs, ho⟩ := exists_orthogonal_rotation M a b
  let u := fun i => R * collarBlockDirection M (rotateLeft r s a b) i
  let v := fun i => R * collarBlockDirection M (rotateRight r s a b) i
  have hf := scaled_directions_feasible M (rotateLeft r s a b) (rotateRight r s a b) R ho
  have hrs' : r ^ 2 + (-s) ^ 2 = 1 := by nlinarith
  refine ⟨rotateLeft r (-s) u v, rotateRight r (-s) u v,
    feasible_rotate M u v R hf hrs', ?_⟩
  rw [← pairing_rotation_invariant M a b _ _ hrs,
    inverse_rotateLeft u v hrs, inverse_rotateRight u v hrs]
  change pairing M (rotateLeft r s a b) (fun i => R * collarBlockDirection M (rotateLeft r s a b) i) +
    pairing M (rotateRight r s a b) (fun i => R * collarBlockDirection M (rotateRight r s a b) i) = _
  rw [pairing_scaled_direction, pairing_scaled_direction, support_eq_rotated_sizes M a b hrs ho]
  ring

theorem support_le_independent (M : Finset ι) (a b : ι → ℝ) :
    support M a b ≤ collarBlockSize M a + collarBlockSize M b := by
  obtain ⟨u, v, hf, he⟩ := support_attained M a b 1
  have hl := pairing_le_radius M a u (by norm_num : (0 : ℝ) ≤ 1) hf.1
  have hr := pairing_le_radius M b v (by norm_num : (0 : ℝ) ≤ 1) hf.2.1
  nlinarith

theorem support_eq_independent_iff (M : Finset ι) (a b : ι → ℝ) :
    support M a b = collarBlockSize M a + collarBlockSize M b ↔ pairing M a b = 0 := by
  constructor
  · intro he
    have hs := support_sq M a b
    have hL := blockSize_sq M a
    have hH := blockSize_sq M b
    have hd := Real.sq_sqrt (gram_determinant_nonneg M a b)
    rw [he] at hs
    have hp : Real.sqrt (energy M a * energy M b - pairing M a b ^ 2) =
        collarBlockSize M a * collarBlockSize M b := by nlinarith
    rw [hp, mul_pow, hL, hH] at hd
    nlinarith [sq_nonneg (pairing M a b)]
  · intro ho
    have hl : rotateLeft 1 0 a b = a := by funext i; change 1 * a i + 0 * b i = a i; ring
    have hr : rotateRight 1 0 a b = b := by funext i; change -0 * a i + 1 * b i = b i; ring
    have he := support_eq_rotated_sizes M a b (r := 1) (s := 0) (by norm_num)
      (by rw [hl, hr]; exact ho)
    rwa [hl, hr] at he

end
end GaloisForLFunctions.BiScaleUncertainty.TwoColumnSchur
