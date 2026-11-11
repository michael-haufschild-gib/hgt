import GaloisForLFunctions.HTGeometry.FejerLatticeVanishing

/-!
# Integer triangle interpolation

Unit triangles linearly interpolate arbitrary integer lattice data. The sum
is locally finite, hence continuous; positivity, bounds, and affine pieces
pass directly from the lattice values to the interpolant.
-/

open Real Finset Set Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-- Linear interpolation of values on the integer lattice by unit triangles. -/
def integerHatInterpolation (a : ℤ → ℝ) (x : ℝ) : ℝ :=
  ∑' j : ℤ, a j * triangleFn 1 (x - j)

private theorem triangle_eq_zero_off_neighbors {k j : ℤ} {x : ℝ}
    (hx : x ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1))
    (hj : j ∉ ({k, k + 1} : Finset ℤ)) : triangleFn 1 (x - j) = 0 := by
  have hj0 : j ≠ k ∧ j ≠ k + 1 := by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hj
  apply triangleFn_eq_zero (by norm_num)
  rcases lt_or_ge j k with h | h
  · have hjk : (j : ℝ) + 1 ≤ k := by exact_mod_cast (show j + 1 ≤ k by omega)
    exact (by linarith [hx.1] : (1 : ℝ) ≤ x - j).trans (le_abs_self _)
  · have hjk : (k : ℝ) + 2 ≤ j := by exact_mod_cast (show k + 2 ≤ j by omega)
    exact (by linarith [hx.2] : (1 : ℝ) ≤ -(x - j)).trans (neg_le_abs _)

/-- Only the two neighboring lattice values contribute. -/
theorem integerHatInterpolation_eq {k : ℤ} {x : ℝ}
    (hx : x ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1)) (a : ℤ → ℝ) :
    integerHatInterpolation a x =
      a k * ((k : ℝ) + 1 - x) + a (k + 1) * (x - k) := by
  unfold integerHatInterpolation
  rw [tsum_eq_sum (s := {k, k + 1}) (fun j hj => by
    rw [triangle_eq_zero_off_neighbors hx hj, mul_zero])]
  have hne : k ≠ k + 1 := by omega
  rw [sum_pair hne]
  have hleft : triangleFn 1 (x - k) = (k : ℝ) + 1 - x := by
    simp only [triangleFn, div_one, abs_of_nonneg (sub_nonneg.mpr hx.1),
      max_eq_left (by linarith [hx.2] : 0 ≤ 1 - (x - k))]
    ring
  have hright : triangleFn 1 (x - ((k + 1 : ℤ) : ℝ)) = x - k := by
    simp only [Int.cast_add, Int.cast_one]
    rw [triangleFn, div_one, abs_of_nonpos (by linarith [hx.2]),
      max_eq_left (by linarith [hx.1])]
    ring
  rw [hleft, hright]

theorem summable_integerHatInterpolation (a : ℤ → ℝ) (x : ℝ) :
    Summable (fun j : ℤ => a j * triangleFn 1 (x - j)) := by
  apply summable_of_ne_finset_zero (s := {⌊x⌋, ⌊x⌋ + 1})
  intro j hj
  rw [triangle_eq_zero_off_neighbors ⟨Int.floor_le x, (Int.lt_floor_add_one x).le⟩ hj,
    mul_zero]

/-- The triangle interpolation is locally a finite sum. -/
theorem continuous_integerHatInterpolation (a : ℤ → ℝ) :
    Continuous (integerHatInterpolation a) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let k : ℤ := ⌊x⌋
  let S : Finset ℤ := Finset.Icc (k - 1) (k + 2)
  have hc : Continuous (fun y : ℝ => ∑ j ∈ S, a j * triangleFn 1 (y - j)) := by
    apply continuous_finsetSum
    intro j hj
    exact continuous_const.mul ((continuous_triangleFn 1).comp (continuous_id.sub continuous_const))
  apply hc.continuousAt.congr_of_eventuallyEq
  have hleft : (k : ℝ) - 1 < x := by linarith [Int.floor_le x]
  have hright : x < (k : ℝ) + 2 := by linarith [Int.lt_floor_add_one x]
  filter_upwards [Ioo_mem_nhds hleft hright] with y hy
  apply tsum_eq_sum
  intro j hj
  have hj' : ¬ (k - 1 ≤ j ∧ j ≤ k + 2) := by simpa only [S, Finset.mem_Icc] using hj
  have hz : triangleFn 1 (y - j) = 0 := by
    apply triangleFn_eq_zero (by norm_num)
    rcases lt_or_ge j (k - 1) with h | h
    · have hjk : (j : ℝ) ≤ (k : ℝ) - 2 := by exact_mod_cast (show j ≤ k - 2 by omega)
      exact (by linarith [hy.1] : (1 : ℝ) ≤ y - j).trans (le_abs_self _)
    · have hjk : (k : ℝ) + 3 ≤ j := by exact_mod_cast (show k + 3 ≤ j by omega)
      exact (by linarith [hy.2] : (1 : ℝ) ≤ -(y - j)).trans (neg_le_abs _)
  rw [hz, mul_zero]

theorem integerHatInterpolation_nonneg {a : ℤ → ℝ} (ha : ∀ j, 0 ≤ a j) (x : ℝ) :
    0 ≤ integerHatInterpolation a x :=
  tsum_nonneg fun j => mul_nonneg (ha j) (triangleFn_nonneg 1 _)

theorem integerHatInterpolation_const (c x : ℝ) :
    integerHatInterpolation (fun _ => c) x = c := by
  rw [integerHatInterpolation_eq ⟨Int.floor_le x, (Int.lt_floor_add_one x).le⟩]
  ring

theorem integerHatInterpolation_le {a : ℤ → ℝ} {C : ℝ} (ha : ∀ j, a j ≤ C) (x : ℝ) :
    integerHatInterpolation a x ≤ C := by
  let k : ℤ := ⌊x⌋
  have hk0 : (k : ℝ) ≤ x := Int.floor_le x
  have hk1 : x ≤ (k : ℝ) + 1 := (Int.lt_floor_add_one x).le
  rw [integerHatInterpolation_eq ⟨hk0, hk1⟩]
  have hleft := mul_le_mul_of_nonneg_right (ha k) (by linarith only [hk1] : 0 ≤ (k : ℝ) + 1 - x)
  have hright := mul_le_mul_of_nonneg_right (ha (k + 1)) (sub_nonneg.mpr hk0)
  linarith only [hleft, hright]

@[simp] theorem integerHatInterpolation_int (a : ℤ → ℝ) (k : ℤ) :
    integerHatInterpolation a k = a k := by
  rw [integerHatInterpolation_eq (k := k) ⟨le_rfl, by linarith⟩]
  ring

theorem integerHatInterpolation_add (a b : ℤ → ℝ) (x : ℝ) :
    integerHatInterpolation (fun j => a j + b j) x =
      integerHatInterpolation a x + integerHatInterpolation b x := by
  simp only [integerHatInterpolation, add_mul]
  exact (summable_integerHatInterpolation a x).tsum_add (summable_integerHatInterpolation b x)

theorem integerHatInterpolation_sub (a b : ℤ → ℝ) (x : ℝ) :
    integerHatInterpolation (fun j => a j - b j) x =
      integerHatInterpolation a x - integerHatInterpolation b x := by
  simp only [integerHatInterpolation, sub_mul]
  exact (summable_integerHatInterpolation a x).tsum_sub (summable_integerHatInterpolation b x)

theorem integerHatInterpolation_mul (c : ℝ) (a : ℤ → ℝ) (x : ℝ) :
    integerHatInterpolation (fun j => c * a j) x = c * integerHatInterpolation a x := by
  simp only [integerHatInterpolation, mul_assoc, tsum_mul_left]

theorem integerHatInterpolation_sum {ι : Type*} (S : Finset ι) (a : ι → ℤ → ℝ) (x : ℝ) :
    integerHatInterpolation (fun j => ∑ i ∈ S, a i j) x =
      ∑ i ∈ S, integerHatInterpolation (a i) x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [integerHatInterpolation]
  | @insert i S hi ih =>
      simp only [sum_insert hi, integerHatInterpolation_add, ih]

/-- The origin coefficient interpolates to the central triangle. -/
theorem integerHatInterpolation_origin (x : ℝ) :
    integerHatInterpolation (fun j => if j = 0 then 1 else 0) x = triangleFn 1 x := by
  simp only [integerHatInterpolation, ite_mul, one_mul, zero_mul]
  rw [tsum_ite_eq]
  simp only [Int.cast_zero, sub_zero]

theorem integerHatInterpolation_neg (a : ℤ → ℝ) (x : ℝ) :
    integerHatInterpolation a (-x) = integerHatInterpolation (fun j => a (-j)) x := by
  unfold integerHatInterpolation
  rw [← (Equiv.neg ℤ).tsum_eq]
  apply tsum_congr
  intro j
  simp only [Equiv.neg_apply, Int.cast_neg, triangleFn, div_one]
  congr 2
  rw [show -x - -(j : ℝ) = -(x - j) by ring, abs_neg]

/-- Affine lattice data remain affine throughout every interval between the nodes. -/
theorem integerHatInterpolation_linear_on_Icc {a : ℤ → ℝ} {L : ℕ} {c x : ℝ}
    (ha : ∀ j : ℤ, 0 ≤ j → j ≤ (L : ℤ) → a j = (j : ℝ) * c)
    (hx : x ∈ Set.Icc (0 : ℝ) L) : integerHatInterpolation a x = x * c := by
  rcases eq_or_lt_of_le hx.2 with h | h
  · rw [h]
    simpa only [Int.cast_natCast] using
      (integerHatInterpolation_int a (L : ℤ)).trans (ha L (by omega) le_rfl)
  · let k : ℤ := ⌊x⌋
    have hk0 : 0 ≤ k := Int.floor_nonneg.mpr hx.1
    have hkL : k + 1 ≤ (L : ℤ) := by
      have hcast : (k : ℝ) < L := (Int.floor_le x).trans_lt h
      have hint : k < (L : ℤ) := by exact_mod_cast hcast
      omega
    rw [integerHatInterpolation_eq (k := k) ⟨Int.floor_le x, (Int.lt_floor_add_one x).le⟩,
      ha k hk0 (by omega), ha (k + 1) (by omega) hkL]
    push_cast
    ring

end GaloisForLFunctions.TransThresholdPairCorrelation
