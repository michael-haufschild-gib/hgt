import GaloisForLFunctions.RHTower.LiEvenCrossInfiniteCriticalAmplitudeSchattenBoundaryNoGo
import GaloisForLFunctions.HTGeometry.CanonicalProductE1Divisor

/-!
# An approaching quartet divisor with the Riemann zero count

Pair consecutive positive Xi ordinates, retaining the second ordinate of
each pair. Put two zeros there at depths `±1/(4(n+1))`, and reflect them
below the real axis. The positive count is the largest even integer below
the Xi count. Distinct depths separate all copies, including repeated
ordinates, and every zero approaches the critical line without lying on it.
-/

noncomputable section
open Complex Set Filter Topology
open GaloisForLFunctions.CountableDivisor
open _root_.RHTower

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- The second ordinate in the `n`-th consecutive pair of Xi zero copies. -/
def pairedXiHeight (n : ℕ) : ℝ := xiOrderedPositiveOrdinate (2 * n + 1)

/-- Strictly decreasing nonzero depths of the paired divisor. -/
def pairedXiDepth (n : ℕ) : ℝ := 1 / (4 * ((n : ℝ) + 1))

theorem pairedXiHeight_pos (n : ℕ) : 0 < pairedXiHeight n :=
  xiOrderedPositiveOrdinate_pos _

theorem pairedXiDepth_pos (n : ℕ) : 0 < pairedXiDepth n := by
  unfold pairedXiDepth
  positivity

theorem pairedXiDepth_lt_half (n : ℕ) : pairedXiDepth n < 1 / 2 := by
  rw [pairedXiDepth, div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith only [Nat.cast_nonneg (α := ℝ) n]

theorem pairedXiDepth_injective : Function.Injective pairedXiDepth := by
  intro n m h
  have h' : 4 * ((n : ℝ) + 1) = 4 * ((m : ℝ) + 1) :=
    inv_injective (by simpa only [pairedXiDepth, one_div] using h)
  have heq : (n : ℝ) = (m : ℝ) := by linarith only [h']
  exact_mod_cast heq

theorem tendsto_pairedXiDepth_zero : Tendsto pairedXiDepth atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  exact tendsto_const_nhds.div_atTop (h.const_mul_atTop (by norm_num : (0 : ℝ) < 4))

/-- Boolean signs label the horizontal and vertical halves of each quartet. -/
def quartetSign (b : Bool) : ℝ := if b then 1 else -1

theorem abs_quartetSign (b : Bool) : |quartetSign b| = 1 := by
  cases b <;> norm_num [quartetSign]

theorem quartetSign_ne_zero (b : Bool) : quartetSign b ≠ 0 := by
  cases b <;> norm_num [quartetSign]

theorem quartetSign_injective : Function.Injective quartetSign := by
  intro b c h
  cases b <;> cases c <;> norm_num [quartetSign] at h ⊢

/-- Centered quartet points; adding `1/2` gives the zeros in the critical strip. -/
def pairedXiPoint (q : ℕ × Bool × Bool) : ℂ :=
  (quartetSign q.2.1 * pairedXiDepth q.1 : ℝ) +
    (quartetSign q.2.2 * pairedXiHeight q.1 : ℝ) * I

@[simp] theorem pairedXiPoint_re (q : ℕ × Bool × Bool) :
    (pairedXiPoint q).re = quartetSign q.2.1 * pairedXiDepth q.1 := by
  simp [pairedXiPoint]

@[simp] theorem pairedXiPoint_im (q : ℕ × Bool × Bool) :
    (pairedXiPoint q).im = quartetSign q.2.2 * pairedXiHeight q.1 := by
  simp [pairedXiPoint]

theorem abs_pairedXiPoint_re (q : ℕ × Bool × Bool) :
    |(pairedXiPoint q).re| = pairedXiDepth q.1 := by
  rw [pairedXiPoint_re, abs_mul, abs_quartetSign,
    abs_of_pos (pairedXiDepth_pos _), one_mul]

theorem abs_pairedXiPoint_im (q : ℕ × Bool × Bool) :
    |(pairedXiPoint q).im| = pairedXiHeight q.1 := by
  rw [pairedXiPoint_im, abs_mul, abs_quartetSign,
    abs_of_pos (pairedXiHeight_pos _), one_mul]

theorem pairedXiPoint_ne_zero (q : ℕ × Bool × Bool) : pairedXiPoint q ≠ 0 := by
  intro h
  have := abs_pairedXiPoint_im q
  rw [h, Complex.zero_im, abs_zero] at this
  exact (pairedXiHeight_pos q.1).ne' this.symm

theorem pairedXiHeight_le_norm (q : ℕ × Bool × Bool) :
    pairedXiHeight q.1 ≤ ‖pairedXiPoint q‖ := by
  rw [← abs_pairedXiPoint_im q]
  exact Complex.abs_im_le_norm _

theorem pairedXiPoint_injective : Function.Injective pairedXiPoint := by
  rintro ⟨n, b, c⟩ ⟨m, d, e⟩ h
  have hn : n = m := pairedXiDepth_injective (by
    simpa only [abs_pairedXiPoint_re] using congrArg (fun z : ℂ => |z.re|) h)
  subst m
  have hb : b = d := quartetSign_injective (mul_right_cancel₀
    (pairedXiDepth_pos n).ne' (by simpa only [pairedXiPoint_re] using congrArg Complex.re h))
  have hc : c = e := quartetSign_injective (mul_right_cancel₀
    (pairedXiHeight_pos n).ne' (by simpa only [pairedXiPoint_im] using congrArg Complex.im h))
  subst d
  subst e
  rfl

/-- The pair cutoff is exactly half the Xi count, rounded down. -/
theorem pairedXiHeight_le_iff (n : ℕ) (T : ℝ) :
    pairedXiHeight n ≤ T ↔ n < (xiZeroCount T).toNat / 2 := by
  rw [pairedXiHeight, xiOrderedPositiveOrdinate_le_iff]
  have hcast := Int.toNat_of_nonneg (xiZeroCount_nonneg T)
  omega

theorem finite_pairedXiHeight_le (T : ℝ) : {n : ℕ | pairedXiHeight n ≤ T}.Finite := by
  have heq : {n : ℕ | pairedXiHeight n ≤ T} =
      (Finset.range ((xiZeroCount T).toNat / 2) : Set ℕ) := by
    ext n
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_range, pairedXiHeight_le_iff]
  rw [heq]
  exact Finset.finite_toSet _

theorem locallyFinite_pairedXiPoint : LocallyFiniteDivisor pairedXiPoint := by
  intro R
  have hf := (finite_pairedXiHeight_le R).prod (Set.toFinite (Set.univ : Set (Bool × Bool)))
  apply hf.subset
  intro q hq
  exact ⟨(pairedXiHeight_le_norm q).trans hq, Set.mem_univ _⟩

/-- Every positive reciprocal power above one is summable on the paired heights. -/
theorem summable_pairedXiHeight_inv_rpow {p : ℝ} (hp : 1 < p) :
    Summable (fun n : ℕ => (pairedXiHeight n)⁻¹ ^ p) := by
  exact (summable_xiOrderedPositiveOrdinate_inv_rpow hp).comp_injective
    (i := fun n : ℕ => 2 * n + 1) (by intro n m h; omega)

/-- The full quartet divisor has convergence exponent at most one. -/
theorem summable_pairedXiPoint_rpow_neg {p : ℝ} (hp : 1 < p) :
    Summable (fun q : ℕ × Bool × Bool => ‖pairedXiPoint q‖ ^ (-p)) := by
  have hh : Summable (fun n : ℕ => pairedXiHeight n ^ (-p)) := by
    apply (summable_pairedXiHeight_inv_rpow hp).congr
    intro n
    rw [Real.inv_rpow (pairedXiHeight_pos n).le,
      Real.rpow_neg (pairedXiHeight_pos n).le]
  have hmajor : Summable (fun q : ℕ × (Bool × Bool) => pairedXiHeight q.1 ^ (-p)) := by
    exact (summable_prod_of_nonneg (fun _ => by positivity)).mpr
      ⟨fun _ => Summable.of_finite, by simpa [tsum_fintype] using hh.mul_left 4⟩
  exact Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun q => Real.rpow_le_rpow_of_nonpos (pairedXiHeight_pos q.1)
      (pairedXiHeight_le_norm q) (by linarith only [hp])) hmajor

theorem summable_pairedXiPoint_inv_sq :
    Summable (fun q : ℕ × Bool × Bool => 1 / ‖pairedXiPoint q‖ ^ (2 : ℕ)) := by
  apply (summable_pairedXiPoint_rpow_neg (p := 2) (by norm_num)).congr
  intro q
  rw [Real.rpow_neg (norm_nonneg _), Real.rpow_two, one_div]

#print axioms pairedXiPoint_injective
#print axioms pairedXiHeight_le_iff
#print axioms summable_pairedXiPoint_inv_sq

end GaloisForLFunctions.InfiniteRankWeilTheory
