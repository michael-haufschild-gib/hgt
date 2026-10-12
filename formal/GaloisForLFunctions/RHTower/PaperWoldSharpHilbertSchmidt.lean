import GaloisForLFunctions.RHTower.PaperWoldCompositeLower

/-! # Exact Hilbert–Schmidt threshold for the full arithmetic Wold kernel

The half-power boundary is sharp. The obstruction already lies in the even
composite entries and does not require information about the primes.
-/

namespace RHTower
noncomputable section
open Filter Topology
open scoped BigOperators

private theorem directed_norm_mono (s t : ℝ) (hst : s ≤ t) (q : ℕ × ℕ) :
    ‖paperWoldDirectedKernel s q‖ ≤ ‖paperWoldDirectedKernel t q‖ := by
  unfold paperWoldDirectedKernel
  split_ifs with h
  · simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ (q.1 : ℝ) + 1) _)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le
          (by linarith [Nat.cast_nonneg (α := ℝ) q.1]) (by linarith)) (abs_nonneg _))
      (abs_nonneg _)
  · exact le_rfl

private theorem directed_isHS_of_lt (t : ℝ) (ht : t < 1 / 2) :
    HilbertSchmidt.IsHS (paperWoldDirectedKernel t) := by
  let p : PaperWoldStrictHalf := ⟨max t 0, le_max_right _ _, max_lt ht (by norm_num)⟩
  have hp : HilbertSchmidt.IsHS (paperWoldDirectedKernel p.t) :=
    paperWoldFullKernel_isHS p
  exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun q => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (directed_norm_mono t p.t (le_max_left _ _) q)) hp

/-- At and above the half power, the actual composite submatrix has infinite energy. -/
theorem paperWoldDirectedKernel_not_isHS (t : {t : ℝ // 1 / 2 ≤ t}) :
    ¬ HilbertSchmidt.IsHS (paperWoldDirectedKernel t) := by
  intro h
  have hinj : Function.Injective (fun q : ℕ × ℕ => (2 * q.2 + 2, 2 * q.1 + 4)) := by
    intro a b hab
    have h1 := congrArg Prod.fst hab
    have h2 := congrArg Prod.snd hab
    apply Prod.ext <;> dsimp at * <;> omega
  have hc : Summable (fun q : ℕ × ℕ =>
      ‖paperWoldDirectedKernel t (2 * q.2 + 2, 2 * q.1 + 4)‖ ^ 2) :=
    h.comp_injective hinj
  have hb : Summable (fun m : ℕ => 1 / (144 * ((m : ℝ) + 1))) :=
    Summable.of_nonneg_of_le (fun m => by positivity) (fun m =>
      (paperWoldDirectedKernel_composite_column_lower t m).trans
        ((hc.prod_factor m).sum_le_tsum _ (fun _ _ => sq_nonneg _))) hc.prod
  have hh : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1)) := by
    exact (hb.mul_left 144).congr fun m => by field_simp
  apply Real.not_summable_one_div_natCast
  exact (summable_nat_add_iff 1).mp (by simpa only [Nat.cast_add, Nat.cast_one] using hh)

/-- Exact domain, including every negative exponent as well as the native nonnegative range. -/
theorem paperWoldDirectedKernel_isHS_iff (t : ℝ) :
    HilbertSchmidt.IsHS (paperWoldDirectedKernel t) ↔ t < 1 / 2 := by
  constructor
  · intro h
    by_contra hn
    exact paperWoldDirectedKernel_not_isHS ⟨t, le_of_not_gt hn⟩ h
  · exact directed_isHS_of_lt t

/-- Positive harmonic energy survives after summing finitely many composite columns. -/
theorem paperWoldDirectedKernel_composite_triangle_lower
    (t : {t : ℝ // 1 / 2 ≤ t}) (N : ℕ) :
    (1 / 144 : ℝ) * (∑ m ∈ Finset.range N, 1 / ((m : ℝ) + 1)) ≤
      ∑ m ∈ Finset.range N, ∑ k ∈ Finset.range (m + 1),
        ‖paperWoldDirectedKernel t (2 * k + 2, 2 * m + 4)‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  have he : (1 / 144 : ℝ) * (1 / ((m : ℝ) + 1)) =
      1 / (144 * ((m : ℝ) + 1)) := by rw [one_div, one_div, one_div, mul_inv_rev, mul_comm]
  rw [he]
  exact paperWoldDirectedKernel_composite_column_lower t m

end
end RHTower
