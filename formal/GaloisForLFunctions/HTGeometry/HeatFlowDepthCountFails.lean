import GaloisForLFunctions.HTGeometry.ShiftAverageNonrealCount
import GaloisForLFunctions.HTGeometry.PolynomialHeatFlow

/-!
# The heat flow has no depth-resolved defect count

For the cosine flow, `cos(hD)p` has at most `2·#{roots w of p : Im w > h}` nonreal roots
(`nonrealRootCount_shiftAvg_le`): only roots deeper than `h` can survive as defects. The heat flow
`e^{−tD²}p` has the matching strip law (all roots of depth `≤ √(2t)` would be absorbed if they were
alone), but no matching count.

**Theorem** (`exists_polyHeat_nonrealRootCount_gt_deep`). For `p = (X² + 1)(X² + 4)` and `t = 3/5`,
the heat flow `e^{−tD²}p = X⁴ − (11/5)X² + 58/25 = (X² − 11/10)² + 111/100` has four nonreal roots,
while only the two roots `±2i` of `p` satisfy `(Im w)² > 2t = 6/5`. At the same second moment
`h² = 2t` the cosine flow keeps at most two (`shiftAvg_counterexample_le_two`).

The shallow pair `±i` is held off the real axis by the deep pair `±2i`: the interaction terms of the
heat dynamics `ż_k = 2Σ_{j≠k}(z_k − z_j)⁻¹` push an inner pair outward. The two-point average
`cos(hD)` has no such interaction, because its zeros are read off from one phase on a line.
-/

open Polynomial Complex Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The quartic `(X² + 1)(X² + 4)`. -/
def depthQuartic : ℝ[X] := X ^ 4 + C 5 * X ^ 2 + C 4

theorem natDegree_depthQuartic : depthQuartic.natDegree = 4 := by
  unfold depthQuartic
  compute_degree!

theorem depthQuartic_ne_zero : depthQuartic ≠ 0 := by
  intro h
  have := natDegree_depthQuartic
  rw [h, natDegree_zero] at this
  norm_num at this

theorem eval_iterate_derivative_depthQuartic (k : ℕ) (x : ℝ) :
    (derivative^[k] depthQuartic).eval x =
      (Nat.descFactorial 4 k : ℝ) * x ^ (4 - k) + 5 * ((Nat.descFactorial 2 k : ℝ) * x ^ (2 - k)) +
        (if k = 0 then 4 else 0) := by
  unfold depthQuartic
  rw [iterate_map_add, iterate_map_add, iterate_derivative_C_mul,
    iterate_derivative_X_pow_eq_smul, iterate_derivative_X_pow_eq_smul]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [iterate_derivative_C hk]
    simp [hk.ne', Algebra.smul_def]

theorem eval_polyHeat_depthQuartic (x : ℝ) :
    (polyHeat (3 / 5) depthQuartic).eval x = (x ^ 2 - 11 / 10) ^ 2 + 111 / 100 := by
  unfold polyHeat
  rw [natDegree_depthQuartic, eval_finsetSum]
  simp only [eval_mul, eval_C, eval_iterate_derivative_depthQuartic, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num [Nat.descFactorial, Nat.factorial]
  ring

theorem polyHeat_depthQuartic_roots : (polyHeat (3 / 5) depthQuartic).roots = 0 := by
  obtain ⟨-, hne⟩ := natDegree_polyHeat (3 / 5) depthQuartic_ne_zero
  refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
  have h := (mem_roots hne).mp hx
  rw [IsRoot, eval_polyHeat_depthQuartic] at h
  nlinarith [sq_nonneg (x ^ 2 - 11 / 10)]

theorem nonrealRootCount_polyHeat_depthQuartic :
    nonrealRootCount (polyHeat (3 / 5) depthQuartic) = 4 := by
  obtain ⟨hdeg, -⟩ := natDegree_polyHeat (3 / 5) depthQuartic_ne_zero
  rw [nonrealRootCount, hdeg, natDegree_depthQuartic, polyHeat_depthQuartic_roots]
  rfl

theorem X_sub_C_mul_X_add_C (a : ℂ) : (X - C a) * (X + C a) = X ^ 2 - C (a ^ 2) := by
  rw [C_pow]; ring

theorem map_depthQuartic :
    depthQuartic.map Complex.ofRealHom =
      ((X - C I) * (X - C (-I))) * ((X - C (2 * I)) * (X - C (-(2 * I)))) := by
  have h1 : (X - C I) * (X - C (-I)) = (X ^ 2 + 1 : ℂ[X]) := by
    rw [C_neg, sub_neg_eq_add, X_sub_C_mul_X_add_C, I_sq, C_neg, C_1]; ring
  have h2 : (X - C (2 * I)) * (X - C (-(2 * I))) = (X ^ 2 + C 4 : ℂ[X]) := by
    rw [C_neg, sub_neg_eq_add, X_sub_C_mul_X_add_C, mul_pow, I_sq]
    rw [show ((2 : ℂ) ^ 2 * -1) = -4 by norm_num, C_neg]; ring
  rw [h1, h2]
  unfold depthQuartic
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C,
    Complex.ofRealHom_eq_coe, Complex.ofReal_ofNat]
  have h5 : (C (5 : ℂ) : ℂ[X]) = C 4 + 1 := by rw [← C_1, ← C_add]; norm_num
  rw [h5]
  ring

theorem roots_map_depthQuartic :
    (depthQuartic.map Complex.ofRealHom).roots = {I, -I, 2 * I, -(2 * I)} := by
  rw [map_depthQuartic]
  have hA : (X - C I) * (X - C (-I)) ≠ (0 : ℂ[X]) :=
    mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
  have hB : (X - C (2 * I)) * (X - C (-(2 * I))) ≠ (0 : ℂ[X]) :=
    mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
  rw [roots_mul (mul_ne_zero hA hB), roots_mul hA, roots_mul hB, roots_X_sub_C, roots_X_sub_C,
    roots_X_sub_C, roots_X_sub_C]
  rfl

theorem card_deep_depthQuartic :
    Multiset.card ((depthQuartic.map Complex.ofRealHom).roots.filter
      (fun w => 2 * (3 / 5 : ℝ) < w.im ^ 2)) = 2 := by
  classical
  rw [roots_map_depthQuartic]
  simp only [Multiset.insert_eq_cons, Multiset.filter_cons, Multiset.filter_singleton]
  norm_num

/-- **No depth-resolved count for the heat flow.** -/
theorem exists_polyHeat_nonrealRootCount_gt_deep :
    ∃ (p : ℝ[X]) (t : ℝ), p ≠ 0 ∧ 0 < t ∧
      Multiset.card ((p.map Complex.ofRealHom).roots.filter (fun w => 2 * t < w.im ^ 2)) <
        nonrealRootCount (polyHeat t p) := by
  refine ⟨depthQuartic, 3 / 5, depthQuartic_ne_zero, by norm_num, ?_⟩
  rw [card_deep_depthQuartic, nonrealRootCount_polyHeat_depthQuartic]
  norm_num

/-- At the same second moment, e.g. `h = √(6/5)`, the cosine flow keeps at most two nonreal roots:
for every depth `1 < h < 2` only the pair `±2i` is deeper than `h`. -/
theorem shiftAvg_counterexample_le_two {h : ℝ} (h1 : 1 < h) (h2 : h < 2) :
    nonrealRootCount (shiftAvg h depthQuartic) ≤ 2 := by
  classical
  refine (nonrealRootCount_shiftAvg_le depthQuartic_ne_zero _).trans ?_
  rw [roots_map_depthQuartic]
  simp only [Multiset.insert_eq_cons, Multiset.filter_cons, Multiset.filter_singleton]
  simp [h2, (show ¬ h < 1 by linarith), (show ¬ h < -1 by linarith),
    (show ¬ h < -2 by linarith)]

end

end GaloisForLFunctions.HTGeometry
