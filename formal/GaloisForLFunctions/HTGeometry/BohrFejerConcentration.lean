import GaloisForLFunctions.HTGeometry.BohrFejerKernel

/-!
# Concentration of the Fejér kernel

Together with nonnegativity and mean one, the property that makes the Fejér kernel an approximate
identity is that it becomes uniformly small away from the zeros of `1 − cos(βu)`.  Summing the
geometric series gives `D_N(u) = (z^{N+1}−1)/(z−1)` with `z = e^{iβu}` of modulus one, so
`‖D_N(u)‖ ≤ 2/‖z−1‖` and

`F_N(u) ≤ 4 / ((N+1)·‖e^{iβu} − 1‖²) = 4 / ((N+1)·(2 − 2cos βu))`.

On the region `cos(βu) ≤ 1 − δ` this is at most `2/((N+1)δ)`, which tends to zero uniformly in `u`.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-- A character at a multiple frequency is a power of the character. -/
theorem expChar_nat_mul (β u : ℝ) (k : ℕ) :
    expChar ((k : ℝ) * β) u = (expChar β u) ^ k := by
  simp only [expChar]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The Dirichlet sum is a geometric sum. -/
theorem fejerSum_eq_geom (β : ℝ) (N : ℕ) (u : ℝ) :
    fejerSum β N u = ∑ k ∈ Finset.range (N + 1), (expChar β u) ^ k := by
  rw [fejerSum]
  exact Finset.sum_congr rfl fun k _ => expChar_nat_mul β u k

/-- The squared distance of a character from `1`. -/
theorem norm_expChar_sub_one_sq (β u : ℝ) :
    ‖expChar β u - 1‖ ^ 2 = 2 - 2 * Real.cos (β * u) := by
  have h := norm_expChar_sub_sq (β * u) 0
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_zero] at h
  exact h

/-- **Concentration bound.**  Away from the zeros of `1 − cos(βu)` the Fejér kernel is at most
`4/((N+1)(2 − 2cos βu))`. -/
theorem fejerKernel_norm_le (β : ℝ) (N : ℕ) {u : ℝ} (hu : Real.cos (β * u) < 1) :
    ‖fejerSum β N u‖ ^ 2 / ((N : ℝ) + 1)
      ≤ 4 / (((N : ℝ) + 1) * (2 - 2 * Real.cos (β * u))) := by
  have hpos : (0 : ℝ) < 2 - 2 * Real.cos (β * u) := by linarith
  have hznorm : ‖expChar β u‖ = 1 := norm_expChar β u
  have hzne : expChar β u ≠ 1 := by
    intro h
    have hsq := norm_expChar_sub_one_sq β u
    rw [h, sub_self, norm_zero] at hsq
    have h0 : (0 : ℝ) = 2 - 2 * Real.cos (β * u) := by simpa using hsq
    linarith
  have hdennorm : (0 : ℝ) < ‖expChar β u - 1‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero_of_ne hzne
  have hgeom : fejerSum β N u
      = ((expChar β u) ^ (N + 1) - 1) / (expChar β u - 1) := by
    rw [fejerSum_eq_geom]
    exact geom_sum_eq hzne (N + 1)
  have hnum : ‖(expChar β u) ^ (N + 1) - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, hznorm, one_pow, norm_one]
    norm_num
  have hbound : ‖fejerSum β N u‖ ≤ 2 / ‖expChar β u - 1‖ := by
    rw [hgeom, norm_div]
    exact div_le_div₀ (by norm_num) hnum hdennorm le_rfl
  have hsq : ‖fejerSum β N u‖ ^ 2 * (2 - 2 * Real.cos (β * u)) ≤ 4 := by
    have h1 : ‖fejerSum β N u‖ ^ 2 ≤ (2 / ‖expChar β u - 1‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hbound 2
    rw [div_pow, norm_expChar_sub_one_sq] at h1
    rw [← le_div_iff₀ hpos]
    calc ‖fejerSum β N u‖ ^ 2 ≤ (2 : ℝ) ^ 2 / (2 - 2 * Real.cos (β * u)) := h1
      _ = 4 / (2 - 2 * Real.cos (β * u)) := by norm_num
  have hN : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hsq, hN]

/-- **Uniform smallness off a neighbourhood of the kernel's peaks.** -/
theorem fejerKernel_norm_le_of_cos_le (β : ℝ) (N : ℕ) {u δ : ℝ} (hδ : 0 < δ)
    (hu : Real.cos (β * u) ≤ 1 - δ) :
    ‖fejerSum β N u‖ ^ 2 / ((N : ℝ) + 1) ≤ 2 / (((N : ℝ) + 1) * δ) := by
  have hlt : Real.cos (β * u) < 1 := by linarith
  refine (fejerKernel_norm_le β N hlt).trans ?_
  have hden : (0 : ℝ) < 2 - 2 * Real.cos (β * u) := by linarith
  have hge : 2 * δ ≤ 2 - 2 * Real.cos (β * u) := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hge, hδ, Nat.cast_nonneg (α := ℝ) N]

/-- The concentration bound tends to zero: the Fejér kernel is an approximate identity. -/
theorem tendsto_fejerBound (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => 2 / (((N : ℝ) + 1) * δ)) atTop (nhds 0) := by
  have hd : Tendsto (fun N : ℕ => ((N : ℝ) + 1) * δ) atTop atTop := by
    refine Filter.Tendsto.atTop_mul_const hδ ?_
    exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact tendsto_const_nhds.div_atTop hd

end

end GaloisForLFunctions
