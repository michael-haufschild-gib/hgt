import GaloisForLFunctions.RHTower.ArchimedeanWeilCertificate

/-!
# Monotonicity of the weight, and the support refinement of the deficit bound

Two further sharpenings of the aperture certificate.

* **The weight is strictly decreasing.**  `K` falls monotonically from `+∞` to `-∞` on `(0, ∞)`:
  its first term `2 e^{-u/2}/(1 - e^{-2u})` has a decreasing positive numerator over an increasing
  positive denominator, and its second term `-4 cosh(u/2)` is decreasing.  This re-proves uniqueness
  of the sign change and, more usefully, supplies the explicit upper bound `K u ≤ K a` for `u ≥ a`,
  which is what bounds the negative mass of the kernel from above.

* **The support refinement.**  The crude deficit bound `D u ≤ 2 g 0` ignores that `f` is supported
  in an interval of length `S`.  For `u > S/2` the two overlap windows
  `[u - S/2, S/2]` and `[-(S/2), S/2 - u]` — on which `f` and its translate must both be supported
  for the correlation to be nonzero — are **disjoint**.  Hence
  `‖f‖²_A + ‖f‖²_B ≤ ‖f‖²`, so `|g u| ≤ ‖f‖_A ‖f‖_B ≤ g 0 / 2` and

  ```
     D u  ≤  (3/2) g 0        for u > S/2,
  ```

  improving the crude factor `2` by a quarter exactly on the upper half of the aperture, which is
  where the weight is most negative.

All statements are unconditional.
-/

namespace RHTower.ArchimedeanKernel

/-! ## The weight is strictly decreasing -/

/-- **`K` is strictly decreasing on the positive axis.** -/
theorem weilKernel_strictAntiOn : StrictAntiOn weilKernel (Set.Ioi (0 : ℝ)) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  have hA := one_sub_exp_neg_two_mul_pos ha'
  have hB := one_sub_exp_neg_two_mul_pos hb'
  have hnum : Real.exp (-b / 2) < Real.exp (-a / 2) := by
    apply Real.exp_lt_exp.mpr
    linarith
  have hden : 1 - Real.exp (-2 * a) < 1 - Real.exp (-2 * b) := by
    have h : Real.exp (-2 * b) < Real.exp (-2 * a) := by
      apply Real.exp_lt_exp.mpr
      linarith
    linarith
  have hposb : (0 : ℝ) < Real.exp (-b / 2) := Real.exp_pos _
  have hq : 2 * Real.exp (-b / 2) / (1 - Real.exp (-2 * b)) <
      2 * Real.exp (-a / 2) / (1 - Real.exp (-2 * a)) := by
    rw [div_lt_div_iff₀ hB hA]
    nlinarith [hposb, hA, hB, hnum, hden]
  have hc : Real.cosh (a / 2) < Real.cosh (b / 2) := by
    apply Real.cosh_lt_cosh.mpr
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ a / 2), abs_of_nonneg (by linarith : (0:ℝ) ≤ b / 2)]
    linarith
  rw [weilKernel, weilKernel]
  linarith

/-- Past any point `a > 0` the weight is bounded above by its value at `a`.  This is the bound that
controls the negative mass of the kernel. -/
theorem weilKernel_le_of_le {a u : ℝ} (ha : 0 < a) (hau : a ≤ u) : weilKernel u ≤ weilKernel a := by
  rcases lt_or_eq_of_le hau with h | h
  · exact le_of_lt (weilKernel_strictAntiOn ha (lt_of_lt_of_le ha hau) h)
  · rw [h]

/-! ## The support refinement -/

/-- For `u > S/2` the two overlap windows are disjoint. -/
theorem disjoint_overlap_windows {S u : ℝ} (h : S / 2 < u) :
    Disjoint (Set.Icc (u - S / 2) (S / 2)) (Set.Icc (-(S / 2)) (S / 2 - u)) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 : u - S / 2 ≤ x := hx.1
  have h2 : x ≤ S / 2 - u := hx'.2
  linarith

/-- Disjoint masses give a halved product: `a² + b² ≤ c` forces `a b ≤ c / 2`. -/
theorem mul_le_half_of_sq_add_sq_le {a b c : ℝ} (h : a ^ (2 : ℕ) + b ^ (2 : ℕ) ≤ c) : a * b ≤ c / 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- **The support-refined deficit bound.**  If the correlation at `u` is bounded by half the value
at the origin — which the disjointness of the overlap windows provides for `u > S/2` — then the
deficit is at most `(3/2) g 0` rather than `2 g 0`. -/
theorem deficit_le_three_halves {g0 gu : ℝ} (h : |gu| ≤ g0 / 2) :
    g0 - gu ≤ 3 / 2 * g0 := by
  have := neg_abs_le gu
  have := le_abs_self gu
  linarith

/-- The certificate inequality with the refined factor. -/
theorem deficit_mul_kernel_ge_refined {d m k : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 3 / 2 * m) :
    3 / 2 * m * min k 0 ≤ d * k := by
  rcases le_total 0 k with hk | hk
  · rw [min_eq_right hk]
    have : 0 ≤ d * k := mul_nonneg hd0 hk
    linarith
  · rw [min_eq_left hk]
    nlinarith

/-- Packaging: from disjoint window masses `α, β` with `α + β ≤ g 0`, the correlation is at most
half the value at the origin, and hence the deficit is at most `(3/2) g 0`. -/
theorem deficit_le_of_disjoint_masses {α β g0 gu : ℝ}
    (hsum : α ^ (2 : ℕ) + β ^ (2 : ℕ) ≤ g0) (hcorr : |gu| ≤ α * β) :
    g0 - gu ≤ 3 / 2 * g0 := by
  have hhalf : α * β ≤ g0 / 2 := mul_le_half_of_sq_add_sq_le hsum
  exact deficit_le_three_halves (le_trans hcorr hhalf)

end RHTower.ArchimedeanKernel
