import GaloisForLFunctions.RHTower.DisplacementMassBlindness

/-!
# The scaling degree law

Stepping back: this field controls masses, moments, energies and frequencies, and needs to control a
height. The gap between the two is usually described as a missing conversion law. That description is
not quite right, and the correct one is sharper.

Conversion laws from averages to heights are not missing. Sobolev embedding, Bernstein's inequality
and the Landau–Kolmogorov interpolation inequalities all convert integral control into sup control,
and the last of them is even *sharp* on the family that matters here: for one bump,
`‖b‖_∞² ≍ ‖b‖_{L¹}·‖b'‖_{L^∞}`, with the displacement cancelling exactly. The trouble is that every
such law is **scale-covariant**: it converts between norms of different homogeneity by supplying a
scale, and the only scale in the problem is the displacement itself — the unknown.

This module proves the underlying dimensional fact. The bump family is a single profile acted on by
the scaling group,

  `bumpKernel (c·d) (c·g) (c·t) = bumpKernel d g t`,

so a functional of the family is graded by its homogeneity degree under that action. Two facts then
close the question:

* the peak value is **degree zero**: `F (bumpKernel d g g) = F 1` for every `F` and every `d ≠ 0`;
* **every** pointwise average is **degree one**: for every `F` and every window,
  `∫ F(bump) = d · (profile integral)`, the factor `d` being the Jacobian of the scaling.

Consequently no pointwise-average functional — no `L^p` norm for finite `p`, no mollified moment, no
smoothed counting function, no nonlinear average whatever — is scale-invariant, and each of them
tends to zero with the displacement while the peak does not move. This strictly generalises the
earlier mass-blindness statement, which was the case `F = id`.

The positive reading is the useful one. The degree-zero class is not a single functional. Besides the
supremum it contains the total variation, since a bump rises once from `0` to `1` and falls once back,
so its variation is exactly `2` whatever its width; and it contains the count of bumps. So the target
is wider than "the sup", and any of these may be attacked. What no linear conversion can do is change
the degree: **a producer must supply a scale, and the only intrinsic scale in the zero distribution
is the spacing.** That is why every wall in this field — the mollified floor, the Littlewood slope,
the inner band, the clustered regime of the monomial witness — is the same wall.
-/

open Real MeasureTheory

namespace RHTower

noncomputable section

/-- **Exact scale covariance.** The bump family is one profile acted on by the scaling group. -/
theorem bumpKernel_scaling {c : ℝ} (hc : c ≠ 0) (d g t : ℝ) :
    bumpKernel (c * d) (c * g) (c * t) = bumpKernel d g t := by
  rw [bumpKernel, bumpKernel, show c * t - c * g = c * (t - g) by ring, mul_pow, mul_pow,
    ← mul_add, mul_div_mul_left _ _ (pow_ne_zero 2 hc)]

/-- The peak value is **degree zero**: it does not see the displacement. -/
theorem comp_bumpKernel_peak (F : ℝ → ℝ) {d : ℝ} (hd : d ≠ 0) (g : ℝ) :
    F (bumpKernel d g g) = F 1 := by
  rw [bumpKernel_peak hd]

/-- **Every pointwise average is degree one.** For any `F` whatever, the window average of `F`
applied to the bump is the displacement times a profile integral: the factor is exactly the Jacobian
of the scaling. -/
theorem integral_comp_bumpKernel (F : ℝ → ℝ) {d : ℝ} (hd : 0 < d) (g R : ℝ) :
    (∫ t in (g - R)..(g + R), F (bumpKernel d g t))
      = d * ∫ x in (-(R / d))..(R / d), F (1 / (1 + x ^ (2 : ℕ))) := by
  have hd0 : d ≠ 0 := hd.ne'
  have hfun : (fun t => F (bumpKernel d g t))
      = fun t => (fun y => F (1 / (1 + (y / d) ^ (2 : ℕ)))) (t - g) := by
    funext t
    rw [bumpKernel_eq_scaled hd0]
  rw [hfun, intervalIntegral.integral_comp_sub_right
      (fun y => F (1 / (1 + (y / d) ^ (2 : ℕ)))) g,
    show g - R - g = -R by ring, show g + R - g = R by ring,
    intervalIntegral.integral_comp_div (fun x => F (1 / (1 + x ^ (2 : ℕ)))) hd0,
    smul_eq_mul, neg_div]

/-- With a uniformly bounded profile the whole average is `O(d)`. -/
theorem abs_integral_comp_bumpKernel_le (F : ℝ → ℝ) {d : ℝ} (hd : 0 < d) (g R : ℝ) {C : ℝ}
    (hC : ∀ S : ℝ, |∫ x in (-S)..S, F (1 / (1 + x ^ (2 : ℕ)))| ≤ C) :
    |∫ t in (g - R)..(g + R), F (bumpKernel d g t)| ≤ C * d := by
  rw [integral_comp_bumpKernel F hd g R, abs_mul, abs_of_pos hd, mul_comm d _]
  exact mul_le_mul_of_nonneg_right (hC (R / d)) hd.le

/-- **The degree law.** For every `F`, every amplification and every tolerance there is a
displacement whose window averages of `F` all stay under the tolerance, while the value of `F` at
the peak is unchanged. No pointwise average, linear or not, sees the displacement go to zero the way
the height does — because they have different homogeneity degrees. -/
theorem exists_small_average_full_peak (F : ℝ → ℝ) (g : ℝ) {C ε : ℝ} (hC : 0 < C)
    (hCb : ∀ S : ℝ, |∫ x in (-S)..S, F (1 / (1 + x ^ (2 : ℕ)))| ≤ C) (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧
      (∀ R : ℝ, |∫ t in (g - R)..(g + R), F (bumpKernel d g t)| < ε) ∧
      F (bumpKernel d g g) = F 1 := by
  refine ⟨ε / (2 * C), by positivity, fun R => ?_,
    comp_bumpKernel_peak F (by positivity) g⟩
  have hb := abs_integral_comp_bumpKernel_le F (show (0 : ℝ) < ε / (2 * C) by positivity) g R hCb
  have h2 : C * (ε / (2 * C)) = ε / 2 := by field_simp
  rw [h2] at hb
  linarith

end

end RHTower
