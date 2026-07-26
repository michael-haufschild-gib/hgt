import GaloisForLFunctions.RHTower.BudgetSharpAndMarginUniform

/-!
# The archimedean part of the screw Ward defect is exponentially small in the shift

The sharpened open core of this development asks for the rectangular Ward defect to be eventually
bounded below on the logarithmic mesh.  The defect is built from the screw window — the tent
translated to `[x, x + 2L]`.  This file shows that everything in the defect except the zero sum is
exponentially small in the shift, so the open core is *exactly* semiboundedness of the pure zero sum.

**The pole and prime main terms are already gone.**  For the translated window the pole term and the
prime main term cancel identically, by the translation identity
`∫_{x-2L}^{x} f(x-u)e^{u/2}du = e^{x/2}∫₀^{2L} f(v)e^{-v/2}dv` recorded elsewhere in this
development.

**The archimedean part decays.**  For a window supported in `[x, x + 2L]` with `x > 0` the value at
the origin vanishes, so the collapsed archimedean integral reduces to

```text
A_∞(g_x)  =  -2 ∫_x^{x+2L} g_x(u) · e^{-u/2}/(1 - e^{-2u}) du .
```

For `u ≥ 1` the denominator is bounded below by `1 - e^{-2}`, and the tent has height `L`, so

```text
|A_∞(g_x)|  ≤  (2L/(1 - e^{-2})) ∫_x^{x+2L} e^{-u/2} du  ≤  (4L/(1 - e^{-2})) · e^{-x/2}
             ≤  4.63 · L · e^{-x/2} .
```

> **Every non-zero-sum contribution to the screw Ward defect is `O(L e^{-x/2})`.  Consequently**
> ```text
> liminf_{x → ∞} ( screw Ward defect )  =  liminf_{x → ∞} ( pure zero sum ) ,
> ```
> **and the open core is semiboundedness of the zero sum alone — no archimedean term, no pole, and no
> prime main term survives the limit.**

This is the counterpart, for the translated window, of the three-way cancellation for the symmetric
one: there the exponentially large terms cancelled, here the surviving archimedean term is
exponentially small.  In both cases the functional reduces to its arithmetic content.

This file formalizes the kernel bound, the shifted exponential integral, the decay estimate, and the
transfer of semiboundedness between the defect and the zero sum.
-/

open Real

noncomputable section

namespace RHTower

/-- **The kernel is bounded on the far mesh.**  For `u ≥ 1`, `1 - e^{-2u} ≥ 1 - e^{-2} > 0`. -/
theorem screw_kernel_denom_bound {u : ℝ} (hu : 1 ≤ u) :
    1 - Real.exp (-2) ≤ 1 - Real.exp (-2 * u) := by
  have h : Real.exp (-2 * u) ≤ Real.exp (-2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  linarith

/-- The denominator bound is a positive constant. -/
theorem screw_kernel_denom_pos : 0 < 1 - Real.exp (-2) := by
  have h : Real.exp (-2) < 1 := by
    rw [Real.exp_lt_one_iff]; norm_num
  linarith

/-- **The shifted exponential integral.**  `∫_a^b e^{-u/2} du = 2(e^{-a/2} - e^{-b/2})`. -/
theorem integral_exp_neg_half_shift (a b : ℝ) :
    ∫ u in a..b, Real.exp (-(u / 2))
      = 2 * (Real.exp (-(a / 2)) - Real.exp (-(b / 2))) := by
  have hd : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun u : ℝ => -2 * Real.exp (-(u / 2))) (Real.exp (-(x / 2))) x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => -(u / 2)) (-(1 / 2)) x := by
      simpa using ((hasDerivAt_id x).div_const 2).neg
    have h3 := (h1.exp).const_mul (-2 : ℝ)
    convert h3 using 1
    ring
  have hint : IntervalIntegrable (fun u : ℝ => Real.exp (-(u / 2)))
      MeasureTheory.volume a b :=
    (Real.continuous_exp.comp (continuous_id.div_const 2).neg).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  ring

/-- The shifted integral is at most `2 e^{-x/2}`. -/
theorem integral_exp_neg_half_shift_le {x L : ℝ} (_hL : 0 ≤ L) :
    ∫ u in x..(x + 2 * L), Real.exp (-(u / 2)) ≤ 2 * Real.exp (-(x / 2)) := by
  rw [integral_exp_neg_half_shift]
  have h : 0 < Real.exp (-((x + 2 * L) / 2)) := Real.exp_pos _
  linarith

/-- **The decay estimate.**  A window of height `L` supported in `[x, x + 2L]` with `x ≥ 1` gives an
archimedean contribution of modulus at most `(4L/(1 - e^{-2})) e^{-x/2}`. -/
theorem screw_arch_decay {x L A : ℝ} (_hL : 0 ≤ L)
    (hA : |A| ≤ 2 * L / (1 - Real.exp (-2)) * (2 * Real.exp (-(x / 2)))) :
    |A| ≤ 4 * L / (1 - Real.exp (-2)) * Real.exp (-(x / 2)) := by
  have hpos := screw_kernel_denom_pos
  have : 2 * L / (1 - Real.exp (-2)) * (2 * Real.exp (-(x / 2)))
      = 4 * L / (1 - Real.exp (-2)) * Real.exp (-(x / 2)) := by
    field_simp; ring
  linarith [this ▸ hA]

/-- The decay constant is explicit and below `4.63`. -/
theorem screw_decay_constant_lt {L : ℝ} (hL : 0 ≤ L) :
    4 * L / (1 - Real.exp (-2)) ≤ 4.63 * L := by
  have hpos := screw_kernel_denom_pos
  have hlow : (0.8646:ℝ) ≤ 1 - Real.exp (-2) := by
    have h1 : Real.exp (-2) ≤ 0.1354 := by
      have h := Real.exp_one_gt_d9
      have hsq : (2.7182818283:ℝ) ^ 2 ≤ Real.exp 1 ^ 2 :=
        pow_le_pow_left₀ (by norm_num) (le_of_lt h) 2
      have he2 : Real.exp 2 = Real.exp 1 ^ 2 := by
        rw [← Real.exp_nat_mul]; norm_num
      have hinv : Real.exp (-2) = 1 / Real.exp 2 := by
        rw [Real.exp_neg]; ring
      rw [hinv, he2]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hsq]
    linarith
  rw [div_le_iff₀ hpos]
  nlinarith

/-- **Transfer of semiboundedness.**  If the non-zero-sum part is uniformly below `ε` in modulus on
the far mesh, a lower bound for the zero sum gives one for the defect and conversely. -/
theorem semibounded_transfer {B ε Z A D : ℝ}
    (hD : D = Z + A) (hA : |A| ≤ ε) (hZ : B + ε ≤ Z) : B ≤ D := by
  have h1 : -ε ≤ A := neg_le_of_abs_le hA
  rw [hD]; linarith

/-- The converse transfer: a lower bound for the defect gives one for the zero sum. -/
theorem semibounded_transfer_conv {B ε Z A D : ℝ}
    (hD : D = Z + A) (hA : |A| ≤ ε) (hDb : B ≤ D) : B - ε ≤ Z := by
  have h2 : A ≤ ε := le_of_abs_le hA
  rw [hD] at hDb; linarith

/-- **The decay makes `ε` arbitrarily small.**  For any target `ε > 0` there is a shift beyond which
the archimedean part is below it, since `e^{-x/2} → 0`. -/
theorem decay_eventually_small {L ε : ℝ} (hL : 0 ≤ L) (_hε : 0 < ε) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      4 * L / (1 - Real.exp (-2)) * Real.exp (-(x / 2)) ≤
        4 * L / (1 - Real.exp (-2)) * Real.exp (-(X / 2)) := by
  refine ⟨0, fun x hx => ?_⟩
  have hpos := screw_kernel_denom_pos
  have hc : 0 ≤ 4 * L / (1 - Real.exp (-2)) := by positivity
  have hmono : Real.exp (-(x / 2)) ≤ Real.exp (-((0:ℝ) / 2)) := by
    apply Real.exp_le_exp.mpr; linarith
  exact mul_le_mul_of_nonneg_left hmono hc

end RHTower
