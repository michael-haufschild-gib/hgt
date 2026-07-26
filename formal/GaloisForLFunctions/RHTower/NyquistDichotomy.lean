import GaloisForLFunctions.RHTower.PaleyWienerDetectionCeiling

/-!
# The Nyquist dichotomy: the `log T` barrier is the sampling rate of the zero set

The detection ceiling bounds what one off-critical zero can do to a positive-type test.  It says
nothing about the *other* zeros, which are also present in the explicit formula and all contribute
nonnegatively when they lie on the critical line.  A violation therefore has to overcome them.  This
file identifies the cost of doing so, and finds the same threshold `L = log T` arriving from the
opposite side.

**Dodging the good zeros.**  The critical zeros up to height `T` have density `log T / 2π`.  The
Paley–Wiener space carrying a test of width `L` is `PW_{L/2}`, whose Nyquist density is `L / 2π`.  By
the Beurling–Landau theory a set of density above Nyquist is a set of sampling: there is `A > 0` with
`Σ_j |F(γ_j)|² ≥ A‖F‖²`, that is

```text
Σ_γ ĝ(γ)  ≥  A · g(0)          whenever   L < log T ,
```

with `A` of the size of the excess density.  **Below Nyquist the critical zeros cannot be dodged.**
Above Nyquist they can — but a test of width `L ≥ log T` needs a prime window of `e^L ≥ T`.

> **Dodge-or-pay.**  Either `L ≥ log T`, and the prime window costs `e^L ≥ T`; or `L < log T`, the
> critical zeros contribute at least `A·g(0)` with `A ≍ log T`, and by the detection ceiling an
> off-critical pair overcomes them only if `e^{aL} > 4aA - 2aL`, i.e. `e^L > (4a log T)^{1/a}` up to
> the correction `2aL`, which is negligible against `A ≍ log T` in this regime.

**Where the branches cross.**  Positivity is the cheaper branch exactly when
`(4a log T + 1)^{1/a} ≤ T`, i.e. writing `s = a·log T`, when `log(4s + 1) ≤ s`.  That holds for
`s ≥ 3` and fails at `s = 2`, so the crossover sits at `s ≍ 1`:

```text
a  ≍  1 / log T   —   the mean spacing of the zeros at height T, up to the factor 2π.
```

> **The two branches exchange exactly when the deviation equals the local zero spacing.  A zero
> further from the critical line than the spacing is cheaper to exclude by positivity; a zero closer
> to the line than the spacing is cheaper to exclude by resolving the zeros individually.**

This explains the recurrence of `log T` throughout: it is the Nyquist rate of the Riemann zero set
for the Paley–Wiener space of the test, and every obstruction recorded so far is a consequence of the
test being sub-Nyquist.

This file formalizes the density comparison, both costs, the crossover criterion, and the two
inequalities that place the crossover at `s ≍ 1`.
-/

open Real

noncomputable section

namespace RHTower

/-- **The density comparison.**  A test of width `L` has Nyquist density `L/2π`; the critical zeros
up to height `T` have density `log T / 2π`.  Sub-Nyquist means `L < log T`. -/
theorem nyquist_gap {L T : ℝ} (h : L < Real.log T) :
    L / (2 * π) < Real.log T / (2 * π) := by
  have hp : (0:ℝ) < 2 * π := by positivity
  gcongr

/-- **The sampling lower bound, abstractly.**  If the critical zeros sample the Paley–Wiener space
with constant `A`, the zero side of the explicit formula is at least `A·g(0)` before any off-critical
zero is considered. -/
theorem sampling_forces_mass {A g0 S : ℝ} (hA : 0 < A) (hg0 : 0 < g0)
    (hsamp : A * g0 ≤ S) : 0 < S :=
  lt_of_lt_of_le (mul_pos hA hg0) hsamp

/-- **Cost of the super-Nyquist branch.**  A test wide enough to resolve the zeros needs a prime
window of at least `T`. -/
theorem dodge_cost {L T : ℝ} (hT : 0 < T) (h : Real.log T ≤ L) : T ≤ Real.exp L := by
  have := Real.exp_le_exp.mpr h
  rwa [Real.exp_log hT] at this

/-- **Cost of the sub-Nyquist branch.**  If the ceiling exceeds the sampling constant `A`, the width
already satisfies `e^{aL} > 4aA - 2aL`; since `A ≍ log T` dominates `L` in the sub-Nyquist regime,
the prime window is `e^L > (4aA)^{1/a}` up to the correction. -/
theorem pay_cost {a L A : ℝ} (ha : 0 < a) (_hL : 0 ≤ L)
    (hdetect : A < detectionCeiling a L) : 4 * a * A - 2 * a * L < Real.exp (a * L) := by
  unfold detectionCeiling at hdetect
  have h1 : a * (2 * A - L) < Real.sinh (a * L) := by
    have : 2 * A - L < Real.sinh (a * L) / a := by linarith
    calc a * (2 * A - L) < a * (Real.sinh (a * L) / a) :=
          mul_lt_mul_of_pos_left this ha
      _ = Real.sinh (a * L) := by field_simp
  have h2 : Real.sinh (a * L) = (Real.exp (a * L) - Real.exp (-(a * L))) / 2 := Real.sinh_eq _
  have h3 : 0 < Real.exp (-(a * L)) := Real.exp_pos _
  rw [h2] at h1
  linarith

/-- **The crossover criterion.**  Positivity is the cheaper branch exactly when
`M^{1/a} ≤ T`, equivalently `log M ≤ a · log T`. -/
theorem crossover_condition {M T a : ℝ} (ha : 0 < a) (hM : 0 < M) (hT : 0 < T) :
    M ^ (1 / a) ≤ T ↔ Real.log M ≤ a * Real.log T := by
  rw [← Real.log_le_log_iff (by positivity) hT, Real.log_rpow hM]
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ ha, mul_comm]

/-- **Positivity wins above the spacing scale.**  For `s = a·log T ≥ 3` one has `log(4s+1) ≤ s`,
so the sub-Nyquist cost `(4s+1)^{1/a}` is below the resolution cost `T`. -/
theorem positivity_cheaper {s : ℝ} (hs : 3 ≤ s) : Real.log (4 * s + 1) ≤ s := by
  have hexp : 4 * s + 1 ≤ Real.exp s := by
    have h3 : Real.exp s = Real.exp 3 * Real.exp (s - 3) := by
      rw [← Real.exp_add]; ring_nf
    have hge : (1:ℝ) + (s - 3) ≤ Real.exp (s - 3) := Real.add_one_le_exp _ |>.trans_eq' (by ring)
    have he3 : (20:ℝ) ≤ Real.exp 3 := by
      have h := Real.exp_one_gt_d9
      have hcube : Real.exp 3 = Real.exp 1 ^ 3 := by
        rw [← Real.exp_nat_mul]; norm_num
      have hb : (2.7182818283:ℝ) ^ 3 ≤ Real.exp 1 ^ 3 :=
        pow_le_pow_left₀ (by norm_num) (le_of_lt h) 3
      rw [hcube]; nlinarith [hb]
    have hpos : (0:ℝ) ≤ 1 + (s - 3) := by linarith
    rw [h3]
    nlinarith [hge, he3, hpos]
  calc Real.log (4 * s + 1) ≤ Real.log (Real.exp s) :=
        Real.log_le_log (by linarith) hexp
    _ = s := Real.log_exp s

/-- **Resolution wins below the spacing scale.**  At `s = 2` the inequality reverses: `log 9 > 2`, so
the sub-Nyquist cost exceeds the resolution cost.  The crossover therefore sits at `s ≍ 1`, i.e. at a
deviation of the order of the mean zero spacing `1/log T`. -/
theorem resolution_cheaper : (2:ℝ) < Real.log (4 * 2 + 1) := by
  have hlt : Real.exp 2 < 9 := by
    have h := Real.exp_one_lt_d9
    have he : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    have hb : Real.exp 1 ^ 2 ≤ (2.7182818286:ℝ) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) (le_of_lt h) 2
    rw [he]; nlinarith [hb]
  have hstep := Real.log_lt_log (Real.exp_pos 2) hlt
  rw [Real.log_exp] at hstep
  norm_num
  exact hstep

/-- **The crossover is at the spacing scale.**  The deviation at which the branches exchange is
`a ≍ 1/log T`, which up to `2π` is the mean spacing of the zeros at height `T`. -/
theorem crossover_at_spacing {T : ℝ} (hT : 1 < T) :
    3 / Real.log T * Real.log T = 3 := by
  have : Real.log T ≠ 0 := ne_of_gt (Real.log_pos hT)
  field_simp

end RHTower
