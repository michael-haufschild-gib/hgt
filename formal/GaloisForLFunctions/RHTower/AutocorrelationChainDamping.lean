import GaloisForLFunctions.RHTower.EffectiveMeanValuePrimeSymbol

/-!
# Chain damping of the prime term in the truncated Weil functional

The prime side of the Weil functional pairs the test function with its own translates:

```text
Σ_{n ≤ e^L} 2 Λ(n) n^{-1/2} · Re ⟨h, T_{log n} h⟩,      supp h ⊆ an interval of length L.
```

The naive bound is `|⟨h, T_a h⟩| ≤ ‖h‖²`, which is what every ceiling in this programme has used.  It
is **not sharp**, and the loss is largest exactly where the prime mass is: at the heaviest terms.

Compressing the translation `T_a` to functions supported in an interval of length `L` decomposes the
space into chains `x, x+a, x+2a, …` meeting the support, each of length at most `M = ⌊L/a⌋ + 1`.  On
a chain of length `M` the operator is the nilpotent shift, whose numerical radius is
`cos(π/(M+1))` — equivalently, the largest eigenvalue of the path-graph adjacency matrix `P_M` is
`2cos(π/(M+1))`, classical.  Hence

```text
| Re ⟨h, T_a h⟩ |  ≤  cos( π / (⌊L/a⌋ + 2) ) · ‖h‖² .
```

The certificate is the sine substitution: with `θ = π/(M+1)` and `w_j = sin(jθ)`, the recurrence
`w_{j-1} + w_{j+1} = 2cos θ · w_j` makes the weighted AM–GM inequalities
`2 v_j v_{j+1} ≤ (w_{j+1}/w_j) v_j² + (w_j/w_{j+1}) v_{j+1}²` telescope, every coefficient collapsing
to the constant `2cos θ`.

Applied to the Weil prime term, the damping factor is `cos(π/(⌊L/log n⌋+2))`:

```text
log n ∈ (L/2, L]  ⟹  M = 2,  factor cos(π/3) = 1/2
log n ∈ (L/3, L/2] ⟹ M = 3,  factor cos(π/4) = √2/2 ≈ 0.707
log n ≤ L/k        ⟹ M = k+1, factor cos(π/(k+2)) → 1.
```

Since `Σ_{n ≤ e^L} Λ(n) n^{-1/2} ≍ 2e^{L/2}` is dominated by `n` near `e^L`, where the factor is
exactly `1/2`, the sharp bound on the prime term is **asymptotically half** the naive one.  That
factor of two is a genuine, unconditional gain in the archimedean-versus-prime competition that
every ceiling of this programme has been measuring.

This file formalizes the sine recurrence that drives the certificate, the weighted AM–GM step, and
the two sharpest cases `M = 2` and `M = 3` — the ones carrying the dominant prime mass.
-/

open Real

noncomputable section

namespace RHTower

/-- The recurrence behind the sine certificate: `sin(a-b) + sin(a+b) = 2 cos b · sin a`. -/
theorem sin_sub_add_sin_add (a b : ℝ) :
    Real.sin (a - b) + Real.sin (a + b) = 2 * Real.cos b * Real.sin a := by
  rw [Real.sin_sub, Real.sin_add]
  ring

/-- Weighted AM–GM, the step that the sine weights make telescope. -/
theorem two_mul_le_weighted {t x y : ℝ} (ht : 0 < t) :
    2 * x * y ≤ t * x ^ (2 : ℕ) + t⁻¹ * y ^ (2 : ℕ) := by
  have hsq : 0 ≤ (Real.sqrt t * x - (Real.sqrt t)⁻¹ * y) ^ (2 : ℕ) := sq_nonneg _
  have hst : Real.sqrt t ^ (2 : ℕ) = t := Real.sq_sqrt ht.le
  have hstpos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hinv : ((Real.sqrt t)⁻¹) ^ (2 : ℕ) = t⁻¹ := by
    rw [inv_pow, hst]
  have hcross : Real.sqrt t * (Real.sqrt t)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hstpos)
  have hexp : (Real.sqrt t * x - (Real.sqrt t)⁻¹ * y) ^ (2 : ℕ)
      = t * x ^ (2 : ℕ) - 2 * x * y + t⁻¹ * y ^ (2 : ℕ) := by
    have hstep : (Real.sqrt t * x - (Real.sqrt t)⁻¹ * y) ^ (2 : ℕ)
        = (Real.sqrt t) ^ (2 : ℕ) * x ^ (2 : ℕ)
          - 2 * (Real.sqrt t * (Real.sqrt t)⁻¹) * (x * y)
          + ((Real.sqrt t)⁻¹) ^ (2 : ℕ) * y ^ (2 : ℕ) := by ring
    rw [hstep, hst, hinv, hcross]; ring
  rw [hexp] at hsq
  linarith

/-- **Chain length two: the sharp damping factor is `cos(π/3) = 1/2`.**  This is the case carrying
the dominant prime mass, `log n ∈ (L/2, L]`. -/
theorem chain_two_bound (v₀ v₁ : ℝ) :
    |v₀ * v₁| ≤ (1 / 2 : ℝ) * (v₀ ^ (2 : ℕ) + v₁ ^ (2 : ℕ)) := by
  rcases abs_cases (v₀ * v₁) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; nlinarith [sq_nonneg (v₀ - v₁)]
  · rw [h]; nlinarith [sq_nonneg (v₀ + v₁)]

/-- `cos(π/3) = 1/2`, so the chain-two constant is exactly the numerical radius of the nilpotent
shift of order two. -/
theorem cos_pi_div_three_eq : Real.cos (Real.pi / 3) = 1 / 2 := by
  rw [Real.cos_pi_div_three]

/-- **Chain length three: the sharp damping factor is `cos(π/4) = √2/2`.**  The extremal vector is
`(sin θ, sin 2θ, sin 3θ)` with `θ = π/4`. -/
theorem chain_three_bound (v₀ v₁ v₂ : ℝ) :
    v₀ * v₁ + v₁ * v₂ ≤ (Real.sqrt 2 / 2) * (v₀ ^ (2 : ℕ) + v₁ ^ (2 : ℕ) + v₂ ^ (2 : ℕ)) := by
  have h2 : Real.sqrt 2 ^ (2 : ℕ) = 2 := Real.sq_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [sq_nonneg (v₀ - v₂), sq_nonneg (v₀ + v₂ - Real.sqrt 2 * v₁), h2, hpos]

/-- `cos(π/4) = √2/2`. -/
theorem cos_pi_div_four_eq : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
  rw [Real.cos_pi_div_four]

/-- The damping factor as a function of the chain length, `cos(π/(M+1))`, is increasing in `M` and
never reaches one: every prime power is damped, and the heaviest are damped the most. -/
theorem damping_lt_one {M : ℕ} (hM : 1 ≤ M) :
    Real.cos (Real.pi / (M + 1)) < 1 := by
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hden : (0 : ℝ) < (M : ℝ) + 1 := by linarith
  have hpos : 0 < Real.pi / ((M : ℝ) + 1) := by
    have := Real.pi_pos; positivity
  have hle : Real.pi / ((M : ℝ) + 1) ≤ Real.pi := by
    have := Real.pi_pos
    rw [div_le_iff₀ hden]
    nlinarith
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) hle hpos
  simpa using h

/-- The chain-two factor is strictly below the naive bound `1`: the dominant part of the prime sum
is damped by exactly one half. -/
theorem chain_two_strict : Real.cos (Real.pi / 3) < 1 := by
  rw [cos_pi_div_three_eq]; norm_num

end RHTower
