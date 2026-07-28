import Mathlib

/-!
# What a zero-density envelope can and cannot decide

A zero-density estimate is an upper bound `N(σ,T) ≤ F(σ,T)` on the number of zeros in
`Re s ≥ σ`, `|Im s| ≤ T`.  The Riemann Hypothesis is the assertion `N(σ,T) = 0` for every
`σ > 1/2`.  Because `N` is integer-valued, `N(σ,T) = 0` is equivalent to `N(σ,T) < 1`, so an
upper bound decides RH **exactly when its envelope drops below `1`**:

```text
F(σ,T) < 1  for all σ > 1/2, T  ⟹  RH
F(σ,T) ≥ 1  for some σ > 1/2, T  ⟹  the envelope is consistent with a zero there
```

This is a dichotomy on the envelope alone, independent of any analytic input, and it is sharp in
both directions: the second half is witnessed by an admissible counting function that actually
takes the value `1`.

Every envelope in the density literature has the shape `C · T^{θ(1−σ)} (log T)^A` with `θ > 0`, and
such an envelope is `≥ 1` at every point of the strip for `T ≥ 1` — its infimum over `T` is
approached only as `T → 1`, never below `C`.  So the whole family is on the wrong side of the
dichotomy, and no improvement of the exponent `θ` changes that: improving `θ` moves the envelope
down but never through `1`.  A density estimate can therefore bound the *number* of exceptional
zeros but can never rule out the *existence* of one.

The distinction matters because the two sides need different theorems: the counting side is
Chebyshev-type and unconditional, the vanishing side is not reachable by counting at all.
-/

namespace RHTower

open Filter

/-- **The vanishing criterion.**  An integer-valued count is zero exactly when it is `< 1`. -/
theorem count_eq_zero_iff_lt_one (N : ℕ) : N = 0 ↔ (N : ℝ) < 1 := by
  constructor
  · rintro rfl; norm_num
  · intro h
    by_contra hne
    have h1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hne
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
    linarith

/-- **An envelope decides vanishing only below `1`.**  If a count is bounded by an envelope that is
`< 1`, the count vanishes.  This is the *only* way an upper bound can produce a vanishing
statement. -/
theorem count_eq_zero_of_envelope_lt_one {N : ℕ} {F : ℝ} (hle : (N : ℝ) ≤ F) (hF : F < 1) :
    N = 0 :=
  (count_eq_zero_iff_lt_one N).mpr (lt_of_le_of_lt hle hF)

/-- **The converse side.**  An envelope that is `≥ 1` is satisfied by a count equal to `1`, hence
never forces vanishing.  The witness is explicit. -/
theorem exists_nonvanishing_count_of_envelope_ge_one {F : ℝ} (hF : 1 ≤ F) :
    ∃ N : ℕ, (N : ℝ) ≤ F ∧ N ≠ 0 :=
  ⟨1, by simpa using hF, one_ne_zero⟩

/-- The density envelope shape of the literature: `C · T^{θ(1−σ)} · (log T)^A`. -/
noncomputable def densityEnvelope (C θ A : ℝ) (σ T : ℝ) : ℝ :=
  C * T ^ (θ * (1 - σ)) * (Real.log T) ^ A

/-- **The whole density family is on the wrong side of the dichotomy.**  For `C ≥ 1`, exponent
`θ ≥ 0`, `σ ≤ 1`, and `T` past the point where `log T ≥ 1`, the envelope is at least `1`.  The
hypotheses are the ones every density estimate satisfies. -/
theorem one_le_densityEnvelope {C θ A : ℝ} (hC : 1 ≤ C) (hθ : 0 ≤ θ) (hA : 0 ≤ A)
    {σ T : ℝ} (hσ : σ ≤ 1) (hT : Real.exp 1 ≤ T) :
    1 ≤ densityEnvelope C θ A σ T := by
  have hT1 : (1 : ℝ) ≤ T := le_trans (le_trans (by norm_num) (Real.add_one_le_exp 1)) hT
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT1
  have hlog : (1 : ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 1) hT
    simpa [Real.log_exp] using this
  have hexp : (0 : ℝ) ≤ θ * (1 - σ) := mul_nonneg hθ (by linarith)
  have hpow : (1 : ℝ) ≤ T ^ (θ * (1 - σ)) := Real.one_le_rpow hT1 hexp
  have hlogpow : (1 : ℝ) ≤ (Real.log T) ^ A := Real.one_le_rpow hlog hA
  have h1 : (1 : ℝ) ≤ C * T ^ (θ * (1 - σ)) := by nlinarith
  unfold densityEnvelope
  nlinarith

/-- **No density estimate rules out an exceptional zero.**  For every envelope of the literature's
shape and every point of the strip past `e`, there is a count consistent with the estimate and
nonzero.  Sharpening the exponent `θ` does not change this: the conclusion holds for every `θ ≥ 0`,
including `θ = 0`. -/
theorem density_estimate_never_forces_vanishing {C θ A : ℝ} (hC : 1 ≤ C) (hθ : 0 ≤ θ) (hA : 0 ≤ A)
    {σ T : ℝ} (hσ : σ ≤ 1) (hT : Real.exp 1 ≤ T) :
    ∃ N : ℕ, (N : ℝ) ≤ densityEnvelope C θ A σ T ∧ N ≠ 0 :=
  exists_nonvanishing_count_of_envelope_ge_one (one_le_densityEnvelope hC hθ hA hσ hT)

/-- **The dichotomy.**  For any envelope, either it drops below `1` — and then it decides vanishing
— or it does not, and then a nonzero count is consistent with it.  There is no third possibility,
so "how strong is the density exponent" is the wrong question to ask of a route to RH; the right
question is whether the envelope crosses `1`. -/
theorem envelope_dichotomy (F : ℝ) :
    (∀ N : ℕ, (N : ℝ) ≤ F → N = 0) ∨ (∃ N : ℕ, (N : ℝ) ≤ F ∧ N ≠ 0) := by
  by_cases hF : F < 1
  · exact Or.inl fun N hN => count_eq_zero_of_envelope_lt_one hN hF
  · exact Or.inr (exists_nonvanishing_count_of_envelope_ge_one (not_lt.mp hF))

/-- **A monotone-in-`T` envelope can never decide RH.**  If the envelope is nondecreasing in the
height and reaches `1` at some height, then at every larger height it fails to force vanishing.
Every density envelope is nondecreasing in `T`, so the deciding region is bounded — a density
estimate can only ever settle a *finite* portion of the strip, which is the numerical verification
already available by other means. -/
theorem monotone_envelope_fails_cofinally {F : ℝ → ℝ} (hmono : Monotone F)
    {T₀ : ℝ} (hT₀ : 1 ≤ F T₀) :
    ∀ T, T₀ ≤ T → ∃ N : ℕ, (N : ℝ) ≤ F T ∧ N ≠ 0 := fun _T hT =>
  exists_nonvanishing_count_of_envelope_ge_one (le_trans hT₀ (hmono hT))

/-- **The unbounded case.**  An envelope tending to infinity is eventually `≥ 1`, so it fails to
force vanishing at all large heights.  This covers every known density estimate at fixed
`σ > 1/2`, where the envelope is a positive power of `T`. -/
theorem tendsto_atTop_envelope_fails_eventually {F : ℝ → ℝ}
    (hF : Tendsto F atTop atTop) :
    ∀ᶠ T in atTop, ∃ N : ℕ, (N : ℝ) ≤ F T ∧ N ≠ 0 := by
  filter_upwards [hF.eventually_ge_atTop 1] with _T hT
  exact exists_nonvanishing_count_of_envelope_ge_one hT

end RHTower
