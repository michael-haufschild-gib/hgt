import GaloisForLFunctions.RHTower.Sieve.WindowAsShifts

/-!
# The additive window is a logarithmic window of computable width

Settling the route.  Gallagher's lemma is available here in its multiplicative form
(`gallagher_identity`), whose output is `logPoly` — the object the Halász chain of units 1–6 acts
on.  Taking it requires expressing the additive window `(z, z+ℓ]` as a window in `log`, which it is,
exactly:

```text
b ∈ (z, z+ℓ]  ↔  log z < log b ≤ log z + logWidth ℓ z ,     logWidth ℓ z := log(z+ℓ) − log z ,
```

and the width is pinned between `ℓ/(z+ℓ)` and `ℓ/z` by `log x ≤ x − 1` used in both directions.  So
over a dyadic range of starting points the width varies by at most a factor two.

That the width *varies at all* is the reason the two Gallagher forms are not interchangeable for
free: a fixed-`δ` logarithmic family is not the additive family, and signed quadratic forms do not
compare under pointwise kernel bounds — as `dyadicMeanSquare_le_band` showed by being true and
useless.  Pinning the width is what makes the comparison quantitative rather than formal.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The logarithmic width of the additive window `(z, z+ℓ]`. -/
def logWidth (ℓ z : ℕ) : ℝ := Real.log ((z : ℝ) + ℓ) - Real.log z

/-- **The additive window is a logarithmic window.** -/
theorem mem_window_iff_log {ℓ z b : ℕ} (hz : 1 ≤ z) (hb : 1 ≤ b) :
    b ∈ Finset.Icc (z + 1) (z + ℓ)
      ↔ Real.log z < Real.log b ∧ Real.log b ≤ Real.log z + logWidth ℓ z := by
  have hz0 : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hzl : (0 : ℝ) < (z : ℝ) + ℓ := by positivity
  rw [logWidth]
  have hsimp : Real.log z + (Real.log ((z : ℝ) + ℓ) - Real.log z)
      = Real.log ((z : ℝ) + ℓ) := by ring
  rw [hsimp, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have hzb : (z : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : z < b)
    have hbz : (b : ℝ) ≤ (z : ℝ) + ℓ := by
      have : ((b : ℕ) : ℝ) ≤ ((z + ℓ : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at this
      linarith
    exact ⟨Real.log_lt_log hz0 hzb, Real.log_le_log hb0 hbz⟩
  · rintro ⟨h1, h2⟩
    have hzb : (z : ℝ) < (b : ℝ) := by
      by_contra hc
      exact absurd (Real.log_le_log hb0 (by linarith : (b : ℝ) ≤ (z : ℝ))) (by linarith)
    have hbz : (b : ℝ) ≤ (z : ℝ) + ℓ := by
      by_contra hc
      exact absurd (Real.log_lt_log hzl (by linarith : (z : ℝ) + ℓ < (b : ℝ))) (by linarith)
    have h1' : z < b := by exact_mod_cast hzb
    have h2' : b ≤ z + ℓ := by
      have : ((b : ℕ) : ℝ) ≤ ((z + ℓ : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    exact ⟨by omega, h2'⟩

/-- The width is at most `ℓ/z`. -/
theorem logWidth_le {ℓ z : ℕ} (hz : 1 ≤ z) : logWidth ℓ z ≤ (ℓ : ℝ) / z := by
  have hz0 : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
  have hlog : Real.log (((z : ℝ) + ℓ) / z) ≤ ((z : ℝ) + ℓ) / z - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) (ne_of_gt hz0)] at hlog
  have hstep : ((z : ℝ) + ℓ) / z - 1 = (ℓ : ℝ) / z := by field_simp; ring
  rw [hstep] at hlog
  rw [logWidth]
  exact hlog

/-- The width is at least `ℓ/(z+ℓ)`. -/
theorem le_logWidth {ℓ z : ℕ} (hz : 1 ≤ z) : (ℓ : ℝ) / ((z : ℝ) + ℓ) ≤ logWidth ℓ z := by
  have hz0 : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
  have hzl : (0 : ℝ) < (z : ℝ) + ℓ := by positivity
  have hlog : Real.log ((z : ℝ) / ((z : ℝ) + ℓ)) ≤ (z : ℝ) / ((z : ℝ) + ℓ) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (ne_of_gt hz0) (ne_of_gt hzl)] at hlog
  have hstep : (z : ℝ) / ((z : ℝ) + ℓ) - 1 = -((ℓ : ℝ) / ((z : ℝ) + ℓ)) := by
    field_simp; ring
  rw [hstep] at hlog
  rw [logWidth]
  linarith

end RHTower.Sieve

end
