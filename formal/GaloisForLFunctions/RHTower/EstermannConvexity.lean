import GaloisForLFunctions.RHTower.EstermannStripPolynomialBound

/-!
# Estermann's zeta function has polynomial growth on the critical strip

Dividing the convexity bound for the entire completion by `(s-1)²`, which is bounded below above
unit height, gives the bound in the form a contour shift uses:

```text
‖D(s, a/q)‖ ≤ C (1 + |t|)^N     for -1 ≤ Re s ≤ 2 and |t| ≥ 1.
```
-/

open Complex

namespace RHTower

noncomputable section

/-- **Polynomial growth of `D(·, a/q)` on the closed strip `-1 ≤ Re s ≤ 2`.** -/
theorem exists_bound_norm_estermannZeta_strip (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖estermannZeta q ((a : ZMod q)) s‖ ≤ C * (1 + |s.im|) ^ N := by
  obtain ⟨C, N, hC0, hC⟩ := exists_bound_norm_estermannEntire_strip q a
  refine ⟨C, N, hC0, fun s h0 h1 him => ?_⟩
  have hsm : (1 : ℝ) ≤ ‖s - 1‖ := by
    have h : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
    have him' : (s - 1).im = s.im := by simp
    rw [him'] at h
    linarith
  have hne : s ≠ 1 := by
    intro hcon
    rw [hcon] at hsm
    norm_num at hsm
  have hbase := hC s h0 h1
  rw [estermannEntire_eq _ hne, norm_mul, norm_pow] at hbase
  have hpow : (1 : ℝ) ≤ ‖s - 1‖ ^ (2 : ℕ) := one_le_pow₀ hsm
  nlinarith [hbase, hpow, norm_nonneg (estermannZeta q ((a : ZMod q)) s)]

end

end RHTower
