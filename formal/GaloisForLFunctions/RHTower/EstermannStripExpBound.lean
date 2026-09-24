import GaloisForLFunctions.RHTower.EstermannZeta
import GaloisForLFunctions.HTGeometry.HurwitzZetaStripExpBound

/-!
# An a priori exponential bound for Estermann's zeta function on a vertical strip

Each of the `q` products in the Hurwitz decomposition is a product of two functions bounded by
`C e^{π|t|/2}` on a vertical strip, so

```text
‖D(s, a/q)‖ ≤ C_q e^{π|t|}     (σ₀ ≤ Re s ≤ σ₁ < 3, |t| ≥ 2).
```

The bound is crude — the truth is polynomial — but it is the a priori growth a
Phragmén--Lindelöf interpolation between the two edges requires, and nothing weaker is available
before that interpolation is carried out.
-/

open Complex HurwitzZeta

namespace RHTower

noncomputable section

/-- **The a priori exponential bound on a vertical strip.** -/
theorem exists_bound_norm_estermannZeta_strip_exp (q : ℕ) [NeZero q] (a : ZMod q) (σ₀ σ₁ : ℝ)
    (hσ : σ₁ < 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → 2 ≤ |s.im| →
      ‖estermannZeta q a s‖ ≤ C * Real.exp (Real.pi * |s.im|) := by
  classical
  choose Ce hCe0 hCe using fun c : ZMod q =>
    GaloisForLFunctions.HTGeometry.exists_bound_norm_expZeta_strip
      (ZMod.toAddCircle (a * c)) σ₀ σ₁ hσ
  choose Ch hCh0 hCh using fun c : ZMod q =>
    GaloisForLFunctions.HTGeometry.exists_bound_norm_hurwitzZeta_strip
      (ZMod.toAddCircle c) σ₀ σ₁ hσ
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set Q : ℝ := (q : ℝ) ^ (-σ₀) with hQ
  have hQ0 : (0 : ℝ) ≤ Q := Real.rpow_nonneg (by linarith) _
  refine ⟨Q * ∑ c : ZMod q, Ce c * Ch c, ?_, fun s h0 h1 him => ?_⟩
  · refine mul_nonneg hQ0 (Finset.sum_nonneg (fun c _ => mul_nonneg (hCe0 c) (hCh0 c)))
  have hcp : ‖((q : ℂ)) ^ (-s)‖ ≤ Q := by
    rw [show ((q : ℂ)) = ((q : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ) < (q : ℝ))]
    rw [hQ]
    refine Real.rpow_le_rpow_of_exponent_le hq1 ?_
    simp only [Complex.neg_re]
    linarith
  have hterm : ∀ c : ZMod q,
      ‖expZeta (ZMod.toAddCircle (a * c)) s * hurwitzZeta (ZMod.toAddCircle c) s‖
        ≤ (Ce c * Ch c) * Real.exp (Real.pi * |s.im|) := by
    intro c
    rw [norm_mul]
    have h1' := hCe c s h0 h1 him
    have h2' := hCh c s h0 h1 him
    calc ‖expZeta (ZMod.toAddCircle (a * c)) s‖ * ‖hurwitzZeta (ZMod.toAddCircle c) s‖
        ≤ (Ce c * Real.exp (Real.pi * |s.im| / 2)) * (Ch c * Real.exp (Real.pi * |s.im| / 2)) :=
          mul_le_mul h1' h2' (norm_nonneg _)
            (mul_nonneg (hCe0 c) (Real.exp_pos _).le)
      _ = (Ce c * Ch c) * (Real.exp (Real.pi * |s.im| / 2) * Real.exp (Real.pi * |s.im| / 2)) := by
          ring
      _ = (Ce c * Ch c) * Real.exp (Real.pi * |s.im|) := by
          rw [← Real.exp_add]
          congr 2
          ring
  have hsum : ‖∑ c : ZMod q, expZeta (ZMod.toAddCircle (a * c)) s * hurwitzZeta (ZMod.toAddCircle c) s‖
      ≤ (∑ c : ZMod q, Ce c * Ch c) * Real.exp (Real.pi * |s.im|) := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun c _ => hterm c)
  rw [estermannZeta, norm_mul]
  have hs0 : (0 : ℝ) ≤ ∑ c : ZMod q, Ce c * Ch c :=
    Finset.sum_nonneg (fun c _ => mul_nonneg (hCe0 c) (hCh0 c))
  calc ‖((q : ℂ)) ^ (-s)‖
        * ‖∑ c : ZMod q, expZeta (ZMod.toAddCircle (a * c)) s * hurwitzZeta (ZMod.toAddCircle c) s‖
      ≤ Q * ((∑ c : ZMod q, Ce c * Ch c) * Real.exp (Real.pi * |s.im|)) :=
        mul_le_mul hcp hsum (norm_nonneg _) hQ0
    _ = Q * (∑ c : ZMod q, Ce c * Ch c) * Real.exp (Real.pi * |s.im|) := by ring

end

end RHTower
