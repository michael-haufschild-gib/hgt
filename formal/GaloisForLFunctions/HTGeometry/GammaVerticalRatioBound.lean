import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The Gamma modulus ratio on vertical lines

For `0 < a ≤ b` the ratio of Gamma moduli along a vertical line,

```text
τ ↦ ‖Γ(a + iτ)‖ / ‖Γ(b + iτ)‖ ,
```

is largest at `τ = 0`.  Equivalently

```text
‖Γ(a + iτ)‖ · Γ(b) ≤ Γ(a) · ‖Γ(b + iτ)‖ .
```

The proof is elementary and needs no Stirling asymptotics: in the Gauss product
`Γ_n(s) = n^s n! / ∏_{j ≤ n} (s + j)` the whole `τ`-dependence sits in the factors
`‖x + j + iτ‖ = √((x+j)² + τ²)`, and

```text
u √(v² + τ²) ≤ √(u² + τ²) v        (0 < u ≤ v)
```

holds termwise because it squares to `u²τ² ≤ τ²v²`.  Passing to the limit in `n` gives the exact
statement for `Γ` itself.
-/

open Complex Filter

namespace HTGeometry

/-- Termwise comparison of the shifted moduli. -/
private theorem mul_sqrt_le {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (τ : ℝ) :
    u * Real.sqrt (v ^ (2 : ℕ) + τ ^ (2 : ℕ)) ≤ Real.sqrt (u ^ (2 : ℕ) + τ ^ (2 : ℕ)) * v := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hleft : u * Real.sqrt (v ^ (2 : ℕ) + τ ^ (2 : ℕ)) = Real.sqrt (u ^ (2 : ℕ) * (v ^ (2 : ℕ) + τ ^ (2 : ℕ))) := by
    rw [Real.sqrt_mul (sq_nonneg u), Real.sqrt_sq hu.le]
  have hright : Real.sqrt (u ^ (2 : ℕ) + τ ^ (2 : ℕ)) * v = Real.sqrt ((u ^ (2 : ℕ) + τ ^ (2 : ℕ)) * v ^ (2 : ℕ)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hv.le]
  rw [hleft, hright]
  refine Real.sqrt_le_sqrt ?_
  have huv2 : u ^ (2 : ℕ) ≤ v ^ (2 : ℕ) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left huv2 (sq_nonneg τ)]

/-- The modulus of a complex number in real/imaginary coordinates. -/
theorem norm_ofReal_add_mul_I (u τ : ℝ) :
    ‖(u : ℂ) + (τ : ℂ) * I‖ = Real.sqrt (u ^ (2 : ℕ) + τ ^ (2 : ℕ)) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring_nf

private theorem norm_GammaSeq_ofReal_add_mul_I (x τ : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖Complex.GammaSeq ((x : ℂ) + (τ : ℂ) * I) n‖
      = (n : ℝ) ^ x * (n.factorial : ℝ)
        / ∏ j ∈ Finset.range (n + 1), Real.sqrt ((x + j) ^ (2 : ℕ) + τ ^ (2 : ℕ)) := by
  rw [Complex.GammaSeq, norm_div, norm_mul, Complex.norm_natCast_cpow_of_pos hn,
    Complex.norm_natCast]
  congr 1
  · congr 1
    simp
  · rw [norm_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    have hrw : (x : ℂ) + (τ : ℂ) * I + (j : ℂ) = ((x + j : ℝ) : ℂ) + (τ : ℂ) * I := by
      push_cast
      ring
    rw [hrw, norm_ofReal_add_mul_I]

private theorem realGammaSeq_eq (y : ℝ) (n : ℕ) :
    Real.GammaSeq y n
      = (n : ℝ) ^ y * (n.factorial : ℝ) / ∏ j ∈ Finset.range (n + 1), (y + j) := rfl

private theorem norm_GammaSeq_mul_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (τ : ℝ) {n : ℕ}
    (hn : 0 < n) :
    ‖Complex.GammaSeq ((a : ℂ) + (τ : ℂ) * I) n‖ * Real.GammaSeq b n
      ≤ Real.GammaSeq a n * ‖Complex.GammaSeq ((b : ℂ) + (τ : ℂ) * I) n‖ := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hPa : (0 : ℝ) < ∏ j ∈ Finset.range (n + 1), (a + j) :=
    Finset.prod_pos fun j _ => by positivity
  have hPb : (0 : ℝ) < ∏ j ∈ Finset.range (n + 1), (b + j) :=
    Finset.prod_pos fun j _ => by positivity
  have hQa : (0 : ℝ) < ∏ j ∈ Finset.range (n + 1), Real.sqrt ((a + j) ^ (2 : ℕ) + τ ^ (2 : ℕ)) :=
    Finset.prod_pos fun j _ => Real.sqrt_pos.mpr (by positivity)
  have hQb : (0 : ℝ) < ∏ j ∈ Finset.range (n + 1), Real.sqrt ((b + j) ^ (2 : ℕ) + τ ^ (2 : ℕ)) :=
    Finset.prod_pos fun j _ => Real.sqrt_pos.mpr (by positivity)
  -- the denominators compare termwise
  have hdenom : (∏ j ∈ Finset.range (n + 1), (a + j))
        * ∏ j ∈ Finset.range (n + 1), Real.sqrt ((b + j) ^ (2 : ℕ) + τ ^ (2 : ℕ))
      ≤ (∏ j ∈ Finset.range (n + 1), Real.sqrt ((a + j) ^ (2 : ℕ) + τ ^ (2 : ℕ)))
        * ∏ j ∈ Finset.range (n + 1), (b + j) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun j _ => by positivity) fun j _ => ?_
    exact mul_sqrt_le (by positivity) (by linarith) τ
  rw [norm_GammaSeq_ofReal_add_mul_I a τ hn, norm_GammaSeq_ofReal_add_mul_I b τ hn,
    realGammaSeq_eq, realGammaSeq_eq, div_mul_div_comm, div_mul_div_comm]
  gcongr

/-- **The Gamma modulus ratio on a vertical line is maximal on the real axis.**  For `0 < a ≤ b`
and every height `τ`,

```text
‖Γ(a + iτ)‖ · Γ(b) ≤ Γ(a) · ‖Γ(b + iτ)‖ .
```
-/
theorem norm_Gamma_mul_Gamma_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (τ : ℝ) :
    ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ * Real.Gamma b
      ≤ Real.Gamma a * ‖Complex.Gamma ((b : ℂ) + (τ : ℂ) * I)‖ := by
  have hleft : Tendsto (fun n : ℕ =>
      ‖Complex.GammaSeq ((a : ℂ) + (τ : ℂ) * I) n‖ * Real.GammaSeq b n) atTop
      (nhds (‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ * Real.Gamma b)) :=
    ((Complex.GammaSeq_tendsto_Gamma _).norm).mul (Real.GammaSeq_tendsto_Gamma b)
  have hright : Tendsto (fun n : ℕ =>
      Real.GammaSeq a n * ‖Complex.GammaSeq ((b : ℂ) + (τ : ℂ) * I) n‖) atTop
      (nhds (Real.Gamma a * ‖Complex.Gamma ((b : ℂ) + (τ : ℂ) * I)‖)) :=
    (Real.GammaSeq_tendsto_Gamma a).mul ((Complex.GammaSeq_tendsto_Gamma _).norm)
  refine le_of_tendsto_of_tendsto hleft hright ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact norm_GammaSeq_mul_le ha hab τ hn

/-- The ratio form: for `0 < a ≤ b` the Gamma modulus ratio at height `τ` is at most its value on
the real axis. -/
theorem norm_Gamma_div_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (τ : ℝ) :
    ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ / ‖Complex.Gamma ((b : ℂ) + (τ : ℂ) * I)‖
      ≤ Real.Gamma a / Real.Gamma b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hGb : (0 : ℝ) < Real.Gamma b := Real.Gamma_pos_of_pos hb
  have hne : Complex.Gamma ((b : ℂ) + (τ : ℂ) * I) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m => ?_
    intro hcontra
    have hre := congrArg Complex.re hcontra
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.neg_re, Complex.natCast_re] at hre
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hnorm : (0 : ℝ) < ‖Complex.Gamma ((b : ℂ) + (τ : ℂ) * I)‖ := norm_pos_iff.mpr hne
  rw [div_le_div_iff₀ hnorm hGb]
  have h := norm_Gamma_mul_Gamma_le ha hab τ
  linarith [h]

end HTGeometry
