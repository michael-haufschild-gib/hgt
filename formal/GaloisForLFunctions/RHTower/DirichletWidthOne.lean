import GaloisForLFunctions.RHTower.DirichletAbsoluteAbscissa

/-!
# Bohr's width-one inequality

The abscissa of absolute convergence of an ordinary Dirichlet series exceeds the abscissa of
convergence by at most one:

```text
σ_a  ≤  σ_c + 1 .
```

The reason is elementary.  Convergence at `s₀` bounds the coefficients by `C (n+1)^{Re s₀}`, and the
majorant `∑ (n+1)^{Re s₀ − x}` converges as soon as `x > Re s₀ + 1`, because a shifted `p`-series
converges exactly for `p > 1`.

Together with `σ_u ≤ σ_a` this closes the classical chain of abscissas

```text
σ_c  ≤  σ_u  ≤  σ_a  ≤  σ_c + 1 .
```
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower

/-- The series converges absolutely on `Re s ≥ x`. -/
def DirichletAbsConvAt (a : ℕ → ℂ) (x : ℝ) : Prop :=
  Summable (fun n : ℕ => ‖a n‖ * ((n : ℝ) + 1) ^ (-x))

/-- **The abscissa of absolute convergence**, in the shifted indexing used here. -/
noncomputable def abscissaOfAbsConvShift (a : ℕ → ℂ) : EReal :=
  sInf <| Real.toEReal '' {x : ℝ | DirichletAbsConvAt a x}

/-- A shifted `p`-series converges for `p > 1`. -/
theorem summable_shift_rpow_neg {p : ℝ} (hp : 1 < p) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-p)) := by
  have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ p)⁻¹) := Real.summable_nat_rpow_inv.2 hp
  have hshift : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ p)⁻¹) :=
    (summable_nat_add_iff 1).2 hbase
  refine hshift.congr fun n => ?_
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) := by positivity
  push_cast
  rw [Real.rpow_neg hpos.le]

/-- **Convergence at a point gives absolute convergence one to the right.** -/
theorem absConvAt_of_convergesAt {a : ℕ → ℂ} {s₀ : ℂ} (h : DirichletConvergesAt a s₀)
    {x : ℝ} (hx : s₀.re + 1 < x) : DirichletAbsConvAt a x := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_coeff_le_of_convergesAt h
  have hp : 1 < x - s₀.re := by linarith
  have hmaj : Summable (fun n : ℕ => C * ((n : ℝ) + 1) ^ (-(x - s₀.re))) :=
    (summable_shift_rpow_neg hp).mul_left C
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmaj
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) := by positivity
  have hker : ((n : ℝ) + 1) ^ (-(x - s₀.re))
      = ((n : ℝ) + 1) ^ (s₀.re) * ((n : ℝ) + 1) ^ (-x) := by
    rw [← Real.rpow_add hpos]
    congr 1
    ring
  rw [hker, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right (hC n) ?_
  positivity

/-- **The width-one bound, at the level of real points.** -/
theorem abscissaOfAbsConvShift_le_of_convergesAt {a : ℕ → ℂ} {s₀ : ℂ}
    (h : DirichletConvergesAt a s₀) {x : ℝ} (hx : s₀.re + 1 < x) :
    abscissaOfAbsConvShift a ≤ (x : EReal) :=
  sInf_le ⟨x, absConvAt_of_convergesAt h hx, rfl⟩

/-- **`σ_u ≤ σ_a`.** -/
theorem abscissaOfUnifConv_le_abscissaOfAbsConvShift (a : ℕ → ℂ) :
    abscissaOfUnifConv a ≤ abscissaOfAbsConvShift a := by
  refine sInf_le_sInf ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, uniformlyConvergesOn_of_summable hx, rfl⟩

end GaloisForLFunctions.RHTower

end
