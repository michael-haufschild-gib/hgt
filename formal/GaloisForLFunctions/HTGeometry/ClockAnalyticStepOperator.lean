import GaloisForLFunctions.HTGeometry.ClockAnalyticWienerScale

/-!
# The operator of one step of the analytic clock iteration

In the coefficient form of the scale the characteristic clock equation

`∂ξ∂η u = (Δ⊥ u + V u) / 4`

reads, coefficient by coefficient, as an infinite system of Goursat problems whose right-hand side
is the image of the state under

`w ↦ (V ⋆ w - k² w) / 4`.

This file records that operator and its estimate in the scale: it maps radius `ρ` to radius `ρ'`
with norm at most `1/(ρ-ρ')² + ‖V‖_ρ/4`. The Laplacian part is the derivative loss of the scale,
the potential part is the Banach-algebra estimate, and nothing else enters.

The elementary lemmas about the weighted norm — the triangle inequality in the form needed for a
difference, and homogeneity — are proved here as well.
-/

namespace GaloisForLFunctions.HTGeometry

/-! ## Elementary properties of the weighted norm -/

theorem wienerSummable_of_abs_le_add {ρ : ℝ} {f g h : ℤ → ℝ} (hf : WienerSummable ρ f)
    (hg : WienerSummable ρ g) (hle : ∀ k, |h k| ≤ |f k| + |g k|) :
    WienerSummable ρ h := by
  refine (hf.add hg).of_nonneg_of_le (fun _ => by positivity) fun k => ?_
  calc |h k| * Real.exp (ρ * |(k : ℝ)|)
      ≤ (|f k| + |g k|) * Real.exp (ρ * |(k : ℝ)|) :=
        mul_le_mul_of_nonneg_right (hle k) (Real.exp_pos _).le
    _ = |f k| * Real.exp (ρ * |(k : ℝ)|) + |g k| * Real.exp (ρ * |(k : ℝ)|) := by ring

theorem wienerNorm_le_add {ρ : ℝ} {f g h : ℤ → ℝ} (hf : WienerSummable ρ f)
    (hg : WienerSummable ρ g) (hle : ∀ k, |h k| ≤ |f k| + |g k|) :
    wienerNorm ρ h ≤ wienerNorm ρ f + wienerNorm ρ g := by
  have hsum : WienerSummable ρ h := wienerSummable_of_abs_le_add hf hg hle
  have hstep : ∀ k : ℤ, |h k| * Real.exp (ρ * |(k : ℝ)|)
      ≤ |f k| * Real.exp (ρ * |(k : ℝ)|) + |g k| * Real.exp (ρ * |(k : ℝ)|) := by
    intro k
    calc |h k| * Real.exp (ρ * |(k : ℝ)|)
        ≤ (|f k| + |g k|) * Real.exp (ρ * |(k : ℝ)|) :=
          mul_le_mul_of_nonneg_right (hle k) (Real.exp_pos _).le
      _ = |f k| * Real.exp (ρ * |(k : ℝ)|) + |g k| * Real.exp (ρ * |(k : ℝ)|) := by ring
  rw [wienerNorm, wienerNorm, wienerNorm, ← hf.tsum_add hg]
  exact Summable.tsum_le_tsum hstep hsum (hf.add hg)

theorem wienerSummable_const_mul {ρ : ℝ} (c : ℝ) {f : ℤ → ℝ} (hf : WienerSummable ρ f) :
    WienerSummable ρ (fun k => c * f k) := by
  have hrw : (fun k : ℤ => |c * f k| * Real.exp (ρ * |(k : ℝ)|))
      = fun k : ℤ => |c| * (|f k| * Real.exp (ρ * |(k : ℝ)|)) := by
    funext k
    rw [abs_mul]
    ring
  rw [WienerSummable, hrw]
  exact hf.mul_left _

theorem wienerNorm_const_mul {ρ : ℝ} (c : ℝ) {f : ℤ → ℝ} :
    wienerNorm ρ (fun k => c * f k) = |c| * wienerNorm ρ f := by
  have hrw : (fun k : ℤ => |c * f k| * Real.exp (ρ * |(k : ℝ)|))
      = fun k : ℤ => |c| * (|f k| * Real.exp (ρ * |(k : ℝ)|)) := by
    funext k
    rw [abs_mul]
    ring
  rw [wienerNorm, wienerNorm, hrw, tsum_mul_left]

/-! ## The step operator -/

/-- The right-hand side of the characteristic clock equation, in coefficients. -/
noncomputable def clockCoeffStep (V w : ℤ → ℝ) : ℤ → ℝ :=
  fun k => (1 / 4 : ℝ) * (wienerConv V w k - sqMul w k)

theorem abs_clockCoeffStep_le (V w : ℤ → ℝ) (k : ℤ) :
    |(fun k => wienerConv V w k - sqMul w k) k| ≤ |wienerConv V w k| + |sqMul w k| := by
  simpa using abs_sub _ _

/-- **The step operator maps radius `ρ` to radius `ρ'`.** -/
theorem wienerSummable_clockCoeffStep {ρ' ρ : ℝ} (hρ0 : 0 ≤ ρ') (hρ : ρ' < ρ) {V w : ℤ → ℝ}
    (hV : WienerSummable ρ V) (hw : WienerSummable ρ w) :
    WienerSummable ρ' (clockCoeffStep V w) := by
  have hconv : WienerSummable ρ' (wienerConv V w) :=
    wienerSummable_of_le hρ.le (wienerSummable_conv (le_trans hρ0 hρ.le) hV hw)
  have hlap : WienerSummable ρ' (sqMul w) := wienerSummable_sqMul hρ hw
  exact wienerSummable_const_mul _
    (wienerSummable_of_abs_le_add hconv hlap (abs_clockCoeffStep_le V w))

/-- **The estimate of the step operator in the scale.** The Laplacian contributes the derivative
loss, the potential the algebra estimate. -/
theorem wienerNorm_clockCoeffStep_le {ρ' ρ : ℝ} (hρ0 : 0 ≤ ρ') (hρ : ρ' < ρ) {V w : ℤ → ℝ}
    (hV : WienerSummable ρ V) (hw : WienerSummable ρ w) :
    wienerNorm ρ' (clockCoeffStep V w)
      ≤ (1 / (ρ - ρ') ^ (2 : ℕ) + wienerNorm ρ V / 4) * wienerNorm ρ w := by
  have hρnn : (0 : ℝ) ≤ ρ := le_trans hρ0 hρ.le
  have hconvρ : WienerSummable ρ (wienerConv V w) := wienerSummable_conv hρnn hV hw
  have hconv : WienerSummable ρ' (wienerConv V w) := wienerSummable_of_le hρ.le hconvρ
  have hlap : WienerSummable ρ' (sqMul w) := wienerSummable_sqMul hρ hw
  have hsplit : wienerNorm ρ' (fun k => wienerConv V w k - sqMul w k)
      ≤ wienerNorm ρ' (wienerConv V w) + wienerNorm ρ' (sqMul w) :=
    wienerNorm_le_add hconv hlap (abs_clockCoeffStep_le V w)
  have hconvle : wienerNorm ρ' (wienerConv V w) ≤ wienerNorm ρ V * wienerNorm ρ w :=
    le_trans (wienerNorm_mono hρ.le hconvρ) (wienerNorm_conv_le hρnn hV hw)
  have hlaple : wienerNorm ρ' (sqMul w) ≤ 4 / (ρ - ρ') ^ (2 : ℕ) * wienerNorm ρ w :=
    wienerNorm_sqMul_le hρ hw
  have hquarter : wienerNorm ρ' (clockCoeffStep V w)
      = (1 / 4 : ℝ) * wienerNorm ρ' (fun k => wienerConv V w k - sqMul w k) := by
    have hdef : clockCoeffStep V w
        = fun k => (1 / 4 : ℝ) * (wienerConv V w k - sqMul w k) := rfl
    rw [hdef, wienerNorm_const_mul]
    norm_num
  rw [hquarter]
  have hchain : wienerNorm ρ' (fun k => wienerConv V w k - sqMul w k)
      ≤ wienerNorm ρ V * wienerNorm ρ w + 4 / (ρ - ρ') ^ (2 : ℕ) * wienerNorm ρ w := by
    linarith [hsplit, hconvle, hlaple]
  have hfinal : (1 / 4 : ℝ)
      * (wienerNorm ρ V * wienerNorm ρ w + 4 / (ρ - ρ') ^ (2 : ℕ) * wienerNorm ρ w)
      = (1 / (ρ - ρ') ^ (2 : ℕ) + wienerNorm ρ V / 4) * wienerNorm ρ w := by ring
  calc (1 / 4 : ℝ) * wienerNorm ρ' (fun k => wienerConv V w k - sqMul w k)
      ≤ (1 / 4 : ℝ)
          * (wienerNorm ρ V * wienerNorm ρ w + 4 / (ρ - ρ') ^ (2 : ℕ) * wienerNorm ρ w) := by
        linarith [hchain]
    _ = (1 / (ρ - ρ') ^ (2 : ℕ) + wienerNorm ρ V / 4) * wienerNorm ρ w := hfinal

end GaloisForLFunctions.HTGeometry
