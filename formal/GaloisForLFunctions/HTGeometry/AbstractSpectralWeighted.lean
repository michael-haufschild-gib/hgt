import GaloisForLFunctions.HTGeometry.AbstractSpectralRigidity

/-!
# Weighted traces of an abstract spectral family

A spectral weight multiplies each point's multiplier by a fixed function of that point.  Polynomial
multipliers are the case of interest: a receiver may be modified by a fixed polynomial in the
spectral variable without destroying any coefficient, provided the polynomial has no zero in the
open right half plane.

Everything the unweighted theory needs from a family — summability, the vertical envelope, the
monotone real-time majorant, analyticity in the time variable — survives, because a subexponential
weight is absorbed by an arbitrarily small fraction of the exponential real-time weight.
-/

open Complex Filter
open scoped BigOperators

namespace HTGeometry

/-- A nowhere-vanishing subexponential weight for spectral points.  `const ε` is the majorant
constant at rate `ε`, valid on the admissible strip `|Im z| ≤ 1/2`, `Re z ≥ 0`. -/
structure SpectralWeight where
  /-- the weight function -/
  toFun : ℂ → ℂ
  /-- it does not vanish anywhere in the open right half plane -/
  ne_zero : ∀ z : ℂ, 0 < z.re → toFun z ≠ 0
  /-- the majorant constant at each rate -/
  const : ℝ → ℝ
  /-- the constants are nonnegative -/
  const_nonneg : ∀ ε : ℝ, 0 ≤ const ε
  /-- the weight is subexponential on the admissible strip -/
  le_const : ∀ ε : ℝ, 0 < ε → ∀ z : ℂ, |z.im| ≤ 1 / 2 → 0 ≤ z.re →
    ‖toFun z‖ ≤ const ε * Real.exp (ε * z.re)

namespace AbstractSpectralFamily

noncomputable section

variable {ι : Type*} (F : AbstractSpectralFamily ι) (W : SpectralWeight)

/-- The weighted multiplier at complex time. -/
def termW (τ : ℂ) (i : ι) : ℂ := W.toFun (F.pt i) * F.term τ i

/-- The weighted real-time majorant. -/
def traceWAbs (σ : ℝ) : ℝ := ∑' i : ι, ‖W.toFun (F.pt i)‖ * F.weight σ i

/-- The weighted trace at complex time. -/
def traceWC (τ : ℂ) : ℂ := ∑' i : ι, F.termW W τ i

theorem norm_toFun_pt_le {ε : ℝ} (hε : 0 < ε) (i : ι) :
    ‖W.toFun (F.pt i)‖ ≤ W.const ε * Real.exp (ε * (F.pt i).re) :=
  W.le_const ε hε _ (F.abs_im_lt i).le (F.re_nonneg i)

/-- **The weighted real-time majorant converges.**  A subexponential weight is absorbed by half of
the real-time exponential. -/
theorem summable_weightedWeight {σ : ℝ} (hσ : 0 < σ) :
    Summable fun i : ι => ‖W.toFun (F.pt i)‖ * F.weight σ i := by
  refine Summable.of_nonneg_of_le
    (fun i => mul_nonneg (norm_nonneg _) (F.weight_pos σ i).le) (fun i => ?_)
    ((F.summable_weight (half_pos hσ)).mul_left (W.const (σ / 2)))
  have hb := F.norm_toFun_pt_le W (half_pos hσ) i
  refine le_trans (mul_le_mul_of_nonneg_right hb (F.weight_pos σ i).le) (le_of_eq ?_)
  simp only [weight]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem norm_termW_le (τ : ℂ) (i : ι) :
    ‖F.termW W τ i‖ ≤ Real.exp (|τ.im| / 2) * (‖W.toFun (F.pt i)‖ * F.weight τ.re i) := by
  rw [termW, norm_mul]
  have h := F.norm_term_le τ i
  calc ‖W.toFun (F.pt i)‖ * ‖F.term τ i‖
      ≤ ‖W.toFun (F.pt i)‖ * (Real.exp (|τ.im| / 2) * F.weight τ.re i) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = Real.exp (|τ.im| / 2) * (‖W.toFun (F.pt i)‖ * F.weight τ.re i) := by ring

theorem summable_norm_termW {τ : ℂ} (hτ : 0 < τ.re) :
    Summable fun i : ι => ‖F.termW W τ i‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => F.norm_termW_le W τ i)
    ((F.summable_weightedWeight W hτ).mul_left _)

theorem traceWAbs_nonneg (σ : ℝ) : 0 ≤ F.traceWAbs W σ :=
  tsum_nonneg fun i => mul_nonneg (norm_nonneg _) (F.weight_pos σ i).le

/-- **The weighted vertical envelope.** -/
theorem norm_traceWC_le {τ : ℂ} (hτ : 0 < τ.re) :
    ‖F.traceWC W τ‖ ≤ Real.exp (|τ.im| / 2) * F.traceWAbs W τ.re := by
  refine le_trans (norm_tsum_le_tsum_norm (F.summable_norm_termW W hτ)) ?_
  rw [traceWAbs, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun i => F.norm_termW_le W τ i) (F.summable_norm_termW W hτ)
    ((F.summable_weightedWeight W hτ).mul_left _)

/-- A displacement bound gives a weighted growth bound: the easy direction. -/
theorem norm_traceWC_le_of_abs_im_le {lam : ℝ} (him : ∀ i, |(F.pt i).im| ≤ lam)
    {τ : ℂ} (hτ : 0 < τ.re) :
    ‖F.traceWC W τ‖ ≤ F.traceWAbs W τ.re * Real.exp (lam * |τ.im|) := by
  refine le_trans (norm_tsum_le_tsum_norm (F.summable_norm_termW W hτ)) ?_
  rw [traceWAbs, mul_comm, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun i => ?_) (F.summable_norm_termW W hτ)
    ((F.summable_weightedWeight W hτ).mul_left _)
  rw [termW, norm_mul]
  have hterm : ‖F.term τ i‖ ≤ Real.exp (lam * |τ.im|) * F.weight τ.re i := by
    rw [norm_term, weight, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hkey : τ.im * (F.pt i).im ≤ lam * |τ.im| := by
      calc τ.im * (F.pt i).im ≤ |τ.im * (F.pt i).im| := le_abs_self _
        _ = |τ.im| * |(F.pt i).im| := abs_mul _ _
        _ ≤ |τ.im| * lam := mul_le_mul_of_nonneg_left (him i) (abs_nonneg _)
        _ = lam * |τ.im| := by ring
    linarith
  calc ‖W.toFun (F.pt i)‖ * ‖F.term τ i‖
      ≤ ‖W.toFun (F.pt i)‖ * (Real.exp (lam * |τ.im|) * F.weight τ.re i) :=
        mul_le_mul_of_nonneg_left hterm (norm_nonneg _)
    _ = Real.exp (lam * |τ.im|) * (‖W.toFun (F.pt i)‖ * F.weight τ.re i) := by ring

/-- The weighted real-time majorant is antitone. -/
theorem traceWAbs_antitone {σ v : ℝ} (hσ : 0 < σ) (hv : 0 ≤ v) :
    F.traceWAbs W (σ + v) ≤ F.traceWAbs W σ := by
  refine Summable.tsum_le_tsum (fun i => ?_) (F.summable_weightedWeight W (by linarith))
    (F.summable_weightedWeight W hσ)
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [weight, weight]
  refine Real.exp_le_exp.mpr ?_
  nlinarith [F.re_nonneg i, hv]

/-! ## Analyticity in the time variable -/

theorem differentiable_termW (i : ι) : Differentiable ℂ fun τ : ℂ => F.termW W τ i := by
  unfold termW term
  fun_prop

theorem norm_termW_le_on_box {σ₀ M : ℝ} (i : ι) {t : ℂ} (ht : t ∈ box σ₀ M) :
    ‖F.termW W t i‖ ≤ Real.exp (M / 2) * (‖W.toFun (F.pt i)‖ * F.weight σ₀ i) := by
  rw [termW, norm_mul]
  have h := F.norm_term_le_on_box (σ₀ := σ₀) (M := M) i ht
  calc ‖W.toFun (F.pt i)‖ * ‖F.term t i‖
      ≤ ‖W.toFun (F.pt i)‖ * (Real.exp (M / 2) * F.weight σ₀ i) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = Real.exp (M / 2) * (‖W.toFun (F.pt i)‖ * F.weight σ₀ i) := by ring

theorem differentiableOn_traceWC_box {σ₀ M : ℝ} (hσ₀ : 0 < σ₀) :
    DifferentiableOn ℂ (F.traceWC W) (box σ₀ M) :=
  Complex.differentiableOn_tsum_of_summable_norm
    (u := fun i : ι => Real.exp (M / 2) * (‖W.toFun (F.pt i)‖ * F.weight σ₀ i))
    ((F.summable_weightedWeight W hσ₀).mul_left _)
    (fun i => (F.differentiable_termW W i).differentiableOn)
    (isOpen_box σ₀ M)
    (fun i _ ht => F.norm_termW_le_on_box W i ht)

theorem differentiableAt_traceWC {t : ℂ} (ht : 0 < t.re) :
    DifferentiableAt ℂ (F.traceWC W) t := by
  have hmem : t ∈ box (t.re / 2) (|t.im| + 1) := ⟨by linarith, by linarith⟩
  refine (F.differentiableOn_traceWC_box W (M := |t.im| + 1)
    (by linarith : (0 : ℝ) < t.re / 2)).differentiableAt ?_
  exact (isOpen_box _ _).mem_nhds hmem

variable [Nonempty ι]

/-- Moving right by `v` costs the weighted majorant at least the least-height rate. -/
theorem exp_bottomHeight_mul_traceWAbs_le {σ : ℝ} (hσ : 0 < σ) {v : ℝ} (hv : 0 ≤ v) :
    Real.exp (F.bottomHeight * v) * F.traceWAbs W (σ + v) ≤ F.traceWAbs W σ := by
  have hterm : ∀ i : ι,
      Real.exp (F.bottomHeight * v) * (‖W.toFun (F.pt i)‖ * F.weight (σ + v) i)
        ≤ ‖W.toFun (F.pt i)‖ * F.weight σ i := by
    intro i
    have hw : Real.exp (F.bottomHeight * v) * F.weight (σ + v) i ≤ F.weight σ i := by
      rw [weight, weight, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith [F.bottomHeight_le i, hv]
    calc Real.exp (F.bottomHeight * v) * (‖W.toFun (F.pt i)‖ * F.weight (σ + v) i)
        = ‖W.toFun (F.pt i)‖ * (Real.exp (F.bottomHeight * v) * F.weight (σ + v) i) := by ring
      _ ≤ ‖W.toFun (F.pt i)‖ * F.weight σ i :=
          mul_le_mul_of_nonneg_left hw (norm_nonneg _)
  calc Real.exp (F.bottomHeight * v) * F.traceWAbs W (σ + v)
      = ∑' i : ι, Real.exp (F.bottomHeight * v) * (‖W.toFun (F.pt i)‖ * F.weight (σ + v) i) := by
        rw [traceWAbs, tsum_mul_left]
    _ ≤ ∑' i : ι, ‖W.toFun (F.pt i)‖ * F.weight σ i :=
        Summable.tsum_le_tsum hterm ((F.summable_weightedWeight W (by linarith)).mul_left _)
          (F.summable_weightedWeight W hσ)
    _ = F.traceWAbs W σ := rfl

end

end AbstractSpectralFamily

end HTGeometry
