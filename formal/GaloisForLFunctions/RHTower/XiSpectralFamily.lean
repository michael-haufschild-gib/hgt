import GaloisForLFunctions.RHTower.XiPoissonShellSplit

/-!
# Admissible spectral families

The vertical-line criterion of `XiPoissonLineBoundRH` never uses the Poisson coordinate as such.  It
uses a family of points indexed by the Xi divisor with six properties: heights bounded away from
zero, displacements uniformly bounded, a summable weight, finite shells, stability under line
conjugation, and the identification of vanishing displacement with the critical line.

This file records that interface and proves the facts that depend only on it: the exponential-type
envelope, summability, and the collapse of the envelope when all displacements vanish.

The Poisson family is the instance carried by the rest of the corpus.  The point of the abstraction
is a second instance -- the mass-shifted family `sqrt (alpha^ ^ 2 + a^2)`, which is prime-accessible
where the Poisson family is not.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A family of spectral points admissible for the vertical-line argument. -/
structure SpectralFamily where
  /-- the points -/
  pt : XiZeroCopy → ℂ
  /-- a positive lower bound for the heights -/
  base : ℝ
  base_pos : 0 < base
  base_le : ∀ q, base ≤ (pt q).re
  /-- displacements are uniformly bounded by one half -/
  abs_im_lt : ∀ q, |(pt q).im| < 1 / 2
  /-- the real-time weight is summable -/
  summable_weight : ∀ {σ : ℝ}, 0 < σ →
    Summable (fun q : XiZeroCopy => Real.exp (-(σ * (pt q).re)))
  /-- shells are finite -/
  shell_finite : ∀ R : ℝ, {q : XiZeroCopy | (pt q).re ≤ R}.Finite
  /-- line conjugation conjugates the points -/
  conj_stable : ∀ q, pt (xiZeroCopyLineConjEquiv q) = (starRingEnd ℂ) (pt q)

namespace SpectralFamily

variable (F : SpectralFamily)

theorem re_nonneg (q : XiZeroCopy) : 0 ≤ (F.pt q).re :=
  le_trans F.base_pos.le (F.base_le q)

/-- The real-time weight of the family. -/
def weight (σ : ℝ) (q : XiZeroCopy) : ℝ := Real.exp (-(σ * (F.pt q).re))

theorem weight_pos (σ : ℝ) (q : XiZeroCopy) : 0 < F.weight σ q := Real.exp_pos _

/-- The multiplier at complex time. -/
def term (τ : ℂ) (q : XiZeroCopy) : ℂ := Complex.exp (-τ * F.pt q)

theorem norm_term (τ : ℂ) (q : XiZeroCopy) :
    ‖F.term τ q‖ = Real.exp (-(τ.re * (F.pt q).re - τ.im * (F.pt q).im)) := by
  rw [term, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- **The unconditional termwise envelope: exponential type at most one half.** -/
theorem norm_term_le (τ : ℂ) (q : XiZeroCopy) :
    ‖F.term τ q‖ ≤ Real.exp (|τ.im| / 2) * F.weight τ.re q := by
  rw [norm_term, weight, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hhalf := F.abs_im_lt q
  have hkey : τ.im * (F.pt q).im ≤ |τ.im| / 2 := by
    calc τ.im * (F.pt q).im ≤ |τ.im * (F.pt q).im| := le_abs_self _
      _ = |τ.im| * |(F.pt q).im| := abs_mul _ _
      _ ≤ |τ.im| * (1 / 2) := mul_le_mul_of_nonneg_left hhalf.le (abs_nonneg _)
      _ = |τ.im| / 2 := by ring
  linarith

theorem summable_norm_term {τ : ℂ} (hτ : 0 < τ.re) :
    Summable (fun q : XiZeroCopy => ‖F.term τ q‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => F.norm_term_le τ q)
    ((F.summable_weight hτ).mul_left _)

/-- The real-time trace of the family. -/
def traceReal (σ : ℝ) : ℝ := ∑' q : XiZeroCopy, F.weight σ q

/-- The trace of the family at complex time. -/
def traceC (τ : ℂ) : ℂ := ∑' q : XiZeroCopy, F.term τ q

theorem traceReal_nonneg (σ : ℝ) : 0 ≤ F.traceReal σ :=
  tsum_nonneg fun q => (F.weight_pos σ q).le

/-- **The unconditional vertical envelope.** -/
theorem norm_traceC_le {τ : ℂ} (hτ : 0 < τ.re) :
    ‖F.traceC τ‖ ≤ Real.exp (|τ.im| / 2) * F.traceReal τ.re := by
  refine le_trans (norm_tsum_le_tsum_norm (F.summable_norm_term hτ)) ?_
  rw [traceReal, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun q => F.norm_term_le τ q) (F.summable_norm_term hτ)
    ((F.summable_weight hτ).mul_left _)

/-- If every displacement vanishes the envelope collapses to boundedness. -/
theorem norm_traceC_le_of_im_eq_zero (him : ∀ q, (F.pt q).im = 0) {τ : ℂ} (hτ : 0 < τ.re) :
    ‖F.traceC τ‖ ≤ F.traceReal τ.re := by
  refine le_trans (norm_tsum_le_tsum_norm (F.summable_norm_term hτ)) ?_
  rw [traceReal]
  refine le_of_eq (tsum_congr fun q => ?_)
  rw [norm_term, him q, weight]
  congr 1
  ring

/-- The real-time trace is antitone. -/
theorem traceReal_antitone {σ v : ℝ} (hσ : 0 < σ) (hv : 0 ≤ v) :
    F.traceReal (σ + v) ≤ F.traceReal σ := by
  refine Summable.tsum_le_tsum (fun q => ?_) (F.summable_weight (by linarith))
    (F.summable_weight hσ)
  rw [weight, weight]
  refine Real.exp_le_exp.mpr ?_
  nlinarith [F.re_nonneg q, hv]

end SpectralFamily

/-- The Poisson family is admissible. -/
def xiPoissonFamily (h : 0 < xiPoissonBottomHeight) : SpectralFamily where
  pt := xiPoissonPoint
  base := xiPoissonBottomHeight
  base_pos := h
  base_le := fun q => xiPoissonBottomCopy_min q
  abs_im_lt := abs_xiPoissonPoint_im_lt_half
  summable_weight := fun hσ => summable_xiPoissonWeight hσ
  shell_finite := finite_xiPoissonShell
  conj_stable := xiPoissonPoint_lineConj

end

end RHTower
