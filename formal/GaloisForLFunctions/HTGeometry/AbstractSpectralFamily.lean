import GaloisForLFunctions.HTGeometry.GeometricAmplitudeDominance
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Abstract spectral families

The vertical-line rigidity proved for the Xi divisor uses nothing about that divisor: it uses a
countable family of points in the right half-plane with heights bounded below, displacements
uniformly bounded, summable weight, finite shells, and an involution conjugating the points.

This file carries the interface over an arbitrary index type, so that the resulting theorem is a
statement about the spectrum of an operator rather than about zeta.  The analytic facts that depend
only on the interface -- the exponential-type envelope, summability, monotonicity of the real-time
trace, and analyticity on the right half-plane -- are proved here.
-/

open Complex Filter
open scoped BigOperators

namespace HTGeometry

noncomputable section

/-- A countable family of spectral points admissible for the vertical-line argument. -/
structure AbstractSpectralFamily (ι : Type*) where
  /-- the points -/
  pt : ι → ℂ
  /-- an involution of the index set -/
  inv : ι ≃ ι
  /-- a positive lower bound for the heights -/
  base : ℝ
  base_pos : 0 < base
  base_le : ∀ i, base ≤ (pt i).re
  /-- displacements are uniformly bounded by one half -/
  abs_im_lt : ∀ i, |(pt i).im| < 1 / 2
  /-- the real-time weight is summable -/
  summable_weight : ∀ {σ : ℝ}, 0 < σ → Summable fun i => Real.exp (-(σ * (pt i).re))
  /-- shells are finite -/
  shell_finite : ∀ R : ℝ, {i : ι | (pt i).re ≤ R}.Finite
  /-- the involution conjugates the points -/
  conj_stable : ∀ i, pt (inv i) = (starRingEnd ℂ) (pt i)

namespace AbstractSpectralFamily

variable {ι : Type*} (F : AbstractSpectralFamily ι)

theorem re_nonneg (i : ι) : 0 ≤ (F.pt i).re := le_trans F.base_pos.le (F.base_le i)

/-- The real-time weight. -/
def weight (σ : ℝ) (i : ι) : ℝ := Real.exp (-(σ * (F.pt i).re))

theorem weight_pos (σ : ℝ) (i : ι) : 0 < F.weight σ i := Real.exp_pos _

/-- The multiplier at complex time. -/
def term (τ : ℂ) (i : ι) : ℂ := Complex.exp (-τ * F.pt i)

theorem norm_term (τ : ℂ) (i : ι) :
    ‖F.term τ i‖ = Real.exp (-(τ.re * (F.pt i).re - τ.im * (F.pt i).im)) := by
  rw [term, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- **The unconditional termwise envelope: exponential type at most one half.** -/
theorem norm_term_le (τ : ℂ) (i : ι) :
    ‖F.term τ i‖ ≤ Real.exp (|τ.im| / 2) * F.weight τ.re i := by
  rw [norm_term, weight, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hkey : τ.im * (F.pt i).im ≤ |τ.im| / 2 := by
    calc τ.im * (F.pt i).im ≤ |τ.im * (F.pt i).im| := le_abs_self _
      _ = |τ.im| * |(F.pt i).im| := abs_mul _ _
      _ ≤ |τ.im| * (1 / 2) := mul_le_mul_of_nonneg_left (F.abs_im_lt i).le (abs_nonneg _)
      _ = |τ.im| / 2 := by ring
  linarith

theorem summable_norm_term {τ : ℂ} (hτ : 0 < τ.re) :
    Summable fun i => ‖F.term τ i‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => F.norm_term_le τ i)
    ((F.summable_weight hτ).mul_left _)

/-- The real-time trace. -/
def traceReal (σ : ℝ) : ℝ := ∑' i : ι, F.weight σ i

/-- The trace at complex time. -/
def traceC (τ : ℂ) : ℂ := ∑' i : ι, F.term τ i

theorem traceReal_nonneg (σ : ℝ) : 0 ≤ F.traceReal σ :=
  tsum_nonneg fun i => (F.weight_pos σ i).le

/-- **The unconditional vertical envelope.** -/
theorem norm_traceC_le {τ : ℂ} (hτ : 0 < τ.re) :
    ‖F.traceC τ‖ ≤ Real.exp (|τ.im| / 2) * F.traceReal τ.re := by
  refine le_trans (norm_tsum_le_tsum_norm (F.summable_norm_term hτ)) ?_
  rw [traceReal, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun i => F.norm_term_le τ i) (F.summable_norm_term hτ)
    ((F.summable_weight hτ).mul_left _)

/-- A displacement bound gives a growth bound: the easy direction, graded. -/
theorem norm_traceC_le_of_abs_im_le {lam : ℝ} (him : ∀ i, |(F.pt i).im| ≤ lam)
    {τ : ℂ} (hτ : 0 < τ.re) :
    ‖F.traceC τ‖ ≤ F.traceReal τ.re * Real.exp (lam * |τ.im|) := by
  refine le_trans (norm_tsum_le_tsum_norm (F.summable_norm_term hτ)) ?_
  rw [traceReal, mul_comm, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun i => ?_) (F.summable_norm_term hτ)
    ((F.summable_weight hτ).mul_left _)
  rw [norm_term, weight, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hkey : τ.im * (F.pt i).im ≤ lam * |τ.im| := by
    calc τ.im * (F.pt i).im ≤ |τ.im * (F.pt i).im| := le_abs_self _
      _ = |τ.im| * |(F.pt i).im| := abs_mul _ _
      _ ≤ |τ.im| * lam := mul_le_mul_of_nonneg_left (him i) (abs_nonneg _)
      _ = lam * |τ.im| := by ring
  linarith

/-- The real-time trace is antitone. -/
theorem traceReal_antitone {σ v : ℝ} (hσ : 0 < σ) (hv : 0 ≤ v) :
    F.traceReal (σ + v) ≤ F.traceReal σ := by
  refine Summable.tsum_le_tsum (fun i => ?_) (F.summable_weight (by linarith))
    (F.summable_weight hσ)
  rw [weight, weight]
  refine Real.exp_le_exp.mpr ?_
  nlinarith [F.re_nonneg i, hv]

/-- Any nonempty set of indices attains a least height. -/
theorem exists_min_re_of_nonempty {s : Set ι} (hs : s.Nonempty) :
    ∃ i₀ ∈ s, ∀ i ∈ s, (F.pt i₀).re ≤ (F.pt i).re := by
  classical
  obtain ⟨i₁, hi₁⟩ := hs
  have hfin : (s ∩ {i : ι | (F.pt i).re ≤ (F.pt i₁).re}).Finite :=
    (F.shell_finite (F.pt i₁).re).subset Set.inter_subset_right
  have hmem : i₁ ∈ hfin.toFinset := by
    simp only [Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨hi₁, le_refl _⟩
  obtain ⟨i₀, hi₀mem, hi₀min⟩ :=
    Finset.exists_min_image hfin.toFinset (fun i => (F.pt i).re) ⟨i₁, hmem⟩
  have hi₀ : i₀ ∈ s ∧ (F.pt i₀).re ≤ (F.pt i₁).re := by
    simpa only [Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq] using hi₀mem
  refine ⟨i₀, hi₀.1, fun i hi => ?_⟩
  by_cases hcase : (F.pt i).re ≤ (F.pt i₁).re
  · refine hi₀min i ?_
    simp only [Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨hi, hcase⟩
  · linarith [not_le.mp hcase, hi₀.2]

/-- A box of the open right half-plane. -/
def box (σ₀ M : ℝ) : Set ℂ := {t : ℂ | σ₀ < t.re ∧ |t.im| < M}

theorem isOpen_box (σ₀ M : ℝ) : IsOpen (box σ₀ M) := by
  refine IsOpen.inter (isOpen_lt continuous_const Complex.continuous_re) ?_
  exact isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem differentiable_term (i : ι) : Differentiable ℂ fun τ : ℂ => F.term τ i := by
  unfold term
  fun_prop

theorem norm_term_le_on_box {σ₀ M : ℝ} (i : ι) {t : ℂ} (ht : t ∈ box σ₀ M) :
    ‖F.term t i‖ ≤ Real.exp (M / 2) * F.weight σ₀ i := by
  obtain ⟨hre, him⟩ := ht
  rw [norm_term, weight, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h1 : σ₀ * (F.pt i).re ≤ t.re * (F.pt i).re :=
    mul_le_mul_of_nonneg_right hre.le (F.re_nonneg i)
  have h2 : t.im * (F.pt i).im ≤ M / 2 := by
    calc t.im * (F.pt i).im ≤ |t.im * (F.pt i).im| := le_abs_self _
      _ = |t.im| * |(F.pt i).im| := abs_mul _ _
      _ ≤ M * (1 / 2) := by
          refine mul_le_mul him.le (F.abs_im_lt i).le (abs_nonneg _) ?_
          exact le_trans (abs_nonneg _) him.le
      _ = M / 2 := by ring
  linarith

theorem differentiableOn_traceC_box {σ₀ M : ℝ} (hσ₀ : 0 < σ₀) :
    DifferentiableOn ℂ F.traceC (box σ₀ M) :=
  Complex.differentiableOn_tsum_of_summable_norm
    (u := fun i : ι => Real.exp (M / 2) * F.weight σ₀ i)
    ((F.summable_weight hσ₀).mul_left _)
    (fun i => (F.differentiable_term i).differentiableOn)
    (isOpen_box σ₀ M)
    (fun i _ ht => F.norm_term_le_on_box i ht)

theorem differentiableAt_traceC {t : ℂ} (ht : 0 < t.re) : DifferentiableAt ℂ F.traceC t := by
  have hmem : t ∈ box (t.re / 2) (|t.im| + 1) := ⟨by linarith, by linarith⟩
  refine (F.differentiableOn_traceC_box (M := |t.im| + 1)
    (by linarith : (0 : ℝ) < t.re / 2)).differentiableAt ?_
  exact (isOpen_box _ _).mem_nhds hmem

/-- **The trace of an abstract admissible family is analytic on the open right half-plane.** -/
theorem analyticOnNhd_traceC : AnalyticOnNhd ℂ F.traceC {t : ℂ | 0 < t.re} := by
  refine DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const Complex.continuous_re)
  intro t ht
  exact (F.differentiableAt_traceC ht).differentiableWithinAt

end AbstractSpectralFamily

end

end HTGeometry
