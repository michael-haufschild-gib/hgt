import Mathlib

/-!
# Two-channel Robertson determinant inequalities

The usual Robertson estimate retains one generator channel.  The characteristic
multi-observable uncertainty relation instead keeps the full Gram matrix.  Its
three-vector determinant gives an exact two-channel bound and permits the
generator channel to be optimized after the source state is fixed.
-/

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace HTGeometry

noncomputable section

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Three-vector Gram-determinant form of the two-channel Robertson inequality.
The two mixed responses on the left are controlled by the determinant of the
two generator channels. -/
theorem twoChannelRobertsonGram (f g h : E) :
    inner ℝ f g ^ (2 : ℕ) * inner ℝ h h -
          2 * inner ℝ f g * inner ℝ f h * inner ℝ g h +
          inner ℝ f h ^ (2 : ℕ) * inner ℝ g g ≤
      inner ℝ f f *
        (inner ℝ g g * inner ℝ h h - inner ℝ g h ^ (2 : ℕ)) := by
  let v : Fin 3 → E := ![f, g, h]
  have hdet := (Matrix.posSemidef_gram ℝ v).det_nonneg
  simp [Matrix.det_fin_three, Matrix.gram_apply, v, real_inner_comm] at hdet
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  nlinarith

variable {alpha : Type*} [MeasurableSpace alpha] {mu : Measure alpha}

/-- Integral form of `twoChannelRobertsonGram`.  This is the directly reusable
multi-observable uncertainty law for three real square-integrable fields. -/
theorem twoChannelIntegralRobertson {f g h : alpha → ℝ}
    (hf : MemLp f 2 mu) (hg : MemLp g 2 mu) (hh : MemLp h 2 mu) :
    (∫ x, f x * g x ∂mu) ^ (2 : ℕ) * (∫ x, h x ^ (2 : ℕ) ∂mu) -
          2 * (∫ x, f x * g x ∂mu) * (∫ x, f x * h x ∂mu) *
            (∫ x, g x * h x ∂mu) +
          (∫ x, f x * h x ∂mu) ^ (2 : ℕ) * (∫ x, g x ^ (2 : ℕ) ∂mu) ≤
      (∫ x, f x ^ (2 : ℕ) ∂mu) *
        ((∫ x, g x ^ (2 : ℕ) ∂mu) * (∫ x, h x ^ (2 : ℕ) ∂mu) -
          (∫ x, g x * h x ∂mu) ^ (2 : ℕ)) := by
  let F : Lp ℝ 2 mu := hf.toLp f
  let G : Lp ℝ 2 mu := hg.toLp g
  let H : Lp ℝ 2 mu := hh.toLp h
  have hinner (u v : alpha → ℝ) (hu : MemLp u 2 mu) (hv : MemLp v 2 mu) :
      inner ℝ (hu.toLp u) (hv.toLp v) = ∫ x, u x * v x ∂mu := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x hux hvx
    rw [hux, hvx]
    simp [mul_comm]
  have hF2 : inner ℝ F F = ∫ x, f x ^ (2 : ℕ) ∂mu := by
    rw [show F = hf.toLp f by rfl, hinner f f hf hf]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have hG2 : inner ℝ G G = ∫ x, g x ^ (2 : ℕ) ∂mu := by
    rw [show G = hg.toLp g by rfl, hinner g g hg hg]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have hH2 : inner ℝ H H = ∫ x, h x ^ (2 : ℕ) ∂mu := by
    rw [show H = hh.toLp h by rfl, hinner h h hh hh]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have hFG : inner ℝ F G = ∫ x, f x * g x ∂mu := hinner f g hf hg
  have hFH : inner ℝ F H = ∫ x, f x * h x ∂mu := hinner f h hf hh
  have hGH : inner ℝ G H = ∫ x, g x * h x ∂mu := hinner g h hg hh
  have hgram := twoChannelRobertsonGram F G H
  rwa [hF2, hG2, hH2, hFG, hFH, hGH] at hgram

end

end HTGeometry
