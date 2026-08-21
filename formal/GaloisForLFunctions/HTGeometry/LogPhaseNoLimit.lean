import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Logarithmic phases do not converge

A nonzero harmonic `A cos (b u) + B sin (b u)` with `b ≠ 0` is periodic and nonconstant, so it has
no limit as `u → ∞`.  Substituting `u = log x` transports this to the logarithmic phase
`A cos (b log x) + B sin (b log x)`, and multiplying by a growing power `x ^ d`, `d > 0`, destroys
convergence even more strongly: the amplified phase is unbounded in both signs.

These statements are the exact obstruction to reading an asymptotic value off an oscillating
primitive of `x^(c-1) cos (b log x)` at infinity.
-/

open Real Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- A periodic function with a limit at `+∞` is constant. -/
theorem eq_of_periodic_of_tendsto_atTop {g : ℝ → ℝ} {T L : ℝ} (hT : 0 < T)
    (hper : Function.Periodic g T) (h : Tendsto g atTop (𝓝 L)) (u : ℝ) : g u = L := by
  have hseq : Tendsto (fun n : ℕ => u + n * T) atTop atTop := by
    refine tendsto_atTop_add_const_left _ u ?_
    exact tendsto_natCast_atTop_atTop.atTop_mul_const hT
  have h2 : Tendsto (fun n : ℕ => g (u + n * T)) atTop (𝓝 L) := h.comp hseq
  have h3 : (fun n : ℕ => g (u + n * T)) = fun _ : ℕ => g u := by
    funext n
    exact (hper.nat_mul n) u
  rw [h3] at h2
  exact tendsto_nhds_unique tendsto_const_nhds h2

/-- The harmonic `A cos (b u) + B sin (b u)` is `2π/|b|`-periodic. -/
theorem periodic_harmonic (A B : ℝ) {b : ℝ} (hb : b ≠ 0) :
    Function.Periodic (fun u : ℝ => A * Real.cos (b * u) + B * Real.sin (b * u))
      (2 * Real.pi / |b|) := by
  intro u
  show A * Real.cos (b * (u + 2 * Real.pi / |b|)) + B * Real.sin (b * (u + 2 * Real.pi / |b|))
      = A * Real.cos (b * u) + B * Real.sin (b * u)
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · have h : b * (u + 2 * Real.pi / |b|) = b * u - 2 * Real.pi := by
      rw [abs_of_neg hneg]
      field_simp
      ring
    rw [h, Real.cos_sub_two_pi, Real.sin_sub_two_pi]
  · have h : b * (u + 2 * Real.pi / |b|) = b * u + 2 * Real.pi := by
      rw [abs_of_pos hpos]
      field_simp
    rw [h, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- A nonzero harmonic has no limit at `+∞`. -/
theorem not_tendsto_harmonic_atTop {A B b L : ℝ} (hb : b ≠ 0) (hAB : A ≠ 0 ∨ B ≠ 0) :
    ¬ Tendsto (fun u : ℝ => A * Real.cos (b * u) + B * Real.sin (b * u)) atTop (𝓝 L) := by
  intro h
  have hT : 0 < 2 * Real.pi / |b| := div_pos (by positivity) (abs_pos.mpr hb)
  have hconst := eq_of_periodic_of_tendsto_atTop hT (periodic_harmonic A B hb) h
  have h0 : A = L := by simpa using hconst 0
  have hpi : -A = L := by
    have := hconst (Real.pi / b)
    rw [mul_div_cancel₀ _ hb] at this
    simpa using this
  have hA : A = 0 := by linarith
  have hL : L = 0 := by rw [← h0, hA]
  have hhalf : B = L := by
    have := hconst (Real.pi / (2 * b))
    have hrw : b * (Real.pi / (2 * b)) = Real.pi / 2 := by field_simp
    rw [hrw] at this
    simpa using this
  rcases hAB with hA' | hB'
  · exact hA' hA
  · exact hB' (by rw [hhalf, hL])

/-- A nonzero logarithmic phase has no limit at `+∞`. -/
theorem not_tendsto_logHarmonic_atTop {A B b L : ℝ} (hb : b ≠ 0) (hAB : A ≠ 0 ∨ B ≠ 0) :
    ¬ Tendsto (fun x : ℝ => A * Real.cos (b * Real.log x) + B * Real.sin (b * Real.log x))
      atTop (𝓝 L) := by
  intro h
  refine not_tendsto_harmonic_atTop (A := A) (B := B) (b := b) (L := L) hb hAB ?_
  have hcomp := h.comp Real.tendsto_exp_atTop
  refine hcomp.congr fun u => ?_
  simp [Function.comp, Real.log_exp]

/-- `cos (b log x)` has no limit at `+∞` when `b ≠ 0`. -/
theorem not_tendsto_cos_log_atTop {b L : ℝ} (hb : b ≠ 0) :
    ¬ Tendsto (fun x : ℝ => Real.cos (b * Real.log x)) atTop (𝓝 L) := by
  intro h
  refine not_tendsto_logHarmonic_atTop (A := 1) (B := 0) (b := b) (L := L) hb (Or.inl one_ne_zero) ?_
  simpa using h

/-- `sin (b log x)` has no limit at `+∞` when `b ≠ 0`. -/
theorem not_tendsto_sin_log_atTop {b L : ℝ} (hb : b ≠ 0) :
    ¬ Tendsto (fun x : ℝ => Real.sin (b * Real.log x)) atTop (𝓝 L) := by
  intro h
  refine not_tendsto_logHarmonic_atTop (A := 0) (B := 1) (b := b) (L := L) hb (Or.inr one_ne_zero) ?_
  simpa using h

/-- A logarithmic phase attains a nonzero value. -/
theorem exists_logHarmonic_ne_zero {A B b : ℝ} (hb : b ≠ 0) (hAB : A ≠ 0 ∨ B ≠ 0) :
    ∃ u : ℝ, A * Real.cos (b * u) + B * Real.sin (b * u) ≠ 0 := by
  rcases hAB with hA | hB
  · exact ⟨0, by simpa using hA⟩
  · refine ⟨Real.pi / (2 * b), ?_⟩
    have hrw : b * (Real.pi / (2 * b)) = Real.pi / 2 := by field_simp
    rw [hrw]
    simpa using hB

/-- **An amplified logarithmic phase has no limit.**  For `d > 0` and a nonzero harmonic the
function `x ↦ x^d (A cos (b log x) + B sin (b log x))` is unbounded along a sequence, so it
converges to no real number. -/
theorem not_tendsto_rpow_mul_logHarmonic_atTop {A B b d L : ℝ} (hb : b ≠ 0)
    (hAB : A ≠ 0 ∨ B ≠ 0) (hd : 0 < d) :
    ¬ Tendsto (fun x : ℝ =>
        x ^ d * (A * Real.cos (b * Real.log x) + B * Real.sin (b * Real.log x)))
      atTop (𝓝 L) := by
  intro h
  obtain ⟨u₀, hu₀⟩ := exists_logHarmonic_ne_zero hb hAB
  set T : ℝ := 2 * Real.pi / |b| with hTdef
  have hT : 0 < T := div_pos (by positivity) (abs_pos.mpr hb)
  have hper := periodic_harmonic A B hb
  -- the sequence of sample points
  have hseq : Tendsto (fun n : ℕ => Real.exp (u₀ + n * T)) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (tendsto_atTop_add_const_left _ u₀ (tendsto_natCast_atTop_atTop.atTop_mul_const hT))
  have hlim : Tendsto
      (fun n : ℕ => Real.exp (u₀ + n * T) ^ d *
        (A * Real.cos (b * Real.log (Real.exp (u₀ + n * T)))
          + B * Real.sin (b * Real.log (Real.exp (u₀ + n * T))))) atTop (𝓝 L) := h.comp hseq
  have hval : ∀ n : ℕ, Real.exp (u₀ + n * T) ^ d *
      (A * Real.cos (b * Real.log (Real.exp (u₀ + n * T)))
        + B * Real.sin (b * Real.log (Real.exp (u₀ + n * T))))
      = Real.exp ((u₀ + n * T) * d) * (A * Real.cos (b * u₀) + B * Real.sin (b * u₀)) := by
    intro n
    rw [Real.log_exp, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    exact (hper.nat_mul n) u₀
  rw [funext hval] at hlim
  have habs : Tendsto (fun n : ℕ =>
      |Real.exp ((u₀ + n * T) * d) * (A * Real.cos (b * u₀) + B * Real.sin (b * u₀))|)
      atTop (𝓝 |L|) := hlim.abs
  have hgrow : Tendsto (fun n : ℕ =>
      |Real.exp ((u₀ + n * T) * d) * (A * Real.cos (b * u₀) + B * Real.sin (b * u₀))|)
      atTop atTop := by
    have hexp : Tendsto (fun n : ℕ => Real.exp ((u₀ + n * T) * d)) atTop atTop :=
      Real.tendsto_exp_atTop.comp
        ((tendsto_atTop_add_const_left _ u₀
          (tendsto_natCast_atTop_atTop.atTop_mul_const hT)).atTop_mul_const hd)
    have := hexp.atTop_mul_const (abs_pos.mpr hu₀)
    refine this.congr fun n => ?_
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact not_tendsto_nhds_of_tendsto_atTop hgrow _ habs

end GaloisForLFunctions.HTGeometry
