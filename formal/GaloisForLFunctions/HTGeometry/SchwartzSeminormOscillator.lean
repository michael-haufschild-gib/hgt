import GaloisForLFunctions.HTGeometry.SchwartzShiftControlled

/-!
# The Schwartz seminorms are bounded by the oscillator seminorms

A Schwartz seminorm bounds `‖x‖ᵏ‖f⁽ⁿ⁾(x)‖`, which is the pointwise norm of the Schwartz function
obtained by applying multiplication by the coordinate `k` times and differentiation `n` times.  The
Sobolev estimate bounds that supremum by the `L²` norm of the elliptic operator applied to it, and
the control calculus bounds that by a power of the shifted number operator.

So every Schwartz seminorm is bounded by a fixed multiple of `‖K^{k+n+2}f‖₂`: the oscillator
presentation of the Schwartz topology is finer than the standard one.  With the converse comparison
already proved, the two presentations agree.

* `coe_derivSCLM_iterate` : iterating the derivative operator is the iterated derivative.
* `mulXCLM_iterate_apply` : iterating multiplication is multiplication by the power.
* `l2ShiftControlled_iterate` : iterating a controlled operator multiplies the order.
* `schwartzSeminorm_le_shifted` : **`p_{k,n}(f) ≤ C‖K^{k+n+2}f‖₂`.**
-/

open scoped Real SchwartzMap
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-! ## Iterates of the basic operators -/

theorem coe_derivSCLM_iterate (n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    (((derivSCLM^[n]) f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = iteratedDeriv n (f : ℝ → ℂ) := by
  induction n generalizing f with
  | zero => rw [Function.iterate_zero_apply, iteratedDeriv_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply, iteratedDeriv_succ']
    rw [ih (derivSCLM f), coe_derivSCLM]

theorem mulXCLM_iterate_apply (k : ℕ) (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ((mulXCLM^[k]) g) x = (x : ℂ) ^ k * g x := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', mulXCLM_apply, ih g, pow_succ]
    ring

theorem norm_mulXCLM_iterate_apply (k : ℕ) (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖((mulXCLM^[k]) g) x‖ = ‖x‖ ^ k * ‖g x‖ := by
  rw [mulXCLM_iterate_apply, norm_mul, norm_pow, Complex.norm_real]

/-! ## Iterating a controlled operator -/

theorem l2ShiftControlled_iterate {T : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ)} {m : ℕ} (h : L2ShiftControlled T m)
    (k : ℕ) : L2ShiftControlled (fun g => (T^[k]) g) (k * m) := by
  induction k with
  | zero =>
    refine l2ShiftControlled_id.order_congr ?_ |>.congr fun g => ?_
    · omega
    · rw [Function.iterate_zero_apply]
  | succ k ih =>
    have hcomp : L2ShiftControlled (fun g => T ((T^[k]) g)) (m + k * m) := h.comp ih
    refine (hcomp.order_congr (by ring)).congr fun g => ?_
    exact (Function.iterate_succ_apply' T k g).symm

/-! ## The seminorm bound -/

/-- **Every Schwartz seminorm is bounded by a power of the shifted number operator.**  The
seminorm bounds the supremum of `x ↦ xᵏf⁽ⁿ⁾(x)`, which is a Schwartz function obtained from `f` by
operators controlled at order `k+n`; the Sobolev estimate and the control calculus turn its
supremum into an `L²` norm of `K^{k+n+2}f`. -/
theorem schwartzSeminorm_le_shifted (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝓢(ℝ, ℂ),
      SchwartzMap.seminorm ℂ k n f
        ≤ C * ‖((shiftedNumberCLM^[k + n + 2]) f).toLp 2 (volume : Measure ℝ)‖ := by
  classical
  set Cs : ℝ := (∫ t : ℝ, ((1 + t ^ (2 : ℕ))⁻¹) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) with hCs
  have hCs_nonneg : 0 ≤ Cs := by
    rw [hCs]
    positivity
  have hcontrol : L2ShiftControlled
      (fun f : 𝓢(ℝ, ℂ) => sobolevOp ((mulXCLM^[k]) ((derivSCLM^[n]) f))) (k + n + 2) := by
    have hmul : L2ShiftControlled (fun g : 𝓢(ℝ, ℂ) => (mulXCLM^[k]) g) k :=
      (l2ShiftControlled_iterate l2ShiftControlled_mulXCLM k).order_congr (by ring)
    have hderiv : L2ShiftControlled (fun g : 𝓢(ℝ, ℂ) => (derivSCLM^[n]) g) n :=
      (l2ShiftControlled_iterate l2ShiftControlled_derivSCLM n).order_congr (by ring)
    have hcomp := (l2ShiftControlled_sobolevOp.comp hmul).comp hderiv
    exact hcomp.order_congr (by omega)
  obtain ⟨C, hC, hbound⟩ := hcontrol 0
  refine ⟨Cs * C, by positivity, fun f => ?_⟩
  refine SchwartzMap.seminorm_le_bound ℂ k n f (by positivity) fun x => ?_
  have hpoint : ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) x‖
      = ‖((mulXCLM^[k]) ((derivSCLM^[n]) f)) x‖ := by
    rw [norm_mulXCLM_iterate_apply, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      coe_derivSCLM_iterate]
  rw [hpoint]
  calc ‖((mulXCLM^[k]) ((derivSCLM^[n]) f)) x‖
      ≤ Cs * ‖(sobolevOp ((mulXCLM^[k]) ((derivSCLM^[n]) f))).toLp
          2 (volume : Measure ℝ)‖ := norm_apply_le_sobolev _ x
    _ ≤ Cs * (C * ‖((shiftedNumberCLM^[k + n + 2]) f).toLp 2 (volume : Measure ℝ)‖) := by
        refine mul_le_mul_of_nonneg_left ?_ hCs_nonneg
        have h := hbound f
        simpa using h
    _ = Cs * C * ‖((shiftedNumberCLM^[k + n + 2]) f).toLp 2 (volume : Measure ℝ)‖ := by ring

end GaloisForLFunctions

end
