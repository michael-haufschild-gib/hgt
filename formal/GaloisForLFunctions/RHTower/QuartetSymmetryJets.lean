import Mathlib

/-!
# Jets under the two quartet symmetries

A quartet packet `{α, -α, conj α, -conj α}` is the orbit of `α` under the reflection `z ↦ -z` and
the Schwarz reflection `z ↦ conj z`.  The symmetry-compatible Hermite interpolation of the
quartet-passport realization prescribes jets at all four points, and the compatibility conditions
required by `RHTower/FiniteHermiteCRT.lean` are exactly the statements collected here.

Analytic side:

* `iteratedDeriv_comp_neg` — jets of `z ↦ f(-z)` are `(-1)^n` times the jets of `f` at the
  reflected point;
* `iteratedDeriv_of_even` — hence an even entire function has jets related by `(-1)^n` at
  antipodal points.

Polynomial side (the form the CRT interface uses, with `Polynomial.derivative^[n]`):

* `iterate_derivative_neg`, `iterate_derivative_comp_neg`, `iterate_derivative_comp_neg_eval` —
  the same sign rule for `P ∘ (-X)`;
* `iterate_derivative_map_conj_eval` — coefficientwise conjugation conjugates every jet.

Together these let the four target jets of a quartet be *defined* from the single target at `α` by
`P`, `P ∘ (-X)`, `P̄`, `P̄ ∘ (-X)`, so the CRT compatibility hypotheses hold by construction rather
than by an analytic computation at each of the four points.

The Schwarz counterpart on the analytic side is the tree's existing
`RHTower.iteratedDeriv_conj_conj` (`RHTower/CompletedFluxGradedReality.lean`), which is reused.
-/

noncomputable section

open Complex Polynomial

namespace RHTower


theorem iterate_derivative_neg (Q : Polynomial ℂ) (n : ℕ) :
    Polynomial.derivative^[n] (-Q) = -(Polynomial.derivative^[n] Q) := by
  induction n generalizing Q with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, map_neg, ih]

/-- Iterated complex derivatives under the reflection `z ↦ -z`. -/
theorem iteratedDeriv_comp_neg {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) (w : ℂ) :
    iteratedDeriv n (fun z => f (-z)) w = (-1) ^ n * iteratedDeriv n f (-w) := by
  induction n generalizing f w with
  | zero => simp
  | succ n ih =>
      have hderiv : Differentiable ℂ (deriv f) :=
        fun z => ((hf.analyticAt z).deriv).differentiableAt
      have hcomp : deriv (fun z : ℂ => f (-z)) = fun z : ℂ => -(deriv f) (-z) := by
        funext z
        have h1 : HasDerivAt (fun x : ℂ => -x) (-1 : ℂ) z := by
          have := (hasDerivAt_id z).neg
          exact this
        have h2 : HasDerivAt f (deriv f (-z)) (-z) := (hf (-z)).hasDerivAt
        have h3 : HasDerivAt (fun x : ℂ => f (-x)) (deriv f (-z) * (-1)) z := h2.comp z h1
        have h4 : deriv f (-z) * (-1 : ℂ) = -(deriv f) (-z) := by ring
        rw [h4] at h3
        exact h3.deriv
      rw [iteratedDeriv_succ', iteratedDeriv_succ', hcomp]
      have hneg : Differentiable ℂ (fun z : ℂ => -(deriv f) z) := hderiv.neg
      have hstep := ih (f := fun z : ℂ => -(deriv f) z) hneg w
      rw [hstep]
      have hnegD : iteratedDeriv n (fun z : ℂ => -(deriv f) z) (-w)
          = -iteratedDeriv n (deriv f) (-w) := by
        show iteratedDeriv n (-(deriv f)) (-w) = -iteratedDeriv n (deriv f) (-w)
        rw [iteratedDeriv_neg]
      rw [hnegD]
      ring

/-- Jets of an even entire function at antipodal points. -/
theorem iteratedDeriv_of_even {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (heven : ∀ z, f (-z) = f z) (n : ℕ) (w : ℂ) :
    iteratedDeriv n f (-w) = (-1) ^ n * iteratedDeriv n f w := by
  have hfun : (fun z : ℂ => f (-z)) = f := funext heven
  have h := iteratedDeriv_comp_neg hf n w
  rw [hfun] at h
  have hpow : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc iteratedDeriv n f (-w)
      = ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) * iteratedDeriv n f (-w) := by rw [hpow]; ring
    _ = (-1 : ℂ) ^ n * ((-1 : ℂ) ^ n * iteratedDeriv n f (-w)) := by ring
    _ = (-1 : ℂ) ^ n * iteratedDeriv n f w := by rw [← h]

/-- Polynomial jets under `X ↦ -X`. -/
theorem iterate_derivative_comp_neg (P : Polynomial ℂ) (n : ℕ) :
    Polynomial.derivative^[n] (P.comp (-X)) =
      Polynomial.C ((-1 : ℂ) ^ n) * ((Polynomial.derivative^[n] P).comp (-X)) := by
  induction n generalizing P with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      have hd : Polynomial.derivative (P.comp (-X))
          = ((-Polynomial.derivative P).comp (-X)) := by
        rw [Polynomial.derivative_comp, Polynomial.neg_comp]
        simp
      rw [hd, ih (-Polynomial.derivative P), iterate_derivative_neg, Polynomial.neg_comp,
        pow_succ]
      rw [Polynomial.C_mul]
      ring_nf
      simp [Polynomial.C_neg]

theorem iterate_derivative_comp_neg_eval (P : Polynomial ℂ) (n : ℕ) (w : ℂ) :
    (Polynomial.derivative^[n] (P.comp (-X))).eval (-w)
      = (-1) ^ n * (Polynomial.derivative^[n] P).eval w := by
  rw [iterate_derivative_comp_neg, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp]
  simp

/-- Polynomial jets under coefficient conjugation. -/
theorem iterate_derivative_map_conj_eval (P : Polynomial ℂ) (n : ℕ) (w : ℂ) :
    (Polynomial.derivative^[n] (P.map (starRingEnd ℂ))).eval ((starRingEnd ℂ) w)
      = (starRingEnd ℂ) ((Polynomial.derivative^[n] P).eval w) := by
  have hiter : Polynomial.derivative^[n] (P.map (starRingEnd ℂ))
      = (Polynomial.derivative^[n] P).map (starRingEnd ℂ) := by
    induction n generalizing P with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih,
          Polynomial.derivative_map]
  rw [hiter, Polynomial.eval_map, Polynomial.eval₂_hom]


end RHTower

end
