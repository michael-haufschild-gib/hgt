import GaloisForLFunctions.RHTower.FiniteHermiteCRT
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Finite critical-point interpolation by polynomial gauge

At finitely many distinct regular points of an analytic function, one polynomial multiplier can
force the derivative of the product to vanish simultaneously.  The load-bearing step is the
existing finite Hermite CRT: prescribe multiplier value `1` and derivative `-F'/F` at every point.
The product rule then gives derivative zero without making any selected point a zero of the
multiplier.

The final theorem preserves the sign and Schwarz involutions.  It is the finite algebraic
certificate behind the paper-level statement that critical-point geometry is not intrinsic to an
unpointed differential field.  This file proves only the exact interpolation theorem.  It does not
formalize Speiser's criterion, hypertranscendence, generated differential fields, entire order, or
the Riemann hypothesis.
-/

open Polynomial Function

namespace RHTower

noncomputable section

/-- **Finite critical-packet interpolation.**  Given distinct points, nonzero function values, and
prescribed derivative values, one polynomial has value `1` at every point and makes the formal
product-rule derivative vanish there. -/
theorem exists_polynomial_critical_packet
    {ι : Type*} [Finite ι]
    (w : ι → ℂ) (hw : Function.Injective w)
    (f df : ι → ℂ) (hf : ∀ i, f i ≠ 0) :
    ∃ P : Polynomial ℂ, ∀ i,
      P.eval (w i) = 1 ∧
      (derivative P).eval (w i) * f i + P.eval (w i) * df i = 0 := by
  let target : ι → Polynomial ℂ := fun i =>
    C 1 + C (-df i / f i) * (X - C (w i))
  obtain ⟨P, hP⟩ :=
    exists_polynomial_iterateDerivative_eval_eq w hw (fun _ => 2) target
  refine ⟨P, fun i => ?_⟩
  have h0 := hP i 0 (by omega)
  have h1 := hP i 1 (by omega)
  have hP0 : P.eval (w i) = 1 := by
    simpa [target] using h0
  have hP1 : (derivative P).eval (w i) = -df i / f i := by
    simpa [target] using h1
  refine ⟨hP0, ?_⟩
  rw [hP0, hP1, div_mul_cancel₀ _ (hf i)]
  ring

/-- **Analytic product realization.**  If `F` has the prescribed derivatives at the packet and is
nonzero there, the interpolating polynomial makes every selected point a genuine critical point of
`P·F`, while retaining multiplier value `1` at the packet. -/
theorem exists_polynomial_mul_hasDerivAt_zero
    {ι : Type*} [Finite ι]
    (w : ι → ℂ) (hw : Function.Injective w)
    (F : ℂ → ℂ) (df : ι → ℂ)
    (hF : ∀ i, HasDerivAt F (df i) (w i))
    (hf : ∀ i, F (w i) ≠ 0) :
    ∃ P : Polynomial ℂ, ∀ i,
      P.eval (w i) = 1 ∧
      HasDerivAt (fun z => P.eval z * F z) 0 (w i) := by
  obtain ⟨P, hP⟩ := exists_polynomial_critical_packet w hw
    (fun i => F (w i)) df hf
  refine ⟨P, fun i => ⟨(hP i).1, ?_⟩⟩
  convert (Polynomial.hasDerivAt P (w i)).mul (hF i) using 1
  exact (hP i).2.symm

/-- **Sign/Schwarz-equivariant critical-packet interpolation.**  For a packet and value/derivative
data compatible with `z ↦ -z` and complex conjugation, the multiplier can be chosen globally even
and Schwarz-real while forcing the formal product derivative to vanish at every packet point. -/
theorem exists_real_even_polynomial_critical_packet
    {ι : Type*} [Finite ι]
    (negIdx conjIdx : ι ≃ ι)
    (w : ι → ℂ) (hw : Function.Injective w)
    (f df : ι → ℂ) (hf : ∀ i, f i ≠ 0)
    (hwneg : ∀ i, w (negIdx i) = -w i)
    (hwconj : ∀ i, w (conjIdx i) = (starRingEnd ℂ) (w i))
    (hfneg : ∀ i, f (negIdx i) = f i)
    (hdfneg : ∀ i, df (negIdx i) = -df i)
    (hfconj : ∀ i, f (conjIdx i) = (starRingEnd ℂ) (f i))
    (hdfconj : ∀ i, df (conjIdx i) = (starRingEnd ℂ) (df i)) :
    ∃ P : Polynomial ℂ,
      (∀ z, P.eval (-z) = P.eval z) ∧
      (∀ z, P.eval ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.eval z)) ∧
      ∀ i,
        P.eval (w i) = 1 ∧
        (derivative P).eval (w i) * f i + P.eval (w i) * df i = 0 := by
  let target : ι → Polynomial ℂ := fun i =>
    C 1 + C (-df i / f i) * (X - C (w i))
  obtain ⟨P, hPneg, hPconj, hP⟩ :=
    exists_real_even_polynomial_iterateDerivative_eval_eq
      negIdx conjIdx w hw (fun _ => 2) target
      hwneg hwconj (fun _ => rfl) (fun _ => rfl) (by
        intro i n hn
        interval_cases n
        · simp [target, hwneg, hfneg, hdfneg]
        · simp [target, hwneg, hfneg, hdfneg]
          ring) (by
        intro i n hn
        interval_cases n <;>
          simp [target, hwconj, hfconj, hdfconj, map_div₀])
  refine ⟨P, hPneg, hPconj, fun i => ?_⟩
  have h0 := hP i 0 (by omega)
  have h1 := hP i 1 (by omega)
  have hP0 : P.eval (w i) = 1 := by
    simpa [target] using h0
  have hP1 : (derivative P).eval (w i) = -df i / f i := by
    simpa [target] using h1
  refine ⟨hP0, ?_⟩
  rw [hP0, hP1, div_mul_cancel₀ _ (hf i)]
  ring

end

end RHTower
