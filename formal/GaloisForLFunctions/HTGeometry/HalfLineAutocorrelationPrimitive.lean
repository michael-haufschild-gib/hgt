import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Half-line autocorrelation controlled by an exponential primitive

For a half-line source `R`, the growing branch of its polar autocorrelation can be dangerous:
the kernel contains `exp(h / 2)`.  Oscillation in `R` removes that growth when the weighted source
`exp(s / 2) R(s)` has a bounded primitive.  This file proves the exact Fubini identity carrying
that cancellation and the corresponding absolute bound.

The theorem is source-independent.  Its intended RHTower consumer is the constrained radial
prolate tail, whose bounded primitive is supplied by its Bessel/Liouville--Green phase.
-/

open Real MeasureTheory Set

namespace HTGeometry

noncomputable section

/-- Positive-lag autocorrelation of a real source on the positive half-line. -/
def halfLineAutocorrelation (R : ℝ → ℝ) (h : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), R (s + h) * R s

/-- Primitive of the growing half-density branch `exp(s/2) R(s)`. -/
def halfLineExpPrimitive (R : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, Real.exp (s / 2) * R s

/-- **Half-line primitive/autocorrelation identity.**  Integrating the growing polar branch of
the autocorrelation over a finite lag interval is exactly the pairing of the decaying source
with an increment of the growing weighted primitive.

The product-integrability hypothesis is the natural Fubini condition.  Local interval
integrability is separated because it is precisely what identifies the translated inner integral
with a primitive increment. -/
theorem integral_exp_half_mul_halfLineAutocorrelation_eq_primitive
    (R : ℝ → ℝ) {H : ℝ} (hH : 0 ≤ H)
    (hlocal : ∀ a b : ℝ,
      IntervalIntegrable (fun t : ℝ => Real.exp (t / 2) * R t) volume a b)
    (hprod : Integrable
      (Function.uncurry (fun h s : ℝ =>
        Real.exp (h / 2) * R (s + h) * R s))
      ((volume.restrict (Ioc (0 : ℝ) H)).prod
        (volume.restrict (Ioi (0 : ℝ))))) :
    (∫ h in Ioc (0 : ℝ) H,
        Real.exp (h / 2) * halfLineAutocorrelation R h) =
      ∫ s in Ioi (0 : ℝ),
        (Real.exp (-s / 2) * R s) *
          (halfLineExpPrimitive R (s + H) - halfLineExpPrimitive R s) := by
  let μH : Measure ℝ := volume.restrict (Ioc (0 : ℝ) H)
  let μp : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let K : ℝ → ℝ → ℝ := fun h s => Real.exp (h / 2) * R (s + h) * R s
  have hswap := integral_integral_swap (f := K) hprod
  have hleft :
      (∫ h, (∫ s, K h s ∂μp) ∂μH) =
        ∫ h in Ioc (0 : ℝ) H,
          Real.exp (h / 2) * halfLineAutocorrelation R h := by
    rw [show μH = volume.restrict (Ioc (0 : ℝ) H) by rfl]
    apply setIntegral_congr_ae measurableSet_Ioc
    filter_upwards with h
    rw [show μp = volume.restrict (Ioi (0 : ℝ)) by rfl]
    rw [halfLineAutocorrelation]
    dsimp [K]
    have hfac :
        (fun s : ℝ => Real.exp (h / 2) * R (s + h) * R s) =
          fun s => Real.exp (h / 2) * (R (s + h) * R s) := by
      funext s
      ring_nf
    rw [hfac, integral_const_mul]
    intro _
    rfl
  rw [hleft] at hswap
  rw [hswap]
  apply setIntegral_congr_ae measurableSet_Ioi
  filter_upwards with s
  intro hs
  dsimp [K]
  have hshift :
      (∫ h in Ioc (0 : ℝ) H, Real.exp (h / 2) * R (s + h)) =
        Real.exp (-s / 2) *
          (halfLineExpPrimitive R (s + H) - halfLineExpPrimitive R s) := by
    rw [← intervalIntegral.integral_of_le hH]
    have hcomp := intervalIntegral.integral_comp_add_right
      (fun t : ℝ => Real.exp (t / 2) * R t) s (a := 0) (b := H)
    have hfac :
        (fun h : ℝ => Real.exp (h / 2) * R (s + h)) =
          fun h => Real.exp (-s / 2) *
            (Real.exp ((h + s) / 2) * R (h + s)) := by
      funext h
      rw [show h / 2 = -s / 2 + (h + s) / 2 by ring_nf, Real.exp_add]
      ring_nf
    rw [hfac, intervalIntegral.integral_const_mul]
    have hcomp' :
        (∫ h in (0 : ℝ)..H, Real.exp ((h + s) / 2) * R (h + s)) =
          ∫ t in s..s + H, Real.exp (t / 2) * R t := by
      simpa [add_comm] using hcomp
    rw [hcomp']
    have h0s := hlocal 0 s
    have hsH := hlocal s (s + H)
    have hprim :
        (∫ t in s..s + H, Real.exp (t / 2) * R t) =
          halfLineExpPrimitive R (s + H) - halfLineExpPrimitive R s := by
      rw [halfLineExpPrimitive, halfLineExpPrimitive,
        ← intervalIntegral.integral_add_adjacent_intervals h0s hsH]
      ring_nf
    rw [hprim]
  calc
    (∫ h in Ioc (0 : ℝ) H,
        Real.exp (h / 2) * R (s + h) * R s) =
        (∫ h in Ioc (0 : ℝ) H,
          Real.exp (h / 2) * R (s + h)) * R s := by
            rw [← integral_mul_const]
    _ = (Real.exp (-s / 2) * R s) *
          (halfLineExpPrimitive R (s + H) - halfLineExpPrimitive R s) := by
      rw [hshift]
      ring_nf

/-- A uniform bound on the weighted primitive turns its increment pairing into an explicit
`L¹` bound.  Combined with
`integral_exp_half_mul_halfLineAutocorrelation_eq_primitive`, this controls the growing polar
branch without taking absolute values before the oscillatory primitive is formed. -/
theorem abs_integral_mul_primitive_sub_le
    (R A : ℝ → ℝ) {H M : ℝ} (hH : 0 ≤ H)
    (hA : ∀ t, 0 ≤ t → |A t| ≤ M)
    (hG : IntegrableOn (fun s : ℝ => Real.exp (-s / 2) * R s) (Ioi 0))
    (hT : IntegrableOn (fun s : ℝ =>
      (Real.exp (-s / 2) * R s) * (A (s + H) - A s)) (Ioi 0)) :
    |∫ s in Ioi (0 : ℝ),
        (Real.exp (-s / 2) * R s) * (A (s + H) - A s)| ≤
      2 * M * ∫ s in Ioi (0 : ℝ), |Real.exp (-s / 2) * R s| := by
  have hdom : IntegrableOn
      (fun s : ℝ => 2 * M * |Real.exp (-s / 2) * R s|) (Ioi 0) := by
    exact hG.abs.const_mul (2 * M)
  calc
    |∫ s in Ioi (0 : ℝ),
        (Real.exp (-s / 2) * R s) * (A (s + H) - A s)| ≤
        ∫ s in Ioi (0 : ℝ),
          |(Real.exp (-s / 2) * R s) * (A (s + H) - A s)| := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm
          (μ := volume.restrict (Ioi (0 : ℝ)))
          (fun s : ℝ =>
            (Real.exp (-s / 2) * R s) * (A (s + H) - A s)))
    _ ≤ ∫ s in Ioi (0 : ℝ),
          2 * M * |Real.exp (-s / 2) * R s| := by
      refine integral_mono_ae hT.abs hdom ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      rw [abs_mul]
      have hs0 : 0 ≤ s := le_of_lt hs
      have hsH : 0 ≤ s + H := add_nonneg hs0 hH
      have hsub : |A (s + H) - A s| ≤ 2 * M := by
        calc
          |A (s + H) - A s| ≤ |A (s + H)| + |A s| := abs_sub _ _
          _ ≤ M + M := add_le_add (hA _ hsH) (hA _ hs0)
          _ = 2 * M := by ring_nf
      nlinarith [abs_nonneg (Real.exp (-s / 2) * R s)]
    _ = 2 * M * ∫ s in Ioi (0 : ℝ),
          |Real.exp (-s / 2) * R s| := by
      rw [integral_const_mul]

end

end HTGeometry
