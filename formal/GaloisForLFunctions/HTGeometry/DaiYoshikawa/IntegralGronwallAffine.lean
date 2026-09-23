import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Grönwall's inequality with an affine source

Lemma 6.3 of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues of the
Laplacian* (arXiv:2509.06151v2), estimates the deviation of the flow differential
`Ξ(η) = (Φ_η)_{*}` from its initial value.  The estimate obtained there is the Volterra bound

```text
ψ(η) ≤ a η + b ∫_0^η ψ(σ) dσ ,
```

with `a = N K`, `b = N`, and the conclusion quoted is `ψ(η) ≤ K (e^{Nη} − 1)`.  That is the exact
solution of the associated linear equation `Z' = b Z + a η`, `Z(0)=0`, not the constant-source
Grönwall bound: the source is affine, not constant, and the sharp envelope is `(a/b)(e^{bη} − 1)`.

The proof is the standard one.  With `V(η) = ∫_0^η ψ` and `Z` the primitive of `bZ + aη`, the
function `(V − Z) e^{−bη}` starts at `0` and has nonpositive derivative, so `V ≤ Z`; feeding that
back into the hypothesis gives the envelope.
-/

open Set intervalIntegral MeasureTheory

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

/-- **Grönwall's inequality, integral form, affine source.**

A continuous function obeying `u(x) ≤ a x + b ∫_0^x u` on `[0,T]` with `b > 0` obeys
`u(x) ≤ (a/b)(e^{bx} − 1)` there. -/
theorem le_affine_gronwall_of_volterra_bound
    {T a b : ℝ} (hb : 0 < b) {u : ℝ → ℝ} (hu : Continuous u)
    (hbd : ∀ x ∈ Icc (0 : ℝ) T, u x ≤ a * x + b * ∫ σ in (0 : ℝ)..x, u σ) :
    ∀ x ∈ Icc (0 : ℝ) T, u x ≤ a / b * (Real.exp (b * x) - 1) := by
  set V : ℝ → ℝ := fun x => ∫ σ in (0 : ℝ)..x, u σ with hVdef
  have hVd : ∀ x : ℝ, HasDerivAt V (u x) x := by
    intro x
    exact intervalIntegral.integral_hasDerivAt_right (hu.intervalIntegrable 0 x)
      (hu.stronglyMeasurableAtFilter _ _) hu.continuousAt
  set Z : ℝ → ℝ := fun x => a / b ^ (2 : ℕ) * (Real.exp (b * x) - 1) - a / b * x with hZdef
  have hlin : ∀ x : ℝ, HasDerivAt (fun y : ℝ => b * y) b x := by
    intro x
    simpa using (hasDerivAt_id x).const_mul b
  have hexp : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Real.exp (b * y)) (Real.exp (b * x) * b) x :=
    fun x => (hlin x).exp
  have hZd : ∀ x : ℝ, HasDerivAt Z (a / b * Real.exp (b * x) - a / b) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => a / b ^ (2 : ℕ) * (Real.exp (b * y) - 1))
        (a / b ^ (2 : ℕ) * (Real.exp (b * x) * b)) x :=
      ((hexp x).sub_const 1).const_mul _
    have h2 : HasDerivAt (fun y : ℝ => a / b * y) (a / b) x := by
      simpa using (hasDerivAt_id x).const_mul (a / b)
    have h3 := h1.sub h2
    have heq : a / b ^ (2 : ℕ) * (Real.exp (b * x) * b) - a / b
        = a / b * Real.exp (b * x) - a / b := by
      field_simp
    rwa [heq] at h3
  set H : ℝ → ℝ := fun x => (V x - Z x) * Real.exp (-(b * x)) with hHdef
  have hnegexp : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => Real.exp (-(b * y))) (Real.exp (-(b * x)) * -b) x := by
    intro x
    exact ((hlin x).neg).exp
  have hHd : ∀ x : ℝ, HasDerivAt H
      ((u x - (a / b * Real.exp (b * x) - a / b)) * Real.exp (-(b * x))
        + (V x - Z x) * (Real.exp (-(b * x)) * -b)) x :=
    fun x => ((hVd x).sub (hZd x)).mul (hnegexp x)
  have hHdiff : Differentiable ℝ H := fun x => (hHd x).differentiableAt
  have hnonpos : ∀ x ∈ interior (Icc (0 : ℝ) T), deriv H x ≤ 0 := by
    intro x hx
    have hxmem : x ∈ Icc (0 : ℝ) T := interior_subset hx
    rw [(hHd x).deriv]
    have hle : u x ≤ a * x + b * V x := hbd x hxmem
    have hZval : b * Z x = a / b * Real.exp (b * x) - a / b - a * x := by
      rw [hZdef]
      field_simp
    have hpos : (0 : ℝ) < Real.exp (-(b * x)) := Real.exp_pos _
    nlinarith [hle, hpos, hZval]
  have hanti : AntitoneOn H (Icc (0 : ℝ) T) :=
    antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hHdiff.continuous.continuousOn
      hHdiff.differentiableOn hnonpos
  intro x hx
  have hH0 : H 0 = 0 := by
    rw [hHdef, hVdef, hZdef]
    simp
  have hVZ : V x ≤ Z x := by
    have hHle : H x ≤ 0 := by
      rw [← hH0]
      exact hanti (left_mem_Icc.mpr (le_trans hx.1 hx.2)) hx hx.1
    have hpos : (0 : ℝ) < Real.exp (-(b * x)) := Real.exp_pos _
    nlinarith [hHle, hpos]
  have hZval : b * Z x = a / b * Real.exp (b * x) - a / b - a * x := by
    rw [hZdef]
    field_simp
  have hfinal : u x ≤ a * x + b * Z x := by
    have := hbd x hx
    nlinarith [this, hVZ, hb]
  rw [hZval] at hfinal
  have hrw : a / b * (Real.exp (b * x) - 1) = a / b * Real.exp (b * x) - a / b := by ring
  rw [hrw]
  linarith

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
