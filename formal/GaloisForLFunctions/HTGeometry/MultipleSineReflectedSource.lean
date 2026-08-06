import GaloisForLFunctions.HTGeometry.BarnesSourceSeries

/-!
# The multiple sine as the reflection of the Barnes cone product

The corpus already builds the Barnes multiple gamma unconditionally: `barnesConeProduct` is the
genus-`N` Weierstrass product over the period cone, entire for periods in a half-plane, and its
logarithmic derivative is the Barnes source whose exact translation annihilator is the full ladder
`∏_j (T_j - 1)`.

The multiple sine is that object reflected:

```text
S_N(z) = Γ_N(z)⁻¹ · Γ_N(|ω| - z)^{(-1)^N},        |ω| = ∑_i ω_i,
```

and since `barnesConeProduct` is the *reciprocal* multiple gamma this reads
`S_N = B(z) · B(|ω| - z)^{(-1)^{N+1}}`.

This file constructs the reflection, the reflected cone product and the multiple sine from those
existing assets, and proves:

* the reflection rule `logDeriv (f ∘ reflect) = -(logDeriv f) ∘ reflect`, missing from mathlib;
* the reflected cone product is entire and nonvanishing off the reflected poles;
* the multiple sine's logarithmic derivative is `Ψ_N(z) - (-1)^{N+1} Ψ_N(|ω| - z)`;
* that source is *anti-invariant* under the reflection, up to the parity sign — the exact symmetry
  the one-face-layer reflection theorem is about.

Nothing is assumed: every statement is derived from the unconditional Barnes cone product.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex GaloisForLFunctions
open scoped BigOperators

noncomputable section

variable {ι : Type} [Fintype ι] [Nonempty ι]

/-! ### The reflection -/

/-- The reflection point `|ω| = ∑_i ω_i`. -/
def barnesReflectionPoint (ω : ι → ℂ) : ℂ := ∑ i, ω i

/-- The reflection `z ↦ |ω| - z`. -/
def barnesReflect (ω : ι → ℂ) (z : ℂ) : ℂ := barnesReflectionPoint ω - z

omit [Nonempty ι] in
@[simp] theorem barnesReflect_barnesReflect (ω : ι → ℂ) (z : ℂ) :
    barnesReflect ω (barnesReflect ω z) = z := by
  unfold barnesReflect
  ring

omit [Nonempty ι] in
theorem hasDerivAt_barnesReflect (ω : ι → ℂ) (z : ℂ) :
    HasDerivAt (barnesReflect ω) (-1) z := by
  unfold barnesReflect
  exact (hasDerivAt_id z).const_sub (barnesReflectionPoint ω)

omit [Nonempty ι] in
theorem deriv_barnesReflect (ω : ι → ℂ) (z : ℂ) :
    deriv (barnesReflect ω) z = -1 :=
  (hasDerivAt_barnesReflect ω z).deriv

omit [Nonempty ι] in
theorem differentiable_barnesReflect (ω : ι → ℂ) :
    Differentiable ℂ (barnesReflect ω) :=
  fun z => (hasDerivAt_barnesReflect ω z).differentiableAt

omit [Nonempty ι] in
/-- **Reflection rule for logarithmic derivatives.**  Precomposing with `z ↦ c - z` negates the
logarithmic derivative and evaluates it at the reflected point. -/
theorem logDeriv_comp_barnesReflect {f : ℂ → ℂ} (ω : ι → ℂ) {z : ℂ}
    (hf : DifferentiableAt ℂ f (barnesReflect ω z)) :
    logDeriv (fun w => f (barnesReflect ω w)) z = -logDeriv f (barnesReflect ω z) := by
  have hcomp : logDeriv (f ∘ barnesReflect ω) z =
      logDeriv f (barnesReflect ω z) * deriv (barnesReflect ω) z :=
    logDeriv_comp hf (differentiable_barnesReflect ω z)
  rw [deriv_barnesReflect] at hcomp
  simpa [Function.comp_def] using hcomp

/-! ### The reflected Barnes cone product -/

/-- The Barnes cone product read at the reflected point. -/
def barnesConeReflected (ω : ι → ℂ) (z : ℂ) : ℂ :=
  barnesConeProduct ω (barnesReflect ω z)

theorem differentiable_barnesConeReflected (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) :
    Differentiable ℂ (barnesConeReflected ω) :=
  (differentiable_barnesConeProduct ω hω).comp (differentiable_barnesReflect ω)

theorem barnesConeReflected_ne_zero (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) {z : ℂ}
    (hz : ∀ n : ι → ℕ, n ≠ 0 → conePeriod ω n + barnesReflect ω z ≠ 0) :
    barnesConeReflected ω z ≠ 0 :=
  barnesConeProduct_ne_zero_of_notMem_poles ω hω hz

theorem logDeriv_barnesConeReflected (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (z : ℂ) :
    logDeriv (barnesConeReflected ω) z =
      -logDeriv (barnesConeProduct ω) (barnesReflect ω z) :=
  logDeriv_comp_barnesReflect ω ((differentiable_barnesConeProduct ω hω) _)

/-! ### The multiple sine -/

variable (ι) in
/-- The reflection exponent `(-1)^{N+1}` of the multiple sine, `N` the number of periods. -/
def multipleSineExponent : ℤ := (-1) ^ (Fintype.card ι + 1)

omit [Nonempty ι] in
theorem multipleSineExponent_mul_self :
    (multipleSineExponent ι : ℂ) * (multipleSineExponent ι : ℂ) = 1 := by
  unfold multipleSineExponent
  push_cast
  rw [← mul_pow]
  norm_num

/-- The multiple sine, built by reflection from the Barnes cone product. -/
def multipleSine (ω : ι → ℂ) (z : ℂ) : ℂ :=
  barnesConeProduct ω z * barnesConeReflected ω z ^ (multipleSineExponent ι)

/-- The multiple-sine source `L_N = (log S_N)'`. -/
def multipleSineSource (ω : ι → ℂ) (z : ℂ) : ℂ :=
  logDeriv (barnesConeProduct ω) z -
    (multipleSineExponent ι : ℂ) *
      logDeriv (barnesConeProduct ω) (barnesReflect ω z)

/-- **The multiple-sine source is the logarithmic derivative of the multiple sine.** -/
theorem logDeriv_multipleSine (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) {z : ℂ}
    (h1 : barnesConeProduct ω z ≠ 0) (h2 : barnesConeReflected ω z ≠ 0) :
    logDeriv (multipleSine ω) z = multipleSineSource ω z := by
  have hzpow : logDeriv (fun w => barnesConeReflected ω w ^ (multipleSineExponent ι)) z =
      (multipleSineExponent ι : ℂ) * logDeriv (barnesConeReflected ω) z := by
    have hcomp : logDeriv ((fun x : ℂ => x ^ (multipleSineExponent ι)) ∘
          barnesConeReflected ω) z =
        logDeriv (fun x : ℂ => x ^ (multipleSineExponent ι)) (barnesConeReflected ω z) *
          deriv (barnesConeReflected ω) z :=
      logDeriv_comp (differentiableAt_zpow.2 (Or.inl h2))
        ((differentiable_barnesConeReflected ω hω) z)
    rw [logDeriv_zpow] at hcomp
    rw [show (fun w => barnesConeReflected ω w ^ (multipleSineExponent ι)) =
      (fun x : ℂ => x ^ (multipleSineExponent ι)) ∘ barnesConeReflected ω from rfl, hcomp,
      logDeriv_apply]
    field_simp
  have hne : barnesConeReflected ω z ^ (multipleSineExponent ι) ≠ 0 :=
    zpow_ne_zero _ h2
  have hmul : logDeriv (multipleSine ω) z =
      logDeriv (barnesConeProduct ω) z +
        logDeriv (fun w => barnesConeReflected ω w ^ (multipleSineExponent ι)) z :=
    logDeriv_mul z h1 hne ((differentiable_barnesConeProduct ω hω) z)
      ((differentiableAt_zpow.2 (Or.inl h2)).comp z
        ((differentiable_barnesConeReflected ω hω) z))
  rw [hmul, hzpow, logDeriv_barnesConeReflected ω hω]
  unfold multipleSineSource
  ring

/-! ### The reflection symmetry of the source -/

omit [Nonempty ι] in
/-- **The multiple-sine source is anti-invariant under the reflection**, up to the parity sign:
`L_N(|ω| - z) = -(-1)^{N+1} L_N(z)`.  This is the exact symmetry that the one-face-layer reflection
theorem describes on the annihilator side. -/
theorem multipleSineSource_barnesReflect (ω : ι → ℂ) (z : ℂ) :
    multipleSineSource ω (barnesReflect ω z) =
      -(multipleSineExponent ι : ℂ) * multipleSineSource ω z := by
  unfold multipleSineSource
  rw [barnesReflect_barnesReflect]
  have hsq := multipleSineExponent_mul_self (ι := ι)
  linear_combination
    (-logDeriv (barnesConeProduct ω) (barnesReflect ω z)) * hsq

end

end GaloisForLFunctions.HTGeometry
