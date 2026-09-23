import GaloisForLFunctions.RHTower.ThreeFamilyClosure

/-!
# The construction side: an `xp` model must have a quadratically growing cutoff

The classification covers mechanisms that *read* `ζ`.  The remaining family does not read it at all:
it constructs an operator whose spectrum is the zero set.  The counting function pins the candidate
immediately — the zeros obey `N(T) = (T/2π)(log(T/2π) - 1) + O(log T)`, which is not a power law, so
no elliptic operator on a compact manifold can have this spectrum; the `log` factor is the
semiclassical signature of `xp`.

**The phase-space count.**  For the classical Hamiltonian `xp` restricted to the box `0 < x < X`,
`0 < p < P`, the area below energy `E` is

```text
Area{ xp < E } = ∫₀^X min(P, E/x) dx = E + E·log(XP/E)     (E < XP) ,
```

so the semiclassical count is `N(E) = (E/2π)(1 + log(XP/E))`.

**Matching forces a growing box.**  Equating with the Riemann count,

```text
1 + log(XP/E) = log(E/2π) - 1   ⟺   XP = E²/(2π e²) .
```

The phase-space cutoff must grow **quadratically** in the spectral parameter.  Conversely a *fixed*
box is impossible outright: with `XP = A` constant the semiclassical count is
`(E/2π)(1 + log A - log E)`, which becomes **negative** once `E > eA` — absurd for a counting
function.

> **No `xp`-type semiclassical model on a fixed phase-space region can carry the zeta spectrum.  The
> box must expand like `E²/(2πe²)`, so the object is a family indexed by the spectral parameter, not
> a single operator.**

That is the precise sense in which the Berry–Keating picture needs an energy-dependent
regularization, and it is consistent with the adelic construction producing an absorption spectrum
rather than a genuine discrete one.  It also matches the corpus's earlier result that a complex
quadruple is incompatible with any self-adjoint problem: the classification maps what such an
operator *would* imply, and this module maps what its semiclassical shadow *must* look like.

This file formalizes the phase-space count, the quadratic matching, and the impossibility of a fixed
box.
-/

open Real

noncomputable section

namespace RHTower

/-- The semiclassical count of `xp` below energy `E` in the box of area `A = XP`. -/
def xpCount (A E : ℝ) : ℝ := E / (2 * π) * (1 + Real.log (A / E))

/-- The Riemann counting law in the same normalization. -/
def riemannCount (E : ℝ) : ℝ := E / (2 * π) * (Real.log (E / (2 * π)) - 1)

/-- **The matching condition.**  The two counts agree exactly when `A = E²/(2πe²)`. -/
theorem xpCount_eq_riemannCount {A E : ℝ} (hE : 0 < E)
    (hmatch : A / E = E / (2 * π * Real.exp 2)) :
    xpCount A E = riemannCount E := by
  unfold xpCount riemannCount
  rw [hmatch]
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have he : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  have hsplit : Real.log (E / (2 * π * Real.exp 2))
      = Real.log (E / (2 * π)) - 2 := by
    rw [show E / (2 * π * Real.exp 2) = (E / (2 * π)) / Real.exp 2 by field_simp,
      Real.log_div (by positivity) (by positivity), Real.log_exp]
  rw [hsplit]
  ring

/-- The required box area: quadratic in the spectral parameter. -/
def requiredArea (E : ℝ) : ℝ := E ^ (2 : ℕ) / (2 * π * Real.exp 2)

/-- The matching condition in solved form. -/
theorem requiredArea_div {E : ℝ} (hE : 0 < E) :
    requiredArea E / E = E / (2 * π * Real.exp 2) := by
  unfold requiredArea
  field_simp

/-- **A fixed box is impossible.**  With constant area the semiclassical count becomes negative once
`E > eA`, which no counting function can do. -/
theorem fixed_box_negative {A E : ℝ} (hA : 0 < A) (hE : Real.exp 1 * A < E) :
    1 + Real.log (A / E) < 0 := by
  have hEpos : (0 : ℝ) < E := lt_trans (by positivity) hE
  have hlt : A / E < 1 / Real.exp 1 := by
    rw [div_lt_div_iff₀ hEpos (Real.exp_pos 1)]
    linarith [hE]
  have hpos : (0 : ℝ) < A / E := by positivity
  have hlog : Real.log (A / E) < Real.log (1 / Real.exp 1) := Real.log_lt_log hpos hlt
  have hval : Real.log (1 / Real.exp 1) = -1 := by
    rw [one_div, Real.log_inv, Real.log_exp]
  rw [hval] at hlog
  linarith

/-- Hence the count itself is negative there: a fixed phase-space region cannot carry the
spectrum. -/
theorem xpCount_neg_of_fixed {A E : ℝ} (hA : 0 < A) (hE : Real.exp 1 * A < E) :
    xpCount A E < 0 := by
  have hEpos : (0 : ℝ) < E := lt_trans (by positivity) hE
  have hneg := fixed_box_negative hA hE
  unfold xpCount
  have hfac : (0 : ℝ) < E / (2 * π) := by positivity
  exact mul_neg_of_pos_of_neg hfac hneg

/-- **The box must grow.**  The required area is strictly increasing in the spectral parameter, so
the construction is a family and not a single operator. -/
theorem requiredArea_strictMono {E₁ E₂ : ℝ} (h1 : 0 < E₁) (h12 : E₁ < E₂) :
    requiredArea E₁ < requiredArea E₂ := by
  unfold requiredArea
  have hden : (0 : ℝ) < 2 * π * Real.exp 2 := by positivity
  rw [div_lt_div_iff₀ hden hden]
  have hsq : E₁ ^ (2 : ℕ) < E₂ ^ (2 : ℕ) := by nlinarith [h1, h12]
  nlinarith [hsq, hden]

end RHTower
