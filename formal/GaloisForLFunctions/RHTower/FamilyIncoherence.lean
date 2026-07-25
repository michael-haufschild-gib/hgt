import GaloisForLFunctions.RHTower.ScaleCouplingObstruction

/-!
# The truncation family is incoherent, so the construction must be non-semiclassical

The construction side needs a family of box-truncated `xp` models with area `A(E) = E²/(2πe²)`.  For
the family to describe *one* spectrum, the low-lying eigenvalues must not move as the box grows.
They do.

**Monotonicity.**  The truncated operator is defined variationally on the box, and enlarging the box
enlarges the form domain, so by min–max every eigenvalue is nonincreasing in the area and the
counting function is nondecreasing.  The semiclassical count makes this explicit and strict:

```text
N(A,E) = (E/2π)(1 + log(A/E))
```

is **strictly increasing** in `A`, since `log` is.  Two different areas therefore give different
counts at the same energy, hence different spectra.

**Incoherence.**  A family `{H_{A(E)}}` whose members are required to share the zeros as spectrum
would have to satisfy `N(A(E₁), E) = N(A(E₂), E)` for energies `E` below both cutoffs.  Strict
monotonicity forbids it whenever `A(E₁) ≠ A(E₂)`, and `A` is strictly increasing.  So

> **No family of box-truncated `xp` models has a common spectrum.  The counting law can be matched at
> each energy by choosing the box, but the individual eigenvalues then move with the box, and no
> single operator emerges.**

That is exactly the status of the Berry–Keating model: a correct heuristic for the *density* of zeros
which does not produce the zeros themselves.  The obstruction is not the quality of the semiclassical
approximation; it is that the family is not coherent.

**Consequence.**  A genuine Hilbert–Pólya operator cannot arise as a limit of box-truncated `xp`
models.  It must be non-semiclassical — which is where the adelic construction lives, and there the
spectrum appears as absorption rather than as eigenvalues.  The classification is thereby complete
over all five families:

```text
read near σ = 1        zero-free regions        capped at 1/log log t
read interior          density estimates        bounds grow in T, never 0
read σ = ½             moments and mollifiers   proportions capped below 1
construct semiclassical                         family incoherent          (this file)
construct non-semiclassical                     the remaining target
```

This file formalizes the strict monotonicity of the count in the area and the resulting impossibility
of a common spectrum.
-/

open Real

noncomputable section

namespace RHTower

/-- **Strict monotonicity in the area.**  The semiclassical count is strictly increasing in the box
area, because `log` is. -/
theorem xpCount_strictMono_area {A₁ A₂ E : ℝ} (hA1 : 0 < A₁) (hA12 : A₁ < A₂) (hE : 0 < E) :
    xpCount A₁ E < xpCount A₂ E := by
  unfold xpCount
  have hfac : (0 : ℝ) < E / (2 * π) := by positivity
  have hdiv : A₁ / E < A₂ / E := by
    rw [div_lt_div_iff₀ hE hE]
    nlinarith [hA12, hE]
  have hlog : Real.log (A₁ / E) < Real.log (A₂ / E) :=
    Real.log_lt_log (by positivity) hdiv
  have : 1 + Real.log (A₁ / E) < 1 + Real.log (A₂ / E) := by linarith
  exact mul_lt_mul_of_pos_left this hfac

/-- **Incoherence.**  Two boxes of different areas cannot give the same count at a common energy, so
they cannot share a spectrum. -/
theorem no_common_spectrum {A₁ A₂ E : ℝ} (hA1 : 0 < A₁) (hA12 : A₁ < A₂) (hE : 0 < E)
    (hsame : xpCount A₁ E = xpCount A₂ E) : False := by
  have h := xpCount_strictMono_area hA1 hA12 hE
  rw [hsame] at h
  exact lt_irrefl _ h

/-- The required areas at two different energies are different, by strict monotonicity of the
required area. -/
theorem required_areas_differ {E₁ E₂ : ℝ} (h1 : 0 < E₁) (h12 : E₁ < E₂) :
    requiredArea E₁ ≠ requiredArea E₂ :=
  ne_of_lt (requiredArea_strictMono h1 h12)

/-- **The family is incoherent.**  Members indexed by different energies have different box areas,
hence different counts at any common energy, hence different spectra. -/
theorem family_incoherent {E₁ E₂ E : ℝ} (h1 : 0 < E₁) (h12 : E₁ < E₂) (hE : 0 < E)
    (hA : 0 < requiredArea E₁)
    (hsame : xpCount (requiredArea E₁) E = xpCount (requiredArea E₂) E) : False :=
  no_common_spectrum hA (requiredArea_strictMono h1 h12) hE hsame

/-- The positive statement that survives: the count can be matched at each energy separately, by
choosing the area there. -/
theorem pointwise_match {E : ℝ} (hE : 0 < E) :
    xpCount (requiredArea E) E = riemannCount E :=
  xpCount_eq_riemannCount hE (requiredArea_div hE)

end RHTower
