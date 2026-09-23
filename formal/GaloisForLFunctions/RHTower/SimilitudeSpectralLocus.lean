import GaloisForLFunctions.RHTower.CompressionCannotSelfAdjointify

/-!
# Similitude of a definite pairing: the other a priori spectral constraint

Entries 24 and 25 leave one requirement: a source of spectral constraint that is not derived from
zeta.  Self-adjointness is one such source, and no compression scheme manufactures it.  There is
exactly one other structure known to constrain a spectrum a priori, and it is the mechanism by which
the function-field Riemann hypothesis is a **theorem**.

**Weil's linear-algebra core.**  In the function-field case one has a finite-dimensional space with a
nondegenerate pairing (Poincaré duality), definite on primitive parts (hard Lefschetz), and a
Frobenius `F` that scales the pairing by `q`.  Everything geometric is used to produce that
configuration; once it is available, the conclusion is two lines:

```text
F x = λ x ,   ‖F x‖² = q‖x‖²      ⟹      ‖λ‖² ‖x‖² = q ‖x‖²      ⟹      ‖λ‖ = √q .
```

> **A similitude of a definite pairing confines its whole spectrum to a circle, exactly as a
> self-adjoint operator confines it to a line.  It is a second, independent a priori source — and in
> logarithmic coordinates the circle `|λ| = √q` is a line, so it feeds the same connectors.**

**It relaxes, like self-adjointness.**  If the pairing is scaled only approximately,
`| ‖F x‖² - q‖x‖² | ≤ δ‖x‖²`, then `| ‖λ‖² - q | ≤ δ`, hence `| ‖λ‖ - √q | ≤ δ/√q`: the spectrum
concentrates on the circle at rate `δ/√q`.  Combined with the asymptotic criterion, an
*approximately* similitudinous family is as good as an exact one.

**What the corpus does not have.**  A search of this development finds no étale cohomology, no
Frobenius action, and no Poincaré duality: the geometric machinery that produces the configuration
above is absent, and Mathlib does not supply it.  What is recorded here is therefore the target
shape, stated so that any future construction can be checked against it, together with the two-line
core and its stability.

This file formalizes the similitude spectral locus, its approximate form, and the resulting
concentration estimate.
-/

open Filter Topology

noncomputable section

namespace RHTower

section Similitude

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- **Similitude spectral locus.**  If `F` scales norms by `√q` and `λ` is an eigenvalue, then
`‖λ‖² = q`: the whole spectrum lies on one circle. -/
theorem similitude_eigenvalue_normSq {F : V → V} {q : ℝ} {lam : ℂ} {x : V}
    (hx : x ≠ 0) (hsim : ‖F x‖ ^ (2 : ℕ) = q * ‖x‖ ^ (2 : ℕ)) (heig : F x = lam • x) :
    ‖lam‖ ^ (2 : ℕ) = q := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hFx : ‖F x‖ = ‖lam‖ * ‖x‖ := by rw [heig, norm_smul]
  rw [hFx] at hsim
  have hsq : (0:ℝ) < ‖x‖ ^ (2 : ℕ) := by positivity
  have hstep : ‖lam‖ ^ (2 : ℕ) * ‖x‖ ^ (2 : ℕ) = q * ‖x‖ ^ (2 : ℕ) := by rw [← hsim]; ring
  exact mul_right_cancel₀ (ne_of_gt hsq) hstep

/-- **Approximate similitude.**  A pairing scaled to within `δ` confines eigenvalue moduli to within
`δ` of `q` in square. -/
theorem approx_similitude_eigenvalue_normSq {F : V → V} {q δ : ℝ} {lam : ℂ} {x : V}
    (hx : x ≠ 0) (hsim : |‖F x‖ ^ (2 : ℕ) - q * ‖x‖ ^ (2 : ℕ)| ≤ δ * ‖x‖ ^ (2 : ℕ))
    (heig : F x = lam • x) :
    |‖lam‖ ^ (2 : ℕ) - q| ≤ δ := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hsq : (0:ℝ) < ‖x‖ ^ (2 : ℕ) := by positivity
  have hFx : ‖F x‖ = ‖lam‖ * ‖x‖ := by rw [heig, norm_smul]
  rw [hFx] at hsim
  have hfac : (‖lam‖ * ‖x‖) ^ (2 : ℕ) - q * ‖x‖ ^ (2 : ℕ) = (‖lam‖ ^ (2 : ℕ) - q) * ‖x‖ ^ (2 : ℕ) := by ring
  rw [hfac, abs_mul, abs_of_pos hsq] at hsim
  exact le_of_mul_le_mul_right (by linarith) hsq

end Similitude

/-- **Concentration on the circle.**  From `|‖λ‖² - q| ≤ δ` and `q > 0` one gets
`|‖λ‖ - √q| ≤ δ/√q`: the spectrum concentrates on the circle of radius `√q` at rate `δ/√q`. -/
theorem modulus_near_sqrt {m q δ : ℝ} (hm : 0 ≤ m) (hq : 0 < q)
    (h : |m ^ (2 : ℕ) - q| ≤ δ) : |m - Real.sqrt q| ≤ δ / Real.sqrt q := by
  have hsq : Real.sqrt q > 0 := Real.sqrt_pos.mpr hq
  have hsqsq : Real.sqrt q ^ (2 : ℕ) = q := Real.sq_sqrt (le_of_lt hq)
  have hfac : m ^ (2 : ℕ) - q = (m - Real.sqrt q) * (m + Real.sqrt q) := by
    have hexp : (m - Real.sqrt q) * (m + Real.sqrt q) = m ^ (2 : ℕ) - Real.sqrt q ^ (2 : ℕ) := by ring
    rw [hexp, hsqsq]
  rw [hfac, abs_mul] at h
  have hsum : Real.sqrt q ≤ |m + Real.sqrt q| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  rw [le_div_iff₀ hsq]
  calc |m - Real.sqrt q| * Real.sqrt q
      ≤ |m - Real.sqrt q| * |m + Real.sqrt q| := by
        exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ ≤ δ := h

/-- **The circle is a line in logarithmic coordinates.**  A modulus condition `‖λ‖ = √q` is the
statement that `log λ` has fixed real part, so a similitude source feeds the same criteria as a
self-adjoint one after the logarithmic change of variable. -/
theorem similitude_locus_is_a_line {m q : ℝ} (_hq : 0 < q) (h : m ^ (2 : ℕ) = q) (hm : 0 ≤ m) :
    m = Real.sqrt q := by
  rw [← h]
  exact (Real.sqrt_sq hm).symm

/-- **Exact similitude is the `δ = 0` case of the approximate one.** -/
theorem exact_is_approx {m q : ℝ} (h : m ^ (2 : ℕ) = q) : |m ^ (2 : ℕ) - q| ≤ 0 := by
  rw [h]; simp

end RHTower
