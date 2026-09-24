# RH as rigidity of a square degeneracy in the Estermann family

- **ID:** edr
- **Stage:** 5-failed
- **Type:** FALSIFIED (reframing, refuted by its own test)
- **Statement:** ζ's zeros are the pair-midpoints of the zeros of the family `D(·, a/q)`, in which ζ
  enters as the `a`-independent square `q^{1−2s}ζ(s)²`; RH should be read as rigidity of that
  degeneracy under the arithmetic deformation, not as positivity of a form built from `ξ'/ξ`.

## Diagnosis this reframing responds to

Every obstruction recorded in `universal-law-field/STATUS.md` from this lane is a failure of
individuation — atomwise zero arguments (CANNOT-323, CANNOT-383), per-modulus bounds (CANNOT-384),
termwise lag walls (route O), finite-band atom control (route Q). Every success was an exact
decomposition, never an estimate. Independently, the Euler product — the input that separates ζ from
the FE-only functions where RH is false (Davenport–Heilbronn, Epstein) — is used in all known
arguments only on `Re s ≥ 1`, because the Dirichlet series diverges inside the strip. No object in
the standard framing carries multiplicativity inward.

## The family and the degeneracy

Proved (`RHTower/EstermannPrincipalPart.lean`, this session):

```text
D(s, a/q) = q^{1−2s} ζ(s)² + q^{−s} R_a(s),
```

the `a`-dependence confined to the regular remainder — this is the character-sum collapse
`∑_{c mod q} expZeta(c/q, s) = q^{1−s} ζ(s)`, and the reason mean-zero twists annihilate the main
term (MUST-383 in the lane log). ζ occurs **squared**, so each simple zero `ρ` of ζ is a double zero
of the `a`-independent part, split by the deformation:

```text
D(s) ≈ q^{1−2ρ} c (s−ρ)² + q^{−ρ} R_a(ρ)  ⟹  s = ρ ± √( −q^{ρ−1} R_a(ρ)/c ).
```

So the family's zeros come in pairs with midpoint `ρ`. RH becomes a statement about pair-midpoints
of a deformation, and multiplicativity enters *inside* the strip through `R_a`'s dependence on `a`
and `q`, the completed family being entire there.

## First test — already run, and it does not close

If the functional equation transferred zeros between members, the midpoints would be pinned. It does
not:

```text
D(1−s, a/q) = 2 q^{2s−1} (2π)^{−2s} Γ(s)² [ D(s, ā/q) + cos(πs) D(s, −ā/q) ]
```

is a **sum** of two members, so zeros of one do not map to zeros of another. The classical
difficulty reappears in the new coordinates. What changes is its type: a transfer acting through the
involution pair `a ↦ ā`, `a ↦ −ā` is monodromy-shaped, not `ξ'/ξ`-shaped.

## Why it may still be the right frame

- Monodromy in a family plus a bootstrap is the only mechanism by which an RH has ever been proved
  (Deligne). The corpus's refuted arithmetic-symplectic descent failed for want of "a canonical
  square root"; this family supplies one canonically, since ζ enters as `ζ²`.
- It replaces "prove positivity of a form on `ξ'/ξ`" — which CANNOT-383 shows is one object in many
  coordinates — with a question about deformation of a degenerate member, where the unknowns are
  different.

## Falsification conditions

- The splitting map `a ↦ ε_a(ρ)` carries no multiplicative structure in `a` (then the Euler product
  still never enters the strip, and the reframing is empty).
- The pair-midpoint description fails beyond leading order in a way that destroys the identification
  of midpoints with ζ's zeros.
- The family's zero statistics are already known to be insensitive to RH (then this is a
  reformulation, not a reduction).

## First concrete step — done, and it came back positive

`RHTower/EstermannCharacterFactorization.lean` (axiom-clean, built, wired). For a prime modulus and
a non-principal `χ`:

```text
sum_char_estermannRegularPart :
  ∑_a χ⁻¹(a) · estermannRegularPart q a s
    = LFunction (𝓕 (χ⁻¹ ∘ neg)) s · ( q^s · LFunction χ s )
```

The twist enters `R_a` only through the dilation `c ↦ ac`; on a prime modulus that dilation is a
bijection of the nonzero residues, so averaging against `χ⁻¹` converts it into the value `χ(c)` and
the two factors separate. Supporting: `sum_char_expZeta` (the twisted exponential zeta is the
L-function of a discrete Fourier transform, via mathlib's `ZMod.LFunction_dft`) and
`sum_char_hurwitzZeta` (mathlib's `ZMod.LFunction` *is* the Hurwitz decomposition).

For primitive `χ` the DFT of `χ⁻¹` is a Gauss sum times `χ`, so the right-hand side is a Gauss-sum
multiple of `q^s L(s,χ)²`. **The splitting amplitudes are squares of Dirichlet L-functions weighted
by Gauss sums**, so the reframing is not empty: multiplicativity enters the strip, and it enters
through `τ(χ)`.

## What this makes of the frame

The family is the `(ZMod q)ˣ`-representation spanned by `{L(s,χ)² : χ mod q}`; every component is a
square, so the degeneracy is not special to ζ; `ζ²` is the invariant (principal) component; the
functional equation acts by the involution pair `χ ↦ χ̄`, `χ ↦ χ(−1)χ̄`; and the component-mixing
weights are Gauss sums, whose modulus `√q` is the finite-field Riemann hypothesis — a theorem.

So in this frame the *proved* RH acts on the *unproved* one exactly through the mixing of isotypic
components. That is the content of the reframing, and its value is decided by one question:

**does the component mixing produce cancellation *between* components?** CANNOT-384 shows that
cancellation, not bounds, is what the lane requires; per-component estimates are known to be
insufficient. If the mixing is cancellation-free the frame is a restatement.

## Log
- 2026-09-24 — created as a reframing attempt, with its first test run and reported as not closing.


## FALSIFIED — the character action is diagonal (2026-09-24)

**Exact killing computation.** Apply `∑_a χ⁻¹(a)` to the family's functional equation
`D(1−s, a/q) = A(s)[D(s, a⁻¹/q) + cos(πs) D(s, −a⁻¹/q)]` and reindex `b = a⁻¹`, so that
`χ⁻¹(a) = χ(b)`. Writing `C_χ(s) = ∑_a χ⁻¹(a) D(s, a/q)`:

```text
C_χ(1−s) = A(s) · (1 + χ(−1) cos(πs)) · C_χ̄(s).
```

The functional equation pairs `χ` with `χ̄` and never mixes distinct characters. Together with
`sum_char_estermannRegularPart` — each component *is* an L-square — the family decomposes
completely into independent Dirichlet L-functions. `ζ²` is the principal component and GRH for each
`χ` is the others; the Gauss sums sit **inside** components, not between them.

So the falsification condition stated above is met: the mixing is cancellation-free, and the frame
is a restatement of "RH for ζ together with GRH" — strictly worse than the starting point. The jump
attempt fails.

**Strongest positive survivor.** The decomposition itself, which is now a theorem
(`RHTower/EstermannCharacterFactorization.lean`, axiom-clean): for a prime modulus and non-principal
`χ`, the `χ`-component of the Estermann regular part is `L(𝓕(χ⁻¹∘neg), s) · q^s · L(χ, s)`, i.e. a
Gauss-sum multiple of `q^s L(s,χ)²`. This is the exact statement that the `a`-aspect carries no
mixing.

**New insight.** Because the `a`-aspect is diagonal, any inter-component cancellation must come from
the **`q`-aspect** — varying the modulus — which is exactly where Kloosterman sums arise as the
failure of the additive/multiplicative decomposition to remain diagonal across moduli. This is
independently consistent with CANNOT-384, which showed this lane requires cancellation between
moduli rather than bounds per modulus. Any future attempt on this family should deform `q`, not `a`.
