# Actual Mayer determinant and primitive modular orbits

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [three approaches, A](argon-three-orthogonal-rh-approaches.md).
- **Inputs:** [power traces](../3-formalized/gauss-mayer-countable-word-traces.md), [primitive modular coding](../3-formalized/gauss-mayer-modular-primitive-coding.md).

## Target

Let `D(w,z)` be the actual Mayer Fredholm determinant. Let `c` range over
nonempty primitive digit-pair cycles, with pair length `ℓ(c)` and expanding
matrix multiplier `λ_c>1`. Prove, initially for `Re w>1` and sufficiently
small `|z|`, the absolutely convergent identity

```text
D(w,z) D(w,−z) = ∏_c ∏_(m≥0) (1−z^(2ℓ(c)) λ_c^(−w−2m)).
```

Then establish convergence at `z=1` on `Re w>2`. The certified conjugacy and
root classification should identify these cycles with primitive positive-trace
hyperbolic integral determinant-one classes. Inverse classes remain distinct
unless the proved inverse-class criterion identifies them.

## Certified results and remaining gap

1. **Certified:** The actual signed determinant product equals its even-word
   trace exponential near zero, with absolute summation over all lengths and
   words. [Paper proof and Lean certificate](../3-formalized/gauss-mayer-even-word-determinant.md).
2. **Certified:** every nonempty pair word has unique primitive-cycle data
   `(c,r,i)`, with `r≥1`, `i<ℓ(c)`, and length `rℓ(c)`. Positive powers
   preserve minimal rotation period, so a repeated primitive word has exactly
   `ℓ(c)` distinct pair rotations. Actual even Gauss words correspond
   bijectively to nonempty pair words, with source length twice pair length.
   [Paper proof and seventeen production audits](../3-formalized/gauss-mayer-primitive-pair-cycle-multiplicities.md).
   Ordinary digit primitivity is incorrect.
3. **Source terms certified:** pair rotation preserves the expanding
   multiplier; repetition gives `λ(u^r)=λ(u)^r`. The actual fixed-point
   multiplier equals this matrix multiplier. The exact source bijection
   gives half-length `rℓ(c)` and literal trace term
   `z^(2rℓ(c))/(rℓ(c)) · (λ_c^r)^(−w)/(1−(λ_c^r)⁻²)`.
   [Paper proof and ten production audits](../3-formalized/gauss-mayer-primitive-orbit-words.md).

4. **Certified:** Exact Gauss-word probability gives geometric absolute trace
   decay for `Re w>2`. The even-word identity now holds throughout `|z|≤1`,
   including `z=1`; the full word series converges absolutely and the actual
   determinant has no spectral zero in this disk.
   [Continuation proof and Lean certificate](../3-formalized/gauss-mayer-unit-even-word-determinant.md).
5. **Certified:** finite rotation sums cancel `ℓ(c)` exactly, preserving
   absolute mass. The resulting primitive-cycle logarithm is
   `J(w,z)=Σ_c Σ_(r≥1) z^(2rℓ(c))/r · (λ_c^r)^(−w)/(1−(λ_c^r)⁻²)`.
   It converges absolutely and satisfies `D(w,z)D(w,−z)=exp(−J(w,z))`
   near zero for `Re w>1`, and throughout `|z|≤1` for `Re w>2`.
   [Paper proof and both production audits](../3-formalized/gauss-mayer-primitive-orbit-logarithm.md).
6. **Open:** expand `(1−λ_c^(−2r))⁻¹`, justify the logarithmic factor
   summation, and identify the convergent Euler product.

The local Hilbert–Schmidt exponential determinant is a convergent-series
representation only near zero. Its totalized exponential cannot replace the
global Fredholm determinant away from that domain.

## Certified source probability and decay

The bottom-row weight `P=1/[d(c+d)]` has total mass one over all words of
every fixed length. Its exact successor telescope and `0≤c≤d` give
`Σ d⁻²≤2`. Each digit pair doubles the denominator, so `d≥2^n` at length
`2n`. The actual expanding multiplier satisfies `λ≥d`.

For `Re w>2`, `q=exp(−(Re w−2)log 2)∈(0,1)` and the complete absolute
trace mass at length `2n+2` is at most `(8/3)q^(n+1)`.
[Paper proof and nine clean production audits](../3-formalized/gauss-mayer-word-probability-and-trace-decay.md).

## Scope

Primitive-cycle trace regrouping is certified on the source domains above.
The Euler product remains unproved. Geometric geodesic lengths, scattering
normalization, and critical-strip resonance exclusion remain separate gaps.
