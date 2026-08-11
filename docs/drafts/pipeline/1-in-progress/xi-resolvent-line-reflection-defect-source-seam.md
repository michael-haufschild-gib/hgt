# Xi resolvent line-reflection defect/source seam

- **ID:** `xi-resolvent-line-reflection-defect-source-seam`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / LEAN TARGET / CROSS-ROUTE CLASSIFICATION
- **Parents:** `XiResolventMassRigidity.lean`, `XiWeilLineConjHilbert.lean`,
  `CCMUniversalWeilSourceReconstruction.lean`, `rh-current-frontier-map.md`
- **Statement:** The Route-U imaginary resolvent mass is exactly one quarter of the squared
  antisymmetric line-reflection defect of the resolvent evaluation vector, and half the gap
  between its ordinary Hilbert norm square and its Xi--Weil quadratic value. Consequently Route
  U's quartic escape condition and the R/L same-carrier non-equivariant reflection defect are the
  same obstruction in two charts.

## Goal

Test whether the new quartic resolvent-mass rigidity can be bounded directly from the prime-side
explicit formula. Preserve the complete Xi divisor, multiplicity copies, and line reflection.

## Heavy conjecture loop

### C0 -- one-body explicit formula bounds the imaginary mass -- FAILED

Put

```text
u_X(q) = (alpha_q^2 + X)^(-1),
M(X)   = sum_q Im(u_X(q))^2.
```

The analytic resolvent trace controls `sum_q u_X(q)^k`. It does not control
`sum_q |u_X(q)|^2`, which couples each divisor copy to its line-reflected copy. The exact scalar
identity is

```text
2 M(X) = sum_q |u_X(q)|^2 - Re(sum_q u_X(q)^2).
```

The second term is a derivative of the Euler-ray response and has a prime--Gamma formula. The
first is non-equivariant and is not one holomorphic trace. Therefore Route-T large values cannot
be applied to `M(X)` without first constructing the missing reflected source carrier.

### C1 -- Hedenmalm anomaly supplies that reflected carrier -- FAILED

The integer-translation anomaly is nonzero on the source core but its Fourier--Laplace transform
is `q_n XiC`; it vanishes in the analytic divisor fibre. Its source-normal quotient survives only
in the essential-singular completion whose strict closed boundary descent is already RH-bearing.
An affine extension linearizes the exact Wess--Zumino cocycle but does not provide the missing
positive closed descent.

### C2 -- normalized translation is contractive on the divisor quotient -- FAILED

On unweighted source `L2`, normalized translation has norm `n^(-1/2)`. If the conormal character
`n^(-s)` descended contractively to a nonzero root fibre, it would force `Re(s) >= 1/2`, and
reflection would force equality. But point evaluation at a nonreal spectral point is not continuous
in that source norm. In the theta-weighted Hilbert space it is continuous, while raw translation is
unbounded. This is exactly the existing strict-completion wall, not a proof of it.

### C3 -- naive adelic `L2` supplies a unitary norm character -- FAILED

The corpus's Allcock--Vaaler/Kummer no-go already proves that bare adelic `L2` destroys closed
product-formula descent, while the centered half-Tate power action becomes scalar. The nontrivial
Xi spectrum must live in the Rost--Schmid coherence-defect quotient; the scalar Kummer line cannot
carry it.

### C4 -- exact line-reflection defect classification -- PROVED ON PAPER

Let `J` reindex `ell2(XiZeroCopy)` by critical-line reflection. The corpus proves

```text
u_X(lineConj q) = conj(u_X(q)).
```

Hence, coordinatewise,

```text
(u_X - J u_X)(q) = u_X(q) - conj(u_X(q)) = 2 i Im(u_X(q)).
```

Absolute summability of `u_X` and `||u_X|| <= 1` gives `u_X in ell2`. Summing squared norms yields

```text
||u_X - J u_X||_2^2 = 4 M(X).                       (1)
```

Since `J` is an isometry and the unconditional Xi--Weil Hilbert quadratic is
`Q(v)=Re inner(Jv,v)`, polarization gives

```text
||u_X - J u_X||_2^2
  = 2 ||u_X||_2^2 - 2 Q(u_X),
```

and therefore

```text
2 M(X) = ||u_X||_2^2 - Q(u_X).                       (2)
```

Equations `(1)`--`(2)` are unconditional. For `X >= 0`, the existing mass criterion then gives

```text
RH <-> u_X = J u_X <-> ||u_X - J u_X|| = 0.          (3)
```

The existing quartic escape theorem likewise becomes

```text
RH <-> (X+1)^4 ||u_X-Ju_X||^2 -> 0.                  (4)
```

Finally, universal continued-Cauchy reconstruction places both `u_X` and `J u_X` in the same
source-generated Hilbert closure. Thus `(1)` is the exact coefficient-faithful non-equivariant
same-carrier theorem needed before any source bound; it does not assert that the defect vanishes.

## No-go closure

- **Exact killing mechanism:** prime explicit formula sees the reflected Weil quadratic but not
  the ordinary norm square. Their gap is exactly the off-line mass.
- **Strongest positive survivor:** `(1)`--`(4)` identify Route-U escape, Xi--Weil reflection
  antisymmetry, and the R/L same-carrier producer as one literal defect.
- **New insight:** arithmetic work must bound an ordinary Hilbert norm relative to a reflected Weil
  quadratic on the same source-selected sequence. A bound on analytic resolvent moments alone
  cannot close RH.
- **RH status:** open. This theorem is a classification/bridge, not a producer.

## Novelty boundary

The identity `||v-Jv||^2 = 2||v||^2-2 Re inner(Jv,v)` for an involutive isometry is elementary
parent Hilbert-space theory. No novelty is claimed for it. Candidate corpus-new content is its
multiplicity-exact Xi resolvent specialization and the resulting proof that Route U's mass wall is
literally the same non-equivariant source-carrier wall already isolated by Routes R and L.

## Lean target

`formal/GaloisForLFunctions/RHTower/XiResolventLineReflectionDefect.lean`

## Gates

- [x] internal corpus audit
- [x] external parent-theory/Weil-Hilbert boundary audit
- [x] paper proof dependency-closed
- [ ] Lean module and targeted elaboration
- [ ] targeted module build and axiom audit
- [ ] source-side uniform defect bound

## Log

- 2026-08-11 -- C0--C3 falsified; C4 dependency-closed on paper.
