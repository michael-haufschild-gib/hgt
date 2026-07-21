# Universal composite swap-bulk orientation

- **ID:** `theta-likelihood-universal-composite-swap-orientation`
- **Stage:** 5-failed
- **Type:** `[FALSIFIED] [UNCONDITIONAL] [NO RH CLAIM]`
- **Parent:**
  `../3-formalized/new_scientific_knowledge/theta-likelihood-swap-bulk-arithmetic-stratification.md`
- **Statement:** The proposed extension
  `Im(Sigma'_k(B,D;z) conjugate(Sigma_k(B,D;z))) <= 0` from prime shells to every composite
  shell in the closed nonnegative temperature quadrant is false already for every prime square.

## Candidate

For the leg-exchange invariant likelihood shell

```text
Sigma_k(B,D;z)=sum_(nm=k)
  [S_n(B)S_m(D)+S_n(D)S_m(B)] exp(i(log n-log m)z/2),
```

the prime-shell theorem proves strict negative current throughout the upper half-plane whenever
`B,D>=0` and `B+D>0`.  The candidate was that composite residuals retain weakly nonpositive
current, which would have supplied a direct bulk orientation law without deleting composite
coupling.

## Exact refutation

Let `p` be prime, `lambda=log p`, and `k=p^2`.  Its complete factor packet consists of

```text
(1,p^2), (p,p), (p^2,1).
```

Put

```text
E_p(B,D)=B S_(p^2)(D)+D S_(p^2)(B),
C_p(B,D)=2 S_p(B)S_p(D).
```

The two endpoint coefficients both equal `E_p`; the central coefficient is `C_p`; their
rapidities are `-lambda,0,+lambda`.  Hence

```text
Sigma_(p^2)(B,D;z)
  = E_p(B,D)[exp(-i lambda z)+exp(i lambda z)] + C_p(B,D).
```

At the reflection wall `z=pi/lambda+i y`, with `y>0`, this gives exactly

```text
Sigma = C_p - 2 E_p cosh(lambda y),
Sigma' = 2 i lambda E_p sinh(lambda y),
J = Im(Sigma' conjugate(Sigma))
  = 2 lambda E_p sinh(lambda y)
      [C_p-2 E_p cosh(lambda y)].                       (1)
```

On the face `D=0`, write `R_n=S_n(0)`.  Then

```text
E_p(B,0)=B R_(p^2),
C_p(B,0)=2 S_p(B)R_p,
J(B,0)/B
  =4 lambda R_(p^2)sinh(lambda y)
      [S_p(B)R_p-B R_(p^2)cosh(lambda y)].              (2)
```

As `B -> 0+`, the right side tends to

```text
4 lambda R_(p^2)sinh(lambda y) R_p^2 > 0.               (3)
```

Continuity therefore makes `J(B,0)>0` for all sufficiently small positive `B`.  This contradicts
the proposed nonpositive composite orientation on every prime-square shell, without numerical
evaluation or any RH assumption.

## No-go closure

- **Exact killing theorem/mechanism:** Prime squares contain a zero-rapidity diagonal mode.  It
  contributes to shell value but not derivative.  Interference with endpoint derivative produces
  formula `(1)`, whose sign is not fixed.
- **Strongest positive survivor:** Exact prime-square sign-wall classification, strictly positive
  first conormal residue `(3)`, and strict negative orientation after subtracting exactly the
  zero-rapidity diagonal amplitude; see
  `../3-formalized/new_scientific_knowledge/theta-likelihood-prime-square-conormal-sign-wall.md`.
- **New insight:** Composite corner mass is not merely a retained coupling witness.  Square-diagonal
  mass is the first orientation defect.  Removing exactly that stationary amplitude restores
  strict reflection-wall orientation for every prime square, so diagonal renormalization is now
  an exact viable mechanism rather than a guess.  A single global sign law for raw swap bulk
  cannot work.
- **Status:** Internal corpus audit found no existing theorem for this likelihood carrier.  Primary
  literature audit found only parent theories, not formulas `(1)`--`(3)`.  Survivor has a
  dependency-closed paper proof and an exact Lean formalization in
  `ThetaCuspLikelihoodPrimeSquareSignWall.lean`.

## Anti-theatre gate

- No estimate, truncation, zero table, or floating-point evaluation is used.
- Refutation holds for every prime `p` and every wall height `y>0`.
- Failure is converted into an exact classifier and representation constraint.
- This does not disprove RH; it disproves one proposed route from shell orientation to RH.

## Log

- 2026-07-21 — Candidate attacked at first composite square stratum and falsified exactly.
- 2026-07-21 — Positive conormal sign-wall survivor extracted for paper proof and Lean.
- 2026-07-21 — Survivor formalized; failure now closes with exact positive witnesses on every
  prime-square shell.
