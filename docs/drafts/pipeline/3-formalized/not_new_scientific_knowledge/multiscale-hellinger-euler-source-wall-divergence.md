# Multiscale Hellinger Euler-source wall divergence

- **ID:** `multiscale-hellinger-euler-source-wall-divergence`
- **Stage:** 3-formalized
- **Type:** FALSIFIED SOURCE ROUTE / THEOREM (Lean) / POSITIVE NO-GO SURVIVOR
- **Source:** `../../1-in-progress/zeta23-beyond-bandwidth-one-proportion.md`
- **Statement:** The full logarithmic-scale Hellinger diagonal on the balanced primitive Euler
  source is exactly `log(9/8)` times its von Mangoldt prime-power weight and is nonsummable.
- **Formal module:**
  `formal/GaloisForLFunctions/RHTower/XiWardMultiscaleEulerSourceDivergence.lean`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT RH] [NO COMPUTATION]`
  `[NO DENSITY IMPROVEMENT CLAIMED]`

## Goal

Hostile-test whether the all-scale positive-shift separator can be realized as one finite
pre-spectral Hilbert trace on the corpus's actual primitive rational-prime/Gamma source.

## Gates

- [x] 0 → 1 in-progress: exact primitive source/co-source carrier and all-scale diagonal fixed.
- [x] 1 → 2 fully-proven: nonsummability proof dependency-closed.
- [x] 2 → 3 formalized: targeted build and standard-axiom audit pass.
- [ ] 3 → 4 publication-ready: no external novelty claimed; route is a project-specific collision
  of two already formalized laws.

## Theorem

For `pe=(p,e)`, put

```text
n_pe = p^(e+1),
lambda_pe = log n_pe > 0.
```

The primitive biorthogonal source at balanced reflection satisfies

```text
sourceCoeff(a,pe) star(coSourceCoeff(-a,pe))
  = Lambda(n_pe)/n_pe.                                   (1)
```

The multiscale horizontal kernel satisfies

```text
K(lambda_pe,lambda_pe)=log(9/8).                         (2)
```

Consequently its source diagonal is

```text
D_a(pe)=log(9/8) Lambda(n_pe)/n_pe.                      (3)
```

The family in `(1)` is already proved nonsummable. Since `log(9/8)>0`, multiplication by that
constant preserves summability iff the unscaled family is summable. Therefore

```text
not Summable(D_a).                                       (4)
```

## Lean certificate

The module proves:

- `xiGammaEulerPrimitiveLogFrequency_pos`;
- `xiGammaEulerPrimitiveDyadicAllScaleDiagonal_eq_kernel`;
- `xiGammaEulerPrimitiveDyadicAllScaleDiagonal_eq_vonMangoldtWeight`;
- `not_summable_xiGammaEulerPrimitiveDyadicAllScaleDiagonal`.

Targeted validation

```text
lake build GaloisForLFunctions.RHTower.XiWardMultiscaleEulerSourceDivergence
```

passes. `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]`. Module is wired
through `formal/GaloisForLFunctions/RHTower.lean`.

## No-go closure

- **Exact killing theorem:** `(4)` forbids a finite global Hilbert/trace realization retaining the
  complete scale-invariant diagonal at balanced reflection.
- **Strongest positive survivor:** uniform submicroscopic zero charge and nonsummable balanced
  Euler charge have the same exact factor `log(9/8)`.
- **New insight:** source theorem must renormalize or subtract the cofinal Euler wall before taking
  all scales. Compact scale truncation is finite but loses the uniform positive-shift quantum.
- **Status:** exact no-go and positive survivor paper- and Lean-proved. Height-localized
  renormalized source comparison remains open.

## Novelty boundary

No external novelty is claimed. Inputs are classical scale-invariant semigroup calculus plus the
corpus's already formalized balanced primitive Euler nonsummability. Value is route closure: it
prevents the new zero-side separator from being misreported as a finite Euler--Gamma estimate.

## Log

- 2026-08-13 — naive all-scale finite-source conjecture falsified; exact nonsummability survivor
  formalized and umbrella-wired.
