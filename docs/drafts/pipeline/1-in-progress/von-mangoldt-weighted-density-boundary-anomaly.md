# Von Mangoldt weighted-density boundary anomaly

- **ID:** `von-mangoldt-weighted-density-boundary-anomaly`
- **Stage:** 1 — in progress
- **Parent:** `SR-41`; `von-mangoldt-cyclic-reader-flux-no-go`
- **Type:** `[UNIVERSAL WEIGHTED MARGINAL LAW] [SOURCE-SPECIFIC FAILED CLASS]`
- **Scientific status:** `[PROVED IN LEAN SCRATCH] [MODULE AUDIT PENDING] [EXTERNAL NOVELTY UNVERIFIED]`
- **RH used:** no
- **Computation used:** no

## Frontier

Existing results exclude ordinary coordinate partial trace and cyclic readers on finite full
matrix algebras.  They leave readers on a proper source algebra, non-cyclic density-weighted
partial traces, and singular boundary anomalies.

The first surviving finite class puts diagonal or full matrix densities on the source and jet
factors before contracting a bivariate kernel.  This card determines its exact conservation and
opening laws.

## Universal density lock

For finite source and jet carriers `P,J`, a bivariate kernel `C`, and arbitrary matrix densities
`A` on `P` and `D` on `J`, define

```text
Jet_A(C)(i,j)
  =sum_(p,q) A(q,p) C((p,i),(q,j)),

Src_D(C)(p,q)
  =sum_(i,j) D(j,i) C((p,i),(q,j)),

<D,X>_tr
  =sum_(i,j) D(j,i) X(i,j).
```

Finite-sum commutation gives

```text
<D,Jet_A(C)>_tr = <A,Src_D(C)>_tr.                    (1)
```

No positivity, Hermitian symmetry, cyclicity, normalization, or nondegeneracy is used.  Diagonal
weights are a specialization of `(1)`.

Equation `(1)` is elementary tensor-contraction algebra and is not claimed as externally novel.

## Exact Suzuki boundary anomaly

Let

```text
R_(M,N)(i,j)=rho_M(i+j+2)
```

be the actual `SR-40` principal-relative jet current and let one infinite density kernel `D` be
restricted to the first `N` jet coordinates.  Adding coordinate `N` gives the exact law

```text
<D_(N+1),R_(M,N+1)>_tr
 =<D_N,R_(M,N)>_tr
  +D(N,N) rho_M(2N+2)
  +sum_(i<N) (D(N,i)+D(i,N)) rho_M(N+i+2).             (2)
```

For every nonempty source aperture and every displayed order,

```text
rho_M(q)>0.                                             (3)
```

Suppose consecutive bivariate kernels have `R_(M,N)` and `R_(M,N+1)` as their `A`-weighted jet
marginals and one fixed source marginal `B` as their `D_N`-weighted source marginal.  Applying
`(1)` twice and subtracting forces

```text
D(N,N) rho_M(2N+2)
 +sum_(i<N) (D(N,i)+D(i,N)) rho_M(N+i+2)=0.             (4)
```

This is exact source flux conservation, not an estimate.

## Consequences

### Diagonal densities

For `D(i,j)=delta_(i,j) beta_i`, `(4)` becomes

```text
beta_N rho_M(2N+2)=0,
```

so `beta_N=0`.  Across every nonempty jet cutoff, all weights above degree zero vanish.  The only
diagonal-density survivor is a rank-one degree-zero reader.  In particular, no diagonal KMS,
Gibbs, signed, or normalized density with a nonzero higher-jet weight can retain one fixed
`SR-38` source marginal.

### Full densities

If `D(N,N)>0`, equation `(4)` forces

```text
there exists i<N with D(N,i)+D(i,N)<0.                 (5)
```

Thus non-diagonal density does not freely evade the trace lock.  Every new positive diagonal
weight requires a strictly negative symmetric boundary coefficient with precisely calibrated
moment flux.  Entrywise nonnegative full densities are excluded.

### Minimal source covariance

There is an algebraic signed escape from `(4)`: choose a negative boundary row to cancel each new
positive diagonal flux.  That escape fails as soon as the density reader must be cyclic against
one simple-spectrum jet-degree clock.  Universally,

```text
<D,QX>_tr=<D,XQ>_tr for every X,
Q=diag(q_i), q_i pairwise distinct
  -> D(i,j)=0 for i!=j.                                (6)
```

Matrix units prove `(6)` directly.  Applying `(6)` at each jet cutoff deletes every boundary
coefficient in `(4)`, after which strict positivity of `rho_M(2N+2)` forces

```text
D(N,N)=0.                                              (7)
```

Across the nonempty tower, every diagonal above degree zero vanishes.  Therefore any finite
regular density reader retaining one fixed source marginal and cyclic against the natural
simple-spectrum degree clock collapses to the degree-zero corner.  A signed star-density can
absorb flux only by violating this minimal clock cyclicity.

## Canonical constructive survivor

Equation `(4)` is triangular inside symmetric Toeplitz densities.  For any moment sequence `m`
with `m_(n+3) != 0`, define `d_0=1` and recursively

```text
d_(n+1)
 =-[m_(2n+4)
    +2 sum_(j=0)^(n-1)
       d_(n-j) m_(n+j+4)]
   /(2 m_(n+3)).                                        (8)
```

Set

```text
D(i,j)=d_|i-j|.                                         (9)
```

The recursion is exactly the opening equation, so every finite Hankel section

```text
H_N(i,j)=m_(i+j+2)
```

satisfies

```text
<D_N,H_N>_tr=m_2          for every N>=1.              (10)
```

Conversely, if `e_0=1` and the symmetric Toeplitz density `E(i,j)=e_|i-j|` keeps these finite-section
pairings constant, subtracting consecutive sections gives the same triangular opening equation;
because `m_(n+3) != 0`, induction forces `e_n=d_n` for every `n`.  Thus every nonvanishing Hankel
moment current has exactly one normalized symmetric Toeplitz countertrace.  No matrix completion,
factorization, target sign, or spectral divisor is chosen.  This existence--uniqueness law is the
positive theorem exposed by the weighted-marginal obstruction.

For actual Suzuki moments

```text
m_q=rho_M(q),
```

strict source positivity guarantees every denominator in `(8)` is nonzero.  Lean proves the exact
source specialization

```text
<D_(M,N),R_(M,N)>_tr=rho_M(2)       for every N>=1.     (11)
```

This is the first source-fixed, inclusion-compatible reader in this attack that genuinely absorbs
all jet-opening flux.  It is not cyclic against the diagonal jet-degree clock; its signed Toeplitz
boundary anomaly is precisely what makes `(11)` possible.

The cofinal statement is not obtained by defining a new density after discarding finite
apertures.  Let `D_M` be the density recursively generated by `rho_M`, and let `D_infinity` be the
one generated by the fully summed moment `rho`.  Pointwise moment convergence and strict
positivity of every limiting pivot imply, by strong induction through the nonlinear recurrence
`(8)`,

```text
d_(M,k) -> d_(infinity,k)                  for every k,
D_(M,N) -> D_(infinity,N) entrywise        for every fixed N.       (12)
```

The limiting reader still obeys the exact law

```text
<D_(infinity,N),R_(infinity,N)>_tr=rho(2)  for every N>=1.          (13)
```

Moreover `(11)` and `(13)` hold after replacing the contracted Hankel matrices by the actual
source-edge Dirac--Krein exchange Grams whose entries they are.  Thus countertrace is attached to
the explicit source realization, not only to an abstract copy of its moment matrix.

## Scientific change

This closes three apparent `SR-41` escapes:

1. replacing ordinary partial trace by an arbitrary diagonal density;
2. replacing it by an entrywise nonnegative non-diagonal density;
3. using a signed full density while retaining cyclicity against a simple-spectrum jet clock.

The exact survivor is narrower: a finite regular reader must carry a signed off-diagonal boundary
row satisfying `(4)` at every jet opening **and** the actual source algebra must not contain the
simple-spectrum degree clock against which the reader is cyclic.  Otherwise reader must vary with
cutoff, abandon finite regular contraction/cyclicity, or become a genuinely singular cofinal
anomaly.

Equations `(8)`--`(13)` construct that survivor canonically at finite aperture and prove its
projective cofinal limit.  Remaining frontier is no longer existence or cutoff compatibility of a
flux-carrying jet reader.  It is whether this exact Toeplitz countertrace:

1. couples to the fixed coherent odd Gamma--Jacobi marginal through one non-separable source
   incidence;
2. realizes completed Euler multiplication on its proper anomalous algebra;
3. feeds the co-Poisson fibre orientation.

This does not construct the required reader, identify completed Euler multiplication, force
co-Poisson fibre orientation, or prove RH.

## Corpus and literature collision audit

Corpus search found ordinary marginal trace lock, finite full-matrix cyclic-reader rigidity,
graded supertraces, KMS constructions, and singular-trace no-go results, but no arbitrary-density
law `(2)`--`(5)` for the actual `SR-40` current or its composition with fixed `SR-38` marginal.

External search found standard partial-trace identities, modular/KMS weights, and Toeplitz
boundary/index anomalies.  Those make `(1)` standard in spirit.  No source located in this pass
contains the von-Mangoldt opening recurrence `(2)`, boundary hyperplane `(4)`, or diagonal-tail
collapse for this arithmetic current.  External priority remains unverified.

## Lean

New modules:

```text
formal/GaloisForLFunctions/HTGeometry/WeightedBivariateMarginalLock.lean
formal/GaloisForLFunctions/RHTower/VonMangoldtWeightedMarginalBoundaryAnomaly.lean
```

Principal declarations:

```text
matrixDensityPair_densityBivariateJetMarginal_eq
matrixDensityClockCyclic_offDiagonal_eq_zero
hankelToeplitzCounterweight_opening_cancellation
hankelToeplitzCounterDensity_opening_cancellation
tendsto_hankelToeplitzCounterweight
hankelToeplitzCounterweight_unique
densityPair_finiteVonMangoldtSuccessor_succ
fixedSourceDensityMarginals_force_boundaryCancellation
fixedSourceDensityMarginals_require_negativeBoundary
fixedSourceDensityMarginals_clockCyclic_force_openingDiagonal_zero
fixedSourceMarginal_clockCyclic_allPositiveJetSections_force_diagonalTail_zero
finiteVonMangoldtHankelToeplitzCounterDensity_opening_cancellation
finiteVonMangoldtHankelToeplitzCounterDensity_pair_constant
vonMangoldtSuccessorRelativeMoment_pos
tendsto_finiteVonMangoldtHankelToeplitzCounterDensity_section
vonMangoldtHankelToeplitzCounterDensity_pair_constant
vonMangoldtHankelToeplitzCounterDensity_diracKrein_pair_constant
fixedSourceMarginals_force_openingJetWeight_zero
fixedSourceMarginal_allPositiveJetSections_force_jetWeight_tail_zero
gammaOddJacobi_fixedSourceMarginal_allPositiveJetSections_force_tail_zero
```

Scratch verification:

```text
lake env lean /tmp/hgt_weighted_marginal_scratch.lean
```

passes without warnings.  One final targeted cached module build remains pending.

## Next falsifier

Construct source-canonical signed boundary rows satisfying `(4)` and test:

1. restriction compatibility across all `N`;
2. proper-source-algebra covariance;
3. compatibility with the coherent odd Gamma--Jacobi marginal;
4. completed Euler multiplication before any Xi or target moment is read.

Failure of any item retires the regular full-density class.  Success would provide the first
nontrivial finite model of the `SR-41` anomaly rather than another trace wrapper.
