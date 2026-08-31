# Theta-source functional-equation root-current transport law

- **ID:** ULF-ODTM-5
- **Stage:** 3-formalized (paper proof companion)
- **Type:** THEOREM (paper)
- **Source:** fixed theta-source inverse, its exact reflection law, and ULF-ODTM-4
- **Statement:** Source reflection lifts to a unitary involution on the quantile Hilbert space,
  anticommutes with the fixed compact source inverse, transports every complete root block at
  `mu` onto the block at `-mu`, and transports its rank-one conormal current with the exact sign
  `(-1)^(d_mu-1)` while preserving all recoverable information.

## Goal

Replace determinant-level functional-equation symmetry by an operator-level action on actual
source packets.  The theorem must preserve the complete generalized history, the terminal
eigenline, algebraic multiplicity, current norm, and current range.  No RH assumption or zero
enumeration enters the construction.

## Gates

- [x] 0 → 1 in-progress: source-pure action and exact transport target identified
- [x] 1 → 2 fully-proven: complete proof below, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem/module and targeted audit
- [ ] 3 → 4 publication-ready: standalone exposition and external audit

## Construction

Let `k` be the fixed even theta source, let

```text
H_k = L2(R, k(x)^(-1) dx),
H   = L2((0,1), dt),
U   : H_k -> H
```

be the source and quantile Hilbert spaces and the already-constructed quantile unitary.  Put

```text
(R_k f)(x) = f(-x),
R = U R_k U^(-1).
```

Evenness of `k` makes `x -> -x` measure preserving for `k(x)^(-1) dx`.  Hence `R_k`, and
therefore `R`, is a complex-linear unitary involution.

Let `B` be the fixed compact theta-source inverse on `H`.  For a nonzero spectral point `mu`, put

```text
G_mu = maxGenEigenspace(B, mu),
N_mu = B|G_mu - mu I,
d_mu = dim_C G_mu,
C_mu = N_mu^(d_mu - 1).
```

By ULF-ODTM-4 and source ODE uniqueness, `C_mu` is nonzero, has rank one, and has range equal to
`ker N_mu`.

## Theorem

For every nonzero source spectral point `mu`:

1. `R^2 = I` and `R B R = -B`.
2. `R(G_mu) = G_(-mu)`, so restriction gives a unitary equivalence
   `R_mu : G_mu -> G_(-mu)` and `d_(-mu) = d_mu`.
3. The nilpotent remainders obey

   ```text
   N_(-mu) R_mu = - R_mu N_mu,
   N_(-mu)^j R_mu = (-1)^j R_mu N_mu^j       for every j >= 0.
   ```

4. The source conormal currents obey the exact covariance law

   ```text
   C_(-mu) R_mu = (-1)^(d_mu - 1) R_mu C_mu.
   ```

5. Consequently reflection preserves current norm, nonvanishing, rank, and complete recovery:

   ```text
   R_mu(range C_mu) = range C_(-mu) = ker N_(-mu),
   dim range C_(-mu) = dim range C_mu = 1.
   ```

Thus functional-equation transport is information-neutral.  Its only action on the terminal
current is the parity character of Jordan depth `d_mu - 1`.

## Proof [PROVED HERE]

Since `k(-x)=k(x)`, also `k(-x)^(-1)=k(x)^(-1)`.  Reflection preserves Lebesgue measure and the
density, hence preserves the weighted measure.  Pullback by reflection is therefore a
complex-linear isometry of `H_k`.  Its square is the identity, so it is onto and unitary.
Conjugating by `U` proves the same assertions for `R`.

The literal source inverse satisfies, for every integrable source vector,

```text
B_source(R_k f)(-x) = -B_source(f)(x).
```

Every vector of `H_k` is integrable, and the quantile inverse is unitarily equivalent almost
everywhere to this literal source inverse.  Therefore the displayed identity is an identity of
`H_k` vectors.  Conjugating by `U` gives `R B R = -B`, equivalently `R B = -B R`.

For every `v` and scalar `mu`, anticommutation gives

```text
(B + mu I) Rv = -R(B - mu I)v.
```

Induction yields

```text
(B + mu I)^j Rv = (-1)^j R(B - mu I)^j v.
```

It follows in both directions, using `R^2=I`, that `R` maps the stabilized generalized
`mu`-kernel exactly onto the stabilized generalized `-mu`-kernel.  This proves the root-block
unitary equivalence and equality of dimensions.  Restricting the `j=1` identity gives the claimed
nilpotent-remainder law, and induction inside the finite-dimensional blocks gives its power law.

Take `j=d_mu-1`.  Equality of block dimensions identifies both current exponents, giving

```text
C_(-mu) R_mu = (-1)^(d_mu-1) R_mu C_mu.
```

The scalar sign has norm one and `R_mu` is unitary.  Conjugation therefore preserves operator norm
and nonvanishing.  Applying both sides to all block vectors proves exact transport of ranges.
ULF-ODTM-4 identifies these ranges with the respective one-dimensional kernels, so rank and the
terminal recoverable eigenline are preserved.  No information is discarded.  QED.

## New universal-law content

The functional equation is not merely evenness of a determinant or a pairing of spectral labels.
It is a depth-graded gauge action on open root histories.  Closed terminal observation forgets the
history but retains its parity character.  Simple zeros (`d_mu=1`) transport evenly; every added
Jordan layer toggles the reflected current sign.  This is a route-independent prediction in the
source, multiplicity, homological-transfer, and conormal-current organs.

## Scope

This theorem does not select the real spectrum and does not prove RH.  It constructs the exact
functional-equation action required before global packet sewing can be called conservative.
Selection still requires a source-generated formation/properness law that controls occurrence,
not generic positivity or reflection symmetry.

## Log

- 2026-08-31 — complete paper proof; promoted directly to Stage 2
- 2026-08-31 — formalized in
  `RHTower.HedenmalmThetaSourceFunctionalEquationRootCurrentTransport`; direct elaboration,
  targeted leaf build, axiom audit, forbidden-declaration scan, and diff check pass
