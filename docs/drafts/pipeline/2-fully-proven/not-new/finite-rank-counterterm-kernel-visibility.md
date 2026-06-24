# Finite-Rank Counterterm Kernel Visibility

- **ID:** finite-rank-counterterm-kernel-visibility
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / route normalization
- **Source:** `test-space-closure-q0-visible-rh.md`,
  `finite-hard-edge-counterterm-q0-rh-strength.md`,
  `finite-rank-one-selector-no-free-lunch.md`
- **Statement:** A finite-rank counterterm can only give source-free information
  on the kernel of its boundary map. Any bad reciprocal atom not isolable in
  that kernel has been moved into the finite-dimensional quotient and requires
  a separate source theorem.

## Setup

Let `Y` be the folded reciprocal nontrivial-zero support of the completed Riemann
`xi`, with positive folded multiplicities `M_y`, conjugation symmetry, and

`sum_y M_y |y| < infinity`.

Set

`K = Y union {0}`.

Let `C_sym(K)` be the real vector space of continuous conjugation-symmetric
functions on `K`, and set

`Q_0[f] = sum_y M_y y f(y)^2`.

Let

`L:C_sym(K) -> R^r`

be a continuous real-linear map, and let `B` be a real quadratic form on `R^r`.
Define the finite-rank counterterm

`C[f] = B(Lf)`

and the renormalized form

`R_C[f] = Q_0[f] + C[f]`.

## Theorem

If

`R_C[f] >= 0 for every f in C_sym(K)`,

then

`Q_0[f] >= 0 for every f in ker L`.

The same conclusion holds if positivity is first proved only on real
polynomials, provided `L` is the restriction of the continuous map above: real
polynomials are uniformly dense in `C_sym(K)`, and `R_C` is continuous for the
uniform norm.

Consequently, every reciprocal atom that is visible to the closed test space
`ker L` lies in `R_{>0}`. In particular, if `ker L` contains the atom-isolators
for all atoms outside a closed conjugation-invariant set `E`, then positivity of
`R_C` forces RH on `Y \ E`; atoms in `Y cap E` are quotient-hidden.

## Proof

If `f in ker L`, then `C[f]=B(0)=0`, so

`0 <= R_C[f] = Q_0[f]`.

Thus `Q_0` is positive on the closed test space `ker L`. The atom-isolation
conclusion is exactly `test-space-closure-q0-visible-rh.md` applied to
`S=ker L`.

If `ker L` contains the isolators for all atoms outside `E`, then the same
closure theorem excludes every bad atom in `Y \ E`. Atoms whose isolators are
not in `ker L` are not tested by this kernel argument; they have been moved into
the finite-dimensional quotient `R^r`.

## Countermodel: Finite Rank Can Hide a Bad Atom

The kernel condition is necessary. In an abstract reciprocal-divisor model with
one negative real atom `a<0` of multiplicity `M`, take

`Q_0[f] = M a f(a)^2`.

Let `L(f)=f(a)` and

`C[f] = -M a L(f)^2`.

Then `C` has rank one and

`R_C[f] = 0`

for every test function, although the atom is off the positive real axis. The
counterterm succeeds only because it is zero-fed: its quotient is exactly the
bad atom evaluation.

For a non-real conjugate pair `a, conjugate(a)`, the same construction uses the
real two-dimensional quotient `f(a) in C` and the counterterm

`C[f] = -2M Re(a f(a)^2)`,

which cancels the pair contribution.

These examples do not prove anything about the actual zeta divisor. They show
that finite rank is not by itself a source certificate. A finite-rank repair must
explain why its quotient is source-built and why no bad atom is hidden there.

## Consequence for the RH Route

Finite-rank boundary or renormalization language has two distinct parts:

1. **Kernel theorem.** On `ker L`, the counterterm disappears. Positivity there
   is a usual `Q_0` visibility test.
2. **Quotient theorem.** Any atom whose isolator has nonzero image under `L`
   lives in the finite-dimensional quotient. Positivity in that quotient is a
   Schur/Weyl/Krein statement and can be zero-fed unless `L` and `B` are
   constructed from source data before the divisor is read.

Thus a finite-rank repair is not automatically a proof engine and not
automatically harmless. It is harmless only for atoms visible in the kernel; it
can hide atoms precisely in its quotient. A non-mirror RH proof must therefore
give a source theorem for the quotient, not merely exhibit a finite-rank positive
repair.

## Theatre Test

For any finite-rank counterterm or boundary repair, ask:

1. What is the boundary map `L`?
2. Which reciprocal atom-isolators lie in `ker L`?
3. Which atoms have nonzero image in the finite-dimensional quotient?
4. Is the quotient form source-built before reading the divisor, or does it
   encode the bad atom evaluations it repairs?

Without those answers, finite-rank positivity is a coordinate chart, not a
source selection theorem.

## Gates

- [x] 0 -> 1 in-progress: finite-rank kernel/quotient split isolated.
- [x] 1 -> 2 fully-proven: kernel theorem and zero-fed countermodels proved.
- [ ] 2 -> 3 formalized: optional finite-dimensional quotient theorem plus
  closed-test-space visibility.

## Log

- 2026-06-24 -- Codex: created to classify finite-rank counterterms after the
  finite hard-edge counterterm theorem. The key point is that finite rank can
  hide atoms in its quotient unless the quotient has a source proof.

## 2026-06-24 non-atomic quotient specialization

`non-atomic-finite-rank-counterterms-rh-strength.md` records the main source-facing specialization of the kernel theorem. If the finite-rank boundary map has no point-mass component at any reciprocal atom, then it annihilates every atom-isolator. Hence positivity of `Q_0+B(L.)` remains RH-strength.

Therefore the quotient can hide bad atoms only by seeing their isolators. In measure terms, that means atom-evaluation content on the reciprocal support.

## 2026-06-24 quotient inertia is a boundary Schur matrix

`finite-rank-boundary-schur-index.md` gives the finite-dimensional quotient algebra complementary to this kernel theorem. The kernel theorem says which atoms remain visible after the boundary map is imposed; the Schur-index theorem says how the finite quotient changes inertia once the boundary form is fixed.

Both parts are necessary. Kernel visibility alone does not prove the quotient sign, and the quotient Schur matrix is source-relevant only if its boundary channels and form are constructed before the reciprocal divisor is read.

## 2026-06-24 general atom-local counterterm audit

`continuous-counterterm-atom-locality.md` generalizes the finite-rank kernel warning. For any continuous quadratic counterterm, finite-rank or not, the decisive local question is its restriction to each reciprocal atom-isolator subspace. If it vanishes there, the repaired positivity remains RH-strength; if it does not, the proof must explain how those atom-local values were source-built.

## 2026-06-24 quotient payments are local domination thresholds

`continuous-counterterm-local-domination-threshold.md` identifies the exact finite-dimensional bill paid by any quotient that sees a bad atom. For a finite-rank repair, the hidden quotient is source-relevant only if its boundary form supplies the required scalar or two-dimensional Loewner domination from source data.

This refines the kernel/quotient split: the kernel leaves atoms visible; the quotient can hide them only by paying the atom-local threshold.
