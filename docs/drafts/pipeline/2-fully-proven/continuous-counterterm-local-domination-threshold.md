# Continuous Counterterm Local Domination Threshold

- **ID:** continuous-counterterm-local-domination-threshold
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / route normalization
- **Source:** `continuous-counterterm-atom-locality.md`,
  `finite-rank-counterterm-kernel-visibility.md`
- **Statement:** Once a continuous quadratic counterterm is allowed to be
  nonzero on atom-isolator subspaces, positivity of `Q_0+C` forces an exact
  atom-local domination inequality. A proposed repair can hide a bad atom only
  by paying this local quadratic bill.

## Setup

Use the setup of `continuous-counterterm-atom-locality.md`.

Thus `Y` is the folded reciprocal nontrivial-zero support of the completed
Riemann `xi`, with positive folded multiplicities `M_y`, conjugation symmetry,
and

`sum_y M_y |y| < infinity`.

Set `K=Y union {0}`. Let `C_sym(K)` be the real vector space of continuous
conjugation-symmetric functions on `K`, and set

`Q_0[f]=sum_y M_y y f(y)^2`.

Let `C` be a continuous real quadratic form on `C_sym(K)`, and define

`R_C[f]=Q_0[f]+C[f]`.

For an atom `a`, let `E_a` be the real atom-isolator subspace:

- if `a` is real, `E_a=R e_a`, with `e_a(a)=1` and `e_a=0` off `{a}`;
- if `a` is non-real, `E_a` is parametrized by `zeta in C` through the
  symmetric isolator `e_{a,zeta}` supported on `{a,conjugate(a)}`.

Write `C_a=C|_{E_a}` and `Q_a=Q_0|_{E_a}`.

## Theorem

Assume

`R_C[f]>=0 for every f in C_sym(K)`.

Then every atom satisfies the following local threshold.

1. If `a` is real, then

   `M_a a + C[e_a] >= 0`.

   In particular, a negative real atom `a<0` can survive only if

   `C[e_a] >= -M_a a > 0`.

2. If `a` is non-real, then the real quadratic form

   `C_a(zeta) + 2 M_a Re(a zeta^2)`

   is positive semidefinite on the two real variables `zeta=x+iy`.
   Equivalently,

   `C_a >= -Q_a`

   in the Loewner order on the real two-dimensional space `E_a`.

These inequalities are exact local conditions. If either one fails at an atom,
global positivity of `R_C` is impossible.

## Proof

Positivity of `R_C` on `C_sym(K)` restricts to positivity on every real
subspace `E_a`.

For a real atom, every element of `E_a` is `t e_a`, with `t in R`. Hence

`0 <= R_C[t e_a] = t^2(M_a a + C[e_a])`

for all real `t`, which is equivalent to `M_a a + C[e_a]>=0`.

For a non-real atom, use the coordinate `zeta=x+iy` on `E_a`. The conjugate pair
contribution to `Q_0` is

`Q_a(zeta)=M_a a zeta^2 + M_a conjugate(a) conjugate(zeta)^2
          =2 M_a Re(a zeta^2)`.

The restricted form is therefore

`R_C[e_{a,zeta}]=C_a(zeta)+2 M_a Re(a zeta^2)`.

Positivity for every `zeta in C` is exactly positive semidefiniteness of this
real quadratic form, equivalently `C_a >= -Q_a` in Loewner order.

## Sharpness In Abstract Models

The local threshold is not merely necessary. In an abstract reciprocal-divisor
model with one bad real atom `a<0`, the rank-one counterterm

`C[f]= -M_a a f(a)^2`

makes the local repaired form vanish on `E_a`.

For one bad non-real conjugate pair, the two-dimensional atom-fed counterterm

`C[f]= -2 M_a Re(a f(a)^2)`

makes the local repaired form vanish on that pair's isolator subspace.

These examples do not prove anything about the actual zeta divisor. They show
that the inequalities above are the exact atom-local payments a repair must
make if bad atoms are present.

## Consequence for the RH Route

`continuous-counterterm-atom-locality.md` said where a nonlocal counterterm must
act. This card says how much it must act there.

A continuous counterterm that leaves every `E_a` untouched is still RH-strength.
A continuous counterterm that repairs a bad atom must supply the corresponding
real scalar payment or two-dimensional Loewner domination payment on that atom's
isolator subspace.

Thus a semilocal or infinite-rank proposal has no hidden reserve just because it
is large. Its nonzero atom-local restrictions are the proof obligation. The
route must construct those local restrictions from source data before the
reciprocal divisor is read, or prove the faithful index by a source theorem that
precedes these atom-local tests.

## Theatre Test

For any proposed continuous counterterm `C`:

1. Compute `C[e_a]` for a real reciprocal atom `a`.
2. Compute the two-dimensional real matrix of `C_a` for a non-real pair.
3. Check whether these values dominate `-Q_a` in the exact local sense above.
4. If they do, identify the source theorem that produced those atom-local
   values without using the reciprocal zeros.
5. If no such source theorem exists, the repair is only an atom-fed correction
   written in a broader vocabulary.

## Novelty And Significance Gate

The proof is finite-dimensional. The value is not a new external theorem about
quadratic forms; the value is the route filter. It converts the remaining
continuous-counterterm escape hatch from a vague nonlocal claim into a precise
local domination bill at each bad reciprocal atom.

## Gates

- [x] 0 -> 1 in-progress: local domination threshold isolated from the
  continuous-counterterm audit.
- [x] 1 -> 2 fully-proven: scalar and two-dimensional restrictions proved.
- [ ] 2 -> 3 formalized: optional finite-dimensional quadratic-form theorem.

## Log

- 2026-06-24 -- Codex: created after the atom-locality card to make the
  nonzero-restriction case exact rather than rhetorical.
