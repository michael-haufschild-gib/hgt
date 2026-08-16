# Uvarov Kernel Pregate RH Equivalence

- **ID:** uvarov-kernel-pregate-rh-equivalence
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / route normalization
- **Source:** `../../3-formalized/not_new_scientific_knowledge/uvarov-repair-requires-boundary-kernel-positivity.md`,
  `source-aware-q0-alone-reciprocal-positivity.md`, and
  `seam-log-hankel-rh-equivalence.md`
- **Statement:** For the actual reciprocal divisor, all-order positivity on the
  first-trivial-zero kernel `p(y_*)=0` is already equivalent to RH. Thus the
  Uvarov kernel pre-gate is not a weaker source target unless it is proved from a
  non-equivalent source principle.

## Setup

Let `D={(y,M_y)}` be the folded reciprocal nontrivial-zero divisor of the completed
Riemann `xi`, with

`y=-(rho-1/2)^(-2)`.

As in `source-aware-q0-alone-reciprocal-positivity.md`, define

`Q_0[p] = sum_y M_y y p(y)^2`

for real polynomials `p`. Fix a real point

`b notin Y={y : M_y != 0}`.

For the first-trivial-zero Uvarov chart, `b=y_*=-4/25`.

Define the boundary-kernel test

`Q_b[q] = Q_0[(y-b)q(y)] = sum_y M_y y (y-b)^2 q(y)^2`.

Equivalently, `Q_b` is the restriction of `Q_0` to the ideal of real polynomials
vanishing at `b`.

## Theorem

For any real `b notin Y`, the following are equivalent:

1. RH.
2. `Q_b[q] >= 0` for every real polynomial `q`.

In particular, positivity of the all-order first-trivial-zero kernel pre-gate

`Q_0[p] >= 0 for every real polynomial p with p(-4/25)=0`

is equivalent to RH.

## Proof

If RH holds, then every reciprocal atom `y` lies in `R_{>0}`. Since `b` is real
and `b notin Y`, each coefficient

`M_y y (y-b)^2`

is positive, and therefore `Q_b[q]>=0` for every real polynomial `q`.

Conversely, suppose some atom `a in Y` is not in `R_{>0}`. The support

`K=Y union {0}`

is compact, countable, has empty interior, and has connected complement. By
Mergelyan approximation, after conjugation symmetrization, real polynomials are
uniformly dense in the continuous conjugation-symmetric functions on `K`.

There are two cases.

1. `a` is real and negative. Since `a != b`, the coefficient

   `M_a a(a-b)^2`

   is negative. Choose a continuous symmetric function on `K` that is `1` at `a`
   and `0` on `K\\{a}`, and approximate it uniformly by real polynomials `q_n`.
   Dominated convergence gives

   `Q_b[q_n] -> M_a a(a-b)^2 < 0`.

2. `a` is non-real. Then `conjugate(a)` is also an atom with the same
   multiplicity. Since `a(a-b)^2 != 0`, choose `zeta in C` with

   `Re(a(a-b)^2 zeta^2) < 0`.

   Choose a continuous symmetric function on `K` that takes value `zeta` at `a`,
   `conjugate(zeta)` at `conjugate(a)`, and `0` elsewhere, and approximate it by
   real polynomials `q_n`. Dominated convergence gives

   `Q_b[q_n] -> 2 M_a Re(a(a-b)^2 zeta^2) < 0`.

In either case, positivity of `Q_b` fails. Hence all-order positivity on the ideal
`(y-b)` excludes every reciprocal atom outside `R_{>0}`. This is equivalent to RH.

For `b=-4/25`, the point is not a nontrivial reciprocal atom of `xi`; it is the
first trivial-zero boundary point used by the Uvarov chart. The theorem applies.

## Consequence for the RH Route

`../../3-formalized/not_new_scientific_knowledge/uvarov-repair-requires-boundary-kernel-positivity.md` showed that a rank-one repair
at `y_*` first requires positivity on `ker e_{y_*}`. This card shows that the
all-order version of that pre-gate already has RH strength for the actual divisor.

Therefore the route cannot gain leverage by moving from the full `Q_0` cone to
the all-order kernel pre-gate. A non-mirror proof must derive this kernel positivity
from independent source rigidity, not list it as a new assumption. In source-built
language, the required theorem becomes:

`Euler/Gamma/FE source data force Q_0[(y+4/25)q] >= 0 for every real q`.

That statement is already a zero-localization theorem in the source-aware reciprocal
divisor chart.

## Source Boundary

The proof is the same compact-polynomial-density isolation argument as the
source-aware `Q_0` theorem, with the nonvanishing factor `(y-b)^2` inserted. It
does not prove RH. It classifies the Uvarov kernel pre-gate as an RH-equivalent
all-order chart when applied to the actual reciprocal divisor.

## Gates

- [x] 0 -> 1 in-progress: tested whether the kernel pre-gate is weaker than `Q_0`.
- [x] 1 -> 2 fully-proven: ideal-restricted source-aware positivity equivalence
  proved.
- [ ] 2 -> 3 formalized: optional; same approximation theorem dependency as
  `source-aware-q0-alone-reciprocal-positivity.md`.

## Log

- 2026-06-24 -- Codex: created after the Uvarov kernel pre-gate note. The key
  observation is that multiplying test polynomials by `(y+4/25)` does not hide any
  reciprocal atom, because `-4/25` is outside the nontrivial reciprocal divisor.

## 2026-06-24 finite-boundary ideal generalization

`finite-boundary-ideal-q0-rh-equivalence.md` generalizes this card from the single Uvarov boundary point to any finite real boundary set disjoint from the reciprocal nontrivial-zero support. Multiplying test polynomials by a fixed real polynomial `h` with `h|_Y` nonzero preserves the atom-isolation proof, so all-order positivity on the ideal `h R[y]` is still equivalent to RH.

Thus the one-point pre-gate is one instance of a broader rule: finite exterior boundary conditioning does not soften the all-order shifted `Q_0` positivity problem.
