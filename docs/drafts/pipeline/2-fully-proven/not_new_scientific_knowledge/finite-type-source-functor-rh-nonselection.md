# Finite-Type Source Functors Do Not Select RH

- **ID:** finite-type-source-functor-rh-nonselection
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / source-functor guardrail
- **Source:** `finite-linear-probe-rh-nonselection.md`;
  `finite-codimension-landscape-rh-nonselection.md`;
  `rh-landscape-proof-gate.md`;
  `source-selector-repair-obligation-ledger.md`
- **Statement:** A source functor whose local repair decision factors through
  finitely many real-linear observables on the even polynomial-tail sector
  cannot select RH. Any viable source functor must consume an all-order source
  object, such as the full Euler product / explicit formula / completed
  polarization, before the repair side is decided.

## Setup

Let

`Xi(t)=xi(1/2+i t)=Phi(t^2)`.

Consider the local even polynomial-tail sector

`Xi_R(t)=Xi(t)+R(t^2)`, `R in R[u]`.

A proposed source functor `F` is **finite-type on this sector** if, after fixing
any finite seam-jet order, its output on `Xi_R` factors through finitely many
real-linear observables

`L_1(R),...,L_m(R)`.

Here "output" may mean an admissibility verdict, a finite boundary matrix, a
repair class, a scalar threshold coordinate, or a finite-dimensional source
feature vector whose entries are real-linear observables of the local tail.

This definition covers finite Taylor passports, finite moment or value probes,
finite symbolic audits, finite boundary-channel matrices, and finite computed
source summaries when their local dependence on `R` factors through finitely
many real-linear probes. It does not cover arbitrary nonlinear finite summaries
without a separate reduction, the full Euler product, the completed explicit
formula as a distributional identity, or an infinite/pro-object polarization.

## Theorem

Let `F` be finite-type on the polynomial-tail sector. Fix any seam-jet order
`N>=0`. Then there is a polynomial `R in R[u]` such that:

1. `Xi_R` agrees with `Xi` through derivatives `0,...,2N+1` at `t=0`;
2. `F(Xi_R)=F(Xi)`;
3. `Xi_R` is even, real on the real axis, entire of order `1`;
4. `Xi_R` has a non-real zero quartet.

Therefore `F` cannot be an RH selector on this sector. If its output certifies
the repaired side for `Xi`, it gives the same certificate to a false-nearby
object. If it excludes that object, the exclusion uses data outside the finite
factorization.

## Proof

Because `F` is finite-type after the seam-jet order is fixed, choose real-linear
observables `L_1,...,L_m` through which its output factors.

Apply `finite-linear-probe-rh-nonselection.md` to these probes and the same
`N`. It gives a non-real `u0` and a polynomial

`R in u^(N+1) R[u]`

such that

`L_j(R)=0` for every `j`,

and

`R(u0)=-Phi(u0)`.

Set

`Xi_R(t)=Xi(t)+R(t^2)`.

The divisibility by `u^(N+1)` makes `R(t^2)` vanish to order `2N+2` at the seam,
so `Xi_R` preserves the seam jet through order `2N+1`. The vanishing of all
`L_j(R)` means the finite data seen by `F` are unchanged; hence

`F(Xi_R)=F(Xi)`.

The perturbation is even and real on the real axis. Since it is polynomial,
`Xi_R` remains entire of order `1`. If `tau^2=u0`, then

`Xi_R(tau)=Phi(u0)+R(u0)=0`.

Evenness and real symmetry give the quartet

`tau, -tau, conj(tau), -conj(tau)`.

Because `u0` is non-real, this quartet is not on the real `t`-axis. Thus the
perturbed object violates RH while preserving every datum through which `F`
factors.

## Consequence For Source-Functor Routes

The phrase "source functor" is not enough. The functor must be non-finite-type
in the sense above.

A source-functor proof must identify an all-order object before it evaluates the
repair side:

1. a full Euler/local-factor source, not finitely many coefficients;
2. the completed explicit formula as an identity of distributions, not a finite
   list of moments;
3. a completed polarization or boundary-index object, not a finite scalar
   reporter;
4. a fake-family source gate that rejects finite-tail perturbations before
   zero-location or positivity language is used.

If the functor factors through a finite-dimensional linear quotient of the local
polynomial-tail sector, it is a finite passport. The theorem above constructs a
same-passport object with a non-real zero quartet.

## Theatre Test

For any proposed source functor, ask:

1. Through what quotient of the local source data does the repair decision
   factor?
2. Is that quotient finite-dimensional or cut out by finitely many probes?
3. If yes, which line of the proof prevents the polynomial-tail fake above?
4. If the answer is "Euler product", where is the all-order Euler product used
   as more than a label?

If no such line exists, the functor is a finite-type passport and cannot be the
landscape proof.

## Source Boundary

This theorem deliberately does not preserve the Euler product. That is the
point: a real source functor must see the Euler product or an equivalent
all-order source structure. Finite-dimensional shadows of that source are too
weak.

The result proves no positivity for zeta and no zero localization. It rules out
one class of source-functor theatre.

## Gates

- [x] 0 -> 1 in-progress: entropy selected the `source-functor` route.
- [x] 1 -> 2 fully-proven: finite-type factorization reduced to the finite
  linear-probe fake theorem.
- [ ] 2 -> 3 formalized: optional finite-dimensional quotient version over
  polynomial vector spaces.

## Log

- 2026-06-24 -- Codex: created under the private RH continuation. The card
  records that a source functor must be all-order/pro-infinite; any local
  finite-type functor leaves a same-output off-line-zero fake.

## 2026-06-24 nonlinear selector boundary

`nonlinear-finite-selector-oracle-vacuity.md` records the boundary of this theorem. The finite-type nonselection result applies to source functors whose local output factors through finitely many real-linear observables. It cannot be extended to arbitrary nonlinear finite-valued maps without extra hypotheses, because a nonlinear finite selector can encode any target property by its characteristic function.

Thus a nonlinear source functor must pass an anti-oracle gate: it needs a source formula, no target predicate in the definition, a fake-family source gate, all-order input, and a transfer theorem from source construction to repaired index.
