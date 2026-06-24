# Finite Linear Probe RH Nonselection

- **ID:** finite-linear-probe-rh-nonselection
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / proof-route guardrail
- **Source:** RH landscape gate; finite-source selection audit
- **Statement:** A finite family of real-linear probes on the even-polynomial
  perturbation directions cannot select RH. After preserving those probes and any fixed
  finite seam jet, one can still force an off-line zero quartet.

## Setup

Let

`Xi(t)=xi(1/2+i t)=Phi(t^2)`

with `Phi` entire and real on the real axis. Let `L_1,...,L_m` be real-linear
functionals on `R[u]`. These represent any finite real-linear audit of the polynomial
perturbation sector: finite Taylor coefficients, finite values, finite moment/passport
coordinates, or any finite linear combination of such data.

Fix `N>=0`. We will preserve the first `2N+1` derivatives at the seam by restricting
to perturbations divisible by `u^(N+1)`.

## Theorem

There are a non-real `u0` and a polynomial `R(u) in u^(N+1) R[u]` such that:

1. `L_j(R)=0` for every `j`;
2. `R(u0)=-Phi(u0)`;
3. for either square root `tau` of `u0`, the function

   `F(t)=Xi(t)+R(t^2)`

   is even, real on the real axis, entire of order `1`, agrees with `Xi` through the
   seam derivatives `0,...,2N+1`, preserves every probe `L_j`, and has the non-real
   zero quartet `tau,-tau,conj(tau),-conj(tau)`.

Thus finite real-linear probe data, finite seam jets, functional-equation parity, and
order-one entire type still do not force RH.

## Proof

Let

`V_N = u^(N+1) R[u]`

and set

`K = {P in V_N : L_j(P)=0 for all j}`.

Since `V_N` is infinite-dimensional and the list of probes is finite, `K` is
infinite-dimensional. Choose two linearly independent real polynomials `P,Q in K`.

The rational function `P/Q` is not constant. If no non-real point had non-real
ratio, then `P(u)/Q(u)` would be real on a nonempty open subset of the upper
half-plane where `Q(u) != 0`. The open mapping theorem would then force `P/Q` to be
constant, contradiction. Hence there is a non-real `u0` with `Q(u0) != 0` and

`P(u0)/Q(u0) notin R`.

Therefore `P(u0)` and `Q(u0)` span `C` over `R`. Choose real `a,b` such that

`a P(u0)+b Q(u0) = -Phi(u0)`.

Set

`R=aP+bQ`.

Then `R in K`, so all probes vanish on the perturbation, and `R` is divisible by
`u^(N+1)`. The value condition gives `R(u0)=-Phi(u0)`.

Now define

`F(t)=Xi(t)+R(t^2)`.

The polynomial `R(t^2)` is even and real on the real axis, so `F` preserves the
functional-equation parity and real symmetry. Its divisibility by `u^(N+1)` makes
`R(t^2)` vanish to order `2N+2` at `t=0`, so `F` agrees with `Xi` through derivatives
`0,...,2N+1` at the seam. Since a polynomial perturbation cannot cancel the
non-polynomial order-one entire function `Xi`, `F` remains order `1`.

Let `tau^2=u0`. Since `u0` is non-real, `tau` is non-real and `tau^2 notin R`. The
value condition gives

`F(tau)=Phi(u0)+R(u0)=0`.

Evenness and real symmetry give the zeros at `-tau`, `conj(tau)`, and `-conj(tau)`.
Thus `F` preserves all finite probe data in the theorem while violating RH.

## Consequence for the RH Route

This theorem strictly strengthens the finite seam-jet guardrail. A finite computation
or finite symbolic audit can be included among the probes; after it is fixed, an
off-line-zero fake remains available unless the audit has already inserted a global
source constraint.

Therefore the RH-bearing step cannot be:

1. a finite Taylor passport;
2. a finite list of moment or value probes;
3. a finite rank-one chart sign;
4. a finite computation that samples the proposed source object.

The proof must consume an infinite/global source structure: Euler product with local
orientation, the completed explicit formula as an all-order object, a geometric
polarization, or an equivalent source-built rigidity theorem.

## Source Boundary

The proof is elementary linear algebra plus the open mapping theorem. It does not
preserve an Euler product, and that limitation is the point: finite probes cannot see
the Euler product as an all-order source object.

This is not claimed as deep mathematics. It is a guardrail against treating finite
observations as proof obligations.

## Gates

- [x] 0 -> 1 in-progress: finite probe route isolated.
- [x] 1 -> 2 fully-proven: finite-codimension perturbation theorem proved.
- [ ] 2 -> 3 formalized: optional Lean version over polynomial vector spaces plus an
  imported complex-analysis lemma.

## Log

- 2026-06-24 -- Professor: created under the RH-only goal after reading
  `docs/consolidated/revision01/big-picture.md`. It sharpens the document's finite
  passport warnings into a reusable finite-probe nonselection theorem.

## 2026-06-24 moment-prefix specialization

`finite-markov-prefix-nonselection.md` is the seam-log moment-coordinate specialization of this finite-probe theorem. It does not perturb `Xi` directly; it works inside the shifted moment sequence and shows that finite Markov/Hankel prefixes cannot decide all-order Stieltjes positivity.

This gives the analytic certificate version of the same rule: finite probes calibrate a route, but they cannot replace the infinite/global source constraint.
