# Finite Seam-Jet RH Nonselection

- **ID:** finite-seam-jet-rh-nonselection
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / proof-route guardrail
- **Source:** RH landscape gate; finite-source selection audit
- **Statement:** No finite Taylor jet at the functional-equation seam, even together with
  the exact even functional-equation symmetry and order-one entire type, can force RH.
  For every finite seam jet of the completed `xi` function there is an even real
  order-one entire fake matching that jet and carrying an off-line zero.

## Setup

Let

`Xi(t) = xi(1/2 + i t)`.

Then `Xi` is an even real entire function of order `1`. RH is equivalent to every zero
of `Xi` being real.

This card asks whether a finite seam Taylor prefix plus the exact even symmetry can
select the RH side. It cannot.

## Theorem

Fix `N >= 0`. Let `tau in C \ R` with `tau^2 notin R`, and set `u0=tau^2`.

There exists an even real entire function `F_N(t)` of order `1` such that:

1. `F_N(t)-Xi(t)` has a zero of order at least `2N+2` at `t=0`;
2. equivalently, `F_N^(j)(0)=Xi^(j)(0)` for every `0 <= j <= 2N+1`;
3. `F_N(t)=F_N(-t)` and `F_N(real) subset R`;
4. `F_N(tau)=F_N(-tau)=F_N(conj(tau))=F_N(-conj(tau))=0`.

Thus `F_N` matches the finite seam jet and the functional-equation parity but violates
RH.

## Proof

Since `Xi` is even, write

`Xi(t)=Phi(t^2)`

with `Phi` entire and real on the real axis.

Choose `Q_N(u)=u^(N+1)(a+b u)` with `a,b in R`. We need

1. `Q_N(u)` has a zero of order at least `N+1` at `u=0`;
2. `Q_N(u0)=-Phi(u0)`;
3. `Q_N(conj(u0))=-Phi(conj(u0))`.

The first condition is automatic. For the second, divide by `u0^(N+1)` and solve

`a+b u0 = -Phi(u0)/u0^(N+1)`.

Because `u0` is non-real, the real-linear map `(a,b) |-> a+b u0` from `R^2` to
`C` is invertible. Thus there are unique real `a,b`. Since `Phi` has real Taylor
coefficients, `Phi(conj(u0))=conj(Phi(u0))`; with `a,b` real, the conjugate value
condition follows automatically.

Define

`F_N(t)=Xi(t)+Q_N(t^2)`.

Then `F_N` is even, real on the real axis, and entire. Since `Q_N(t^2)` is a polynomial
and `Xi` has order `1`, the resulting function has order at most `1`; unless the
polynomial cancels `Xi` identically, which is impossible for arbitrary non-polynomial
`Xi`, its order is `1`.

The zero of order `N+1` of `Q_N(u)` at `u=0` implies `Q_N(t^2)` vanishes to order
`2N+2` at `t=0`, proving the seam-jet matching. The value condition gives

`F_N(tau)=Phi(u0)+Q_N(u0)=0`.

Evenness and real symmetry give the other three zeros. Since `tau notin R`, `F_N` has a
non-real zero and therefore fails RH.

## Consequence for the RH Route

This theorem does not use the Euler product and does not approximate `xi` as a source
object. That is exactly the point: any proof route whose decisive data are only a finite
seam Taylor prefix, parity under `t -> -t`, and order-one entire type cannot prove RH.

The source-built proof must consume an infinite/global source constraint: the full
Euler product, the completed explicit formula, a geometric polarization, or an
equivalent all-order object. A finite seam passport is compatible with both RH and
off-line-zero worlds.

In the landscape gate vocabulary, this is a finite-passport blindness theorem. It
strengthens the rank-one-selector guardrail: not only does a finite rank-one chart have
no hidden selector, finite seam-local data do not even determine the correct side of
the divisor geometry.

## Source Boundary

The proof is elementary Hermite interpolation plus the standard parity form of the
completed `xi` function. It is not claimed as deep mathematics. Its role is to prevent
a false proof shape: finite local seam agreement cannot be promoted into source-built
RH rigidity.

## Gates

- [x] 0 -> 1 in-progress: finite seam data identified as a possible false selector.
- [x] 1 -> 2 fully-proven: Hermite-interpolation fake constructed.
- [x] 2 -> 3 formalized: `RHTower/FiniteProbeRHNonselection.lean`.

## Log

- 2026-06-24 -- Professor: created under the RH-only goal. Entropy draw `strengthen` /
  `river-meanders`: strengthen the finite rank-one crossing guardrail to a finite
  seam-passport nonselection theorem.

## 2026-08-16 Lean closure

`RHTower/FiniteProbeRHNonselection.lean` builds the perturbation construction on the actual
centered completed function, unconditionally.

`xiPerturbed R t = XiC t + R(t^2)` is `Xi_R`.  Its structural clauses are proved once and for all:

- `xiPerturbed_even`: `Xi_R(-t) = Xi_R(t)`, the functional-equation parity.
- `xiPerturbed_conj` and `xiPerturbed_ofReal_im`: Schwarz reality, and `Xi_R` real on the real axis.
- `xiPerturbed_differentiable`: `Xi_R` is entire.
- `xiPerturbed_order`: `Xi_R` carries the same order-one envelope
  `||Xi_R(t)|| <= exp(C (1 + ||t||) log(2 + ||t||))` that the corpus proves for `xi`
  (`XiC_order`, from `xi_growth_order_le_one`).  Moreover `xiPerturbed_sub_XiC` shows
  `Xi_R - Xi` is a polynomial function, so `Xi_R` lies in exactly the same growth class as `Xi`;
  that is the content of the cards' "entire of order 1" clause, and it is proved without any
  lower bound on the order of `xi`.
- `xiPerturbed_seamJet`: if `X^(N+1)` divides `R` then `Xi_R - Xi` equals `t^(2N+2)` times an
  entire function, i.e. it vanishes to order at least `2N+2` at the seam.  This is clause 1 of the
  seam-jet statement; the derivative reformulation `Xi_R^(j)(0) = Xi^(j)(0)` for `j <= 2N+1` is the
  standard restatement of the same divisibility.

The two algebraic inputs are proved from scratch:

- `exists_indep_pair_of_finiteCodim`: for any real subspace of finite codimension `<= m` in
  `R[X]` and any `N`, the slice `W cap X^(N+1) R[X]` contains two `R`-independent polynomials.
  The proof is a rank count on the `m+2` monomials `X^(N+1), ..., X^(N+m+2)` followed by an
  elementary extraction of a second vector outside the span of the first.
- `exists_nonreal_spanning`: two `R`-independent real polynomials take, at some non-real point,
  values spanning `C` over `R`.  **The card's open-mapping step is replaced by an algebraic
  argument**: if the values were `R`-dependent at every non-real point, then for each real shift
  `c` the polynomial `P(z - ic) Q(z + ic) - P(z + ic) Q(z - ic)` would vanish on the whole real
  axis, hence identically; evaluating it at `z = a + ic` shows `P(a) Q - Q(a) P = 0` for every
  complex `a`, and a real point where `Q` does not vanish forces `P` and `Q` proportional.

Axioms of every theorem listed: `propext`, `Classical.choice`, `Quot.sound`.

Card-specific.  `exists_offLine_perturbation_prescribed` is the card's theorem in its exact form:
the quartet point is prescribed.  For any `tau` with `tau^2` non-real and any `N`, the explicit
two-term perturbation `R = a X^(N+1) + b X^(N+2)` with real `a, b` solving
`a u^(N+1) + b u^(N+2) = -Xi(tau)`, `u = tau^2`, does the job; solvability is the identity
`Im(conj(u^(N+1)) u^(N+2)) = normSq(u)^(N+1) Im(u) != 0`.
