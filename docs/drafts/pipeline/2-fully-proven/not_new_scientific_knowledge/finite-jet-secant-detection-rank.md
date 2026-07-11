# Finite Jet Faces Are Detected by Bounded Monomial Secant Rank

- **ID:** finite-jet-secant-detection-rank
- **Stage:** 2-fully-proven / not new scientific knowledge
- **Type:** THEOREM (paper) / BRIDGE / ALGEBRAIC CONSTRAINT
- **Scientific status:** `[BRIDGE]` — the classical secant-dimension theorem for the rational normal curve, proved directly by a confluent Vandermonde Jacobian
- **Statement:** Every nonzero polynomial on order-`m` jet space is nonzero on a sum of at most `ceil((m+1)/2)` monomial jets.

## Goal

Give a finite algebraic ceiling to the Newton-cluster attack on the super-Gaussian DA problem. The theorem shows that unbounded cluster rank is unnecessary: for an ADE of fixed differential order, a bounded number of genuinely variable monomial directions already detects every nonzero jet face.

## Gates

- [x] Complete unconditional paper proof.
- [x] Sharp dimension threshold identified.
- [x] Direct Jacobian proof supplied.
- [x] Parent-theory gate: **FAILS scientific novelty.** This is the standard secant-variety dimension of a rational normal curve.
- [ ] Formalization: not attempted. The card cannot enter `3-formalized` without a complete unconditional Lean proof of the whole theorem.

## Setup

Fix `m>=0` and define the affine monomial-jet curve

`v_m(s)=(1,s,s^2,...,s^m) in C^(m+1)`.                                      `(1)`

For `k>=1`, define the `k`-term jet map

`Psi_k((u_i,s_i)_(1<=i<=k))=sum_(i=1)^k u_i v_m(s_i)`.                       `(2)`

This is the order-`m` Euler jet at `x=0` of the exponential polynomial

`F(x)=sum_(i=1)^k u_i exp(s_i x)`.

Under `z=exp x`, integer values `s_i=n_i` are ordinary monomial exponents.

## Theorem `[PROVED HERE] [BRIDGE]`

Let

`k_m=ceil((m+1)/2)`.

Then `Psi_(k_m)` has Zariski-dense image in `C^(m+1)`. Consequently, for every nonzero polynomial

`H in C[Y_0,...,Y_m]`,

the polynomial

`H(Psi_(k_m)(u_1,s_1,...,u_(k_m),s_(k_m)))`                                  `(3)`

is not identically zero.

Equivalently, some sum of at most `k_m` monomial jets detects `H`.

The bound is dimension-sharp: for `2k<m+1`, the Zariski closure of the image of `Psi_k` has dimension at most `2k<m+1` and therefore cannot fill jet space.

## Proof

### 1. The Jacobian is confluent Vandermonde

Choose pairwise distinct complex numbers `s_1,...,s_k` and nonzero amplitudes `u_1,...,u_k`. The two Jacobian columns associated with `(u_i,s_i)` are

`partial_(u_i) Psi_k = v_m(s_i)`,

`partial_(s_i) Psi_k = u_i v_m'(s_i)`.                                       `(4)`

After rescaling the second column in each pair by `u_i^(-1)`, the Jacobian is the truncated confluent Vandermonde matrix

`[v_m(s_1),v_m'(s_1),...,v_m(s_k),v_m'(s_k)]`.                               `(5)`

### 2. The Jacobian has maximal possible rank

Suppose a row functional represented by a polynomial

`p(T)=c_0+c_1T+...+c_mT^m`

annihilates every column in (5). Then

`p(s_i)=p'(s_i)=0`                                                            `(6)`

for all `i`. Thus `p` is divisible by

`product_(i=1)^k (T-s_i)^2`,                                                  `(7)`

which has degree `2k`.

If `2k>=m+1`, a polynomial of degree at most `m` satisfying (7) is zero. Hence the rows of (5) are independent and the Jacobian has rank `m+1`.

For `k=k_m`, the inequality `2k>=m+1` holds. Therefore `Psi_(k_m)` is a dominant polynomial map, and its image is Zariski dense in `C^(m+1)`.

### 3. Polynomial detection

If (3) were the zero polynomial, `H` would vanish on the image of `Psi_(k_m)` and hence on its Zariski closure, which is all of `C^(m+1)`. This would force `H=0`, contrary to hypothesis.

For `2k<m+1`, the source of `Psi_k` has dimension `2k`, so its image closure has dimension at most `2k`; this proves dimension sharpness. `square`

## Secant detection rank

For nonzero `H`, define

`rho_sec(H)=min{k>=1 : H o Psi_k is not identically zero}`.                   `(8)`

Then

`1 <= rho_sec(H) <= ceil((m+1)/2)`.                                           `(9)`

If the leading ADE face vanishes on every monomial jet, then `rho_sec(H)>=2`. Thus `rho_sec` measures how many simultaneous Taylor directions are required before that face becomes visible.

No scientific novelty is claimed for (8)-(9); it is a convenient constraint coordinate on the standard secant filtration.

## Exact consequence for the super-Gaussian problem

The algebraic branch of the Newton-cluster attack is now finite. For a candidate ADE of order `m`, it suffices to produce asymptotically generic clusters of at most `ceil((m+1)/2)` Taylor monomials. Such clusters would force its dominant face to vanish identically.

The remaining open step is analytic and arithmetic: super-Gaussian decay gives arbitrarily wide one-monomial plateaux, but it does not yet prove that the actual transition clusters are Zariski dense in the parameter space of `Psi_(k_m)`. A single sequence may remain trapped in a proper algebraic transition locus.

## Parent and literature audit

1. Projectively, the closure of the image of `Psi_k` is the `k`-secant variety of the rational normal curve.
2. Its dimension is `min(2k-1,m)` in projective space, equivalently `min(2k,m+1)` for the affine cone used here.
3. The confluent Vandermonde proof above is a direct proof of this classical fact, not a new scientific mechanism.

## Lean boundary

The project contains generic multivariate-polynomial and minimal-total-degree infrastructure, but not the complete Jacobian/dominance/Zariski-density chain needed for this theorem. A partial Vandermonde wrapper would not formalize the whole card and therefore does not justify movement to `3-formalized`.

## Log

- 2026-07-11 — Proved the finite secant detection ceiling and classified it `[BRIDGE]` under the rational-normal-curve parent theory.
