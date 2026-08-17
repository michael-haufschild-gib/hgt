# Finite Jet Faces Are Detected by Bounded Monomial Secant Rank

- **ID:** finite-jet-secant-detection-rank
- **Stage:** 3-formalized / not new scientific knowledge
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
- [x] Formalization: complete.  `GaloisForLFunctions.HTGeometry.MonomialJetSecantRank`
      proves the whole theorem and its sharpness unconditionally; axioms
      `[propext, Classical.choice, Quot.sound]`.

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

Superseded on 2026-08-17: the Jacobian/dominance/density chain is now formalized in full, with
holomorphic openness in place of scheme-theoretic dominance.  See the formalization section below.

## Log

- 2026-07-11 — Proved the finite secant detection ceiling and classified it `[BRIDGE]` under the rational-normal-curve parent theory.

## Lean formalization — 2026-08-17

`formal/GaloisForLFunctions/HTGeometry/MonomialJetSecantRank.lean`, unconditional
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`).

| Paper step | Lean name |
|---|---|
| (1) the monomial-jet curve `v_m(s)` and its derivative | `jetVec`, `jetVecDeriv` |
| (2) the `k`-term jet map `Psi_k` | `jetMap` |
| §1 the Jacobian is confluent Vandermonde | `jetRow`, `jetMapDeriv`, `hasStrictFDerivAt_jetMap`, `jetMapDeriv_single_fst`, `jetMapDeriv_single_snd` |
| §2 (6)-(7): a row functional gives a degree-`m` polynomial with a double root at every node | `dualPoly`, `dual_apply_jetVec`, `dual_apply_jetVecDeriv`, `natDegree_dualPoly_le`, `dualPoly_eq_zero_iff` |
| §2 the Jacobian has rank `m+1` when `2k >= m+1` | `span_jet_eq_top`, `range_jetMapDeriv_eq_top` |
| §3 dominance, Zariski density, polynomial detection | `mvPolynomial_eq_zero_of_hasStrictFDerivAt_surj`, `mvPolynomial_eq_zero_of_eval_jetMap` |
| the theorem at `k_m = ceil((m+1)/2)` | `secantRank`, `secantRank_spec`, `mvPolynomial_eq_zero_of_eval_jetMap_secantRank` |
| (8)-(9): `rho_sec(H) <= ceil((m+1)/2)` | `exists_jetMap_eval_ne_zero` |
| dimension sharpness for `2k < m+1` | `hankelPoly`, `eval_hankelPoly`, `hankelPoly_ne_zero`, `eval_hankelPoly_jetMap`, `exists_ne_zero_vanishing_on_jetMap` |

Two deliberate substitutions, both strengthening the card rather than weakening it:

1. **Density is replaced by openness.**  Instead of "dominant morphism ⇒ dense image ⇒ a vanishing
   polynomial is zero", the Lean proof uses the holomorphic submersion theorem: the differential is
   surjective at a node configuration with distinct `s_i` and nonzero `u_i`, so `jetMap` maps a
   neighbourhood onto a neighbourhood (`HasStrictFDerivAt.map_nhds_eq_of_surj`), and a polynomial
   vanishing on a nonempty open subset of `C^(m+1)` is zero (the corpus's
   `mvPolynomial_eq_zero_of_eqOn_zero_isOpen`).  This avoids scheme-theoretic dominance entirely and
   gives the same conclusion with no hypotheses.
2. **Dimension sharpness is replaced by an explicit witness.**  For `2k <= m` (equivalently
   `2k < m+1`) the card argues by dimension count that the image closure is proper.  The Lean proof
   exhibits the obstruction: the `(k+1) x (k+1)` catalecticant `det (y_(a+b))` is a nonzero
   polynomial (it is a signed permutation matrix at the anti-diagonal jet) which vanishes on every
   `k`-term jet, because the coefficient vector of `prod_i (X - s_i)` is a kernel vector of the
   Hankel matrix.  This is strictly stronger than "dimension at most `2k`".

Not formalized, and not an obligation of this card: the "exact consequence for the super-Gaussian
problem" paragraph, which the card itself marks as an open analytic and arithmetic step.

## Log

- 2026-08-17 Formalized in Lean 4 and promoted to stage 3.  Both halves — the detection theorem at
  `ceil((m+1)/2)` and its sharpness below that rank — are unconditional Lean theorems.
