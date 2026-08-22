# Super-Gaussian Series Have Arbitrarily Wide Monomial Newton Plateaux

- **ID:** supergaussian-wide-newton-plateau-monomialization
- **Stage:** 2-fully-proven / not new scientific knowledge
- **Type:** THEOREM (paper) / BRIDGE / CONSTRAINT REDUCTION
- **Scientific status:** `[BRIDGE]` — an exact maximum-term convexity theorem whose ADE corollary is the classical Wiman-Valiron dominant-face obstruction
- **Statement:** Faster-than-every-Gaussian Taylor decay forces arbitrarily wide logarithmic-radius intervals on which every fixed jet is exponentially close to one Taylor monomial.

## Goal

Replace exceptional-set Wiman-Valiron approximation by a coefficient-exact monomialization sequence adapted to the super-Gaussian problem. This identifies the first ADE face that must degenerate and isolates the genuinely new higher-osculation step.

## Gates

- [x] Complete unconditional paper proof.
- [x] Uniform approximation proved for every fixed finite jet and every argument on the selected circles.
- [x] Autonomous ADE principal-face corollary proved.
- [x] Parent-theory gate: **FAILS scientific novelty.** The plateau theorem is elementary Newton-envelope theory; the face corollary is contained in the classical Wiman-Valiron dominant-term framework.
- [ ] Formalization: not attempted. The card cannot enter `3-formalized` without a complete unconditional Lean proof of the whole theorem.

## Setup

Let

`f(z)=sum_(n>=0) a_n z^n`

be a transcendental entire function satisfying, for every `A>0`,

`|a_n| <= C_A exp(-A n^2)`.                                                    `(SG)`

For every `n` with `a_n!=0`, put

`ell_n(t)=nt+log|a_n|`,

and let

`Phi(t)=sup_n ell_n(t)=log mu(exp t,f)`

be the logarithm of the maximum term. An index `n` is active when `ell_n=Phi` on a nonempty interval. Write the maximal such interval as

`I_n=[alpha_n,beta_n]`

and its width as `W_n=beta_n-alpha_n`.

## Theorem 1 `[PROVED HERE] [BRIDGE]`

There are active indices `n_k->infinity` such that

`W_(n_k)->infinity`.                                                           `(1)`

Let

`t_k=(alpha_(n_k)+beta_(n_k))/2`, `r_k=exp(t_k)`.

Then, for every fixed derivative order `j>=0`, uniformly for `|z|=r_k`,

`f^(j)(z) / ((n_k)_j a_(n_k) z^(n_k-j)) -> 1`,                                `(2)`

where `(n)_j=n(n-1)...(n-j+1)`. More quantitatively, for every fixed `j` there is `C_j>0` such that the absolute value of the difference from `1` is at most

`C_j exp(-W_(n_k)/3)`                                                         `(3)`

for all sufficiently large `k`.

## Proof

### 1. Bounded plateau width contradicts super-Gaussian decay

List the active indices increasingly as

`m_0<m_1<m_2<...`

and let `tau_i` be the transition slope between `m_i` and `m_(i+1)`. Thus

`tau_i=(b_(m_(i+1))-b_(m_i))/(m_(i+1)-m_i)`,

where `b_n=-log|a_n|`, and the plateau width at `m_i` is `tau_i-tau_(i-1)`.

Suppose all sufficiently late widths were bounded by `B`. Since the number of active indices not exceeding `m_i` is at most `m_i+1`,

`tau_i <= C+B i <= C+B m_i`.                                                   `(4)`

Summing the secant identities gives

`b_(m_i) = b_(m_0)+sum_(h<i) tau_h(m_(h+1)-m_h) <= O(m_i^2)`.                 `(5)`

But `(SG)` gives, for every `A>0`,

`b_(m_i) >= A m_i^2-log C_A`,                                                  `(6)`

contradicting (5) after choosing `A` larger than its implied quadratic constant. Therefore the active plateau widths are unbounded, proving (1) after passage to a subsequence.

The same convex-slope description shows that `t_k/n_k->infinity`. Indeed, the left supporting slope at `n_k` is at least the secant slope from any fixed initial active index to `n_k`, while `(SG)` gives `b_(n_k)/n_k^2->infinity`. Consequently `r_k->infinity` and `n_k/r_k->0`.

### 2. Mid-plateau separation is linear in index distance

Fix an active `n=n_k`, write `W=W_n`, and take `t` at the midpoint of `I_n`. For `m>n`, comparison at the right endpoint `beta_n` gives

`ell_n(t)-ell_m(t) >= (m-n)W/2`.                                               `(7)`

For `m<n`, comparison at the left endpoint gives the same estimate with `|m-n|`. Hence

`|a_m|r^m/(|a_n|r^n) <= exp(-|m-n|W/2)`                                       `(8)`

for every `m!=n`.

### 3. Every finite jet is monomial

Termwise differentiation and (8) give

`|f^(j)(z)-(n)_j a_nz^(n-j)| / |(n)_j a_nz^(n-j)|`

` <= sum_(m!=n) |(m)_j/(n)_j| exp(-|m-n|W/2)`.                                `(9)`

For fixed `j` and large `n`, the falling-factorial ratio grows at most polynomially in `1+|m-n|/n`, while the last factor is geometric in `|m-n|`. The sum in (9) is therefore at most `C_j exp(-W/3)`. This proves (2)-(3). `square`

## Theorem 2: autonomous ADE principal-face degeneracy `[PROVED] [SEARCH]`

Let

`P(Y_0,...,Y_m)=sum_gamma c_gamma product_(j=0)^m Y_j^(gamma_j)`

be a nonzero autonomous differential polynomial with `P(f,f',...,f^(m))=0`. For a monomial indexed by `gamma`, define

`d(gamma)=sum_j gamma_j`,

`w(gamma)=sum_j j gamma_j`.

Let `D=max_gamma d(gamma)` and

`q=min{w(gamma):d(gamma)=D}`.

Then

`sum_(d(gamma)=D, w(gamma)=q) c_gamma = 0`.                                   `(10)`

Equivalently, the top-degree/minimal-weight face of `P` vanishes after the rational-normal-curve substitution

`Y_j |-> X T^j`.

### Proof

At the circles from Theorem 1, put

`x_k=a_(n_k)z^(n_k)`, `eta_k=n_k/z`.

The jet estimate gives `f^(j)(z)=x_k eta_k^j(1+o(1))`. Since `n_k/r_k->0`, terms of degree `D` and weight greater than `q` are negligible relative to `x_k^D eta_k^q`.

Terms of degree less than `D` are also negligible. For every fixed `N`, choose a nonzero Taylor coefficient `a_L` with `L>N`; then `|x_k|=mu(r_k,f)>=|a_L|r_k^L`, so `|x_k|/r_k^N->infinity`. Thus the loss of one power of `x_k` dominates every possible fixed negative power of `eta_k`.

After division by `x_k^D eta_k^q`, the ADE therefore tends to the left side of (10), which must be zero. `square`

## Parent and novelty audit

1. The maximum-term/central-index framework is classical Wiman-Valiron theory.
2. Wittich's dominant-term theorem excludes a transcendental entire solution when the differential polynomial has only one dominant monomial.
3. The standard arbitrary-order refinement groups maximal-degree differential monomials by weight: if every same-weight coefficient sum is nonzero, a transcendental solution has positive order. See W. Bergweiler, P. J. Rippon, and G. M. Stallard, *Dynamics of meromorphic functions with direct or logarithmic singularities*, Theorem 13.1 and its cited entire-function parent. Thus (10) is parent-theory material, not new science.
4. The genuinely open step begins after (10): quantify successive normal derivatives of the face along the rational normal curve when its principal symbol vanishes.

## Successor residue

`[OPEN CORE]` Prove that `(SG)` forces not only (10) but infinite-order vanishing of the dominant ADE face along the monomial-jet curve. Theorem 1 supplies exponentially accurate monomial plateaux, but the first nonzero normal residual may still be larger than the next differential-weight scale. Controlling that comparison is the finite jet-osculation problem.

## Exact heat consequence

Every infinite-spectrum entire-complex-time lattice heat anchor has the monomialization sequence (1)-(3). Hence any proposed autonomous ADE for that anchor must already lie on the Wiman-degenerate face (10). This is a structural restriction, not yet a full HT theorem and not a no-go for the actual de Bruijn-Newman deformation.

## Log

- 2026-07-11 — Proved wide Newton plateaux and uniform finite-jet monomialization; identified the ADE face corollary as classical Wiman-Valiron parent theory.
