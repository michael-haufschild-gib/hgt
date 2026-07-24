# Raw Möbius Hermitian positive-excursion law

- **ID:** `raw-mobius-hermitian-positive-excursion-law`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [UNCONDITIONAL] [NOT RH]`
- **Dominance status:** strict even-index strengthening proved in
  `even-index-hermitian-additive-pole-law.md`; do not reuse unrestricted recurrence as newest claim.
- **Source:** ordinary generating function of reciprocal Dirichlet coefficients / Mellin pole
  obstruction
- **Statement:** Raw Hermitian additive convolutions of twisted Möbius coefficients have
  infinitely many positive values.  At every order at least four, their positive excursions have
  an unconditional power-law lower order.  In particular, the binary additive Möbius
  self-convolution is positive infinitely often.

## Statement

Let `chi` be a fixed primitive Dirichlet character and put

```text
a_chi(n)=mu(n)chi(n),
A_chi(z)=sum_(n>=1) a_chi(n)z^n.
```

For `k>=1`, define the raw Hermitian `2k`-fold additive convolution

```text
R_(chi,k)(N)
 = sum_(n_1+...+n_k+m_1+...+m_k=N)
     product_j a_chi(n_j) product_j conjugate(a_chi(m_j)).       (R1)
```

All coordinates in `(R1)` are positive integers.  The coefficient is real.  Let

```text
Psi_(chi,k)=limsup_(N->infinity)
  log(1+max(R_(chi,k)(N),0))/log(N+1),                           (R2)
```

and let `Theta_chi` be the supremum of the real parts of the nontrivial zeros of
`L(s,chi)`.  Then

```text
2k Theta_chi-1 <= Psi_(chi,k) <= 2k-1.                           (R3)
```

Moreover,

```text
R_(chi,k)(N)>0 for infinitely many N, for every k>=1.            (R4)
```

Functional-equation symmetry gives `Theta_chi>=1/2`.  Consequently, for every `k>=2`
and every `epsilon>0`,

```text
R_(chi,k)(N)=Omega_+(N^(k-1-epsilon)).                           (R5)
```

For a real primitive character, including the conductor-one zeta case, `(R4)` is an
`Omega_+(1)` statement because every coefficient is an integer.  In particular,

```text
sum_(a+b=N) mu(a)mu(b) >= 1                                    (R6)
```

for infinitely many positive integers `N`.

This is not an upper bound and does not prove binary Chowla cancellation or RH.

## Exact radial law

For real `0<r<1`, absolute convergence and Cauchy multiplication give

```text
sum_(N>=1) R_(chi,k)(N) r^N = |A_chi(r)|^(2k) >= 0.              (R7)
```

Hence

```text
|A_chi(r)|^(2k)
 <= sum_(N>=1) max(R_(chi,k)(N),0) r^N.                         (R8)
```

The exact Mellin identity in `Re(s)>1` is

```text
integral_0^infinity A_chi(exp(-x)) x^(s-1) dx
 = Gamma(s)/L(s,chi).                                          (R9)
```

Unlike a norm estimate, `(R8)` discards all negative raw correlations while retaining enough
radial information to detect every pole of `1/L`.

## Proof of the exponent lower bound

Suppose first that `2k Theta_chi-1>0` and that the lower inequality in `(R3)` fails.  Choose

```text
Psi_(chi,k) < lambda < 2k Theta_chi-1.
```

The limsup definition gives

```text
max(R_(chi,k)(N),0) <= C_lambda (N+1)^lambda.                   (R10)
```

Set `r=exp(-x)`, `0<x<=1`.  The standard exponential-moment bound and `(R8)` imply

```text
|A_chi(exp(-x))|^(2k) = O(x^(-lambda-1)),
|A_chi(exp(-x))| = O(x^(-b)),
b=(lambda+1)/(2k) < Theta_chi.                                 (R11)
```

The function

```text
H(s)=1/Gamma(s) integral_0^infinity
       A_chi(exp(-x)) x^(s-1) dx                               (R12)
```

is therefore holomorphic in `Re(s)>b`.  Equation `(R9)` and the identity theorem give
`H(s)L(s,chi)=1` there.  By the definition of `Theta_chi`, there is a nontrivial zero `rho`
with `Re(rho)>b`, contradicting evaluation at `rho`.  Thus the lower bound holds when its
right side is positive.  When `2k Theta_chi-1<=0`, it follows from the automatic inequality
`Psi_(chi,k)>=0`.

The upper bound in `(R3)` is elementary: `(R1)` has at most `(N+1)^(2k-1)` summands and every
summand has modulus at most one.

For `k>=2`, symmetry `Theta_chi>=1/2` and `(R3)` give
`Psi_(chi,k)>=k-1>0`; the definition of limsup gives `(R5)`.

## Proof of positive recurrence at the binary endpoint

The exponent statement alone is insufficient when `k=1` and `Theta_chi=1/2`, because the
right side of `(R3)` is zero.  A separate endpoint argument gives `(R4)` at every order.

Assume only finitely many `R_(chi,k)(N)` are positive.  Then the positive-part series in `(R8)`
is a polynomial and is uniformly bounded for `0<r<1`.  Therefore `A_chi(r)` is bounded as
`r` tends to one.  Since `A_chi(exp(-x))` decays exponentially as `x` tends to infinity,
`(R12)` is now holomorphic throughout `Re(s)>0`.  But `(R9)` would continue `1/L(s,chi)`
holomorphically across every nontrivial zero.  Primitive Dirichlet `L`-functions have
nontrivial zeros in the critical strip, a contradiction.  Thus positive coefficients recur
infinitely often.

## Relation to the exact Mertens-convolution law

Let `M_chi(N)=sum_(n<=N)a_chi(n)` and let `C_(chi,k)` be its mixed `2k`-fold convolution.
Ordinary generating functions give the exact integration law

```text
sum_N C_(chi,k)(N)z^N
 = (1-z)^(-2k) sum_N R_(chi,k)(N)z^N.                           (R13)
```

Equivalently,

```text
C_(chi,k)(N)
 = sum_(j<=N) binom(N-j+2k-1,2k-1) R_(chi,k)(j).               (R14)
```

The companion theorem

```text
limsup log(1+[C_(chi,k)(N)]_+)/log(N+1)
 = 2k(1+Theta_chi)-1                                          (R15)
```

is exact because the classical twisted Littlewood theorem also supplies the matching upper
bound for `M_chi`.  The raw theorem `(R3)` supplies only the lower spectral edge; proving a
matching critical upper edge for raw binary convolution is substantially stronger and remains
open.

## Hostile audit

1. **Not RH.**  `(R3)` detects a lower edge forced by existing zeros; it does not prove
   `Theta_chi=1/2`.
2. **Not binary Chowla.**  Positive recurrence gives neither `o(N)` nor cancellation in
   `sum_(a+b=N)mu(a)mu(b)`.
3. **Not an estimate in disguise.**  Core statements `(R4)` and `(R7)` are qualitative/exact;
   `(R3)` is an order law.  The higher-order omega corollary is a consequence, not the source
   theorem.
4. **No simplicity, RH, LI, or zero-density assumption.**  A single nontrivial zero suffices
   for `(R4)`; the full zero frontier gives `(R3)`.
5. **Endpoint handled separately.**  `Psi>=0` alone would not prove infinitely many positive
   binary coefficients.  The bounded-positive-tail argument is essential.
6. **Complex characters handled Hermitianly.**  Plain even powers would not be nonnegative for
   complex coefficients.  Conjugate pairing gives the real coefficients and `(R7)`.

## Literature boundary

Targeted corpus and external searches through 2026-07-22 found no statement of `(R3)`--`(R6)`.
The closest sources are:

- M. Cantarini, A. Gambini and A. Zaccagnini, *On the discrete convolution of the Liouville and
  Möbius functions*, arXiv:2603.10241 (2026), derive weighted explicit formulas for raw
  Liouville and Möbius convolutions under RH and simplicity assumptions.  Their paper does not
  state unconditional positive recurrence or the one-sided exponent lower law.
- W. D. Banks and I. E. Shparlinski, *Multiple sums with the Möbius function*, Q. J. Math. 77
  (2026), 109--127, explicitly note that binary versions of their nontrivial cancellation bounds
  remain out of reach.  `(R6)` is a weaker sign-recurrence theorem, not such a cancellation
  bound.
- J. Kaczorowski and A. Perelli, *General Omega-theorems for coefficients of L-functions*,
  Proc. Amer. Math. Soc. 143 (2015), 5139--5145, concern Dirichlet coefficients of polynomial
  combinations of Selberg-class `L`-functions.  The coefficients in `(R1)` are ordinary-additive
  Cauchy convolutions of reciprocal coefficients, so their theorem is not `(R3)`.
- Classical Littlewood and modern Hardy--Littlewood--Riesz criteria control linear reciprocal
  sums or smoothed transforms and supply neighboring Mellin methodology, not positive parts of
  raw additive convolutions.

Negative search is not proof of priority.  Specialist review and MathSciNet/Zentralblatt searches
remain required before any priority claim.

## Significance verdict

The theorem gives a first candidate unconditional sign law on the raw binary additive Möbius
convolution and a universal higher-order positive-excursion law for every primitive Dirichlet
character.  It is directly adjacent to an active binary frontier and uses neither RH nor the
conditional explicit formulas currently used for this object.

It does **not** solve a recognized major open problem such as binary Chowla, GRH, or RH.  Current
classification is `CANDIDATE NEW SCIENTIFIC KNOWLEDGE`, not `MAJOR OPEN PROBLEM SOLVED`.

## Formal certificate

The existing Lean module

```text
formal/GaloisForLFunctions/RHTower/DirichletLMixedAdditiveZeroAbscissaLaw.lean
```

already formalizes the exact generic algebraic core needed here:

- `mixedAdditiveConvolutionPower` is `(R1)` for an arbitrary complex sequence;
- `star_mixedAdditiveConvolutionPower` and
  `mixedAdditiveConvolutionPower_im_eq_zero` prove reality;
- `pow_mul_star_pow_eq_tsum_mixedAdditiveConvolutionPower_mul_pow` proves `(R7)`;
- `norm_sq_pow_le_tsum_of_mixedAdditiveConvolutionPower_upper` formalizes `(R8)`.

The Dirichlet character, nontrivial-zero, Mellin-continuation, and limsup layers remain
paper-level.  No duplicate Lean wrapper is warranted.

## Gates

- [x] corpus search
- [x] exact theorem and endpoint proof
- [x] complex-character audit
- [x] initial 2025--2026 collision search
- [x] dependency-closed paper proof
- [x] generic Hermitian Abel core already formalized
- [ ] specialist priority review
- [ ] MathSciNet/Zentralblatt search
- [ ] full analytic Lean formalization
- [ ] binary Chowla cancellation
- [ ] RH

## Log

- 2026-07-22 -- derived raw Hermitian radial law from existing mixed Abel core; proved the
  zero-frontier lower exponent, unconditional higher-order positive excursions, and separate
  binary endpoint positive recurrence; audited closest 2015, 2025, and 2026 literature.
- 2026-07-22 -- superseded as publication headline by `PARITY-RAW-001`, which proves the same
  lower edge and recurrence on even output indices and contains a dyadic Gram refinement.

## Log

- 2026-07-24 — Formalization audit + capstone. The convolution-power norm bounds underlying the `(R3)`
  upper bound `Ψ_{χ,k} ≤ 2k-1` are already in the corpus (`RHTower/MobiusMertensEvenConvolutionOrderLaw.lean`:
  `additiveConvolutionPower_one`, `norm_additiveConvolutionPower_succ_le`; and the one-sided order
  comparisons `norm_pow_even_mobiusDiscreteLaplaceTransform_le_of_evenConvolutionUpper` /
  `...SubpowerUpperBound`).  Formalized the reusable analytic **capstone** for the `Ψ ≤ d` order shape
  (`HTGeometry/LogOrderLimsupBound.lean`, unconditional, axioms `[propext, Classical.choice, Quot.sound]`):
  * `limsup_log_one_add_div_log_le` — for `0 ≤ f N ≤ C·(N+1)^d`,
    `limsup_N log(1 + f N)/log(N+1) ≤ d`.
  With `f N = max(R_{χ,k}(N), 0)` bounded by the binomial term count `~ N^{2k-1}` (via the existing norm
  bounds), this yields the `(R3)` upper bound `Ψ_{χ,k} ≤ 2k-1`.  The lower bound `2kΘ_χ - 1 ≤ Ψ` and the
  positivity `(R4)` remain the analytic/`L`-zero direction (the abstract `(9)` route is formalized in
  `even-index-hermitian-additive-pole-law` via `frequently_re_pos_of_dirichletPole`; the concrete claim
  needs a pole of `1/L(s,χ)` in `Re s > 0`, i.e. an `L`-function zero).
- 2026-07-24 — **`(R3)` upper bound `Ψ_{χ,k} ≤ 2k-1` formalized** abstractly
  (`RHTower/EvenIndexHermitianOrderUpperBound.lean`, unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`), for any unit-bounded coefficient sequence
  (`∀ n, ‖a n‖ ≤ 1`):
  * `norm_additiveConvolutionPower_succ_le_pow` — `‖C_{j+1}(N)‖ ≤ (N+1)^j` (the corpus convolution
    estimate at `A = 1`, `α = 0`).
  * `norm_mixedAdditiveConvolutionPower_le_pow` — `‖R_{j+1}(N)‖ ≤ (N+1)^{2j+1}` (antidiagonal sum of
    the leg bounds; the composition count).
  * `limsup_log_mixedAdditiveConvolutionPower_re_le` —
    `limsup_N log(1 + max(Re R_{j+1}(N), 0))/log(N+1) ≤ 2j+1`, i.e. `Ψ_{χ,j+1} ≤ 2(j+1)-1`, via the
    log-order limsup capstone `HTGeometry.limsup_log_one_add_div_log_le`.
  The lower bound `2kΘ_χ - 1 ≤ Ψ` and the positivity `(R4)` remain the analytic `L`-zero direction
  (the abstract `(9)`/`(R4)` route is formalized in `even-index-hermitian-additive-pole-law` via
  `frequently_re_pos_of_dirichletPole`; the concrete claim needs a pole of `1/L(s,χ)` in `Re s > 0`).
