# Even-index Hermitian additive pole law

- **ID:** `even-index-hermitian-additive-pole-law`
- **Theorem ID:** `PARITY-RAW-001`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** EXACT UNIVERSAL LAW + QUALITATIVE RECURRENCE THEOREM
- **Scientific status:** `[PROVED HERE] [STRICT CORPUS STRENGTHENING]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Headline consequence:** Raw Möbius and Liouville binary additive convolutions are positive for
  infinitely many **even** totals.

## 1. Abstract theorem

Let `(a(n))_(n>=1)` be a complex sequence of polynomial growth and write

```text
A(z)=sum_(n>=1) a(n)z^n,
A#(z)=sum_(n>=1) conjugate(a(n))z^n.                          (1)
```

For `k>=1`, define the Hermitian ordinary-additive coefficient

```text
R_k(N)
 = sum_(n_1+...+n_k+m_1+...+m_k=N)
     product_j a(n_j) product_j conjugate(a(m_j)).             (2)
```

Every variable in `(2)` is a positive integer. Conjugating and exchanging the `n` and `m`
coordinates shows that `R_k(N)` is real. Define the even-index generating function

```text
P_k(u)=sum_(q>=0) R_k(2q)u^q.                                 (3)
```

Then, for every real `0<u<1`, the exact parity law is

```text
P_k(u)
 = (|A(sqrt(u))|^(2k)+|A(-sqrt(u))|^(2k))/2
 >= 0.                                                        (4)
```

In particular,

```text
|A(sqrt(u))|^(2k) <= 2 sum_(q>=0) max(R_k(2q),0)u^q.           (5)
```

Assume in addition that for some Dirichlet series `D(s)` one has the initial Mellin identity

```text
integral_0^infinity A(exp(-x))x^(s-1)dx = Gamma(s)D(s)         (6)
```

in a right half-plane. Let `theta>0` be a pole frontier for `D`: for every `b<theta`, `D` has a
nonremovable pole `rho` with `Re(rho)>b`. Put

```text
Psi_k^even = limsup_(q->infinity)
  log(1+max(R_k(2q),0))/log(q+1).                              (7)
```

Then

```text
Psi_k^even >= max(0,2k theta-1).                              (8)
```

If `D` has even one nonremovable pole in `Re(s)>0`, then

```text
R_k(2q)>0 for infinitely many q.                              (9)
```

The exact law `(4)`, not the order inequality `(8)`, is the universal theorem. Statement `(9)`
is its qualitative pole-theoretic consequence.

## 2. Proof of the exact parity law

Absolute convergence in the unit disc and Cauchy multiplication give

```text
F_k(z):=A(z)^k A#(z)^k = sum_(N>=0) R_k(N)z^N.                (10)
```

For real `r` with `|r|<1`, `A#(r)=conjugate(A(r))`, hence

```text
F_k(r)=|A(r)|^(2k)>=0.                                        (11)
```

The order-two character projector extracts the even coefficients:

```text
(F_k(r)+F_k(-r))/2=sum_(q>=0)R_k(2q)r^(2q).                   (12)
```

Set `u=r^2`. Equations `(11)` and `(12)` prove `(4)`. Dropping the second nonnegative radial
square and then every negative coefficient proves `(5)`.

For `k=1`, split the coefficient sequence into its even and odd parts,

```text
E(u)=sum_(n>=1)a(2n)u^n,
O(u)=sum_(n>=0)a(2n+1)u^n.
```

Then `(4)` has the sharper sum-of-two-squares form

```text
P_1(u)=|E(u)|^2+u|O(u)|^2.                                   (13)
```

Thus the even-index channel is not merely nonnegative after summation; it is an exact parity
Gram decomposition.

## 3. Proof of the pole lower edge

Suppose `2k theta-1>0` and `(8)` fails. Choose

```text
Psi_k^even < lambda < 2k theta-1.                             (14)
```

After absorbing finitely many terms,

```text
max(R_k(2q),0) <= C_lambda(q+1)^lambda.                        (15)
```

Put `u=exp(-2x)` in `(5)`. The standard Abel moment estimate gives

```text
|A(exp(-x))|^(2k)
 <= 2 C_lambda sum_(q>=0)(q+1)^lambda exp(-2qx)
 = O(x^(-lambda-1)).                                         (16)
```

Consequently

```text
A(exp(-x))=O(x^(-b)),  b=(lambda+1)/(2k)<theta.               (17)
```

The Mellin integral in `(6)` now defines a holomorphic continuation of `Gamma(s)D(s)` to
`Re(s)>b`. Since Gamma has no zeros, this contradicts a pole of `D` with real part greater than
`b`. This proves `(8)`; if its displayed right side is nonpositive, the definition gives the
automatic lower bound zero.

For `(9)`, assume only finitely many `R_k(2q)` are positive. The positive-part series on the
right of `(5)` is then a polynomial and is bounded as `u` tends to one. Hence `A(exp(-x))` is
bounded as `x` tends to zero. Polynomial growth of `a(n)` gives exponential decay as `x` tends to
infinity, so `(6)` continues `D` holomorphically throughout `Re(s)>0`, contradicting the assumed
pole. Therefore positive even coefficients recur infinitely often.

## 4. Power-sieved Möbius--Liouville family

For an integer `m>=2`, define the real multiplicative sequence `a_m` by

```text
sum_(n>=1) a_m(n)n^(-s)=zeta(ms)/zeta(s),   Re(s)>1.           (18)
```

Its Euler factor is

```text
(1-p^(-s))/(1-p^(-ms)),
```

so exactly

```text
a_m(p^e)= 1  if e=0 mod m,
          -1  if e=1 mod m,
           0  otherwise.                                     (19)
```

Thus `a_2=lambda`. For every fixed integer `n`, `a_m(n)=mu(n)` once `m` exceeds every prime
exponent in `n`; in this pointwise sense the family terminates at `a_infinity=mu` with
`D_infinity(s)=1/zeta(s)`. The family and Dirichlet identity are classical; no novelty is claimed
for `(18)`--`(19)`.

Let

```text
Theta=sup{Re(rho): zeta(rho)=0, 0<Re(rho)<1}.                 (20)
```

For finite `m`, `zeta(ms)/zeta(s)` has a structural pole at `s=1/m`, because
`zeta(1/m)` is finite and nonzero. It also has a pole at every rightmost nontrivial zeta zero:

- if `Re(rho)>1/2`, then `Re(m rho)>1`, so `zeta(m rho)` is nonzero;
- if `Re(rho)=1/2` and `m>=3`, again `Re(m rho)>1`;
- if `Re(rho)=1/2` and `m=2`, then `2rho` lies on `Re(s)=1` away from `s=1`, where the classical
  zero-free-line theorem makes `zeta(2rho)` finite and nonzero.

Hence the pole frontier of every `D_m`, including `m=infinity`, is exactly `Theta`. Applying the
abstract theorem gives, for all `m in {2,3,...,infinity}` and `k>=1`,

```text
Psi_(m,k)^even >= 2k Theta-1,                                (21)
R_(m,k)(2q)>0 for infinitely many q.                          (22)
```

Because `Theta>=1/2`, for `k>=2` and every `epsilon>0`, `(21)` yields positive even totals with

```text
R_(m,k)(2q) >= q^(k-1-epsilon).                               (23)
```

This power consequence is secondary; the exact parity law and infinite sign recurrence are the
headline results.

## 5. Binary Möbius and Liouville consequences

At `k=1` and `m=infinity`, coefficients are integers. Therefore `(22)` gives

```text
sum_(a+b=2q) mu(a)mu(b) >= 1                                 (24)
```

for infinitely many `q`.

At `k=1` and `m=2`, every summand is `+1` or `-1`, and `(22)` gives

```text
sum_(a+b=2q) lambda(a)lambda(b) >= 1                          (25)
```

for infinitely many `q`. There are `2q-1` ordered positive decompositions of `2q`. Consequently,
for infinitely many even totals, same-sign Liouville pairs form a strict majority over
opposite-sign pairs. This conclusion is unconditional.

The structural pole of `zeta(2s)/zeta(s)` at `s=1/2` already suffices for qualitative recurrence
in `(25)`; no assertion about zeta-zero locations is needed for that endpoint.

## 6. Integrated exact-order companion

The family also fits the already proved integrated positive-part law. Indeed

```text
a_m = mu * 1_(mth powers),
S_m(x):=sum_(n<=x)a_m(n)=sum_(d^m<=x) M(x/d^m).               (26)
```

The classical bound `M(y)=O_epsilon(y^(Theta+epsilon))` and `m Theta>=1` give

```text
S_m(x)=O_epsilon(x^(Theta+epsilon)).                           (27)
```

The pole frontier supplies the reverse obstruction. Therefore the mixed Hermitian `2k`-fold
additive convolution of `S_m` has positive-part order

```text
2k(1+Theta)-1.                                                (28)
```

Statement `(28)` is a specialization of the existing universal integrated theorem, not a second
novelty claim. New candidate content of this card is even-index raw projection `(4)`, recurrence
`(9)`, and arithmetic consequences `(24)`--`(25)`.

## 7. Hostile audit

1. **Not RH and not binary Chowla.** Positive recurrence gives no `o(N)` cancellation and no
   upper half-power source.
2. **Not the existing even-order hierarchy.** Prior corpus theorems use `2k` convolution factors
   but allow every output index. Here the order-two character projector restricts the output to
   the even arithmetic progression. The statements are logically different.
3. **Not a new generalized Liouville function.** The quotient `zeta(ms)/zeta(s)` and its
   coefficients are treated as classical. Only their additive parity consequence is at issue.
4. **No coefficientwise positivity.** Individual `R_k(2q)` may be negative. Positivity appears
   after exact Abel synthesis in `(4)`.
5. **Endpoint is not inferred from exponent zero.** Infinite recurrence uses the separate
   bounded-positive-tail contradiction.
6. **No hidden RH input for Liouville.** Its positive recurrence follows already from the
   structural pole at `1/2`.
7. **No major-open-problem claim.** The sign-majority conclusion appears nontrivial and may be new,
   but it is weaker than the recognized binary correlation/cancellation problems.

## 8. Corpus comparison

- `mobius-even-additive-zero-abscissa-order-law.md`: even convolution **order**, integrated Mertens
  coefficients, all output indices.
- `mobius-even-additive-convolution-hierarchy.md`: same order hierarchy and RH upper wall.
- `raw-mobius-hermitian-positive-excursion-law.md`: raw coefficients and unrestricted output
  indices; `(4)`--`(9)` strictly strengthen it by forcing the even progression.
- `mobius-liouville-square-dilation-wall-preservation.md`: analytic-unit equivalence of the open
  Mellin wall; it contains no raw additive sign theorem.
- `infinite-squarefree-moebius-normalization.md` and `mfree-moebius-ladder-carrier-bridge.md`:
  classical `m`-free quotient family; they contain no parity-projected additive law.

No matching corpus statement was located on 2026-07-22.

## 9. Literature boundary

Current targeted searches located work on Liouville/Möbius additive convolutions, conditional
explicit formulas, strict nonmaximality, local sign patterns, and multi-variable cancellation.
No source has yet been located that states `(4)`, `(24)`, or `(25)`. This is not proof of priority.
Exact phrase/concept searches, primary-source inspection, MathSciNet/Zentralblatt review, and
specialist review remain required before publication language can say “first” or “new.”

## 10. Formalization boundary

Existing Lean already proves the unrestricted Hermitian Cauchy-power identity and positive-part
bound in

```text
formal/GaloisForLFunctions/RHTower/DirichletLMixedAdditiveZeroAbscissaLaw.lean.
```

Only the order-two coefficient projector and even-index connector are genuinely new algebraic
content. The analytic pole and zeta specializations remain paper-level. No broad rebuild is
warranted.

## Gates

- [x] canonical-ledger registration
- [x] exact abstract theorem
- [x] dependency-closed paper proof
- [x] corpus collision audit
- [x] Möbius specialization
- [x] Liouville specialization
- [x] power-sieved family specialization
- [ ] primary-literature collision audit
- [ ] specialist priority review
- [ ] minimal Lean parity connector
- [ ] recognized major open problem solved
- [ ] RH

## Log

- 2026-07-22 — proved exact parity projection, pole lower edge, even-index positive recurrence,
  Möbius/Liouville binary corollaries, and the power-sieved family specialization. Novelty label
  remains suspended pending literature audit.

