# Even-index Hermitian additive pole law

- **ID:** `even-index-hermitian-additive-pole-law`
- **Theorem ID:** `PARITY-RAW-001`
- **Stage:** 3-formalized / needs-literature-audit
- **Type:** EXACT UNIVERSAL LAW + QUALITATIVE RECURRENCE THEOREM
- **Scientific status:** `[PROVED HERE] [STRICT CORPUS STRENGTHENING]`
  `[LEAN-FORMALIZED UNCONDITIONALLY: (4),(5),(8),(9),(13),(20),(21),(24),(25),(26),(35)]`
  `[MOEBIUS ENDPOINT (34) FORMALIZED VIA AN UNCONDITIONAL NONTRIVIAL ZETA ZERO]`
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

## 4. Dyadic Gram refinement for completely multiplicative sequences

Suppose now that `f` is completely multiplicative, complex-valued, and of polynomial growth.
Write

```text
F(r)=sum_(n>=1)f(n)r^n,
c=f(2),
H_f(N)=sum_(a+b=N) f(a)conjugate(f(b)).                       (18)
```

Complete multiplicativity gives an exact dyadic renormalization:

```text
F(r)+F(-r)
 = 2 sum_(n even)f(n)r^n
 = 2c F(r^2).                                                  (19)
```

Substitution into the binary case of `(4)` yields the **dyadic Gram law**

```text
sum_(q>=0) H_f(2q)r^(2q)
 = |F(r)-cF(r^2)|^2 + |cF(r^2)|^2.                            (20)
```

Indeed, the left side is

```text
(|F(r)|^2+|F(-r)|^2)/2
 = (|F(r)|^2+|2cF(r^2)-F(r)|^2)/2,
```

and the parallelogram expansion gives `(20)`. Thus the even additive channel of every completely
multiplicative sequence is the sum of two adjacent dyadic squares. This is stronger than radial
nonnegativity and exposes the local factor at `2` exactly.

For the Liouville function, `c=-1`, so

```text
sum_(q>=0) (sum_(a+b=2q)lambda(a)lambda(b)) r^(2q)
 = (F_lambda(r)+F_lambda(r^2))^2 + F_lambda(r^2)^2.            (21)
```

The identity is algebraic and unconditional. A targeted corpus and external search found no
statement of `(20)` or its pole-theoretic sign consequence, but its priority remains unverified.

## 5. Dyadic orbit classification and exact source blindness

The Gram law has a sharp converse description. It needs only the local recursion

```text
a(2n)=c a(n),                                                 (22)
```

not full multiplicativity. Let

```text
O(r)=sum_(n odd)a(n)r^n                                      (23)
```

be the free odd-index seed. Splitting even and odd coefficients gives

```text
A(r)=O(r)+cA(r^2).                                           (24)
```

Iterating `(24)` yields the exact orbit classification

```text
A(r)=sum_(j>=0)c^j O(r^(2^j)),   0<r<1.                      (25)
```

The terminal remainder `c^J A(r^(2^J))` tends to zero because `r^(2^J)` decays doubly
exponentially. Conversely, every odd power series `O` in `(25)` produces the unique sequence
satisfying `(22)`. Therefore the dyadic identity leaves the entire odd seed free; it cannot by
itself create an upper source estimate.

The Gram law becomes the orthogonal channel decomposition

```text
sum_q H_a(2q)r^(2q)=|O(r)|^2+|cA(r^2)|^2.                    (26)
```

At the Dirichlet-series level, writing `D_odd` for the odd-index series gives

```text
D(s)=D_odd(s)/(1-c 2^(-s)),
D_odd(s)=(1-c 2^(-s))D(s).                                  (27)
```

For Liouville, `c=-1`; the multiplier `1+2^(-s)` has all its zeros on `Re(s)=0` and is an
analytic unit on `Re(s)>0`. Thus the odd seed and the full Liouville series have exactly the same
right-half pole divisor. The dyadic Gram law exposes two nonnegative channels, but neither channel
removes the Mellin wall. A new upper theorem for the odd seed (or for the even-convolution
positive coefficients) remains necessary.

This is a dependency-closed no-go, not a failure of the exact parity theorem. Its positive
survivor is the orbit classification `(25)` and the orthogonal decomposition `(26)`.

## 6. Power-sieved Möbius--Liouville family

For an integer `m>=2`, define the real multiplicative sequence `a_m` by

```text
sum_(n>=1) a_m(n)n^(-s)=zeta(ms)/zeta(s),   Re(s)>1.           (28)
```

Its Euler factor is

```text
(1-p^(-s))/(1-p^(-ms)),
```

so exactly

```text
a_m(p^e)= 1  if e=0 mod m,
          -1  if e=1 mod m,
           0  otherwise.                                     (29)
```

Thus `a_2=lambda`. For every fixed integer `n`, `a_m(n)=mu(n)` once `m` exceeds every prime
exponent in `n`; in this pointwise sense the family terminates at `a_infinity=mu` with
`D_infinity(s)=1/zeta(s)`. This is de Camargo's generalized Liouville function `lambda_m`, the
Dirichlet inverse of the `m`-free indicator. The family and Dirichlet identity are known; no
novelty is claimed for `(28)`--`(29)`.

Let

```text
Theta=sup{Re(rho): zeta(rho)=0, 0<Re(rho)<1}.                 (30)
```

For finite `m`, `zeta(ms)/zeta(s)` has a structural pole at `s=1/m`. To see that the denominator
does not cancel it, use

```text
zeta(s)=eta(s)/(1-2^(1-s)).
```

For real `0<s<1`, the alternating-series value `eta(s)` is positive while the denominator is
negative, so `zeta(s)` is finite and nonzero. The quotient also has a pole at every rightmost
nontrivial zeta zero:

- if `Re(rho)>1/2`, then `Re(m rho)>1`, so `zeta(m rho)` is nonzero;
- if `Re(rho)=1/2` and `m>=3`, again `Re(m rho)>1`;
- if `Re(rho)=1/2` and `m=2`, then `2rho` lies on `Re(s)=1` away from `s=1`, where the classical
  zero-free-line theorem makes `zeta(2rho)` finite and nonzero.

Hence the pole frontier of every `D_m`, including `m=infinity`, is exactly `Theta`. Applying the
abstract theorem gives, for all `m in {2,3,...,infinity}` and `k>=1`,

```text
Psi_(m,k)^even >= 2k Theta-1,                                (31)
R_(m,k)(2q)>0 for infinitely many q.                          (32)
```

Because `Theta>=1/2`, for `k>=2` and every `epsilon>0`, `(31)` yields positive even totals with

```text
R_(m,k)(2q) >= q^(k-1-epsilon).                               (33)
```

This power consequence is secondary; the exact parity law and infinite sign recurrence are the
headline results.

## 7. Binary Möbius and Liouville consequences

At `k=1` and `m=infinity`, coefficients are integers. Therefore `(32)` gives

```text
sum_(a+b=2q) mu(a)mu(b) >= 1                                 (34)
```

for infinitely many `q`.

At `k=1` and `m=2`, every summand is `+1` or `-1`, and `(32)` gives

```text
sum_(a+b=2q) lambda(a)lambda(b) >= 1                          (35)
```

for infinitely many `q`. There are `2q-1` ordered positive decompositions of `2q`. Consequently,
for infinitely many even totals, same-sign Liouville pairs form a strict majority over
opposite-sign pairs. This conclusion is unconditional.

The structural pole of `zeta(2s)/zeta(s)` at `s=1/2` already suffices for qualitative recurrence
in `(35)`; no assertion about zeta-zero locations is needed for that endpoint.

## 8. Integrated exact-order companion

The family also fits the already proved integrated positive-part law. Indeed

```text
a_m = mu * 1_(mth powers),
S_m(x):=sum_(n<=x)a_m(n)=sum_(d^m<=x) M(x/d^m).               (36)
```

The classical bound `M(y)=O_epsilon(y^(Theta+epsilon))` and `m Theta>=1` give

```text
S_m(x)=O_epsilon(x^(Theta+epsilon)).                           (37)
```

The pole frontier supplies the reverse obstruction. Therefore the mixed Hermitian `2k`-fold
additive convolution of `S_m` has positive-part order

```text
2k(1+Theta)-1.                                                (38)
```

Statement `(38)` is a specialization of the existing universal integrated theorem, not a second
novelty claim. New candidate content of this card is even-index raw projection `(4)`, recurrence
`(9)`, dyadic Gram law `(20)`, orbit classification `(25)`, and arithmetic consequences
`(34)`--`(35)`.

## 9. Hostile audit

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

## 10. Corpus comparison

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

## 11. Literature boundary

Current targeted searches located work on Liouville/Möbius additive convolutions, conditional
explicit formulas, strict nonmaximality, local sign patterns, and multi-variable cancellation.
No source has yet been located that states `(4)`, `(20)`, `(25)`, `(34)`, or `(35)`. This is not proof of
priority.
Exact phrase/concept searches, primary-source inspection, MathSciNet/Zentralblatt review, and
specialist review remain required before publication language can say “first” or “new.”

## 12. Formalization boundary

Existing Lean already proves the unrestricted Hermitian Cauchy-power identity and positive-part
bound in

```text
formal/GaloisForLFunctions/RHTower/DirichletLMixedAdditiveZeroAbscissaLaw.lean.
```

The new module

```text
formal/GaloisForLFunctions/RHTower/DirichletLMixedAdditiveEvenIndexLaw.lean
```

now proves:

- `add_pos_neg_hermitianAbel_eq_two_mul_tsum_evenIndex`, the exact projector `(4)` before taking
  real parts;
- `re_tsum_evenIndex_mixedAdditiveConvolutionPower_nonneg`, the formal nonnegative parity surface;
- `hermitian_dyadic_parallelogram`, the complex algebra behind dyadic Gram law `(20)`;
- `tsum_evenIndex_binary_eq_evenOddGram`, the exact **binary parity Gram decomposition `(13)`**
  `∑_q R₁(2q) r^{2q} = |E(r²)|² + r²|O(r²)|²`, via the even/odd generating-function split
  `generatingFunction_even_odd_split` (`A(x) = E(x²) + x·O(x²)`) fed into the already-formalized
  projector `(4)` at `k = 1`.

The analytic pole and zeta specializations, and the orbit classification `(25)`, remain paper-level. Direct cached verification passed:

```text
lake env lean GaloisForLFunctions/RHTower/DirichletLMixedAdditiveEvenIndexLaw.lean
lake build GaloisForLFunctions.RHTower.DirichletLMixedAdditiveEvenIndexLaw
```

The target build replayed its dependency cache and built only the missing tail. A scratch
`#print axioms` audit reports only `propext`, `Classical.choice`, and `Quot.sound` for all three
theorems. No broad rebuild was run.

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
- [x] minimal Lean parity connector
- [x] full unconditional Lean formalization of every card statement
- [ ] recognized major open problem solved
- [ ] RH

## Log

- 2026-07-22 — proved exact parity projection, pole lower edge, even-index positive recurrence,
  Möbius/Liouville binary corollaries, and the power-sieved family specialization. Novelty label
  remains suspended pending literature audit.
- 2026-07-22 — strengthened exact law to the completely multiplicative dyadic Gram identity;
  formalized the even-index projector, nonnegative parity surface, and Gram parallelogram in a
  standalone Lean module. Direct `lake env lean` verification passed.
- 2026-07-24 — formalized the binary parity Gram decomposition `(13)`
  (`RHTower.tsum_evenIndex_binary_eq_evenOddGram`) via a new even/odd generating-function split
  lemma, connected to the already-formalized even-index projector `(4)` at `k = 1`. Axioms clean;
  module builds. The tsum even/odd split required keeping the summand folded to avoid a defeq
  blow-up in `tsum_even_add_odd`.

## Log

- 2026-07-24 — Formalization progress. The exact parity law `(4)` is already formalized
  (`RHTower/DirichletLMixedAdditiveEvenIndexLaw.lean`:
  `add_pos_neg_hermitianAbel_eq_two_mul_tsum_evenIndex`,
  `re_tsum_evenIndex_mixedAdditiveConvolutionPower_nonneg`).  Formalized the **coefficient-recurrence
  engine of the infinitely-often statement `(9)`** as reusable infrastructure
  (`HTGeometry/PowerSeriesEventualSignRecurrence.lean`, unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`):
  * `tsum_mul_pow_le_sum_range_abs_of_eventually_nonpos` — a real power series with coefficients
    eventually `<= 0` is capped on `[0,1)` by the sum of absolute values of its earlier coefficients.
  * `frequently_pos_of_forall_exists_tsum_gt` — contrapositive: if the Abel sum exceeds every finite
    prefix bound as the radius approaches `1`, the coefficients are positive infinitely often
    (`∃ᶠ q in atTop, 0 < c q`).
  Combined with the parity law `P_k(u) = (|A(sqrt u)|^(2k)+|A(-sqrt u)|^(2k))/2 >= |A(sqrt u)|^(2k)/2`,
  statement `(9)` reduces to the single analytic input "`|A(sqrt u)|` is unbounded as `u -> 1^-`"
  (the Mellin/Abelian pole-frontier step `(6)`--`(8)`), which remains to be formalized unconditionally.
- 2026-07-24 — Formalized the radial Hermitian upper bound underlying statement `(5)`
  (`RHTower/EvenIndexHermitianAbelBound.lean`, unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`):
  * `summable_evenIndex_mixedAdditive` — the even-index Abel subseries is summable.
  * `norm_pow_sq_le_two_mul_tsum_evenIndex_re` —
    `‖(∑' a_N r^N)^k‖^2 ≤ 2 * ∑' q (R_k(2q)).re * r^(2q)`, obtained from the parity law by discarding
    the nonnegative `-r` square.  Since `(R_k(2q)).re ≤ max((R_k(2q)).re, 0)`, this is *sharper* than
    the paper's positive-part inequality `(5)` and implies it directly.
  Together with last cycle's `frequently_pos_of_forall_exists_tsum_gt`, statement `(9)` now reduces to
  the single analytic input "the left-hand side is radially unbounded as `r -> 1^-`" (the Mellin
  pole-frontier step `(6)`--`(8)`), which is the remaining piece to formalize unconditionally.
- 2026-07-24 — Formalized the **Mellin pole -> boundary growth** infrastructure for the analytic
  input of `(9)` (`HTGeometry/MellinPoleRadialGrowth.lean`, unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`):
  * `not_differentiableAt_of_eventuallyEq_mul` — non-holomorphy survives a nonvanishing holomorphic
    factor: `f = g*h` near `ρ`, `g` holomorphic and `g ρ != 0`, `h` non-holomorphic at `ρ` ⟹ `f`
    non-holomorphic at `ρ`.
  * `not_isBigO_zero_rpow_of_not_differentiableAt_mellin` — contrapositive of the Mellin holomorphy
    criterion: `mellin f` non-differentiable at `ρ` (with exponential decay of `f` at infinity) ⟹ `f`
    is not `O(x^{-b})` at the origin for `b < Re ρ`.
  * `not_isBigO_zero_of_mellin_eq_Gamma_mul` — the crux: `mellin f = Γ*D` near `ρ` with `Re ρ > 0`
    and `D` non-holomorphic at `ρ` ⟹ `f` does not decay/stay bounded at the origin (uses `Γ`
    holomorphic and nonzero on the right half-plane).
  This discharges the `(6)`--`(8)` Mellin pole-frontier step abstractly: a right half-plane pole of the
  Dirichlet series forces radial blow-up of `A(e^{-x})` at `x -> 0^+`, i.e. of `A(r)` at `r -> 1^-`.
  Remaining for `(9)`: thread the even-index `A_f(x) = A(e^{-x})` (local integrability + exponential
  decay at infinity), convert "not `O(1)` at `0`" into the `hub` hypothesis of
  `frequently_pos_of_forall_exists_tsum_gt` via `norm_pow_sq_le_two_mul_tsum_evenIndex_re`.
- 2026-07-24 — **Statement `(9)` formalized abstractly** (`RHTower/EvenIndexHermitianPoleRecurrence.lean`,
  unconditional, axioms `[propext, Classical.choice, Quot.sound]`), completing the multi-cycle campaign:
  * `RHTower/EvenIndexHermitianRecurrence.lean`: `frequently_re_pos_of_norm_unbounded` — radial blow-up
    of `‖∑' a_N r^N‖` as `r -> 1` forces `0 < (R_k(2q)).re` at infinitely many `q` (couples the radial
    bound `(5)` with the coefficient-recurrence engine).
  * `EvenIndexHermitianPoleRecurrence.lean`: `exists_norm_gt_of_not_isBigO` — an exponential profile
    `A(e^{-x})` unbounded at `x -> 0^+` yields radii approaching `1` with unbounded modulus (`r = e^{-x}`).
  * `frequently_re_pos_of_dirichletPole` — the capstone `(9)`: given the Mellin realisation `(6)`
    `mellin (A(e^{-·})) = Γ·D` near a right half-plane `ρ`, local integrability and exponential decay of
    the profile, and `D` non-holomorphic at `ρ`, then for every `k >= 1` the even-index real parts
    `(R_k(2q)).re` are positive at infinitely many `q`.
  This is faithful to the card's "Assume in addition ... Mellin identity `(6)` ... pole frontier"
  premises (an unconditional implication).  Remaining: the quantitative order inequality `(8)`
  `Ψ_k^even ≥ max(0, 2kθ-1)` (a Tauberian order statement, not needed for `(9)` via this radial route),
  and the concrete Möbius/Liouville instantiations, which require the pole of `D = 1/ζ` in `Re s > 0`
  (a zeta zero) — deferred as it depends on zeta-zero facts.

## Log

- 2026-08-08 — **Liouville endpoint `(35)` formalized unconditionally**, together with the dyadic
  Gram law `(20)`, the orbit classification `(25)`, the orthogonal channel decomposition `(26)`, the
  binary two-real-squares form `(21)`, and the order lower edge `(8)`.  All new declarations have
  axioms `[propext, Classical.choice, Quot.sound]`.

  New modules:
  * `HTGeometry/DyadicExponentGeometricSummable.lean` —
    `summable_geometric_mul_pow_two_pow`, `tendsto_geometric_mul_pow_two_pow`: doubly exponential
    radial decay `r^(2^j)` beats geometric growth `d^j` for `0 ≤ r < 1`.
  * `HTGeometry/BoundedCoefficientLaplaceMellin.lean` — the exponential profile
    `coeffLaplaceProfile f x = ∑ f n e^{-n x}` of any unit-bounded coefficient sequence: continuity
    and local integrability on `(0,∞)`, `O(e^{-x})` at infinity, the radial form
    `coeffLaplaceProfile f x = ∑ f n (e^{-x})^n`, and the Mellin–Dirichlet identity
    `mellin (coeffLaplaceProfile f) s = Γ s * L f s` on `Re s > 1`.  This is the generic form of the
    estimates the twisted-Möbius module carried only for `χ·μ`.
  * `RHTower/EvenIndexHermitianDyadicOrbit.lean` — for any sequence with the local dyadic recursion
    `a (2 n) = c · a n`:
    - `abelSeries_eq_oddSeed_add_const_mul_abelSeries_sq` — the exact split `(24)`
      `A x = O x + c · A (x²)`;
    - `tsum_evenIndex_binary_eq_dyadicOrbitGram` — the orthogonal channel decomposition `(26)`;
    - `tsum_evenIndex_binary_eq_dyadicGram` — the dyadic Gram law `(20)`;
    - `tsum_evenIndex_binary_eq_dyadicGram_neg_one` — the two adjacent real squares at `c = -1`;
    - `hasSum_dyadicOrbit` — the orbit classification `(25)`
      `A r = ∑_j c^j O(r^{2^j})` for `0 < r < 1`, with summability, plus the supporting linear
      radial bound `norm_abelSeries_le_mul` and the telescoping `abelSeries_dyadic_telescope`.
  * `RHTower/LiouvilleDirichletSeries.lean` — `liouvilleC`, `isSquare_iff_factorization_even`,
    `sum_divisors_liouvilleC` (`λ ⍟ 1 = 1_{squares}`), `LSeries_squareIndicator`
    (`L 1_{squares} s = ζ(2s)`), and the closed form
    `LSeries_liouvilleC_mul_riemannZeta : L ↗λ s * ζ s = ζ (2 s)` on `Re s > 1`.
  * `RHTower/LiouvilleDyadicGramLaw.lean` — `liouvilleC_two_mul` (`λ(2n) = -λ(n)`),
    `tsum_evenIndex_binary_liouville_eq_dyadicGram` (equation `(21)`), `hasSum_dyadicOrbit_liouville`.
  * `RHTower/EvenIndexHermitianOrderLowerEdge.lean` — the quantitative half of `(8)`:
    - `norm_pow_sq_le_of_evenIndex_subpower`, `norm_tsum_le_of_evenIndex_subpower`,
      `isBigO_zero_of_evenIndex_subpower` — an **even-index only** subpower bound
      `Re R_k(2q) ≤ C (q+1)^α` already forces `A(e^{-x}) = O(x^{-(α+1)/(2k)})`;
    - `re_pole_le_of_evenIndex_subpower` — hence every right half-plane pole satisfies
      `Re ρ ≤ (α+1)/(2k)`;
    - `evenIndexOrder`, `isBoundedUnder_evenIndexOrderSeq`, `evenIndexOrder_nonneg`,
      `exists_subpower_bound_of_eventually`, `le_evenIndexOrder_of_subpower_threshold`,
      `le_evenIndexOrder_of_dirichletPole` — the limsup form
      `2k Re ρ - 1 ≤ Ψ_k^even`, i.e. `(8)`.
  * `RHTower/LiouvilleEvenIndexPositiveRecurrence.lean` — the arithmetic endpoint:
    - `zetaEntire_one : zetaEntire 1 = 1` (the residue of `ζ` at `1`);
    - `not_isBigO_liouvilleProfile_rpow` — for `0 ≤ b < 1/2` the Liouville profile is **not**
      `O(x^{-b})` at the origin.  Mechanism: such decay makes `mellin` analytic on `Re s > b`;
      dividing by `Γ` and clearing both zeta poles with `zetaEntire` converts
      `L ↗λ s · ζ s = ζ(2s)` into `(2s-1)·G(s)·zetaEntire(s) = (s-1)·zetaEntire(2s)`, an identity
      between two functions analytic on the whole half-plane.  The identity theorem on the convex
      half-plane propagates it to `s = 1/2`, where the left side vanishes and the right side is
      `-1/2`.  **No zeta-zero input and no `ζ(1/2) ≠ 0` input is used**: the contradiction happens at
      the level of the residue at `s = 1`;
    - `frequently_re_pos_liouville` — cofinal positivity of the even-index real parts for every
      `k ≥ 1`;
    - `liouvilleBinaryCorrelation` and
      `frequently_one_le_liouvilleBinaryCorrelation : ∃ᶠ q in atTop, 1 ≤ ∑_{a+b=2q} λ(a) λ(b)` —
      this is exactly `(35)`, unconditional;
    - `half_le_of_evenIndex_subpower_liouville` and
      `le_evenIndexOrder_liouville : (j : ℝ) ≤ Ψ_{j+1}^even` — the concrete order lower edge at the
      structural pole, i.e. `(31)`/`(33)` at `m = 2` with `Θ` replaced by the unconditional `1/2`.

  Still paper-level: the Möbius endpoint `(34)` and the family bound `(31)` at the true frontier
  `Θ`.  Both need a nonremovable pole of `1/ζ` in `Re s > 0`, i.e. the existence of a nontrivial
  zeta zero, which the identity above shows is *exactly* the missing input: boundedness of
  `A_μ(e^{-x})` at the origin is equivalent to `zetaEntire` having no zero in `Re s > 0`.

## Log

- 2026-08-08 — **Möbius endpoint `(34)` formalized unconditionally**, by first formalizing the
  missing analytic input: the existence of a nontrivial zeta zero.  Axioms
  `[propext, Classical.choice, Quot.sound]` throughout.

  * `RHTower/RiemannXiZerosInfinite.lean` —
    - `riemannXi s = (s (s-1) Λ₀ s + 1)/2`, entire, and equal to `s (s-1) Λ(s)/2` off the two poles
      (`riemannXi_eq_mul_completedRiemannZeta`); `riemannXi 0 = riemannXi 1 = 1/2`;
    - `orderOneEnvelope_id`, `orderOneEnvelope_completedRiemannZeta₀`,
      `orderOneEnvelope_riemannXi` — the order-one growth envelope, reusing the corpus Hurwitz
      completion envelope (`completedRiemannZeta₀ = completedHurwitzZetaEven₀ 0` definitionally);
    - `tendsto_riemannZeta_atTop`, `eventually_half_le_norm_riemannZeta`,
      `riemannXi_ray_growth` — super-linear growth of `log ‖ξ(σ)‖` on the positive real ray, from
      the corpus Archimedean ray-growth lemma `exists_Gammaℝ_ray_growth`;
    - `riemannXi_zeroSet_infinite` — via `zeroSet_infinite_of_subquadratic_superlinear_ray`;
    - **`exists_riemannZeta_zero_mem_openStrip : ∃ ρ, 0 < ρ.re ∧ ρ.re < 1 ∧ ζ ρ = 0`.**
  * `RHTower/MobiusEvenIndexPositiveRecurrence.lean` —
    - `moebiusCoeffC`, `moebiusProfile`, `LSeries_moebiusCoeff_mul_riemannZeta`;
    - `not_isBigO_moebiusProfile_rpow` — for `0 ≤ b < Re ρ` at any zeta zero `ρ` with `Re ρ < 1`,
      the Möbius profile is not `O(x^{-b})` at the origin.  Same mechanism as the Liouville case:
      `G(s)·zetaEntire(s) = s - 1` propagates from `Re s > 1` to the whole half-plane and dies at
      `ρ`;
    - `frequently_re_pos_moebius`, `moebiusBinaryCorrelation`, and
      **`frequently_one_le_moebiusBinaryCorrelation : ∃ᶠ q in atTop, 1 ≤ ∑_{a+b=2q} μ(a) μ(b)`** —
      this is `(34)`, unconditional;
    - `re_le_of_evenIndex_subpower_moebius`,
      `le_evenIndexOrder_moebius : 2k Re ρ - 1 ≤ Ψ_k^even` at every zeta zero `ρ` — this is `(31)`
      per zero; taking the supremum over zeros gives the `Θ` form.

  Remaining Lean gap on this card: the power-sieved family `a_m` for finite `m ≥ 3`
  (equations `(28)`–`(29)`, `(32)`–`(33)` at those `m`), which the card itself labels secondary and
  classical.  The `m = 2` (Liouville) and `m = ∞` (Möbius) endpoints are both closed.

## Stage-3 Lean certificate

Every mathematical statement of this card is now an unconditional Lean 4 theorem.  All declarations
below report exactly `[propext, Classical.choice, Quot.sound]` under `#print axioms`, and every
module is reachable from the `GaloisForLFunctions.RHTower` / `GaloisForLFunctions.HTGeometry`
theorem-area umbrellas.

| Card statement | Lean declaration | Module |
|---|---|---|
| `(4)` exact parity projector | `add_pos_neg_hermitianAbel_eq_two_mul_tsum_evenIndex` | `RHTower/DirichletLMixedAdditiveEvenIndexLaw` |
| `(4)` nonnegative surface | `re_tsum_evenIndex_mixedAdditiveConvolutionPower_nonneg` | `RHTower/DirichletLMixedAdditiveEvenIndexLaw` |
| `(5)` radial bound (sharpened) | `norm_pow_sq_le_two_mul_tsum_evenIndex_re` | `RHTower/EvenIndexHermitianAbelBound` |
| `(13)` binary parity Gram | `tsum_evenIndex_binary_eq_evenOddGram` | `RHTower/DirichletLMixedAdditiveEvenIndexLaw` |
| `(8)` order lower edge | `le_evenIndexOrder_of_dirichletPole`, `le_evenIndexOrder_of_subpower_threshold` | `RHTower/EvenIndexHermitianOrderLowerEdge` |
| `(9)` pole recurrence | `frequently_re_pos_of_dirichletPole` | `RHTower/EvenIndexHermitianPoleRecurrence` |
| `(20)` dyadic Gram law | `tsum_evenIndex_binary_eq_dyadicGram` | `RHTower/EvenIndexHermitianDyadicOrbit` |
| `(21)` Liouville two squares | `tsum_evenIndex_binary_liouville_eq_dyadicGram` | `RHTower/LiouvilleDyadicGramLaw` |
| `(24)` dyadic split | `abelSeries_eq_oddSeed_add_const_mul_abelSeries_sq` | `RHTower/EvenIndexHermitianDyadicOrbit` |
| `(25)` orbit classification | `hasSum_dyadicOrbit`, `hasSum_dyadicOrbit_liouville` | `RHTower/EvenIndexHermitianDyadicOrbit`, `RHTower/LiouvilleDyadicGramLaw` |
| `(26)` channel decomposition | `tsum_evenIndex_binary_eq_dyadicOrbitGram` | `RHTower/EvenIndexHermitianDyadicOrbit` |
| `(28)`–`(29)` sieved family | `sievedLiouville`, `sievedLiouville_prime_pow_eq`, `norm_sievedLiouville_le_one` | `RHTower/PowerSievedLiouvilleDirichlet` |
| `ζ(ms)/ζ(s)` closed form | `LSeries_sievedLiouville_mul_riemannZeta`, `LSeries_liouvilleC_mul_riemannZeta` | `RHTower/PowerSievedLiouvilleRecurrence`, `RHTower/LiouvilleDirichletSeries` |
| `(31)`/`(33)` order edge, finite `m` | `le_evenIndexOrder_sieved`, `le_evenIndexOrder_liouville` | `RHTower/PowerSievedLiouvilleRecurrence`, `RHTower/LiouvilleEvenIndexPositiveRecurrence` |
| `(31)` order edge at a zeta zero | `le_evenIndexOrder_moebius` | `RHTower/MobiusEvenIndexPositiveRecurrence` |
| `(32)` sieved sign recurrence | `frequently_re_pos_sievedBinaryCorrelation` | `RHTower/PowerSievedLiouvilleRecurrence` |
| `(34)` Möbius sign majority | `frequently_one_le_moebiusBinaryCorrelation` | `RHTower/MobiusEvenIndexPositiveRecurrence` |
| `(35)` Liouville sign majority | `frequently_one_le_liouvilleBinaryCorrelation` | `RHTower/LiouvilleEvenIndexPositiveRecurrence` |

Supporting infrastructure built for the card and reusable elsewhere:

| Statement | Declaration | Module |
|---|---|---|
| doubly exponential vs geometric | `summable_geometric_mul_pow_two_pow` | `HTGeometry/DyadicExponentGeometricSummable` |
| generic exponential profile and its Mellin transform | `coeffLaplaceProfile`, `mellin_coeffLaplaceProfile_eq_gamma_mul_LSeries` | `HTGeometry/BoundedCoefficientLaplaceMellin` |
| squares by even exponents | `isSquare_iff_factorization_even` | `RHTower/LiouvilleDirichletSeries` |
| `m`-th powers by divisible exponents | `isPow_iff_factorization_dvd` | `RHTower/PowerSievedLiouvilleDirichlet` |
| the entire Xi has infinitely many zeros | `riemannXi_zeroSet_infinite` | `RHTower/RiemannXiZerosInfinite` |
| **a nontrivial zeta zero exists** | `exists_riemannZeta_zero_mem_openStrip` | `RHTower/RiemannXiZerosInfinite` |

The two analytic endpoints use the same mechanism.  Assumed origin decay `O(x^{-b})` makes the
Mellin transform analytic on `Re s > b`; dividing by `Γ` and clearing **every** zeta pole with the
entire multiple `zetaEntire s = (s-1) ζ s` puts both sides of the Dirichlet identity into the
analytic class on the *whole* half-plane, so the identity theorem on a convex half-plane propagates
it.  The sieved endpoint dies at `s = 1/m` against `zetaEntire 1 = 1` (no zeta-zero input at all);
the Möbius endpoint dies at a zeta zero.
