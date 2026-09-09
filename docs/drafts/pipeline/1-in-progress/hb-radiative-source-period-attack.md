# HB: direct source-period attack on radiative extinction

Status: analytical source reduction; physical extinction and RH unproved. Frontier map remains read-only.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hard target remains the complete physical quantity `2 Ω(B(p,p)/2, B(m,m)/2)`, including full tensor corrections, time onset, horizon and AdS terms. A scalar source moment is a test of a proposed cancellation mechanism, not a replacement for that target.

## Frozen cancellation conjecture and tests

Conjecture: the literal source relations force cancellation between the complete causal bulk pairing and its actual endpoint terms at the fixed Hawking clock. This remains unproved. No zero-pairing premise may be inserted in its construction.

The working method is conjecture → attempted proof or falsification → pivot. Do not resume general action-current infrastructure unless a specific step in a source-level proof needs it. Failed proof attempts and falsified statements must be distinguished.

The current positive result is the [exact onset decomposition of the full original mixed scalar source](../3-formalized/hb-full-source-onset-reduction.md). It reuses the existing global angular inverse and identifies the actual time-dependent remainder as a fixed ingoing onset pulse. The incoming horizon profile is explicitly `H-s(s-1)Q/4`; it must remain in the causal pairing. The next primary test is cancellation between this horizon contribution and the pulse response in the complete tensor action, including the missing scalar-scalar and vector-vector channels. Do not substitute an isolated scalar-pole or normalization theorem for that test.

**Active tensor test.** The [Einstein radial action current](../3-formalized/hb-mixed-radial-action-current.md) is proved by differentiating the actual volume-weighted action current. The [original-source contact reduction](hb-causal-onset-contact-cancellation.md) identifies the pulse term that cancels the particular field's explicit `D_chi=integral exp(-6v)*chi'^2` coefficient. The remaining local contribution has only `C_chi=integral exp(-6v)*chi²` and the exact complex factor `2s+3`. This is a local analytical source identity; actual causal horizon admission and global integration remain open. The explicit unresolved term is equation (6) in that card: the pulse's horizon pairing through `roughLaplacian-1`, its cross terms with the particular field, and its original-source contact terms. Equation (7) reduces the cross terms to one source-derived test while retaining time and cusp boundaries. Evaluate that causal pulse term next; do not repeat the squared-onset coefficient check. Full extinction also requires every other tensor-sector pairing. With independent branch polarizations, SS–VV and SV–SV carry different amplitude monomials; do not combine their coefficients without a source-derived relation. No physical extinction is proved.

1. **Test: the original fundamental source is a cubic endpoint primitive.** The exact reduction below leaves one period with an explicitly fixed coefficient. At `s=w=0`, the source integral is `2/3`; the coefficient of the remaining period is nonzero. Thus the proposed universal pure-cubic-primitive identity fails. This is not a counterexample to extinction at a Xi divisor, and does not retire HB. The positive result is the explicit primitive-plus-period decomposition.
2. **Test: the complementary period is obtained by exchanging the two physical QNM branches.** The period identity exchanges `(w,2s)`. The actual target frequencies have real part between `-2` and `-1`, whereas the source rates `2s` have real part between `-4` and `-2`. Thus simple physical branch exchange does not perform the needed period exchange. The canonical left connection covectors also act on source/response coordinates at a fixed spectral parameter; their proved normalization is not the missing source-rate exchange. This rejects that proposed proof step, not every possible augmented adjoint identity.
3. **Positive source test: do radial and angular completion use independent affine arguments?** They do not. The original radial quadratic coefficient factors through the same `5 rho/2-1` and `3 rho/2` arguments appearing in the evaluated angular source, and their functional-equation complements. The exact identities are below. Whether the *full tensor causal pairing* uses these factors with the required orientation remains open.

## Actual radial source, without setting w = 2s

The starting definitions are `D4BMJointSource.fundamentalSourceCore` and `fundamentalSourceMoment`, together with `D4BMLaplaceRadial.sourceRemainder`. The corpus already identifies the original two-endpoint moment with its full first-subtracted Mellin integral at every physical fundamental QNM.

Put `y=sqrt(1-z)`, `alpha=2s-w`, `beta=2s+w+2`, and

```
A = (5s²+15s+4)/4
C = s(s-1)(alpha+2)(beta+3)/8.
```

The factorization follows directly from

```
(s+2)² - [(w+1)(w+2)/2 - (s+1)(s+2)]
  = (2s-w+2)(2s+w+5)/2.
```

The actual density transforms to

```
2 a² y² (1-y)^w (1+y)^(2s) (A+C y²) dy.
```

This is a change of coordinate in the original source, not a new source model. The original horizon finite part must be transported with the coordinate change.

Let `D=beta(beta+1)(beta+2)`, `U=s(s-1)(alpha+2)`, `V=5s²+15s+4`, and define the denominator-cleared cubic `P(y)=c0+c1 y+c2 y²+c3 y³` by

```
c3 = -U beta(beta+1)(beta+2)/4
c2 = -U alpha beta(beta+1)/4
c1 = -beta [U(3beta+6+alpha²)+2V(beta+2)]/4
c0 = -alpha [U(5beta+8+alpha²)+2V(beta+2)]/4
R  = c1+alpha c0.
```

Its exact polynomial identity is

```
(1-y²)P'(y) + (alpha-beta y)P(y)
  = 2D y²(A+C y²) + R.
```

Both this denominator-cleared identity and the original source factorization passed `lake env lean` scratch checks, with only `propext`, `Classical.choice`, and `Quot.sound`. They have no premises. They are not installed as standalone corpus leaves: the integral/physical-pairing result, rather than two isolated algebra lemmas, is the intended deliverable.

Multiplying by `(1-y)^w(1+y)^(2s)` identifies the left side as the derivative of

```
(1-y)^(w+1)(1+y)^(2s+1) P(y).
```

For `Re w>-2`, `w+1 != 0`, and `D != 0`, define the endpoint period by

```
I(w,s) = lim_(b→1-) [integral_0^b (1-y)^w(1+y)^(2s) dy
                     + 2^(2s)(1-b)^(w+1)/(w+1)].
```

The Taylor remainder at `y=1` is first order, so the subtracted integral converges. Transporting the original `z`-cutoff finite part gives the analytical formula

```
fundamentalSourceMoment(w,s,a) = -a² [c0 + R I(w,s)] / D.
```

To check the finite-part transport, set `z=epsilon`, `b=sqrt(1-epsilon)`. Then `epsilon=(1-b)(1+b)`. The primitive's leading divergent term cancels the original source subtraction and the period subtraction because

```
-2(w+1)P(1) = 2D(A+C)+R.
```

Every remaining endpoint error is `O(epsilon^(Re w+2))`, hence tends to zero. The AdS endpoint is `y=0` and contributes `-c0`. This establishes the paper reduction; the integral identity and its complete Lean admission are not yet formalized.

## Substitution of the actual Xi parameters

For `rho=q.1`, the source rates are `s=rho-2` and `s=-rho-1`; the two target frequencies are `w=-1-rho/2` and `w=-2+rho/2`. They remain independent slots.

| Source rate | Target | alpha+2 | beta+3 | beta |
|---|---|---|---|---|
| `rho-2` | `-1-rho/2` | `5rho/2-1` | `3rho/2` | `3rho/2-3` |
| `rho-2` | `-2+rho/2` | `3rho/2` | `5rho/2-1` | `5rho/2-4` |
| `-rho-1` | `-1-rho/2` | `1-3rho/2` | `2-5rho/2` | `-5rho/2-1` |
| `-rho-1` | `-2+rho/2` | `2-5rho/2` | `1-3rho/2` | `-3rho/2-2` |

Since actual Xi divisors have nonzero imaginary part, `D != 0` in all four cases. The target-branch exchange swaps the two factors in C; it does not change C at a fixed source rate. Both source branches have

```
A = (5rho²-5rho-6)/4.
```

Writing `x=5rho/2-1`, `v=3rho/2`, the two C coefficients are

```
C_plus  = (rho-2)(rho-3) x v / 8
C_minus = (rho+1)(rho+2) (1-v)(1-x) / 8.
```

Thus `C_plus*C_minus` contains the completion polynomial `x(x-1)v(v-1)`. These are exactly the two non-repeated affine arguments in `physicalSelfSourceCoefficient_fourLambda`; the repeated argument is `rho/2`. This is an exact source normalization relation, not evidence by itself that the full pairing vanishes.

## Complementary-period candidate: required admission and missing identification

In the ordinary convergence chamber, splitting the complete interval at zero gives

```
I(w,s) + I(2s,w/2)
  = integral_(-1)^1 (1-y)^w(1+y)^(2s) dy
  = 2^(w+2s+1) integral_0^1 t^w(1-t)^(2s) dt.
```

Continuation to the physical parameters cannot use the same first subtraction in both terms. For the exchanged term, `-4<Re(2s)<-2`, so subtract the three actual Taylor terms of `(2-t)^w`:

```
2^w [1 - w t/2 + w(w-1)t²/8].
```

The corresponding restored boundary terms are

```
2^w [1/(2s+1) - w/(2(2s+2)) + w(w-1)/(8(2s+3))].
```

The remainder is `O(t³)`, giving absolute admission because `Re(2s)+3>-1`. These coefficients are forced by the candidate period, not adjustable counterterms. None has yet been identified with the actual augmented Einstein horizon/AdS/onset terms. The continuing hard attack is that identification with the *complete* scalar-scalar, scalar-vector, and vector-vector source and its causal corrections. A scalar period completion must not be promoted to physical extinction without it.
