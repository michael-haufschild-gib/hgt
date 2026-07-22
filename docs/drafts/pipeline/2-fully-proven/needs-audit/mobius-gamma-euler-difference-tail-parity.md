# Möbius Gamma--Euler difference tail-parity obstruction

- **ID:** `mobius-gamma-euler-difference-tail-parity`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / NO-GO CLOSURE
- **Status:** `[PAPER-PROVED] [ALGEBRAIC CORE LEAN-PROVED] [NOVELTY UNVERIFIED] [NO RH CLAIM]`
- **Lean companion:**
  `formal/GaloisForLFunctions/RHTower/MobiusGammaEulerDifferenceTailParity.lean`
- **Parent:** `../../3-formalized/needs-audit/mobius-laplace-gamma-hankel-localization-wall.md`

## Goal

Attack the concrete source inequality suggested by Gamma--Hankel localization: insert inverse
Euler factors one prime at a time and ask whether every insertion decreases normalized Gamma
energy.  If that monotone contraction held cofinally for the Möbius Euler product, the diagonal
squarefree mass would control the full Hankel energy for every exponent `r>1`, proving the
Möbius--Laplace energy criterion and RH.

The monotone mechanism is false.  Failure occurs after only two prior Euler channels and follows
from an exact tail-parity law, without computation.

## Gamma characteristic and Euler difference

For `r>0`, normalize the Gamma height density

```text
w_r(t) dt = const_r |Gamma(r/2+i t)|^2 dt.
```

Its characteristic function is

```text
phi_r(u)=integral exp(i t u) w_r(t)dt=sech(u/2)^r.        (1)
```

For a scale `h>0`, put `a=exp(-r h/2)`.  Multiplication by the normalized squared Euler factor

```text
|1-a exp(-i h t)|^2/(1+a^2)
```

acts on characteristic functions by a positive scalar multiple of

```text
(D_(r,h)f)(u)
 =2 cosh(rh/2)f(u)-f(u+h)-f(u-h).                        (2)
```

Indeed, `1+a^2=2a cosh(rh/2)`.

## Theorem 1: one channel preserves correlation sign

For every `r,h>0` and every real `u`,

```text
D_(r,h) phi_r(u)>0.                                      (3)
```

### Proof

Evenness reduces to `u>=0`.  Set `x=u/2`, `y=h/2`, `X=tanh x`, and `Y=tanh y`.  Then

```text
phi_r(u+h)/phi_r(u)=[sech(y)/(1+XY)]^r,
phi_r(u-h)/phi_r(u)=[sech(y)/(1-XY)]^r.
```

For fixed `0<Y<1`,

```text
g(X)=(1+XY)^(-r)+(1-XY)^(-r)
```

is strictly increasing on `0<=X<1`.  Its limiting value at `X=1` gives

```text
sech(y)^r g(1)=exp(-ry)+exp(ry)=2cosh(ry).
```

Thus the sum of the two shifted ratios is strictly below `2cosh(rh/2)`, proving `(3)`.

## Theorem 2: iterated tail parity

For positive shifts `h_1,...,h_k`,

```text
lim_(u->infinity) exp((r/2+1)u)
  (D_(r,h_1)...D_(r,h_k) phi_r)(u)

=(-1)^(k+1) r 2^(r+k)
  product_j [cosh((r/2+1)h_j)-cosh(rh_j/2)].             (4)
```

Every bracket on the right is positive.  Hence an odd number of Euler differences has an
eventually positive correlation tail, while an even number has an eventually negative tail.  In
particular,

```text
D_(r,h_1)D_(r,h_2)phi_r(u)<0
```

for all sufficiently large positive `u`.

### Proof

As `u->infinity`,

```text
phi_r(u)
 =2^r exp(-ru/2)(1+exp(-u))^(-r)
 =2^r exp(-ru/2)[1-r exp(-u)+O(exp(-2u))].               (5)
```

Every exponential `exp(-lambda u)` is an exact eigenfunction of `(2)`, with eigenvalue

```text
d_(r,h)(lambda)
 =2[cosh(rh/2)-cosh(lambda h)].                           (6)
```

At the leading rate `lambda=r/2`, eigenvalue is zero.  At the next rate
`lambda=r/2+1`, it is strictly negative.  Applying the commuting differences to `(5)` kills the
leading mode and multiplies next coefficient `-r 2^r` by `k` negative eigenvalues.  Remainder stays
one exponential order smaller under every fixed finite translation.  This proves `(4)`.

## Consequence for prime-by-prime Gamma contraction

After two fixed Euler factors, normalized tilted Gamma density is nonnegative, but its
characteristic function is a positive multiple of

```text
D_(r,h_1)D_(r,h_2)phi_r.
```

By `(4)`, that characteristic is negative at every sufficiently large frequency.  Choose a prime
`p` with `log p` beyond this threshold.  Adding its normalized Euler factor changes total energy
by

```text
-c_p times [current characteristic at log p],    c_p>0,
```

and therefore **increases** energy.  Thus no ascending prime-by-prime proof can establish the
required Möbius Gamma--Hankel bound by claiming each normalized Euler factor is a contraction.

This does not falsify a global diagonal upper bound after all primes are assembled.  It kills its
most natural local induction and shows any valid proof must use block cancellation whose size is
at least three channels, or a genuinely all-prime identity.

## Lean certificate

Lean proves exact exponential-mode algebra `(6)`, first two parity signs, and arbitrary finite-block
sign parity:

- `gammaEulerCentralDifference_exp`;
- `gammaEulerCentralDifferenceEigenvalue_base`;
- `gammaEulerCentralDifferenceEigenvalue_next_neg`;
- `gammaEulerOneDifferenceNextCoefficient_pos`;
- `gammaEulerTwoDifferenceNextCoefficient_neg`;
- `gammaEulerManyDifferenceNextCoefficient_signed_pos`.

Direct verification:

```text
lake env lean GaloisForLFunctions/RHTower/MobiusGammaEulerDifferenceTailParity.lean
```

The analytic asymptotic transport `(4)` remains paper-level.

## Literature boundary

Targeted searches found classical central-difference calculus for powers of `sech`, but no source
stating `(4)` with the Gamma characteristic, normalized Euler factors, and the resulting
two-channel-to-third-channel contraction reversal.  Priority remains unverified; no publication
claim is made.

## No-go closure

- **Exact killing mechanism:** two Euler differences make the first surviving Gamma tail mode
  negative; a sufficiently large third prime increases normalized energy.
- **Strongest positive survivor:** general iterated parity law `(4)` and unconditional one-channel
  positivity `(3)`.
- **New insight:** local Gamma sewing is genuinely positive for one channel but cannot be iterated
  monotonically.  Required cancellation starts at multi-prime block level.
- **Status:** dependency-closed paper proof; exact eigenmode core formalized; full asymptotic Lean
  proof and novelty audit open.

## Gates

- [x] source conjecture isolated before use
- [x] one-channel sign proved
- [x] general finite tail parity proved
- [x] two-to-third-channel contraction reversal proved
- [x] exact eigenmode algebra and arbitrary finite-block coefficient parity formalized in Lean
- [ ] formalize asymptotic formula `(4)`
- [ ] specialist novelty audit
- [ ] replace failed local induction by a block/global source inequality

## Log

- 2026-07-22 — primewise diagonal-dominance attack initiated and killed; Gamma--Euler tail-parity
  survivor proved without computation; exact eigenmode core added to Lean.
