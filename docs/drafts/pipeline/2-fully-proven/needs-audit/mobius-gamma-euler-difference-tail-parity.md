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

The analytic asymptotic transport `(4)` is formalized for arbitrary finite blocks in
`RHTower/GammaEulerTwoChannelAsymptotic.lean` (`gammaEulerDifferenceList_asymptotic`, with the
even-block no-go `gammaEulerDifferenceList_eventually_neg`); Theorem 1 in
`RHTower/GammaEulerCharacteristicPositivity.lean`.

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
- [x] formalize asymptotic formula `(4)` (arbitrary finite block, `RHTower/GammaEulerTwoChannelAsymptotic.lean`)
- [ ] specialist novelty audit
- [ ] replace failed local induction by a block/global source inequality

## Log

- 2026-07-22 — primewise diagonal-dominance attack initiated and killed; Gamma--Euler tail-parity
  survivor proved without computation; exact eigenmode core added to Lean.

## Log

- 2026-07-24 — Correction: a `Fin k` iterated-tail-parity module was briefly added, then removed as a
  duplicate — the general finite-block parity is already in the corpus as
  `MobiusGammaEulerDifferenceTailParity.gammaEulerManyDifferenceNextCoefficient_signed_pos` (over an
  arbitrary `Finset`, sign `(-1)^(card S + 1)`), which strictly subsumes the `Fin k` restatement.
- 2026-07-24 — **Theorem 1 formalized** (`RHTower/GammaEulerCharacteristicPositivity.lean`,
  unconditional, axioms `[propext, Classical.choice, Quot.sound]`), completing the card's analytic
  companion to the tail-parity:
  * `euler_ratio_core` — for `0 < s < c`, `r > 0`, the even symmetric sum
    `(c+sT)^{-r} + (c-sT)^{-r}` is strictly below its endpoint `(c+s)^{-r}+(c-s)^{-r}` whenever
    `|T| < 1` (strict monotonicity of the sum in `|T|`, via positive derivative on `(0,1)`).
  * `gammaEulerCentralDifference_cosh_rpow_pos` — `0 < D_{r,h} φ_r(u)` for the Gamma characteristic
    `φ_r(u) = cosh(u/2)^{-r}`, every `r,h>0`, `u`: one Euler channel preserves the correlation sign
    (eq (3)).  The factorisation `cosh((u±h)/2) = cosh(u/2)(cosh(h/2) ± sinh(h/2) tanh(u/2))` reduces
    it to `euler_ratio_core` at `T = tanh(u/2)`, with endpoint `(c+s)^{-r}+(c-s)^{-r} = 2 cosh(rh/2)`.
  With the corpus's finite-block tail parity (`gammaEulerManyDifferenceNextCoefficient_signed_pos`),
  **both Theorem 1 and Theorem 2 are now formalized** — the card's full no-go mechanism (one channel
  fine, two channels reverse the sign) is unconditional.  The remaining open gate is the analytic
  asymptotic transport formula `(4)` (the `lim exp((r/2+1)u)·(D…φ_r)(u)` limit), still paper-level.
- 2026-07-24 — **Asymptotic transport formula `(4)` formalized for one channel** (gate `formalize
  asymptotic formula (4)`, `k = 1` case), in `RHTower/GammaEulerAsymptoticTransport.lean`
  (unconditional, axioms `[propext, Classical.choice, Quot.sound]`):
  * `cosh_half_rpow_factor` — the exact factorisation
    `cosh(v/2)^{-r} = 2^r · exp(-rv/2) · (1 + exp(-v))^{-r}` (reusable).
  * `gammaEulerOneDifference_asymptotic` — `exp((r/2+1)u)·D_{r,h}φ_r(u) → gammaEulerOneDifferenceNextCoefficient r h`
    as `u → ∞`, for the Gamma characteristic `φ_r(u) = cosh(u/2)^{-r}`.  The exact identity
    `D_{r,h}φ_r(u) = 2^r exp(-ru/2)·F(exp(-u))` (with `F 0 = 0`, `F'(0) = -r·d_{r,h}(r/2+1)`) reduces the
    limit to the boundary slope `F(e)/e → F'(0)` (leading `exp(-ru/2)` mode annihilated).
  This connects the continuous characteristic to the corpus coefficient `gammaEulerOneDifferenceNextCoefficient`.
  Remaining for gate `(4)`: the general `k`-channel asymptotic (iterating the difference on the
  characteristic profile), i.e. connecting `exp((r/2+1)u)·(D…φ_r)(u)` to
  `gammaEulerManyDifferenceNextCoefficient` for arbitrary finite blocks.
- 2026-07-24 — **Two-channel asymptotic transport `(4)` (`k = 2`) + the headline no-go `(99)`
  formalized**, in `RHTower/GammaEulerTwoChannelAsymptotic.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`).  Reusable profile-operator core, then the two-channel
  limit and its sign consequence:
  * `gammaEulerProfileStep` / `gammaEulerCentralDifference_profile` — writing
    `g(u) = 2^r exp(-ru/2) H(exp(-u))`, the difference `D_{r,h}` acts on the profile `H` by the
    linear operator `gammaEulerProfileStep r h H` (`H` at scaled arguments `e·exp(∓h)`).
  * `gammaEulerProfileStep_zero` — the profile operator kills the value at `0` (any `H`): the exact
    annihilation of the leading `exp(-ru/2)` tail mode.
  * `gammaEulerProfileStep_hasDerivAt` — it scales the derivative at `0` by the next-mode eigenvalue
    `d_{r,h}(r/2+1)`.  Iterating over two channels multiplies the next coefficient `-r·2^r` by the
    two (negative) eigenvalues.
  * `gammaEulerTwoDifference_asymptotic` — `exp((r/2+1)u)·(D_{r,h₁} D_{r,h₂} φ_r)(u) →
    gammaEulerTwoDifferenceNextCoefficient r h₁ h₂` for `φ_r(u) = cosh(u/2)^{-r}`, via the boundary
    slope `K(e)/e → K'(0)` (`K = gammaEulerProfileStep r h₁ (gammaEulerProfileStep r h₂ H₀)`,
    `H₀ = (1+·)^{-r}`).
  * `gammaEulerTwoDifference_eventually_neg` — since the limit is strictly negative
    (`gammaEulerTwoDifferenceNextCoefficient_neg`), `(D_{r,h₁} D_{r,h₂} φ_r)(u) < 0` for all large
    `u`: the card's headline equation `(99)`, now unconditional at the continuous level.
  Gate `formalize asymptotic formula (4)`: the `k = 1` and `k = 2` cases are formalized (with the
  reusable profile-operator core); the general arbitrary-`k` block asymptotic remains (iterate
  `gammaEulerProfileStep` over a finite list, connecting to `gammaEulerManyDifferenceNextCoefficient`).
- 2026-07-24 — **Asymptotic formula `(4)` fully formalized for arbitrary finite blocks** (gate
  `formalize asymptotic formula (4)` closed), in `RHTower/GammaEulerTwoChannelAsymptotic.lean`
  (unconditional, axioms `[propext, Classical.choice, Quot.sound]`).  Iterating the profile operator
  over a finite list of scales:
  * `gammaEulerDifferenceList` / `gammaEulerProfileList` — the iterated difference `D_{r,h₁}⋯D_{r,h_k}`
    and its profile counterpart as right folds over a `List ℝ` of scales.
  * `gammaEulerDifferenceList_profile` — the iterated difference acts on the rescaled profile by the
    iterated profile operator (induction over the list, one `gammaEulerCentralDifference_profile` per step).
  * `gammaEulerProfileList_zero` / `gammaEulerProfileList_hasDerivAt` — a nonempty iterated operator
    kills the value at `0`, and scales the derivative at `0` by the **product** of the next-mode
    eigenvalues `∏_{h∈L} d_{r,h}(r/2+1)` (induction over the list).
  * `gammaEulerDifferenceList_asymptotic` — for nonempty `L`,
    `exp((r/2+1)u)·(D_{r,h₁}⋯D_{r,h_k} φ_r)(u) → -r·2^r·∏_{h∈L} d_{r,h}(r/2+1)`, i.e. equation (4) for
    an arbitrary finite block (the product mirrors `gammaEulerManyDifferenceNextCoefficient`).
  * `gammaEulerEigenvalueList_prod_sign` — the eigenvalue product is positive for even-length blocks,
    negative for odd (each factor strictly negative), the continuous analogue of the corpus signed sign.
  * `gammaEulerDifferenceList_eventually_neg` — **general no-go**: for any nonempty even-length list of
    positive scales, `(D_{r,h₁}⋯D_{r,h_{2m}} φ_r)(u) < 0` for all large `u`.  Any even number of Euler
    channels reverses the correlation-sign tail, generalizing the two-channel headline `(99)`.
  With Theorem 1 (`GammaEulerCharacteristicPositivity`) and Theorem 2 (corpus finite-block coefficient
  parity + this asymptotic transport), the card's full analytic no-go mechanism is now unconditional
  in Lean.  Remaining gates are non-Lean: specialist novelty audit; replacing the failed local
  induction by a block/global source inequality.
