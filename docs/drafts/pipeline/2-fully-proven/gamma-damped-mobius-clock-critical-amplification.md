# The diagonal Gamma--Sonin orbit lift erases Mobius sign and has super-four critical energy

- **ID:** `gamma-damped-mobius-clock-critical-amplification`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / NO-GO WITH POSITIVE HT SUCCESSOR
- **Scientific status:** `[PROVED HERE] [LITERATURE NOVELTY OPEN] [NOT AN RH PROOF]`
- **Source inputs:**
  - `mobius-critical-fisher-tangent-hilbert-lift.md`
  - `../3-formalized/not_new_scientific_knowledge/sonin-log-coordinate-mellin-scattering-carrier.md`
  - `not_new_scientific_knowledge/gamma-damped-stationary-prime-log-covariance-law.md`
- **Statement:** Every basis-diagonal orbit map intertwining the doubled Mobius clock with Sonin
  reflection consumes the Mobius sign on the invariant Fisher state.  The undamped orbit sum is
  not a Hilbert vector near criticality.  The canonical time-one Gamma damping repairs its domain,
  but the odd Fisher tangent then has the exact critical energy

  ```text
  C_Gamma=6 sqrt(2) Gamma(1/4)/(pi^(3/2) Gamma(3/4))
         =4.5085689807...>4.                                (1)
  ```

  Thus an orbit-only Gamma--Sonin lift is not the missing nonexpansive RH source map.  The
  divisor/floor incidence cocycle must be inserted before the Gamma square and retained in a
  principal-relative trace.

## Doubled source clock and pointed Sonin system

Let `sigma>1`, `epsilon=sigma-1`, and use the squarefree source notation

```text
Z(sigma)=sum_d mu(d)^2d^(-sigma),
psi_sigma(d)=Z(sigma)^(-1/2)mu(d)d^(-sigma/2),
A_sigma=L-E_sigma(log d).                                  (2)
```

On `H_sq direct_sum H_sq`, put

```text
S(f,g)=(J_M g,J_M f),
Psi_sigma=2^(-1/2)(psi_sigma,J_M psi_sigma),
X_sigma=epsilon diag(A_sigma,-A_sigma),                    (3)
```

where `J_M e_d=mu(d)e_d` on squarefree support.  The parent theorem proves

```text
S Psi_sigma=Psi_sigma,
S X_sigma Psi_sigma=-X_sigma Psi_sigma,
||X_sigma Psi_sigma||^2=epsilon^2 Var_sigma(log d)->1.     (4)
```

Let `(K,U,J_infinity,xi)` be the pointed time-one Gamma cyclic representation:

```text
||xi||=1,
J_infinity xi=xi,
J_infinity U_h=U_(-h)J_infinity,
<xi,U_h xi>=phi(h)=(cosh h)^(-1/2).                       (5)
```

The scattering relations in `(5)` are the abstract content of the proved logarithmic Sonin
carrier.

## Forced sign-erasure theorem `[PROVED HERE]`

Consider a basis-diagonal orbit synthesis

```text
W e_d^+=a_d U_(log d)xi,
W e_d^-=b_d U_(-log d)xi.                                 (6)
```

Then

```text
W S=J_infinity W
```

on the algebraic finite-support core if and only if

```text
a_d=mu(d)b_d                                               (7)
```

for every squarefree `d`.

### Proof

The clock sends `e_d^+` to `mu(d)e_d^-`.  Hence the two sides of the intertwining relation on
`e_d^+` are

```text
mu(d)b_d U_(-log d)xi,
a_d J_infinity U_(log d)xi=a_d U_(-log d)xi.              (8)
```

This gives `(7)`; the equation on `e_d^-` is equivalent because `mu(d)^2=1`.  Conversely `(7)`
and `(5)` prove the intertwining on both basis sectors. `QED`

After writing `b_d=b(log d)`, equations `(2)`--`(3)` and `(7)` give

```text
W Psi_sigma
 =1/sqrt(2Z(sigma)) sum_d mu(d)^2d^(-sigma/2)b_d
     (U_(log d)+U_(-log d))xi,                            (9)

W X_sigma Psi_sigma
 =epsilon/sqrt(2Z(sigma)) sum_d mu(d)^2d^(-sigma/2)
     (log d-m_sigma)b_d(U_(log d)-U_(-log d))xi.          (10)
```

Thus the intertwiner necessarily uses the Mobius character to match reflection, and the
character disappears from both descended coefficient sums.  This is not a choice of gauge.

**Positive HT statement.**  In a reflection-constrained source, an arithmetic character can
survive as the grading of the constraint while disappearing from every orbit-diagonal invariant
state.  Character cancellation in the target must then be carried by a non-diagonal incidence
cocycle or a relative angle, not by orbit coefficients alone.

## Undamped orbit-domain no-go `[PROVED HERE]`

Take `b_d=1`.  For every `1<sigma<=2`, the positive even series `(9)` does not converge in `K`.

Indeed, in a dyadic squarefree block `N<=d<=2N`, all logarithmic differences have absolute value
at most `log 2`, and hence

```text
phi(log d-log e)>=phi(log 2)>0.                            (11)
```

Squarefree integers have positive density, so the block contains at least `cN` elements for all
large `N`.  The within-block Gram contribution is bounded below by a positive constant times

```text
(N N^(-sigma/2))^2=N^(2-sigma).                           (12)
```

Summing over disjoint dyadic blocks diverges for `sigma<=2`. `QED`

**Positive HT statement.**  Exact symmetry intertwining does not imply that the distinguished
source state lies in the target Hilbert domain.  In this example the obstruction is cofinal
positive covariance, not failure of any finite clock.

## Canonical Gamma damping

The source-derived damping from the Gamma sum-frequency diagonal is

```text
b_d=d_Gamma(log d)=sqrt(phi(2 log d))
   =2^(1/4)d^(-1/2)(1+d^(-4))^(-1/4).                    (13)
```

For `sigma>1`, the coefficients in `(9)` are absolutely summable after `(13)`, so both `(9)` and
`(10)` define vectors in `K`.  The odd kernel in `(10)` is

```text
K_odd(h,k)=phi(h-k)-phi(h+k).                             (14)
```

It is positive semidefinite because

```text
K_odd(h,k)
 =2 integral sin(hx)sin(kx) dnu_Gamma(x),                (15)
```

where `nu_Gamma` is the probability measure with characteristic function `phi`.

## Exact super-four critical limit `[PROVED HERE]`

Let

```text
Y_sigma=W_(d_Gamma)X_sigma Psi_sigma.                     (16)
```

Then

```text
lim_(sigma->1+)||Y_sigma||^2=C_Gamma,                    (17)
```

with `C_Gamma` as in `(1)`.

### Dirichlet reduction

Put

```text
eta_d=(1+d^(-4))^(-1/4),
F(z)=sum_d mu(d)^2 eta_d d^(-z),
alpha=(sigma+1)/2.                                       (18)
```

Since `eta_d-1=O(d^(-4))`, one has near `z=1`

```text
F(z)=1/(zeta(2)(z-1))+H(z),                              (19)
```

where `H` is holomorphic on a neighborhood of the closed line used below.  If

```text
D_epsilon(x)=-F'(alpha-i x)-m_sigma F(alpha-i x),         (20)
```

the spectral form `(15)` gives the exact identity

```text
||Y_sigma||^2
 =2sqrt(2) epsilon^2/Z(sigma)
   integral (Im D_epsilon(x))^2 dnu_Gamma(x).             (21)
```

### Pole scaling

The squarefree pole gives

```text
Z(1+epsilon)~1/(zeta(2)epsilon),
m_(1+epsilon)=epsilon^(-1)+O(1).                          (22)
```

For `x=epsilon y`, equations `(19)`--`(22)` imply locally uniformly in `y`

```text
epsilon^2D_epsilon(epsilon y)
 ->1/zeta(2) [1/(1/2-i y)^2-1/(1/2-i y)].                (23)
```

Away from the pole window, `(21)` tends to zero.  This follows by subtracting the pole in `(19)`,
using the standard vertical-line bounds for `zeta(z)/zeta(2z)`, and the exponential tail of the
Gamma cyclic density.  On the pole window the rational majorant obtained from `(19)` is square
integrable.  Dominated convergence after `x=epsilon y` is therefore valid.

The Gamma cyclic measure has continuous density `rho_Gamma`, and Fourier inversion gives

```text
rho_Gamma(0)
 =1/(2pi) integral_R (cosh t)^(-1/2)dt
 =Gamma(1/4)/(2sqrt(pi)Gamma(3/4)).                       (24)
```

Finally,

```text
integral_R
 (Im[1/(1/2-i y)^2-1/(1/2-i y)])^2dy=pi.                (25)
```

Combining `(21)`--`(25)` yields

```text
lim ||Y_sigma||^2
 =2sqrt(2)rho_Gamma(0)pi/zeta(2)
 =6sqrt(2)Gamma(1/4)/(pi^(3/2)Gamma(3/4)).                (26)
```

This proves `(17)`.

### The constant is strictly larger than four

For `t>=0`,

```text
cosh t<=(e^t+1)/2.
```

Consequently

```text
integral_R(cosh t)^(-1/2)dt
 >=4sqrt(2)asinh(1).                                     (27)
```

The elementary bounds `asinh(1)>7/8` and `pi^2<10` give

```text
12asinh(1)>pi^2.                                         (28)
```

Equations `(24)`, `(26)`, and `(28)` imply `C_Gamma>4`. `QED`

Numerical evaluation of the exact expression gives

```text
C_Gamma=4.5085689807710507...                             (29)
```

This number was used only to pre-certify the direction of the strict inequality; the proof is
`(27)`--`(28)`.

## No-go and nontrivial positive successor

The source clock has unit critical tangent energy by `(4)`, whereas its canonical diagonal
Gamma--Sonin image has energy `C_Gamma>4`.  Thus this source-fixed orbit lift is not nonexpansive.
Applying it to the completed tangent `chi_sigma=2X_sigma Psi_sigma` would have limiting energy
`4C_Gamma`, not four.

This kills only the **orbit-diagonal** lift.  It proves a stronger positive selection theorem:

```text
source four-unit Fisher tangent
  + Mobius reflection grading
  + time-one Gamma domain repair
  - orbit-diagonal synthesis
  -> finite universal residue-density energy C_Gamma>4.  (30)
```

The excess is a real archimedean covariance invariant, not an arbitrary norm loss.  A surviving
RH construction must use the complementary floor/tail packets before the Gamma square so that
their signed incidence angle contributes to the principal-relative subtraction.  Normalizing
`W_(d_Gamma)` by hand to force energy four is rejected: it would erase the exact Gamma cyclic
normalization and would still not restore the Mobius sign consumed in `(9)`--`(10)`.

**Positive general-HT statement.**  When a Dirichlet source pole is sewn to a continuous
archimedean cyclic measure at the unique exponent which repairs the Hilbert domain, the critical
tangent energy is the product of three local invariants:

```text
Dirichlet pole residue x archimedean spectral density at zero
  x universal centered-pole profile.                     (31)
```

For the squarefree pole and the time-one Gamma measure, `(31)` is exactly `(26)`.  This
residue-density law separates domain repair from metric contraction: the first can hold while the
second fails by a computable universal amount.

## Literature gate

Gamma/Meixner characteristic functions, squarefree Dirichlet series, Fisher scores, and Sonin
reflection are established parent mechanisms.  The project inputs remain admissible sources even
when already proved by other agents.  A targeted literature audit has not located the combined
forced-sign-erasure theorem or the critical constant `(26)`; specialist audit remains open.  No
novelty claim is needed for the route consequence: even if `(26)` has a literature parent, it
still excludes the orbit-only RH lift and selects the incidence-relative successor.

## Gates

- [x] doubled Mobius clock and unit critical Fisher tangent
- [x] characterize every basis-diagonal Sonin orbit intertwiner
- [x] prove forced Mobius sign erasure
- [x] prove failure of the undamped Hilbert domain
- [x] insert the canonical time-one Gamma diagonal
- [x] derive the positive odd Gamma kernel
- [x] prove the exact residue-density critical limit
- [x] prove the constant is strictly larger than four
- [x] isolate the complementary-incidence relative successor
- [ ] independent specialist literature audit
- [x] formalize the finite clock/intertwiner algebra in Lean
- [ ] construct the incidence-before-Gamma relative lift
- [ ] RH

## Formalization (in progress)

**Working state — a session picking up this card should continue here, not restart.**

`[LEAN-PROVED]` The **forced sign-erasure theorem** `(6)`–`(10)` and the abstract core of the
**undamped orbit-domain no-go** are compiled in
`formal/GaloisForLFunctions/HTGeometry/OrbitDiagonalReflectionIntertwiner.lean` (imported by
`GaloisForLFunctions.HTGeometry`; builds clean, no warnings; axiom-clean).

| Card item | Lean name |
|---|---|
| **`(7)`** the intertwining relation forces `a_d = μ(d) b_d` | `HTGeometry.orbitDiagonal_intertwines_iff` |
| **`(9)`, `(10)`** the character cancels from both descended coefficient families | `HTGeometry.orbitDiagonal_descended_coefficients` |
| the block covariance bound behind the no-go | `HTGeometry.mul_sq_sum_le_norm_sq_sum` |
| the cofinal-block divergence criterion | `HTGeometry.not_summable_of_cofinal_blocks` |

`orbitDiagonal_intertwines_iff` is stated with the weakest hypotheses the card's own computation
uses — a linear reflection `J` with `J (U h ξ) = U (-h) ξ` and `U t ξ ≠ 0`, a character `m` with
`m² = 1` — and proves the equivalence on **both** sectors at once:

```lean
(J (a • U t ξ) = (m * b) • U (-t) ξ ∧ J (b • U (-t) ξ) = (m * a) • U t ξ) ↔ a = m * b
```

No unitarity, positivity or continuity of `U` enters, so the statement is exactly the card's "this
is not a choice of gauge".  `orbitDiagonal_descended_coefficients` is the companion cancellation
`(m·c)(m·b) = c·b` and `(m·(m·c))·b = c·b`: the even and odd descended weights coincide and are
character-free, which is what `(9)`–`(10)` assert.

For the no-go, the two abstract ingredients are in place: a nonnegatively weighted block with all
pairwise covariances at least `γ` has energy at least `γ (∑ w)²`, and a family with arbitrarily late
blocks of energy bounded below is not summable (via `Summable.vanishing`).

`[LEAN-PROVED]` The **arithmetic input of the no-go** is now in place:
`formal/GaloisForLFunctions/RHTower/SquarefreeDensityLowerBound.lean` (imported by
`GaloisForLFunctions.RHTower`; builds clean, no warnings; axiom-clean).

| Content | Lean name |
|---|---|
| telescoping tail `∑_{k ≥ K} k^(-2) ≤ 1/(K-1)` | `RHTower.sum_Ico_one_div_sq_le` |
| **`∑_p p^(-2) ≤ 49/100`**, uniformly in the cutoff | `RHTower.sum_primesBelow_one_div_sq_le` |
| prime-square union bound for the non-squarefree integers | `RHTower.card_filter_not_squarefree_le` |
| **positive density** `#sf(0,M] ≥ (51/100)·M` | `RHTower.card_filter_squarefree_ge` |
| **dyadic block count** `#sf(N,2N] ≥ N/50` | `RHTower.card_filter_squarefree_Ioc_ge` |

Neither mathlib nor the corpus had any squarefree counting bound.  The proof is the elementary
sieve with an explicit constant: every non-squarefree `d` is a multiple of some `p²`, so
`#{d ≤ M : ¬Squarefree d} ≤ ∑_p ⌊M/p²⌋ ≤ M ∑_p p^(-2)`, and the prime inverse-square sum is split
at `29` — the nine primes below `29` contribute at most `45/100` and the telescoping tail
`∑_{k ≥ 29} k^(-2) ≤ 1/28` the rest, giving `∑_p p^(-2) ≤ 49/100`.  Since `51/100 > 1/2`, the count
on `(0, 2N]` minus the trivial bound `N` on `(0, N]` leaves `#sf(N, 2N] ≥ N/50`: **every dyadic
block carries a positive proportion of squarefree integers**, which is exactly the block-mass input
of the no-go.

`[LEAN-PROVED]` The **undamped orbit-domain no-go** is closed, in
`formal/GaloisForLFunctions/RHTower/GammaOrbitDomainNoGo.lean` (imported by
`GaloisForLFunctions.RHTower`; builds clean, no warnings; axiom-clean).

| Card item | Lean name |
|---|---|
| the Gamma cyclic covariance `φ(h) = (cosh h)^(-1/2)` | `RHTower.gammaCyclicCovariance` |
| `φ > 0`, even, decreasing in `|h|` | `RHTower.gammaCyclicCovariance_pos`, `..._neg`, `..._le` |
| **`(11)`** dyadic logarithmic separation `≤ log 2` | `RHTower.abs_log_sub_log_le_log_two` |
| symmetric orbit covariance `≥ 2 φ(log d − log e)` | `RHTower.two_mul_gammaCyclicCovariance_le_inner_re` |
| **the no-go**: the undamped synthesis is not summable | `RHTower.not_summable_gammaOrbit` |
| `(13)` the canonical damping `η_d`, `b_d = 2^(1/4) d^(-1/2) η_d` | `RHTower.gammaDampingFactor`, `RHTower.gammaDampingWeight` |
| `0 < η_d ≤ 1` | `RHTower.gammaDampingFactor_pos`, `..._le_one` |
| **the damped coefficients are absolutely summable for `σ > 1`** | `RHTower.summable_gammaDampedWeight` |
| the orbit vectors are unit-normalised, `‖v_d‖ ≤ 2` | `RHTower.norm_gammaOrbitVector_le` |
| **the damped synthesis is a Hilbert vector** | `RHTower.summable_gammaDampedOrbit` |

The carrier enters **only** through its Gram relation
`⟨U_h ξ, U_k ξ⟩.re = φ(h − k)`, which is the abstract content of `(5)`; nothing is assumed about how
the pointed cyclic representation is realized, so the statement is unconditional relative to the
parent scattering carrier.

The Lean statement is also **stronger than the card**: the divergence is proved for every `σ ≤ 2`,
with no lower restriction `1 < σ` — the restriction plays no role in the block estimate.  The proof
is exactly the card's: given any finite set `s`, the dyadic block `B = (N, 2N] ∩ squarefree` with
`N = max s + 1` is disjoint from `s`; on it every pairwise covariance is at least `2φ(log 2) > 0`
by `(11)`, and its weight satisfies `∑_{d ∈ B} d^(-σ/2) ≥ #B/(2N) ≥ (N/50)/(2N) = 1/100` using
`d^(-σ/2) ≥ d^(-1)` for `σ ≤ 2` and the density bound `RHTower.card_filter_squarefree_Ioc_ge`.
Hence every such block has energy at least `2φ(log 2)/10⁴`, and
`HTGeometry.not_summable_of_cofinal_blocks` gives non-summability.

The **domain dichotomy** of the card is therefore machine-checked on both sides: with `b_d = 1` the
synthesis leaves the carrier for every `σ ≤ 2` (`not_summable_gammaOrbit`), while after the
canonical Gamma damping `(13)` it is a Hilbert vector for every `σ > 1`
(`summable_gammaDampedOrbit`), because the damped coefficients are dominated by
`2^(1/4) d^(-(σ+1)/2)` and the orbit vectors have norm at most `2` — the carrier being pointed at a
unit vector is itself read off the Gram relation at `h = k`.

`[LEAN-PROVED]` The **Fourier-inversion constant `(24)`** is reduced to its closed Gamma form in
`formal/GaloisForLFunctions/HTGeometry/TanhSubstitution.lean` (imported by
`GaloisForLFunctions.HTGeometry`; builds clean, no warnings; axiom-clean).

| Content | Lean name |
|---|---|
| `tanh' = 1/cosh²`, strict monotonicity, `1 - tanh² = 1/cosh²` | `HTGeometry.hasDerivAt_tanh`, `HTGeometry.tanh_strictMono`, `HTGeometry.one_sub_tanh_sq` |
| the exact image `tanh '' (0,∞) = (0,1)` | `HTGeometry.tanh_image_Ioi_zero` |
| **the tanh substitution** `∫_0^∞ cosh^(-s) = ∫_0^1 (1-x²)^(s/2-1)` | `HTGeometry.integral_cosh_rpow_neg_Ioi` |
| the square substitution `u = x²` | `HTGeometry.two_mul_integral_one_sub_sq_rpow` |
| **the real Euler Beta integral** `∫_0^1 u^(a-1)(1-u)^(b-1) = Γ(a)Γ(b)/Γ(a+b)` | `HTGeometry.integral_rpow_mul_one_sub_rpow` |
| **the closed value** `∫_0^∞ (cosh t)^(-s) dt = √π Γ(s/2)/(2Γ((s+1)/2))` | `HTGeometry.integral_cosh_rpow_neg_Ioi_eq` |
| the exponential envelope `cosh t ≥ e^{\|t\|}/2` and `(cosh t)^(-s) ≤ 2^s e^(-s\|t\|)` | `HTGeometry.exp_abs_div_two_le_cosh`, `HTGeometry.cosh_rpow_neg_le` |
| integrability of `(cosh t)^(-s)` on `ℝ` | `HTGeometry.integrable_cosh_rpow_neg` |
| **`(24)`** `∫_ℝ (cosh t)^(-s) dt = √π Γ(s/2)/Γ((s+1)/2)` | `HTGeometry.integral_cosh_rpow_neg` |

Mathlib has **no** derivative, monotonicity or image API for `Real.tanh` and no real Beta integral,
so all of it is built here.  At `s = 1/2` the closed value gives
`∫_0^∞ (cosh t)^(-1/2) dt = √π Γ(1/4)/(2 Γ(3/4))`, i.e. exactly the card's `(24)`
`ρ_Γ(0) = Γ(1/4)/(2√π Γ(3/4))` after doubling to the full line and dividing by `2π`.

`(24)` is therefore complete: at `s = 1/2`,
`∫_ℝ (cosh t)^(-1/2) dt = √π Γ(1/4)/Γ(3/4)`, so `ρ_Γ(0) = Γ(1/4)/(2√π Γ(3/4))` exactly as the card
states.

`[LEAN-PROVED]` The **pole scaling `(22)`** is available in the card's own form:

| Card item | Lean name |
|---|---|
| `(1)` `Z(σ) = ζ(σ)/ζ(2σ)` | `RHTower.ofReal_squarefreeMobiusTotal_eq_zetaRatio` (corpus) |
| `ζ(2)` has real part `π²/6` | `RHTower.re_riemannZeta_two` |
| **`(22)`** `(σ-1) Z(σ) → 6/π² = 1/ζ(2)` | `RHTower.tendsto_sub_one_mul_squarefreeMobiusTotal` |
| **`(22)`** `(σ-1) m_σ → 1` | `RHTower.tendsto_squarefreeMobiusLogMoment_one_critical` (corpus) |

`formal/GaloisForLFunctions/RHTower/SquarefreePartitionPole.lean` turns the corpus's reciprocal
statement `(Z σ)⁻¹/(σ-1) → ζ(2)` into the direct pole scaling with the closed real value; the second
half of `(22)` was already proved.

`[LEAN-PROVED]` The **holomorphic-remainder structure of `(19)` on the real axis** is in
`formal/GaloisForLFunctions/RHTower/GammaDampedSquarefreeSeries.lean` (imported by
`GaloisForLFunctions.RHTower`; builds clean, no warnings; axiom-clean).

| Card item | Lean name |
|---|---|
| the concavity defect `1 - (1+x)^(-1/4) ≤ x/4` | `RHTower.one_sub_rpow_quarter_le` |
| **`η_d - 1 = O(d^(-4))`**, uniformly | `RHTower.one_sub_gammaDampingFactor_le` |
| the damped mass `μ(d)² η_d d^(-σ)` and its summability | `RHTower.gammaDampedMass`, `RHTower.summable_gammaDampedMass` |
| the correction bound `\|F_d - Z_d\| ≤ d^(-4)/4` for every `σ ≥ 0` | `RHTower.abs_gammaDampedMass_sub_le` |
| **absolute convergence of the correction series** | `RHTower.summable_gammaDampedCorrection` |
| **`(19)`** `F(σ) = Z(σ) + H(σ)` with `H` bounded on `σ ≥ 0` | `RHTower.gammaDampedTotal_eq`, `RHTower.abs_tsum_gammaDampedCorrection_le` |
| **the damping does not move the pole**: `(σ-1) F(σ) → 6/π²` | `RHTower.tendsto_sub_one_mul_gammaDampedTotal` |

The Lean form is again stronger than the card: the correction is proved absolutely summable and
uniformly bounded on the whole half line `σ ≥ 0`, not merely near `σ = 1`, and the bound is the
explicit `(1/4)·ζ(4)`-type majorant `(1/4)∑_d d^(-4)`.  Only the complex-analytic continuation of
`H` past `σ = 1` remains for the full `(19)`.

`[LEAN-PROVED]` The **critical constant `(1)`, `(24)`, `(26)`, `(27)`--`(28)`** are closed, in
`formal/GaloisForLFunctions/HTGeometry/CoshHalfPowerLowerBound.lean` and
`formal/GaloisForLFunctions/RHTower/GammaCriticalConstant.lean` (imported by
`GaloisForLFunctions.HTGeometry` and `GaloisForLFunctions.RHTower`; build clean, no warnings;
axiom-clean).

| Card item | Lean name |
|---|---|
| the primitive `-2 arsinh(e^(-t/2))` of `(e^t+1)^(-1/2)` | `HTGeometry.hasDerivAt_expShiftPrimitive` |
| integrability of `(e^t+1)^(-1/2)` on the ray | `HTGeometry.integrableOn_invSqrtExpAddOne` |
| **the elementary integral** `∫_0^∞ (e^t+1)^(-1/2) = 2 arsinh 1` | `HTGeometry.integral_Ioi_invSqrtExpAddOne` |
| **the envelope `cosh t ≤ (e^t+1)/2`** in integrand form | `HTGeometry.sqrt_two_mul_inv_sqrt_le_cosh_rpow` |
| **`(27)`** `4√2 arsinh 1 ≤ √π Γ(1/4)/Γ(3/4)` | `HTGeometry.four_sqrt_two_mul_arsinh_one_le_gammaQuotient` |
| **`(28)`** `arsinh 1 > 7/8`, from `e^7 < 577 + 408√2 = (1+√2)^8` | `HTGeometry.seven_div_eight_lt_arsinh_one` |
| **`(24)`** `ρ_Γ(0) = Γ(1/4)/(2√π Γ(3/4))` | `RHTower.gammaCyclicDensityZero`, `RHTower.gammaCyclicDensityZero_eq` |
| **`(1)`, `(26)`** `C_Γ = 6√2 Γ(1/4)/(π^(3/2)Γ(3/4)) = 2√2 ρ_Γ(0) π/ζ(2)` | `RHTower.gammaCriticalConstant`, `RHTower.gammaCriticalConstant_eq_residueDensityProfile` |
| **`C_Γ > 4`** | `RHTower.four_lt_gammaCriticalConstant` |

`(26)` is stated exactly as the card's residue--density--profile law `(31)`: the constant is
`(pole residue) × (archimedean spectral density at zero) × (universal centred-pole profile)`, with
the residue entered through `(riemannZeta 2).re` so the identity is welded to the corpus's
`re_riemannZeta_two`.  The strict inequality is the card's own `(27)`--`(28)` chain and uses no
numerical evaluation of `Γ(1/4)/Γ(3/4)`: the Gamma quotient is bounded below by comparing the
half-power hyperbolic integral with its elementary envelope, giving `C_Γ ≥ 48 arsinh 1/π²`, and then
`12 arsinh 1 > 21/2 > 9.9225 > π²`.  Mathlib has no `arsinh` integral, no `tanh` calculus and no
real Beta integral, so both the closed value `(24)` and the lower bound `(27)` are built here.

`[LEAN-PROVED]` The **universal centred-pole profile `(25)`** is closed, in
`formal/GaloisForLFunctions/HTGeometry/CentredPoleProfileIntegral.lean` and
`formal/GaloisForLFunctions/RHTower/CentredPoleProfile.lean` (imported by
`GaloisForLFunctions.HTGeometry` and `GaloisForLFunctions.RHTower`; build clean, no warnings;
axiom-clean).

| Card item | Lean name |
|---|---|
| the rational profile `p(y) = y(3/4-y²)/(y²+1/4)²` | `HTGeometry.poleProfile` |
| **`Im[(1/2-iy)^(-2) - (1/2-iy)^(-1)] = p(y)`** | `RHTower.criticalPoleProfile`, `RHTower.criticalPoleProfile_eq` |
| the explicit primitive of `p²` | `HTGeometry.poleProfilePrimitive`, `HTGeometry.hasDerivAt_poleProfilePrimitive` |
| the majorant `p(y)² ≤ (y²+1/4)^(-1)` and integrability | `HTGeometry.poleProfile_sq_le`, `HTGeometry.integrable_poleProfile_sq` |
| vanishing of the rational part at both ends | `HTGeometry.tendsto_poleProfilePrimitiveRat_atTop`, `..._atBot` |
| **`(25)`** `∫_ℝ p(y)² dy = π` | `HTGeometry.integral_poleProfile_sq`, `RHTower.integral_criticalPoleProfile_sq` |
| **`(31)`** residue × density × profile, profile in integral form | `RHTower.gammaCriticalConstant_eq_profileEnergy` |

The primitive is `P(y) = (-(1/2)y⁵ + (5/12)y³ - (1/32)y)/(y²+1/4)³ + arctan(2y)`, so `(25)` is the
total variation `π` of `arctan` plus a rational part that vanishes at both ends; the integrability
majorant is the exact identity `(y²+1/4)³ - y²(3/4-y²)² = (9/4)(y² - 1/12)²`.  With this the law
`(31)` is machine-checked in its intended three-factor form: `C_Γ` equals the squarefree pole
residue `1/ζ(2)` times the archimedean spectral density at zero times the *integral* `(25)`, not a
hand-inserted constant `π`.

`[LEAN-PROVED]` The **complex Dirichlet reduction `(18)`--`(19)`** is closed, in
`formal/GaloisForLFunctions/RHTower/GammaDampedDirichletSeries.lean` (imported by
`GaloisForLFunctions.RHTower`; builds clean, no warnings; axiom-clean).

| Card item | Lean name |
|---|---|
| **`(18)`** the three coefficient families `[sf]`, `μ(d)²η_d`, `μ(d)²(η_d-1)` | `RHTower.squarefreeCoeff`, `RHTower.gammaDampedCoeff`, `RHTower.gammaDampedCorrectionCoeff` |
| `η_d - 1 = O(d^(-4))` in coefficient-norm form | `RHTower.norm_gammaDampedCorrectionCoeff_le` |
| **abscissa of the correction `≤ -3`** | `RHTower.abscissaOfAbsConv_gammaDampedCorrectionCoeff_le` |
| **`(19)`** `H` is holomorphic on `re z > -3` | `RHTower.analyticOnNhd_gammaDampedCorrectionLSeries`, `RHTower.analyticAt_gammaDampedCorrectionLSeries_one` |
| `∑_d [sf] d^(-z) = ζ(z)/ζ(2z)` in `LSeries` form | `RHTower.lSeries_squarefreeCoeff` |
| **`(19)`** `F(z) = ζ(z)/ζ(2z) + H(z)` on `re z > 1` | `RHTower.lSeries_gammaDampedCoeff` |
| the complex series restricts to the real total | `RHTower.ofReal_gammaDampedTotal_eq` |
| **`(22)` complex**: `(z-1)F(z) → 1/ζ(2) = 6/π²` in the Euler half plane | `RHTower.tendsto_sub_one_mul_lSeries_gammaDampedCoeff`, `..._closed` |

The bound `‖μ(d)²(η_d-1)‖ ≤ (1/4) d^(-4)` feeds mathlib's abscissa estimate to give abscissa `≤ -3`,
and mathlib's `LSeries_analyticOnNhd` then gives holomorphy of `H` on the whole half plane
`re z > -3` -- the card's "`H` is holomorphic on a neighborhood of the closed line used below" in its
strongest form.  The pole statement is proved by welding the corpus identity
`L([sf], z) = ζ(z)/ζ(2z)` to mathlib's `riemannZeta_residue_one` and the non-vanishing of `ζ(2)`,
with `(z-1)H(z) → 0` from holomorphy at `1`.  The limit is taken inside the Euler half plane, which
is where the series converges; on the real line it specialises to the already proved
`RHTower.tendsto_sub_one_mul_gammaDampedTotal` through `RHTower.ofReal_gammaDampedTotal_eq`.

`[LEAN-PROVED]` The **Laurent structure `(19)` and the scaled local limit `(20)`, `(23)`** are
closed, in `formal/GaloisForLFunctions/RHTower/GammaDampedLaurentAtOne.lean` and
`formal/GaloisForLFunctions/RHTower/GammaDampedScaledSpectralLimit.lean` (imported by
`GaloisForLFunctions.RHTower`; build clean, no warnings; axiom-clean).

| Card item | Lean name |
|---|---|
| the entire pole-free zeta `A(z) = ζ(z) - 1/((z-1)Γℝ(z))` | `RHTower.zetaPoleFree`, `RHTower.differentiable_zetaPoleFree` |
| `ζ(2z) ≠ 0` and holomorphy on `re z > 1/2` | `RHTower.riemannZeta_two_mul_ne_zero`, `RHTower.analyticAt_riemannZeta_two_mul` |
| **`(19)` additive form** `F(z) = C(z) + B(z)/(z-1)`, `B(1) = 1/ζ(2)` | `RHTower.lSeries_gammaDampedCoeff_laurent`, `RHTower.gammaDampedResidueFactor_one` |
| holomorphy of both Laurent parts on `re z > 1/2` | `RHTower.analyticAt_gammaDampedPoleFree`, `RHTower.analyticAt_gammaDampedResidueFactor` |
| the derivative in Laurent form | `RHTower.deriv_lSeries_gammaDampedCoeff` |
| **`(z-1)² F'(z) → -1/ζ(2)`** | `RHTower.tendsto_sub_one_sq_mul_deriv_lSeries_gammaDampedCoeff` |
| the scaled point `z_ε = 1 + ε(1/2 - iy)` and its half-plane approach | `RHTower.criticalScaledPoint`, `RHTower.tendsto_criticalScaledPoint` |
| `ε F(z_ε) → 1/(ζ(2) w)` and `ε² F'(z_ε) → -1/(ζ(2) w²)` | `RHTower.tendsto_mul_lSeries_gammaDampedCoeff`, `RHTower.tendsto_sq_mul_deriv_lSeries_gammaDampedCoeff` |
| **`(22)`** `ε m_(1+ε) → 1` in the `ε` parametrisation | `RHTower.tendsto_mul_squarefreeMobiusLogMoment` |
| **`(20)`** the spectral symbol `D_ε` at `x = εy` | `RHTower.gammaDampedSpectralSymbol` |
| **`(23)`** `ε² D_ε(εy) → (1/ζ(2))[w^(-2) - w^(-1)]` | `RHTower.tendsto_sq_mul_gammaDampedSpectralSymbol` |
| the limit's imaginary part is `(6/π²) p(y)` | `RHTower.im_gammaDampedSpectralLimit` |

The Laurent step needs no removable-singularity argument: mathlib's completed-normalisation lemma
`ζ(z) - 1/((z-1)Γℝ(z))` differentiable at `1` makes `A` entire, so `F = C + B/(z-1)` is an *identity*
of holomorphic functions on `re z > 1`, and both critical scalings follow by continuity of `B`, `C`
and their derivatives.  `(23)` is then the composition of these two scalings with the corpus moment
law `(σ-1)m_σ → 1`, and its imaginary part is exactly `(6/π²)` times the centred-pole profile whose
energy `(25)` is `π` -- the two factors of `(26)` that multiply the archimedean density.

`[LEAN-PROVED]` The **Fourier transform of the Gamma cyclic covariance** -- the gateway to `(15)` --
is closed, in `formal/GaloisForLFunctions/HTGeometry/CoshFourierTransform.lean` (imported by
`GaloisForLFunctions.HTGeometry`; builds clean, no warnings; axiom-clean).

| Content | Lean name |
|---|---|
| the logistic substitution `v = e^t/(2 cosh t)` with its calculus and exact image | `HTGeometry.logisticVar`, `HTGeometry.hasDerivAt_logisticVar`, `HTGeometry.logisticVar_image_univ` |
| the two logarithmic identities `log v = t - log(2 cosh t)`, `log(1-v) = -t - log(2 cosh t)` | `HTGeometry.log_logisticVar`, `HTGeometry.log_one_sub_logisticVar` |
| the Beta integrand in hyperbolic coordinates | `HTGeometry.betaIntegrand_logisticVar` |
| **`∫_ℝ (cosh t)^(-s) e^(-ixt) dt = 2^(s-1) Γ((s-ix)/2)Γ((s+ix)/2)/Γ(s)`** | `HTGeometry.integral_cosh_rpow_neg_mul_exp` |
| the transform as a real quantity `2^(s-1)\|Γ((s+ix)/2)\|²/Γ(s)` | `HTGeometry.integral_cosh_rpow_neg_mul_exp_eq_ofReal` |
| **its nonnegativity** -- the positivity behind `(15)` | `HTGeometry.integral_cosh_rpow_neg_mul_exp_nonneg` |

This is the `x ≠ 0` generalisation of the closed value `(24)`: the same substitution, run with the
complex Beta parameters `(s ∓ ix)/2`, using mathlib's `Complex.betaIntegral`.  Conjugation symmetry
`Γ(z̄) = conj Γ(z)` turns the product of the two Gamma values into `‖Γ((s+ix)/2)‖²`, so the transform
of the Gamma cyclic covariance is **manifestly nonnegative** -- which is exactly what makes
`ν_Γ` of `(15)` a measure.  At `s = 1/2` it reads
`∫_ℝ (cosh t)^(-1/2) e^(-ixt) dt = 2^(-1/2) ‖Γ(1/4 + ix/2)‖²/√π ≥ 0`.

`[LEAN-PROVED]` **Fourier inversion for the Gamma cyclic covariance** is closed, in
`formal/GaloisForLFunctions/HTGeometry/CoshFourierInversion.lean` (imported by
`GaloisForLFunctions.HTGeometry`; builds clean, no warnings; axiom-clean).

| Content | Lean name |
|---|---|
| `φ' = -(1/2)(cosh t)^(-3/2) sinh t` | `HTGeometry.hasDerivAt_coshHalfReal`, `HTGeometry.deriv_coshHalf` |
| **`φ'' = (1/4)(cosh t)^(-1/2) - (3/4)(cosh t)^(-5/2)`** | `HTGeometry.hasDerivAt_coshHalfDerivReal`, `HTGeometry.deriv_coshHalfDeriv` |
| integrability of `φ`, `φ'`, `φ''` | `HTGeometry.integrable_coshHalf`, `..._coshHalfDeriv`, `..._coshHalfDeriv2` |
| two integrations by parts: `𝓕φ'' = (2πix)² 𝓕φ` | `HTGeometry.fourier_coshHalfDeriv2` |
| the quadratic decay `‖𝓕φ(x)‖·4π²x² ≤ ‖φ''‖₁` | `HTGeometry.norm_sq_mul_fourier_coshHalf_le` |
| **`𝓕φ` is integrable** | `HTGeometry.integrable_fourier_coshHalf` |
| **inversion** `𝓕⁻(𝓕φ) = φ` | `HTGeometry.fourierInv_fourier_coshHalf` |

The closed second derivative is what makes this elementary: `sinh² = cosh² - 1` collapses the
derivative of `-(1/2)(cosh)^(-3/2) sinh` to a combination of two hyperbolic powers, both integrable
by the already proved envelope, so the standard `‖𝓕φ‖ ≤ min(‖φ‖₁, ‖φ''‖₁/(2πx)²)` bound gives
`𝓕φ ∈ L¹` by comparison with `(1+x²)^(-1)`.  With the closed nonnegative value of `𝓕φ` this is
exactly the data of `(15)`: `φ` is the characteristic function of the measure with density `𝓕φ ≥ 0`.

`[LEAN-PROVED]` **The Gamma cyclic spectral measure `ν_Γ` and the spectral form `(15)`** are closed,
in `formal/GaloisForLFunctions/HTGeometry/GammaCyclicSpectralMeasure.lean` (imported by
`GaloisForLFunctions.HTGeometry`; builds clean, no warnings; axiom-clean).

| Card item | Lean name |
|---|---|
| the archimedean density `ρ(x) = 2^(-1/2)\|Γ(1/4+iπx)\|²/√π` | `HTGeometry.gammaCyclicDensity` |
| `𝓕φ = ρ`, `ρ ≥ 0`, `ρ` continuous and integrable | `HTGeometry.fourier_coshHalf_apply`, `..._nonneg`, `continuous_gammaCyclicDensity`, `integrable_gammaCyclicDensity` |
| **`∫ e^(2πihx) ρ(x) dx = (cosh h)^(-1/2)`** | `HTGeometry.integral_exp_mul_gammaCyclicDensity` |
| the cosine form and the total mass `∫ρ = 1` | `HTGeometry.integral_cos_mul_gammaCyclicDensity`, `HTGeometry.integral_gammaCyclicDensity` |
| **`ν_Γ` as a probability measure** | `HTGeometry.gammaCyclicMeasure`, `HTGeometry.isProbabilityMeasure_gammaCyclicMeasure` |
| **`(5)`** `∫ e^(ihy) dν_Γ(y) = φ(h)` | `HTGeometry.integral_exp_gammaCyclicMeasure` |
| **`(15)`** `φ(h-k) - φ(h+k) = 2∫ sin(hy) sin(ky) dν_Γ(y)` | `HTGeometry.gammaCyclicOddKernel_measure_eq` (density form: `gammaCyclicOddKernel_eq`) |

`ν_Γ` is built exactly as the card describes it -- *the* probability measure whose characteristic
function is `φ` -- with no hypothesis: the density is the closed nonnegative Fourier transform, its
mass is `φ(0) = 1`, and the pushforward under `x ↦ 2πx` puts it in the `e^(ihy)` normalisation.  The
odd-kernel identity `(15)` is then the real part of the difference of the characteristic function at
`h-k` and `h+k`, via `cos A - cos B = 2 sin((A+B)/2) sin((B-A)/2)`.

`[LEAN-PROVED]` The **abstract odd spectral synthesis norm** -- the analytic core of `(21)` -- is
closed, in `formal/GaloisForLFunctions/HTGeometry/OddSpectralSynthesis.lean` (imported by
`GaloisForLFunctions.HTGeometry`; builds clean, no warnings; axiom-clean).

| Content | Lean name |
|---|---|
| `‖∑ y_d‖² = ∑_e ∑_d ⟪y_e, y_d⟫` for an absolutely convergent synthesis | `HTGeometry.norm_sq_tsum_eq_tsum_inner` |
| the sine series and its uniform bounds | `HTGeometry.sinSeries`, `HTGeometry.continuous_sinSeries`, `HTGeometry.abs_sinSeries_le` |
| uniformly dominated interchange `∫ ∑ = ∑ ∫` on a finite measure | `HTGeometry.integral_tsum_of_bounded` |
| **`∫ (∑ c_d sin(h_d y))² dν = ∑_d ∑_e c_d c_e ∫ sin sin dν`** | `HTGeometry.integral_sinSeries_sq` |
| **`(21)` core**: odd Gram `⟪v_d,v_e⟫ = 2∫ sin sin dν` gives `‖∑ c_d v_d‖² = 2∫(∑ c_d sin(h_d y))² dν` | `HTGeometry.norm_sq_oddSynthesis` |

The statement is proved for an arbitrary real Hilbert space, an arbitrary finite measure and an
arbitrary absolutely summable coefficient family, so it applies verbatim to the Gamma carrier through
`HTGeometry.gammaCyclicOddKernel_measure_eq`: the Gram hypothesis is exactly `(15)`.  Both
interchanges of sum and integral are justified by the single uniform majorant `(∑|c_d|)² ν(ℝ)`.

`[LEAN-PROVED]` **The spectral identity `(20)`--`(21)`** is closed, in
`formal/GaloisForLFunctions/RHTower/GammaDampedSineSeries.lean` (imported by
`GaloisForLFunctions.RHTower`; builds clean, no warnings; axiom-clean).

| Card item | Lean name |
|---|---|
| the vertical line `α - ix`, `α = (σ+1)/2`, and its identification with the scaled point | `RHTower.criticalLinePoint`, `RHTower.criticalScaledPoint_eq` |
| **`(20)`** the symbol `D(σ,x) = -F'(α-ix) - m_σ F(α-ix)` | `RHTower.gammaDampedSymbol`, `RHTower.gammaDampedSpectralSymbol_eq` |
| the odd coefficients `μ(d)²η_d(log d - m_σ)d^(-α)` and their absolute summability | `RHTower.gammaDampedSineCoeff`, `RHTower.summable_abs_gammaDampedSineCoeff` |
| the symbol as a Dirichlet series with those coefficients | `RHTower.gammaDampedSymbol_eq_lSeries` |
| **`Im D(σ,x) = ∑_d μ(d)²η_d(log d - m_σ)d^(-α) sin(x log d)`** | `RHTower.im_gammaDampedSymbol` |
| **`(21)`** `‖∑ c_d v_d‖² = 2 ∫ (Im D(σ,y))² dν_Γ(y)` for any odd-Gram synthesis | `RHTower.norm_sq_gammaDampedOddSynthesis` |

The Dirichlet reduction uses mathlib's `LSeries_deriv` on the half plane `re z > 1` (the abscissa of
`μ(d)²η_d` is at most `1`), so `-F' - m_σ F` is literally the L-series of
`(log d - m_σ)·μ(d)²η_d`; the imaginary part of each term is computed from
`d^(-(α-ix)) = d^(-α)(cos(x log d) + i sin(x log d))`.  Absolute summability of the coefficients uses
the corpus bound `RHTower.summable_abs_log_natCast_pow_mul_rpow_neg` at `β = α > 1`.  Feeding the
Gram relation `(15)` into the abstract odd synthesis norm then gives `(21)` with **no hypothesis on
the carrier beyond its Gram matrix**.

`[LEAN-PROVED]` The **logarithmic vertical-line bound for zeta** -- the far-field input of `(17)` --
is closed, in `formal/GaloisForLFunctions/RHTower/ZetaVerticalLineBound.lean` (imported by
`GaloisForLFunctions.RHTower`; builds clean, no warnings; axiom-clean).

| Content | Lean name |
|---|---|
| `‖n^z‖ = n^(re z)` for `n ≥ 1` | `RHTower.norm_natCast_cpow` |
| the Dirichlet polynomial is at most the harmonic number | `RHTower.norm_dirichletPoly_le_one_add_log` |
| the Euler--Maclaurin pole term is at most `1/2` when `\|t\| ≥ 2` | `RHTower.norm_emPole_le` |
| **`\|ζ(σ+it)\| ≤ log\|t\| + 5` for `1 ≤ σ ≤ 2`, `\|t\| ≥ 2`** | `RHTower.norm_riemannZeta_le_log_add` |

This reuses the corpus's own unconditional Euler--Maclaurin carrier
(`RHTower.zeta_sub_emCarrier_norm_le`: `‖ζ(s) - emCarrier N s‖ ≤ ‖s‖ N^(-σ)/σ`) at the truncation
`N = ⌈\|t\|⌉`, so nothing about the representation had to be rebuilt: the three pieces are the
harmonic bound `1 + log N`, the pole bound `N^(1-σ)/\|s-1\| ≤ 1/2`, and the remainder
`‖s‖/N ≤ 2`.  The bound is **uniform in `σ` down to `σ = 1`**, which is exactly what the critical
scaling `α = 1 + ε/2 → 1` needs.

`[LEAN-PROVED]` The **vertical-line bound for the damped series itself** is closed, in
`formal/GaloisForLFunctions/RHTower/GammaDampedVerticalBound.lean` (imported by
`GaloisForLFunctions.RHTower`; builds clean, no warnings; axiom-clean).

| Content | Lean name |
|---|---|
| `∑_{n≥1} n^(-2) = π²/6 ≤ 2` | `RHTower.tsum_inv_natCast_sq_le` |
| termwise-bounded Dirichlet series are bounded on `re s ≥ 2` | `RHTower.norm_lSeries_le_of_term_bound`, `RHTower.norm_term_le_inv_sq` |
| **`‖1/ζ(s)‖ ≤ 2` for `re s ≥ 2`** (Möbius series) | `RHTower.norm_inv_riemannZeta_le` |
| **`‖H(z)‖ ≤ 1/2` for `re z ≥ 0`** | `RHTower.norm_gammaDampedCorrectionLSeries_le` |
| **`‖F(z)‖ ≤ 2(log\|Im z\| + 5) + 1/2`** on `1 < re z ≤ 2`, `\|Im z\| ≥ 2` | `RHTower.norm_lSeries_gammaDampedCoeff_le` |

Combined with the Dirichlet reduction `F = ζ(z)/ζ(2z) + H(z)` this is the far-field control the
dominated-convergence step needs: it is **uniform in `σ` down to `1`**, and both auxiliary series are
compared against `∑ n^(-2)` with no analytic input.

`[LEAN-PROVED]` The **Cauchy estimate for the derivative on the critical vertical line** is closed,
in `formal/GaloisForLFunctions/RHTower/GammaDampedVerticalBound.lean`.

| Content | Lean name |
|---|---|
| the disc of radius `(σ-1)/4` around `α - ix` stays in `1 < re ≤ 2`, `\|Im\| ≥ 2` | `RHTower.mem_strip_of_dist_le` |
| **`‖F'(α-ix)‖ ≤ (2(log(2\|x\|)+5) + 1/2)/((σ-1)/4)`** | `RHTower.norm_deriv_lSeries_gammaDampedCoeff_le` |

The disc is small enough (radius `ε/4` at `α = 1 + ε/2`) to stay inside the half plane of absolute
convergence, where mathlib's `LSeries_differentiableOn` applies, and large enough that the Cauchy
estimate loses only the factor `4/ε` -- exactly the factor the far-field estimate can absorb, since
`m_σ ≍ 1/ε` appears anyway.

`[LEAN-PROVED]` The **tail data of the density** is in place, in
`formal/GaloisForLFunctions/HTGeometry/GammaCyclicSpectralMeasure.lean`:

| Content | Lean name |
|---|---|
| `ρ(x) ≤ ‖φ‖₁` | `HTGeometry.gammaCyclicDensity_le_bound` |
| **`ρ(x)·4π²x² ≤ ‖φ''‖₁`** (quadratic decay) | `HTGeometry.gammaCyclicDensity_mul_sq_le` |
| `ρ` is even | `HTGeometry.gammaCyclicDensity_neg` |

`[LEAN-PROVED]` The **logarithmic tail integral** is closed, in
`formal/GaloisForLFunctions/HTGeometry/GammaCyclicDensityTail.lean` (imported by
`GaloisForLFunctions.HTGeometry`; builds clean, no warnings; axiom-clean).

| Content | Lean name |
|---|---|
| `{x : 3 ≤ \|x\|} = Iic (-3) ∪ Ici 3` and `∫_{\|x\|≥3} \|x\|^(-3/2) < ∞` | `HTGeometry.setOf_three_le_abs`, `HTGeometry.integrableOn_abs_rpow_tail` |
| `log(2\|x\|) ≤ 8\|x\|^(1/4)` and `(log(2\|x\|)+C)² ≤ (128+2C²)\|x\|^(1/2)` | `HTGeometry.log_two_mul_abs_le`, `HTGeometry.log_weight_le` |
| **`∫_{\|x\|≥3} (log(2\|x\|)+C)² ρ(x) dx < ∞`** | `HTGeometry.integrableOn_log_sq_mul_gammaCyclicDensity` |

The negative half line is handled by the measure-preserving reflection
(`Measure.measurePreserving_neg` + `MeasurePreserving.integrableOn_comp_preimage`), so no evenness of
the weight is needed.  This is the last standing analytic input of the far field: the weight is
exactly the square of the vertical-line bound, and the density's quadratic decay
(`gammaCyclicDensity_mul_sq_le`) turns the product into the convergent tail `|x|^(-3/2)`.

`[LEAN-PROVED]` The **far-field estimate** of `(17)` is closed, in
`formal/GaloisForLFunctions/RHTower/GammaDampedFarField.lean` (imported by
`GaloisForLFunctions.RHTower`; builds clean, no warnings; axiom-clean).

| Content | Lean name |
|---|---|
| **`\|Im D(σ,u)\| ≤ (12/(σ-1))(log(2\|u\|)+6)` for `\|u\| ≥ 3`** | `RHTower.abs_im_gammaDampedSymbol_le` |
| the same in the density variable `u = 2πx` | `RHTower.abs_im_gammaDampedSymbol_scaled_le` |
| continuity of `u ↦ D(σ,u)` on the whole line | `RHTower.continuous_gammaDampedSymbol` |
| **`∫_{\|x\|≥3}(Im D(σ,2πx))² ρ(x) dx ≤ (12/(σ-1))² · (finite tail)`** | `RHTower.gammaDampedFarEnergy_le` |

Multiplied by the `ε³` of the critical scaling this is `O(ε)`, so the far field contributes nothing
in the limit -- with a **single** estimate, no region-dependent constants.  The two hypotheses on the
first logarithmic moment (`0 ≤ m_σ` and `m_σ ≤ 2/(σ-1)`) hold eventually as `σ → 1+` by the proved
limit `RHTower.tendsto_mul_squarefreeMobiusLogMoment`.

`[LEAN-PROVED]` The **near-field Laurent split and its uniform bounds** are in place, in
`formal/GaloisForLFunctions/RHTower/GammaDampedNearField.lean` (imported by
`GaloisForLFunctions.RHTower`; builds clean, no warnings; axiom-clean).

| Content | Lean name |
|---|---|
| the compact window `K = closedBall 1 (1/2+6π) ∩ {re ≥ 1} ⊆ {re > 1/2}` | `RHTower.nearFieldSet`, `RHTower.isCompact_nearFieldSet`, `RHTower.nearFieldSet_subset` |
| every critical point with `1 < σ ≤ 2`, `\|u\| ≤ 6π` lies in `K` | `RHTower.mem_nearFieldSet` |
| **a single uniform bound `M` for `B, B', C, C'` on `K`** | `RHTower.exists_nearField_bound` |
| **the Laurent split `D = P + R`** with `P = B/(z-1)² - m B/(z-1)`, `R = -B'/(z-1) - C' - mC` | `RHTower.gammaDampedPolePart`, `RHTower.gammaDampedRegPart`, `RHTower.gammaDampedSymbol_eq_polePart_add_regPart` |
| **`‖R‖ ≤ 5M/(σ-1)`** on the window | `RHTower.norm_gammaDampedRegPart_le` |

The regular part therefore contributes `ε³·(5M/ε)²·ν(ℝ) = 25M²ε → 0` to the critical scaling with no
change of variables at all, and the pole part is the explicit rational expression whose scaled
majorant `M/\|w\|² + KM/\|w\|` is square integrable -- the two ingredients of the near-field
dominated-convergence step.

*Note for future sessions*: a concurrent agent renamed `RHTower.criticalLinePoint` to
`RHTower.gammaDampedCriticalLinePoint` (and `abscissa_lt_criticalLinePoint` likewise) in
`GammaDampedSineSeries.lean`; use the new names.

### Remaining

1. **The spectral identity `(15)`, `(21)` and the final limit `(17)`.**  Everything on the Dirichlet
   side is now machine-checked: the reduction `(18)`--`(19)` with its holomorphic remainder, the
   Laurent form, the pole residue `(22)`, the scaled symbol `(20)` and its exact local limit `(23)`.
   Everything on the archimedean side is machine-checked too: the density `(24)`, the profile energy
   `(25)`, the combination `(26)`/`(31)` and the strict bound `(1)`/`(27)`--`(28)`.

   What remains is the *bridge*: the spectral representation `(15)` of the odd Gamma kernel
   `K_odd(h,k) = φ(h-k) - φ(h+k) = 2∫ sin(hx) sin(kx) dν_Γ(x)`, which needs the Gamma cyclic measure
   `ν_Γ` itself, and then `(21)` plus the dominated-convergence step that turns `(23)` into `(17)`.
   `(15)` is now proved with the measure `ν_Γ` constructed unconditionally.  What remains is the
   norm identity `(21)` and the final limit `(17)`:

   * `(17)` alone remains.  The passage `(21) → (17)` is the substitution `x = εy` in
     `∫ (Im D)² dν_Γ` together with the proved local limit `(23)`, split as the card describes:

     - **pole window** `|x| ≤ δ`: the Laurent form `F = C + B/(z-1)` gives the majorant
       `|ε² D(1+ε, εy)| ≲ 1/|1/2 - iy|² + 1/|1/2 - iy|`, which is square integrable in `y`, so
       dominated convergence applies and produces `ρ_Γ(0) · ∫ (Im[w^(-2) - w^(-1)])² dy /ζ(2)²`,
       i.e. `(24)·(25)` against the pole residue;
     - **far field** `|x| > δ`: the vertical-line bound is now proved, so the remaining steps are
       mechanical:
       1. `‖F(z)‖ ≲ log|x| + C` -- **proved**, `RHTower.norm_lSeries_gammaDampedCoeff_le`;
       2. `‖F'(α - ix)‖ ≲ (log|x|)/ε` -- **proved**,
          `RHTower.norm_deriv_lSeries_gammaDampedCoeff_le`;
       3. hence `ε³ ∫_{|x|>δ} (Im D)² ρ ≲ ε ∫ log²|x| ρ(x) dx → 0`.  The density inputs are proved
          (`gammaCyclicDensity_le_bound`, `gammaCyclicDensity_mul_sq_le`, `gammaCyclicDensity_neg`);
          and both the tail integral and the far-field energy estimate are **proved**
          (`HTGeometry.integrableOn_log_sq_mul_gammaCyclicDensity`,
          `RHTower.gammaDampedFarEnergy_le`).  What is left is the near field `|x| ≤ 3`: split the
          symbol there as `D = D_pole + D_reg` with
          `D_pole = (1/ζ(2))[(z-1)^(-2) - m_σ (z-1)^(-1)]`, apply dominated convergence to the pole
          part (its scaled majorant `1/|w|² + K/|w|` is square integrable, so mathlib's
          `tendsto_integral_filter_of_dominated_convergence` applies directly) and the `O(ε)`
          estimate to the regular part, whose Laurent bounds are uniform on the compact set
          `{α - iu : ε ∈ [0,1], |u| ≤ 6π}` -- **all of this is now proved**
          (`RHTower.gammaDampedSymbol_eq_polePart_add_regPart`, `RHTower.norm_gammaDampedRegPart_le`,
          `RHTower.exists_nearField_bound`).  What is left is only the integral bookkeeping: the
          change of variables `x = εv/(2π)` for the pole part, its dominated convergence against the
          proved pointwise limit `(23)`, the `O(ε)` estimate for the regular part, the
          Cauchy--Schwarz cross term, and the assembly of the constant through `(24)`, `(25)`
          and `(26)`.
       No higher derivatives of `φ` and no `ζ'` bound are needed on this route.
