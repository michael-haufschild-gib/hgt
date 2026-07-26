# The complementary incidence packet has the exact shifted-Euler connection source

- **ID:** `complementary-packet-euler-connection-weld`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / SOURCE-FRAMED GAMMA WELD
- **Scientific status:** `[PROVED HERE] [LITERATURE NOVELTY OPEN] [NOT AN RH PROOF]`
- **Parents:**
  - `not_new_scientific_knowledge/coupled-floor-mobius-complementary-shift-incidence-law.md`
  - `not_new_scientific_knowledge/suzuki-euler-pole-archimedean-moment-annihilation.md`
  - `not_new_scientific_knowledge/suzuki-tail-is-exact-summatory-error-transform.md`
- **Statement:** Differentiating the exact complementary floor/tail packet in its divisor-clock
  coordinate produces one unit moving boundary atom plus the shifted power-sum atoms.  Signed
  Mobius synthesis combines them exactly into the centered positive shifted-Euler source.  The
  Gamma moment then annihilates precisely its main density.  This is an incidence-before-Gamma,
  pre-divisor source identity; no Xi zero or target norm enters.

## Continuous divisor-clock packet

Fix `omega>0` and `delta>0`.  Put

```text
q_delta(t)=e^(-delta t),
c_omega=1/(1+omega),

R_omega(Y)=sum_(m<=Y)m^omega-Y^(1+omega)/(1+omega),
k_(omega,delta)(t)
 =e^(-(1+omega+delta)t)R_omega(e^t).                     (1)
```

For a continuous clock value `h>=0`, define the distributional `L2` packet

```text
B_h(t)
 =e^(-delta h)1_(t>=h)k_(omega,delta)(t-h)
  -c_omega 1_(t<h)q_delta(t).                            (2)
```

At `h=log d`, equation `(2)` is exactly the proved packet

```text
d^(-delta)V_(log d)k_(omega,delta)
 -(1/(1+omega))(I-P_d)q_delta.                           (3)
```

The two branches meet with the source-fixed jump

```text
B_h(h+)-B_h(h-)
 =e^(-delta h)(k_(omega,delta)(0)+c_omega)
 =e^(-delta h),                                          (4)
```

because

```text
k_(omega,delta)(0)=R_omega(1)=omega/(1+omega).            (5)
```

Thus the moving incidence boundary has unit coefficient before any completion.

## Packet connection equation `[PROVED HERE]`

As a distribution in `t`, the packet path satisfies

```text
(partial_h-(1+omega))B_h
 =q_delta
  -sum_(m>=1)e^(-delta h)m^(-1-delta)
     delta_(h+log m).                                    (6)
```

### Proof

Away from the jump points of the power sum, distributional differentiation of `(1)` gives

```text
k'_(omega,delta)
 =-(1+omega+delta)k_(omega,delta)-q_delta.               (7)
```

At `t=log m`, `m>=2`, the jump of `k_(omega,delta)` is

```text
m^omega m^(-(1+omega+delta))=m^(-1-delta).               (8)
```

For `t<h`, the left side of `(6)` is

```text
0-(1+omega)(-c_omega q_delta)=q_delta.                   (9)
```

For `t>h` away from the shifted jumps, `(7)` gives the same value `q_delta`.  Moving the boundary
`t=h` contributes minus the jump `(4)`, which is the `m=1` term in `(6)`.  Moving every shifted
jump `(8)` contributes the corresponding negative atom.  This proves `(6)`. `QED`

## Exact Mobius synthesis `[PROVED HERE]`

Let

```text
c_omega(n)
 =n^omega product_(p|n)(1-p^(-2omega))
 =sum_(dm=n)mu(d)d^(-omega)m^omega.                      (10)
```

Multiply `(6)` at `h=log d` by `mu(d)d^(-1-2omega)` and sum over `d`.  Both the divisor sum and
the atomic sum converge absolutely for `delta>0`.  The continuous term is

```text
sum_d mu(d)d^(-1-2omega)q_delta
 =q_delta/zeta(1+2omega).                                (11)
```

At the atom `t=log n`, write `n=dm`.  Its coefficient is

```text
n^(-delta)
 sum_(dm=n)mu(d)d^(-1-2omega)m^(-1)
 =c_omega(n)n^(-1-omega-delta).                          (12)
```

Therefore

```text
sum_d mu(d)d^(-1-2omega)
 (partial_h-(1+omega))B_h|_(h=log d)

 =q_delta/zeta(1+2omega)
  -sum_(n>=1)c_omega(n)n^(-1-omega-delta)
     delta_(log n).                                      (13)
```

The right side is the negative of the centered shifted-Euler atomic connection: the first term is
its exact Euler main density, and the second is its positive arithmetic source.

## Gamma completion weld

Suzuki's kernel has Mellin multiplier

```text
G_omega(s)=gamma(s-omega)/gamma(s+omega)                 (14)
```

and the exact zero moment

```text
integral_0^1 g_omega^(1)(x)x^omega dx=0.                 (15)
```

Under logarithmic Mellin/Stieltjes convolution, `(15)` annihilates the first term in `(13)`
exactly.  The atomic term becomes

```text
x^(-1)sum_(n<=x)c_omega(n)g_omega^(1)(n/x),              (16)
```

which is Suzuki's completed causal source.  Equivalently, subtracting the main density before or
after Gamma completion gives the same error-transform identity.

Thus the weld

```text
complementary divisor incidence
  -> divisor-clock connection `(6)`
  -> signed Mobius synthesis `(13)`
  -> Gamma zero-moment completion `(16)`                 (17)
```

is exact and source-framed before any Xi divisor expansion.

## Relation to the four-unit incidence curvature

The moving boundary atom in `(4)` is the distributional derivative of the same threshold
involution

```text
S_t e_d=(2*1_(log d<=t)-1)e_d                           (18)
```

whose commutator with the signed source projection has critical relative energy four.  Equations
`(6)` and `(13)` now identify the missing affine/source part of that curvature: the off-diagonal
threshold field carries the four-unit metric, while its clock connection carries the exact
shifted-Euler source and Gamma calibration.

This closes the entrywise incidence-before-Gamma identity.  It does not yet prove that inserting
the connection part into the Gamma/Sonin relative square is trace-neutral or orthogonal to the
four-unit curvature.

## No-go and positive successor

**No-go.**  Applying Gamma only to the bare threshold curvature is rational-gauge blind and cannot
identify the Xi seam.  Applying Gamma only to the positive shifted-Euler atoms discards the
four-unit signed incidence angle.

**Positive successor.**  Use `(17)` as the affine connection weld on the already asymptotically
passive Gamma/Sonin curvature.  Prove that the connection correction is a trace-zero commutator or
a Lueders-orthogonal block in the source relative trace.  Then the proved four-unit upper bound is
preserved while `(16)` supplies the exact completed arithmetic framing.

**Positive general-HT statement.**  A complementary incidence can carry two independently
necessary boundary data: its commutator curvature supplies a metric charge, while the derivative
of its affine packet path supplies the source connection.  Neither determines the other, but the
unit moving jump welds them canonically.

## Literature gate

Distributional differentiation of moving steps, divisor convolution, and Stieltjes/Mellin
summation are standard mechanisms.  Targeted searches have not located the exact packet
connection equation `(6)` or the weld `(13)`--`(17)` in this squarefree/Suzuki form.  Project
inputs are admissible regardless; specialist external audit remains required before any novelty
claim.

## Gates

- [x] continuous divisor-clock packet written
- [x] unit moving boundary jump proved
- [x] distributional packet connection equation proved
- [x] exact shifted power-sum atoms identified
- [x] signed Mobius synthesis evaluated
- [x] shifted-Euler coefficients recovered exactly
- [x] Gamma main-moment annihilation welded
- [x] pre-divisor completed causal source identity proved
- [ ] insert the connection weld into the Gamma/Sonin relative square
- [ ] prove trace neutrality or Lueders orthogonality
- [ ] continue the framed source to `ell_E`
- [ ] independent specialist literature audit
- [ ] RH

## Formalization

Both `[PROVED HERE]` sections of this card — the packet connection equation `(6)` and the exact
Möbius synthesis `(13)` — are compiled unconditionally in Lean.  Every module builds clean with no
warnings and `#print axioms` gives exactly `propext, Classical.choice, Quot.sound`.

### The packet connection

`formal/GaloisForLFunctions/RHTower/DampedComplementaryPacketConnection.lean`

| Card item | Lean name |
|---|---|
| `(1)` damped divisor-clock kernel `k_{ω,δ}` | `RHTower.dampedPacketKernel` |
| its closed step form | `RHTower.dampedPacketKernel_eq` |
| zero damping recovers the boundary kernel | `RHTower.dampedPacketKernel_zero_damping` |
| **`(5)`** `k_{ω,δ}(0) = R_ω(1) = ω/(1+ω)` | `RHTower.dampedPacketKernel_zero` |
| `(2)` the continuous divisor-clock packet | `RHTower.dampedPacketPath` |
| left limit of the incoming branch | `RHTower.tendsto_dampedPacketPath_nhdsLT` |
| **`(4)`** the unit moving boundary jump `e^(-δh)` | `RHTower.dampedPacketPath_jump` |
| **`(6)`** the packet connection equation | `RHTower.dampedPacketPath_connection` |
| **`(7)`** `k' = -(1+ω+δ)k - q_δ` between atoms | `RHTower.hasDerivAt_dampedPacketKernel` |
| **`(8)`** the shifted power-sum atom `m^(-1-δ)` at `log m` | `RHTower.tendsto_dampedPacketKernel_nhdsLT` |

`(6)` is a statement about distributions in `t`.  It is formalised in the equivalent **integrated**
form obtained by taking the `h`-primitive, which turns every atom into an absolutely continuous
contribution and therefore holds pointwise, with no distributional interpretation and no test
functions: for `0 < ω`, every `δ`, all `h₁ ≤ h₂` and **every** `t`,

```text
e^(-(1+ω)h₂) B_{h₂}(t) - e^(-(1+ω)h₁) B_{h₁}(t)
  = e^(-δt) (e^(-(1+ω)h₁) - e^(-(1+ω)h₂))/(1+ω)
    - e^(-(1+ω+δ)t) (S_ω(t-h₁) - S_ω(t-h₂)) ,
```

where `S_ω(s) = ∑_{m ≤ e^s} m^ω` is the step profile.  The two sides of `(6)` are visible term by
term: the first summand is the primitive of the continuous term `q_δ`, and the second collects
exactly the atoms `e^(-δh) m^(-1-δ)` swept by the moving clock, since the transported atom weight at
`h = t - log m` is `e^(-(1+ω+δ)t) m^ω`.  The proof is a three-case split (both branches outgoing,
the moving boundary crossed, both branches incoming) and the `m = 1` term is precisely the unit
boundary jump `(4)`.

The two classical readings are proved separately and are what identifies the right-hand side of
`(6)`: `hasDerivAt_dampedPacketKernel` gives the exact smooth relation on every interval
`(log m, log (m+1))`, and `tendsto_dampedPacketKernel_nhdsLT` gives the left limit at `log m`,
exhibiting the jump `m^(-1-δ)` of `(8)`.

### The signed Möbius synthesis

`formal/GaloisForLFunctions/RHTower/ShiftedEulerMobiusSynthesis.lean`

| Card item | Lean name |
|---|---|
| `(10)` `c_ω(n) = ∑_{dm=n} μ(d) d^(-ω) m^ω` | `RHTower.shiftedEulerCoefficient` |
| `(10)` as a weighted Möbius divisor sum | `RHTower.shiftedEulerCoefficient_eq` |
| **`(10)`** Euler product form `n^ω ∏_{p ∣ n}(1 - p^(-2ω))` | `RHTower.shiftedEulerCoefficient_eq_prod` |
| **`(12)`** the exact atomic coefficient | `RHTower.sum_divisorsAntidiagonal_shifted` |
| **`(13)`** the synthesis of the atoms | `RHTower.mobiusSynthesis_atoms` |
| **`(11)`** the Euler main density `1/ζ(1+2ω)` | `RHTower.ofReal_tsum_moebius_rpow` |

`(12)` is the pointwise identity

```text
∑_{dm=n} μ(d) d^(-1-2ω-δ) m^(-1-δ) = c_ω(n) n^(-1-ω-δ) ,
```

and `(13)` is its summed form: for any bounded `f` (the atoms are tested against a bounded weight),
`0 < ω`, `0 < δ`,

```text
∑_d μ(d) d^(-1-2ω) ( ∑_m d^(-δ) m^(-1-δ) f(log d + log m) )
  = ∑_n c_ω(n) n^(-1-ω-δ) f(log n) ,
```

proved by absolute convergence of the double family and the divisor-antidiagonal regrouping
`(d, m) ↦ n = dm`.  The atom of `(6)` at clock `h = log d` sits at `t = log d + log m = log n` with
weight `d^(-δ) m^(-1-δ)`, so this **is** the synthesis of the packet connections.

`(11)` is proved for every real `s > 1` in the form
`(∑' n, μ(n) n^(-s) : ℝ) = (ζ(s))⁻¹`, by casting the corpus Möbius normalization
`RHTower.LSeries_moebius_eq_inv_riemannZeta`; at `s = 1 + 2ω` it is the exact coefficient of the
continuous term of `(13)`.

The Euler product form of `(10)` is proved through the multiplicativity of `d ↦ μ(d) d^(-2ω)`: its
divisor sum is multiplicative, and on a prime power `p^k` (`k ≥ 1`) it collapses to `1 - p^(-2ω)`
because `μ(p^j) = 0` for `j ≥ 2`.

### Remaining

Nothing in the formalisation of this card's own theorems.  The Gamma completion weld `(14)`–`(17)`
is **not** a `[PROVED HERE]` item: it consumes Suzuki's kernel zero moment `(15)`,
`∫_0^1 g_ω^{(1)}(x) x^ω dx = 0`, which is a cited parent result
(`not_new_scientific_knowledge/suzuki-euler-pole-archimedean-moment-annihilation.md`) and is not
formalised anywhere in the corpus; gates 7 and 8 rest on it.  The four unchecked gates
(`insert the connection weld into the Gamma/Sonin relative square`, `trace neutrality or Lüders
orthogonality`, `continue the framed source to ell_E`, specialist audit, RH) are open **research**,
not open formalisation.
