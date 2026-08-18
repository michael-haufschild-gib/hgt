# Suzuki's archimedean primitive has a forced sign change below the half shift

- **ID:** `suzuki-archimedean-primitive-forced-sign-change`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (paper), `[PROVED HERE; SEARCH/BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** Suzuki's explicit shifted-Xi Mellin kernel;
  `../../3-formalized/not_new_scientific_knowledge/shifted-euler-prime-orbit-pf2-failure.md`
- **Statement:** In the RH-relevant range `0<omega<1/2`, the integrated archimedean kernel entering
  Suzuki's one-sign criterion is negative near zero and positive near one.  Thus neither the
  archimedean factor alone nor positivity of the Euler dilation coefficients can give the required
  eventual sign by a pointwise sign-preservation argument.

## Setup

Let `g_omega` be Suzuki's compactly supported archimedean kernel on `(0,1)`, and define

```text
g_omega^(1)(x)
 =integral_x^1 sqrt(y/x) g_omega(y) dy/y,
                                                        0<x<1.               (1)
```

Suzuki's explicit kernel has the endpoint asymptotics

```text
g_omega(y)
 =A_omega(1-y)^(omega-1)+o((1-y)^(omega-1))             as y->1-,

A_omega=(2pi)^omega/Gamma(omega)>0,                     (2)
```

and, for `0<omega<3/2`,

```text
g_omega(y)
 =-B_omega y^(omega-1)+o(y^(omega-1))                   as y->0+,

B_omega=4omega pi^(omega-1/2)Gamma(3/2-omega)>0.        (3)
```

## Theorem: opposite endpoint signs

For `0<omega<1/2`,

```text
g_omega^(1)(x)
 ~-B_omega/(1/2-omega) x^(omega-1)                      as x->0+,             (4)

g_omega^(1)(x)
 ~ A_omega/omega (1-x)^omega                            as x->1-.             (5)
```

Consequently `g_omega^(1)` is negative on some interval `(0,epsilon_omega)` and positive on some
interval `(1-delta_omega,1)`.  In particular it changes sign on `(0,1)`.

### Proof near zero

Rewrite `(1)` as

```text
g_omega^(1)(x)
 =x^(-1/2) integral_x^1 y^(-1/2)g_omega(y)dy.           (6)
```

By `(3)`, the singular part of the integrand is

```text
-B_omega y^(omega-3/2).
```

Since `omega-1/2<0`,

```text
integral_x^delta y^(omega-3/2)dy
 ~x^(omega-1/2)/(1/2-omega).                            (7)
```

Multiplication by `-B_omega x^(-1/2)` gives `(4)`.  The integral over `[delta,1]` is
`O(x^(-1/2))`, which is lower order than `x^(omega-1)` because `omega<1/2`.  The `o` term in `(3)`
is handled by the same split with an arbitrary relative-error bound.

### Proof near one

On `[x,1]`, both `x^(-1/2)` and `y^(-1/2)` tend uniformly to one.  Insert `(2)` into `(6):

```text
integral_x^1 A_omega(1-y)^(omega-1)dy
 =A_omega/omega (1-x)^omega.
```

The integrated `o` term is lower order, proving `(5)`.

Continuity on `(0,1)` then gives the sign change.

## Route C consequence

Suzuki's causal source primitive is

```text
h_omega^(1)(x)
 =x^(-1) sum_(n<=x)c_omega(n)g_omega^(1)(n/x),
```

with positive `c_omega(n)`.  The summand kernel itself has both signs, and the coefficient sequence
fails PF2 on every prime orbit.  Therefore no pointwise-positive or variation-diminishing argument
forces `h_omega^(1)` to have the eventual single sign that would imply innerness.

The remaining possibility is a genuinely arithmetic cancellation theorem for the complete
prime-dilation mixture against the explicit archimedean sign change.  Such a theorem must use the
distribution of all prime powers quantitatively; neither factor separately has the required sign
rigidity.

## Scientific-novelty verdict

`[NOT NEW SCIENTIFIC KNOWLEDGE]` The endpoint expansions are direct integrations of Suzuki's
published kernel asymptotics.  The result is a route-local bridge and not new analysis.

## Lean formalization

Modules:

- `formal/GaloisForLFunctions/HTGeometry/EndpointIntegralAsymptotics.lean` — the two endpoint
  transfer laws for a primitive: `HTGeometry.tendsto_rpow_mul_intervalIntegral_nhdsGT_zero`
  (divergent endpoint, `α < -1`) and `HTGeometry.tendsto_rpow_mul_intervalIntegral_nhdsLT`
  (convergent endpoint, `β > -1`).
- `formal/GaloisForLFunctions/RHTower/SuzukiRealKernelForm.lean` — the real form of the literal
  kernel and its primitive (`RHTower.ofReal_suzukiRealSourceG`,
  `RHTower.ofReal_suzukiRealSourceGOne`), the complete beta value
  `RHTower.suzukiRealBetaTail_zero`, the endpoint rate of the incomplete-beta tail
  `RHTower.tendsto_suzukiRealBetaTail_nhdsLT_one`, and interval integrability of the weighted
  kernel `RHTower.intervalIntegrable_suzukiRealSourceGWeighted`.
- `formal/GaloisForLFunctions/RHTower/SuzukiArchimedeanPrimitiveSignChange.lean` — the endpoint
  expansions and the sign change.

| Card statement | Lean declaration |
|---|---|
| `(2)` `g_ω(y) ∼ A_ω (1-y)^{ω-1}`, `A_ω=(2π)^ω/Γ(ω)` | `RHTower.tendsto_suzukiRealSourceG_div_rpow_nhdsLT_one` |
| `(3)` `g_ω(y) ∼ -B_ω y^{ω-1}`, `B_ω=4ωπ^{ω-1/2}Γ(3/2-ω)` | `RHTower.tendsto_suzukiRealSourceG_div_rpow_nhdsGT_zero` |
| `(4)` `g_ω^{⟨1⟩}(x) ∼ -B_ω/(1/2-ω) x^{ω-1}` | `RHTower.tendsto_suzukiRealSourceGOne_div_rpow_nhdsGT_zero` |
| `(5)` `g_ω^{⟨1⟩}(x) ∼ A_ω/ω (1-x)^ω` | `RHTower.tendsto_suzukiRealSourceGOne_div_rpow_nhdsLT_one` |
| negative near `0`, positive near `1` | `RHTower.exists_suzukiRealSourceGOne_neg`, `RHTower.exists_suzukiRealSourceGOne_pos` |
| forced sign change on `(0,1)` | `RHTower.suzukiRealSourceGOne_sign_change`, `RHTower.suzukiSourceGOne_sign_change` |

The endpoint expansions `(2)` and `(3)` are quoted in the card from Suzuki's published kernel
asymptotics; in Lean they are *proved* from the literal kernel `suzukiSourceG` (Suzuki (2012),
equation (204)), so the sign change rests on no imported asymptotic.  The constant `B_ω` is obtained
from the Euler beta value `Γ(3/2-ω)Γ(ω)/Γ(3/2)` and `Γ(3/2) = √π/2`.

`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for every declaration above.

## Gates

- [x] 0 -> 1: archimedean one-sign proposal and endpoint falsifier isolated.
- [x] 1 -> 2: both asymptotics and forced sign change proved on paper.
- [x] 2 -> 3: formalized; see `## Lean formalization`.  The open theorem remains the all-prime
  cancellation law.
- [ ] 3 -> 4: no scientific-novelty claim.
