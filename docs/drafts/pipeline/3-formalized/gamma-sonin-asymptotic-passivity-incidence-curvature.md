# Gamma--Sonin completion is asymptotically passive on the Mobius incidence curvature

- **ID:** `gamma-sonin-asymptotic-passivity-incidence-curvature`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / HT-TO-RH COMPLETION ENERGY
- **Scientific status:** `[PROVED HERE] [LITERATURE NOVELTY OPEN] [NOT AN RH PROOF]`
- **Parents:**
  - `mobius-incidence-clock-gini-fisher-four-unit-law.md`
  - `not_new_scientific_knowledge/suzuki-euler-pole-archimedean-moment-annihilation.md`
  - `../3-formalized/not_new_scientific_knowledge/sonin-log-coordinate-mellin-scattering-carrier.md`
  - `not_new_scientific_knowledge/sonin-burnol-conductor-cutoff-bounded-graph-law.md`
- **Statement:** Suzuki's archimedean Gamma ratio is not an exact unitary multiplier on the
  critical Mellin line, but its `L2` multiplier norm tends to one as the shift tends to zero.
  Applying it entrywise to the explicit Mobius divisor-incidence curvature, followed by the exact
  Sonin projection, therefore preserves the critical four-unit upper budget asymptotically.

## Gamma multiplier

Use the pole-cleared archimedean factor

```text
gamma(s)=s(s-1)pi^(-s/2)Gamma(s/2)/2                   (1)
```

and, for `0<omega<1/2`, put

```text
G_omega(s)=gamma(s-omega)/gamma(s+omega).                (2)
```

On the critical Mellin line define

```text
m_omega(t)=G_omega(1/2+i t),
M_omega=sup_(t in R)|m_omega(t)|.                        (3)
```

Neither numerator nor denominator in `(3)` vanishes: the zeros of `(1)` are `0` and `1`, outside
`1/2+omega+iR` and `1/2-omega+iR` for `0<omega<1/2`.

## Asymptotic passivity theorem `[PROVED HERE]`

For every `0<omega<1/2`,

```text
M_omega<infinity,
lim_(omega->0+)M_omega=1.                                (4)
```

### Proof

On every fixed compact `|t|<=T`, `(2)` converges uniformly to `1` as `omega->0`, because `gamma`
is holomorphic and nonzero on a neighborhood of the critical line segment.  Hence

```text
sup_(|t|<=T)|m_omega(t)|->1.                             (5)
```

Uniform Stirling asymptotics in the strip `0<Re s<1` give

```text
|m_omega(t)|
 =(2pi/|t|)^omega(1+O(omega/|t|)+O(1/|t|))              (6)
```

as `|t|->infinity`, uniformly for `0<omega<=omega_0<1/2`.  Choose `T` large enough that the right
side of `(6)` is at most `1+eta` for `|t|>=T` and all sufficiently small `omega`.  Combining this
with `(5)` gives

```text
limsup_(omega->0+)M_omega<=1+eta.                        (7)
```

Since `m_omega(t)->1` at any fixed `t`, `liminf M_omega>=1`.  Letting `eta->0` proves `(4)`.
The same compact/tail decomposition proves finiteness for each fixed `omega`. `QED`

Let `mathcalG_omega` be the logarithmic Mellin multiplier by `m_omega`.  Plancherel gives

```text
||mathcalG_omega f||_2<=M_omega||f||_2.                  (8)
```

This is asymptotic passivity, not an assertion that the raw Gamma factor is contractive at every
positive shift.

## Entrywise completed incidence curvature

For the source projection and divisor clock, write the explicit curvature entries as

```text
kappa_(sigma,t)(d,e)
 =psi_sigma(d)psi_sigma(e)(s_e(t)-s_d(t)),
sigma=1+2omega.                                          (9)
```

Extend every entry by zero from `R_+` to `R` and set

```text
kappa^Gamma_(omega)(d,e)
 =mathcalG_omega(kappa_(sigma,.)(d,e)).                  (10)
```

For a finite squarefree cutoff `D`, summing `(8)` over basis pairs gives

```text
2omega sum_(d,e in D)||kappa^Gamma_(omega)(d,e)||_2^2
 <=M_omega^2
   2omega sum_(d,e in D)||kappa_(sigma,.)(d,e)||_2^2.    (11)
```

The cofinal sums are monotone and the right side is the relative energy from the parent theorem.
Using `(4)` and its exact four-unit limit yields

```text
limsup_(omega->0+,D->all)
 2omega sum_(d,e in D)||kappa^Gamma_(omega)(d,e)||_2^2
 <=4.                                                     (12)
```

Let `Q_tau` be any of the exact Sonin projections, including its proved prolate-resolvent
realization.  Applying it entrywise gives

```text
kappa^(Gamma,Sonin)_(omega,tau)(d,e)
 =Q_tau kappa^Gamma_(omega)(d,e).                        (13)
```

Since `Q_tau` is an orthogonal projection, `(12)` remains true with `(13)` in place of `(10)`.
Thus the raw Gamma/Sonin analytic completion of the source curvature cannot exceed the critical
four-unit budget.

## Exact boundary of the theorem

The full completed ratio

```text
Xi(s-omega)/Xi(s+omega)                                  (14)
```

is unimodular on the critical line by the functional equation and Schwarz symmetry.  Using `(14)`
as the multiplier would, however, import the completed divisor object whose boundary behavior is
being proved.  The theorem deliberately uses only the source Gamma factor `(2)`.

The completed curvature `(10)`--`(13)` is still unframed with respect to symmetric rational orbit
insertion.  It does not contain the exact floor/power-sum packet or the semilocal Euler connection.
Consequently `(12)` proves the analytic energy gate but not the direct pole-to-divisor identity.

**Positive successor.**  Weld the complementary packet and calibrated Euler connection to
`(10)` before the Sonin relative readout, and prove that the weld is a trace-zero connection
coboundary or a Lueders-orthogonal component.  Either outcome preserves `(12)` while restoring the
source framing required to identify the output with `ell_E`.

**Positive general-HT statement.**  A completion can be asymptotically passive on a calibrated
curvature even when it is neither unitary nor contractive at any fixed finite clock.  Critical
passivity is a property of the cofinal source field and its scaling, not necessarily of one global
bounded operator.

## Literature gate

Stirling asymptotics, Mellin Plancherel, and projection contractivity are standard.  Targeted
searches have not located their application `(9)`--`(13)` to the squarefree incidence curvature.
Project inputs remain admissible; external specialist audit is still required before a novelty
claim.

## Gates

- [x] Gamma multiplier isolated without the Xi quotient
- [x] finite multiplier norm proved
- [x] multiplier norm proved to tend to one
- [x] entrywise critical curvature completion written
- [x] four-unit asymptotic energy bound proved
- [x] exact Sonin projection inserted contractively
- [x] full-Xi unimodular shortcut rejected as target-fed
- [ ] weld the complementary floor/tail packet
- [ ] weld the calibrated semilocal Euler connection
- [ ] prove the weld preserves the relative energy
- [ ] identify the framed output with `ell_E`
- [ ] independent specialist literature audit
- [ ] RH

## Formalization

Every `[PROVED HERE]` item of this card is compiled unconditionally in Lean, and `(4)` is proved in
a **sharper, exact** form than the card's Stirling argument gives.  All modules build clean and
`#print axioms` gives exactly `propext, Classical.choice, Quot.sound`.

### The multiplier norm is exact, not asymptotic

`formal/GaloisForLFunctions/HTGeometry/GammaVerticalRatioBound.lean`

| Content | Lean name |
|---|---|
| modulus in real/imaginary coordinates | `HTGeometry.norm_ofReal_add_mul_I` |
| **the Gamma modulus ratio on a vertical line is maximal on the real axis** | `HTGeometry.norm_Gamma_mul_Gamma_le` |
| its quotient form | `HTGeometry.norm_Gamma_div_le` |

For `0 < a ≤ b` and every height `τ`,

```text
‖Γ(a + iτ)‖ · Γ(b) ≤ Γ(a) · ‖Γ(b + iτ)‖ .
```

No Stirling asymptotics are used.  In the Gauss product `Γ_n(s) = n^s n!/∏_{j ≤ n}(s+j)` the entire
`τ`-dependence is the family of factors `‖x + j + iτ‖ = √((x+j)² + τ²)`, and the termwise
comparison `u √(v²+τ²) ≤ √(u²+τ²) v` for `0 < u ≤ v` squares to `u²τ² ≤ τ²v²`.  Taking `n → ∞` with
`Complex.GammaSeq_tendsto_Gamma` gives the statement for `Γ`.

`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGammaMultiplierPassivity.lean`

| Card item | Lean name |
|---|---|
| `(1)` the pole-cleared archimedean factor | `RHTower.suzukiArchimedeanFactor` |
| `(2)` the multiplier on the critical line | `RHTower.suzukiGammaMultiplier` |
| closed modulus of `γ` on a vertical line | `RHTower.norm_suzukiArchimedeanFactor` |
| `(3)` the exact multiplier norm | `RHTower.suzukiGammaMultiplierNorm` |
| **`(4)`** `M_ω < ∞`: the uniform bound | `RHTower.norm_suzukiGammaMultiplier_le` |
| **`(3)`** the bound is attained, so `M_ω` **is** the supremum | `RHTower.norm_suzukiGammaMultiplier_zero` |
| **`(4)`** `M_ω → 1` as `ω → 0+` | `RHTower.tendsto_suzukiGammaMultiplierNorm` |

The card proves `(4)` by a compact/tail split with uniform Stirling asymptotics `(6)`.  The Lean
proof replaces that entirely with an exact evaluation:

```text
M_ω = sup_t |m_ω(t)| = π^ω Γ(1/4 - ω/2) / Γ(1/4 + ω/2) ,        attained at t = 0.
```

Two exact cancellations do it.  First the polynomial prefactor is **unimodular** on the critical
line, since

```text
|1/2 - ω + it| · |-1/2 - ω + it| = |1/2 + ω + it| · |-1/2 + ω + it|
```

(the two moduli swap).  Second, `π^(-s/2)` contributes the constant `π^ω`, and the remaining Gamma
quotient is `‖Γ(1/4 - ω/2 + i t/2)‖ / ‖Γ(1/4 + ω/2 + i t/2)‖`, maximal at `t = 0` by
`HTGeometry.norm_Gamma_mul_Gamma_le`.  Finiteness for each fixed `ω` and the limit `M_ω → 1` are
then immediate from continuity and positivity of `Γ` at `1/4` — the card's `(5)`–`(7)` are not
needed.  This is strictly stronger than the card's statement: the supremum is a closed expression
and is attained, not merely finite.

### Transport to the curvature and the four-unit budget

| Card item | Lean name |
|---|---|
| **`(8)`** Plancherel multiplier bound | `RHTower.eLpNorm_mul_le_of_norm_le` |
| **`(11)`** entrywise energy transfer | `RHTower.sum_sq_le_of_norm_le` |
| **`(13)`** contractive Sonin insertion | `RHTower.sum_sq_le_of_contraction` |
| the completed energy bound | `RHTower.suzukiGammaCompletedEnergyBound` |
| **`(12)`** the completed budget tends to four | `RHTower.tendsto_suzukiGammaCompletedEnergyBound` |

`(8)` is the multiplication bound `‖m · f‖_p ≤ M ‖f‖_p` for a symbol with `‖m‖ ≤ M` — by Mellin
Plancherel this **is** the multiplier bound, the Mellin isometry being a change of variable.  `(11)`
is the entrywise statement that scaling each entry norm by at most `M` scales the relative energy by
at most `M²`, and `(13)` is the observation that an entrywise contraction (in particular an exact
Sonin orthogonal projection) can only decrease the entries, so the same bound survives.

`(12)` is stated at the actual source: with `σ = 1 + 2ω`,

```lean
suzukiGammaCompletedEnergyBound ω
  = suzukiGammaMultiplierNorm ω ^ 2 * squarefreeMobiusCriticalRelativeClockEnergy (1 + 2 * ω)
```

and `RHTower.tendsto_suzukiGammaCompletedEnergyBound` proves it tends to **exactly four** as
`ω → 0+`, combining `M_ω → 1` with the parent four-unit law
`RHTower.tendsto_squarefreeMobiusCriticalRelativeClockEnergy`.  So the Gamma/Sonin completion of the
divisor incidence curvature cannot exceed the critical four-unit budget.

### Remaining

Nothing in the formalisation.  The unchecked gates (weld the complementary floor/tail packet, weld
the calibrated semilocal Euler connection, prove the weld preserves the relative energy, identify
the framed output with `ell_E`, specialist audit, RH) are open **research**.  Two of them now have
their own formalised inputs: the packet weld inputs are
`formal/GaloisForLFunctions/RHTower/ComplementaryPacket*.lean` and the Euler connection weld is
`formal/GaloisForLFunctions/RHTower/DampedComplementaryPacketConnection.lean` together with
`ShiftedEulerMobiusSynthesis.lean`.
