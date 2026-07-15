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
