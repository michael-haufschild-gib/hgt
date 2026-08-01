# Sonin--Burnol frequency logarithmic-order no-go

- **ID:** `sonin-burnol-frequency-logarithmic-order-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean) / TERMINAL ROUTE-F NO-GO WITH POSITIVE SURVIVOR
- **Parent:** `sonin-principal-shell-cyclic-trace.md`
- **Statement:** Uniformly over every finite tower height, the frequency-reflected Burnol log-shell
  channel has only logarithmic-order diagonal response on the canonical modulated Sonin packets;
  the already-proved linear coupling-energy schedule therefore makes its completed packet channel
  unbounded below.

## Goal

Close Route F's last concrete semilocal survivor without replacing it by an arbitrary scalar.
Position-side channel is already uniformly bounded on fixed-annulus packets. Missing theorem is
frequency-side channel itself, with tower height allowed to depend arbitrarily on coupling scale.

Successful proof terminally retires literal Burnol-conductor completion in typed and operator
forms. It does not prove RH. It proves current Route F source class cannot reach its RH consumer.

## Theorem

Fix a geometric tower `R_k=a₀ r₀^k`, `a₀>0`, `r₀>1`, a strict annulus `0<b<c`, and canonical
packets `w_A=soninPacketEven(b,c,2πA)`. Let

```text
F_n = Fourier * evenLogShellChannel(a₀,r₀,n) * Fourier.
```

There are constants `C₀,C₁>=0`, independent of `A` and `n`, such that for every `A>=1`,

```text
Re <w_A, F_n w_A> <= C₀ + C₁ log A.                    (1)
```

Consequently, for every height schedule `n(A)`, this diagonal contribution is sublinear in `A`.
Along the existing schedule whose successive-layer Hilbert--Schmidt energy has a positive linear
lower bound, `soninCompletedPacketValueVar` has no lower floor.

The same conclusion holds for the full finite Burnol conductor because its position half is
uniformly bounded on the fixed physical annulus. `[PROVED HERE]`

## Complete paper proof

Put `phi=soninAnnulusBump(b,c)` and `D(eta)=|Fourier(phi)(eta)|^2`. Exact modulation gives

```text
Fourier(w_A)(xi)
 = (1/2) Fourier(phi)(xi-A)
 + (1/2) Fourier(phi)(xi+A)
 - mu_A Fourier(phi)(xi),                               (2)
```

where `|mu_A|<=1`. Hence

```text
|Fourier(w_A)(xi)|^2
 <= 3 ((1/4)D(xi-A)+(1/4)D(xi+A)+D(xi)).                (3)
```

Smooth compact support makes `phi` Schwartz. Choose a global sixth-order bound

```text
D(eta) <= C^2 |eta|^(-12)                               (4)
```

for `eta!=0`. If `A>=2`, `t>=2A`, and `|xi|>=t`, then
`|xi-A|,|xi+A|>=|xi|/2` and `|xi|>0`. Equations `(3)`--`(4)` give one constant `K`, independent
of `A,t`, with

```text
|Fourier(w_A)(xi)|^2 <= K |xi|^(-12).                   (5)
```

Integrating the two power tails gives

```text
||1_(|xi|>=t) Fourier(w_A)||_2^2 <= K' t^(-11).          (6)
```

Write `P_k` for the orthogonal projection onto the symmetric frequency shell
`R_k<=|xi|<R_(k+1)`. Fourier involutivity, self-adjointness, and orthogonality give the exact
quadratic-form expansion

```text
Re <w_A,F_n w_A> = sum_(k<n) log(R_k) ||P_k Fourier(w_A)||^2.  (7)
```

Split the sum into three sets.

1. If `R_k<1`, its coefficient is negative and its mass nonnegative, so discard it in an upper
   bound.
2. If `1<=R_k<=2A`, then `log R_k<=log(2A)`. Orthogonality and contractivity of the total shell
   projection give total mass at most `||w_A||^2`. The packet norms are uniformly bounded by an
   annulus constant `B`, so this part is at most `B log(2A)`.
3. If `R_k>2A`, the shell mass is at most the outer mass in `(6)` at `t=R_k`. Since
   `log R_k<=R_k` for `R_k>=1`, this contribution is at most `K' R_k^(-10)`. The whole geometric
   series is finite:

   ```text
   sum_(k>=0) R_k^(-10)
     = a₀^(-10) sum_(k>=0) r₀^(-10k)
     = a₀^(-10)/(1-r₀^(-10)).                           (8)
   ```

This bound is independent of terminal height `n`. Since `log(2A)=log A+log 2`, `(7)`--`(8)` prove
`(1)`.

For the position half of the Burnol conductor, every `w_A` is supported in the same annulus and
`exists_bound_norm_evenLogShellChannel_of_annulus` supplies a height-independent operator bound;
Cauchy--Schwarz turns it into a constant quadratic-form bound. Adding this constant to `(1)` keeps
the full conductor response logarithmic.

Finally use the already-proved one-product Sonin schedule. Its coupling energy is bounded below by
`s r-C` for one `s>0`, whereas `C₀+C₁ log r=o(r)`. Therefore the completed contribution falls
short by a fixed positive amount eventually. `not_bddBelow_soninCompletedPacketValueVar_of_shortfall`
then gives an explicit sequence of finite packets below every proposed floor. No zero data, RH
premise, numerical estimate, target-fitted scalar, or selected tower height enters.

## Hostile audit

- Ordinary operator norm cannot prove `(1)`: it grows with tower height. Bound must use packet
  spectral mass before taking norm.
- Mere blow-up of `||F_n w_A||` is irrelevant: logarithmic blow-up is still sublinear versus Route
  F's linear Hilbert--Schmidt mode count.
- Height schedule cannot be restricted. Proof must be uniform in every `n`.
- Packet must be exact source packet already used by completion theorem; no target-selected vector.
- Defining completion to equal coupling energy is circular source matching and forbidden.
- Result is new only if it closes frequency-reflected channel uniformly in height. Instantiating
  generic sublinear no-go with an assumed cap is theorem theatre.

## External novelty audit

Primary-source audit found no collision with the uniform order theorem or its terminal source
handoff. Burnol's co-Poisson and Sonine-space work proves qualitative transform, completeness, and
minimality structure, not a canonical-packet conductor bound uniform in truncation height
([co-Poisson intertwining](https://arxiv.org/abs/math/0407443),
[complete/minimal zeta systems](https://arxiv.org/abs/math/0203120)). Connes--Consani--Moscovici
construct semilocal Sonin isomorphisms and prolate operators but do not prove a lower-floor producer
or an order-one packet response
([Zeta zeros and prolate wave operators](https://alainconnes.org/wp-content/uploads/Zeta-zeros-and-prolateproofs-final-2024.pdf)).
Archimedean Weil positivity and quasi-inner local-factor results supply operator structure, not the
missing cofinal semilocal floor
([Weil positivity](https://arxiv.org/abs/2006.13771),
[quasi-inner local factors](https://arxiv.org/abs/2008.10974)). The 2025 spectral-triple proposal
reports numerical spectral agreement and states rigorous convergence remains sufficient for RH;
it does not close this source estimate
([Zeta Spectral Triples](https://arxiv.org/abs/2511.22755)).

## No-go closure

- **Exact killing theorem/mechanism:** uniform logarithmic packet-diagonal bound `(1)` plus existing
  linear coupling-energy schedule and completion shortfall theorem.
- **Strongest positive survivor:** any universal Route F floor-restorer must have packet-diagonal
  response of at least positive linear order along a source schedule. Thus a future source operator
  must have microlocal order at least one; Tate/Burnol logarithmic conductors have order zero.
- **New insight:** Route F's missing object is not another finite part or better logarithmic
  regularization. It requires a new order-one arithmetic source operator, or a renormalization that
  removes the Sonin Weyl-volume term before the Gamma conductor is attached.
- **Status:** dependency-closed paper proof and exact unconditional Lean theorem complete. The final
  theorem quantifies over every tower-height schedule, uses the canonical source packets, pairs
  them with the full concrete Burnol conductor, and produces the source schedule witnessing failure
  of the lower floor.

## Lean formalization

- `SoninPacketHighTailPolynomial.lean` proves the uniform twelfth-order pointwise density tail and
  integrated eleventh-order cutoff-energy tail for the canonical packet.
- `SoninChannelMovingThreshold.lean` proves the missing height-uniform shell estimate with a real
  moving threshold, avoiding any carrier-to-shell rounding assumption.
- `SoninBurnolFrequencyLogOrder.lean` proves the full conductor quadratic form is bounded by
  `C₀ + C₁ log A`, uniformly in carrier and height.
- `SoninBurnolFrequencyLogarithmicOrderNoGo.lean` composes that exact bound with the explicit
  linear-energy Sonin schedule and proves
  `not_bddBelow_soninCompletedPacketValueVar_soninBurnolLogShellConductorFamily`.
- Axiom audit for all four load-bearing theorems: `propext`, `Classical.choice`, `Quot.sound` only.
- No `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declaration occurs in these modules.

## Gates

- [x] 0 -> 1 in-progress: source-pure statement, exact falsifier, anti-theatre boundary
- [x] 1 -> 2 fully-proven: dependency-closed proof of uniform logarithmic diagonal bound
- [x] 2 -> 3 formalized: unconditional Lean theorem, umbrella wiring, source-level lint and axiom audit
- [ ] 3 -> 4 publication-ready

## Log

- 2026-08-01 — Route F audit reduced last concrete survivor to uniform frequency-channel order.
- 2026-08-01 — paper proof closed by positive/middle/tail shell split and a uniform Schwartz tail;
  tower height disappears before the growth comparison.
- 2026-08-01 — exact canonical-packet tail, moving-threshold shell bound, full-conductor logarithmic
  order, and arbitrary-height source no-go formalized in Lean.
