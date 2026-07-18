# Xi source-completion polarization architecture

- **ID:** `xi-source-completion-polarization-architecture`
- **Stage:** 1-in-progress
- **Type:** RH ARCHITECTURE CONJECTURE
- **Scientific status:** `[CONJECTURE] [OPEN CORE]`
- **Source:** whole `HTGeometry` theorem graph; `MinimalHTCompletionArchitecture`;
  `self-dual-decorated-clock-boundary`; Xi shift-source and slab detector theorems
- **Statement:** An RH proof compatible with the live HT geometry must realize the completed Xi
  source as a source-calibrated, two-channel, noncompact all-scale completion whose reflected
  Hilbert defect is exactly the localized Xi height-fibre variance, and must prove saturation of
  that polarization from source data.

## What the whole HTGeometry corpus forces

The recurring formal mechanisms are not interchangeable:

1. **Private source / infinite capacity.** Prime pivots, valuation layers, Gamma clocks, and
   elliptic-gamma faces create unbounded differential rank from a thin source boundary.
2. **Observation / quotient.** Finite reporters reconstruct only modulo their common invisible
   gauge. Jointly conservative reporters require labelled pairing data, not separate marginal
   spectra.
3. **Completion / transgression.** Finite fusion forces an infinite strict tower, while the Euler
   logarithm and the Xi filtered source lie outside the differential closure of all individual
   valuation layers.
4. **Calibration.** Differential fields, Kähler clocks, projective Wigner--Smith data, and carrier
   isomorphism forget affine origin, scalar normalization, or the divisor section.
5. **Topology.** Finite clocks, compact completions, finitely many rates, and diagonal/cofinal
   samples all miss genuine source directions. The source must select a rigging or full-product
   bornology.
6. **Reflection and orientation.** Reflection pairs off-fixed degeneracies but does not exclude
   them. Hypertranscendence is compatible with strict Hankel positivity, and field completion is
   blind to Krein orientation.
7. **Polarization saturation.** Balanced Hilbert polarization turns equality of reflected
   channels into zero defect. The Xi detector-order classification forces height localization;
   the reflected first moment is killed, so the centered second moment/variance is the minimal
   surviving scalar detector.

Thus the missing theorem is not another nonnegativity statement. It is a source-produced equality
case.

## Exact conjectural factorization

Let

```text
K_layer = C(s)<P(rs) : r >= 1>_d
```

and let `D_2` be the filtered von Mangoldt carrier exposed by the corrected `+2` Xi shift. The
paper-proved all-layer barrier says `D_2` is hypertranscendental over `K_layer`.

The upper-end coordinate theorem gives the exact calibration/source split

```text
logDeriv(xi)(s+2) - logDeriv(xi)(s) = R_2(s) + D_2(s),
R_2(s) = 1/(s+2) + 1/(s+1) - 1/(s-1),
R_2 in C(s) <= K_layer,
D_2 hypertranscendental over K_layer.
```

Consequently the uncorrected Xi shift is itself hypertranscendental over `K_layer`. The rational
term is pure coordinate calibration; the filtered carrier is the private source. A valid Hilbert
construction must preserve this distinction: `R_2` may fix the affine normalization of the two
channels, but it cannot supply, cancel, or finitely reconstruct the `D_2` direction.

There is also a paper-closed source-to-divisor transport. Define

```text
B_2(s)=xi(s)/xi(s+2).
```

Then `B_2'/B_2` is the negative uncorrected Xi shift, so HTGeometry's exact logarithmic-source
boundary makes `B_2` hypertranscendental over `K_layer`. On the critical strip the denominator is
zero-free, hence `B_2` carries exactly the Xi zero divisor. Directly squaring `D_2` would square
poles at Xi zeros, whereas `B_2` carries zeros.

However, the whole RHTower audit identifies `B_2` after recentering with Suzuki's shifted-Xi
quotient at `omega=1`. Its Hardy leakage is already zero unconditionally because poles at shift
`omega` detect only zeros with `Re(rho)>1/2+omega`. Thus `B_2` is a valid multiplicative source
primitive but **not** the missing RH Hilbert carrier. The fixed-ratio route is retired in
`../5-failed/xi-shift-ratio-fixed-aperture-rh-no-go.md`.

**[CONJECTURE — SOURCE-COMPLETION POLARIZATION]** There is a construction made only from the
prime-power source of `D_2`, the archimedean Gamma factor, analytic continuation, and the
functional-equation involution which, for every real height `gamma`, produces two vectors
`U_plus(gamma)` and `U_minus(gamma)` in one source-selected rigged Hilbert completion and a
positive scalar `c(gamma)` such that

```text
norm(U_plus(gamma) - U_minus(gamma))^2
  = c(gamma) * V_Xi(gamma),
```

where `V_Xi(gamma)` is the multiplicity-weighted centered second moment of the Xi zeros at that
height. The construction must not use `xi`, a zero set, a zero-indexed basis, or a chosen divisor
section in defining the vectors. Its source relations must further imply

```text
U_plus(gamma) = U_minus(gamma)
```

for every `gamma`.

The existing detector theorem then gives `V_Xi(gamma)=0` for every height, hence RH.

## Open core

**[OPEN CORE]** Construct the source-pure realization of the complete transverse family

```text
Theta_omega(z)=xi(1/2-omega-i*z)/xi(1/2+omega-i*z),
L_omega=P_- M_(Theta_omega)|H^2_+,
```

inside one source-selected true-aperture Hilbert completion, and prove from the completed Euler
source that `L_omega=0` for every `omega>0`. The existing Hardy theorem then gives RH, while the
leakage entry aperture of a zero `rho=1/2+a+i*gamma` records the exact displacement `a`.

The immediate positive theorem suggested by HTGeometry is now formalized in its strongest closed
form: distinct positive integral shift-defect sources have full finite differential rank even over
the field generated by the true rational coordinate and every scalar prime-valuation layer. Hence
no finite set of safe shifts or valuation reporters can generate the remaining transverse flow.
The exact theorem is recorded in
`../3-formalized/new_scientific_knowledge/xi-transverse-shift-defect-differential-rank.md`. It is
not the RH bound, but it determines the minimum source capacity of any valid Hilbert realization.
Its concrete cofinite-prime Gram theorem supplies positive finite sections of the required source
metric at every aperture-jet depth; the missing step is to identify their source-selected infinite
completion with the full Hardy leakage family rather than a fixed prolate or fixed-moment metric.

## Falsity and circularity guards

- A determinant chosen to be `xi`, any zero-indexed operator, or any definition using
  `V_Xi(gamma)` is circular.
- Reflection alone permits paired off-line zeros.
- Positivity alone is insufficient: digamma already supplies an HT function with strict positive
  Hankel towers.
- Any finite reporter network, compact reporter, finite list of rates, single scalar filtration,
  or diagonal cofinal sample is excluded by formal HTGeometry no-gos.
- Separate prime and archimedean spectra are insufficient; the two channels and their labels must
  be preserved by one comparison map.
- A proof that stays inside differential algebra over `K_layer` cannot reach `D_2`; the
  all-valuation barrier makes the necessary analytic-completion crossing exact.
- Fixed-aperture innerness is excluded as an RH mechanism: `Theta_1`, equivalently `B_2`, is inner
  unconditionally and still contains every off-line Xi zero as a numerator zero.

## Gates

- [x] whole live HTGeometry mechanism inventory audited through its umbrella, generated API,
  424 dependency roots, source cards, failed routes, and current model logs
- [x] finite/compact/scalar/positivity-only representations excluded
- [x] concrete Xi source upgraded to the all-valuation completion boundary on paper
- [x] logarithmic source multiplicatively integrated to the zero-carrying all-layer-impermeable
      Xi ratio `B_2` on paper
- [x] fixed-ratio RH route retired by the exact Suzuki `omega=1` identification
- [x] prove finite transverse shift-defect differential rank over the complete scalar valuation
      field in `RHTower.XiTransverseShiftAllValuationLayerRank`
- [x] build deletion-robust positive Hilbert Gram sections for every finite transverse shift-jet
      packet in `RHTower.XiTransversePrimeSourceHilbertMetric`
- [ ] construct the source-pure all-`omega` two-channel comparison map
- [ ] prove the defect identity without divisor data
- [ ] prove source-forced saturation
- [ ] external specialist novelty and equivalence audit

## Log

- 2026-07-18 — replaced the narrow “HT result as RH analogy” reading by a whole-theory necessity
  statement. The first exact mathematical output is the all-valuation Xi-source barrier; the RH
  residue is localized to source-produced polarization saturation.
- 2026-07-18 — retired `B_2` as the RH carrier after identifying it with the unconditionally safe
  Suzuki aperture `omega=1`; pivoted the open core to the full transverse leakage filtration.
- 2026-07-18 — formalized full finite differential rank of distinct positive integral transverse
  shift sources. The remaining RH core is therefore genuinely infinite-aperture and Hilbertian,
  not a finite differential reconstruction problem.
- 2026-07-18 — upgraded that rank theorem across the full scalar valuation-layer completion. The
  whole finite source packet survives simultaneously, so adding every scalar prime-zeta dilation
  does not reduce the infinite-aperture requirement.
- 2026-07-18 — realized the transverse source rank as positive-definite cofinite-prime Hilbert Gram
  sections. This builds the finite metric skeleton; the RH-bearing open core remains its canonical
  infinite source-to-Hardy completion and saturation.
