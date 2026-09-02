# FZZ external-BRST branch-charge classification

- **ID:** FZZ-EBRST-BC
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Halder--Jafferis, arXiv:2402.00932v3, (3.16)--(3.19), (3.29), (3.33); arXiv:2310.02313, (4.26)--(4.27)
- **Statement:** First marked cigar OPE monodromy against a quantized external vertex is `+p` on `W+` and `-p` on `W-`; it is independent of radial label `j`, level `k`, and winding `nu`.

## Goal

Kill the chain

`external-BRST branch incidence -> torus area Ward law -> divisor-mode passivity -> Mellin completeness -> RH`

when the first arrow uses only branch existence or logarithmic monodromy. Preserve the strongest radial datum exposed by the obstruction.

## Gates

- [x] 0 -> 1: source-pure claim and exact RH-chain role
- [x] 1 -> 2: dependency-closed paper proof `[PROVED HERE]`
- [x] 2 -> 3: Lean theorem, targeted build, axiom audit
- [ ] 3 -> 4: publication-ready

## Definitions

Put `q = 1 - 2/k`,

`m = (p-k nu)/2`, `mbar = -(p+k nu)/2`, with `p,nu` integral.

For radial label `j`, Wick contraction of the cigar operators gives marked logarithmic coefficients

`L+L = -j/q + m`, `L+R = -j/q + mbar`,

`L-L = -j/q - m`, `L-R = -j/q - mbar`.

The signed branch charge is `B = LL-LR`; the charge-even log-modulus coefficient is the mean of the two sums `LL+LR`.

## Proof `[PROVED HERE]`

Equation (3.29) changes compact winding by `1-delta` and radial weight by `1-delta/q`. Equations (3.16)--(3.19), with free-field OPE `X_L(z)X_L(0) ~ -(1/2) log z`, give the four coefficients above after differentiating at `delta=0`.

Quantization gives

`m-mbar = p`, `m+mbar = -k nu`.

Hence

`B+ = L+L-L+R = p`, `B- = L-L-L-R = -p`.

At `delta=0` the base monodromy is integral, so analytic continuation of the marked logarithm changes it by `2 pi i B`. Thus branch incidence is exactly `p != 0`, independent of `j,k,nu`. Any predicate of this channel is constant as `j` varies, so it cannot select zero radial momentum or any radial Abel wall.

The symmetric coefficients are

`S+ = L+L+L+R = -2j/q-k nu`,

`S- = L-L+L-R = -2j/q+k nu`.

Therefore their charge-even mean is

`(S+ + S-)/2 = -2j/q`,

and, for `q != 0`, it reconstructs `j = -(q/2)((S+ + S-)/2)`. This is the strongest positive survivor.

## Hostile audit

- Sign convention: fixed directly by (3.16)--(3.19) and the `mp i` signs in (3.29).
- Base branch: `p` integral makes the undeformed OPE single-valued; only differentiated logarithm contributes additive monodromy.
- Neutral-pair objection: distinct `W+` and `W-` blocks need not cancel pointwise; theorem does not claim they do.
- BRST mass-shell objection: extra on-shell correlations are additional data. The killed route is branch incidence/monodromy alone.
- Scope: full branch kernel, charge-even modulus, support motion, and higher replica order survive.

## No-go closure

- **Exact killing theorem/mechanism:** logarithmic monodromy is the quantized momentum charge `+-p`, hence radial-label blind.
- **Strongest positive survivor:** charge-even log-modulus mean reconstructs radial label exactly.
- **New insight:** external-BRST route must use modulus/on-shell coupling or support dynamics; branch existence and discontinuity cannot supply FZZ-P radial passivity.
- **Status:** internal corpus and primary-source audit complete; no prior classification found through 2026-08-31; formalized in `FZZCigarParityExternalBRSTBranchChargeNoGo`; targeted build passes; key theorems use only `propext`, `Classical.choice`, `Quot.sound`.
