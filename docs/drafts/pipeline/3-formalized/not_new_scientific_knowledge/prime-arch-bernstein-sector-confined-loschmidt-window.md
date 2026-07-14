# Prime--archimedean sector-confined Loschmidt window

- **ID:** `prime-arch-bernstein-sector-confined-loschmidt-window`
- **Status:** 3 -- formalized
- **Classification:** `[NOVELTY UNVERIFIED]`

## Claim

Let
\[
 u_\rho=\lambda_\rho/R_*,\qquad
 B_{\rm sec}=\frac{501}{500},\qquad
 \Pi_M=\sum_{i=0}^M a_{M,i}^2.
\]
The endpoint quartet estimate gives, for every Xi-divisor copy,
\[
 (\Im u_\rho)^2\le\frac1{84}(\Re u_\rho)^2.
\]
Together with the strict quarter-disk bound for off-line atoms, this forces
\[
 |u_\rho|+|1-u_\rho|<B_{\rm sec}.
\]
Consequently the completed Bernstein source obeys
\[
 \Pi_M\le A_*^2 B_{\rm sec}^{2M}.
\]
If RH is false, its cancellation-resistant purity exponent therefore lies in the exact
window
\[
 1<r\le\left(\frac{501}{500}\right)^2
 =\frac{251001}{250000}<\frac{201}{200}.
\]

## Proof

Put `r=|u|`, `s=|1-u|`, and `x=Re u`.  The orientation inequality gives
\[
 r^2=x^2+(\Im u)^2\le\frac{85}{84}x^2,
\]
and the rational comparison
\[
 \left(\frac{497}{500}\right)^2\frac{85}{84}<1
\]
therefore yields `(497/500)r <= x`.  Since `r<1/4`, direct comparison of
\[
 s^2=1-2x+r^2
\]
with `(501/500-r)^2` proves `r+s<501/500`.  The exact divisor-envelope identity and the
Bernstein binomial sum then give
\[
 T_M\le A_*\left(\frac{501}{500}\right)^M,
 \qquad
 \Pi_M\le A_*^2\left(\frac{501}{500}\right)^{2M}.
\]
The already proved cancellation-resistant purity law says that false RH supplies some surviving
exponent `r>1`; the new upper estimate forces that exponent to be at most
`(501/500)^2 = 251001/250000 < 201/200`.

No RH assumption, verified-height certificate, divisor truncation, or numerical zero enumeration
is used.

## Remaining RH-bearing theorem

`[OPEN CORE]` Select the endpoint exponent: prove that `Pi_M` is uniformly bounded, equivalently
that every strict exponential normalization kills it.  The present theorem confines any contrary
phase to `(1,(501/500)^2)`, strictly inside `(1,201/200)`, but does not make that interval
empty.

## Formalization target

`formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinSectorConfinedPhase.lean`

Primary declarations:

- `norm_add_norm_one_sub_lt_sectorConfinedBase`
- `xiEndpointNormalizedReciprocalSquare_orientation_sq_le`
- `xiEndpointBernsteinAtomAmplitudeBase_lt_sectorConfined`
- `primeArchEndpointBernsteinTotalVariation_le_sectorConfined`
- `primeArchEndpointBernsteinPurity_le_sectorConfined`
- `xiSectorConfinedBernsteinAmplitudeBase_sq_eq`
- `exists_sectorConfined_primeArchEndpointBernsteinPurity_phase_of_not_riemannHypothesis`
- `exists_strict_sectorConfined_primeArchEndpointBernsteinPurity_phase_of_not_riemannHypothesis`
- `exists_fivePerMille_primeArchEndpointBernsteinPurity_phase_of_not_riemannHypothesis`
- `primeArchBernsteinSectorConfinedLoschmidtPhaseMaster`

## Gates

- [x] Existing disk, orientation, and purity declarations located
- [x] Paper proof complete
- [x] Lean theorem complete without placeholders
- [x] Targeted module check and axiom audit pass
- [x] Integrate into the master theorem and manuscript
