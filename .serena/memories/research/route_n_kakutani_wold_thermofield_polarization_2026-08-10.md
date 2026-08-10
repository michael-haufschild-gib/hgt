# Route N C15-C16: Kakutani/Wold thermofield polarization

Date: 2026-08-10

## Closed formal modules

- `formal/GaloisForLFunctions/RHTower/HedenmalmGammaSewnKakutaniPolarizationBridge.lean`
- `formal/GaloisForLFunctions/RHTower/HedenmalmGammaSewnWoldThermofieldBridge.lean`
- Both umbrella-wired in `formal/GaloisForLFunctions/RHTower.lean`.
- Direct `lake env lean` passed for both.
- Explicit olean generation passed.
- Axiom audits use only `propext`, `Classical.choice`, `Quot.sound`.

## C15 exact channel/Krein polarization

At Route N critical horizon:
- universal channel mass `M0(p)=p^-1`;
- twisted channel mass `Mt(p)=p^(-1-2|t|)`;
- exact ratio `Mt/M0=p^(-2|t|)`, the transverse modular cocycle;
- square-root amplitudes `A0=p^-1/2`, `At=p^(-1/2-|t|)`;
- exact gap
  `primeValuationHellingerGap(-|t|,p)=(A0-At)^2
    = p Q_t(p)^2/(1+p^-|t|)^2`.
The singular C14 factor `p` is division by universal critical mass `p^-1`, not arbitrary renormalization.
The gap sequence is summable iff `t=0`.

## C16 exact Wold thermofield collision

The C15 masses are literally existing prime-valuation Wold masses:
- `M0 = primeRadialCriticalMass`;
- `Mt = primeRadialTwistedMass(-|t|)`;
- `A0*At = primeRadialCrossMass(-|t|)=p^(-1-|t|)`.

For existing squared local Wold thermofield Hellinger factor `F_t(p)`:
`1-F_t(p)
 = primeValuationHellingerGap(-|t|,p)/(1-p^(-1-|t|))^2
 = [p Q_t(p)^2/(1+p^-|t|)^2]/(1-p^(-1-|t|))^2`.

Its defect is summable iff `t=0`.

## Scientific meaning

Route N Krein wall, transverse modular cocycle, unnormalized Kakutani numerator, and full normalized Wold thermofield sector are exact polarizations of one Gamma-sewn marked doublet. Product-measure geometry is no longer an external analogous detector.

Corpus already supplies finite Wold thermofield vectors and finite Boolean contractions. Do not waste work reconstructing finite half-densities. Remaining producer is source-canonical coupled strict all-prime Boolean--Wold totalization on exceptional Cartier object, attaching Gamma/co-Poisson/Sonin Xi boundary class before divisor evaluation and proving Xi specialization conserves Wold modular marginal instead of replacing it with saturated Boolean/Weyl record.

## Docs updated

- Route N card advanced through C16 and equations N.30-N.32.
- Frontier Route N open core corrected from building finite half-densities to coupled Boolean--Wold exceptional-Cartier totalization.
