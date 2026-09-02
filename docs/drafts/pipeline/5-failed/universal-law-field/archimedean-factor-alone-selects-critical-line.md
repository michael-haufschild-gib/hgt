# Archimedean factor alone selects the critical line

- **Stage:** 5-failed
- **Claim:** The Gamma factor and functional equation alone force nontrivial zeros onto the critical line.
- **Verdict:** `[FALSIFIED]`
- **Lean status:** Killing mechanism and positive survivors already `[LEAN-PROVED]`; no new Lean required.

## What is wrong

`GammaFECell` is closed under multiplication by a positive reciprocal quartic. The resulting
all-prime zeta-bearing member is zero-free on the real open strip but has an explicit nonreal
off-line strip zero. Thus Gamma completion, integral multiplicativity, the functional equation,
and real-strip zero-freeness do not select the line. Exact certificate:
`gammaFECell_real_zero_free_nonreal_strip_mobility` in
`RHTower/GammaCellNonrealMobility.lean`.

This also blocks the stronger slogan that the archimedean factor contains the divisor. On
`Re s > 1`, `Gamma_R` is nonvanishing and completed zeta is `Gamma_R(s) zeta(s)`; nontrivial divisor
data are not created by Gamma.

## Strongest positive survivor

The corpus supports a narrower reversal.

1. The actual positive-half theta seam is diffuse information not recoverable, even nonlinearly,
   from all prime-power samples; its sampling defect is its full mass. Reflection completion doubles
   that defect and leaves normalized defect equal to one
   (`SeamArchimedeanSamplingQuotient.lean`, `ArchimedeanSamplingDefect.lean`).
2. The archimedean form is uniformly positive definite with lower constant
   `4 - 3 log 2 - pi/2`; Weil positivity becomes the operator domination `P_prime <= Q_infinity`
   (`ArchimedeanPairingDefinite.lean`).
3. Actual completed walls split exactly as positive atomic prime mass minus positive continuous
   archimedean mass (`SuzukiWardAtomicContinuousLightWeld.lean`), and cofinal raw-prime contours
   differ from complete Weil energy by one explicit centered archimedean square
   (`XiPhysicalPrimeApertureThetaAbelEnergyPrimeCanonicalVanishingLimit.lean`).
4. Direct Hilbert--Schmidt or sampling reconstruction cannot weld the atomic and diffuse channels;
   the completed reciprocity current is instead the nonlocal meromorphic cochain `-xi'/xi`
   (`SeamArchimedeanNoGo.lean`, `SeamFluxCompletion.lean`).

Hence infinity supplies the polarization/capacity and finite places supply atomic loading. The
vertical zero pattern can depend on primes while the horizontal axis is fixed by the half-density
normalization at infinity. This is a global interface statement, not an archimedean-local theorem.

## Replacement constraint

A live mechanism must prove, from literal integer formation before divisor specialization, a
coefficient-faithful **nonlocal atomic--diffuse completion law**. It must force the finite-place
current to be admissible in the archimedean theta polarization while retaining orientation and
completion history. Its RH consequence would be the already exact domination/selection endpoint.

It cannot be:

- Gamma or functional-equation structure alone;
- raw measure domination, since atomic and diffuse channels are singular;
- reconstruction from prime-power samples;
- a direct Hilbert--Schmidt pairing;
- imposed Weil positivity, self-adjointness, regularity, or bounded completion.

The remaining scientific question is whether the full integer theta source—not the isolated Gamma
factor—generates such admissibility through a law coupling additive Fourier self-duality to
multiplicative Euler formation. Static addition-versus-multiplication coherence is already retired;
only a law about their inequivalent completions can survive.

## Parent-theory audit

Connes--Consani derive genuine positivity at the single archimedean place from compressed scaling,
but explicitly pass to the semilocal setting for the RH implication
(`arXiv:2006.13771`). Their adelic trace formula treats critical zeros as absorption spectrum and
possible off-line zeros as resonances (`arXiv:math/9811068`). These support the polarization versus
resonance split but do not supply the missing source-generated atomic--diffuse admission law.

## Positive-survivor status

- Sampling escape/maximal defect: `[LEAN-PROVED]`.
- Archimedean definiteness and atomic--continuous decompositions: `[LEAN-PROVED]`.
- Source-generated nonlocal admission law: `[OPEN CORE]`; no theorem claimed.

