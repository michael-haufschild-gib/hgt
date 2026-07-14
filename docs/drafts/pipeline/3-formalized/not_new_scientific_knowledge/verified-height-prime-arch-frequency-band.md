# Verified height transfers to a prime--archimedean frequency band

- **ID:** `verified-height-prime-arch-frequency-band`
- **Stage:** 3-formalized
- **Type:** THEOREM / `[TOP-DOWN VALUE TRANSFER]`
- **Scientific status:** `[PROVED IN LEAN] [BRIDGE] [NOT AN RH PROOF]`

## Target

Let `RHVerifiedThrough H` mean that every positive-ordinate Xi zero of height at most `H`
lies on the critical line.  For every real `R` with

```text
R + 1/2 <= H,
```

the continued prime--archimedean relative trace has the anti-Herglotz sign on the
whole centered frequency band

```text
0 < Im z < 1/2,  |Re z| <= R.
```

Moreover, under the same certificate, the positive-frequency tail above `R` is equivalent to
RH.  Thus the verified prefix is removed from the open source condition exactly, leaving only
the one-sided unverified tail.

## Mechanism

Pair every centered Xi spectral atom `a` with its critical-line conjugate.  If the underlying
zero has `|Im rho| <= H`, the verified-height hypothesis and Schwarz reflection give
`Im a = 0`.  Otherwise `H < |Re a|`.  The radius condition then gives

```text
|Re z - Re a| > 1/2 > |Im a|,
```

so the exact reflected-pair resolvent formula has nonpositive imaginary part.  Summation over
the multiplicity-exact Xi divisor transfers the atomwise sign to the continued source trace.

## Certified specialization

The paper-proven external certificate in
`../../2-fully-proven/not_new_scientific_knowledge/verified-height-one-zero-turing-extension.md`
has

```text
H1 = 768044885196911 / 256
   = 3,000,175,332,800.43359375.
```

The corresponding exact rational frequency radius is

```text
R1 = H1 - 1/2
   = 768044885196783 / 256
   = 3,000,175,332,799.93359375.
```

The generic transfer and the exact rational specialization are formalized.  The specialization
accepts the external certificate as an explicit `RHVerifiedThrough H1` hypothesis; importing the
published Platt--Trudgian prefix and the Arb Turing computation as a proof certificate remains
separate.

## Lean declarations

File:
`formal/GaloisForLFunctions/RHTower/PrimeArchVerifiedHeightAccretivity.lean`

- `xiZeroCopy_re_eq_half_of_verifiedThrough_of_abs_im_le`
- `XiC_ne_zero_of_upperHalf_verifiedHeightBand`
- `xiRelativeResolventTerm_lineConj_pair_im_nonpos_of_verifiedHeight`
- `xiRelativeResolventTrace_im_nonpos_of_verifiedHeight`
- `xiRelativeResolventTrace_im_nonpos_on_verifiedHeightBand`
- `continuedPrimeArchSourceRelativeTrace_im_nonpos_of_verifiedHeight`
- `continuedPrimeArchSourceRelativeTrace_im_nonpos_on_verifiedHeightBand`
- `continuedPrimeArchUpperAntiHerglotz_of_verifiedHeight_and_positiveFrequencyAbove`
- `continuedPrimeArchPositiveFrequencyAbove_iff_rh_of_verifiedHeight`
- `continuedPrimeArchPositiveFrequencyAbove_plattTrudgianArbRadius_iff_rh`

The atomwise, summed trace, and continued prime--Gamma source statements retain exact divisor
multiplicity.  No zero enumeration or RH assumption is used beyond the named finite-height
certificate.

## Gates

- [x] exact atomwise mechanism isolated
- [x] generic verified-height accretive-band theorem formalized
- [x] one-sided tail-to-RH capstone formalized
- [x] generated index and umbrella wiring
- [ ] external numerical certificate imported into Lean
- [ ] RH
