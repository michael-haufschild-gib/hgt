# Suzuki affine-sewn Weil--Robin far-tail factorization — formalization certificate

- **Stage:** 3-formalized
- **Paper proof:**
  `../../2-fully-proven/new_scientific_knowledge/suzuki-affine-sewn-weil-robin-far-tail-factorization.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/SuzukiAffineSewnWeilRobinFarTailFactorization.lean`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [SOURCE-SPECIFIC]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Formalized core

For sewn characteristic

```text
P=(beta-alpha) W_alpha W_beta
```

and affine sewn interval channel `S_gamma`, Lean proves every channel common after characteristic
normalization factors exactly:

```text
S_gamma(m W_alpha,m W_beta)=m P.
```

Consequences formalized without division:

- finite sums of common source channels factor before any cofinal limit;
- completed causal Weil--Robin reconstructions sew after multiplication by `z^2`;
- every delayed-hinge exterior and every Xi-real critical delayed-hinge atom factors through `P`;
- a common characteristic factor changes Hermitian Bezoutian only by congruence;
- at the phase-aligned node, any nonzero sewn characteristic preserves the strictly negative Pick
  diagonal of a positive-weight delayed-hinge atom.

Key declarations:

```text
suzukiAffineSewnIntervalPart_commonChannel_factorization
suzukiAffineSewnIntervalPart_finiteCommonChannels_factorization
z_sq_mul_suzukiAffineSewnIntervalPart_weilRobinReconstruction
suzukiAffineSewnIntervalPart_delayedHingeWeilExterior_factorization
suzukiAffineSewnIntervalPart_criticalDelayedHinge_factorization
suzukiHermitianBezoutCross_commonFactor
suzukiAffineSewnCharacteristicScaledPick_delayedHinge_neg_phaseAligned
```

The paper theorem then sums far prime-power channels in the source-native convergence half-plane:

```text
S_gamma(E_alpha^far,E_beta^far)
 = -P(z) sum_(log n>=2a) Lambda(n)/sqrt(n) exp(i z log n).
```

Thus far tail is universal after normalization: independent of both shifts, deficiency vectors,
and affine target.  Lean intentionally stops at finite common-channel algebra and exact individual
sign obstruction; it does not encode an unproved critical-line infinite sum.

## Frontier effect

Affine sewing cannot cancel far primes and cannot repair their atomwise negative Pick directions.
Any viable proof must mix complete far von-Mangoldt tail with Robin, aperture-entry, polar, and
Gamma channels before positivity.  Exact unresolved statement is
`SUZUKI-CAUSAL-ENTRY-SCHUR-WARD`; proving it would feed existing compound Pick/pole-tomography
connectors to RH.

## Integration and verification

- imported by `GaloisForLFunctions.RHTower` umbrella;
- imported and summarized in `RiemannHypothesisSOTA2026`;
- direct source check:
  `lake env lean GaloisForLFunctions/RHTower/SuzukiAffineSewnWeilRobinFarTailFactorization.lean`;
- targeted SOTA build: `9450/9450` jobs;
- axiom audit for five frontier declarations: `propext`, `Classical.choice`, `Quot.sound` only;
- forbidden declaration scan: no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.

RH is not yet proved.
