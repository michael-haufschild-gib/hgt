# Suzuki critical wall-field square-root weld — formalization certificate

- **Stage:** 3-formalized
- **Paper proof:**
  `../../2-fully-proven/new_scientific_knowledge/suzuki-critical-wall-field-square-root-weld.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/SuzukiCriticalWallFieldSquareRootWeld.lean`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [SOURCE-SPECIFIC]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT RH]`

## Formalized result

For `n=p^(e+1)`, Lean defines observer-free critical Gamma wall field

```text
b_e=sqrt((log p/n)*exp(log n/2)),
omega_e(t)=conj(xiGammaEulerHeightBoundaryFeature(-1/2,t;(p,e))).
```

It proves, without estimates,

```text
omega_e(t)=b_e*exp(I*t*log(n)/2),
b_e^2=Lambda(n)/sqrt(n),
omega_e(t)^2=(Lambda(n)/sqrt(n))*exp(I*t*log n).
```

Consequently exact Xi-real far-hinge atom is `-I*omega_e(t)^2/t^2`; off `t=0`, multiplying by
`t^2` gives exact symmetric-square numerator.  Same field's linear degree is bare entry third jet
`t^2*omega_e(t)`, and existing critical forcing is this bare jet times cubically normalized
observer innovation.

Lean also proves source-type no-go: at valuation depth zero, old declaration
`suzukiCriticalEntryWallEndpointAmplitude` is injective in positive observer aperture.  Therefore
it cannot be one observer-independent restricted-Weil deficiency endpoint trace at two distinct
observer apertures.

Key declarations:

```text
suzukiCriticalWallField_eq_bareAmplitude_mul_kernel
sq_suzukiCriticalEntryWallBareAmplitude_eq_vonMangoldt_div_sqrt
sq_suzukiOscillatoryKernel_primePowerEntryWall
sq_suzukiCriticalWallField_eq_farHingeNumerator
suzukiCriticalDelayedHingeJumpAtom_eq_neg_I_mul_wallField_sq_div
sq_mul_suzukiCriticalDelayedHingeJumpAtom_eq_neg_I_mul_wallField_sq
suzukiDelayedHingeCompletedJet3_entryWall_eq_bareThirdJetAtom
suzukiCriticalEntryWallThirdJetAtom_eq_bare_mul_innovation
suzukiCriticalEntryWallEndpointAmplitude_zero_injective
```

## Scope and frontier

Formalization removes separate far-channel matching: far numerator is quadratic degree of same
field whose linear degree drives entry.  Subsequent resolvent audit classifies `b_e` as input
coordinate, not endpoint candidate.  Correct open core is
`SUZUKI-RESOLVENT-DRESSED-WALL-WARD`: instantiate actual restricted-Weil spectral measure and
boundary observation on dressed field, then prove mixed compensation residual uniformly lower
bounded.  Existing connector still requires assembled Ward-defect lower bound.  RH is not proved.

## Verification

- direct source check:
  `lake env lean GaloisForLFunctions/RHTower/SuzukiCriticalWallFieldSquareRootWeld.lean`;
- targeted SOTA build: `9454/9454` jobs;
- axiom audit: `propext`, `Classical.choice`, `Quot.sound` only;
- repository formal lint reaches new module but remains red on eleven unrelated concurrent
  unreachable modules (four `RHTower`, six `HTGeometry`, one `HilbertMetric`);
- no `sorry`, `admit`, new axiom, `opaque`, `unsafe`, numerical computation, estimate, or RH premise.
