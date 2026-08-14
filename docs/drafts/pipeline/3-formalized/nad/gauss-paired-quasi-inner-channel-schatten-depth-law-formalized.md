# Gauss-paired quasi-inner channel Schatten depth law — formalized

- **ID:** `gauss-paired-quasi-inner-channel-schatten-depth-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `gauss-paired-quasi-inner-channel-schatten-depth-law.md`
- **Umbrella imports:** `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `HTGeometry/GaussPairedChannelSchattenDepth.lean` | the channel residue `(8)`, its independence of the component, the paired total residue `(11)`, the cofinal critical depth, and the regularization-order floor |
| `RHTower/WeakSchattenResidue.lean` | weak Schatten membership, the logarithmic partial sum, the log residue, and the exact-depth theorem |
| `RHTower/GaussPairedSchattenResidueProducer.lean` | the arithmetic residue as an actual `HasSchattenLogResidue` certificate |
| `RHTower/GaussPairedChannelSchattenCapstone.lean` | the exact direct-sum depth `(12)`–`(13)` and the cofinal exclusion law |
| `HTGeometry/DixmierIdeal.lean` | the Dixmier partial sum and ideal |
| `HTGeometry/ArithmeticComplementRank.lean` | the coefficient–state allocation `(19)`–`(20)` |

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

- `(8)` `gaussChannelResidue`, `gaussChannelResidue_pos`,
  `gaussChannelResidue_independent_of_component` — the exact positive per-channel residue
  `2(p−1)^{2m}(p^m−1)²/(p^{2m}m² log p)`, and its independence of the component label;
- `(11)` `gaussPairedChannelResidue`, `gaussPairedChannelResidue_pos` — the paired total residue is
  the sum over the aperture and is strictly positive;
- `(12)`–`(13)` `gaussPairedChannel_exact_schattenDepth` and
  `gaussPairedFinChannel_exact_schattenDepth` — **the exact Schatten depth**: from weak membership at
  exponent `2m` and the positive logarithmic residue, every exponent `0 < q ≤ 2m` is excluded and
  every `q > 2m` is admitted, so `inf{q > 0 : T ∈ S_q} = 2m` with the endpoint attained only in the
  weak ideal;
- the two halves that make it work, proved separately:
  `MemWeakSchattenClass.memSchattenClass_of_lt` (weak-to-ordinary inclusion strictly above the
  endpoint) and `HasSchattenLogResidue.not_memSchattenClass` (a positive logarithmic residue forbids
  the ordinary class at the endpoint), combined in
  `exact_schattenDepth_of_weak_of_positive_logResidue`;
- the residue side as a genuine certificate: `hasSchattenLogResidue_gaussPairedChannelResidue` and
  `hasSchattenLogResidue_gaussPairedCriticalDepth`;
- the cofinal regularization law: `gaussPairedCriticalDepth`, `tendsto_gaussPairedCriticalDepth`,
  `exists_gaussPairedCriticalDepth_gt`, `exists_gaussPairedCriticalDepth_ge`,
  `gaussPaired_regularizationOrder_iff`, and `exists_cutoff_not_memSchattenClass` — **no single
  positive Schatten class contains the whole cutoff family**;
- `(19)`–`(20)` `finrank_eq_arithmeticIntersection_add_complement` and
  `HTGeometry.finrank_le_arithmeticComplement_add` — the exact coefficient–state split and the
  linear allocation bound.

## Verification

```text
lake build GaloisForLFunctions.RHTower.GaussPairedChannelSchattenCapstone
lake build GaloisForLFunctions.RHTower.GaussPairedSchattenResidueProducer
```

## What closed last

The card's own audit had recorded that the module it cites "does not exist" and that the tree
contains "no weak Schatten ideals, no Dixmier traces".  Both were wrong: the module is in the
general-geometry area (`HTGeometry/GaussPairedChannelSchattenDepth.lean`, namespace
`GaloisForLFunctions.RHTower`), so a path-based check under `RHTower/` misses it, and
`WeakSchattenResidue.lean` and `DixmierIdeal.lean` carry the ideal substrate.  With that corrected,
the exact depth `(12)`–`(13)` is a theorem of the tree, proved from the analytic endpoint
certificates as explicit hypotheses — the `GaussChannelSchattenEndpointInput` structure is not used,
so nothing is postulated.

## Boundary

The endpoint certificates — weak `S_{2m,∞}` membership and the logarithmic residue value for the
actual quasi-inner channel operator — enter the Lean theorems as hypotheses; supplying them for the
true restricted-Weil operator is the card's own open gate "transport the resulting index to the true
restricted-Weil operator", together with "construct a uniform smoothing or covariance cancellation"
and "prove semilocal trace-remainder positivity".  The independent audit of the Gauss-component
residue theorem `(8)` is an external obligation, and **RH is the card's declared terminal open
core**.  This is not a proof of RH.
