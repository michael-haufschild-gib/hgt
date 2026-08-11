# Label-faithful multi-place assembly of the Gauss channel system (2026-08-11)

Card: `docs/drafts/pipeline/1-in-progress/gauss-multiplace-label-faithful-assembly.md`.
Module: `RHTower/GaussMultiPlaceAssembly.lean` — umbrella-wired, RHTower builds, all nine
capstones depend only on propext/Classical.choice/Quot.sound.

Content (step 2 of the intersection-form programme, successor of
`research/gauss-propagated-iterate-m2-closed-2026-08-11`):
- `gaussAssembledBlock hm kk prime : GaussAssembledSpace J →L[ℂ] _` — block-diagonal of the
  per-place `gaussQuasiInnerGFull` on `PiLp 2 (fun _ : J => Lp ℂ 2 haar)`, built by the
  `PiLp.continuousLinearEquiv` sandwich; place-by-place apply is `rfl`; powers act placewise.
- Exact label-faithfulness: cross-place matrix elements of every power vanish identically;
  same-place elements are the actual single-place elements.
- `gaussAssembledDiagonal` — the (J → ℂ)-valued two-sided diagonal current (both frequency
  orientations as separate summands, never summed over labels).
- Per-label residue laws for the ACTUAL assembled operator: m = 1 (power 1) and m = 2 (power 2),
  each label carrying `gaussChannelResidue m (prime j)`.
- Codiagonal collapse: summing labels gives exactly `gaussPairedChannelResidue` — the existing
  paired Schatten layer is the label-blind shadow of this object.
- Reflection retention per label (sample-value conjugation, phase evenness).
- `gaussCanonicalPrimeFamily N : Fin (π N) → Nat.Primes` via `Nat.nth Nat.Prime`, proved
  injective (`Nat.nth_lt_nth Nat.infinite_setOf_prime`); `gaussCanonicalAssembled_law` bundles
  injectivity + per-label laws + collapse + cofinal depth.
- Carrier bridge: `gaussChannelResidueCurrent m : Nat.Primes → ℝ` strictly positive; Weil
  normalization `residue·log p = (2/m²)((p−1)/p)^{2m}(p^m−1)²`
  (`gaussChannelResidueCurrent_mul_log`); pointwise product with
  `sourceZeroHorizontalPrimeCarrier` preserves sign (left/right half), reverses under
  `xiZeroCopyLineConjEquiv`, and has the exact critical radical at every label.

Honest boundary (kept on the card): identification with the LITERAL Connes–Consani
intersection/Weil pairing is NOT claimed; positivity/orientation law absent; m ≥ 3 depth open.
The frontier map was updated in the multi-place-assembly section, the final frontier statement,
and the anchor list.