# Exact collar gauge energy and correlation-only packet control

- **ID:** signed-prime-polar-gauge-correlation
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Parent:** `1-in-progress/signed-prime-polar-transport-2026-10-17.md`
- **Count:** not yet counted; one complete package.

## Statement

For every actual compact continuous source f, collar source g at A=exp(a),
d=exp(b), and k=g'-g/2, prove

∫k² = 2(h(0)-h(d))/d² + ||g||²/4.

Both ||g||² and ∫k² are independent of A. With the existing actual source radius
T=multiplierSourceRadius f, prove

(∫|k|)² ≤ (2T+d) [2(h(0)-h(d))/d²+||g||²/4].

Substitute into the rough-source packet bound and global Lévy transport, eliminating
the constructed gauge L¹ cost in favor of original-source correlation geometry.
The roughness term M_N²||f-g||² remains explicit.

## Evidence and proof gates

- [x] Searches `/tmp/spp6-search.json` and `/tmp/spp6-gauge-search.json`:
  partial=false/errors=[]; candidate lemmas and source arguments inspected.
  Semantic coverage unmeasured; refresh deferred. No external novelty claim.
- [x] Read existing rough-gauge endpoints, actual source-radius construction, and
  compact-support derivative integration theorem. No retrieved endpoint provides
  this exact collar gauge law and elimination of the gauge-cost interface.
- [x] Dependency-closed paper proof in `SignedPrimePolarGaugeCorrelation.md`.
- [ ] Prove exact collar slope energy, slope/source orthogonality, gauge energy law.
- [ ] Prove position invariance and source-derived support interval of length 2T+d.
- [ ] Prove admitted L¹ bound from exact L² energy and support length.
- [ ] Transfer to actual packet and global signed Chebyshev transport.
- [ ] Direct leaf checks, scratch axioms/signatures, umbrella, lint/index, ledger.

No source derivative, grid blindness, nonzero-source or arithmetic estimate premise.
README remains read-only. Generic Cauchy–Schwarz and integration by parts are
inputs, not separately counted contributions.
