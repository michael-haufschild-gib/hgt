# CCM exterior cosine dual mass wall

- **ID:** ccm-exterior-cosine-dual-mass-wall
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `ccm-exterior-cosine-superoscillation.md` · route decision C4
- **Statement:** Fixed-error approximation of the constant mode on expanding compact windows by arbitrary signed finite measures supported in a fixed exterior half-line forces total variation to diverge.

## Goal

Replace canonical-packet exponential growth by a representation-independent obstruction for the
whole CCM exterior finite-measure gauge ideal.  The theorem must use the actual positive-minus-positive
measure model and the exact mass appearing in the corrected-symbol coercive bound.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: Lean theorem, targeted build green, axiom audit PASS
- [ ] 3 → 4 publication-ready: standalone paper + Lean certificate + novelty audit

## Conjecture loop

### C5 — universal exterior mass wall

Fix `H₀ > 0` and `0 ≤ ε < 1`.  Let `μ_N, ν_N` be finite positive measures supported on
`[H₀,∞)`.  If their cosine-transform difference approximates `1` with error at most `ε` on the
support of a Sonin bump of width `N+1`, then

~~~text
(1-ε) J₀ ≤ 2 S((N+1)H₀) (μ_N(ℝ)+ν_N(ℝ)),
~~~

where `J₀>0` is reference-bump mass and `S(R)→0` is the already-formalized uniform Fourier-tail
majorant.  Hence combined measure mass tends to infinity.

## Approach

1. Prove Fubini identity pairing a Sonin bump with an arbitrary CCM cosine measure gauge.
2. Use exterior support and `soninRefTailSup` to bound pairing by measure mass times tail.
3. Pair uniform approximation error with nonnegative compact bump.
4. Cancel exact bump scaling and prove asymptotic mass divergence.
5. Feed result back into corrected-symbol compact reduction and decide whether any bounded
   Fourier–Stieltjes gauge route survives.

## Hostile audit

- Bound must cover arbitrary finite measures, not only atomic packets.
- Approximation need only hold where compact bump is nonzero; global uniform approximation is not
  required.
- Result does not by itself exclude a gauge whose mass diverges but whose useful positive tail also
  diverges.  Existing exterior Fourier–Stieltjes channel is bounded by this same mass, so route
  impact depends on exact error–tail comparison.
- A lower bound tending to infinity is not RH and must not be presented as positivity.

## Log

- 2026-08-21 — created after corpus search found the needed separator already split across
  `SoninReferenceTailSup.lean`, `SoninScaledMeanBound.lean`, and
  `CCMActualHeadExteriorCosineMeasureGauge.lean`.
- 2026-08-21 — C5 proved for arbitrary finite measures and formalized in
  `CCMActualHeadExteriorCosineDualMassWall.lean`.  Exact finite-width lower bound and asymptotic
  combined-mass divergence are unconditional.  Direct source check, targeted module build, and
  ten declaration axiom audits pass.  Route remains in progress: next test is whether rapid
  Fourier decay plus logarithmic Gamma coercivity creates an impossible mass/window fixed point.
- 2026-08-21 — corpus search exposed `SoninRefTailWeightedVanishing.lean`; reused its existing
  uniform rapid-decay theorem to strengthen C5.  For every fixed power `p`, combined mass divided
  by `(((N+1)H₀)^p)` tends to infinity.  Hostile audit rejects an immediate RH/no-fixed-point claim:
  global representative positivity does not itself force constant approximation across the whole
  Gamma-recovery interval.
