# Low-edge anchoring forces cofinal Gauss spread and harmonic projective work

- **ID:** mass-shifted-projective-low-edge-anchor-cofinal-spread
- **Stage:** 3-formalized
- **Route:** U, cofinal projective curvature renewal
- **Type:** THEOREM (Lean) + FRONTIER REDUCTION
- **Scientific status:** [PAPER-PROVED] [LEAN-PROVED] [AXIOM-AUDITED] [NOT RH]
- **Paper proof:**
  `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/mass-shifted-projective-low-edge-anchor-cofinal-spread.md`
- **Lean module:**
  `GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionProjectiveCofinalSpread`
- **Statement:** Positive shifted-Xi admission blocks have strictly increasing Gauss-root spread;
  every cofinal positive-block schedule has divergent normalized spread; and one fixed low Jacobi
  edge forces a degree-uniform harmonic lower bound for projective arithmetic surplus.

## Formalized theorem surface

Lean proves:

1. exact low-edge square completion and positivity of
   `projectiveLowEdgeAnchor`;
2. `projectiveLowEdgeAnchor (xiShiftedFarRightNormalizedMoment w) -> 1` as `w -> +infinity`;
3. exact degree renewal
   `G_(n+1) - G_n = n/(n+1) * (alpha_n - mean(alpha_<n))^2 + 2 * beta_n`;
4. strict spread increase on every positive admission block;
5. fixed-prefix beta inventory lower bound for current spread;
6. low-edge coercivity
   `surplus >= anchor/(2*n+1) * flux^2`;
7. eventual shifted-Xi harmonic bound
   `surplus >= 1/(2*(2*n+1)) * flux^2`, uniformly in degree;
8. divergence of projective Gauss-root spread along every cofinal actual shifted-Xi schedule whose
   required Hankel blocks are positive definite.

Principal declarations:

- `projectiveGaussRootSpread_succ_sub`
- `projectiveGaussRootSpread_strictMono_step`
- `projectiveGaussRootSpread_ge_two_beta_prefix`
- `projectiveSurplus_ge_lowEdgeAnchor_mul_flux_sq_div_degree`
- `dimensionlessProjectiveArithmeticSurplus_ge_harmonic`
- `tendsto_projectiveGaussRootSpread_along_cofinal_actual_positive_blocks`
- `routeU_cofinalSpread_and_harmonicWork_closed`

`routeU_cofinalSpread_and_harmonicWork_closed` is a closed Lean proposition, but its cofinal-spread
component quantifies an implication from positive Hankel blocks. It does **not** prove those blocks
positive and is not an unconditional RH theorem. This wrapper is only an axiom-audit surface; it
must not be counted as removal of Route U's positivity premise.

## Verification

Executed from `formal/` on 2026-08-12:

```text
lake env lean GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionProjectiveCofinalSpread.lean
lake build GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionProjectiveCofinalSpread
lake env lean /tmp/RouteUCofinalAudit.lean
```

All three commands exited `0`. Targeted build emitted
`XiShiftedCanonicalAdmissionProjectiveCofinalSpread.olean` (1,594,600 bytes). Axiom audit of the
four principal declarations reported only standard Lean foundations:

```text
[propext, Classical.choice, Quot.sound]
```

Source scan found no `sorry`, `admit`, declaration `axiom`, `opaque`, or `unsafe`. Module is wired
into `GaloisForLFunctions.RHTower`.

Repository-wide `scripts/formal_tools.py lint` was also run. It exited `1` on existing unrelated
umbrella-reachability debt spanning Bourgain, Sieve, Suzuki, and HTGeometry modules; it did not
report this module as unreachable or report a forbidden declaration here. Therefore global lint is
not claimed green.

No numerical or symbolic computation was used to discover, justify, or certify these statements.

## Exact remaining obstruction

This formalization closes two generic escapes: absolute normalized spread collapse and continuous
projective work smaller than harmonic degree order. It does not synchronize degree changes.
Positive moment geometry admits divergent negative reciprocal-clock resets while ordinary
variance and spread increments vanish. Remaining hard target is Xi-specific control of either:

1. normalized flux away from the singular reciprocal-mean boundary; or
2. cumulative denominator-weighted hyperbolic reset action.

Proving neither is replaced by the present implication. RH remains open in this corpus.

## Log

- 2026-08-12 — exact paper theorem formalized, direct Lean check and targeted Lake build passed,
  axiom surface audited; remaining denominator-weighted synchronization obstruction preserved.
