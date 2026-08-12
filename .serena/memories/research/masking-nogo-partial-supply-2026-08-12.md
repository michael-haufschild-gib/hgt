# Step 38: frontier pair — masking no-go + two-scale supply

Card: `docs/drafts/pipeline/1-in-progress/xic-order-one-growth-organ.md` (step 38).
Attack on step 37's frontier items (a)/(b)/(c).

## (c) DONE — masking no-go [LEAN-PROVED]

`GaloisForLFunctions.HTGeometry.exists_nonreal_config_forall_turanMinor_re_nonneg`
(`HTGeometry/TuranMinorSubEdgeMasking.lean`): explicit configuration — real atoms 12/25 and
5/12 with multiplicity 100 each, non-real conjugate pair w = (50+35i)/149 — is
conjugation-symmetric, in the open right unit half-disk, has ALL moments ≥ 0 and ALL plain
Turán minors ≥ 0 (every n), yet w is off the real axis. Key inequalities: |w| ≤ 5/12 gives
every w-interaction scale ≤ 1/5 = product of real atoms; multiplicity 100² vs 100 wins by a
single n-free rational bracket (norm_num). w is realizable as an actual resolvent point
(γ² = 1+√149/10, b = 7/(10γ) < 1/2, X = 0). Conclusion: plain minors cannot detect below
the geometric mean of two higher real atoms; the polynomial quantifier of the single-minor
criterion is NOT removable.

## (a) RESOLVED as a bridge [LEAN-PROVED]

The p = 1 datum Re(R₀R₂ − R₁²) ≥ 0 is not provable from the resolvent-chart axioms
(adversarial configuration makes it negative). Winnable form:
`RHTower.xiResolventTuranMinor_zero_re_nonneg_of_partial_line`
(`RHTower/XiResolventPartialLineSupply.lean`): (i) all copies with ‖u‖ ≥ δ on the line,
(ii) 8εS ≤ 2r₁r₂(r₁−r₂)² (ε = sub-δ tail of norm mass, S = total, r₁ ≠ r₂ above-δ moduli)
⇒ index-0 plain minor ≥ 0. Proof: pair-expansion split at δ; above-δ block = positive reals
≥ witness pair; complement mass = S² − (S−ε)² ≤ 2εS, ×4. Companion
`polyTuranMinor_one_zero_re_nonneg_of_partial_line` + `xiPolyMoment_one`.

## (b) QUEUED — effective descent

Turán power-sum effective bounds → finite-n oscillation windows → finite jet certificates
for partial RH. First step: quantitative version of the machine's Cesàro contradiction.

## New Lean traps

- `rw [norm_mul, norm_pow, norm_mul, pow_one]` normalizes only the first power of
  ‖(uv)^{0+1}(u−v)²‖ — target later bounds at the actual residual form.
- `set` after theorem binders rewrites inside hypotheses: `rw [← hx] at h` then fails
  (h already mentions x). Use the hypothesis directly.
- `![a,b,w,w']` at indices 2,3: prove `= w` / `= w'` as rfl facts, feed to norm_num
  (bare norm_num reduces only indices 0,1).
- Anonymous-constructor complex literals: prefer `↑x + ↑y * I` over ⟨x, y⟩ for access to
  the ofReal simp set.
