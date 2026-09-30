# Slice positivity at orders `≥ C log log t` for almost every height

- **ID:** XI-SLICE-LOGLOG-ORDER
- **Stage:** 3-formalized
- **Type:** PARTIAL PRODUCER (slice receiver, route LA)
- **Parent:** `rh-goal-loop-opus-2026-09-29.md`, cycle 47; successor of XI-SLICE-TYPICAL-ORDER (MUST-567)

## Target

For every `δ > 0` there is `C_δ` such that for all large `T`, the heights `t ∈ [T, 2T]` at which
`c_{2k}(t) ≤ 0` for some `k ≥ C_δ log log t` have measure `≤ δT`.

So at almost every height the RH content of the slice criterion (all higher Laguerre inequalities
of `Ξ` at `t`) sits in orders `O(log log t)`.

## Mechanism (paper)

Order `k`, `L = log t`, saddle radius `R ≈ 2k/L`, saddle disc radius `≍ R`. The strip saddle
(`XiSliceSaddleStrip`) needs: zero-freeness on a disc of radius `≍ R` at displacement `≍ R`, and
the Stirling comparison with `C ≤ cL`, i.e. `|ζ'/ζ| ≤ cL` on the saddle disc. Dyadic scales
`R_j = 2^j R_0`, each handled by:

1. **Zero-freeness.** Zeros with displacement `b ≥ R_j/10` within height `≍ R_j`: bad measure
   `≲ Σ_{b ≥ cR₀} b` summed over scales (geometric), `≤ (D/(cR₀L))T + O(L²)` by the critical-scale
   tail moment (MUST-566).
2. **Upper bound.** `log|ζ| ≤ M ≈ (3/2) log L + ½ log V` on the Borel–Carathéodory disc: area mean
   value at radius `≍ R_j`, vertical mean square `≪ T log³ T` (A1), unit-`R_j` cells, Markov
   (bad measure `≤ T/V`); reflection with `|χ| ≤ K t^d`, `d ≍ R_j`, near the line (cost `e^{O(ck)}`).
3. **Lower bound at the centre.** On the zero-free disc `log|ζ|` is harmonic, so `log|ζ(c)|` equals
   the disc average; the average of `(log|ζ|)^-` over heights is `≤ (log|ζ|)^+`-average plus the
   **displaced Littlewood floor** `∫_T^{2T} log|ζ(x+it)| dt ≥ −C − K log T` for `x ∈ [½, 1]`
   (rectangle `[x, 15/2]`, zero term `≥ 0`). Markov: `(log|ζ(c)|)^- ≤ W log L` off `O(T/W)`.
4. **Borel–Carathéodory + Cauchy.** `|log ζ| ≤ C(M + W log L)` on the inner disc, `|ζ'/ζ| ≤
   C(M + W log L)/R_j`; the Stirling constant is `≤ cL` once `k ≥ C'(M + W log L)`, i.e.
   `k ≥ C_δ log L`.
5. **Tail.** Circle decay `t^{−R(1−cos θ)} = e^{−≈kθ²}` against `(B/m₀)² ≤ e^{2M + 2W log L +
   O(ck)}`.

Limit of the method: Borel–Carathéodory costs the size of `log|ζ|` at displacement `k/L`, which is
unbounded (≈ `√(log(L/k))` in distribution); bounded orders need direct mean squares of `ζ'/ζ`
near the line (Selberg's method).

## Lean plan

- D1 `ZetaDisplacedLittlewoodFloor`: displaced-line log-mean floor.
- D2 `ZetaTypicalScaleBounds`: scale-`R` typical upper/lower bounds and zero-freeness.
- D3 `ZetaTypicalScaleLogDeriv`: Borel–Carathéodory at scale `R`.
- D4 `XiSliceLogLogOrderPositivity`: saddle assembly over dyadic scales + tail.

## Log

- 2026-09-30 — card opened.
- 2026-09-30 — **D1 [L]** `ZetaDisplacedLittlewoodFloor`: Littlewood's lemma on `[c, 15/2] × [T₁, T₂]`,
  `½ ≤ c ≤ 1`, uniform edges; floor `∫ log|ζ(c+it)| ≥ −C − K log T₂`.
- **D2 [L]** `ZetaTypicalScaleBounds`: cells of length `h`, sliding windows with `(a+b)`-fold
  overlap; large values at scale `R` (`exists_volume_zetaLargeNearScale_le`, `O(T/(c²V²))`); small
  values on vertical lines (`exists_volume_logZeta_lt_neg_le`, `O(T log log T/W)`, tangent-line
  Jensen); scaled zero shadows (`exists_volume_zetaZeroShadowScaled_le`).
- **D3 [L]** `ZetaTypicalScaleLogDeriv`: Borel–Carathéodory at scale `R` (disc `2.9R` about
  `½ + 3R + it`): `|ζ'/ζ| ≤ 58(log M + W + 1)/R`, `|ζ| ≥ e^{−W−8(log M+W+1)}` on `|s−c| ≤ 2.3R`.
- **D4 [L]** `XiSliceLogLogOrderPositivity` (`ZetaScaleData`, per-scale saddle; B generalized to
  `2r ≤ R₁`), `XiSliceLogLogOrderDensity` (dyadic selection, covering, summed bounds, final
  theorem `eventually_volume_xiSliceCoeff_nonpos_loglog_le`). All clean, standard axioms, wired,
  no collisions. STATUS MUST-569 (MUST-568 was taken by another lane).
- 2026-09-30 — **Boundary (loop row 48).** Bounded orders a.e. need `|ζ'/ζ| ≤ cL` at displacement
  `≍ K/L` at typical heights, which is Selberg-level: either near-line zero density with exponent
  linear in `σ − ½` (for Selberg's `ζ'/ζ` lemma at `x = T^{C/K}`), or `S(t)`-type mean values (for the
  pair-correlation variance of Poisson-smoothed counts, whose `α ≈ 0` spike must be known to
  relative precision `o(1/K)`). Both reduce to the near-line mollified mean square with exponential
  error, which second moments do not give (head `ΣΛ(n)/log X · n^{−s}` ⇒ `1/a`; sharp cutoff ⇒
  `L⁴ e^{−2θa}`).
