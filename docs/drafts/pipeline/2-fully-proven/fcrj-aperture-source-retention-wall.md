# FCRJ aperture source-retention wall

- **ID:** `fcrj-aperture-source-retention-wall`
- **Stage:** `2-fully-proven`
- **Route:** `CCM-FU / FCRJ`
- **Type:** `THEOREM (paper) [LEAN-PROVED] [POSITIVE SURVIVOR] [SHARP PROVIDER BOUNDARY]`
- **Date:** 2026-08-27
- **Source:** conjecture loops 58--65 in
  `docs/drafts/pipeline/1-in-progress/critical-multiplicative-compensated-cancellation-rh.md`

## Question

Can loop 65's shrinking-width ultraviolet control be used while retaining a nontrivial normalized
physical FCRJ source? More strongly, does the same aperture-width mechanism control complete
coherent carrier energy `||P||²`, the corrected-response deficit in `(AC26)--(AC28)`?

## Answer

Let

```text
W = sum_p log(p)/p,
L = sum_p (log(p)/p) ell_p,
P = sum_p (log(p)/p) phi_p,
```

where `ell_p` is clipped interval length and `phi_p` its centered indicator. For every finite
packet and `A>0`, weighted Hilbert Cauchy--Schwarz gives

```text
||P||² <= W sum_p (log(p)/p)||phi_p||² <= W L.          (SR1)
```

The second inequality uses the exact one-prime variance

```text
||phi_p||² = ell_p - ell_p²/A <= ell_p.                (SR2)
```

If every selected interval is active, `ell_p<=k-m`, hence

```text
||P||² <= (k-m)W².                                     (SR3)
```

Activity also implies the localized Mertens bound `W<=k+log 4`, so for `m<=k`, including the empty
packet,

```text
||P||² <= (k-m)(k+log 4)².                             (SR4)
```

For a nonempty packet, `||P||²=W² Disp`; therefore

```text
Disp <= k-m.                                           (SR5)
```

In the proper chamber `0<k-m<A`, corpus endpoint noncancellation supplies the other side:

```text
0 < Disp <= k-m.                                       (SR6)
```

Consequently every active schedule with `k_n-m_n -> 0` has `Disp_n -> 0`, and no fixed `c>0` can
lower-bound all normalized source strengths.

## Verdict

`[PROVED — FULL PHYSICAL FCRJ CARRIER ENERGY HAS PACKET-FREE MERTENS-WIDTH UPPER BOUND; SHRINKING
WIDTH CANNOT RETAIN A UNIFORM POSITIVE NORMALIZED SOURCE]`.

This is stronger than loop 65: `(SR4)` controls complete corrected-response deficit `||P||²`, not
only high-character tail. It gives an explicit RH-facing landing criterion. Any coefficient-faithful
FCRJ schedule satisfying

```text
(k_M-m_M)(k_M+log 4)² << log(M)^B/M
```

automatically places the full carrier inside target error budget. Conversely, presenting a
shrinking aperture as harmless ultraviolet regularization is false: `(SR6)` forces normalized
source collapse. Actual fixed-ratio physical windows remain unresolved; width cannot be freely
changed without changing source.

## Novelty audit

Weighted Cauchy--Schwarz, centered-indicator variance, and squeeze theorem are standard parent
analysis and are not claimed new. Prime short-window variance and its RH/pair-correlation links are
established literature; relevant primary sources include
[Montgomery--Soundararajan](https://arxiv.org/abs/math/0409258),
[Bui--Keating--Smith](https://arxiv.org/abs/1506.03741), and
[Carneiro--Chandee--Chirre--Milinovich](https://arxiv.org/abs/2108.09258).

Mandatory corpus searches and targeted current-literature searches found no statement combining
the exact clipped prime-log FCRJ carrier, physical weights `log p/p`, activity-localized Mertens
mass, full energy bound `(SR1)--(SR4)`, and normalized source-retention wall `(SR5)--(SR6)`.
Candidate-new content is restricted to this coefficient-faithful source synthesis and its exact
FCRJ provider boundary. No broad priority claim is made without expert review.

## Lean

Module:

```text
GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureSourceRetentionWall
```

Capstones:

- `norm_sq_xiPhysicalPrimeLogAggregateApertureCarrier_le`
- `xiPhysicalPrimeLogApertureFusionEnergy_le_weight_mul_weightedLength`
- `xiPhysicalPrimeLogApertureFusionEnergy_le_width_mul_totalWeight_sq`
- `xiPhysicalPrimeLogApertureFusionEnergy_le_mertens_width`
- `xiPhysicalPrimeLogNormalizedApertureDispersion_le_width`
- `xiPhysicalPrimeLogNormalizedApertureDispersion_mem_Ioc_width`
- `tendsto_xiPhysicalPrimeLogNormalizedApertureDispersion_zero_of_width`
- `not_exists_uniform_positive_xiPhysicalPrimeLogNormalizedApertureDispersion_of_width`

Audit:

- direct `lake env lean` check: pass;
- targeted `lake build GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureSourceRetentionWall`: pass;
- capstone `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`;
- theorem-area umbrella: wired;
- global lint: this module is reachable and clean, but promotion remains blocked by unrelated
  concurrently owned unwired modules in `RHTower.Sieve` and `HTGeometry`.

## Remaining burden

Instantiate `(SR4)` on actual cofinal `FCRJ` packet parameters. If physical ratio `K_M/M` stays
away from one, `k_M-m_M=log(K_M/M)` does not supply target decay; remaining problem is genuine
centered moving prime-log discrepancy, not Fourier ultraviolet control. If source construction
forces a sufficiently narrow coefficient-faithful window, `(SR4)` closes full carrier-energy
burden immediately.
