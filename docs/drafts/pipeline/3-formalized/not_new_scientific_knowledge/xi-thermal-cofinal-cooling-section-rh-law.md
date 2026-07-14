# Xi thermal cofinal cooling-section RH law

- **ID:** `xi-thermal-cofinal-cooling-section-rh-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / RH-LEVERAGE
- **Status:** `[PROVED] [FORMALIZED] [NOVELTY NOT ASSERTED]`

## Main law

Let `size,cold : N -> N` be arbitrary schedules with

```text
size(j) -> infinity,
cold(j) -> infinity.
```

For the faithful finite projective thermal values

```text
Z_j = xiThermalProjectiveColdTruncation (size j) (cold j),
```

Lean proves the exact alternative

```text
not RH  <->  Z_j -> +infinity.                                  (1)
```

Equivalently,

```text
RH <-> exists C, eventually_j Z_j <= C,                          (2)
RH <-> exists C, frequently_j Z_j <= C.                          (3)
```

The second equivalence is the strongest proof-burden reduction.  A uniform two-parameter cold and
thermodynamic estimate is unnecessary.  One fixed upper bound need only recur cofinally often
along one simultaneous cooling schedule.  In particular the diagonal `size(j)=cold(j)=j` gives

```text
RH <-> exists C, frequently_j
  xiThermalProjectiveColdTruncation j j <= C.                     (4)
```

Thus one bounded subsequence of explicit finite KMS systems along the diagonal is sufficient.

## Proof

Every summand of the finite partition value is positive.  The truncation is therefore monotone in
both finite-system size and inverse temperature.  A bound along a cofinal section dominates every
fixed finite rectangle; the already-formalized pointwise thermodynamic limit then bounds the
complete cold partition.  The existing bounded-cold-partition criterion yields RH.

For the sharp converse, if RH is false then at least one multiplicity copy `q` has strictly positive
projective reflection displacement

```text
d_q = |Re(q)-1/2| > 0.
```

Every cofinal size schedule eventually contains that atom, while every cofinal cold schedule makes
its positive contribution

```text
xiThermalNode(q) * exp(cold(j) * d_q)
```

tend to `+infinity`.  Positivity transfers this divergence to the full finite partition value.
This proves `(1)`, and `(3)` follows because a sequence tending to `+infinity` cannot return
cofinally often below one fixed finite bound.

## Direct prime-source application

For every admissible fixed window and cutoff, the exact Gamma-free target is now

```text
abscissa(rectangularPrimePolarSource negative part) <= 1
  <-> exists C, frequently_j
        xiThermalProjectiveColdTruncation j j <= C.               (5)
```

Consequently the finite KMS producer, closed trace-Hankel cone, thermodynamic limit, and RH
capstone reduce the remaining physics obligation to one recurrent diagonal value estimate.  No
single finite system must realize all moments, no two-parameter uniform limit must be controlled,
and no exact source-moment equality is assumed in `(5)`.

The right side of `(5)` is not proved unconditionally here, so this theorem does not prove RH.

## Lean certificate

Formalization:

```text
formal/GaloisForLFunctions/RHTower/XiThermalProjectiveCofinalSection.lean
```

Principal declarations:

- `xiThermalProjectiveColdTruncation_mono_size`;
- `xiThermalProjectiveColdTruncation_mono_cold`;
- `xiThermalProjectiveColdTruncation_mono`;
- `riemannHypothesis_iff_exists_eventually_bounded_thermalProjectiveCofinalSection`;
- `thermalProjectiveCofinalSection_tendsto_atTop_of_not_riemannHypothesis`;
- `thermalProjectiveCofinalSection_tendsto_atTop_iff_not_riemannHypothesis`;
- `riemannHypothesis_iff_exists_frequently_bounded_thermalProjectiveCofinalSection`;
- `riemannHypothesis_iff_exists_frequently_bounded_thermalProjectiveDiagonal`;
- `rectangularPrimePolarSource_negativeAbscissa_le_one_iff_frequently_bounded_thermalProjectiveDiagonal`.

## Verification

- [x] direct module compilation
- [x] narrow Lake target build
- [x] registered in the RHTower umbrella
- [x] no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
