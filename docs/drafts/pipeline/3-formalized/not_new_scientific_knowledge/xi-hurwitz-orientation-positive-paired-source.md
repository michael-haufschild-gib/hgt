# Xi--Hurwitz orientation positive paired source reduction

- **ID:** `xi-hurwitz-orientation-positive-paired-source`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NO NOVELTY CLAIM]`
- **Statement:** At every exact off-line-quartet accretive radius `R`, the complete canonical
  Xi--Hurwitz orientation vector belongs to the Hilbert closure generated only by the
  positive-frequency Schwarz pairs `C_z - C_{-conj z}` with `R < re z`.  Their four-block
  continued prime--Gamma kernel is exactly a real kernel involving only positive-frequency
  source values.

## One-sided closure

Ordinary Schwarz conjugation acts on centered spectral coordinates by

```text
a -> -conj(a)
```

and on divisor Cauchy vectors by

```text
SchwarzLp(C_z) = -C_{-conj z}.
```

The signed Hurwitz orientation coefficient is invariant under the same conjugation.  The
absolutely summable multiplicity-fiber expansion of `v_Xi` can therefore be regrouped over the
positive-frequency half of the Xi divisor.  The exact quartet budget keeps the horizontal pole
exhaustion exterior, giving unconditionally

```text
v_Xi in closure span_C {
  C_z - C_{-conj z} : z is in the continued source domain, R < re z
}.
```

Consequently, positivity of the Weil Hilbert quadratic form on this one-sided paired algebraic
core implies RH.  Conversely RH makes the form nonnegative on the whole divisor `ell^2` carrier.
Thus

```text
XiPositivePairedContinuedCauchyCorePassivity R <-> RH
```

for every quartet-admissible `R`, including `R = 218/25`.

## Exact value reflection

On the full continued source domain Lean strengthens the previously used imaginary-part law to

```text
T(-conj z) = -conj(T(z)),
T(conj z) = conj(T(z)),
T(-z) = -T(z),
```

where `T = continuedPrimeArchSourceRelativeTrace`.  If

```text
K(z,w) = (T(conj w) - T(z)) / (z - conj w),
```

then the four blocks of the paired generators satisfy

```text
K(-conj z,-conj w) = conj(K(z,w)),
K(-conj z,w)       = conj(K(z,-conj w)).
```

Hence their complete paired kernel is the real lift

```text
2 re [
  (conj(T(w)) - T(z)) / (z - conj(w))
  + (T(w) + T(z)) / (z + w)
].
```

It uses only positive-frequency source values `T(z)` and `T(w)`.  Lean also identifies the
complete finite reduced matrix energy with the exact Weil Hilbert quadratic value of every
pairwise conjugate-separated positive paired packet.  Positive separated packets are dense in the
paired algebraic core, with their reduced source energies converging to the Hilbert value.

Therefore Lean proves the value-level criterion

```text
XiPositivePairedReducedSourcePassivity R <-> RH
```

at every quartet-admissible radius, including `218/25`.

## Remaining open core

The open input is now the matrix sign on the positive-frequency reduced kernel, not a two-sided
exterior source condition.  Scalar diagonal positivity does not suffice: mixed correlations
between distinct positive poles remain.  A proof must establish
`XiPositivePairedReducedSourcePassivity (218/25)` directly from the displayed prime--Gamma values,
without importing Xi zero locations or an RH-equivalent measure.

## Lean certificate

Module:

`formal/GaloisForLFunctions/RHTower/XiHurwitzOrientationPositivePairedSource.lean`

Principal declarations:

- `RHTower.continuedPrimeArchSourceRelativeTrace_negConj`
- `RHTower.xiWeilSchwarzLp_continuedCauchy`
- `RHTower.xiHurwitzOrientationFiberCoefficient_zeroConj`
- `RHTower.hasSum_xiHurwitzOrientationPositivePairedFiberVector`
- `RHTower.xiHurwitzOrientationVector_mem_positivePairedContinuedCauchyHilbertSubspace`
- `RHTower.riemannHypothesis_of_positivePairedContinuedCauchyCore_nonnegative`
- `RHTower.ccmPositivePairedCauchyKernel_eq_reduced`
- `RHTower.positivePairedContinuedCauchyCorePassivity_iff_riemannHypothesis`
- `RHTower.xiWeilHilbertQuadratic_positivePairedCauchy_eq_reducedKernel`
- `RHTower.xiWeilHilbertQuadratic_positivePairedPacket_eq_reducedEnergy`
- `RHTower.exists_pairwiseConjSeparatedPositivePairedSourceEnergy_tendsto`
- `RHTower.positivePairedReducedSourcePassivity_iff_riemannHypothesis`
- `RHTower.positivePairedReducedSourcePassivity_twoHundredEighteen_twentyFifths_iff_rh`

The module is imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Gates

- [x] mathematical proof complete
- [x] Lean formalization complete
- [x] focused module check
- [x] RHTower umbrella import
- [ ] positive semidefiniteness of every finite reduced positive-frequency kernel matrix
