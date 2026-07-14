# Xi faithful thermal projective-moment abscissa spectrum

- **ID:** `xi-thermal-projective-moment-abscissa-spectrum`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[PROVED] [FORMALIZED] [RH-LEVERAGE] [NOVELTY NOT ASSERTED]`

## Main value law

For every multiplicity copy `q` of a Xi zero, set

```text
x_q = Re (xiZeroCopyReciprocalSquare q) > 0,
d_q = |Re(q)-1/2|.
```

The faithful static projective thermal moments are

```text
P_m = sum_q x_q d_q^m.
```

Every `P_m` is absolutely summable and nonnegative.  Its zeroth mass is already the unconditional
prime--Gamma source value

```text
P_0 = normalizedPrimeArchMoment 0 > 0.
```

For every `alpha >= 0`, Lean proves the exact source-normalized support law

```text
XiZeroHalfPlaneBound alpha
  <-> forall m, P_m <= normalizedPrimeArchMoment 0 * alpha^m.       (1)
```

For every positive `alpha`, the prefactor and every finite initial segment can be discarded:

```text
XiZeroHalfPlaneBound alpha
  <-> exists C, eventually_m P_m <= C * alpha^m.                   (2)
```

Faithfulness is decisive in the converse.  If one atom has `d_q > alpha`, then
`x_q d_q^m` is a positive lower bound for `P_m` and geometrically outruns every fixed multiple of
`alpha^m`.

## Direct prime-source interface

For every admissible fixed window, the established projective source spectrum and `(1)` give

```text
abscissa(negative fixed-window prime--Gamma source) <= 1+alpha
  <-> forall m, P_m <= normalizedPrimeArchMoment 0 * alpha^m.       (3)
```

At every positive scale the sharper cofinal form is

```text
abscissa(negative fixed-window prime--Gamma source) <= 1+alpha
  <-> exists C, eventually_m P_m <= C * alpha^m.                   (4)
```

The exact Gamma-free RH target is therefore

```text
abscissa(rectangularPrimePolarSource negative part) <= 1
  <-> forall alpha>0, exists C_alpha,
        eventually_m P_m <= C_alpha * alpha^m.                     (5)
```

Equation `(5)` is a genuine proof-burden change.  The earlier thermal chart asked for exact
second-moment convergence to the continued source value.  The cofinal chart asks instead for
arbitrarily small eventual exponential rates at high moment order; no exact finite-coordinate
identity and no prescribed prefactor remains.

## Cold partition strengthening

The same faithful state has the positive cold partition values

```text
Z_k = sum_q x_q * exp(k*d_q).
```

They are finite for every `k`, satisfy `Z_0=normalizedPrimeArchMoment 0`, and are pointwise limits
of the growing finite-system partition values.  Lean proves the exact free-energy envelope

```text
XiZeroHalfPlaneBound alpha
  <-> exists C, eventually_k Z_k <= C*exp(k*alpha)                 (7)
```

for every `alpha>=0`.  At the critical scale this collapses to one positive boundedness
obligation:

```text
RH <-> exists C, eventually_k Z_k <= C,                            (8)

abscissa(rectangularPrimePolarSource negative part) <= 1
  <-> exists C, eventually_k Z_k <= C.                             (9)
```

Thus an off-line atom is not merely a small quadratic energy: it produces exponential cold
free-energy growth.  The remaining physics obligation can be stated as uniform boundedness across
the thermodynamic and cold limits.  Pointwise thermodynamic convergence alone does not provide
that uniformity.

## Finite thermodynamic discharge

Let

```text
Z_(N,k) = sum_(j<N) x_(q_j) * exp(k*d_(q_j))
```

be the finite thermal partition value.  Lean proves the exact finite-system law

```text
RH
  <-> exists C, eventually_k eventually_N Z_(N,k) <= C,          (10)

abscissa(rectangularPrimePolarSource negative part) <= 1
  <-> exists C, eventually_k eventually_N Z_(N,k) <= C.          (11)
```

For each sufficiently cold `k`, pointwise thermodynamic convergence passes the eventual
finite-system bound to `Z_k`; the bound `C` is already independent of `k`, so `(8)` closes RH.
Conversely, positivity makes every finite partition value at most its full value, so RH supplies
the same uniform finite-system bound.  Consequently the remaining finite-physics obligation is
neither one exact finite realization nor convergence of moments alone.  It is exactly one uniform
energy estimate across the cold and thermodynamic limits.

## Finite KMS producer

For the multiplicity-exact enumeration `q_j`, define

```text
P_(N,m) = sum_(j<N) x_(q_j) d_(q_j)^m.
```

Lean proves unconditionally:

- every `P_(N,.)` is an explicit finite KMS/Wightman moment sequence;
- `P_(N,.)` converges pointwise to `P_.`;
- the complete limit belongs to the closed trace--Hankel cone.

Thus the finite-system and thermodynamic-limit positivity obligations are fully discharged.  The
remaining physics or arithmetic obligation is the cofinal decay in `(5)`.

## Zero fibre

The faithful first moment is nonnegative and

```text
RH <-> P_1 = 0 <-> P_1 <= 0.                                      (6)
```

This positive statement is retained as the finite-coordinate endpoint, while `(5)` supplies the
asymptotic endpoint that can interact with locality, clustering, or high-order field estimates.
Neither `(5)` nor `(6)` is proved here unconditionally on its right-hand side, so this module does
not prove RH.

## Lean certificate

Formalization:

```text
formal/GaloisForLFunctions/RHTower/XiThermalProjectiveMomentSpectrum.lean
```

Principal declarations:

- `xiThermalProjectiveMoment`
- `xiThermalProjectiveTruncation`
- `summable_xiThermalProjectiveMoment`
- `xiThermalProjectiveMoment_zero_eq_source`
- `xiThermalProjectiveColdPartition`
- `xiThermalProjectiveColdTruncation`
- `summable_xiThermalProjectiveColdPartition`
- `xiThermalProjectiveColdPartition_zero_eq_source`
- `tendsto_xiThermalProjectiveColdTruncation`
- `xiThermalProjectiveColdTruncation_le_partition`
- `finiteKMSWightmanMomentSequence_xiThermalProjectiveTruncation`
- `tendsto_xiThermalProjectiveTruncation`
- `sequenceTraceHankelNonnegative_xiThermalProjectiveMoment`
- `xiZeroHalfPlaneBound_iff_forall_thermalProjectiveMoment_le`
- `primeGamma_abscissa_le_iff_forall_thermalProjectiveMoment_le`
- `xiZeroHalfPlaneBound_iff_exists_eventually_thermalProjectiveMoment_le`
- `primeGamma_abscissa_le_iff_exists_eventually_thermalProjectiveMoment_le`
- `riemannHypothesis_iff_forall_pos_exists_eventually_thermalProjectiveMoment_le`
- `rectangularPrimePolarSource_negativeAbscissa_le_one_iff_cofinal_thermalProjectiveMoments`
- `xiZeroHalfPlaneBound_iff_exists_eventually_thermalProjectiveColdPartition_le`
- `riemannHypothesis_iff_exists_eventually_bounded_thermalProjectiveColdPartition`
- `rectangularPrimePolarSource_negativeAbscissa_le_one_iff_eventually_bounded_coldPartition`
- `riemannHypothesis_iff_exists_eventually_cold_eventually_thermodynamic_bound`
- `rectangularPrimePolarSource_negativeAbscissa_le_one_iff_eventually_cold_eventually_thermodynamic_bound`
- `xiThermalProjectiveMoment_one_eq_zero_iff_rh`
- `xiThermalProjectiveMoment_one_le_zero_iff_rh`

## Verification

- [x] direct module compilation
- [x] finite KMS realization and pointwise closed-cone limit
- [x] exact scale-wise moment law
- [x] converse by faithfulness and geometric-power escape
- [x] cofinal eventual-envelope law
- [x] fixed-window and Gamma-free abscissa interfaces
- [x] zero-fibre RH equivalence
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [x] formal lint
