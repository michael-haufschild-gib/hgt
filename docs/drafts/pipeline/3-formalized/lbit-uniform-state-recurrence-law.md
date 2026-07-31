# Uniform-product-state visibility of l-bit recurrence rank

- **ID:** `lbit-uniform-state-recurrence-law`
- **Status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Formal file:** `formal/GaloisForLFunctions/HTGeometry/LBitUniformStateRecurrenceLaw.lean`

## Exact theorem

For any finite binary l-bit Hamiltonian
\[
E_J(x)=\sum_{S\subseteq I}J_S\chi_S(x),
\]
the configuration-basis state with amplitudes
\[
\psi_+(x)=\sqrt{2^{-|I|}}
\]
is normalized and has nonzero Born weight on every configuration. Its
state-visible anchored-gap space is therefore exactly the full l-bit gap
space:
\[
\operatorname{span}_{\mathbb Q}
\{E_J(x)-E_J(0):|\psi_+(x)|^2\ne0\}
=
\operatorname{span}_{\mathbb Q}
\{E_J(x)-E_J(0):x\in\{0,1\}^{I}\}.
\]
Hence its visible temporal rank is `lbitTemporalRank J`.

Its Hilbert-space survival amplitude is exactly the equal-weight spectral
phase sum
\[
\langle\psi_+,e^{itH_J}\psi_+\rangle
=2^{-|I|}\sum_x e^{itE_J(x)}.
\]
Finally,
\[
\tau(J)=2^{|I|}-1
\]
if and only if, at every replica order, the completed long-time mean of this
single state's survival-fidelity moment attains the unavoidable permutation
collision floor.

## Lean declarations

- `lbitUniformSpectralWeight`
- `lbitUniformSpectralWeight_pos`
- `sum_lbitUniformSpectralWeight_eq_one`
- `lbitUniformProductState`
- `sum_normSq_lbitUniformProductState_eq_one`
- `lbitUniformProductState_ne_zero`
- `lbitDiagonalEvolvedUniformProductState`
- `lbitUniformProductStateSurvivalAmplitude`
- `lbitUniformProductStateSurvivalAmplitude_eq`
- `lbitUniformStateVisibleGapSubspace`
- `lbitUniformStateVisibleGapSubspace_eq`
- `lbitUniformStateVisibleTemporalRank`
- `lbitUniformStateVisibleTemporalRank_eq`
- `lbitTemporalRank_eq_maximal_iff_maximallyProjectiveEnergy`
- `lbitUniformState_all_survivalFidelityMoments_extremal_iff`

## Verification

Foreground target check:

```text
lake env lean GaloisForLFunctions/HTGeometry/LBitUniformStateRecurrenceLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/LBitUniformStateRecurrenceLaw.olean
```

passed. `#print axioms` for all load-bearing theorems reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Hostile scope audit

This closes one precise objection: maximal Hamiltonian recurrence rank is
not hidden from every preparable state at the exact l-bit fixed point. The
uniform product state has full configuration support and sees every gap
direction.

It does **not** prove:

- efficient extraction of exact rational rank from finite noisy data;
- scalable measurement of all replica orders;
- preparation in microscopic physical-spin coordinates when the l-bit
  dressing unitary is unknown;
- transfer to a generic Anderson, random-field XXZ, or MBL Hamiltonian;
- an experimentally feasible device protocol.

The result is a formalized bridge from spectral rank to one concrete
full-support return observable. It is not by itself a novelty headline.
