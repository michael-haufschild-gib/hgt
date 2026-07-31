# Quasi-local infinite l-bit law

- **ID:** `quasi-local-infinite-lbit-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Date:** 2026-07-30
- **Formal sources:**
  - `formal/GaloisForLFunctions/HTGeometry/QuasiLocalInfiniteLBitLaw.lean`
  - `formal/GaloisForLFunctions/HTGeometry/QuasiLocalInfiniteLBitDynamicsLaw.lean`
  - `formal/GaloisForLFunctions/HTGeometry/QuasiLocalInfiniteLBitEvolutionLaw.lean`

## Exact law

There is one coefficient assignment \(J\) on every nonempty finite support
of the countable chain such that:

\[
  \sum_{S\subset_{\mathrm{fin}}\mathbb N}|J_S|<\infty,
\]

\[
  |J_S|\le
  2^{-\left(|S|+\max S+\operatorname{diam}S\right)},
\]

and the coefficients are rationally independent. Consequently, for every
finite site type \(I\) and every embedding \(e:I\hookrightarrow\mathbb N\),
the restriction of this single field has

\[
  \boxed{\tau(J|_{e(I)})=2^{|I|}-1.}
\]

Thus exponential spatial decay and absolute summability do not impose a
finite-window recurrence-dimension ceiling.

The same coefficient field defines a genuine energy on every infinite
Boolean configuration:
\[
  E_\infty(\sigma)=\sum_{S\subset_{\mathrm{fin}}\mathbb N}
  J_S\chi_S(\sigma).
\]
This series is absolutely convergent, uniformly bounded and continuous in
the product topology. The nested first-\(n\)-site energies converge
uniformly to \(E_\infty\), with error bounded by the omitted absolute
interaction mass.

On continuous complex amplitudes over the infinite configuration space, this
energy generates the exact phase evolution
\[
  (U_t\psi)(\sigma)=
  \exp(-itE_\infty(\sigma))\psi(\sigma).
\]
The maps \(U_t\) form a strongly continuous one-parameter group of complex
linear isometric equivalences in the uniform norm.

## Formal declarations

- `quasiLocalInfiniteLBitCoefficient_linearIndependent`;
- `abs_quasiLocalInfiniteLBitCoefficient_le`;
- `abs_quasiLocalInfiniteLBitCoefficient_le_physical`;
- `summable_abs_quasiLocalInfiniteLBitCoefficient`;
- `quasiLocalInfiniteLBitRestriction_linearIndependent`;
- `quasiLocalInfiniteLBitRestriction_fullRank`;
- `summable_quasiLocalInfiniteLBitEnergyTerm`;
- `abs_quasiLocalInfiniteLBitEnergy_le_mass`;
- `abs_quasiLocalInfiniteLBitEnergy_sub_window_le_tail`;
- `tendsto_quasiLocalInfiniteLBitWindowTail_zero`;
- `tendstoUniformly_quasiLocalInfiniteLBitWindowEnergy`;
- `exists_quasiLocalInfiniteLBitWindow_uniformError`;
- `continuous_quasiLocalInfiniteLBitEnergy`;
- `quasiLocalInfiniteLBitEvolution_add`;
- `quasiLocalInfiniteLBitEvolution_neg_left`;
- `norm_quasiLocalInfiniteLBitEvolution`;
- `quasiLocalInfiniteLBitEvolutionLinearIsometryEquiv`;
- `continuous_quasiLocalInfiniteLBitEvolution_time`.

## Scope

The result is one origin-dependent, countable, absolutely summable l-bit
coefficient field, a
bounded continuous infinite-configuration diagonal energy, its uniform
finite-window limit, and reversible strongly continuous Schrödinger phase
evolution on the Banach space of continuous amplitudes. It does not
construct a multiplication operator on a chosen \(L^2\) measure, and
therefore does not claim Hilbert-space self-adjoint/unitary dynamics. It
also does not transfer the construction to a microscopic disordered spin
Hamiltonian.

## Verification

Direct target compilation passed:

```text
lake env lean GaloisForLFunctions/HTGeometry/QuasiLocalInfiniteLBitLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/QuasiLocalInfiniteLBitLaw.olean

lake env lean GaloisForLFunctions/HTGeometry/QuasiLocalInfiniteLBitDynamicsLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/QuasiLocalInfiniteLBitDynamicsLaw.olean

lake env lean GaloisForLFunctions/HTGeometry/QuasiLocalInfiniteLBitEvolutionLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/QuasiLocalInfiniteLBitEvolutionLaw.olean
```

Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
Final `lake build` audit is reserved for publication audit.
