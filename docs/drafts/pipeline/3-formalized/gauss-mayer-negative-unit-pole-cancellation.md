# Successor telescoping cancels the negative-unit Mayer determinant pole

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [exact determinant pole](gauss-mayer-rank-one-determinant-pole.md).

## Theorem

For every `Re w>0`, the actual Mayer remainder `R(w)` and projection `P f=f(0)·1` satisfy

`det(I+R(w)+tP)=det(I+R(w))` for every complex `t`.

Consequently `B(w,−1)=0` throughout this half-plane. The genuine source
determinant equals `A(w,−1)` there, including its assigned value at one,
and is holomorphic throughout the half-plane. The parameter is nonzero; this is a specific cancellation required
by the even-word determinant product, beyond generic zero isolation.

## Proof

1. The actual disc `|z−1|≤3/2` excludes the branch cut of `1+z`, so
   `f_w(z)=1−(1+z)^(−w)` belongs to its disc algebra and vanishes at zero.
   For `a=n+z`, both `a` and `a+1` have positive real part. Their principal
   logarithms have imaginary parts in `(−π/2,π/2)`, making their difference
   lie in `(−π,π)`. Exponential/logarithm inversion gives
   `log(1+a⁻¹)=log(a+1)−log a`. Hence each genuine branch applied to `f_w`
   equals `(n+z)^(−w)−(n+z+1)^(−w)`. The first `N` terms telescope to
   `(1+z)^(−w)−(N+1+z)^(−w)`. The established source power bound makes
   the tail tend to zero. Normal convergence of the operator remainders
   identifies this sum with `R(w)f_w`, proving `f_w+R(w)f_w=1`.
2. In the fixed Hilbert coefficient space, let `Q` be the actual Cauchy
   analysis map and let
   `q(v)=Σ_j (−1)^j(6/5)^(−j)v_j`. Its coefficients are absolutely
   summable, making `q` bounded. Cauchy's formula gives `q(Qg)=g(0)`.
   Thus `x=Q1`, `u=Qf_w`, and `P_H=x⊗q` have `q(x)=1`, `q(u)=0`.
3. Subtract the same zeta multiple of `P_H` from the existing Hilbert
   source operator to obtain `A`. Its matrix is exactly the remainder
   matrix, and the established factorization gives `AQg=QR(w)g`.
   Therefore `u+Au=x`. No inverse of `I+A` is assumed.
4. The generic Hilbert–Schmidt rank-one update, applied to `tu,tx,q`,
   gives `det₂(I+A+tP_H)=det₂(I+A) exp(−t)`. The actual matrices decay
   geometrically. Passing their finite determinants gives the ordinary
   Fredholm identity `det(I+M)=det₂(I+M) exp(Σ_i M_ii)`.
   The diagonal of `P_H` sums to one, so its correction contributes
   `exp(t)`. The two exponentials cancel, proving independence of `t`.
5. The exact affine decomposition defines
   `B(w,−1)=det(I+R(w)+P)−det(I+R(w))`. It is zero by step 4.
   The exact source identity becomes `D(w,−1)=A(w,−1)`; the proved
   holomorphy of `A` gives holomorphy of the actual determinant through one.

## Lean certificate

Module: `RenormalizedIntersectionTheory/GaussMayerNegativeUnitCancellation.lean`.
Namespace: `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCancellation`.

- `branch_response`, `partial_telescope`, `remainder_response`, `perturbed_response`.
- `coefficientEvaluation_analysis`, `matrixOf_hilbertProjection`, `hilbert_response`.
- `det2_perturbed`, `perturbedDeterminant_negative_one`, `polePart_negative_one`.
- `sourceDeterminant_negative_one`, `differentiableOn_sourceDeterminant_negative_one`,
  `analyticAt_sourceDeterminant_negative_one`.

Direct production check passed without diagnostics. Thirteen transitive axiom
audits use only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import wired.

## Scope

This resolves one specific nonzero cancellation in the actual source
family. The generic rank-one update and geometric Fredholm consumers
already existed; the successor telescope and its source transport discharge
their inputs. No literature-priority claim is made.

The removable value and its possible vanishing order are not determined.
The parameter `λ=1`, primitive modular coding, Selberg/scattering comparison,
and off-critical resonance exclusion remain open. No RH conclusion follows.

The [finite successor shear](gauss-mayer-raw-negative-unit-determinants.md)
also proves convergence of the genuine raw finite-branch determinants at
`λ=−1`, despite divergence of the raw operators on `0<Re w<1`.
