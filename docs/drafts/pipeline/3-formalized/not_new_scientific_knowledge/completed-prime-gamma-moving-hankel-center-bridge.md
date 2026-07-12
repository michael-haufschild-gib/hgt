# Completed prime--Gamma moving Hankel center bridge

- **ID:** `completed-prime-gamma-moving-hankel-center-bridge`
- **Stage:** 3-formalized
- **Type:** `[BRIDGE]`
- **Scientific status:** `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean file:** `formal/GaloisForLFunctions/RHTower/CompletedPrimeGammaMovingHankel.lean`

## Statement

For a complex base point `sigma`, define the translated completed relative trace

\[
T_\sigma(z)=i\left(
  \frac{\xi'}\xi(\sigma+iz)-\frac{\xi'}\xi(\sigma)
\right)
\]

and its normalized moment germ `G_sigma(z)=-T_sigma(z)/z`, with analytic divided-difference value
at zero.  Let

\[
H_n(\sigma)_{ij}
=\operatorname{analyticTraceMoments}(G_\sigma,i+j).
\]

Then

\[
H_n(1/2)=\texttt{primeArchSourceMomentHankelMatrix }n
\]

entrywise, and their leading determinants are equal.

## Formal declarations

- `logDeriv_xi_one_half`;
- `completedMovingRelativeTrace`;
- `completedMovingMomentGerm`;
- `completedMovingHankelMatrix`;
- `completedMovingHankelDet`;
- `completedMovingRelativeTrace_one_half`;
- `normalizedTraceMomentGerm_eventuallyEq_of_eventuallyEq`;
- `completedMovingMomentGerm_one_half_eventuallyEq`;
- `completedMovingHankelMatrix_one_half`;
- `completedMovingHankelDet_one_half`.
- `completedCenteredCoordinate`;
- `primeArchSourceRelativeTrace_completedCenteredCoordinate`;
- `completedMovingRelativeTrace_eq_primeArchSource_value_sub`;
- `primeArchSourceValueDifference`;
- `primeArchSourceValueMomentGerm`;
- `primeArchSourceValueHankelMatrix`;
- `completedMovingHankelMatrix_eq_primeArchSourceValueHankelMatrix`.
- `completedMovingRelativeTrace_eq_arch_sub_prime_valueDifferences`.

## Proof

The functional equation makes `logDeriv xi` anti-invariant under `s -> 1-s`, so it vanishes at
`s=1/2`.  The affine logarithmic-derivative identity then gives

\[
T_{1/2}(z)=\operatorname{logDeriv}\Xi_C(z).
\]

The existing continued prime--Gamma trace equals this Xi logarithmic derivative as a germ at zero.
Normalized divided difference preserves germ equality, as do all iterated derivatives at the base
point.  Therefore every analytic trace moment, matrix entry, and finite determinant agrees.

On `Re s>1`, the moving family has the stronger two-value description

\[
T_s(z)=P(w_s+z)-P(w_s),
\qquad w_s=-i(s-1/2),
\]

where `P=primeArchSourceRelativeTrace`.  This is proved first pointwise and then as an equality of
analytic germs.  Thus every moving Hankel matrix in the Euler half-plane is computed solely from
translated values of the one fixed source function.

Expanding those two values gives the channel-resolved constraint

\[
T_s(z)=i\left(
  [A(s+iz)-A(s)]-[E(s+iz)-E(s)]
\right),
\]

where `A=logDeriv archFactor` and
`E(s)=sum Lambda(n)n^(-s)`.  This retains the unsquared infinite prime carrier and the
archimedean/boundary correction separately.

## Top-down consequence

The far-right determinant route now has one fixed source-defined family rather than two matrices
joined only by analogy:

```text
far-right positivity of completedMovingHankelDet n                         [PAPER]
  + source-controlled zero winding from the far-right base point to 1/2    [OPEN CORE]
  -> positivity of primeArchSourceMomentHankelMatrix n for every n          [Lean]
  -> RH.                                                                     [Lean]
```

The bridge does not assert the winding hypothesis and therefore does not redress RH.

The moving family is not an auxiliary flow: it is the normalized two-point constraint of the
prime--Gamma source under translation.

## Scientific status

This is affine chain rule, functional-equation symmetry, and equality of analytic germs packaged
for the exact source determinant family.  It is architectural rather than new scientific
knowledge.

## Gates

- [x] source-defined moving family
- [x] exact center identity
- [x] unconditional Lean proof
- [x] no placeholders or project axioms
- [x] imported by the RHTower umbrella
