# Prime--archimedean reflection-positive quantum moments imply RH

- **ID:** `prime-arch-reflection-positive-quantum-moment-rh`
- **Stage:** 3-formalized
- **Type:** `[BRIDGE] [FORMALIZATION] [OPERATIONAL LEAN VALUE]`
- **Source:** Osterwalder--Schrader reflection positivity; the discrete
  `({\mathbb Z},{\mathbb N},-\mathrm{id})` reflection-positive/Hankel correspondence;
  `PrimeArchMomentMeasureRH.lean`; `TraceHankelSequenceCone.lean`.
- **Statement:** A real or complex Hilbert-space family with Gram values
  `inner (v i) (v j) = normalizedPrimeArchMoment (i+j)` makes every canonical
  prime--Gamma trace-Hankel test a squared norm and therefore implies RH. A bounded
  self-adjoint observable whose vacuum moments are the normalized prime--archimedean
  moments supplies such a Gram family automatically. If every finite real reflected packet is
  linearly independent, then every source Hankel determinant is strictly positive.

## Goal

Replace the measure-producing hypothesis in `PrimeArchMomentMeasureRH.lean` by two
operator-facing interfaces native to quantum physics and the Sonin code:

1. a static reflection-positive/GNS Gram orbit; and
2. a bounded self-adjoint observable with the exact vacuum value relation
   `inner omega ((A^n) omega) = normalizedPrimeArchMoment n`.

The weak interface discharges `PrimeArchSourceTraceHankelIntNonnegative` directly, without
constructing a representing measure, proving monomial integrability, or introducing a time
evolution. The strict interface replaces the measure route's infinite-support hypothesis by
finite linear independence of the reflected state packets. It therefore also feeds the strict
Hankel-determinant and Gram machinery.

## Literature bridge

Osterwalder and Schrader introduced reflection positivity as the positivity condition used to
reconstruct a Hilbert-space quantum theory from Euclidean data:
<https://doi.org/10.1007/BF01608978>. Adamo--Neeb--Schober identify the discrete symmetric
semigroup `({\mathbb Z},{\mathbb N},-\mathrm{id})` with reflection-positive operators and
positive Hankel representations:
<https://arxiv.org/abs/2105.08522>. The formal relation is the coefficient-level finite packet
used by that correspondence: the Hankel kernel `m_(i+j)` is a Hilbert Gram kernel, so a polynomial
test is the norm square of the corresponding state packet.

## Lean certificate

Reusable HTGeometry module:
`formal/GaloisForLFunctions/HTGeometry/ReflectionPositiveHankel.lean`.

Principal declarations:

- `reflectionPositiveStateVector` and `complexReflectionPositiveStateVector`;
- `momentFunctional_pow_two_eq_reflectionPositiveStateVector_normSq`;
- `momentFunctional_pow_two_eq_complexReflectionPositiveStateVector_normSq`;
- real and complex reflection-positive square-nonnegativity theorems;
- `momentHankelMatrix_posDef_of_reflectionPositiveGram`;
- `det_momentHankelMatrix_pos_of_reflectionPositiveGram`;
- `inner_selfAdjointObservableOrbit` and its real/complex moment consequences.

RHTower module:
`formal/GaloisForLFunctions/RHTower/PrimeArchReflectionPositiveHankelRH.lean`.

Principal declarations:

- real and complex Gram-to-`SequenceTraceHankelNonnegative` bridges;
- real and complex Gram-to-`PrimeArchSourceTraceHankelIntNonnegative` bridges;
- real and complex self-adjoint-observable-to-source-positivity bridges;
- `primeArchSourceMomentHankelDeterminantsPositive_of_reflectionPositiveGram`;
- `primeArchSourceMomentHankelDeterminantsPositive_of_selfAdjointObservableOrbit`;
- the corresponding weak and strict RH capstones.

Validation:

- both modules build in the project toolchain;
- both area umbrellas import the modules;
- the formal lint gate passes;
- the checked public theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Proof

For coefficients `c_i`, let `Psi_c = sum_i c_i v_i`. The Gram identity gives

`inner Psi_c Psi_c = sum_i sum_j c_i c_j m_(i+j)`.

The existing `momentFunctional_sq_eq_hankelForm` theorem identifies the right side with
`momentFunctional m (p^2)`. Hence every polynomial-square moment value is a norm square. For a
self-adjoint bounded observable `A`, symmetry of `A^i` and `A^i A^j = A^(i+j)` give

`inner (A^i omega) (A^j omega) = inner omega (A^(i+j) omega)`,

so its vacuum moments are a reflection-positive Gram orbit. The existing prime--Gamma
coefficient identity rewrites each source trace-Hankel test to this moment functional, and the
existing source positivity criterion closes to RH.

For a finite packet `v_0,...,v_(n-1)`, the source Hankel matrix is definitionally its real Gram
matrix. Linear independence makes that Gram matrix positive definite, so its determinant is
strictly positive. Applied to the Krylov packet `omega,A omega,...,A^(n-1) omega`, this is exactly
the absence of a nonzero polynomial annihilator below degree `n`.

## Open source obligation

The bridge does not construct the reflected family or the observable. The remaining RH-grade
input is the all-order source-specific value relation. The strict interface additionally asks for
finite linear independence of the orbit; it is useful to downstream strict Gram machinery but is
not needed for the weak trace-Hankel-to-RH capstone.

## Gates

- [x] 0 -> 1: source-pure static value relation and direct Lean consumer identified.
- [x] 1 -> 2: real, complex, weak, strict, and observable proofs are complete.
- [x] 2 -> 3: modules build, umbrella wiring is present, axioms are standard, and formal lint
  passes.
- [ ] 3 -> 4: infrastructure result; no preprint is claimed.
