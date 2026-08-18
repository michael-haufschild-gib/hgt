# G-CE coefficient-faithful affine boundary renormalization

- **ID:** g-ce-coefficient-faithful-affine-boundary-renormalization
- **Stage:** 3-formalized
- **Type:** exact source comparison / boundary rigidity
- **Route:** G-CE inside Route G / CCM
- **Status:** [LEAN-PROVED] [NOVELTY-PLAUSIBLE]
- **RH used:** no
- **Computation used:** no

## Audited frontier

[CORPUS] The pre-scalar affine producer retains a nonzero positive-Euler plus Gamma charge and a
marked two-order clock packet. At zero clock its odd commutator port is exactly zero, while its
joint readout is the completed division-free prime--polar--Gamma numerator.

[CORPUS] The clock-normalized true-complement defect is the squarefree overlap times the continued
anti-causal Ward response. On the zero-clock node the overlap is exactly one.

[CORPUS] Every canonical finite G-CE head contains the zero node. Its source-response entry there
is exactly the clock-normalized true-complement defect; a strictly cofinal source-depth schedule
transports this entry to

~~~text
d = continuedXiAntiCausalWardResponse (1/2).
~~~

[CORPUS] The exact positive singular-graph budget is `4 + |d|^2`; fixed budget four is available
exactly when `d=0`, equivalently RH. Scalar cancellation is RH or universal `-I` erasure.

[LITERATURE] Connes--Consani--Moscovici and Suzuki supply finite self-adjoint realizations and
spectral/characteristic-function architectures, but no source-specific zero-mode renormalization
identifying this prime--polar--Gamma affine readout with the escaped Ward coefficient. Their global
spectral/source convergence remains conjectural.

## Hostile conjecture loop

### C1 -- divide the zero-clock affine readout only by `sigma-1`

[FALSIFIED] This converges to the full completed Xi logarithmic trace, not the strict-right escaped
coefficient. It omits the non-right Wiener--Hopf record.

### C2 -- subtract a free scalar opposite copy

[FALSIFIED] This is the unique universal `-I` erasure. It pays one copy of `|d|^2` and transfers the
debt to a hidden port; it is not coefficient-faithful source cancellation.

### C3 -- recover the missing record from the positive-clock commutator

[FALSIFIED] The marked odd port vanishes strongly cofinally for every bounded clock and is exactly
zero at zero clock. It cannot retain the fixed radial column `d/(1+u)`.

### C4 -- canonical complementary boundary renormalization

[PAPER-PROVED] Let `sigma_j` be the canonical critical sequence and let `A(j,N)` be the actual
zero-clock affine packet formed from the moving normalized Mobius source. Put

~~~text
Z(j,N) = readout(A(j,N)) / (sigma_j - 1).
~~~

Because the full-Euler overlap is one at zero clock, pre-scalar factorization gives exactly

~~~text
Z(j,N) = completedPrimeArchTrace(centered(sigma_j)).                 (1)
~~~

Define the canonical renormalization at `w_j=sigma_j-1/2` by

~~~text
B(j,N) = -2 i Z(j,N)
         -2 i logDeriv(xiNonrightCanonicalProduct)(i w_j)
         + xiAntiCausalWardBoundarySelfSymbol.                      (2)
~~~

The Euler--Ward complementary-record identity turns `(1)--(2)` into

~~~text
B(j,N) = continuedXiAntiCausalWardResponse(w_j).                    (3)
~~~

At the base coordinate of every finite G-CE head, the Fisher score is zero and squarefree overlap
is one. Therefore, before any limit,

~~~text
B(j,N) = mobiusGammaXiCoupledErrorSourceResponse(j,N,base(N)).       (4)
~~~

Equation `(4)` is coefficient-faithful: affine charge, moving Mobius source, finite-head label,
and boundary response remain in one equality. It does not apply a scalar controller.

The correction in `(2)` is forced, not optional. Rearranging `(4)` gives the unconditional exact
difference law

~~~text
sourceResponse(j,N,base(N)) - (-2 i Z(j,N))
  = -2 i logDeriv(xiNonrightCanonicalProduct)(i w_j)
    + xiAntiCausalWardBoundarySelfSymbol.                            (5)
~~~

Thus any coefficient-faithful scalar renormalization must carry the genuine complementary divisor
record. A pure affine charge or commutator cannot manufacture it.

Along the existing source-native strictly cofinal finite self-adjoint schedule, `(4)` implies

~~~text
B(depth(N),N) -> d.                                                  (6)
~~~

Consequently

~~~text
B(depth(N),N) -> 0  iff  d=0  iff  RH.                               (7)
~~~

This excludes universal erasure: off RH the actual renormalized source coefficient survives.

## Scientific conclusion

The requested boundary comparison exists and is exact at every finite head, not merely in the
limit. It closes the source-provenance gap between the affine producer and transported G-CE
coefficient.

It does **not** prove RH. The comparison exposes why: coefficient faithfulness reconstructs the
radial Hardy representer with coefficient `d`, whose sharp positive cost is `|d|^2`. Hence the
renormalized finite positive completions converge to budget `4+|d|^2`, and reducing that budget to
four is equivalent to RH itself. Boundary renormalization closes the bridge but cannot remove the
graph leg.

## Lean certificate

Module:

~~~text
GaloisForLFunctions.RHTower.MobiusGammaXiPreScalarAffineBoundaryRenormalization
~~~

Lean proves:

1. actual moving zero-clock affine packet and normalized readout;
2. exact completed-trace normalization;
3. canonical complementary renormalization and exact laws `(3)--(5)`;
4. nonzero charge plus identically zero odd-port provenance at every finite stage;
5. source-native cofinal transport `(6)` and zero-limit/RH classification `(7)`;
6. fixed-four global wall positivity iff RH;
7. premise-free capstone
   `exists_mobiusGammaXiPreScalarAffineCoefficientFaithfulBoundaryRenormalization`.

Verification:

- `lake env lean GaloisForLFunctions/RHTower/MobiusGammaXiPreScalarAffineBoundaryRenormalization.lean` passed;
- targeted `lake build GaloisForLFunctions.RHTower.MobiusGammaXiPreScalarAffineBoundaryRenormalization` passed;
- axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`;
- no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration occurs in module;
- module is imported by `GaloisForLFunctions.RHTower` umbrella.
