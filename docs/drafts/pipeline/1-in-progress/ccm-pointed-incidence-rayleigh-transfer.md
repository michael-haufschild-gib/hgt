# CCM pointed-incidence Rayleigh transfer

- **ID:** `ccm-pointed-incidence-rayleigh-transfer`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** Route B finite-Weil characteristic-determinant lane
- **Statement:** The actual radial-prolate CCM source has cofinal even-sector Rayleigh excess at most `O(lambda^(-1))` times the true restricted-Weil gap, and the corresponding true ground state is simple and even.

## Goal

Prove a source theorem which contains neither `RiemannHypothesis`, `Xi`, nor a zero-location
predicate. Let `A_lambda` be the true restricted Weil operator, `g_lambda` the normalized
radial-prolate source, `epsilon_0(lambda)` the true even ground energy, and
`Gap_lambda=epsilon_1(lambda)-epsilon_0(lambda)`. The target is

```text
(<A_lambda g_lambda,g_lambda>-epsilon_0(lambda))/Gap_lambda
  = O(lambda^(-1)),
```

together with simple-evenness of the ground state on one cofinal aperture sequence.

This is not a rephrasing of RH. It is a quantitative comparison of a specified source vector with
a specified self-adjoint operator. It has stronger independently checkable consequences: the true
ground state must inherit the constrained-prolate fixed-mode ratios, the `8/11` versus `8/13`
Fourier-parity separation, and the endpoint response scale.

## Gates

- [x] 0 → 1 in-progress: source-pure quantitative statement, downstream chain, and falsifiable finite-mode fingerprints isolated
- [ ] 1 → 2 fully-proven: prove the bilinear exterior-tail estimate and cofinal simple-evenness
- [ ] 2 → 3 formalized: formalize only after the true restricted Weil operator and source comparison exist in Lean
- [ ] 3 → 4 publication-ready: independent novelty and significance audit

## Backward implication chain

```text
actual von Mangoldt coefficients + archimedean completion
  -> pointed prime/source incidence tensor
  -> source-specific exterior-tail bilinear estimate
  -> Rayleigh excess / true even gap = O(lambda^(-1))
  -> projective ground-vector distance = O(lambda^(-1/2))
  -> growing Mellin convergence on every compact substrip
  -> locally uniform normalized finite Hermitian determinants -> XiC
  -> all XiC zeros are real
  -> RH.
```

The final two arrows are now formalized by
`riemannHypothesis_of_normalizedHermitianCharpoly_tendstoLocallyUniformly`. The Rayleigh-to-Mellin
arrows are proved on paper in the existing Route-B transfer cards. The first unresolved arrow is the
source-specific bilinear estimate, not an abstract determinant-convergence assumption.

## Paper-proof inputs

The stage-2 `new_scientific_knowledge` corpus contributes constraints and source data rather than a
hidden proof of the open arrow:

1. `constrained-prolate-two-mode-ground-state.md` supplies the canonical `h_0-h_4` source and the
   positive `8/11` surrogate floor.
2. `constrained-prolate-fixed-mode-spectral-ladder.md` supplies every fixed-depth Hermite contrast
   and the adjacent `lambda^8` separation, giving falsifiable fingerprints for true-Weil transfer.
3. `constrained-prolate-fourier-parity-floor-separation.md` supplies the positive/negative parity
   floors `8/11` and `8/13` and a quantitative parity margin.
4. `ccm-constrained-endpoint-euler-response-constant.md` calibrates the first formal endpoint
   component, but `ccm-prolate-endpoint-jet-resummation-law.md` proves that a fixed endpoint-jet
   expansion is not cofinally ordered at frequencies comparable to `lambda`. The actual source
   theorem must use the uniform radial-prolate exterior profile.
5. `semilocal-all-even-jacobi-prolate-residue-tower.md` confirms that the alternating even-mode
   residue structure persists at every fixed depth, but does not identify the true Weil form.
6. `semilocal-grading-deformation-unbounded.md` and
   `semilocal-prolate-core-disjointness.md` rule out bounded-perturbation and common-core shortcuts;
   the comparison must use a graph-domain, closed-form, or two-resolvent argument.
7. `finite-archimedean-gamma-product-boundary-law.md` proves that a finite commensurable Gamma
   completion contributes one upper projective valuation direction and cannot generate the
   infinite prime-frequency module. `ccm-radial-dilation-divisibility-carrier.md` identifies the
   exact independent carrier: shifted lower tails select divisible radial Fourier indices, finite
   Möbius inversion recovers every component, and the finite radial carrier has exact dimension
   `K` with phase rank at least `pi(K)`.
8. `critical-center-euler-unit-trace-hankel-instability.md`, the fixed-divisor freeness theorems,
   and the maximal-HT Bohr-boundary theorem rule out deriving the missing sign or divisor selector
   from compact-open germs, abstract HT, scalar symmetries, or finite passports.
9. `constrained-prolate-radial-leakage-divisibility-spectrum.md` proves the first actual uniform
   radial input: the constrained exterior leakage converges to
   `(8/(11*pi))dx/(x*sqrt(x^2-1))`, every fixed off-diagonal radial Gram entry is `o(d_1)`, and
   the diagonal divisibility spectrum is `(8/(11*pi*k))arcsin(1/k)`. The remaining source problem
   is simultaneous growing-index/von-Mangoldt uniformity, not fixed-index radial asymptotics.
10. `ccm-radial-prime-first-row-reduction.md` reduces that growing-index problem to two positive
    estimates. The `j,k>=2` sector needs an exact almost-orthogonality bound, while the only
    stationary sector needs uniform first-row vanishing. Fixed-index stationary phase and the
    explicit Weber kernel at `k` comparable to `c` both give the target scale
    `G_lambda(1,k)=O(d_1*c^(-1/2)k^(-2))`. Uniformly matching those regimes and transferring the
    result through the exact radial remainder are the present analytic gates.

The additive heat-aperture zero echo and the unrestricted Krein-index realization remain detectors
or no-go theorems. They cannot discharge this source comparison: echo disappearance and index zero
would each require an independent selector carrying essentially the missing global arithmetic
information.

## Attack

Work in the pointed incidence topology before taking the compact-open determinant quotient. Use
Dunster's uniform radial PSWF expansion across `1<x<infinity`, including its Bessel endpoint
regime, to estimate the exact radial Gram sums

```text
G_lambda(j,k)=inner(H_(lambda,j),H_(lambda,k)).
```

Retain the entire weighted dilation-autocorrelation vector, the von Mangoldt coefficients, the
archimedean logarithmic form, and the Poisson central correction in one closed-form remainder. A
fixed endpoint-jet truncation is not an admissible cofinal substitute. Seek a Schur-complement
lower bound

```text
L_lambda <= epsilon_0(lambda),
(<A_lambda g_lambda,g_lambda>-L_lambda)/Gap_lambda
  = O(lambda^(-1)).
```

This certified-lower-bound form avoids a strong-residual estimate and matches the exact quadratic
radical quotient. The parity-floor separation is the candidate mechanism for cofinal
simple-evenness. Any proof which first shows `epsilon_0(lambda)->0` instead belongs to the shorter
Weil spectral-floor branch and has already absorbed the full RH burden.

## Failure conditions

Retire or split the claim if any of the following occurs:

- the actual source loses the fixed-mode prolate ratios under the true Weil form;
- the parity margin changes sign cofinally;
- the exterior-tail estimate is available only in an unweighted scalar topology which forgets the
  prime/source incidence;
- the radial estimate controls only finitely many dilation coordinates or assumes tightness of the
  rescaled exterior mass without proving it;
- the proof extrapolates a fixed endpoint-jet asymptotic into the critical region
  `y` comparable to `lambda`;
- the comparison proves only ordinary `L2` convergence, not the growing Mellin rate;
- the proposed proof uses compact-open germ density, HT, finite Gamma phase rank, or a finite
  passport as the missing sign selector.

## Log

- 2026-07-11 — created by working backward from the formal Hermitian-determinant implication and
  auditing the stage-2 paper proofs; exact open source theorem isolated above the standard transfer
  chain.
- 2026-07-11 — replaced the nonuniform fixed-jet attack by the uniform radial-prolate
  dilation/divisibility Gram theorem; separated the one-direction Gamma boundary from the
  infinite arithmetic carrier.
