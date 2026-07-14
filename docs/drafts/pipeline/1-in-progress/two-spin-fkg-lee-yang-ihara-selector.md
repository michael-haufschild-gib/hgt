# Two-spin FKG defect as the Lee--Yang and Ihara selector

- **ID:** `two-spin-fkg-lee-yang-ihara-selector`
- **Stage:** 1-in-progress
- **Type:** `[BRIDGE] [FORMALIZATION TARGET]`
- **Lean targets:** `formal/GaloisForLFunctions/RHTower/TwoSpinFKGLeeYangBridge.lean`,
  `formal/GaloisForLFunctions/RHTower.lean`
- **Consumers:** `LeeYangQuadraticBlock`, `IharaBlockSelector`,
  `EulerReciprocalLeeYangNoGo`, `PrimeEulerFerromagneticInteraction`, and the low-face test in
  `prime-source-ferromagnetic-ising-lee-yang-limit-rh`

## Claim

For the normalized zero-field two-spin weight table

```text
W_c = [[1,c],[c,1]],
```

the FKG/log-supermodular determinant is

```text
Delta_FKG(c) = det(W_c) = 1-c^2.
```

The same scalar is exactly the selector for both existing finite zero-location interfaces:

```text
Delta_FKG(c) >= 0
  <-> every zero of 1+2cz+z^2 lies on |z|=1
  <-> blockSpectralBound 1 (-2c).
```

For the prime interaction `c_p=exp(-log(p)/2)`, the determinant is strictly positive.  For the
reciprocal Euler coefficient `c(a)=(a+a^(-1))/2`, it is

```text
Delta_FKG(c(a)) = -(a^2-1)^2/(4a^2),
```

so a positive contracting Euler weight lies strictly outside the FKG chamber.  This converts the
active inverse-Ising problem's first low face into the same scalar hypothesis already consumed by
the Lee--Yang and Ihara theorem families.

## Corpus value

1. A source packet can discharge a circle-localization hypothesis by proving one determinant
   inequality rather than reconstructing a coupling or re-running the root argument.
2. The existing Lee--Yang and Ihara selectors become directly interoperable.
3. The prime square-root interaction is certified as an interior ferromagnetic point, while raw
   reciprocal Euler pairing receives an exact signed obstruction rather than only an off-circle
   conclusion.

## Verification gates

- [ ] theorem file compiles in the repository toolchain
- [ ] prime and reciprocal Euler consumers compile
- [ ] public umbrella exports the bridge
- [ ] `#print axioms` reports only accepted foundational axioms
- [ ] formal lint and generated-index checks pass

## Primary physics sources

- T. D. Lee and C. N. Yang, *Statistical Theory of Equations of State and Phase Transitions. II.
  Lattice Gas and Ising Model*, Physical Review 87 (1952), 410--419,
  <https://doi.org/10.1103/PhysRev.87.410>.
- R. B. Griffiths, *Correlations in Ising Ferromagnets. I*, Journal of Mathematical Physics 8
  (1967), 478--483, <https://doi.org/10.1063/1.1705219>.
- C. M. Fortuin, P. W. Kasteleyn, and J. Ginibre, *Correlation Inequalities on Some Partially
  Ordered Sets*, Communications in Mathematical Physics 22 (1971), 89--103,
  <https://doi.org/10.1007/BF01651330>.

