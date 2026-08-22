# Lean formalization work packages

All 234 Stage-2 cards in this directory are assigned to one work package. A package groups cards by reusable Lean substrate and expected theorem ownership, not by paper-proof status. Stage-2 remains the source of record: package placement does not claim a complete proof, a complete Lean implementation, or an available mathlib API.

Before taking a card, audit its exact stated theorem and its reported Lean status. Reuse or extend a package-local foundation only after searching the current formal tree. Do not create a broad package umbrella until at least one dependency-closed theorem needs it.

| Package | Cards | Shared substrate | Likely Lean ownership |
|---|---:|---|---|
| [01 Bottcher complex dynamics](01-bottcher-complex-dynamics/README.md) | 6 | quadratic dynamics, monodromy, potential theory | new focused module; then HTGeometry if reusable |
| [02 Analytic DA and entire functions](02-analytic-da-entire-functions/README.md) | 22 | analytic identities, differential algebra, composition | HTGeometry |
| [03 HT translation and projective geometry](03-ht-translation-projective-geometry/README.md) | 27 | DA/HT interfaces, translation actions, projective finite data | HTGeometry |
| [04 RG, stochastic, and quantum fields](04-rg-stochastic-quantum-fields/README.md) | 23 | recurrences, Markov structure, finite spectral/probability cores | HTGeometry |
| [05 Algebraic geometry and cohomology](05-algebraic-geometry-cohomology/README.md) | 16 | finite algebra, cohomology, gluing, motive-style reductions | HTGeometry |
| [06 Integrable QFT and Yang--Baxter](06-integrable-qft-yang-baxter/README.md) | 9 | finite matrices, tensors, cocycles, scattering identities | HTGeometry |
| [07 Functional analysis and operator theory](07-functional-analysis-operator-theory/README.md) | 20 | Hilbert spaces, bounded operators, spectral and norm arguments | HilbertMetric or HTGeometry |
| [08 Sonin, semilocal, and co-Poisson](08-sonin-semilocal-copoisson/README.md) | 17 | Fourier/Mellin interfaces, cutoff spaces, real analysis | RHTower |
| [09 Mobius and prime sums](09-mobius-prime-sums/README.md) | 13 | finite arithmetic sums, divisor identities, asymptotic shells | RHTower |
| [10 Euler, Gamma, and completion](10-euler-gamma-completion/README.md) | 19 | Euler/Gamma algebra, completed transforms, residues | RHTower |
| [11 RH zero and divisor geometry](11-rh-zero-divisor-geometry/README.md) | 29 | critical-line predicates, divisor/zero bookkeeping, positivity | RHTower |
| [12 Prime, theta, and Fock incidence](12-prime-theta-fock-incidence/README.md) | 18 | finite prime data, theta/Fock finite models, incidence matrices | RHTower |
| [13 Constraint and carrier calculus](13-constraint-carrier-calculus/README.md) | 15 | finite constraint systems, carrier/charge interfaces, reflection | HTGeometry or RHTower |

Assign concurrent agents to separate packages. Within a package, land reusable finite/algebraic lemmas before card-specific analytic interfaces; this prevents duplicate definitions and keeps shared code reviewable.
