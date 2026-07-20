# RH SOTA literature-to-Lean wall through 2026

- **ID:** `rh-sota-literature-lean-wall-2026`
- **Stage:** 1-in-progress
- **Type:** PRIMARY-LITERATURE COVERAGE / LEAN FRONTIER LEDGER
- **Audit date:** 2026-07-20
- **Scope:** Riemann zeta and live RH routes; primary sources through the audit date
- **Scientific status:** `[MECHANICAL INGESTION] [NOT AN RH PROOF] [NO NUMERICAL EVIDENCE]`
- **Typed ledger:** `GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026`

## Acceptance rule

A source enters the mathematical frontier only through an exact unconditional theorem.  A
criterion equivalent to RH, an implication assuming a closure/convergence/localisation statement,
a theorem assuming RH or simple zeros, a finite computation, and a claimed proof without a
completed proof audit are recorded separately.  None is promoted to a theorem claiming RH.

“Formalized” below means that the named declaration represents the source theorem or its exact
logical connector without `sorry`, `admit`, project axioms, opaque declarations, unsafe code, or
numerical certification.  Generic infrastructure is not called a formalization of a paper's
concrete operator unless the source-defined objects have also been constructed.

## Live spectral and positivity routes

| Route and primary source | Exact unconditional endpoint | Lean coverage | Current wall |
|---|---|---|---|
| Connes--van Suijlekom, [Quadratic Forms, Real Zeros and Echoes of the Spectral Action](https://arxiv.org/abs/2511.23257); Connes, [The Riemann Hypothesis: Past, Present and a Letter Through Time](https://arxiv.org/abs/2602.04022) | A lower-bounded self-adjoint convolution operator with an isolated simple lowest eigenvalue and even eigenfunction has a ground-state Fourier transform with only real zeros.  The finite Toeplitz/paraorthogonal mechanism is unconditional. | `finiteOPUCParaorthogonal_lineCayley_root_im_eq_zero`; `riemannHypothesis_of_XiC_locally_uniform_real_zero_approximants`; typed wall `ConnesXiGroundStateLimitWall`. | Prove simplicity/evenness for the actual Weil ground state and locally uniform convergence of the actual transforms to `XiC`. |
| Connes--Consani--Moscovici, [Zeta Spectral Triples](https://arxiv.org/abs/2511.22755) | Finite-prime rank-one perturbations are self-adjoint; the reported spectral/determinant agreement is numerical. | The real-zero limit consumer is formalized; constrained-prolate and determinant infrastructure is present.  The paper's concrete finite operator family is not represented end-to-end. | Rigorous operator/ground-state or normalized determinant convergence to Xi. |
| Hedenmalm, [Spectral interpretation of Riemann zeta zeros](https://arxiv.org/abs/2606.17494) | The explicit theta boundary problem has a nontrivial solution exactly at a Xi zero; a positive inner product making the operator pair self-adjoint would force spectral parameters real. | `XiHedenmalmBoundaryValueProblem`: explicit solution, equation, endpoint limits, uniqueness, and `existsUnique_xiHedenmalmNormalizedBoundaryValueProblem_iff`.  Complete Weil/Hedenmalm positivity wall: `HedenmalmXiPositiveFormWall` and `hedenmalmXiPositiveFormWall_iff_riemannHypothesis`. | Construct the positive source-derived Hilbert form/self-adjoint pair; the boundary-value equivalence alone does not imply reality. |
| Suzuki, [Weil's quadratic form via the screw function](https://arxiv.org/abs/2606.09096) | Friedrichs realization; continuous lowest eigenvalue; small-aperture positive simple even ground state; a deficiency-`(1,1)` derivative operator whose self-adjoint extensions have entire characteristic functions `W(a,theta;z)` with only real zeros. | Generic symmetric-eigenvalue reality exists.  `suzukiXiCharacteristicTarget`, `SuzukiXiCharacteristicLimitWall`, and `suzukiXiCharacteristicLimitWall_implies_riemannHypothesis` formalize Corollary 6's exact zero-transfer endpoint. | Construct Suzuki's screw function, form domain, Friedrichs extension, deficiency spaces, and actual `W` in Lean; prove the conjectural locally uniform normalized limit to `z^2 xi/xi'`. |
| Connes--Consani--Moscovici constrained-prolate branch | Exact secular vector and finite/infinite constrained spectral algebra. | `ConstrainedProlateOperator`, `ConstrainedProlateBesselBound`, `ConstrainedProlateFullDistanceCCM`, especially `ccm_tendsto_min_norm_lp_normalize_sub_twoModeSeed`. | The concrete first two prolate-to-Hermite coordinate limits; no declaration claims them. |
| Weil positivity / Guinand--Weil | Complete multiplicity-aware Weil positivity is equivalent to RH. | `riemannHypothesis_iff_xiWeilPolarization_nonneg`; complete sharp prime--Gamma identity in `XiGuinandWeilRectangularFullFormula`. | Prove source positivity on the complete divisor test domain, not merely a finite or Cauchy core. |
| Groskin, [A finite Guinand-Weil dictionary and archimedean tail order](https://arxiv.org/abs/2607.02828) | Exact finite Galerkin zero-sum dictionary and analytic archimedean tail ordering; the paper also reports computations. | The project has a stronger cutoff-free sharp rectangular prime--Gamma identity: `xiWeilPolarization_rectangular_eq_prime_add_arch`, `rectangularCorrectedXiWeilValue_eq_primePolarSource`. | Finite-cutoff positivity does not establish full Weil positivity without a certified analytic passage; numerical rows are excluded. |

## Li, approximation, and equivalent-criterion routes

| Route and primary source | Exact endpoint | Lean coverage | Current wall |
|---|---|---|---|
| Li--Keiper / Bombieri--Lagarias | Nonnegativity of every canonical Li coefficient is equivalent to RH. | `wCoordinate_normSq_eq_one_iff`; pointwise transform `li_secular_pointwise`; finite packet transforms `finiteLiCoefficient_eq_secularMoments` and `finiteSecularMoment_eq_liCoefficients`. | Canonical infinite multiplicity-sensitive summation/logarithmic-derivative definition, convergence of the transforms, and the global positivity equivalence are not yet formalized. |
| Manzur--Noor--Quintero, [A Hardy space approximation supporting zero-free half-planes](https://arxiv.org/abs/2606.16097) | Membership of `1/s` in the closed span of the zeta generators in `H^2(C_alpha)` forces zeta to be zero-free in `C_alpha`; the rest is numerical investigation. | `continuousLinearMap_eq_zero_on_closedSpan`, `not_mem_closedSpan_of_continuous_evaluation`, `exists_generator_evaluation_ne_zero_of_mem_closedSpan`. | Construct the concrete half-plane Hardy carrier, bounded evaluations, and the actual `E,G_k`; prove the closure statement rather than estimate it numerically. |
| Alvarez Cruz--Alvarez Gutierrez, [A Colombeau--Beurling criterion](https://arxiv.org/abs/2606.22562) | A specific moderate, uniformly `L^2`-bounded damped Baez--Duarte net is associated with `-1_(0,1)` iff RH. | The common closed-span evaluation obstruction is formalized; concrete Colombeau algebras/nets are absent. | Formalize moderation, association, uniform `L^2` control, and both damping constructions.  This remains an equivalent criterion, not a discharged condition. |
| Gonzalez--Negrin, [A new equivalence via the Salem integral equation](https://arxiv.org/abs/2604.15396) | A Mellin mode `t^(i gamma)` solves the Salem equation exactly when the corresponding eta/zeta value vanishes; excluding those modes off the critical line is equivalent to RH. | Mellin/Dirichlet infrastructure exists, but the exact Fermi-kernel integral identity and criterion are not represented. | Formalize the Mellin integral identity and its nonvanishing factors.  The resulting statement is a criterion only. |
| Liflandsky, [Discrete Laplace transform of the Mobius function](https://arxiv.org/abs/2607.09797) | The stated decay bound implies RH unconditionally; the explicit zero formula assumes all zeros simple and the converse needs extra hypotheses. | Mobius and Xi transform infrastructure exists, but this discrete Laplace transform and one-way criterion are not represented. | Formalize the transform/one-way Tauberian implication without importing the paper's simple-zero hypothesis as a fact. |
| Baez--Duarte / Nyman--Beurling | Closure/cyclicity criterion equivalent to RH. | Finite Mobius/Schur and Hilbert closure infrastructure exists; no exact global Baez--Duarte equivalence declaration was found. | Concrete `L^2(0,1)` fractional-part generators and the global closure equivalence. |

## Diagnostic, conditional, computational, or background work

These sources are kept in the ledger but do not move an RH proof wall.

| Source | Classification and exact reason |
|---|---|
| Moriya, [Gaussian--Perron prime-side defect](https://arxiv.org/abs/2607.04316) | Exact zero-side formula and selected-zero profile are unconditional.  Full localisation assumes explicit damping/pole/contour hypotheses; the asymptotic profile near zeros assumes RH and a simple zero.  Diagnostic, not a proof endpoint. |
| Covei, [Spectral Riccati--Gamma concavity](https://arxiv.org/abs/2606.24924) | Unconditional no-go for naive two-sided vertical concavity and finite cancellation results; RH conclusion explicitly conditional on localisation hypotheses. |
| Michalowski, [Polya frequency order of the de Bruijn--Newman kernel](https://arxiv.org/abs/2602.20313) | Toeplitz reduction and coefficient decomposition are analytic/algebraic; PF5 failure and threshold values are interval-arithmetic computations.  The global PF4 question remains open.  Computational claims excluded by task scope. |
| Freedman, [Finite-core Volterra reductions for a Weyl-positive Riemann phase kernel](https://arxiv.org/abs/2606.29555) | Several finite-core routes are obstructed; the target Weyl positivity is supported by numerical tests and remains open. |
| Bagarello--Kuzel, [On the Berry--Keating Operator](https://arxiv.org/abs/2606.24405) | Review and complementary Hilbert/distributional viewpoints; no self-adjoint operator with exactly the zeta-zero spectrum is proved. |
| Connes--Consani, [Jacobian of compactified Spec Z](https://arxiv.org/abs/2602.15941) and [Absolute Geometry of Spec Z](https://arxiv.org/abs/2606.06604) | Geometric foundations for adelic/scaling-site programs; no purity or RH theorem is claimed. |
| Goldston--Suriajaya, [Zeta zeros in a narrow vertical box](https://arxiv.org/abs/2603.28104) | Conditional narrow-box result yielding asymptotically at least two-thirds simple critical-line zeros; it assumes the required zero localisation. |
| 2026 quantum/Hilbert--Polya and Berry--Keating overviews | Background only unless they construct a self-adjoint operator and prove the exact spectral identification. |
| `arXiv:2607.04338` claimed proof | Not accepted as SOTA without an independent line-by-line proof audit.  No claim is imported into Lean. |

## Established older walls retained because no 2026 source closes them

- **de Bruijn--Newman:** Rodgers--Tao prove `Lambda >= 0`; RH is the opposite endpoint
  `Lambda <= 0`.  Computational upper bounds are excluded.  The project has Xi heat/deformation
  infrastructure but no full Newman-constant construction and theorem.
- **Jensen polynomials / Laguerre--Polya:** asymptotic hyperbolicity of each fixed degree does not
  give all degrees at once.  `xi_laguerrePolya_of_rh` and the first Laguerre detector are
  formalized; the converse/global Jensen chain is not.
- **Classical analytic number theory:** zero-free regions, critical-line proportions, zero-density
  estimates, large values, and gap statistics are unconditional information about zeros but do
  not currently cofinalize to all zeros on the line.  Conditional consequences are not treated as
  proof routes.

## Completion gates

- [x] Search live Lean source, generated API, formalized cards, and failed-route cards first.
- [x] Audit 2026 arXiv records and source text for the live spectral/criterion papers.
- [x] Separate unconditional theorems, equivalent criteria, conditional statements, and
  computations.
- [x] Formalize Hedenmalm's normalized explicit boundary-value theorem.
- [x] Formalize the finite Caratheodory--Fejer/Cayley reality connector.
- [x] Formalize the Connes and Suzuki locally-uniform zero-transfer walls as named propositions.
- [x] Formalize the finite Li/secular transforms.
- [x] Formalize the generic Hardy closed-span zero obstruction.
- [ ] Formalize Suzuki's concrete screw-function Hilbert space, unbounded operators, and `W`.
- [ ] Formalize the half-plane Hardy and Colombeau carriers and concrete generators.
- [ ] Formalize the full analytic Li criterion.
- [ ] Formalize the Salem integral and discrete Mobius-Laplace one-way criteria.
- [ ] Axiom audit, lint, generated index, and final module builds.
- [ ] Move to stage 3 only when every claimed formalized row is compiler- and axiom-audited; leave
  source-realization gaps explicitly open.
