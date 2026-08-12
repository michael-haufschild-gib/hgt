# CCM literature-to-Lean parity before frontier research

- **ID:** `ccm-literature-to-lean-parity`
- **Stage:** 1-in-progress
- **Type:** PRIMARY-LITERATURE COVERAGE / LEAN FRONTIER LEDGER
- **Started:** 2026-08-11
- **Scope:** whole Connes/CCM RH program: Route C1, CCM-FU, and Route O
- **Scientific status:** `[MECHANICAL INGESTION] [NOT NEW SCIENCE] [NOT AN RH PROOF]`

## Expanded operational goal

Treat Route C1 and Route O as one CCM program.  Close it only by a literal source theorem through
RH or a source-complete no-go/classification.  Before originating another CCM conjecture, make the
umbrella-reachable Lean corpus theorem-level complete for every unconditional primary-literature
result that lies ahead of it.  Only the residual after this parity audit is a scientific frontier.

## Acceptance rule

An item is `EXACT` only when umbrella-reachable Lean constructs the source-defined objects,
internalizes admissibility in the objects' types, proves every scientific hypothesis from those
definitions, and proves the paper's endpoint without proposition-valued premises, `sorry`, `admit`,
project axioms, opaque declarations, unsafe code, or computation.  Generic
operator infrastructure, an abstract surrogate, a conditional RH receiver, or an unwired file is
not exact coverage.  Numerical observations and convergence conjectures are recorded but never
formalized as theorems.

## Fixed primary-source ledger

| Source | Unconditional theorem relevant to CCM | Current Lean status | Required action |
|---|---|---|---|
| Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta function* | semilocal trace formula and quotient spectral realization | `PARTIAL`: rational adelic/Bruhat and trace-norm infrastructure exists; no theorem-level source audit yet | inventory exact numbered results against declarations |
| Connes--Consani, arXiv:1910.14368 | semilocal Fourier unitary; cutoff trace formula; projection/logarithmic-derivative sign criterion | `PARTIAL`: exact class-space pieces exist; source trace formula not identified end-to-end | formalize missing exact operator identities |
| Connes--Consani, arXiv:2006.13771 | quantized differential is infinitesimal of infinite order; Sonin compressed trace identity; archimedean Weil lower bound for support `[2^(-1/2),2^(1/2)]` with the paper's Fourier vanishing hypotheses | `PARTIAL-EXACT`: all source-normalized scaling, convolution, Sonin/Hankel, infinite-order, phase, Mellin, scattering, and geometric-kernel layers are umbrella-wired. The scaled kernel `lemsch7(i)`, geometric--spectral bridge, literal Proposition 7(iv) phase trace identity, exact trace cocycles, and an independent global finite-part archimedean Weil distribution with finite-aperture/tail split are now also exact. Missing theorem is the equality of the literal geometric tested trace/phase-rate functional with that finite-part Weil distribution for the paper's compact log test, followed by the support-limited inequality | formalize only this final trace-to-Weil identification and exact non-computational inequality; separately audit paper's numerical spectral bound |
| Connes--Consani, arXiv:2106.01715 | lower-semicontinuous restricted Weil form; spectral triples; exact zeta-cycle spectral theorem | `MISSING/PARTIAL`: many restricted-Weil and prolate pieces exist; no literal zeta-cycle theorem located | formalize exact circle periodization, orthogonal complement, and spectral characterization |
| Connes--Consani--Moscovici, arXiv:2310.18423 | semilocal Sonin Hilbert isomorphism; common de Branges image; Gamma-quarter Jacobi/metaplectic model; semilocal prolate operator | `PARTIAL`: Gamma density, moments, Jacobi recurrence, relative traces, and continuous Sonin pieces exist; exact Hilbert isomorphism not located | prove missing source-space isometries and identify every local surrogate |
| Connes--Consani--Moscovici, arXiv:2511.22755 | finite simple-even ground rank-one perturbation is self-adjoint in the Weil quotient; regularized determinant equals the ground Fourier transform; every transform zero is real | `CONDITIONAL SOURCE THEOREM`: literal finite matrix, unconditional ground shift, source/response completion, determinant lemma, and real-rooted completion already exist; paper does not discharge simplicity/evenness or convergence | do not add a hypothesis-packaging theorem; only an unconditional proof of the literal eta-channel assumptions would move parity |
| Connes--van Suijlekom, arXiv:2511.23257 | lower-bounded convolution ground-state Fourier real-zero theorem; continuous-kernel and finite-matrix variants | `PARTIAL`: finite paraorthogonal connector and zero-limit transfer exist; continuous theorem absent | formalize exact continuous theorem after finite CCM capstone |
| Connes, arXiv:2602.04022 | survey synthesis and finite CCM source statements | `AUDIT`: do not count restatements as new theorems | check only for genuinely stronger unconditional statements |

## First exact claim

Formalize the unconditional Connes--Consani archimedean compressed-trace theorem of
arXiv:2006.13771 on the paper's concrete test algebra, scaling representation, and Sonin
projection.  The final closed statement universally quantifies over the test function and proves
the source inequality from its intrinsic support and Fourier-vanishing conditions; it must not
take the inequality, a spectral bound, a positivity interface, or a numerical certificate as a
premise.  Required endpoints are:

1. multiplicative convolution, involution, and Fourier character identities on exact smooth
   compactly supported tests;
2. the unitary scaling representation on even `L2(Real)` and its integrated operator `rho(g)`;
3. the concrete physical and Fourier cut projections and their Sonin intersection projection;
4. trace-classness and positivity of `rho(g) S rho(g)^*`;
5. the exact trace-remainder identity with the archimedean Weil distribution;
6. the source inequality, without importing the paper's floating-point spectral estimates.

The published proof's bound `gamma approximately 2.94355` is numerically sourced.  Under the
no-computation rule it is not an admissible premise.  The formal proof must replace that step by an
exact analytic estimate, or record a genuine rigor gap in the source theorem and formalize the
strongest unconditional trace identity preceding it.

## Dependency order

1. Audit the source proof's non-computational lemmas and isolate the exact missing spectral bound.
2. Reuse the corpus's continuous `L2`, Fourier, projection, and trace-ideal infrastructure.
3. Formalize source test algebra and integrated scaling representation.  Integrated L1 scaling,
   contractivity, Haar involution, and adjoint law are complete in
   `CCMArchimedeanIntegratedScaling.lean` and `CCMArchimedeanScalingStar.lean`.
   `CCMArchimedeanConvolutionRepresentation.lean` proves the intrinsic Haar convolution is
   `L1`, expands the two Bochner integrals, and proves `rho(g*h)=rho(g)rho(h)` by the
   measure-preserving shear, with no representation premise.
   The literal half-line projection `P`, Hardy projection `F P F⁻¹`, involution
   `H = 2 F P F⁻¹ - 1`, intrinsic Schwartz multiplier, and exact cross-Hardy-block decomposition
   are complete in `CCMArchimedeanQuantizedCalculus.lean`.  In
   `CCMArchimedeanHankelTraceClass.lean`, both explicit half-line factors are unconditionally
   Hilbert--Schmidt, their composite is Schatten one, the Volterra factor has its exact integral
   representative, and the factor kernels integrate exactly to the paper's `g(x+y)` Hankel
   kernel.  `CCMArchimedeanHankelKernel.lean` and
   `CCMArchimedeanFourierCrossBlock.lean` identify that operator with the literal reflected Fourier
   crossblock.  `CCMArchimedeanInfiniteOrder.lean` implements the paper's smooth cutoff, proves
   all oscillator-power kernel operators Hilbert--Schmidt, derives rapid Hermite approximation
   numbers, identifies the positive compression with the actual Hankel operator, and transports
   rapid decay through reflection, adjoint, Fourier conjugation, addition, and scalar
   multiplication to the literal quantized differential.  `CCMArchimedeanPhaseTemperate.lean`
   proves from Gamma/digamma asymptotics that the paper-convention phase
   `u_infinity(t)=conj(zetaChi(1/2+it))=exp(2 i theta(t))` has temperate growth, so multiplication
   by `u_infinity` sends every Schwartz Mellin symbol back to Schwartz and its quantized
   differential is an infinitesimal of infinite order. `CCMArchimedeanPhaseOperatorProduct.lean`
   proves the exact source Leibniz identity and makes the tested logarithmic phase differential
   infinite-order, Schatten one, and trace class. `CCMArchimedeanMellinTransport.lean` then proves
   for every intrinsic logarithmic `L¹` kernel that integrated physical scaling is exactly its
   normalized Fourier--Mellin multiplier; for Schwartz log kernels it transports the preceding
   result back to the literal geometric product and proves that product trace class.
   `CCMArchimedeanFourierMellinScattering.lean` proves the exact source identity
   `archimedeanMellinUnitary (evenFourierTransform f) =
   l2Reflection (ccmArchimedeanScatteringL2Multiplier (archimedeanMellinUnitary f))` for every
   even `L²` vector. Critical-line weighted integrability, Gamma normalization, and density of the
   even-Schwartz core are discharged internally; no intertwining premise remains.
   `CCMArchimedeanGeometricScatteringKernel.lean` and
   `CCMArchimedeanGeometricCommutatorKernel.lean` then prove the literal kernels in Lemma
   `sch3(i)` and `(ii)` on the actual multiplicative-Haar carrier.  The commutator proof extends
   the kernel identity to the even `L¹∩L²` core because the sharp projection destroys Schwartz
   regularity. `CCMArchimedeanGeometricCompositeKernel.lean` proves `sch3(iii)` as the exact
   iterated operator pairing. It also proves that the source's displayed pointwise composition
   cannot be a Bochner integral: at `ν=μ=1` its `y>1` integrand is `-4 cos²(2πy)`, its truncated
   positive mass tends to `+∞`, and it is not Lebesgue integrable. Thus subsequent use must remain
   distributional; Lean's totalized integral is not an admissible pointwise definition.
4. Exact Sonin projection, compressed positive trace, scaled geometric kernel, geometric--spectral
   bridge, tested phase trace, and finite-part Weil distribution are complete.
5. Prove the final equality between the tested geometric trace/phase-rate functional and
   `ccmArchimedeanWeilSharpDistribution`, then its finite-aperture/tail remainder identity.
6. Prove an exact analytic replacement for the numerical spectral step, or classify the source
   endpoint as not presently unconditional at published proof level.
7. Wire every completed exact module into `RHTower.lean`; run file Lean, targeted module build,
   lint, and axiom audit.
8. Continue with arXiv:2310.18423 and arXiv:2106.01715.  Revisit arXiv:2511.22755 only if its
   simple-even eta-channel hypotheses are discharged unconditionally.

## Gates

- [x] Existing corpus and failed-route audit checked before formalization.
- [x] Exact paper hypotheses and theorem text recovered from primary TeX.
- [x] Numerical convergence and experimental claims excluded.
- [x] Conditional arXiv:2511.22755 hypothesis packaging rejected as non-progress.
- [x] Source-normalized integrated scaling representation exact and umbrella-reachable.
- [x] Exact intrinsic Haar convolution representation law exact and umbrella-reachable.
- [x] Archimedean compressed bounded-operator positivity exact and umbrella-reachable.
- [x] Positive-quadrant Hankel kernel has an unconditional explicit Schatten-one factorization.
- [x] Literal Fourier cross block equals the factorized Hankel operator.
- [x] Quantized differential is infinitesimal of infinite order (not only trace class).
- [x] Literal archimedean phase is an unconditional Schwartz multiplier at every derivative order.
- [x] Exact Mellin diagonalization of intrinsic `L¹` scaling and literal geometric phase product trace-classness.
- [x] Exact Connes--Consani Fourier--Mellin scattering intertwining on the full even `L²` carrier.
- [x] Archimedean tested operator trace-class, exact trace cocycles, and phase trace identity.
- [x] Scaled geometric kernel and independent finite-part Weil distribution exact.
- [ ] Literal tested trace functional equals the finite-part Weil distribution.
- [ ] Support-limited lower bound without numerical spectral input.
- [ ] Semilocal Sonin/de Branges source isomorphisms exact and umbrella-reachable.
- [ ] Zeta-cycle spectral theorem exact and umbrella-reachable.
- [ ] Continuous Connes--van Suijlekom theorem exact and umbrella-reachable.
- [ ] Joint C1/O frontier recomputed only after parity closure.

## 2026-08-12 literature-ingestion audit: `quantsmooth`

`[MECHANICAL INGESTION] [NOT NEW SCIENCE]` The full published infinite-order conclusion is now
`RHTower.ccmQuantizedDifferential_isInfinitesimalOfInfiniteOrder` in
`CCMArchimedeanInfiniteOrder.lean`.  Its endpoint universally quantifies over the intrinsic
Schwartz symbol and has no proposition-valued analytic premise.  The proof does not infer rapid
decay from trace class: it constructs the source cutoff kernel, proves every oscillator-power
synthesis operator Hilbert--Schmidt, derives explicit approximation-number decay through the
complete Hermite basis, and proves the cutoff compression equals the already identified literal
Hankel block before transporting the result to `[H,M_f]`.

Audit evidence: file Lean passed; targeted build
`GaloisForLFunctions.RHTower.CCMArchimedeanInfiniteOrder` passed; formal lint passed; `#print
axioms` for both the compression equality and final theorem reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## 2026-08-12 literature-ingestion audit: Proposition 7(iv) analytic phase input

`[MECHANICAL INGESTION] [NOT NEW SCIENCE] [NOT THE TRACE FORMULA]` The source proof of Proposition
7(iv) uses that `hat f * u_infinity` is Schwartz.  That claim is now unconditional in
`CCMArchimedeanPhaseTemperate.lean`; it is not represented by an assumed temperate multiplier.
The module proves:

1. every positive-real-part vertical digamma restriction has logarithmic zeroth growth and
   polynomially bounded derivatives of every order, globally in both height directions;
2. the exact normalized-Gamma phase ODE transfers those bounds through universal Bell
   polynomials, giving `RHTower.gammaHardyPhase_hasTemperateGrowth`;
3. squaring and conjugating identifies the literal source convention
   `u_infinity(t)=conj(zetaChi(linePt t))` and gives
   `RHTower.ccmArchimedeanScatteringPhase_hasTemperateGrowth`;
4. `RHTower.ccmArchimedeanScatteringPhaseMul` is therefore a genuine Schwartz function for every
   Schwartz input, and its quantized differential satisfies the stronger infinite-order endpoint
   `RHTower.ccmArchimedeanScatteringPhase_quantizedDifferential_isInfinitesimalOfInfiniteOrder`.

The same ingestion pass closes the exact integrated representation product in
`CCMArchimedeanConvolutionRepresentation.lean`:
`rho(g*h)=rho(g)rho(h)` and `rho(g*g_star)=rho(g)rho(g)^*`.  Fubini integrability and the Haar shear
are proved internally.

**Frontier moved, but the archimedean inequality is not yet closed.** The analytic regularity, literal
trace-class assertion, and Fourier--Mellin phase intertwining are no longer gaps.
`CCMArchimedeanPhaseOperatorProduct.lean` proves the exact source operator identity, while
`CCMArchimedeanMellinTransport.lean` proves exact Mellin diagonalization of `rho(f)` and
trace-classness of the literal geometric product

~~~
rho(f) * (1/2) * (u_infinity^* d u_infinity)^g,
~~~

for every Schwartz logarithmic source, hence in particular for the paper's compactly supported
smooth tests. `CCMArchimedeanFourierMellinScattering.lean` now proves, for every even `L²` vector,
the exact source relation `F_eR^w = I ∘ u_infinity^g`; its proof derives critical-line
integrability and the exact Gamma ratio on a dense even-Schwartz core and extends by continuity.
The literal geometric kernels in Lemma `sch3(i)--(iii)` are now closed. Part `(iii)` is necessarily
an operator/distributional kernel identity: the new diagonal divergence theorem rules out the
naive Bochner reading of the paper's composition integral. Subsequent committed modules close the
scaled kernel, its geometric--spectral conjugacy, the tested phase trace identity, exact trace
cocycles, and the independent finite-part Weil distribution with restricted/tail decomposition.
The exact missing source content is now one comparison theorem: identify the literal geometric
tested trace/phase-rate functional with `ccmArchimedeanWeilSharpDistribution` on the paper's
compact logarithmic test. Only then derive the support-limited inequality. Repackaging
`quantsmooth`, phase regularity, Mellin transport, scattering, kernels, or trace class again would
be rediscovery.

Audit evidence: all three geometric-kernel files pass `lake env lean`; targeted build
`GaloisForLFunctions.RHTower.CCMArchimedeanGeometricCompositeKernel` passes; and `RHTower.lean`
elaborates with all modules umbrella-wired. `#print axioms` for the scattering kernel,
sharp-commutator kernel, composite distributional pairing, and diagonal nonintegrability endpoint
reports only `propext`, `Classical.choice`, and `Quot.sound`. Global formal lint is presently blocked by
unrelated dirty-tree modules that are not umbrella-wired; the new CCM module is not in the
reported unreachable set.
