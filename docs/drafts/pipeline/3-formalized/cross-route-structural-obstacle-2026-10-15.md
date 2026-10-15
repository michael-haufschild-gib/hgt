# Finite Meyer spectral source synthesis with one common Xi boundary

Status: FORMALIZED. All four theorem modules and the final axiom audit pass. Repository-wide lint reports only unrelated concurrent modules, detailed below.

## Contract

Find an unconditional structural theorem combining multiple existing RH-route frontiers.
An improved estimate, RH equivalence, conditional receiver, or renamed existing result does not qualify.
Use Lean corpus and its research search; no external search, historical research notes, numerical experiments, or extra axioms.

## Plan

1. Recover live route mechanisms and obstructions from Lean sources.
2. State exact competing conjectures; attack each against the corpus and its definitions.
3. Complete a dependency-closed paper proof of a surviving structural advance.
4. Formalize, audit dependencies, compile only needed modules, wire umbrella, lint, clean owned artifacts.
5. Reassess significance honestly; continue conjecturing if the contribution gate fails.

## Initial evidence

- `XiWardCubicPrimeGammaSecantFundamentalSymmetryGap`: replacing the ordinary Weil form by the positive fundamental-symmetry metric loses a nonzero reflection defect; eliminating that defect is already RH.
- `GammaSewnMobiusXiWardHardySaturation`: strict-right Ward transport is unconditionally contractive, but unitary saturation is already RH.

These rule out presenting positive metric replacement or contractivity as the missing structural step.

## Constraints and workspace

- Existing user change: `formal/GaloisForLFunctions/RHTower/WeilPhiDoobDivisorEnergy.lean`; preserve.
- Serena lists memories but configured language is Python. No historical memory content used as mathematical evidence.
- `update_plan` is not exposed in this session; plan tracked here.
- Initial hybrid search completed, but compiler coverage is largely source-only/stale. Every used claim requires source inspection and Lean verification.

## Conjecture ledger

1. Correct the scalar Ward phase to a differentiable lossless family. Rejected as a receiver: `RoutePScalarUnitaryCompletionRegularityNoGo` proves that the proposed differentiability already implies RH. Square-root time reparametrization changes the clock but supplies no arithmetic comparison; insufficient as the requested contribution.
2. Use the exact Xi cap to make scalar translated boundaries preserve cohomology. Rejected: `PrimeRotationXiSourceTransport` proves that a holomorphic scalar correction preserving the local Xi ideal kills its whole quotient. The actual native-clock boundary defect is surjective, not zero.
3. **Proved:** every finite full Xi jet quotient of literal Meyer cohomology admits a source-constructed section intertwining the negative logarithmic derivative. Constructed by repeated causal division of the fixed actual Xi boundary, without a global inverse-Mellin spectral-synthesis premise.
4. **Proved consequence:** the section realizes every finite packet endomorphism faithfully and preserves composition.
5. **Proved cross-route identification:** after its exact phase normalization, the actual source has centered Mellin transform equal to the existing Hedenmalm divided chain, through every actual Xi multiplicity. Its Jordan recurrence holds before passage through the entire comparison map.
6. **Proved structural refinement:** every finite raw source packet has the same universal one-boundary generator defect. Its coefficient is exactly the sum of bottom-chain coefficients. No packet-dependent arithmetic boundary is needed.

## Proven statement

Let H be the all-derivative, all-exponential-decay logarithmic target, B the literal Meyer Poisson boundary range, and Q = H/B. Let A = -d/dt on Q. For every finite set S of actual Xi divisor points, let J_S be the existing full multiplicity jet packet, E_S : Q -> J_S its existing evaluation map, and T_S the action on jets induced by multiplication by s.

Construct L_S : J_S -> Q with E_S L_S = identity and A L_S = L_S T_S. Moreover L_S takes values in classes of explicit causal divisions of a single fixed cap source; evaluations outside S vanish to full Xi multiplicity. Thus P_S = L_S E_S is an actual finite-rank invariant projection. This is stronger than an arbitrary vector-space section or an equivariant quotient. It does not assert completeness of all spectral packets, positivity, or RH.

## Dependency-closed paper proof

Write M(g)(s) = integral exp(st)g(t) dt. The corpus supplies a fixed cap f_Xi with g_0 = Z(f_Xi) in H and M(g_0) = xi on the whole complex plane. Negative Euler differentiation preserves the cap and intertwines Z with -d/dt; hence A descends to Q. The corpus also supplies the true analytic multiplicities m_rho and jet evaluations on Q.

For g in H with M(g)(rho)=0 define

U_rho(g)(x) = exp(-rho*x) integral_[x,infinity) exp(rho*t)g(t) dt.

The full zero moment gives the identical left expression with a minus sign. Each exponential weight of g is integrable. For any real N choose M >= abs(Re rho), abs(N). On the positive half-line the right expression is bounded by exp(-M*x) times the L1 norm of exp(M*t)g(t); on the negative half-line the left expression is bounded by exp(M*x) times the L1 norm of exp(-M*t)g(t). Hence U decays against every exponential at both ends. Differentiating the tail integral gives U' = -rho U - g. Smoothness follows by induction from this differential equation, and every higher derivative is a finite linear combination of U and derivatives of g. These have all exponential decay, so U belongs to H. Integration by parts gives (s-rho) M(U)(s) = M(g)(s) for every s. Uniqueness holds in H: a solution of h'=-rho h is a constant exponential, and decay at both ends forces that constant to vanish.

For a genuine Xi divisor rho of multiplicity m, iterate this operation g_k=U_rho(g_(k-1)), 1<=k<=m. At stage k-1<m, the transform is xi(s)/(s-rho)^(k-1), with its removable value, and still vanishes at rho. Thus every division is admitted. All g_k are actual H functions. Their classes v_k satisfy (A-rho)v_1=0 and (A-rho)v_k=v_(k-1). Their transforms have exact orders m-k at rho. The coefficient of degree m-k is the same nonzero local Xi cofactor. Consequently their m jets form a triangular matrix with nonzero diagonal after reversing k. At any other Xi divisor eta, division by (s-rho)^k is an analytic unit and preserves its full multiplicity, so every permitted eta jet vanishes.

For finite S, sum the resulting chain spans. Evaluation is block triangular and invertible on the coefficient space, giving L_S by its inverse. The derivative recurrence shows the chain span is A-invariant. The existing Mellin derivative identity gives E_S A = T_S E_S, so injectivity of evaluation on the chain span proves A L_S=L_S T_S. Then P_S^2=P_S, im(P_S)=im(L_S), and A P_S=P_S A. For disjoint S,T, outside-support jet vanishing gives P_S P_T=P_T P_S=0.

Every step is integral calculus or an explicitly identified unconditional corpus theorem. All four implementation modules now pass direct Lean audits. The dependency audit below records the remaining integration checks separately.

## Formalization

- `DeningerMeyerCausalDivision.lean`: direct Lean audit passed; targeted dependency build passed. All-derivative/all-exponential decay, the actual causal source, generator identity, and exact entire Mellin division are formalized.
- `DeningerMeyerXiCausalChains.lean`: actual multiplicity chains, local orders, off-divisor vanishing, and quotient generator passed direct Lean audit.
- `DeningerMeyerFiniteXiCausalSplitting.lean`: finite triangular synthesis, invariant section/projector, disjoint packet separation, and faithful finite operator lifting passed direct Lean audit.
- `DeningerMeyerHedenmalmSourceRealization.lean`: exact Hedenmalm transform, centered source recurrence, universal common-boundary decomposition, and exact projector dimension passed direct Lean audit.
- New consequence of the conjecture: every finite packet endomorphism B lifts by L_S B E_S, preserving composition and remaining faithful. This makes finite spectral operator constructions available inside literal Meyer cohomology, rather than only its jet quotients.
- Coverage caveat: research search reports semantic coverage unavailable and some cached generations stale. Exhaustive Lean text search found no preexisting Meyer causal/Jordan/source-projector declarations outside these new files. Mathematical dependencies are verified directly, not accepted from search status.

## Cross-route identification

The new actual sources realize the existing Hedenmalm divided chains exactly. With alpha = -i(rho-1/2), write C_k(z) for the corpus's iterated divided difference of XiC at alpha. Existing partial factorization gives XiC(z)=(z-alpha)^k C_k(z). The causal source gives XiC(z)=i^k(z-alpha)^k M(g_k)(1/2+iz). Away from alpha cancellation yields M(g_k)(1/2+iz)=(-i)^k C_k(z). Both sides are entire, so continuity extends equality to alpha. Rescaling the source by i^k realizes C_k exactly. The centered Jordan recurrence holds in the actual cohomology. Both statements passed Lean.

## Exact common-boundary decomposition

The fixed Xi cap produces a stronger source-level identity. Index a finite packet by (rho,j), 0<=j<m_rho, and synthesize G(c)=sum c_(rho,j) g_(rho,j+1). Let J(c)=sum c_(rho,j)[rho*g_(rho,j+1) + (j=0 ? 0 : g_(rho,j))]. The generator recurrence gives

A G(c) = J(c) + [sum_(rho,j=0) c_(rho,j)] Z(f_Xi).

This is an exact outer-product decomposition of the source defect: every finite packet uses the same single actual boundary vector, independently of its size and multiplicities. Proof: expand A through the finite sum, apply the established chain recurrence termwise, split j=0 from j>0, and collect the common g_0=Z(f_Xi). This does not assume closure or global spectral synthesis. The paper proof is complete before formalization.

## Structural significance audit

The obstruction addressed is the gap between finite dual/quotient spectral data and invariant classes constructed from actual arithmetic sources. The proof discharges source admission explicitly: repeated causal integrals land in the full Meyer target, exact Xi factorization admits every step, and the finite jet matrix is proved invertible. The section is generator-invariant, not merely a vector-space splitting. Linear independence and the exact finite dimension preserve all multiplicities. The Hedenmalm identification ties the construction to the existing divided-chain route. The common-boundary identity identifies the exact arithmetic source defect before quotienting.

The resulting new class of available constructions is every finite packet endomorphism, realized faithfully as L_S B E_S on literal Meyer cohomology, with composition preserved. The identity of this finite operator calculus is P_S, not the identity on the whole cohomology.

Scope is algebraic finite spectral synthesis. No topological continuity of the projectors, infinite-packet convergence, completeness of the divisor chains, vanishing of the jet-invisible kernel, positive inner product, or RH is asserted. These remain distinct research obligations. The contribution does not retire any RH route.

## Integration audit

- Direct `lake --old env lean <module>.lean` audits passed for all four new leaves. For dependent leaves the same foreground command also exported the needed `.olean` with `-o`. No full or umbrella build was run; no heartbeat increase, numerical experiment, or added axiom was used.
- All four leaves are explicitly imported in `formal/GaloisForLFunctions/RHTower.lean`.
- Fresh exact lexical research search returns `deningerMeyerHedenmalmSource_transform` in its new module.
- `scripts/formal_tools.py lint` was rerun after wiring. It reports no error for this contribution. Repository-wide exit status is 1 because two unrelated modules are unreachable from the RH umbrella: `CHMDStage16GrowthPositivityCollapseAndTwoPointCriterion` and `CHMDStage20TwoPointCoshSinhClosedFormsAndRhoCosShiftDecomposition`. These concurrent changes were left untouched.
- Final `/tmp` scratch audit passed under `lake --old env lean`, verifying the used mathlib names against this toolchain and printing axioms for twelve principal results: causal decay admission, Xi class recurrence, source independence, section right-inverse, projector commutation, disjoint projectors, composition-preserving and faithful operator lifting, exact Hedenmalm transform, centered Jordan recurrence, common-boundary decomposition, and exact finite dimension. Every result depends only on `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx` or new axiom occurs.
- Scratch scripts, logs, and search outputs created for this task were removed after recording these results. Valid compiled leaf artifacts remain available for downstream imports.
