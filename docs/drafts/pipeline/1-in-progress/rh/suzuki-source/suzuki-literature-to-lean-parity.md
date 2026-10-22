# Suzuki literature-to-Lean parity audit

**Status:** in progress  
**Audit date:** 2026-08-12  
**Scope:** Suzuki's Riemann-zeta screw-function/operator route and direct operator-theoretic
predecessors needed by the current frontier.  This is a parity ledger, not a claim of new science.

## Exactness rule

`EXACT` means the source's mathematical objects are defined and the cited result is proved for
those objects.  A theorem about free matrices, arbitrary Hilbert-space operators, or a predicate
named after Suzuki is only `GENERIC CORE`.  A comment saying that a paper supplies a premise is not
a formalization of the paper theorem.  RH-conditional results remain RH-conditional results; they
must not be relabelled unconditional.

## Primary-source frontier

1. Masatoshi Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096v1
   (2026-06-08).  This is the latest Suzuki paper directly defining the finite-aperture route.
2. Alain Connes, Caterina Consani, Henri Moscovici, *Zeta Spectral Triples*,
   arXiv:2511.22755v1 (2025-11-27).  This supplies the finite restricted-Weil predecessor cited by
   Suzuki.
3. Masatoshi Suzuki, *On the Hilbert space derived from the Weil distribution*,
   arXiv:2301.00421v3 (2025-11-07; incorporates arXiv:2209.04658).
4. Masatoshi Suzuki, *Aspects of the screw function corresponding to the Riemann zeta function*,
   arXiv:2206.03682v4 (2023-05-30).
5. Masatoshi Suzuki, *A canonical system of differential equations arising from the Riemann
   zeta-function*, arXiv:1204.1827 (published source version).

## arXiv:2606.09096 theorem parity

| Source result | Exact content | Corpus status | Required closure |
|---|---|---|---|
| Theorem 1.1 | For every `a > 0`, the actual self-adjoint operator `A_a` associated with the localized Weil form is the Friedrichs extension of the actual symmetric `B_a = D* G_a D`. | **MISSING OPERATOR THEOREM; EXACT COMPLEX TEST-CORE SEMIBOUND CLOSED.** `SuzukiRestrictedWeilSourceForm.lean` fixes the literal archimedean constant, visible prime-power aperture, and continuous smooth kernel in the four-block real test-function form. `SuzukiRestrictedWeilFinitePart.lean`, `SuzukiRestrictedWeilSmoothBound.lean`, `SuzukiRestrictedWeilSemibounded.lean`, and `SuzukiRestrictedWeilComplexCore.lean` prove exact finite-part, smooth, full real, and literal complex `C_c^∞(-a,a)` semibounds. No corpus declaration yet completes the form in complex `L²`, defines actual `A_a` and `B_a`, or proves their extension equality. | Construct the localized complex closed-form completion and representing self-adjoint operator, construct `B_a` on `H₀¹`, and prove graph/form-core equality giving the Friedrichs extension. |
| Corollary 1.2 | Infimum attained in form closure and equals the Rayleigh infimum over `C_c^∞(-a,a)`. | **MISSING EXACT.** A literal smooth compact-support core type now exists and the prime/smooth blocks have unconditional lower bounds. No completed localized form domain, core-density theorem, or actual Rayleigh minimizer is constructed. | Finite-part lower bound, form completion and core density, representation theorem, and exact equality `Q_W^a(v)=⟨B_av,v⟩`. |
| Theorem 1.3 | Actual lowest eigenvalue `a ↦ λ_a` is continuous. | **MISSING OPERATOR INSTANTIATION.** No actual `λ_a` is defined. The exact bounded-interval `H^log` compact embedding is formalized. Provisional umbrella `SuzukiWeilRemainderRegularity.lean` removes the apparent singularity of the literal smooth remainder, fixes its value at zero to `-7/4`, and proves the resulting even kernel continuous and bounded/integrable on finite apertures. Generic resolvent-limit modules still do not instantiate Suzuki's scaled logarithmic form. | Formalize fixed-interval scaled forms `q_a`, turn kernel regularity into parameter-dependent bounded-form continuity, prove upper semicontinuity on a common smooth core, and prove lower semicontinuity using `SuzukiHlogCompactEmbedding.lean`. |
| Theorem 1.4 | For small `a`, `λ_a` is positive and simple, has the stated logarithmic asymptotic, and its eigenfunction is even. | **ACTUAL SMOOTH SOURCE-FORM POSITIVITY CLOSED; SPECTRAL CLOSURE MISSING.** `SuzukiOriginLogarithmicRemainder.lean`, `SuzukiOriginRemainderFirstJet.lean`, and `SuzukiOriginRemainderRegularity.lean` prove the literal Eq. (2.2) decomposition, exact first jet, global `C²`, sharp `r(t)/t² → -7/8`, and `O(t²)`. `SuzukiLimitingLogFormCoercivity.lean` proves the new explicit bound `L(u) ≥ ‖u‖²₂/24`. `SuzukiPrimeFreeScaledCoercivity.lean` proves a uniform source-remainder bound and a coefficient tending to `+∞`. Crucially, `SuzukiScaledFormBridge.lean` proves the exact change-of-variables identity from that fixed-interval expression to `(1/a)` times the literal restricted Weil form on rescaled complex test cores, and hence strict positivity for normalized tests at bundled sufficiently small apertures. No closed-form completion, actual `λ_a`, simplicity theorem, or even ground state is constructed. | Extend quantitative coercivity through the form completion; construct the associated compact-resolvent operator and actual lowest eigenvalue; prove perturbative simplicity and reflection commutation; select the even ground sector. |
| Theorem 1.5 | Actual minimal derivative on the completed form space has deficiency indices `(1,1)`; the actual `W(a,θ;z)` is entire, its zeros are exactly the spectrum of the actual self-adjoint extension, and every zero is real. | **MISSING EXACT.** `SuzukiFiniteApertureHermiteBiehler.lean` begins from `SuzukiAllAngleRealZeros`; the comment says Suzuki supplies it. `SuzukiProjectedContinuousDeficiency.lean` proves interval identities under ODE and regularity premises. Neither defines the actual completion/operator/deficiency vectors. | Build `H(T_a)`, the densely defined derivative `𝒟_a`, its adjoint and one-dimensional deficiency spaces; construct von Neumann extensions; define actual normalized `v_±`; prove the Lagrange identity and characteristic equivalence; derive reality from self-adjointness. |
| Corollary 1.6 | Compact-open convergence of gauged `W(a,θ(a);·)` to `z² ξ/ξ'` implies RH. | **PARTIAL EXACT NO-GO, NOT THE COROLLARY.** `SuzukiCharacteristicEntireLimitNoGo.lean` treats an ordinary one-angle holomorphic-gauge target obstruction. | Formalize the literal meromorphic target and Hurwitz/pole-removal implication, while retaining the source's convergence premise as a premise because it is conjectural rather than a theorem. Do not claim that premise. |

### Exact 2026 source infrastructure already present

- `SuzukiExplicitScrewRegularKernel.lean`: literal prime/Lerch regular kernel pieces and exact
  derivative identities, including the Suzuki constants.
- `SuzukiScrewDistributionalKernel.lean`: distributional second-derivative/integration-by-parts
  bridge on prime-free intervals.
- `SuzukiRestrictedWeilForm.lean`: generic four-block test-function form and representative
  decomposition; deliberately stops before fixing every source parameter or constructing `A_a`
  or `B_a`.
- `SuzukiWeilRemainderRegularity.lean` (**current dirty umbrella, provisional**): exact two-step
  l'Hopital evaluation of the smooth remainder at zero as `-7/4`, continuous removal of the
  singularity, continuous even source kernel, and unconditional finite-aperture boundedness and
  interval integrability. This closes literal source-kernel regularity, not form-parameter
  continuity or operator construction.
- `SuzukiRestrictedWeilSourceForm.lean` (**current dirty umbrella, provisional**): inserts the
  literal archimedean constant, exact visible prime-power indices, and continuous remainder into
  the four-block form; proves its exact distributional representative, complete prime-block
  jump-energy decomposition and lower bound, and uniform finite-aperture smooth-kernel difference
  bound. Every source parameter is fixed. Finite-part semiboundedness and operator construction
  remain.
- `SuzukiRestrictedWeilSmoothBound.lean` (**current dirty umbrella, provisional**): chooses the
  canonical compact-aperture kernel bound and proves the literal smooth quadratic block is bounded
  below by an explicit finite multiple of interval `L²` energy. No regularity premise remains.
- `SuzukiOriginLogarithmicRemainder.lean` (**current dirty umbrella, provisional**): proves literal Eq.
  (2.2), its even source remainder, the exact `-7/4` renormalized curvature at the origin,
  continuity on the line, and a uniform local curvature bound. This closes origin-remainder
  analysis, not the small-aperture eigenvalue theorem.
- `SuzukiOriginRemainderFirstJet.lean` and `SuzukiOriginRemainderRegularity.lean` (**current dirty
  umbrella, provisional**): identify the exact first jet, prove its derivative is the continuous
  curvature, prove global `C²` regularity of the source remainder, the sharp two-sided limit
  `r(t)/t² → -7/8`, and the exact `O(t²)` germ.  This closes the analytic origin expansion used by
  the scaled-form argument.
- `SuzukiRestrictedWeilFinitePart.lean`, `SuzukiRestrictedWeilSmoothBound.lean`,
  `SuzukiRestrictedWeilSemibounded.lean`, and `SuzukiRestrictedWeilComplexCore.lean` (**current
  dirty umbrella, provisional**): close the literal finite-part identity and semibound, smooth
  perturbation bound, complete real source-core semibound, and its extension to mathlib's literal
  complex test-function space.  Form completion and operator identification remain.
- `SuzukiLimitingLogFormCoercivity.lean` (**current dirty umbrella, provisional; new strengthening**):
  defines Suzuki's exact complex limiting form on `C_c^∞((-1,1),ℂ)` and proves unconditionally
  `L(u) ≥ ‖u‖²₂/24`.  Suzuki's paper establishes only an unnamed positive ground constant by
  compactness/contradiction; the explicit constant is new quantitative information, not parity
  busywork.  It does not by itself construct the finite-aperture operator or eigenvalue.
- `SuzukiPrimeFreeScaledCoercivity.lean` and `SuzukiScaledFormBridge.lean` (**current dirty umbrella,
  provisional; exact source bridge**): prove the visible prime layer is empty for
  `2a < log 2`, replace Suzuki's fixed-vector `O(a)` in (5.1) by a uniform Schur form bound, prove
  the resulting coercivity coefficient tends to `+∞`, construct the exact rescaled source cores,
  and prove `(1/a) Q_W^a(u(·/a))` equals the literal prime-free fixed-interval numerator.  The final
  closed theorem gives strict positivity of the actual smooth source form for normalized complex
  tests at intrinsically bundled sufficiently small apertures.  Extending this bound through the
  closed form and identifying its lowest eigenvalue remain open.
- `SuzukiHlogCompactEmbedding.lean`: exact source weight `1 + log⁺|ξ|`, exact zero-extended
  bounded-interval unit ball, published uniform Fourier-tail estimate, and compact closure for every
  bundled bounded interval.  This closes Suzuki (2026), Proposition 4.1 / the compact-embedding
  ingredient cited from CCM (2025), rather than a discrete or finite-dimensional proxy.
- `SuzukiScrewNondegeneracy.lean`: constructs the exact zero-extension injection from the literal
  subtype realization of `L²(-a,a)` used by Suzuki's trace-class integral operator to the whole-line
  fixed-support realization used by the strict screw-form theorem, proves equality of both literal
  double-kernel forms, identifies the full sesquilinear interval form with the operator pairing,
  proves radical-zero nondegeneracy equivalent to operator injectivity, and closes both source
  formulations of the RH-implies-nondegeneracy/no-zero-eigenvalue half of Suzuki (2023), Theorem
  1.4.
- `CompactFourierEntire.lean`: exact entire/exponential-type theorem for compact interval Fourier
  integrals; usable for the entireness clause once the actual deficiency vectors are constructed.
- `SuzukiFiniteApertureHermiteBiehler.lean`, `SuzukiAllAngleWitnesses.lean`,
  `SuzukiFiniteApertureBoundaryPhaseLocking.lean`, and `SuzukiStrongResolventLimit.lean` are
  **generic consequences/bridges**, not exact proofs of Theorems 1.1--1.5.

## arXiv:2511.22755 direct-predecessor parity

| Source result | Corpus status |
|---|---|
| Lemma 2.2, common-translation invariance of `f* * g` and `q(f,g)` | **EXACT.** `CCMTranslationInvariance.lean` defines the literal complex `L¹(ℝ,dx)` source, CCM translation convention, involution, additive convolution, and even Hermitian correlation, then proves both common-translation identities as closed theorems. |
| Lemma 2.3, exact convolution formulas for finite-interval Fourier modes | **EXACT.** `CCMZeroExtendedFourierCorrelation.lean` defines the normalized periodic modes on `[0,L]`, extends them by zero to `ℝ`, defines the literal convolution correlation, and proves equations (2.7), (2.10), and the complete diagonal/off-diagonal Lemma 2.3 formula. Positive aperture and legal lag are bundled, so the final theorem is closed and has no spectral or RH premise. |
| Inversion-splitting lemma preceding Proposition 3.2, `Ψ(H)=Ψ#(H+H∘ι)` | **EXACT FINITE-APERTURE FORM.** `CCMLogarithmicWeilFormTransport.lean` defines literal complex two-sided `Ψ` and one-sided `Ψ#` from the published polar, archimedean, and finite von Mangoldt components and proves their exact inversion/evenization identity without integrability assumptions hidden as premises. |
| Proposition 3.2, logarithmic isometry and restriction of the Weil form to `Ψ#(q(f,g)∘log)` | **EXACT.** `CCMLogarithmicApertureUnitary.lean` proves the literal onto isometry `L²([0,2 log λ],dx) ≃ L²([λ⁻¹,λ],d*u)` for bundled `λ>1`, its a.e. formula `κf(u)=f(log(λu))`, sharp-support intertwining, and the induced equivalence of extendably smooth closed-interval functions. `CCMLogarithmicWeilFormTransport.lean` constructs literal complex `L¹(ℝ₊*,d*u)`, multiplicative involution and Haar convolution, proves logarithmic transport of the involutive convolution algebra, and derives the exact closed theorem `QW(κf,κg)=Ψ#(q(f,g)∘log)` for bundled interval sources. |
| Theorem 3.6 analytic compactness ingredient, compact embedding for Fourier weights tending to infinity; Suzuki specialization `H^log(I) ↪ L²(I)` | **EXACT.** `CCMGeneralFourierWeightCompactEmbedding.lean` proves the published theorem for every bundled positive monotone Fourier weight tending to infinity, on every bounded interval. `SuzukiHlogCompactEmbedding.lean` separately proves the literal `1 + log⁺|ξ|` specialization used by Suzuki, including its exact tail estimate and compact closure. Both use actual `L²(ℝ)` zero extensions and time-band compact operators, not sequence or finite-dimensional proxies. |
| Theorem 1.1(i), rank-one perturbed scaling operator is self-adjoint under simple/even lowest-eigenvector assumptions | **GENERIC CORE ONLY.** Boundary-completion and metric-self-adjoint matrix laws exist. Actual source matrix is defined. The simple/even assumptions are not proved universally and must not be erased. |
| Theorem 1.1(ii), regularized determinant formula | **MISSING EXACT.** |
| Theorem 1.1(iii), Fourier transform entire, real-zeroed, with zeros equal to spectrum | **GENERIC/PARTIAL.** Entire compact Fourier infrastructure and generic real-spectrum arguments exist; literal source operator/eigenvector identity is not closed. |

## arXiv:2301.00421v3 parity

| Source result | Corpus status |
|---|---|
| Theorem 1.1, under RH the Weil completion is isomorphic to the Xi de Branges/model space with exact norm identity | **MISSING EXACT.** No literal Hilbert completion/model-space isomorphism. |
| Proposition 1.2, actual screw-line function `𝔖_t` belongs to `L²(ℝ)` | **MISSING EXACT.** Corpus has related summable-spectrum screw Hilbert results, not the full zeta/gamma/prime definition from the paper. |
| Proposition 1.3, integrated actual screw-line packet belongs to `L²` | **MISSING EXACT.** |
| Theorem 1.4, RH iff the exact screw-line/Weil norm equality holds for all compact tests; countable tests suffice | **MISSING EXACT.** |
| Corollary 1.5, RH iff `2‖ψ‖²=⟨ψ,ψ⟩_W` on actual `V°(0)` | **MISSING EXACT.** |

## arXiv:2206.03682 and arXiv:1204.1827

### arXiv:2206.03682v4 theorem parity

| Source result | Corpus status |
|---|---|
| Theorem 1.1(i), one-sided Fourier transform of the literal `Psi` for `Im z > 1/2` | **EXACT.** `SuzukiScrewFourierTransform.lean` proves the source transform with the literal prime--Lerch `suzukiPsi` and centered Xi logarithmic derivative. |
| Theorem 1.1(ii), multiplicity-exact Xi-zero series for every `t >= 0` and its even extension | **EXACT.** `SuzukiExplicitScrewZeroSeries.lean` proves the literal prime--Lerch formula equals the unconditional full Xi screw divisor, including multiplicity and conjugation symmetry. |
| Proposition 2.1, `sum_{n <= exp t} Lambda(n)/sqrt(n) (t-log n) = 4 exp(t/2) + O(exp(t/2-c sqrt t))` | **EXACT.** `SuzukiScrewGrowthBound.lean` proves the finite Abel identity against the sharp Chebyshev function, transfers the corpus's unconditional stronger Littlewood PNT through an exact split at `exp(t/2)`, and proves the stated source asymptotic with closed existential constants. |
| Theorem 1.1(iii), `Psi(t) << exp(t/2-c sqrt t)` | **EXACT.** `SuzukiScrewGrowthBound.lean` proves both an explicit eventual bound and the `IsBigO atTop` source statement for literal `suzukiPsi`; the Lerch and archimedean terms are bounded after the exact Proposition 2.1 cancellation. |
| Lemma 2.1, an exponential-type entire function constant on every Xi zero is constant | **EXACT.** `TitchmarshZetaInputs.lean`, `TitchmarshCircleChain.lean`, `TitchmarshZeroGap.lean`, and `SuzukiTitchmarshUniqueness.lean` supply the unconditional quantitative distinct-zero input and close Suzuki's exact exponential-type uniqueness statement. |
| Theorem 1.2, RH iff the literal `g=-Psi` is a Krein screw function on the real line | **EXACT.** `SuzukiScrewFunctionCriterion.lean` proves both implications for the source kernel and all finite kernel matrices. |
| Theorem 1.3, restricted screw hermitian form iff RH; under RH strict positivity on every nonzero `L²(-a,a)` vector | **EXACT.** `SuzukiScrewL2Form.lean`, `SuzukiScrewSmoothTestCriterion.lean`, `SuzukiCompactL2Fourier.lean`, and `SuzukiScrewStrictPositivity.lean` define the literal form, prove the RH equivalence, and exclude its radical under RH. |
| Proposition 3.1, derivative of the screw form equals the Weil-distribution convolution form | **EXACT.** `SuzukiScrewWeilIdentity.lean` proves the global source test-function identity, including the prime-power atoms. |
| Theorem 1.4, RH iff every restricted form/operator is nondegenerate / has no zero eigenvalue | **NECESSITY AND FORM/OPERATOR EQUIVALENCE EXACT; CONVERSE MISSING.** `SuzukiScrewNondegeneracy.lean` bridges the two actual `L²(-a,a)` realizations by an injective zero extension, proves exact equality of the literal screw form and the full sesquilinear operator pairing, proves radical-zero nondegeneracy equivalent to `Function.Injective T_a`, and proves the closed implications from RH in both formulations. The reverse implication is not abstract operator algebra: the source uses a maximal positive aperture and uniform infinite Gram--Schmidt estimates to force a zero mode at the boundary if RH fails. |
| Theorem 1.5, every actual restricted screw-kernel operator is trace class unconditionally | **EXACT.** `SuzukiScrewTraceClass.lean` constructs the literal bounded-interval operator and proves its unconditional trace-class factorization; `SuzukiScrewTraceFormula.lean` proves the diagonal and eigenvalue-sum identities. |
| Theorem 1.6, RH iff `Psi=O(1)` on `[0,infinity)` | **EXACT.** `SuzukiScrewBoundednessCriterion.lean` proves the literal boundedness equivalence. |
| Paragraph after Theorem 1.6, `Psi` belongs to neither `L¹(0,infinity)` nor `L²(0,infinity)` regardless of RH | **EXACT.** `SuzukiScrewNonintegrability.lean` proves both closed negations from the exact Laplace continuation and central Xi-resolvent residue. |
| Theorem 1.7, RH iff pointwise `Psi >= 0`; under RH `Psi(t)>0` for `t != 0` | **EXACT.** `SuzukiScrewPointwiseNonnegativityCriterion.lean` closes the equivalence and `SuzukiScrewStrictPositivity.lean` closes strict positivity using the now-exact uniqueness theorem. |
| Theorem 1.8, published determinant-chain criterion | **PUBLISHED CONVERSE INVALID AS PROVED; CORRECTED EXACT THEOREM CLOSED.** `SuzukiStieltjesDeterminantCounterexample.lean` gives a closed sequence with both determinant chains nonnegative but a negative shifted Hankel form, disproving the generic implication used in the paper. `StieltjesSemidefiniteExistence.lean`, `HardyStieltjesDeterminacy.lean`, `SuzukiStieltjesMoments.lean`, and `SuzukiStieltjesCriterion.lean` prove the literal corrected theorem: RH iff both ordinary and shifted Hankel forms are positive semidefinite. The valid RH-to-determinant direction is also exact. Whether the determinant-only converse happens to hold for this special moment sequence remains open; the printed proof does not establish it. |
| Theorem 4.1, local positivity | **WEAK SOURCE-SUFFICIENT FORM EXACT; STRONG PRINTED RANGE OPEN.** `SuzukiScrewFirstGap.lean` proves symbolically that `Psi(t)>0` on `0<t<1/20`, which the source explicitly says suffices for Theorem 1.4. It also proves the exact first-gap derivative and exposes a missing `-(log pi)/2` in the printed formula. The claimed `t₀>log 2` proof still depends on computer-found derivative roots and is not yet formalized. |
| Theorems 4.2--4.3, small-aperture positive definiteness and Yoshida coercivity | **PARTIAL REPAIR, ANALYTIC INTERFACES PROVISIONALLY CLOSED.** Lean proves by a PSD matrix counterexample that entrywise kernel order does not imply quadratic-form order. `SuzukiOrientedPrimitive.lean` and committed `SuzukiGramDominationRepair.lean` give exact finite-packet Gram and form bounds. Current dirty umbrella-wired `SuzukiL2GramRepair.lean` proves finite energy, exact actual-source free-kernel Gram factorization, literal Eq. (4.2) Fourier factorization, and both disputed form bounds for every `L²(-a,a)` source. Dirty umbrella-wired `SuzukiArchimedeanCoercivity.lean` proves corrected weight normalization, global minimum, high-frequency coercivity, and compact-band lower envelope. Generic dirty umbrella-wired `HTGeometry/FriedrichsFormOperator.lean` supplies positive self-adjoint form operators, compact resolvent under compact embedding, and core extension. Commit, direct audit, and concrete Suzuki coercivity/form-domain/Friedrichs assembly remain. |
| Unnumbered theorem after Theorem 1.5, failure of RH produces a nonzero Xi-zero coefficient family whose screw exponential series vanishes on an interval | **MISSING EXACT; DEPENDS ON THEOREM 1.4 CONVERSE.** The literal divisor features and convergent kernel series exist, but the required raw-`L²` zero eigenvector is exactly the still-missing sufficiency half of Theorem 1.4. |
| Section 8 theorem, exact mutually inverse transformations between Suzuki moments `μ_n` and Li coefficients `λ_n` | **MISSING EXACT.** `SuzukiStieltjesMoments.lean` defines the literal `μ_n` and proves unconditional integrability/determinacy infrastructure. `LiFiniteCriterionFrontier.lean` is only a finite-divisor algebraic analogue and does not define the actual Li coefficients or prove Suzuki's infinite source identities. |
| Section 8 theorem, positive-coefficient recurrence for the literal Suzuki moments | **MISSING EXACT.** Requires literal Li coefficients, the `ξ(1/(1-w))` Taylor coefficients, their positivity, and the source's exact coefficient extraction. |
| Section 11 theorem, `ξ` zero-free in `Re s > 1/2+ω` iff the shifted literal `Ψ_ω` is eventually nonnegative | **MISSING EXACT.** No corpus object currently defines Suzuki's literal shifted screw function `Ψ_ω` from the shifted Xi logarithmic derivative. Gamma-shift multiplier files concern a different later route and are not this theorem. |

### arXiv:1204.1827

This source is now inventoried statement by statement. The explicit canonical system is
unconditional only in the paper's proved parameter range (`omega > 1`); extension to the critical
range is not literature-known and must not be postulated. Similar canonical-system names in corpus
do not establish parity.

| Source statement | Exact Lean status |
|---|---|
| Introductory shifted-Xi identities and Proposition `prop_basic`: RH iff every literal `A^omega` has only real zeros for all `omega>0` | **EXACT.** `SuzukiCanonicalShiftedXi.lean` defines the paper's literal `A^omega,B^omega`, proves the centered-Xi identities and Schwarz reflection, proves RH gives strict shifted-modulus separation off the real axis, constructs the explicit positive shifts `omega_n=1/(n+1)`, proves their locally uniform convergence to `XiC`, and applies the closed-locus Hurwitz transfer to prove the converse. |
| Equations (105_1)--(108): literal `E^omega`, `Theta_omega=E^sharp/E`, meromorphicity, reflection/product law, unit-modulus real boundary, normalization at zero, and Hermite--Biehler/disk equivalence | **EXACT AT THE MEROMORPHIC REPRESENTATIVE LEVEL.** `SuzukiCanonicalShiftRatio.lean` defines the literal source ratio, proves all unconditional numerator/reflection identities, global meromorphicity, `Theta_omega(0)=1`, the unit-modulus law at every regular real point, and the exact Hermite--Biehler iff denominator-regular strict-disk law. The printed product identity is correctly stated on the regular locus because Lean's total quotient assigns `0/0=0`; claiming pointwise equality at poles would be false representation, not formalization. |
| Proposition `intro_2`: the zeta zero-free half-plane `Re s>1/2+omega_0` iff every `Theta_omega`, `omega>omega_0`, is meromorphic inner | **EXACT.** `SuzukiLagariasMeromorphicInner.lean` formalizes the hard cited dependency, Lagarias--Suzuki (2006), Theorem 4, from the multiplicity-exact Xi Hadamard product: reflection-paired factors remove genus-one exponentials, every finite block has the strict modulus inequality, and a positive-real infinite-product proof preserves strictness. It then defines the source-faithful meromorphic-inner predicate, proves both directions including isolated-zero shift selection and an exact meromorphic-order pole contradiction, and closes the full quantified theorem as `suzuki2012_zetaZeroFree_iff_forall_theta_meromorphicInner`. The zeta predicate explicitly excludes `s=1`, correctly treating it as a meromorphic pole rather than Lean's totalized point value. |
| Proposition `prop_1`: the absolutely convergent Mellin transform of literal `h_omega` equals `Theta_omega` for `omega>0`, `Im z>1/2+omega` | **EXACT.** `SuzukiCanonicalKernelMellin.lean` proves the literal incomplete-beta `g_omega`, its support, square substitution, multiplicative Mellin convolution, Gamma recurrence, and exact archimedean quotient. `SuzukiCanonicalArithmeticMellin.lean` proves the coefficient L-series summability, inverse-dilation norm law, Tonelli/Fubini interchange, equality of the series with the floor-truncated equation (204), and closed capstone `suzuki2012_proposition_one` with absolute convergence encoded by `HasMellin`. |
| Theorem `thm_2`: innerness of `Theta_omega` iff each of the three exact convolution/support/`L²` conditions | **MISSING EXACT.** Requires the literal shifted Mellin transform, Hardy/Mellin identification, and closed convolution operator. |
| Lemma `lem_301`: `Theta_omega H² subset H²` implies literal `Theta_omega` inner | **MISSING EXACT.** Requires pole exclusion plus the paper's Phragmen--Lindelof strip bound for the literal ratio. |
| Lemma `lem_401`: the literal Hankel integral extends to an `L²(0,infinity)` isometry and satisfies the shifted Mellin intertwining identity, including compact-support continuation to `Im z>=0` | **EXACT.** `SuzukiCanonicalHankelKernelBridge.lean`, `SuzukiCanonicalHankelKernelInversion.lean`, and `SuzukiCanonicalHankelLemma41.lean` identify the literal compact-smooth integral with the global canonical spectral unitary and extend by density to the full positive-ray `L²` space. `SuzukiCanonicalHankelOneSidedSupport.lean`, `SuzukiOneSidedFourierLaplaceAnalytic.lean`, and `SuzukiCanonicalHankelLemma401Continuation.lean` prove the exact one-sided support transport and holomorphic/closed-half-plane continuation of equation (4.01). |
| Lemma `lem_402`: for `omega>1/2`, the compressed literal Hankel operator is self-adjoint Hilbert--Schmidt for `a>1` and zero for `0<a<=1` | **EXACT.** `SuzukiCanonicalKernelLocalL2.lean` proves the sharp local `L²` threshold for the literal incomplete-beta kernel; `SuzukiCanonicalArithmeticLocalL2.lean` transfers it through every inverse dilation in the finite arithmetic sum; `SuzukiCanonicalCompressedHankel.lean` proves the literal two-variable kernel lies in `L²((0,a)²)` and is Hermitian; `SuzukiCanonicalCompressedHankelOperator.lean` constructs the actual operator `(H_{ω,a}f)(x)=∫₀ᵃ h_ω(xy)f(y)dy`, proves the formula almost everywhere, and closes self-adjointness, Hilbert--Schmidt compactness, and exact vanishing for `a<=1`. All capstones have only Lean's standard quotient/classical axioms. The proof also exposes a stronger unconditional survivor: the literal beta tail, `g_ω`, and `h_ω` are pointwise real for every real `ω`, not merely the paper's `ω>1/2` range. |
| Lemma `lem_403`: a nonzero `H_omega P_a f` cannot have compact support | **EXACT.** `SuzukiCanonicalHankelLemma43.lean` combines the literal transform identity, Xi zero-density lower bound, and compact-support exponential-type upper bound to prove Suzuki's exact compact-output obstruction. |
| Lemma `lem_404`: exact annihilated subspace, strict vector contraction, operator norm `<1`, and invertibility of `1 plus/minus H_{omega,a}` | **EXACT.** `SuzukiCanonicalHankelCompressionBridge.lean` proves that the literal Hilbert--Schmidt kernel operator is the finite compression of the actual global canonical unitary. `SuzukiCanonicalHankelLemma44.lean` proves inner-interval annihilation, equality rigidity via Lemma 4.3, strict contraction of every nonzero vector, compact self-adjoint norm attainment, the uniform norm gap, and both resolvents as units. |
| Lemma `lem_405`: unique real Fredholm solutions `phi_a^plus/minus`, their support, and continuity for `omega>1` | **EXACT.** `SuzukiCanonicalKernelContinuity.lean` proves continuity of the literal incomplete-beta kernel and floor-truncated arithmetic kernel, including integer breakpoints. `SuzukiCanonicalHankelLemma45.lean` constructs both inverse-resolvent solutions, proves the exact integral equation and uniqueness, real-valuedness a.e., the lower support gap, and the pointwise-real continuous representative vanishing on `[0,1/a]` for `omega>1`. |
| Lemma `lem_406`: unique extended `L²` and continuous solutions on larger intervals/the half-line | **EXACT.** `SuzukiCanonicalHankelLemma46.lean` constructs the literal larger-interval boundary and Fredholm solution, proves exact cross-interval compression, restriction to Lemma 4.5's solution, pointwise-a.e. equation (402), uniqueness, and reality on every `L²(0,b)`.  For `omega>1` it defines literal formula (404.1), proves local compact-row continuity on the full half-line, upgrades it to continuity at `0` using the sharp support gap, proves pointwise reality and agreement with the finite continuous representative, and derives genuine uniqueness among all continuous `[0,infinity)` solutions of (402) by reducing their compact restriction to the finite resolvent theorem. |
| Lemma `lem_ad1`: piecewise continuous differentiability of extended `phi_a^plus/minus` in `x` | **EXACT KERNEL DIFFERENTIABILITY CLOSED; PARAMETRIC INTEGRAL CORE OPEN.** `SuzukiCanonicalKernelDifferentiability.lean` proves the exact FTC derivative and `C¹(0,1)` regularity of the literal incomplete-beta tail, `C¹(0,1)` for the literal `g_omega`, and `C¹` regularity of the floor-truncated arithmetic `h_omega` at every positive noninteger.  It also proves `x ↦ h_omega(ax)` is `C¹` on the source's exact complement of `{n/a}`.  Remaining hard clause is differentiation of `∫₀ᵃ h_omega(xy) phi_a^epsilon(y)dy` across moving integrable cusps; a fixed pointwise dominating derivative does not exist, so the proof must formalize source-specific moving-breakpoint/Fredholm-minor estimates rather than invoke generic dominated convergence. |
| Lemma `lem_ad2`: continuity and punctured continuous differentiability of `phi_a^plus/minus` in aperture `a` | **MISSING EXACT.** Requires aperture-differentiated Fredholm determinants/minors. |
| Lemma `lem_407`: convergence and meromorphic/upper-half-plane analytic continuation of literal `Psi_a` | **MISSING EXACT.** Depends on the exact Hankel transform and extended Fredholm solutions. |
| Lemma `lem_408`: continuation, `Theta_omega` functional equation, and entire Xi-products for `tilde E_a,tilde E_a*` | **MISSING EXACT.** Depends on Lemma `lem_407` and the exact Mellin-Hankel intertwining identity. |
| Lemma `lem_409`: continuation, entire completion, parity, and `Theta_omega` covariance of `A_a,B_a` | **MISSING EXACT.** Depends on Lemma `lem_408`. |
| Lemma `lem_411`: `A_a,B_a` are real entire functions | **MISSING EXACT.** Requires the literal theta-Mellin representation and source solutions. |
| Lemma `lem_410`: `A_a,B_a` converge locally uniformly to `A^omega,B^omega` as `a -> 1+` | **MISSING EXACT.** Requires quantitative source Fredholm convergence. |
| Theorem `thm_4`: for `omega>1`, the complete literal Fredholm-determinant Hamiltonian and canonical system with solution `A_a,B_a` | **MISSING EXACT.** This is the dependency closure of Lemmas `lem_401`--`lem_411`; abstract canonical systems elsewhere do not instantiate the source. |
| Theorem `thm_3` parts (1)--(5): exact model-space kernel formula, `L²` tail equivalence, eventual-sign and limit sufficient conditions, and RH-family asymptotic for `h_omega^{<1>}` | **MISSING EXACT.** Literal `h_omega^{<1>}` and its Mellin/model-space theory are absent. |
| Theorem `thm_5`: the differentiated `h_omega^{<1>}` transform extends to the literal `H_omega` isometry | **MISSING EXACT.** Depends on `thm_3`, `prop_a1`, and exact operator closure. |
| Proposition `prop_a1`: absolutely convergent Mellin transform of `h_omega^{<1>}` equals `(i/z)Theta_omega` | **EXACT.** `SuzukiCanonicalArithmeticMellin.lean` formalizes the literal weighted integral `(a202)`, proves its convolution coordinate and Mellin multiplier `(s-1/2)⁻¹`, defines the literal floor-truncated `(a204)`, proves pointwise equality with the arithmetic series, and closes `suzuki2012_proposition_a1` with exact `(i/z)Theta_omega(z)` value and absolute convergence. |

## Route-G paper theorems SR-94--SR-109

The recent source-realization paper developments are not literature parity.  Current exact status:

- SR-94--SR-104: paper proofs/generic ingredients only; literal Xi source statements are not Lean
  theorems.
- SR-105--SR-109: Lean files prove scalar or abstract Hilbert-space cores only.  They do not define
  the literal Xi sinc-Gram tails, moving cutoffs, source residual, or source spectral measure.
- `ClusteredExponentialMomentAnnihilator.lean` now proves unconditionally the exact rectangular
  Vandermonde annihilator and simultaneous degree-`< n` exponential Taylor cancellation used by
  the clustered-packet mechanism.  It is a dependency, not a formalization of SR-104's Xi-cluster
  existence or analytic remainder estimate.
- `CCMZeroExtendedFourierCorrelation.lean` closes CCM Lemma 2.3 from the literal source functions;
  this repairs the prior definitional gap between the zero-extended Fourier packet and
  `CCMPublishedRestrictedWeilMatrix.lean`'s sine/tent entries.

## Current hard boundary

Literature remains ahead of corpus at the unbounded-operator layer, not at finite scalar algebra.
The logarithmic compact-embedding, literal smooth-remainder regularity and `L²` block bound, and
source-locked four-block test form are now closed (last items provisionally beyond the committed cutoff). Exact
parity still requires a localized Weil-form/operator stack:

1. finite-part semiboundedness and the resulting complex localized Weil sesquilinear form on a
   genuine `L²(-a,a)` domain;
2. lower-semibounded closed-form representation/Friedrichs extension;
3. actual first-order derivative on the form completion, adjoint, deficiency indices, and von
   Neumann extensions;
4. actual characteristic Fourier function and spectral zero equivalence.
5. for Suzuki (2023), Theorem 1.4's converse, formal maximal-positive-aperture continuation and
   the source's uniform infinite Gram--Schmidt estimates producing a literal kernel vector at the
   boundary aperture when RH fails.

Until those objects exist, counting generic Schur, Cayley, CFC, or finite-matrix consequences as
Suzuki's theorems is theatre.
