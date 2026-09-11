# Route L: original prime Green denominator in the full Xi norm

- **ID:** L-C51
- **Date:** 2026-09-12
- **Stage:** 3-formalized; all three final leaf audits passed
- **Depends on:** C46 full source packet; C49 literal Green identity; C50 retained boundary residues
- **RH status:** unproved

Chain: complete original Green/BV source → fixed physical-reader agreement
→ conormal vanishing → RH. Reader agreement remains the hard mathematical
gap. Before comparing the complete source, its original prime Green
resolvent must be admitted in the full Xi-indexed norm. Pointwise
nonvanishing of the denominator does not prove that admission.

## Candidate bound and paper argument

Proved: one constant C>0, independent of the original prime p and
actual Xi zero rho, satisfies

`norm((1-p^(-rho))^(-1)) <= C*(1+abs(Im rho))^2`.

The corpus theorem `Sieve.exists_zeta_uniform_strip_zero_free` supplies a
fixed L0>=1 and excludes zeros with
`Re(s)>=1-1/log(K)^2`, `abs(Im(s))<=K`, `log(K)>=L0`, and `s!=1`.
Apply it to the reflected actual zero `1-rho`, at
`K=exp(L0)+abs(Im rho)`. The original Xi strip and functional equation
must be used to prove all zero, height, and non-pole premises. This gives
`Re(rho)>1/log(K)^2` without critical-line placement.

For x>0, `exp(x)>=1+x` gives
`1/(1-exp(-x))<=1+1/x`. The reverse triangle inequality and
`norm(p^(-rho))=exp(-Re(rho)*log(p))` therefore bound the resolvent by
`1+1/(Re(rho)*log(p))`, at most `1+log(K)^2/log(2)` for every prime p.
Finally `log(K)<=K` and
`K<=max(exp(L0),1)*(1+abs(Im rho))` supply the claimed polynomial envelope.
These steps now pass Lean in `DeningerOriginalGreenXiResolventBound` under
default limits. No uniform positive lower bound on Re(rho), zero simplicity,
or pole deletion is asserted. The constant is independent of the original
prime and of the native Xi divisor point.

The actual Gaussian polynomial envelope and dominated convergence in the
original Xi norm pass Lean in `DeningerOriginalGreenGaussianEnvelope`.
The proof uses unconditional Xi Gaussian monomial summability at twice the
source time, not a lattice-Gaussian estimate or a changed norm. The next
dependent step is now scratch-verified in
`DeningerOriginalPrimeGreenXiAdmission`: it combines these results with the
actual C46 source-prefix estimate, constructs the literal C49 resolvent
field, and proves its full norm convergence. Original prime, multiplicity
copies, source coefficient, Gamma residue normalization, and Tate depth
are retained. No reweighting of the original completion norm is used.

## Full-source argument

The tempting shortcut, a uniform bound on the unweighted prefix vector,
does not control an unbounded diagonal inverse. The positive replacement
is a common coordinate envelope. Write G(q) for the actual reflected
Gaussian source, w(k) for the summable original-prime step weight, and
`B(a)=exp(2*sum_k w(k+1))`. The actual step theorem gives
`norm(F_(n+1)(q)) <= exp(2*w(n+1))*norm(F_n(q))`; the zero prefix is G.
Induction followed by the finite-sum-to-tsum bound gives
`norm(F_n(q)) <= B(a)*norm(G(q))` uniformly in n. Coordinate continuity
passes the same bound to the already-admitted actual source limit F.

For `t=abs(Im rho)` and `N=norm(xiSpectralPoint(q))^2`, the actual coordinate
identity gives `t^2<=N`, hence `(1+t)^4<=8*(1+N^2)`.
The square of the Gaussian source norm is the heat-term norm at twice
the source time. Unconditional summability of the degree-zero and
degree-two heat monomials therefore proves
`sum_q ((1+t)^2*norm(G(q)))^2 < infinity`, over every original multiplicity
copy. Together with the prime-uniform inverse bound this yields one
square-summable majorant for every `F_n(q)/(1-p^(-rho))` and its actual
limit `F(q)/(1-p^(-rho))`.

Each quotient is thus admitted to the original Xi Hilbert space.
Coordinate convergence and the common envelope dominate squared errors
by four times the envelope square. Tannery gives convergence of their
sum to zero; the existing exact lp norm-square formula proves full norm
convergence. The finite and completed quotient coordinates are identified
with the literal weighted Green integrals using C49's original
translation formula and proved integrability.

For each fixed original prime, the admitted coefficient multiplies its
ordinary-prime cycle atom and every native cofinal averaging packet.
The existing completed differential gives exactly the corresponding
full Xi-indexed graph vector. Its native-depth limit follows through the
existing continuous graph spread. Gamma residue normalization cancels
its original packet exactly, leaving the same nonzero coefficient.
The fixed physical transport still reads that coefficient times the
original fixed Sonin receiver. This graph construction does not identify
the complete two-ended BV boundary with the physical reader; that source
comparison remains the RH-bearing gap.

## Corpus and method audit

[Zero-margin search](route-l-green-zero-margin-search.json): generation
878155, coverage pending, partial at deadline/filter-and-judge. All 20
candidate statements and 20 source-method summaries were inspected. No
proof ideas or ingredient groups returned; applicability is source-only
and unchecked. The selected uniform strip method combines a high-height
lower bound with a compact low-height zero-free box. Its exact source and the multiplicative lower-strip proof have been read;
all actual-zero application premises now pass Lean. The separate
`XiWardZeroFreeMarginPrimeLogSampling` source was read through its
logarithmic margin proof; it currently states the centered strict-right
case. It cannot simply be applied to every Xi copy without the required
reflection/case argument.

Conditional shifted-zero bounds and definitions quantifying boundedness
over all zeros are not unconditional producers. Generated method prose
sometimes calls a definition a proof; the source declaration, not that
description, governs applicability.

[Gaussian search](route-l-green-gaussian-envelope-search.json), generation
878274, and [norm convergence search](route-l-green-lp-convergence-search.json),
generation 878309, were partial at deadline/filter-and-judge with coverage
pending. All 20 candidate statements and 20 method summaries in each report
were read. Neither returned proof ideas or ingredient groups. Integer-lattice
Gaussian bounds do not supply actual Xi-divisor summability. The exact
unconditional Xi heat monomial theorem was located in source and applied in
Lean. The selected Tannery theorem controls the sum of squared coordinate
errors; pointwise convergence without this domination is insufficient.

[Source-envelope search](route-l-green-source-envelope-search.json),
generation 878422, was partial during text/source retrieval and reranking.
Its coverage snapshot inventoried 57,017 files (47,410 Lean, 9,607 prose),
with compiler metadata predominantly pending. All 20 candidates, 20 method
summaries, and the proposed ingredient group were inspected. The proposed
inner-product/coordinate-norm group does not produce a summable Gaussian
coordinate envelope from a uniform whole-vector norm bound. The existing
actual prime-step coordinate theorem is instead exposed and reused, with
its proof unchanged, avoiding duplicate prime-factor calculus.

## Broad literature transfer audit

Single-word search `coercivity` selected the September 7, 2026 paper
[Frequency Domain Biot–Allard Equations](https://arxiv.org/html/2609.07388v1).
The model formulations and Appendix C/D continuity, adjointness, and
coercivity arguments were inspected. Lemma 6 eliminates boundary integrals
using homogeneous boundary conditions; those premises are unavailable for
the retained nonzero original boundary. Dynamic adjointness also requires
the stated Hermitian coefficient. No skew-adjointness or coercivity claim
was transferred to the actual Green source. No numerical experiments were
used.

## Lean proof optimization and verification

The application reuses the existing prime-step coordinate theorem. Its
proof is unchanged; its public name and both existing references were
updated together. A broad simplification of the scaled Gaussian envelope
reached the default 200,000-heartbeat limit. Replacing it with an explicitly
typed summability statement and `Summable.congr` applied to `mul_pow`
removed the timeout. An explicit equality for the zeroth Mellin-jet
function also avoids relying on simplification of an unapplied function.
No heartbeat or recursion-limit increase was introduced.

All three new modules and the exposed source estimate passed foreground
scratch checking with `lake env lean`. Sequential final audits passed:

- `lake build GaloisForLFunctions.RHTower.DeningerOriginalGreenXiResolventBound`
- `lake build GaloisForLFunctions.RHTower.DeningerOriginalGreenGaussianEnvelope`
- `lake build GaloisForLFunctions.RHTower.DeningerOriginalPrimeGreenXiAdmission`

Only the named new modules and the shared source module rebuilt; dependency
messages were replayed. One Lean process ran at a time. No full or umbrella
build was run. All 22 new public declarations and the shared source theorem
are indexed; all three new imports occur once in `RHTower.lean`. Byte-identical
workspace scratch copies were removed after the formal modules were retained.

Logs: [denominator audit](route-l-green-xi-bound-build.log),
[Gaussian audit](route-l-green-gaussian-envelope-build.log),
[full admission audit](route-l-green-xi-admission-build.log),
[index](route-l-green-xi-admission-index.log),
[global lint](route-l-green-xi-admission-lint.log).

Global lint failed on eight unrelated modules unreachable from their own
theorem-area umbrellas: `RHTower.ThetaCuspHawkingBMHorizonCoordinateJets`,
`RHTower.ThetaCuspHawkingBMPrincipalChannelHorizonJet`,
`RHTower.ThetaCuspHawkingBMSelfChannelHorizonJet`,
`RHTower.ThetaCuspHawkingBMTemporalCurrentHorizonJet`,
`HTGeometry.AnalyticJetGerm`, `HTGeometry.ElementaryHorizonJets`,
`HTGeometry.SecondEndpointMellinLaurentInterchange`, and
`HTGeometry.UniformSecondOrderJet`. None was edited for C51. The new C51
modules are wired; this is not a passed global lint gate.

## Next comparison audit

The [complete-boundary deep search](route-l-green-complete-boundary-pairing-search.json)
at generation 878542 returned no candidates, methods, or ingredient groups
before its partial retrieval deadline. Its inventory snapshot covered
57,023 files, with most compiler metadata pending. The broader
[lexical search](route-l-green-boundary-pairing-lexical.json) returned 20
declarations and five exploration hits; all source statements were read.
The selected second-derivative half-line identity retains all four endpoint
limits. The Stein identity retains the finite endpoint and assumes the
infinite endpoint vanishes. The critical Mellin–Stieltjes identity assumes
its terminal source value vanishes. None produces that vanishing for this
complete source. The finite ordered-word identity retains its terminal
source boundary and carry exactly. Their relevant proofs were read; no
new physical-reader identification follows from these templates alone.
The next attack must evaluate the retained two-ended source pairing and
identify its actual physical image, with no discarded endpoint term.
