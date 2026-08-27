# BM third-order phase-normalized causal-cut identity

- **ID:** HB-BM3-PNCC
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** failed `HB-BM3-OPT` · `hawking-bm-augmented-einstein-mode-evaluation.md` · current Lean causal-cut corpus
- **Statement:** `[CONJECTURE]` Hermitian phase-normalized retarded-minus-advanced projection of complete augmented Birmingham--Mokhtari `++-` Einstein--Teukolsky Schur source equals exact mixed-horizon optical section.

## Goal

Discharge physical hypotheses of corpus conditional causal-cut theorem using complete sourced BM
boundary problem. Establish normalization-invariant nonzero cut at every off-critical Xi fibre,
without assigning positivity to bare complex-frequency QNM coefficient.

This does not alone prove RH. A source-global law must still force retarded/advanced equality or
simultaneous solvability before optical zero-locus can force critical line.

## Gates

- [x] 0 → 1 in-progress: exact phase-covariant claim, source-pure attack, corpus/literature frontier audited
- [ ] 1 → 2 fully-proven: full augmented Einstein mode evaluation and boundary Green proof closed
- [ ] 2 → 3 formalized: exact physical theorem, targeted build, axiom and lint gates
- [ ] 3 → 4 publication-ready: standalone paper, source conventions, proof, Lean certificate, priority audit

## Exact frozen claim

Fix Xi divisor copy `q`, nonzero canonical theta amplitude `A`, and exact massless `d=4`
topological-AdS Birmingham--Mokhtari mode `p_A=A p_1` with real-field partner
`m_A=conj(A)m_1`. Let `L_aug`, `B_aug`, `C_aug` be first three derivatives of one gauge-fixed
bulk-plus-ingoing-horizon-plus-normalizable-AdS residual. Let `R^ret_{++},R^ret_{+-}` and advanced
counterparts be complete sourced inverses including stationary constraint closure. Let `ell_q` be
fixed unit-Wronskian augmented left target-QNM functional.

Write

\[
\Sigma_{\mathrm{ret/adv}}(A,q)
=\ell_q\!\left(
B(p_A,R^{\mathrm{ret/adv}}_{+-}B(p_A,m_A))
+B(m_A,R^{\mathrm{ret/adv}}_{++}(B(p_A,p_A)/2))
+C(p_A,p_A,m_A)/2\right).
\]

Frozen identity is

\[
\overline A\,[\Sigma_{\mathrm{ret}}(A,q)-\Sigma_{\mathrm{adv}}(A,q)]
=J^{\mathrm{BM}}_{+-}(q)\,
\left\|\Pi^{\mathrm{BM}}_{\mathrm{hor}}(A,q)\right\|^2,
\tag{PNCC}
\]

where `J^BM_{+-}(q)` is actual analytically continued mixed radial causal jump fixed by physical
ingoing/normalizable Green kernel, and `Pi^BM_hor` is corpus gauge-fixed horizon optical
projection with its BM Jost derivative normalization. No free nonzero factor may be inserted after
freezing.

Required consequences:

1. both sides scale as `|A|^4` and are U(1)-invariant;
2. `J^BM_{+-}(q) ≠ 0` unconditionally;
3. right side vanishes iff `Re(q)=1/2`;
4. on real-momentum Sturm slice only, chosen counterclockwise convention gives `i` times positive flux;
5. no positivity claim is made for analytically continued complex Xi momentum.

## Corpus-grounded frontier

- `[LEAN-PROVED]` `ThetaCuspHawkingCubicPhaseCovarianceOpticalNoGo.lean`: modal work is mandatory phase-zero observable and has exact sign classification.
- `[LEAN-PROVED]` `ThetaCuspHawkingTotalThirdOrderCokernelSchurSection.lean`: complete augmented Schur source and exact third-order channel formula.
- `[LEAN-PROVED]` `ThetaCuspHawkingTotalThirdOrderCausalCut.lean`: causal cut removes common direct third jet and is sum of two sourced response jumps.
- `[LEAN-PROVED, CONDITIONAL LANDING]` `ThetaCuspHawkingBMMixedHorizonCausalOpticalProducer.lean`: abstract response-incidence plus reciprocity hypotheses imply optical section and critical-line zero locus.
- `[LEAN-PROVED]` `ThetaCuspHawkingBMProjectiveCausalResponse.lean`: mixed scalar projective response is finite nonzero negative norm-square; common `Gamma(c)` pole is not physical gain.
- `[LEAN-PROVED]` `ThetaCuspHawkingBMMixedHorizonFrobeniusMonodromy.lean`: horizon-normalized logarithmic representative has explicit nonzero monodromy, but physical augmented landing remains a hypothesis.
- `[LEAN-PROVED]` `ThetaCuspHawkingAIMEThirdOrderSourceCohomology.lean`: exact complete third-order cohomology and cancellation alternatives.
- `[LEAN-PROVED]` `ThetaCuspHawkingAIMECrossBranchTeukolskyResidue.lean`: nonzero AIME component with exact physical boundary-Jost derivative.
- `[OPEN]` `hawking-bm-augmented-einstein-mode-evaluation.md`: horizon harmonic products, Kodama--Ishibashi reconstruction, sourced radial kernels, boundary jets, and target adjoint projection.

Mandatory corpus searches found no theorem discharging `(PNCC)` from actual BM augmented Einstein
data. Existing optical sections either define desired flux algebraically or assume exact response
and reciprocity identities.

## External frontier

- Birmingham--Mokhtari (`hep-th/0609028`) supplies exact linear gravitational QNMs, not nonlinear sourced projection.
- Green--Hollands--Sberna--Toomani--Zimmerman (`arXiv:2210.15935`) supplies conserved QNM bilinear/projection framework, not completeness or this topological-AdS cubic identity.
- Sberna et al. (`arXiv:2112.11168`) derive AIME mechanism, not complete third-order Einstein coefficient.
- Spiers--Pound--Moxon (`arXiv:2305.19332`) derive second-order Teukolsky sources.
- Neuser--Thiemann (`arXiv:2602.08125`) derive third-order Schwarzschild reduced Hamiltonian; topological-AdS BM polar/axial QNM projection remains future work.

No audited source proves `(PNCC)`.

## Hostile attack

- `FALSE` if physical projective cancellation removes mixed Frobenius jump from augmented inhomogeneous Green kernel.
- `FALSE` if `++` causal response contributes independent boundary discontinuity not absorbed by right side.
- `FALSE` if augmented left pairing yields an indefinite bilinear concomitant after Hermitian amplitude normalization.
- `FALSE` if cusp/AdS counterterms have non-Hermitian finite jump under FE/Schwarz involution.
- `FALSE` if target QNM and its FE/Schwarz partner do not land in one adjoint Green identity.
- `CIRCULAR` if any step assumes critical-line placement, real Xi momentum, or RH-equivalent global balance.
- `INCOMPLETE` if proved only for scalar master variable without reconstructing gauge-fixed metric, horizon constraint, and AdS boundary residual.
- Current verdict: `FAILS PROPOSED CHANNEL PROOF`; exact scalar equality survives only as an
  unproved cross-channel coincidence. Under variational cyclicity and Peierls skewness, mixed
  `+-` self-contraction cancels and polarized `++/--` pairing carries the cut.

## Proof programme

1. Fix one explicit gauge and augmented residual; derive `B_aug,C_aug` from Einstein action, horizon condition, and AdS counterterms.
2. Construct BM horizon harmonic product algebra and project `++`, `+-`, `++-` sources without scalar parity truncation.
3. Build retarded/advanced sourced Green kernels at exact composite frequencies; separate finite projective response from logarithmic horizon representative.
4. Derive truncated-domain Green identity before analytic continuation; prove direct third jet and conservative counterterms cancel from modal-work cut.
5. Match remaining horizon concomitant to BM Jost derivative and corpus optical projection with exact coefficient.
6. Continue two independent holomorphic mode/Schwarz fibres, then specialize to conjugate data.
   Ordinary norm square is nonholomorphic and cannot be continued as a one-variable identity.
7. Only after dependency closure, formalize `(PNCC)`; no placeholder physical hypotheses.

## Proven infrastructure

`ThetaCuspHawkingBMMixedHorizonIntegratedOpticalForm.lean` now proves, for every compact radial
interval `0<a≤b<1` and every twice differentiable forced solution of the exact mixed BM equation,

\[
J(b)-J(a)=\int_a^b w(z)\operatorname{Im}(\overline{y(z)}f(z))\,dz,
\qquad
J(z)=p(z)\operatorname{Im}(\overline{y(z)}y'(z)).
\]

This closes finite-radius integration of corpus local Sturm identity. Remaining hard step is not
calculus: prove horizon/AdS endpoint limits for actual sourced augmented Einstein solution and
identify resulting source work with complete phase-normalized `++-` cokernel cut.

`ThetaCuspHawkingBMMixedHorizonUnitWronskianMonodromy.lean` closes first horizon normalization
audit. If `N=2n+2k+2`, raw regular branch starts with `z^(N+1)`, and its Sturm Wronskian with
constant branch tends to `N+1`. Therefore raw log-monodromy coefficient `2πiκ` becomes
`(N+1)2πiκ` in leading unit-Wronskian basis. Positivity and nonvanishing survive. Any final
`(PNCC)` coefficient must use this factor or prove an exactly compensating adjoint normalization.

## No-go closure

- **Exact killing theorem/mechanism:** pending full sourced-kernel attack
- **Strongest positive survivor:** phase-covariant modal work and abstract cubic Peierls
  polarization law, both Lean-formalized
- **New insight:** under action cyclicity and Peierls skewness, mixed `+-` self-channel cancels;
  surviving carrier is polarized `++/--`, not scalar mixed Frobenius gain
- **Status:** frozen PNCC channel identity remains `[CONJECTURE] [OPEN CORE]`; replacement abstract
  law is `[LEAN-PROVED]` in `ThetaCuspHawkingCubicPeierlsPolarization.lean`

## Log

- 2026-08-27 — frozen after bare optical claim failed U(1) attack; corpus conditional theorem and projective-response no-go incorporated.
- 2026-08-27 — proved and Lean-formalized compact-interval integrated mixed BM optical identity; targeted build, axiom audit, and formal lint pass.
- 2026-08-27 — found and formalized exact `N+1` raw-to-unit-Wronskian Frobenius normalization; corpus monodromy coefficient alone is not yet unit-Wronskian causal coefficient.
- 2026-08-27 — Peierls hostile attack killed proposed one-channel proof: cyclicity makes mixed
  causal self-contraction zero and moves carrier to polarized `++/--` source pairing. Frozen PNCC
  can survive only through a new cross-channel identity; opened `HB-BM3-PPC`.
- 2026-08-27 — Lean no-go proves old conditional mixed-response/zero-`++`/reciprocity landing is
  incompatible off critical with any cyclic action and skew Peierls propagator. No direct physical
  weld to `ThetaCuspHawkingBMMixedHorizonCausalOpticalProducer.lean` remains.
