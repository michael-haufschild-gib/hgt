# HB Peierls stationary-channel elimination

- **ID:** HB-PEIERLS-PM-KILL
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` (read-only) · HB full `++-` Einstein--Teukolsky causal-cut burden
- **Statement:** In every cyclic variational Peierls realization of the HB `++-` cut, the stationary `+-` projected response is identically zero, so the full cut vanishes exactly when the radiative `++` projection vanishes.

## Goal

Kill nontrivial stationary/radiative anti-alignment in the RH chain

`Xi divisor -> AIME/simple-pole source -> full ++- causal cut -> BM optical/clock defect -> RH`.

The preceding direct-third-jet theorem reduced cancellation to anti-alignment of stationary `+-`
and radiative `++` projected response jumps.  This theorem removes the stationary term from every
physical route whose mixed response jump comes from the causal propagator of the same cyclic action.
The remaining HB burden is one radiative `++` left-cokernel projection, not a two-channel phase
matching problem.

## Gates

- [x] 0 → 1  in-progress: exact corpus-derived statement, route scope, hostile boundary, proof idea
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, targeted `lake build` green, axiom audit
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Corpus audit

- `ThetaCuspHawkingHBDirectThirdJetCausalCutRigidity`: full cut zero iff projected `+-` and `++`
  response jumps anti-align; common direct cubic jets have no cancellation power.
- `ThetaCuspHawkingCubicPeierlsPolarization`:
  `d4GaugeFixedTeukolskyPeierls_mixed_self_eq_zero` proves the mixed quadratic source contracts
  trivially with its own Peierls image under Hessian symmetry, third-variation cyclicity, and causal
  skewness.
- `ThetaCuspHawkingBMMixedOpticalPeierlsNoGo` uses that identity only to derive a zero-cut corollary
  after separately assuming the `++` sourced jump vanishes.  It does not classify the full cut for
  arbitrary radiative response or kill anti-alignment.
- `ThetaCuspHawkingBMSecondHarmonicComplexOrientationClassification` and
  `ThetaCuspHawkingBMCrossPairResponseCompensator` falsify any phase-only argument: complex and even
  division-free reflection-covariant weights can cancel nontrivially.
- Corpus search found no theorem equating the general physical total cut to its radiative term or
  packaging the stationary/radiative anti-alignment route as killed.

## Literature audit (through 2026-08-31)

- Khavkine, arXiv:1402.1282, proves the covariant Peierls/Poisson construction under precise gauge,
  constraint, and hyperbolicity conditions; causal antisymmetry is general infrastructure, not this
  nonlinear channel-elimination theorem.
- Green--Hollands--Sberna--Toomani--Zimmerman, arXiv:2210.15935, constructs conserved Kerr QNM
  bilinear forms and excitation projections; it proposes nonlinear mode-coupling applications but
  does not derive a cubic retarded-minus-advanced channel classification.
- Spiers--Pound--Moxon, arXiv:2305.19332, constructs the second-order Kerr Teukolsky nonlinear source
  and gauge control; no Peierls self-pairing reduction of a third-order causal cut.
- Aruquipa--Casals--Nolan, arXiv:2604.21219, derives exact pieces of the retarded Schwarzschild
  Teukolsky Green function; no nonlinear advanced-minus-retarded channel elimination.
- Targeted searches for `Peierls nonlinear Teukolsky`, `Peierls second-order Teukolsky`, and
  stationary/second-harmonic retarded--advanced cancellation found no exact theorem matching this
  statement.

## Heavy conjecture loop and hostile audit

- **C0 (failed):** both physical response channels lie on one signed real ray, hence cannot
  anti-align.  Corpus disproves the needed premise: the `++` channel and left-QNM projection retain
  complex phase, and explicit cross-pair response corrections cancel reflected currents.
- **C1 (failed):** arbitrary left-response phase still forbids anti-alignment.  False at the abstract
  level: complex cancellation has a one-dimensional hyperplane on every ordered reflection pair.
- **C2 (selected):** impose only source-derived physical structure.  Symmetry of the Einstein
  Hessian makes the mixed residual equal `B(p,m)`; cyclicity moves the target leg onto the propagated
  mixed source; Peierls skewness then makes the term its own negative.  No statement about the phase
  or sign of the radiative channel is needed.

Hostile boundaries:

- False for arbitrary unrelated `+-` response maps: the identity specifically requires their
  retarded-minus-advanced jump to be the causal propagator inducing the Peierls bracket.
- False without cyclicity/source-derived left incidence: an arbitrary cokernel covector can assign
  any complex value to the stationary response.
- Does not kill the radiative `++` projection.  That is the sole positive survivor and next HB
  producer burden.

## Approach

Expand the total cokernel cut as `M + P`, with

`M = pairing(m, B(p, Delta(q_+-)))`

and `P` the arbitrary projected `++` response jump.  Hessian symmetry gives `q_+- = B(p,m)` in the
corpus normalization.  Cyclicity rewrites `M` as the Peierls source self-pairing of `q_+-`; skewness
gives `M=-M`, hence `M=0` over `C`.  Therefore the total cut equals `P`, so its zero and nonzero loci
are exactly those of the radiative projection.

## Paper proof `[PROVED HERE]`

Let `q = (B(p,m)+B(m,p))/2` be the mixed quadratic residual and let
`Delta = R_+-^ret-R_+-^adv`.  Hessian symmetry gives `B(m,p)=B(p,m)`, hence `q=B(p,m)`.  Write the
stationary projected contribution as

`M = pairing(m, B(p, Delta q))`.

Cyclicity of the third action variation states

`pairing(x,B(y,z)) = pairing(z,B(x,y))`.

With `(x,y,z)=(m,p,Delta q)` and Hessian symmetry, this gives

`M = pairing(Delta q,B(m,p)) = pairing(Delta q,q)`.

By definition this is the Peierls source pairing `Omega(q,q)`.  Causal skewness gives
`Omega(q,q)=-Omega(q,q)`, so `2 Omega(q,q)=0`; since the scalar field is `C`, `M=0`.

The exact total-causal-cut expansion from the corpus is

`K = M + pairing(m, B(m,(R_++^ret-R_++^adv)q_++))`.

Substituting `M=0` proves exact equality of `K` with the radiative term.  Equality immediately gives
both zero-locus and nonzero-locus equivalences.  Combining the zero equivalence with the preceding
anti-alignment classification shows that physical stationary/radiative anti-alignment occurs iff
the radiative term itself is zero; no nonzero two-channel cancellation survives.

All inputs are structural laws defining the route class.  No spectral estimate, response sign,
phase choice, division, or RH premise enters the proof.

## No-go closure

- **Exact killing theorem/mechanism:** Peierls skewness annihilates the entire stationary arm before
  it can anti-align with radiative response; Lean theorem
  `d4HBPeierlsStationaryRadiativeAntiAlignmentRouteKilled`.
- **Strongest positive survivor:** exact equality of full HB cut with the projected radiative `++`
  response jump, including zero/nonzero equivalences.
- **New insight:** physical HB cancellation is not two-channel interference.  Once response incidence
  is derived from one cyclic action, only second-harmonic radiation can carry the causal cut.
- **Status:** paper and Lean proved in
  `ThetaCuspHawkingHBPeierlsStationaryChannelElimination`; direct `lake env lean` and targeted
  `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingHBPeierlsStationaryChannelElimination`
  passed; axioms only `propext`, `Classical.choice`, `Quot.sound`; umbrella wired.  Formal lint
  reaches the module and reports only unrelated concurrently owned unreachable modules
  `HedenmalmThetaSourceFunctionalEquationRootCurrentTransport` and
  `ConstitutiveEvenPositiveWeightedReflection`.

## Log

- 2026-08-31 — C0 and C1 falsified by corpus complex-orientation and cross-pair countermodels.
- 2026-08-31 — C2 selected: exact physical stationary-channel elimination tied to HB→RH chain.
- 2026-08-31 — paper proof closed; no analytic or spectral dependency remains.
- 2026-08-31 — exact equality, zero/nonzero laws, anti-alignment classification, and closed route-kill
  certificate formalized; targeted build and axiom audit passed.
