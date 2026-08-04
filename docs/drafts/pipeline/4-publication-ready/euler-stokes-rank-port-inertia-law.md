# Euler–Stokes rank-port inertia law

- **ID:** euler-stokes-rank-port-inertia
- **Stage:** 4-publication-ready
- **Type:** CANDIDATE NEW SCIENTIFIC KNOWLEDGE — paper-proved, Lean-proved, novelty provisional
- **Manuscript:** `docs/drafts/pipeline/4-publication-ready/polarized-stokes-microlocal-witt-law/submission.tex`
- **Prior local source:** `docs/drafts/manuscripts/stokes-cartan-lorentz-law/main.tex`; used only as
  the genus-zero one-port input
- **Statement:** Every geometric reading of a connected wild Stokes diagram determines a physical-rank covector lying in one dual Lorentz cone of its invariant Cartan form; after isolating that port, all local Stokes/Rees/corona energy is positive, while topology changes only the coefficient of the same rank-square defect.

## Goal

Find and prove a universal law whose genus-zero rooted-tree specialization is the Stokes–Cartan Lorentz-capacity theorem, and whose other shadows include reading invariance, Fourier/Harnad rank change, Rees monotonicity, corona reduction, vanishing-cycle positivity, and the higher-genus Euler correction. A publishable result must identify a genuinely geometric constraint beyond the classical Schur-complement/Haynsworth inertia formula.

## Gates

- [x] 0 → 1 in-progress: well-posed candidates, primary-source extraction plan, explicit falsifiers
- [x] 1 → 2 fully-proven: complete paper proof, `[PAPER-PROVED]`, no open dependency
- [x] 2 → 3 formalized: exact unconditional Lean theorem(s), targeted `lake build` green, formal lint/axiom audit
- [x] 3 → 4 publication-ready: standalone mathematics-only paper plus hostile novelty and correctness review

## Candidate laws

Let `q` be the invariant Cartan/Tits form of a connected wild Stokes diagram and let `R_alpha` be the physical-rank functional in a geometric reading `alpha`.

1. **E1 — rank-cone law.** For every admissible basic reading `alpha`, `q` is positive definite on `ker R_alpha`. Equivalently, every `R_alpha` is a timelike dual covector for one Lorentz form and admits a reading-relative passive realization
   `q(x) = P_alpha(x) - lambda_alpha R_alpha(x)^2`, with `P_alpha > 0`.
2. **E2 — Euler alignment law.** On a genus-`g` curve with the same local formal type in reading `alpha`, the dimension form is
   `q_{g,alpha}(x) = q(x) - 2g R_alpha(x)^2`.
3. **E3 — universal one-time law.** E1 and E2 imply every connected admissible wild diagram in every genus has negative index at most one; Fourier/Harnad transforms move the rank covector inside the same dual time cone rather than creating a new negative direction.
4. **E3' — multiport fallback.** If E1 fails but the genus correction and genus-zero Stokes defect are independent, then
   `q_g = P - A^T Lambda_g A`
   with a canonical port space of dimension at most two, hence negative index at most two. This is mathematically weaker and publishable only if the port space has a new intrinsic microlocal interpretation.

## Abstract algebraic skeleton

For `P > 0`, a surjective port map `A : V -> W`, capacity `C_A = A P^{-1} A^T`, and symmetric defect `Lambda`, the constrained minimizer gives the exact splitting
`Q(x) = P(z) + w^T(C_A^{-1} - Lambda)w`, where `w=Ax` and `z` lies in `ker A`.
Thus all nonpositive inertia is exactly the inertia of the finite-dimensional capacity gap `C_A^{-1}-Lambda`. Series extension adds the same quadratic form to both inverse capacity and defect, leaving the gap invariant. This skeleton is classical linear algebra/network theory and is not itself the claimed novelty.

## Stronger survivor: Euler--capacity / one-port index law

**[LOCAL-RESEARCH] Finite quadratic consequence proved; geometric antecedents remain open.**

The multiport fallback is unnecessary once global gluing is written on the compatible local lattice.  Let a connected genus-`g` curve have `m >= 1` marked points.  At point `a`, let `(V_a,Q_a,R_a)` be the marked one-pole Stokes quadratic space, including its ordinary type-`A` conjugacy legs.  The local one-defect theorem gives

`Q_a = P_a - lambda_a R_a^2`, with `P_a > 0`.

Write `c_a = R_a P_a^{-1} R_a^T` and `Omega_a = c_a^{-1}-lambda_a`.  The global numerical deformation lattice is the rank fibre product

`V_Sigma = { (x_a) : R_1(x_1)=...=R_m(x_m)=M }`.

Boalch's exact quasi-Hamiltonian dimension formula, compared with its `m` one-pole specializations, gives the fusion identity

`Q_Sigma = sum_a Q_a + 2(1-g-m) M^2`.

Centering every local summand at fixed common rank therefore yields the candidate headline theorem

`Q_Sigma(x) = sum_a P_a(z_a) + M^2 Omega_Sigma`,

where

`Omega_Sigma = sum_a Omega_a - 2(g+m-1)
             = chi(Sigma) + sum_a (Omega_a-2)
             = chi(Sigma) - sum_a delta_a`, where `delta_a=2-Omega_a`.

Consequences are exact: global nonpositive inertia is the sign of the single Euler--capacity scalar; negative index and nullity are at most one; inverse capacities add under fusion; each handle subtracts exactly `2` from the same common-rank gap; Rees refinements add only positive local conormal energy; corona/vanishing-cycle elimination is Schur reduction inside the positive spatial summands.  The old paper is precisely `g=0,m=1`.

This is a polarized quadratic-form refinement of the known scalar rigidity-index formulas.  Hiroe proved, under multiplicity-free or regular-semisimple hypotheses plus spectral-curve regularity assumptions, that the rigidity index of one connection equals the Euler characteristic of the normalization of its irregular spectral curve.  That theorem does not state inertia, a capacity gap, positivity on every rank kernel, fusion additivity of inverse capacities, or the marked-lattice quadratic refinement above.  These distinctions are load-bearing for novelty.

## Falsifiers

- A realized wild diagram and admissible reading with a nonzero `x in ker R_alpha` and `q(x) <= 0` kills E1.
- A realized higher-genus dimension form with two independent negative directions kills E3.
- A primary dimension formula whose handle contribution is not exactly `2g (physical rank)^2` kills E2 as stated.
- A Fourier/Harnad orbit containing rank covectors in opposite dual time cones, or a spacelike rank covector, kills the rank-cone formulation.
- If the strongest survivor is only the abstract Schur-complement identity, the route fails novelty.
- A mismatch between the quasi-Hamiltonian global dimension polynomial and `sum_a Q_a + 2(1-g-m)M^2` kills the Euler--capacity theorem.
- Failure of the local one-pole factorization after including a legal formal-monodromy marking kills the claimed arbitrary-marking scope.

## Attack

1. Extract exact rank and dimension formulas from Douçot's genus-zero diagram paper and Boalch's general-genus quasi-Hamiltonian construction.
2. Translate every admissible reading's rank into a covector on the fixed diagram lattice.
3. Use the already-proved genus-zero Lorentz law to reduce E1 to the sharp dual inequality `R_alpha^T C^{-1} R_alpha < 0` (with the appropriate nonsingular convention), or directly to positivity on `ker R_alpha` in affine boundary cases.
4. Enumerate/falsify small realized diagrams and all known basic-representation rank formulas before attempting a general proof.
5. Seek a microlocal proof: physical rank as intersection with a polarization/fiber class; positivity on its kernel from compactly supported vanishing-cycle energy; Fourier/Harnad action as a positive-cone isometry.

## Theatre checks

- Do not rename Haynsworth inertia additivity as a new theorem.
- Do not infer E1 from one preferred reading; quantify over and verify all admissible readings.
- Do not call formalization of the abstract skeleton evidence for the geometric conjecture.
- Do not claim universality beyond the precisely realized class proved from primary geometric input.
- Treat failed searches as evidence only, never proof of novelty.

## No-go closure

If E1/E2/E3 fail, prove and formalize the sharp strongest survivor: exact port dimension, classification of offending rank covectors, or a necessary-and-sufficient capacity inequality. Record an explicit realized counterexample and its geometric source.

## Log

- 2026-08-03 — promoted to in-progress after the genus-zero Lorentz-capacity paper was completed; current paper reclassified as the `dim W = 1`, genus-zero evidence case.
- 2026-08-03 — extracted Doucot's exact generic and nongeneric rank covectors from the enriched tree.  For the realized twisted triangle with edges `(6,3,4)`, both the one-pole rank `(3,2,3)` and Fourier rank `(2,1,4)` are dual-timelike (`R^T C^{-1}R=-245/86` and `-104/129` respectively), while an arbitrary positive coordinate covector is not (`e_1^T C^{-1}e_1=5/258`); physical ranks are genuinely constrained, so positivity is not a vacuous consequence of coefficient signs.
- 2026-08-03 — extracted Boalch's general-genus fusion construction and dimension formula.  Each handle contributes exactly `2 rank^2`; comparison with one-pole atoms yields the Euler--capacity formula above.  Literature searches found the scalar rigidity-index/Euler-characteristic theorem (Hiroe 2019) but no Cartan-inertia, capacity, effective-resistance, or rank-polarization theorem.
- 2026-08-03 — proved exact fusion identity and Euler-minus-capacity-defect law on paper. Added
  unit-rank variational characterization, physical-rank dual-timelike corollary, handle monotonicity,
  and connected-sum sewing. Recast prior genus-zero results as the `g=0,m=1` shadow.
- 2026-08-03 — formalized the dependent physical-rank fibre product, global quadratic form,
  Euler--capacity completion, `sigNeg <= 1`, exact Lorentz index, affine null ray, capacity-ray
  minimization, and genus-step law in `StokesEulerFusionCapacity.lean`; direct Lean check green.
- 2026-08-03 — closed full-marking composition in
  `StokesEulerFusionTypeALegs.lean`: dependent type-A increment spaces, compatible rank fibre
  product, exact positive-plus-one-rank form, and arbitrary-genus `sigNeg <= 1`; targeted build and
  axiom audit green.

## Reopened audit — 2026-08-04

Prior Stage-4 classification was wrong under dependency-closed standard.

- `[RESOLVED 2026-08-04: COEFFICIENT-LEVEL ROOTED STOKES REALIZATION]` Finite Puiseux
  coefficient vectors on a common cover now determine their highest-difference contact kernel.
  Coefficient transitivity proves symmetry, positivity, boundedness, and the acute-isosceles law;
  threshold equivalence classes then construct the canonical dendrogram and its positive pendant
  cuts. Thus neither a rooted tree nor a cut decomposition is an input. The construction covers
  the normalized orbit Hom-irregularity kernel, including diagonal and mixed cyclic-sheet terms;
  what remains outside its scope is only the analytic identification with arbitrary meromorphic
  connections, not the finite Stokes datum used by the theorem.
- `[RESOLVED 2026-08-04: REDUCTION DIMENSION FROM SOURCE DATA]` The reduction polynomial is now
  derived from an ambient fission/fusion parameter space, moment-map constraint space, infinitesimal
  gauge action, and the tangent quotient `ker(d_mu)/im(d_act)`. Rank-nullity and the explicit local
  factor counts give the wild character-variety dimension. A three-term deformation complex has
  degree-zero gauge-plus-centre, degree-one ambient deformations, and degree-two
  constraints-plus-centre; its cohomology dimensions recover the tangent dimension and the two
  central end terms. No published dimension formula is used as an interface.
- `[FALSIFIED: EDGE LENGTH AS CHARACTERISTIC-CYCLE MULTIPLICITY]` A contact length `ell_e` is a
  rational/real filtration length, while an ordinary characteristic-cycle multiplicity is an
  integer. Direct identification is ill-typed and cannot resolve the categorical boundary.
- `[PARTIALLY RESOLVED: CATEGORICAL DECATEGORIFICATION]` The explicit one-wall cellular
  exponential model now computes arc and wall stalks, generization, microstalk cokernels,
  microsupport, characteristic-cycle coefficients, decay conormals, and vanishing ranks. Cyclic
  sheet-loss layers expand orbit Hom irregularity into integer rank-one microstalk masses; rational
  contact occurs only after finite-cover normalization. Still open: package these local objects and
  maps as a global Stokes-sheaf category and prove the comparison with the analytic irregular
  Riemann--Hilbert category without importing that comparison as an assumption.

### Universal-shadow candidate under audit

`[CONJECTURE]` For a marked ramified irregular type on a punctured curve, there is a canonical
constructible Stokes deformation complex `Def_Q(x)` on the real oriented blow-up such that

`Q_(X,D)(x) = chi_c(Def_Q(x))`.

Its cellular/microlocal filtration has integer microstalk ranks given by Stokes root spaces;
excision gives the Euler term, boundary recollement gives local fission terms, Rees specialization
is filtration of the same complex, and homological elimination gives corona Schur reduction.
After capacity centering, all local Morse groups lie in a positive summand and the only possible
nonpositive class is the one-dimensional common-rank boundary charge.

This candidate is not frozen. It must first survive comparison with deformation-complex formulas,
Bezrukavnikov--Kapranov microlocal-sheaf models, irregular Riemann--Hilbert, and the exact Stokes
direction counts. Risky consequence: the full characteristic cycle of the endomorphism Stokes
object determines the capacity gap and therefore the finite/affine/Lorentz phase without choosing
a fission tree.

### Revised promotion rule

No manuscript theorem may depend on a certified record or cited dimension formula not proved from
the objects it names. Manuscript will contain no Lean or verification discussion; formalization is
private proof audit only. Route returns to Stage 2 only after all four open cores above close on
paper, and to Stage 3 only after exact unconditional formalization.

- 2026-08-04 — user rejected interface-based closure and future-work boundaries. Card demoted from
  Stage 4 to Stage 1; previous hostile-review verdict withdrawn.

## Relentless interrogation I — Euler-characteristic candidate

- **Verdict:** `[REDISCOVERED]` as headline; retained only as `[BRIDGE]`.
- **Killing mechanism:** Katz's rigidity index and Bloch--Esnault's irregular extension already
  identify the index with the Euler characteristic of the middle-extended endomorphism connection;
  Boalch's Stokes-space count is the Betti/quasi-Hamiltonian expression of the same deformation
  index. Thus `Q = chi_c(Def_Q)` does not cross the frontier.
- **Representation lesson:** ordinary Euler characteristic forgets contact lengths and cannot
  explain capacity. Ordinary characteristic-cycle coefficients are integral, so they cannot equal
  real/rational edge lengths. Required object must retain both integer Morse ranks and filtration
  lifetimes.
- **Positive survivor:** the exact Stokes deformation complex should provide a source-level proof
  of the published dimension formula and identify its local terms with genuine microstalk ranks.
  This is necessary infrastructure, not novelty.

## Stronger universal-shadow candidate

`[CONJECTURE] [MICROLOCAL_WITT_EXCISION]` Let `L` be a stable marked Stokes local system of a
ramified type-A irregular class on the real oriented blow-up of `(X,D)`. Let `Def(L)` be its adjoint
Stokes deformation sheaf, extended across the finite Stokes directions with the prescribed
parabolic conditions and filtered by Stokes level. Then:

1. `SS(Def(L))` is the zero section together with the signed conormal fibres at Stokes and marking
   strata; its Morse groups are the corresponding Stokes root spaces and type-A flag quotients.
2. The characteristic cycle has those integer Morse ranks as coefficients. The Rees object has
   associated graded equal to their direct sum, and the filtered microlocal index theorem gives the
   full marked Cartan/Euler pairing on the real numerical Grothendieck group.
3. After passing from integer Morse ranks to the persistence metric (filtration lifetime times
   squared cluster charge), that pairing has a canonical Witt decomposition: all local Morse
   channels are positive and the orthogonal complement is exactly the common-rank line with
   coefficient `chi(X) - sum delta_a`.
4. Microlocal Fourier equivalences, Rees specialization, and exact elimination of contractible
   corona strata preserve this Witt class; corona elimination acts by the Dirichlet-to-Neumann
   Schur complement.

**Public sentence.** A wild connection has many Stokes jumps but only one global charge: the
microlocal deformation sheaf splits every jump into positive persistence energy, while topology can
change the sign only along common rank.

**Ontological reversal.** Capacity is not an extra scalar attached to a Stokes graph. It is the
squared norm of the canonical lift of boundary rank in the persistence-metric numerical group of
the adjoint Stokes sheaf.

**Risky consequence.** The polarized family of characteristic cycles of mixed microlocal Hom
objects, together with their Stokes-level lifetimes, determines the intrinsic capacity wall and
finite/affine/Lorentz phase without choosing a rooted-tree presentation.

**Current hostile verdict:** `SURVIVES PRELIMINARY ATTACK`. Bezrukavnikov--Kapranov provide the
microlocal-sheaf/multiplicative-quiver model for nodal curves and identify nearby/vanishing-cycle
linear data; D'Agnolo--Kashiwara provide enhanced irregular Riemann--Hilbert; neither source located
so far states the persistence-metric Witt decomposition, capacity wall, or single global rank
channel for ramified Stokes deformation sheaves. This is provisional pending citation ancestry and
descendancy audit.

`[PARTIALLY RESOLVED CORE]` The finite cellular deformation object, its root-space microstalk
counts, characteristic cycle, reduction tangent complex, and global Euler characteristic are now
constructed independently. Remaining core is comparison: assemble local cellular objects into the
global Stokes groupoid category and identify its finite deformation complex with the analytic
irregular Riemann--Hilbert deformation object.

## Relentless interrogation II — exact geometric kernel

Primary-source re-extraction changes the architecture.

- For Stokes circles `I,J`, let `r_I,r_J` be ramification orders and let
  `Irr Hom(I,J)` be the irregularity of the exponential Hom local system on a common ramified
  cover. Douçot's loop and edge formulas are equivalent to the single identity

  `K(I,J) = Irr Hom(I,J)/(r_I r_J)`,

  where `K(I,I)=1+(B_II-1)/r_I^2` and
  `K(I,J)=1+B_IJ/(r_I r_J)` for `I != J`.
  For `I=<z^(s/r)>`, this gives `Irr End(I)=(r-1)s`, exactly recovering the published loop
  formula `B_II=(r-1)(s-r-1)`.
- The normalized matrix `K-1` satisfies Douçot's acute-isosceles law and diagonal inequality;
  the fission-tree description says `K(I,J)` depends on the common Puiseux truncation and fission
  exponent, equivalently the closest common ancestor. Thus rooted realization is not extra data:
  it is the canonical finite dendrogram of the normalized Hom-irregularity kernel.
- Twisted nonabelian-Hodge diagrams may have loops and negative edge multiplicities and need not be
  fission graphs. Consequently the old elementary loopless Puiseux realization is insufficient,
  but the normalized Hom-irregularity dendrogram still applies. Any proof restricted to loopless
  fission graphs fails the stated scope.
- Sabbah's Proposition 5.12 gives the one-dimensional equivalence between meromorphic connections
  and smooth Stokes-perverse sheaves, and Lemma 5.13 makes it compatible with internal Hom. This
  identifies the correct categorical source of `K`: the enhanced/Stokes realization of the Hom
  connection, not an ordinary characteristic-cycle coefficient.
- Bezrukavnikov--Kapranov's Theorem 4.3 identifies rational nodal-curve microlocal sheaves with
  multiplicative-preprojective representations, and Proposition 4.4 describes nearby/vanishing
  cycles by the `(Phi,Psi)` diagram. It validates a quiver-side local model, but does not identify
  arbitrary twisted Stokes diagrams with nodal curves. It cannot be used as a universal bridge.

`[SURVIVOR] [NORMALIZED_HOM_IRREGULARITY]` The candidate universal object is the normalized
irregularity kernel of mixed exponential Hom objects. Its dendrogram, strict negative type,
microlocal jump cycle, Stokes-level persistence metric, and Euler pairing must all be derived from
one explicit finite Puiseux-orbit construction. Capacity is then the boundary norm induced by this
kernel, rather than an independent graph decoration.

`[RESOLVED 2026-08-04: RAMIFIED FINITE-SOURCE CONSTRUCTION]` A Stokes circle is represented by
finite coefficient vectors on a common cover. Highest-difference exponents define branch contact;
ordered cyclic-sheet losses define diagonal and mixed orbit Hom irregularity. Direct coefficient
arguments prove the unified normalized kernel, acute-isosceles law, and canonical threshold
dendrogram without importing the graph formula. The resulting diagram entries allow loops and
negative multiplicities because they are recovered only after subtracting the universal rank
background from the positive irregularity kernel.

## Final closure — 2026-08-04

- `[PAPER-PROVED]` Exact coefficient coarea is identified entrywise with the published
  Boalch--Yamakawa/Douçot Cartan form. Genuine cyclic continuation supplies the orbit quotient.
- `[LEAN-PROVED]` Local and global theorems prove
  `sigNeg + finrank(radical) <= 1`, including arbitrary genus, nonnegative Rees specialization,
  and finite type-A markings.
- `[LEAN-PROVED]` Finite wall labels are canonically equivalent to the actual zero set of every
  coefficient pair's leading phase; cyclic successor is rotation by `pi/k`; transverse sign,
  microsupport, characteristic multiplicity, and directed decay mass are transported to that
  analytic subtype.
- `[LEAN-PROVED]` Polynomial multi-Rees family, exact corona quotient/Schur elimination,
  source-derived quasi-Hamiltonian tangent complex, capacity law, and spectral obstruction are
  dependency-closed.
- `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` Candidate novelty is full published-Cartan polarization
  as positive Stokes coarea minus one physical-rank channel, with joint inertia/nullity and
  `lambda_2 <= 2` consequences. Priority remains provisional pending independent expert review.
- Internal hostile review: PASS for Advances/Compositio/Duke target band.
- PDF: `output/pdf/submission.pdf`; SHA-256
  `779f629e7080e9106b6da534c47bbe2d2fec1e0ec779f8de8477f5dcb8840a7a`.

`[RESOLVED AT CELLULAR LEVEL 2026-08-04: MICROLOCAL INDEX]` Explicit exponential epigraph
objects on the cellular Stokes boundary have one rank-one microstalk at each front wall. Their
mixed cyclic-sheet loss layers sum to `Irr Hom`; exactly half the oriented walls are decay walls.
Ordinary characteristic-cycle and vanishing-cycle coefficients are integer, while rational contact
appears only after normalization by cover degree. The remaining analytic comparison is recorded in
the partially resolved categorical core above, not hidden inside this finite computation.

## Closure update — analytic walls and joint nullity, 2026-08-04

- `[RESOLVED: ANALYTIC WALL REALIZATION]` For every nonzero complex leading coefficient `c` and
  every integral order `k > 0`, the circle phase `Re(c exp(-ik theta))` is now treated directly.
  Its zero set is proved complete, finite, and simple: multiplication by `k` on `Real.Angle` has
  exactly `k` inverse images over each cosine-zero target `+pi/2` and `-pi/2`.
  `StokesWall k = Fin k × Bool` is bijective with this actual zero set; the Boolean branch equals
  transverse derivative sign. This closes the gap in which `2k` cellular labels had been supplied
  without proving that they were analytic Stokes walls. Exact module:
  `StokesAnalyticWallRealization.lean`.
- `[RESOLVED: GLOBAL JOINT NULLITY LAW]` Positivity on common-rank kernel now yields sharp joint
  statement `sigNeg Q + finrank(radical Q) <= 1`, not merely separate upper bounds. Rank kernel is
  positive definite and therefore contributes to `sigPos`; rank-nullity for common-rank functional
  and Sylvester signature identity leave at most one dimension for negative plus radical parts.
  Same theorem holds for every nonnegative global multi-Rees specialization. Exact module:
  `StokesGlobalPuiseuxWittLaw.lean`.
- Direct checks of both modules pass. Axiom audit reports only standard `propext`,
  `Classical.choice`, and `Quot.sound`. Repository-wide formal lint reaches unrelated existing
  umbrella error: `GaloisForLFunctions.RHTower.DeningerStageZeroCohomology` is unreachable from
  `RHTower` umbrella; no Stokes-module lint violation was reported before that gate.
