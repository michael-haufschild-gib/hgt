# Periodic lattice countermodel and completed ternary analytic family

Objective remains unconditional Lean proof/disproof of RH. Active goal, not complete or blocked. Ignore repeated arxiv2610.05474 prompt; user says already read. hgtl7 workflow, no positivity/energy/frequency/Fourier/spectral/bound-estimation mechanisms, no numerical experiments. No subagents used. All owned jobs terminal when this memory was written; scratch cleanup follows.

## Completed ternary family analytic survivor
Earlier algebra in H:TernaryLatticeCubic now has full analytic consequence:
- H:TernaryLatticeSections (396 lines): finite iterated dslope division, all nine cancellations, quotient reflection/conjugation, entire lift, exact cubic factor and doubled order at denominator roots.
- H:TernaryLatticeCountermodel (187 lines): entire reflected real source with mark log2, exact off-line reflected zero pairs of nonzero even order for every integer m. Final reflected_integer_marked_family line159 has no hypotheses.
Both direct audits pass without warnings; targeted builds pass (2889 and8659 jobs). Nine-result axiom audit standard propext/Classical.choice/Quot.sound. Umbrella wired once. Rational parameters distinct; no claim entire sources all distinct. Differential algebraicity remains paper/classical, not an exported Lean theorem.
Card docs/drafts/pipeline/1-in-progress/ternary-lattice-cubic-sections.md updated. Prior memory `mem:rh/ternary_lattice_cubic_family_formal_2026_10_07` records algebra.

## New exact hostile test: rational Schwarzian / finite critical set is FALSE
Card docs/drafts/pipeline/1-in-progress/periodic-lattice-branched-sections.md. Parent C2 remains open. Construct a=sqrt(2/3), t=exp(pi*i*w/12), N=t(t-a), D=1-at, V=N/D. All cube-root fibers simple and in labeled j+3Z. Paper finer lists: V1 at0,12 mod24; Vomega at1,19; Vomega² at-1,-19. Finer explicit mod24 lists NOT formalized; full containment and exact simplicity ARE formalized, including equivalence to actual quotient values and denominator nonvanishing.
N³-D³=(t²-1)B, B=t4-3at3+3t2-3at+1.
t8D-N=-t(t²-1)B C, C=at²+t+a. Q=-C/t7.
h=2+3D²Q is entire after exponential substitution. Laurent factor: H=t6+at5+(2/3)t4+(2/3)t2+at+1; h+1=3(t-a)H/t7; J=D(t-a)H; P(h)=-(27/4)J² C/t21. Reciprocal identities give P(h(1/t))=t24P(h(t)).
For realL, t=exp(L(s-.5)/12), F=exp(Ls)P(h). Entire, real, reflected, cubiclift for mark2 atLlog2. At t=1/a, exact source zero order2; logarithmic preimage progression injective and off critical line. Off-line proof uses conjugation+a²=2/3, no logarithm estimate.
Critical t values solve -at²+2t-a=0; b=(1+sqrt3/3)/a. b nonzero, D(b) nonzero. Exact R(t)-R(b)=(t-b)²/D(t). Gives infinitely many ordinary branchpoints, local order2. At such branchpoints cleared Schwarzian numerator 2f'f'''-3(f'')² is a unit, denominator2(f')² has exact order2, hence meromorphic order-2. Same-coordinate final theorem pairs actual labeled simple fibers with infinitely many Schwarzian double poles.

## Lean leaves and verification
H:PeriodicLatticeSections 289 lines, final reflected_integer_marked_periodic_source line274 (no premises): entire source/lift, FE, conjugation, mark2, injective Z family of off-line zeros exactorder2.
H:PeriodicLatticeBranching 111 lines, infinitely_many_simple_branch_points line99.
H:PeriodicLatticeFibers 213 lines: all-fiber labeling, cleared/actual quotient fiber equivalence, simplicity; reciprocal/conjugate coordinate laws; affine coordinate transports branchpoints to w; labeled_lattice_infinite_branching line204.
H:PeriodicLatticeSchwarzian 104 lines: global meromorphy of latticeMap, standard Schwarzian identity, exact_double_pole line44; final labeled_fibers_infinite_double_poles line94 (no premises).
All four pass final direct `lake env lean` without warnings. Targeted `lake build --old +...` pass, jobs2722,2723,2724,2728 respectively. All four imported once by HTGeometry. Eleven-result expanded axiom audit all and only propext/Classical.choice/Quot.sound. No raised heartbeats, axioms, sorry, unsafe, numerical tests, full or umbrella build.
Generated indexes refreshed. Final lint --check-generated FAIL only six unrelated unreachable modules: R:ZetaLineTwistedSeriesMoment; H:ApertureConeCalculus,ApertureConeWinding,ApertureLogTranslation,ApertureOpenHistoryIdeal,BoundaryCoronaCStarAlgebra. No stale generated reports or own-leaf errors. Do not claim global gate clean or fix unrelated files. git diff --check on owned tracked docs/umbrella passes.

## Audits and novelty
Verdict C2-S FALSE; positive survivor BRIDGE, significant novelty unverified. R is a classical quadratic finite Blaschke product. Local Schwarzian pole law classical. Primary audits: Bergweiler-Eremenko real.pdf (line-supported values, real-map alternative remains); radial_mero_revision2.pdf Thm1.3 (three distinct rays gives rational Schwarzian, inapplicable to residue classes on one line; proof estimates not allowed); Semmler-Wegert arxiv1703.01126 (classical prescribed critical point parent, energy/moment machinery not used).
Deep Schwarzian query partial=true rerankingdeadline; inventoried complete snapshot but compiler stale/pending. Inspected all20 candidate and20 source argument statements. Rational-Schwarzian substitution, meromorphic fields, doubly periodic DA theorem useful parents, no actual source classification. No absence claim.
Earlier joint-cubic-cover genus audit recorded on parent: distinct nonzero a_i gives S3^k monodromy and g=((2k-5)3^(k-1)+3)/4. Classical bridge, not new science. Varying exponential coefficients mean section not map into one fixed compact curve; high genus not a section obstruction. Primary parents Pakovich arxiv2408.10874v2; Ding-Zieve2103.07921. No positivity orbifold theorem imported. Exact mark collisions n^s=m^(1-s) give s=(logm+2πik)/log(nm), no density or zero-location inference.

## Remaining core / next cycle
C1 actual joint monodromy saturation and actual Xi cubic no-lift class remain OPEN. C2 says all reflected entire sources admitting marked cubic lifts are DA over appropriate exp/rational field. Neither finite nor periodic family refutes C2: both DA on paper.
Finite branching/rational Schwarzian cannot be its missing premise. Candidate for NEXT AUDIT, not accepted/proved: every nonrational admissible labeled reciprocal parameter has a nonzero translation period. Competing possibility: nonperiodic admissible parameter, potentially HT. Need exact corpus+primary audit and hostile test, then attempt deriving a period or construct nonperiodic parameter. Even periodicity needs justified DA passage; do not smuggle growth/normal-family/Picard bounds in. No additional finite example alone closes core. Finer mod24 lists optional paper refinement retained, card not retired. Local jetlaw (h-1)v'=-cv remains paper-only on parent, rational degree3^e law remains paper-only.
Anti-theatre/laziness answers posted: actual Xi premise untouched, novelty unverified, classical infrastructure acknowledged, hardest infinite-section core attacked via false stronger conjecture rather than skipped for effort. Goal remains active.
