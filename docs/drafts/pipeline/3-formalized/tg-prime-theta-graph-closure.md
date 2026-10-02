# TG-C9.9: exact closure of the actual two-prime theta action

- **ID:** TG-C9.9-20261002-01a0
- **Stage:** 3-formalized
- **Type:** THEOREM / complete relation classification
- **Leaf:** `PrimeBurnolFourierJetThetaClosure`
- **Parents:** `../1-in-progress/tg-fourier-jet-theta-cubic-domain.md`, `tg-fourier-jet-prime-graph-core.md`

## Hard question

Does the original prime-dependent theta action have ANY single-valued closed extension
on the completed even Fourier-jet source graph G? A norm obstruction does not answer
closability. C9.8 shows exact single-prime full-cubic cancellation, so the next question
must keep the incompatible actions of different primes together.

## Exact new theorem

Every individual prime's depth tower is a core for the same entire even maximal
multiplication graph (`PrimeBurnolFourierJetPrimeCore`). The actual fixed-prime theta
map is Q_p=c_p²I+(v_p²-c_p²)N+v_pc_pS (`PrimeBurnolFourierJetThetaDomain`).
The actual tanh law and prime log injectivity now prove that p↦v_p² is injective at
every nonzero parameter, strengthening the previous uniqueness result at balance.

For distinct primes p,q, let L_a be the literal finite relation obtained by summing
the graphs of Q_p on the p-depth source core and Q_q on the q-depth source core.
The exact classification is:

- at a=0, closure(L_a) is exactly the closed original neutral graph;
- at every a≠0, closure(L_a)=G×G.

The second statement is much stronger than unboundedness: every vertical fibre is G.
The original finite relation is single-valued, proved from global linear independence
of the actual even Burnol columns and algebraic disjointness of distinct prime graph
cores. Hence the literal finite two-prime operator has a closed extension exactly
when a=0 (`primeBurnolJetTwoPrimeTheta_isClosable_iff`). The nonzero closure is a
multivalued relation, never misidentified with `LinearPMap.closure`.

The positive survivor is complete simultaneous approximation: every pair of completed
jet source and response vectors lies in the same finite arithmetic graph closure.
This is an exact classification and a sharp boundary, not only a negative norm result.

## Dependency-closed paper proof

Use the product of the TWO separate multiplication graphs as raw coordinates. The
existing continuous jet assembly maps ((f,Mf),(g,Mg)) to the literal graph vector.
For fixed p, scalar theta acts continuously on those raw coordinates. Prime graph-core
density therefore places (z,Q_p z) in closure(L_a) for every originally admitted even z.
Ordinary L2 density alone would not suffice.

For a≠0, prove injectivity of p↦v_p²: equality of v² gives
equality of c²; c_p and c_q have the same sign, so tanh injectivity and log injectivity
give p=q. For distinct p,q write d=v_p²-v_q² and e=v_pc_p-v_qc_q. The original-source
matrix Q_p-Q_q=[[d,e],[e,-d]] squares to (d²+e²)I, with d²+e²>0. Its explicit inverse
preserves the separately admitted even source domain.

Subtract the two limits (z,Q_p z),(z,Q_q z). Invertibility of their difference gives
(0,w) in closure(L_a) for every originally admitted w, hence for every w∈G by closure.
Subtract these vertical vectors from literal graph vectors to obtain the dense horizontal
core, hence G×G. The reverse inclusion follows because both actual source outputs stay
in G. At a=0 all theta maps are the same neutral operation; its closedness gives one
inclusion, and the separate prime multiplication graph core gives the other.

The proof uses continuous raw graph assembly and submodule closure throughout. The current ambient
product has the max norm, not a Hilbert product. The retrieved `GraphSaturationCore`
annihilator theorem requires genuine Hilbert carriers and is not directly applicable.

## Search and verification

Search `distinct dense subspaces operator graph closure multivalued scalar action`
was partial (semantic deadline). It returned actual graph-closure and graph-saturation
lemmas; their hypotheses were read. No absence claim follows from that search.
Current search `prime theta graph closure dense cores difference invertible` had complete
inventory and partial reranking (deadline); it retrieved the actual prime graph-core
theorems used above. Compiler freshness was mixed. Source declarations were read and
applicability verified in Lean; no absence claim was inferred.

The complete scratch and production leaf pass foreground `lake --old env lean`,
without warnings or errors. The existing raw assembly is now public as
`burnolJetGraphAssembly`; PrimeCore, NeutralGraph and ThetaDomain were rechecked in
dependency order. PrimeCore retains its existing informational ring_nf suggestion.
The new leaf is wired into RHTower; no full or umbrella build. BalancedCubic was also
rechecked after its dependency update and passes without warnings/errors. The separate
/tmp API and axiom audit passes all 19 added/exposed public declarations (12 new
theorems), with only propext, Classical.choice and Quot.sound. No added axiom, hole,
numerical experiment, heartbeat increase, subagent, commit or push.

Index refresh exits zero and updates the three generated API documents. Scoped
whitespace checks are clean. Authoritative lint exits one only for 11 unrelated
unwired RHTower leaves: CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, DivisorSourceLogPhase,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving. No TG leaf error;
existing large-file warnings remain. All five affected production oleans are newer
than their sources. Owned temporary proofs, searches and logs were removed after audit;
all owned processes exited.

## Remaining route problem

Even total theta graph closure would not by itself classify the COMPLETE mixed-prime
Gram-modular cubic: products may have cancellations not shared by their factors.
Continue in `../1-in-progress/tg-fourier-jet-mixed-cubic-closure.md` with its actual
relation/domain and all cross terms. Gamma–Xi identification,
Hardy-index transfer and the arithmetic sub-unit producer remain open. No RH conclusion.
