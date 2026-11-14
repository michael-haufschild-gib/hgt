# RH research: obstacles, breakthrough questions and programmes

The most concrete shared frontier is the passage from certified arithmetic structure to a uniform exclusion theorem. The corpus already has a `7/8` zero-free boundary, a positive full Weil floor through aperture `1881/5000`, a lossless first overlap step at every block size, detailed critical-state structure, and both heat and arithmetic Galois theories. None supplies the remaining all-scale arithmetic estimate. [MMD] [BLOCK-FLOOR] [GREEN-FIRST] [HF] [MONODROMY] [TRACE-FIELD]

Three requirements organize the research: **P — arithmetic production**, **U — uniform exclusion**, and **R — faithful realization and transport**. AAL adds a separate finite-exception question to these requirements. The [route report](route-obstacles.md) records all 38 routes and 12 candidates; the [wall ledger](walls-ledger.md) gives precise boundaries; the [unification ledger](route-unification-ledger.md) distinguishes identities from analogies.

Research programmes below are proposals, not claimed proofs. “Smaller” means a restricted mathematical target with fewer global quantifiers, not a proved ordering of difficulty. Quasi-RH is already available in this corpus through MMD; an open question cannot honestly be advertised as a necessary preliminary to obtaining that existing result. The original review did not run compilation. Source claims rest on the [fact log](../../../logs/review-1411-facts.txt) and its Lean evidence; external context uses primary sources.

## 2.1 — Tasks that are work rather than new mathematics

The list is deliberately shorter than the research list. Applying an RH criterion after assuming its missing input does not solve an obstacle.

**A1–A7 are formalized within the stated finite scope.** The [theorem index and proofs](../../drafts/pipeline/3-formalized/review-1411-finite-work-obstacles.md) give exact statements, owning modules and transitive axiom audits. A3 exposes the three remaining excesses; it does not prove their vanishing.

| Task | Concrete deliverable | Why it is work; boundary |
|---|---|---|
| **A1. Combine the strip and Jensen rung** | Formalize real-rootedness through degree `31922` using `w≤3/8`, verified height `67`, and `(d−1)w²≤67²`. | The receiver and both inputs exist; the numerical inequality is rational arithmetic. The source directly states degree `17957`; the assembled corollary reaches `31922`. It is a finite rung. [MMD] [JENSEN-RUNG] |
| **A2. Export certified floor consequences** | Give common wrappers for smaller apertures, real/complex tests, step packets, neutral charge-free forms and dressed middles, with constants and cutoff ranges explicit. | The first-overlap implications are already theorems. This consolidates usable interfaces; it does not extend the certified aperture. [BLOCK-FLOOR] [GREEN-FIRST] |
| **A3. Make the finite overlap budget explicit** | Express the ratio-three target using the remaining terms of `levelAt 2 4`, with the first term zero and exact rational ratio milestones. | The recursion and implication are proved. Proving those remaining excesses vanish is B, not part of A3. [GREEN-LADDER] [GREEN-FIRST] |
| **A4. Preserve completion in route transfers** | Instantiate existing WL, CHMD, SZ, HAT-C and PM dictionaries with their actual pole, Gamma, jump and root-number terms. | These are exact normalization/conversion results. No stronger bound is created by conversion. [WL] [CHMD] [SZ] [HATC] [PM] |
| **A5. Specialize finite algebraic constructions** | Work out specified finite prime-trace equations, finite reflection-radicand relations, local collision permutations and finite contact ideals. | The algebraic templates exist. An infinite square-class classification, existence of a desired collision, or source-field purity remains B. [TRACE-FIELD] [REFLECTION] [HEAT-TURN] [CONTACT] |
| **A6. Transfer existing family results within their scope** | Instantiate primitive Hecke/Brauer completion and scattering statements for specified representations or the actual Eisenstein family. | Completion and signed divisor bookkeeping are available. General Artin holomorphy and a new number-field cancellation estimate are excluded from this task. [ARTIN] [MMD] [RINGDOWN] |
| **A7. Reuse exact finite certificates** | Turn a fully specified rational/Taylor/Gram inequality into a reusable checked certificate and expose its hypotheses. | Certificate evaluation and exact finite algebra are work. Finding a certificate with the desired sign, or proving its remainder bound, may be research. [FLOOR] [CHARGES] |

There is no identified routine final step for WL, MC, WD, ACS or AAL that would close them with present inputs. Their receivers are substantially complete; their missing arithmetic assertions are not.

## 2.2 — Open mathematical obstacles

| Problem | Required theorem | Routes affected |
|---|---|---|
| **P1. Critical signed cancellation** | Actual Möbius/prime/reciprocity sums satisfy the critical subpower bounds with the required length, conductor and phase uniformity. | MC, WD, FU, CTF, CHMD, PBM; quantitative improvements feed PM and JAS. |
| **P2. A producer outside the classified Gauss mechanism** | A source-retaining reciprocity transform improves the attainable exponent without falling into the completed monomial `3/5` class. | MMD/FCT/CRF and all consumers of improved strips. [GAUSS] |
| **U1. All-aperture arithmetic sign or margin** | Actual Weil/window forms have the required global bound; equivalently, signed overlap losses remain under the global binding budget. | ACS, RW, HF, EWU, OWU, HAT-C and other sign receivers. [ACS] [GREEN-GLOBAL] |
| **U2. Exclusion of the critical state** | The explicitly characterized arithmetic critical half-line state cannot occur at positive threshold. | HF and causal/ground-energy variants. [HF] |
| **U3. Finite-exception rigidity** | Every rightward zero can be transported to arbitrarily high ordinates with arbitrarily small loss of real part; or prove a finite exceptional layer exists. | AAL, tail-only SC/JAS branches, exceptional-layer programmes. [AAL-TRANSPORT] [AAL-LAYER] |
| **U4. Heat descent and conjugation** | Arithmetic control of positive-time branch/conjugation data that survives the limit to time zero. | ZCG, LA, PTR, TG. [ZCG] [HEAT-HORIZON] |
| **U5. Actual higher correlations** | Bounds for arithmetic fourth/higher traces or an alternative invariant controlling the zero census, with the correct near-line scale. | Census/IGP, SRT, WD and near-line programmes. [CENSUS] [CENSUS-AMBIGUITY] |
| **R1. Faithful arithmetic realization** | Construct the proposed field, geometry, history, character or physical observable and identify the full ξ divisor, including exceptions and multiplicities. | ECP, APF, W1C, IRK, WBF, PM and geometry candidates. |
| **R2. Arithmetic restrictions on Galois actions** | Prime-field relations independently constrain weights/reflection strongly enough to force criticality. | Arithmetic Galois/ZCG interface. [WEIGHT-ORBIT] [REFLECTION] |
| **R3. Correct absolute intersection theory** | Contacts, jets, logarithmic negative geometric self-pairings and archimedean normalization admit a source-derived global theorem. | F₁/AGZ, ACS and geometric RH programmes. [CONTACT-JET] [SELF-PAIRING] |

The terminal versions of many entries are RH-equivalent. Smaller stepping stones below are not known to be equivalent. Neither a corpus search nor a literature check establishes that “nobody” has an unpublished solution; the precise claim is that the audited sources do not discharge these inputs and RH remains open in the established literature. [Clay](https://www.claymath.org/millennium/Riemann-Hypothesis/)

## 2.3 — Can a Frankenstein route bypass a single-route blocker?

**The strongest compatible assembly is a retained-charge window route.** Start with the WTZ analytic certificate; retain its low moments, primitive mass and signed prime autocorrelations; use regional charged gaps and Gamma remainder identities; then apply the exact Green Schur formula and refinement theorem. This avoids the prohibited replacement of a high-rank coupling by a fixed-rank product of charges: the full jet/contact operator remains present. A successful bound would feed ACS, RW, HF and both parity sectors simultaneously. The unpaid theorem is the signed Schur estimate beyond the certified aperture, followed by a global loss budget. Assembling the pieces does not pay it. [FLOOR] [CHARGES] [GAMMA-LAGS] [RANK-WALL] [GREEN-LOSS]

**A second assembly joins decompletion to signed arithmetic production.** The correction can already be made zero-free near the half-line. Attach a reciprocity identity whose boundary error remains visible, preserve the target and reciprocal phases, and estimate their signed interaction before taking absolute values. This could bypass the completed-monomial barrier because its hypotheses would no longer apply. A reciprocal boundary-error theorem and an actual saving are both missing. [DECOMPLETE] [GAUSS] [AVERAGE]

**Three useful but incomplete assemblies:**

- MMD plus the verified-height Jensen theorem gives the finite rung in A1. It does not give unbounded degree. [JENSEN-RUNG]
- MMD plus the JAS strip-dependent criterion removes that criterion's strip premise. Its double-exponential-window and cofinal-shell inequalities remain. [JAS-STRIP]
- Prime-trace Galois theory plus heat monodromy could organize a comparison of arithmetic reflection with analytic continuation. No comparison map carrying the necessary arithmetic constraints is currently supplied. Large heat monodromy is compatible with nonreal configurations. [TRACE-FIELD] [ZCG] [HEAT-ODD]

No currently assembled combination circumvents every blocker. In particular, AAL plus a fixed `7/8` boundary is not RH; finite-window positivity plus an exact gluing identity is not a global sign theorem; a physical interpretation plus a decay/RH equivalence is not a decay proof.

## 2.4 — A breakthrough below a global RH problem

**Question:** can the actual ratio-three neutral window have exactly one negative square at every block size, by proving `levelAt 2 4 = 0`?

This asks for a bounded ratio and one finite segment of the overlap ladder. The first loss is zero. The other terms are explicit Schur excesses of actual arithmetic matrices. A proof must retain the full signed end coupling and give estimates uniform in block size; checking finitely many matrices is insufficient. The theorem connecting this target to all ratio-three windows is already available. [GREEN-FIRST] [GREEN-LADDER]

The gain would be a complete uniform gluing result well beyond the present certified ratio and a test of whether retained-charge estimates can control the exact Green term. A counterexample to a *specified comparison estimate* would locate its missing charge or phase; it would not refute the actual window claim. There is no demonstrated implication from this single finite-ratio theorem to RH or AAL. Its narrower scope, rather than an asserted complexity theorem, makes it a credible intermediate target.

## 2.5 — A breakthrough in finding a producer

**Question:** can an incompletely completed reciprocity transform retain the Möbius target and all root-number phases while its reflection defect has a genuine power saving, uniformly over the ranges needed by the detector?

The relevant starting point is not another search for a zero-free correction: that correction already exists for each `σ>1/2` after truncation. The unknown is compatibility with reflection. Seek an exact identity of the form

`source(s,w) = phase(s,w) · dualSource(1−s,w′) + boundaryDefect(s,w)`

with every factor independently defined from prime/ideal arithmetic. The target coefficient must be recovered exactly. Specify conductor, sum length, cutoff and complex-parameter ranges before estimating the defect. A saving in a range disjoint from the receiver's requirements is not a producer. [DECOMPLETE]

The first milestone is a nontrivial uniform saving in one explicit rectangular range, while retaining the reciprocal target rather than averaging it away. The second is stability under the family continuation used by the detector. Only the third asks whether the resulting exponent beats the classified `3/5` boundary. An exact phase-preserving transform with a controlled defect would be a breakthrough even before the final exponent improves: it creates a mathematically different producer class. A transform reducible to the classified monomial completion, or one whose saving is obtained after deleting the target, fails this test. [GAUSS] [AVERAGE]

## 2.6 — Breakthrough with positivity and every spectral method excluded

**Question:** does prime arithmetic impose a nontrivial divisibility law on the multiplicity of each individual off-critical zero?

Start with the open half-plane `Re s>1/2`. Seek an arithmetic descent operation on local analytic divisor germs that preserves the germ of ξ while making its vanishing order divisible by two. The finite first target is **even multiplicity at every off-critical zero**, derived from prime identities or local algebra, without a positive form, a self-adjoint operator, an eigenvalue argument or a spectral reformulation.

This target alone is compatible with RH being false. A coherent iteration giving divisibility by arbitrarily large powers of two would force each finite local order to be zero, hence exclude the zeros. That is the proposed path to RH; the existence and iteration of the descent are both unknown. Merely permuting a reflected quartet proves parity of the quartet's total multiplicity, which is already automatic, not parity at one point. [QUARTET-PARITY]

Global square roots of ξ are the wrong object: the corpus proves an odd-order zero exists. The construction must be regional, allow the critical line as a boundary, and provide prime-defined transition data rather than assume an analytic root. A successful regional multiplicity descent would open a route outside all sign and spectral criteria. No such descent is claimed here. [ROOT-WALL]

## 2.7 — Breakthrough under the AdS/modular-horizon hypothesis

**Question:** can a prime-marked modular-horizon observable obey a causal identity that forces quarter-rate reflected-pulse decay, while an independently proved boundary dictionary identifies every relevant ζ pole with an observable singularity?

The existing modular and Bianchi models give precise arithmetic scattering dictionaries. They do not establish that RH is an AdS phenomenon. In the pulse normalization, the desired statement is decay at every rate `1/4−ε` for every compact smooth pulse, with constants allowed to depend on pulse and ε. Bianchi's divisor is `ζL(χ₋₃)`, so that version proves the corresponding Dedekind statement as well. The unconditional source rate is `1/16−ε`. [PM] [RINGDOWN]

The first research target is a complete observable and its arithmetic dictionary, followed by one strictly improved rate obtained from a bulk causal or modular Ward identity. A law that only controls a cuspidal subspace, or misses finitely many resonances, cannot prove RH. The decisive test is whether the decay is derived from independently defined horizon dynamics rather than imposed as “physical stability.”

Maldacena's eternal-AdS construction provides an established setting involving two boundary theories and an entangled state; it supplies no ζ identification. The proposed prime-marked dictionary and decay law are additional hypotheses to construct and test. [Maldacena](https://arxiv.org/abs/hep-th/0106112)

## 2.8 — Breakthrough under a topological/geometric hypothesis

**Question:** can the arithmetic square's actual Frobenius contacts and jets be realized by a relative intersection theory whose moving/normal-direction law forces the required index, including its negative logarithmic diagonal?

The square and contacts are not missing names: finite contact ideals and planar Bézout identities exist. The obstruction is a global realization that carries the exact archimedean correction and proves its index. Ordinary nonnegative geometric self-intersections cannot realize the measured couplings: the two-run law forces negative geometric self-pairing at logarithmic scale. [CONTACT] [CONTACT-JET] [BEZOUT] [SELF-PAIRING]

A first breakthrough would be an independently defined renormalized normal object whose self-intersection produces the actual diagonal, together with an exact-sequence or moving-law proof on one window containing both prime-two and prime-three contacts. Extending its compatibility under refinement would give a plausible route to global index control. Declaring the desired pairing to have Hodge index merely restates the target. Generic geometry is insufficient: compact Selberg geometry permits finite off-line exceptions. [SELBERG]

## 2.9 — Would RH require a new field of mathematics?

No known theorem establishes such a necessity. Existing analysis, arithmetic geometry or algebra could contain the missing argument. A useful new discipline would earn its place by solving a problem shared by these routes, rather than by renaming RH.

**Proposed subject: arithmetic transport across scale.** Its objects would be arithmetic test-function spaces, prime contact operators, completion terms, signed response maps and exact defects between scales. Its language would distinguish a source, a realization of that source, an observable and its loss under transfer. Morphisms would preserve the prime coefficients and record all pole/Gamma corrections.

Its central questions: which signed quantities survive completion? When does local control compose without accumulating an unbounded defect? Which invariants retain a finite exceptional zero? Its tools would include phase-preserving reciprocity, exact Schur/response calculus, conductor-uniform continuation and obstruction classes for source descent.

Acceptance criteria are concrete: recover the first-overlap theorem and Gauss barrier; explain why fixed-rank gluing and target-blind averaging fail; prove one new uniform signed estimate outside those failures; and make the estimate consumable by two independent receivers. A theory that only translates all routes into “positivity of the arithmetic object” has not advanced the research. [GREEN-FIRST] [GAUSS] [RANK-WALL] [AVERAGE]

## 2.10 — Would AAL proof or falsification require a new field?

Again, necessity is unknown. A focused subject would be **arithmetic rigidity of finite defects**. Its objects would be exact Euler products with completion data, finite divisor edits, infinite tails, and maps preserving or changing the prime source. Its basic invariant must distinguish the genuine source from edit models with the same coarse counting asymptotics.

The central dichotomy is precise. AAL transports every rightward zero arbitrarily high with arbitrarily small real-part loss. Its failure isolates a finite nonempty layer above a stricter tail boundary. The corpus also identifies failure with a finite-oscillation form of the prime error. These are three descriptions of the same issue, not three independent proofs. [AAL-TRANSPORT] [AAL-LAYER] [AAL-OSCILLATION]

The existing three-law decomposition provides finer research targets: **finite stratum**, finitely many off-critical zeros imply none; **landing**, approach to the line implies only finitely many off-critical zeros; and the defined **asymptotic Deuring–Heilbronn law**, failure of AAL implies approach to the line. Their conjunction is AAL. A theory should identify which law its arithmetic invariant addresses rather than hide all three in a single rigidity axiom. [AAL-LANDING]

Required tools: a calculus of finite edit defects; reflection and conductor compatibility tests; source-sensitive asymptotic invariants; and a transport theorem stable under the permitted arithmetic operations. A first benchmark is to separate one explicit tail-twin construction from ζ by a computable-in-principle exact invariant, without using the zero locations as its definition. [EDIT] [EDIT-DEFECT]

A proof programme must derive height transport for the real source. A falsification programme must exhibit both a top zero and a uniform lower tail abscissa. Finding one off-line zero would refute RH but could leave AAL true. An invariant insensitive to finite edits cannot settle this question.

## 2.11 — A new field with all positivity and spectral methods banned

**Proposed subject: regional arithmetic divisor descent.** Objects are local analytic rings, effective divisors, prime-defined correspondences, branch cocycles and their integral multiplicities on domains separated from the critical line. The permitted language is algebraic and complex analytic; it excludes Hilbert-space realizations, eigenvalues, positive kernels, Weil positivity and equivalent sign certificates.

Its tools should be descent of local units, ramification and multiplicity, compatibility of prime-indexed roots, and obstruction classes for gluing regional analytic roots. The first question is whether an arithmetic operation forces even local order off the line. The next is whether the operation iterates coherently without merely postulating roots of ξ. The terminal mechanism is unbounded divisibility of a finite integer order.

The framework must explain the known global odd-order obstruction and distinguish local multiplicity from the automatically even size of reflected orbits. It must also work on an explicit class of arithmetic analytic functions where multiplicities can be independently determined, exposing where the descent fails. A theorem about formal divisors with the desired divisibility assumed would not qualify. [ROOT-WALL] [QUARTET-PARITY]

This is a speculative route, with no current arithmetic descent operator. Its value is a sharply different mechanism and a finite first test, not evidence that it will succeed.

## 2.12 — A new field under the AdS/modular-horizon hypothesis

**Proposed subject: arithmetic causal geometry.** Objects would include an AdS bulk with a specified modular horizon, a boundary observable algebra, prime-marked cycles of length `log p`, completion counterterms, and a scattering map defined before ζ is identified. The construction must state dimension, quotient, boundary conditions and normalization; “AdS” alone determines none of these.

Required mechanisms are a derivation of the prime contribution, a geometric account of the archimedean factor, a functional-equation involution and complete detection of divisor singularities. Tools would combine causal propagation, modular identities, renormalized boundary actions and arithmetic gluing. The central dynamical question is why the physical law enforces decay at every rate below a quarter, rather than merely reproducing the arithmetic equivalence.

Benchmarks: reproduce the exact modular/Bianchi scattering phase and the strip-derived `1/16−ε` bound; identify an observable that sees any finite exceptional resonance; derive a stronger rate from a bulk theorem; then reach the quarter threshold. An imposed stability axiom equivalent to the desired rate fails the independence requirement. [PM] [RINGDOWN]

Existing AdS duality motivates the setting but supplies none of this arithmetic mechanism. A successful theory would explain both the prime source and the decay law; a visual or thermodynamic analogy would not. [Maldacena](https://arxiv.org/abs/hep-th/0106112)

## 2.13 — A new field under the topology/geometry hypothesis

**Proposed subject: renormalized arithmetic intersection topology.** Its objects would be arithmetic squares, prime contact strata, jets along the diagonal, a normal-direction object, and compatible refinements of finite windows. Its language needs signed self-intersection, not only positive degree, and must distinguish geometric incidence from the analytic completion of incidence.

Questions: what geometric operation produces the logarithmic diagonal? Why are the pole plane and archimedean term canonical? Which exact sequences control index when windows overlap? How do contacts survive base change and refinement? A theory must retain the contacts that perfection destroys and account for the rank growth that fixed charge-product gluing misses. [PERFECT] [SELF-PAIRING] [RANK-WALL]

Tools should include relative cohomology or a substitute with exact localization, contact multiplicities, renormalized self-intersection and a moving law compatible with the arithmetic source. The first benchmark is a genuine geometric proof of an actual finite-window inequality not inserted as an axiom. Global compatibility is the second, much harder benchmark.

Deninger's arithmetic dynamical systems demonstrate that primes/periodic-orbits/topology analogies can support precise constructions. They do not establish the specific index theorem required here. [Deninger](https://arxiv.org/abs/2301.11643)

## 2.14 — Research programme for F₁

**Target.** Construct an absolute base and geometry suitable for the arithmetic square and its intersection theory. A nontrivial ordinary field with one element is impossible under the usual `0≠1` field axioms; “F₁” must denote a different categorical base. Existing monoid, semiring and absolute-algebra frameworks are starting points, not absent inventions. Connes–Consani's scaling site provides a precise tropical/arithmetic setting and a Riemann–Roch analogue on its prime periodic orbits. [The Scaling Site](https://arxiv.org/abs/1507.05818)

**Objects and language.** Choose explicitly a category of absolute algebras, its tensor product, modules/sections, prime ideals or points, and a base-change functor to rings. Construct the absolute analogue of `Spec ℤ × Spec ℤ`; identify diagonal and Frobenius graphs; define their contact ideals and normal jets. Compare the chosen category with the corpus's ghost/planar arithmetic square instead of assuming they coincide. [CONTACT] [CONTACT-JET] [BEZOUT]

**Milestones and criteria.**

1. **Algebraic adequacy:** functorial base change to ℤ and finite fields; a meaningful product; exact reproduction of the known prime-power contact divisibilities. A perfected model that erases contacts fails immediately. [PERFECT]
2. **Sections and degree:** a lattice or replacement for sections, exact local counts, and a degree compatible with products and finite-field specializations. Prove the finite statements before introducing a global intersection law.
3. **Archimedean completion:** derive jets, the pole contribution and the diagonal counterterm from intrinsic objects. Recover the required negative geometric self-intersection at logarithmic scale. This is a new mathematical construction, not routine base change. [SELF-PAIRING]
4. **Localization and Riemann–Roch:** build exact localization sequences and an Euler-characteristic/degree formula whose terms match the actual arithmetic square. State the error or defect when they do not.
5. **RH-relevant theorem:** prove the necessary global index or an alternative source-derived exclusion law. It must be a theorem of the constructed geometry, not an axiom defining “absolute surface.”

The first decisive deliverable is a comparison theorem preserving contacts, jets and the diagonal simultaneously. Construction of a category called F₁ without that comparison does not close AGZ or ACS. Conversely, a comparison on a nontrivial finite window would already be worthwhile without RH.

## 2.15 — Research programme for WD

**Terminal target.** With `M_N(s)=Σ_{n≤N} μ(n)n^(−s)`, prove

`∀ε>0 ∃B≥0 ∀N≥1, ∫₀¹ |ζ(1/2+iu) M_N(1/2+iu)|² du ≤ B N^(2ε)`.

The exact equivalence to RH is available. A pointwise subpower condition on `M_N` at a fixed critical-line height and a positive-proportion low-set condition are alternative receivers with different quantifiers. Choose one as the primary target; do not mix them midway. [WD] [WD-PROPORTION]

An especially useful long-range alternative is also exact: find one `K≥0` such that, for arbitrarily large `θ`, some `C_θ` bounds the `[1,T]` zeta-mollified second moment at length `⌊T^θ⌋` by `C_θ T^K` for cofinally large `T`. The constant may depend on θ; the exponent K may not. This is substantially weaker than demanding a near-unit moment, but it is still an RH-equivalent missing estimate. [WD-COFINAL]

**Objects and tools.** Use the actual convolution coefficients of `ζM_N`, chronological/scale decompositions, completed Ward identities, near-line cameras and phase-preserving bilinear sums. Retain the final scale and cross terms. Short-mollifier second moments and the Euler block factorization are starting estimates within their explicit length ranges, not long-mollifier solutions. [WD-SHORT] [WD-BLOCK]

The short exponent-`13/50` construction already proves a positive proportion of critical odd fibres. This arithmetic result is distinct from the low-set positive-proportion criterion above: the latter concerns arbitrarily long prefixes on every specified height window and at every positive error exponent. A positive fraction of zeros on the line cannot replace it. [MZF-PROPORTION] [WD-PROPORTION]

**Programme.** First derive an exact signed decomposition of the fixed-window error in which each uncontrolled term is named. Next establish a new cancellation estimate on one nontrivial long range, with constants uniform in the variables needed for iteration. Then prove scale stability: the gain must survive the last block rather than being consumed by completion or absolute values. Finally reach every positive exponent and every length in the displayed target.

**Tests and failure criteria.** A bound on raw Möbius polynomials uniform over all lengths at fixed height is not the zeta-mollified target. A near-unit second moment for a fixed `N=T^θ` has a separate lower-bound obstruction; abandon that excessive target rather than declare all long-moment routes dead. A near-line density theorem still leaves exceptional zeros. [WD-RAW] [LONG-MOMENT]

**First breakthrough:** a source-specific signed estimate that improves a terminal-scale cross term beyond its norm bound and remains valid under the required length amplification. That would be a producer contribution, not another reformulation of WD.

## 2.16 — Research programme for ACS

**Terminal target.** Bound the actual neutral-window matrix margin uniformly over all admissible windows. The corpus proves that a single finite lower bound on this margin is equivalent to RH. A uniform positive gap at every aperture is unnecessary and conflicts with the proved long-window behaviour under RH. [ACS] [MARGIN-DECAY]

**Objects.** Neutral matrices `N(Q,R,J)`, their two charges, full jet/contact coupling, the dyadic middle, its Green response, Schur excess and the cumulative level. Preserve exact prime-floor maps; replacing them by a free mixing model loses arithmetic.

**Programme.**

1. Use the full `1881/5000` floor to anchor the overlap calculation at every block size. This stage is available. [BLOCK-FLOOR] [GREEN-FIRST]
2. Prove the remaining zero-loss terms in the ratio-three ladder, or a quantitatively sufficient alternative. Retain moments and primitive mass until after the signed cancellation has been used. [GREEN-LADDER] [CHARGES]
3. Handle the first window containing both prime-two and prime-three contacts, with a comparison uniform in refinement. Full coupling must remain: the fixed-rank lowered-product model is excluded. [RANK-WALL]
4. Prove a recurrence for the *actual* losses with a total below the binding ceiling, or establish the equivalent global lower margin directly. The global theorem is the hard closure step. [GREEN-GLOBAL] [GREEN-LOSS]

**Tools to develop:** a retained-charge Schur calculus with explicit cross terms; analytic certificates for Gamma remainders; refinement-compatible response estimates; and sharp tests distinguishing an inadequate comparison from a negative actual form. Contact-process gap/curvature alone cannot deliver this. [TREE-GAP] [TREE-CURVATURE]

**Success criterion:** each new aperture theorem is uniform in block size and proved from the actual arithmetic form. A finite matrix certificate at fixed `R`, or an assumption that the desired Schur complement is nonnegative, does not meet it.

## 2.17 — Research programme for ZCG

**Terminal target.** Establish the conjugation compatibility of the forward heat cover at every positive real nonbranch base, or another theorem forcing the full zero configuration to be real at time zero. The corpus supplies an exact transport criterion for RH. In the usual external heat convention, Rodgers–Tao prove `Λ≥0`; the missing RH bound is `Λ≤0`. Their lower bound cannot be used as an upper bound. [ZCG] [Rodgers–Tao](https://arxiv.org/abs/1801.05914)

**Objects and language.** The forward heat cover, branch times, signed zero pairs, real-branch turn words, conjugation, and the boundary fibre at time zero. Keep arithmetic field automorphisms separate from cover monodromy unless a comparison is constructed.

**Programme.** First exploit the explicit local collision laws to classify which branch words can change the real configuration. Next find an arithmetic invariant of those words that is not shared by generic even heat families. Then prove that the invariant controls all relevant branch events and cannot be lost through zeros escaping to arbitrarily large height as time approaches zero. The explicit heat horizon gives useful fixed-time control but grows rapidly as time shrinks. [HEAT-TURN] [HEAT-HORIZON]

**First breakthrough:** an arithmetic restriction on a specified real-branch turn word, or a uniform zero-height compactness statement in a restricted time/height regime that genuinely reaches a new boundary. Generic transitivity and the index-at-most-two theorem are already available; proving that the group is still larger need not help RH. An odd number of nonreal quartets can produce the full signed group, not a contradiction. [MONODROMY] [HEAT-ODD]

The full group also follows from one isolated off-centre double collision at a forward complex time. This is a precise conditional classification; the existence of that collision is not established by the theorem and its group-theoretic consequence is not a reality obstruction. [HEAT-TURN]

**Failure criteria:** a permutation invariant that is automatic for all even heat families; a positive-time theorem with no `t→0` control; or an unsupported claim that generic analytic relations imply algebraic independence at a special fibre. [HEAT-RELATION]

## 2.18 — Research programme for MC/JAS

**Two receivers, one arithmetic agenda.** MC asks for subpower growth of its actual Möbius Hilbert form. JAS can use the available strip, but still asks for double-exponential-window and cofinal-shell inequalities; other JAS formulations split off an off-line-chain or loud-set condition. These conjuncts are not interchangeable. [MC] [JAS-STRIP] [JAS] [JAS-SUM]

**Objects.** Möbius prefixes and Hilbert forms; prime ancestry words with phase and grade; actual shell power sums; and the exceptional-chain indicator. The producer must preserve these data, not replace them with an arbitrary bounded row or a critical-line model.

The corpus already proves logarithmic two-point Liouville cancellation for each fixed positive shift. Its proof offers prime-dilation and rational-twist tools, but the terminal statement lacks the quantitative rate and growing-parameter uniformity needed here. Developing those is a new arithmetic estimate, not routine summation of the existing limit. [CHOWLA]

**Programme.** Derive an exact coefficient-level bridge for one chosen JAS shell observable to a signed Möbius/reciprocity expression. Specify all weights and ranges, then prove cancellation before taking norms. Use MMD only to remove the fixed-strip premise. Control the remaining shell/window conditions with estimates that are cofinal in the required scale and uniform in the powers appearing in the criterion. Separately settle the finite/tail obstruction when using a criterion with that extra conjunct.

**First breakthrough:** one phase-sensitive shell estimate uniform over a growing family of powers, with no target-blind averaging. A full range matching a terminal criterion would be RH-level; a fixed nontrivial range is a legitimate intermediate target.

**Tools:** reciprocity with explicit phase defects, multiscale summation retaining reciprocal targets, and exact comparison between shell observables and prefix errors. Literal reversible all-prime RFHM sewing is ruled out, so the bridge must allow and control its nonreversible defect. [RFHM] [AVERAGE]

## 2.19 — General Galois theory of the nontrivial zeros

The programme starts with existing Galois constructions. An infinite set of zeta zeros cannot be the root set of one nonzero polynomial of finite degree over a field. The viable formulation is a compatible system of finite-fibre equations and an infinite algebraic extension over a specified source field. It does not assert that zeros are algebraic over ℚ.

**Available objects.** Complete-fibre source fields, finite equations for widths, normal zero extensions, and the prime-value extension over the mixed prime-trace field. The latter has a faithful zero action preserving absolute ordinate; its base already contains transcendental elements over ℚ. A different complete-fibre field has its own RH-sensitive equality theorem. These fields must not be silently identified. [TRACE-FIELD] [FIBRE-FIELD]

**Programme.**

1. Give the prime-trace field a presentation by arithmetic source germs and explicit relations, with controlled finite subfields/composita. The existing equality with source traces is a starting point; the new objective is usable independent relations.
2. Classify finite zero orbits and stabilizers through prime-weight membership. The current conjugate-pair criterion does not force weight `p`, hence does not prove `Re ρ=1/2`. [WEIGHT-ORBIT]
3. Solve the reflection-lift problem through the exact parity condition on finite square relations among its radicands. A lift, if obtained, still needs a theorem identifying it with conjugation to yield criticality. [REFLECTION]
4. Construct a specialization/comparison mechanism between arithmetic fields and the analytic heat cover. Prove exactly what it preserves. Generic heat monodromy and fixed-fibre field automorphisms have different domains and constraints. [MONODROMY] [HEAT-RELATION]

**Tools:** infinite Galois theory through finite subextensions, Kummer square classes, divisor-valued source moments, arithmetic presentations and analytic specialization. **First breakthrough:** a source-derived restriction on the reflection square classes or prime weights that is not merely the corresponding zero-location criterion rewritten. Defining coefficients from the desired zeros and observing that they satisfy the resulting polynomial is insufficient.

## 2.20 — Programme assuming RH is false

The assumption fixes a research direction; it does not provide a counterexample. Two deliverables must be distinguished.

**(a) Prove falsity.** Seek a finite analytic certificate: a compact arithmetic test with strictly negative actual Weil form, or a contour wholly in `1/2<Re s<1` with nonzero ξ winding. Either would give a theorem rather than numerical evidence. A failed lower bound for the form is not a negative value of the form. A negative form in an edited or Selberg model is not a certificate for ζ. [BLOCK-FLOOR] [SELBERG] [EDIT]

**(b) Specify a concrete zero without computation.** Choose explicit rational `a,b,c,d` with `1/2<a<b<1`, and the rectangle `D={a<Re s<b, c<Im s<d}`. Prove analytically that ξ is nonzero on its boundary and has exactly one distinct zero inside, of certified multiplicity `m≥1`. A Rouché comparison giving count one is sufficient in the simple-zero case; the programme must also allow higher multiplicity. Then the contour formula

`ρ = (∮∂D s ξ′(s)/ξ(s) ds) / (∮∂D ξ′(s)/ξ(s) ds)`

defines the unique zero exactly, and the rectangle proves it is off the line. This is a concrete specification without a decimal search. The difficult step is constructing the explicit rectangle and proving its boundary estimates and uniqueness; the formula does not perform that construction. A positive zero count alone proves falsity in this rectangle, but its normalized first moment could average several zeros, so it is not yet the requested single-zero specification.

**Objects and tools.** Analytic divisors, exact contour estimates, prime-defined comparison functions and finite source certificates. The Galois programme can organize a hypothetical quartet and its orbit, but a nontrivial permutation action does not establish that such a quartet exists. [TRACE-FIELD] [WEIGHT-ORBIT]

**AAL falsification is stronger in a different direction:** additionally prove that all sufficiently high zeros lie in a strictly narrower strip. A single off-line rectangle does not supply this tail theorem. [AAL-LAYER]

The first acceptable advance is a strict sign or contour estimate for the actual source in an explicitly stated region. No such counterexample is supplied by this report.

## 2.21 — The one priority question

**Does the actual Weil form on the first full two-prime window admit a finite retained-charge certificate, uniform under arbitrarily fine block refinement, or can that certificate calculus be proved insufficient?**

Use aperture `A=log 2`, equivalently the ratio-four window, with the actual prime-two and prime-three contacts. The target is finite in aperture and unbounded in resolution. Keep the full jet and contact operator; add finitely many moment charges and the exact pole charges. Predeclare the allowed certificate calculus: retained Gamma Taylor terms with proved remainders, regional charged-gap inequalities, exact autocorrelation identities and signed Schur estimates. The certificate must dominate the complete quadratic form, including all cross terms. “Remainder nonnegative” cannot be an unproved certificate field. [CONTACT-JET] [CHARGES] [GAMMA-LAGS]

There are two valuable answers:

- **Constructive answer:** exhibit a finite charge list and an analytic remainder bound proving the actual form nonnegative at this aperture for every admissible test, hence for all corresponding block sizes. This removes a common obstacle for ACS, RW, HF, EWU and OWU and supplies a serious seed for further overlap. It still needs a global recurrence to prove RH.
- **Obstruction answer:** give a uniform family of tests showing that every certificate in a precisely bounded version of this calculus loses the required margin. Identify the term responsible and the minimal enlargement forced by it. This would retire several charge-only variants without retiring the full routes. The existing fixed-rank lowered-coupling no-go is already known; the new question retains the full coupling and must go beyond that result. [RANK-WALL]

Why this question: it combines actual source arithmetic, the strongest finite floor, the exact overlap mechanism and sharp no-go information. It asks for a theorem that could change several route assessments rather than another terminal equivalence. It has a finite-aperture success criterion and a meaningful negative outcome. Neither answer is claimed to settle AAL or RH, and no proof of a strict difficulty ordering is known. The ratio-three question in §2.4 is its immediate intermediate target. [FLOOR] [GREEN-LADDER] [GREEN-LOSS]

<!-- source references -->
[MMD]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/QuasiRiemannHypothesis.lean#L1
[BLOCK-FLOOR]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheFirstOverlapWindowHasAPositiveWeilFloorAtEveryBlockSize.lean#L1
[GREEN-FIRST]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheFirstOverlapStepHoldsAtEveryBlockSize.lean#L1
[HF]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineStateIsUniqueUpToSign.lean#L96
[MONODROMY]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheForwardMonodromyGroupHasIndexAtMostTwoInTheSignedPermutationsOfFiniteSupport.lean#L1
[TRACE-FIELD]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ThePrimeTraceGaloisGroupOfTheZeros.lean#L850
[JENSEN-RUNG]: ../../../formal/GaloisForLFunctions/VerifiedHeightRungs/TheJensenRungAtTheSaddleScale.lean#L117
[GREEN-LADDER]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheExcessOfAnOverlapStepAndTheFourStepLadderToRatioThree.lean#L1957
[WL]: ../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean#L868
[CHMD]: ../../../formal/GaloisForLFunctions/RHTower/CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion.lean#L385
[SZ]: ../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiTransitionCoreAlignedGammaCompletion.lean#L380
[HATC]: ../../../formal/GaloisForLFunctions/HyperbolicArakelovTheory/TheJumpTailFloorNeedsTheFullArithmeticNormalization.lean#L38
[PM]: ../../../formal/GaloisForLFunctions/RingdownOfTheCubicCover/BianchiHorizonRingdownEquivalence.lean#L1
[REFLECTION]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ThePrimeReflectionKernelOfTheZeros.lean#L455
[HEAT-TURN]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheTurnAroundAnIsolatedDoubleCollisionOffTheCentreIsTheExchangeOfTwoPairs.lean#L131
[CONTACT]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheFrobeniusGraphsMeetInThePrimes.lean#L98
[ARTIN]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/EveryArtinLFunctionHasACompletionWithAFunctionalEquation.lean#L220
[RINGDOWN]: ../../../formal/GaloisForLFunctions/RingdownOfTheCubicCover/UnconditionalScatteringResonanceBounds.lean#L1
[FLOOR]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheEvenWeilFormHasAFloorAtAperture1881Over5000.lean#L340
[CHARGES]: ../../../formal/GaloisForLFunctions/LatticeSectionTheory/WindowJumpCounts/RegionalLogarithmicChargedGaps.lean#L1
[GAUSS]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/MoebiusSignedGaussPairingsEndAtThreeFifths.lean#L586
[ACS]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/AUniformLowerBoundOnTheMarginOfTheWindowMatricesForcesTheRiemannHypothesis.lean#L505
[GREEN-GLOBAL]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheExcessOfAnOverlapStepAndTheFourStepLadderToRatioThree.lean#L2178
[AAL-TRANSPORT]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/TheAbscissaLawsOfAZeroConfiguration.lean#L106
[AAL-LAYER]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/TheFailureOfTheAbscissaLawIsAFiniteLayer.lean#L33
[ZCG]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheForwardMonodromyDeterminesTheReflectionAndTheConjugationOfTheZeros.lean#L186
[HEAT-HORIZON]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/HeatScaleRepulsion/TheExplicitHeightOfTheWeylHorizon.lean#L356
[CENSUS]: ../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ZetaSamplingPrimePoleFourth.lean#L262
[CENSUS-AMBIGUITY]: ../../../formal/GaloisForLFunctions/IncommensurableGaborPinching/SplitBandMomentAmbiguity.lean#L1
[WEIGHT-ORBIT]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheOrbitOfAZeroIsItsConjugatePairIffItsWeightLiesInThePrimeTraceField.lean#L1
[CONTACT-JET]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/WeilsOffDiagonalIsContactsPlusJets.lean#L125
[SELF-PAIRING]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheCouplingsOfAWindowAreNotMixedAreasAndTheIndexForcesLogarithmicSelfPairings.lean#L268
[GAMMA-LAGS]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheGammaRemainderRetainsHigherLagsThroughRadiusTwo.lean#L1
[RANK-WALL]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheBindingOfTheTwoHalvesOfAWindowOfRatioFourHasRankProportionalToTheBlockSize.lean#L929
[GREEN-LOSS]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheLossOfAnOverlapStepIsAdditiveBelowTheBindingEnergyOfTheMiddle.lean#L568
[DECOMPLETE]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/TheWallIsThePriceOfCompletion.lean#L211
[AVERAGE]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/TheAverageRowIsBlindToTheTarget.lean#L1
[JAS-STRIP]: ../../../formal/GaloisForLFunctions/RHTower/JointAncestryDoubleExpWindowsDyadicShells.lean#L26
[HEAT-ODD]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/AnOddNumberOfQuartetsOfNonrealZerosAtARealTimeGivesEverySignedPermutation.lean#L372
[QUARTET-PARITY]: ../../../formal/GaloisForLFunctions/RHTower/OrbitParityOffLine.lean#L116
[ROOT-WALL]: ../../../formal/GaloisForLFunctions/RHTower/GlobalParityWall.lean#L117
[BEZOUT]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/BezoutIsAnEqualityOnThePlanarSquare.lean#L124
[SELBERG]: ../../../formal/GaloisForLFunctions/CompactHyperbolicSurfaces/SmallEigenvalueZeta.lean#L113
[AAL-OSCILLATION]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/TheOneOffsAreFiniteOscillationsOfThePrimeError.lean#L736
[AAL-LANDING]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/TheLandingLaw.lean#L117
[EDIT]: ../../../formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/AFiniteLayerWithATailOverTheRationalPrimes.lean#L488
[EDIT-DEFECT]: ../../../formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/FakeEditsWithSubpolynomialDefectEnergy.lean#L67
[PERFECT]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/APerfectSquareKeepsNoContact.lean#L81
[WD]: ../../../formal/GaloisForLFunctions/MultiscaleMollifiedZetaField/TheWidthIsReadInOneWindow.lean#L485
[WD-PROPORTION]: ../../../formal/GaloisForLFunctions/MultiscaleMollifiedZetaField/TheExponentOfTheMollifiedErrorIsRigid.lean#L605
[WD-COFINAL]: ../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/LongMoebiusSecondMomentRigidity.lean#L704
[WD-SHORT]: ../../../formal/GaloisForLFunctions/MultiscaleMollifiedZetaField/TwistedSecondMomentsBelowSquareRoot.lean#L128
[WD-BLOCK]: ../../../formal/GaloisForLFunctions/MultiscaleMollifiedZetaField/TheTwistedMomentFactorsOverBlocks.lean#L585
[MZF-PROPORTION]: ../../../formal/GaloisForLFunctions/MultiscaleMollifiedZetaField/TheTwistedMomentGivesAPositiveCriticalProportion.lean#L109
[WD-RAW]: ../../../formal/GaloisForLFunctions/ArithmeticProduction/LongIntegerPolynomialsSeeParity.lean#L1
[LONG-MOMENT]: ../../../formal/GaloisForLFunctions/ArithmeticProduction/LongMollifiersImplyCriticalClustering.lean#L422
[MARGIN-DECAY]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/UnderTheRiemannHypothesisTheMarginOfALongWindowTendsToZero.lean#L442
[TREE-GAP]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/TheDilationProcessHasNoGap.lean#L174
[TREE-CURVATURE]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/TheFloorTreesHaveCurvatureZero.lean#L1
[HEAT-RELATION]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/AnAnalyticRelationAmongZerosInDistinctPairsHoldsOnEveryConfigurationOrOnADiscreteSet.lean#L1
[MC]: ../../../formal/GaloisForLFunctions/RHTower/MobiusHilbertFormEquivalence.lean#L219
[JAS]: ../../../formal/GaloisForLFunctions/RHTower/JointAncestryShellAmplitudeAbscissaDuality.lean#L213
[JAS-SUM]: ../../../formal/GaloisForLFunctions/RHTower/JointAncestryShellLoudSetCriterion.lean#L295
[CHOWLA]: ../../../formal/GaloisForLFunctions/LogarithmicChowla/LogarithmicChowlaTheorem.lean#L90
[RFHM]: ../../../formal/GaloisForLFunctions/RHTower/JointAncestryAllPrimeReversibleRFHMSewingNoGo.lean#L132
[FIBRE-FIELD]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheFieldOfCompleteFibreTraces.lean#L409
