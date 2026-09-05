# Corpus-wide search for an arithmetic proof architecture

- **ID:** RH-CORPUS-20260905
- **Stage:** 1-in-progress
- **Type:** CANDIDATE SEARCH; no RH implication or novelty claim established
- **Source:** `scripts/formal_tools.py research`; current frontier map; audited Lean declarations; primary literature.
- **Statement:** Find a source-derived operation whose exact arithmetic constraints can distinguish horizontal displacement without importing an RH-equivalent estimate or selecting the desired zeros in its definition.

**Current result: ONE PROVISIONALLY ADMITTED ARCHITECTURE.** Euler-deletion quasi-shuffle refinement survives the current bounded corpus/literature collision screen. Its finite scaling core is proved, but the zero-to-refinement-coherence producer is open; there is no RH implication or global novelty certificate. Multiplication-fibre stabilization is now retired together with the earlier branches.

## Binding research scope

Use `scripts/formal_tools.py research` together with `rg` on definitions and proof bodies. The user explicitly excludes Suzuki, Hedenmalm, Weil positivity (typed “weyl positivity”), Connes, Burnol, Hilbert–Pólya, all spectral approaches, Gamma, and other usual RH routes, including relabelled versions. A new subsidiary object with an old decisive open step does not qualify. The intended output is a new mechanism, not more retrieval, generic obstruction lemmas, or a familiar criterion in new vocabulary. Early ideas need not yet imply RH, but must be explicit enough to conjecture about and falsify.

These exclusions are user instructions, not mathematical impossibility theorems. They belong here, not in the factual `STATUS.md` ledger.

## Goal and scope

Search the full indexed corpus, including the non-RH theorem areas. Ranked search is discovery, not a proof-body audit of every declaration. Record coverage and inspect the exact hypotheses and proofs of candidates before using them. Literature searches can establish ancestry and collisions, but cannot certify absence from all literature.

## Work plan

1. Inventory corpus and existing frontier; search independent mathematical mechanisms across all areas.
2. Select a concrete source operation; write falsifiable conjectures and test both its arithmetic realization and its claimed consequence.
3. Prove, reject, or pivot. Distinguish established identities from proposed RH bridges. Extract the strongest meaningful positive survivor of any retired realization.
4. Formalize only closed proved statements, using scratch checks, foreground single-process Lean runs, narrow leaf builds, umbrella wiring, and axiom/lint audits.
5. Record route-independent consequences in `universal-law-field/STATUS.md` only if new and supported. Keep technical attempts here.

## Current evidence

- Existing source/receiver boundaries forbid treating an RH equivalence as a producer.
- The earlier normalized rank-one theta sewing realization has zero tangent already at first order; it supplies no selective nonlinear obstruction. The arithmetic formal-deformation obstruction still lacks an independently constructed Xi-linked source satisfying its bounds.
- Existing working-tree changes predate this audit and are preserved.
- The literal Euler-deletion coefficient `a_q(n)=1-q[q∣n]` is already in the corpus. Its scalar Dirichlet series is only `(1-q^(1-s))ζ(s)`, so scalar combinations are forbidden as producers.
- Pointwise `2×3` fusion has zero block mass and an integer first moment, but that moment is origin-sensitive and trivial modulo the canonical period. This kills the first attempted carry-orientation detector.
- Multiplication-fibre stabilization passed its literal `2×3` test but failed the generic-mechanism and factorization gates. Corpus modules already contain the exact Jordan overlap `min(positive mass, negative mass)`, signed quotient loss, reserve fusion cocycle, abelian odometer, and product-sign decomposition. The proposed stabilized count is therefore a specialization of existing machinery; its expected Dirichlet series also factors through `ζ(s)^2`.
- The current survivor keeps chronological order rather than multiplication fibres. A modulus-`P` Euler-deletion block is the jump word `(1,…,1,1-P)`: level one is exactly `0`, while the quasi-shuffle bracket `Σ jump²` is `P(P-1)`. Replicating a nonzero quadratic source `P` times scales its bracket by `P`; Euler dilation scales it by `|P^(1-s)|²=P^(2-2 Re(s))`. Equality of these independently defined refinements forces `Re(s)=1/2`.

## Open obligations

No RH-producing theorem has passed the gates. Current candidate is a source-construction program, not an asserted RH criterion. Immediate obligation is the QSR producer below: derive quasi-shuffle refinement coherence from the complete family of zero-valued Euler-deletion series, rather than assuming quadratic balance.

## Conjecture / failure / pivot

**C1: ordinary products of theta resonant responses retain the same source. Rejected.** The corpus equation is `u_alpha' = -i alpha u_alpha - i k`. Consequently `(u_alpha u_beta)' = -i(alpha+beta)u_alpha u_beta - i k(u_alpha+u_beta)`. The forcing changes; causal/anti-causal agreement of the factors does not make `alpha+beta` another zero of the original transform. The positive survivor is the exact response-dependent forcing law. This is an immediate product-rule consequence of `HedenmalmThetaEigenODE`, not a novel mathematical principle or a retired general nonlinear route.

**C2: the ordinary Volterra product algebra itself is radically new. Rejected by literature.** Guo–Gustavson–Li, *An algebraic study of Volterra integral equations and their operator linearity*, Journal of Algebra 595 (2022), [arXiv:2008.06756v2](https://arxiv.org/abs/2008.06756), treats matching twisted Rota–Baxter identities and reduction to iterated integrals for separable kernels. Hedenmalm's actual source spectral architecture is itself published: [arXiv:2606.17494](https://arxiv.org/abs/2606.17494). Neither is new merely because combined.

**C3: the equal-time rank-one sewing algebra also closes unequal-time histories. Abandoned by the research-scope correction.** The elementary exponent observation was

`t(i+j+2a)^2 + u(i-j)^2 = (t+u)(i^2+j^2) + 2(t-u)ij + 4ta(i+j) + 4ta^2`.

Here `a=0` and `a=1/2` are the two parity sectors; `t,u` absorb pi. A Gaussian/Vandermonde minor classification was considered. Only mathlib API names were checked in `/tmp/hgt-rh-audit-20260905/Api.lean`; no rank theorem was written or checked. This would remain auxiliary standard mathematics, not the requested architecture.

**C4: pointwise coprime block fusion has a canonical oriented moment. Rejected.** For

`a_q(n)=1-q[q∣n]`, `c_{p,q}(n)=a_p(n)a_q(n)`, `P=pq`, and coprime `p,q>1`, direct inclusion--exclusion gives

`sum_(n=1)^P c_{p,q}(n)=0`,

`sum_(n=1)^P n c_{p,q}(n)=P(p-1)(q-1)/2`.

For `p=2,q=3`, the cell is `(1,-1,-2,-1,1,2)`, with first moment `6`; interval reversal gives `-6`. This initially looked like an oriented carry charge. It fails: cyclically changing the block origin changes the integer moment, while its residue modulo `P` is zero because `(p-1)(q-1)` is even. Corpus audit also found the same two-prime inclusion--exclusion polynomial in `MobiusLaplaceCriterionFrontier`; using its derivative would re-enter an explicitly excluded Möbius--Laplace route.

- **Exact killing mechanism:** boundary-origin dependence plus zero class in the cyclic quotient.
- **Strongest positive survivor:** exact zero-mass/first-moment formula and its literal `2×3` Lean certificate.
- **New insight:** scalar pointwise CRT fusion cannot supply canonical orientation; the source operation must retain multiplication fibres before scalar collapse.
- **Status:** finite `2×3` statement formalized; general paper identity proved above; no RH consequence.

**C5: multiplication-fibre stabilization of a coprime deletion grid. Rejected after the stronger corpus collision screen.** Put

`w(m,n)=a_2(m)a_3(n)`, `1≤m≤2`, `1≤n≤3`,

and push forward along `π(m,n)=mn`:

`(π_*w)(k)=sum_(mn=k) w(m,n)`.

Every row and column sum of `w` is zero. Nevertheless `π` is noninjective: `(1,2)` and `(2,1)` meet at `2` with weights `+1,-1`. If `P_k,N_k` are positive and negative source masses entering fibre `k`, then `min(P_k,N_k)` is `1` at `k=2` and `0` elsewhere. Thus the total least-action cancellation count is `1`, although the aggregated coefficient at `2` is `0`. Separately, exact table calculation gives

`sum_(m,n) w(m,n)^2 = 12`,

`sum_k (π_*w)(k)^2 = 10`,

`Delta_mul(w)=12-10=2`.

The literal fact is correct and survives as positive content. It does not support a new architecture. `HTGeometry/ConstitutiveTVConflictColoring.lean` already proves the exact fibre overlap as `min(positive mass, negative mass)`; `SignedCancellationQuotient.lean`, `ConstitutiveCausalJordanFormation.lean`, and `AbelianRepairLeastAction.lean` already provide quotient loss, reserve cocycle, and odometer semantics. `RHTower/MobiusCoprimeProductSignExtraction.lean` already carries signed product-pair mass in an excluded Möbius family. Thus source separation did not escape generic signed-measure machinery.

### Rejected architecture sketch: multiplication-fibre repair tower

1. Build coprime block-deletion grids entirely from literal integer divisibility.
2. Push them through multiplication and cancel opposite signed chips inside each product fibre by an abelian least-action repair. Retain odometer/cancellation data, not only the pushed scalar coefficient.
3. Refine blocks cofinally and prove source-fixed compatibility of stabilization under adding a new coprime block.
4. Attach the complex weight `k^(-s)` only after fibre stabilization. A ζ zero kills scalar augmentation because each deletion series has a ζ factor; the retained stabilization class is not allowed to use that factorization as its definition.
5. Seek a zero-local closure law forcing the stabilized class to vanish, and a separate source theorem showing off-critical horizontal displacement leaves a nonzero class. No functional equation, `1-s`, Γ, θ, spectral operator, Möbius inversion, or Weil positivity may enter either statement.

### Falsification gates and outcome

- **Factorization gate:** retire if every stable observable is determined by the scalar Dirichlet convolution coefficient or a multiple of ζ.
- **Generic-energy gate:** retire if the construction reduces to an ordinary mean-square/mollifier diagonal; the retained datum must be an integer fibre-repair class.
- **Source gate:** graph, firing rule, and observable must be fixed before choosing a zero.
- **Critical-line gate:** `1/2` must emerge from a proved source scaling/duality law, not a half-density inserted into a definition.
- **Analytic gate:** use bounded-partial-sum Dirichlet continuation on `Re(s)>0`; importing the completed zeta functional equation retires this route.
- **Novelty gate:** failed. Corpus contains the generic source-separated cancellation object, not merely its ingredients.

### Retirement certificate: the full cancellation count

The finite cell alone does not establish that the retained count escapes scalar arithmetic. For the cofinal rectangular grid, every fixed positive product `k` eventually contains all divisor pairs of `k`. Let `C(k)` be their signed sum, `A(k)` their total absolute source mass, and `O(k)` the number of opposite-sign unit pairs cancelled. The proposed exact classification is

`2 O(k) = A(k) - |C(k)|`.

For the literal `2,3` deletion source, put `D_r(k) = d(k/r)` when `r` divides `k`, and zero otherwise, where `d` counts positive divisors. The stronger candidate identity to verify is

`O = D_2 + D_3 - D_4 - D_9 - D_6 + D_12 + 2 D_18 - 2 D_36`.

If established for the actual stabilized source, its Dirichlet series on the absolute-convergence half-plane is

`[x+y-x^2-y^2-xy+x^2 y+2xy^2-2x^2 y^2] zeta(s)^2`,

with `x=2^(-s)`, `y=3^(-s)`. That fails the candidate's factorization gate for the specified count. The displayed general count formula remains a paper calculation rather than a Lean theorem, but the generic corpus collision independently retires this route. No further multiplication-fibre scan is a priority.

**C6: Euler-deletion quasi-shuffle refinement. Provisionally admitted.** For modulus `P=q+1`, retain the deletion block as the chronological jump word

`J_P=(1,…,1,1-P)=(1,…,1,-q)`.

Its ordinary endpoint and diagonal quasi-shuffle bracket are

`L₁(J_P)=Σ_j J_P(j)=0`,

`[J_P,J_P]=Σ_j J_P(j)^2=P(P-1)`.

For a complex jump word `x`, let `H₂(x)=Σ_{i<j}x_i conjugate(x_j)`. The finite Hermitian quasi-shuffle identity is

`|Σ_i x_i|²=Q(x)+2 Re H₂(x)`, where `Q(x)=Σ_i|x_i|²`.

Thus scalar deletion erases level one while the deterministic iterated-sum source retains a nonzero level-two bracket; for a closed nonzero-bracket word, `H₂` is nonzero. Chronological concatenation and amplitude scaling give

`H₂(rep_P x)=P H₂(x)` when `Σx=0`,

`H₂(c x)=|c|² H₂(x)`.

For the Euler amplitude `c=P^(1-s)`, these are the two independently defined refinement laws

`Q(rep_P x)=P Q(x)`,

`Q(P^(1-s)·x)=|P^(1-s)|² Q(x)=P^(2-2σ)Q(x)`, where `σ=Re(s)`.

Consequently equality of the chronological second levels cancels the proved nonzero `H₂`, gives `P=P^(2-2σ)`, and therefore gives `σ=1/2` for every `P>1`. The half exponent is the unique fixed exponent of chronological multiplicity versus Euler amplitude; it is not inserted as a half-density.

### Provisional architecture: deletion-signature refinement tower

1. Treat every periodic Euler deletion `a_P(n)=1-P[P∣n]` as a chronological, deterministic quasi-shuffle path. Keep bracket and higher iterated-sum levels before scalar summation.
2. Use bounded partial sums to land the level-one path on `Re(s)>0`. If `ζ(ρ)=0`, every deletion endpoint `(1-P^(1-ρ))ζ(ρ)` is zero without functional equation or reflection.
3. Construct a cofinal resolution category generated by chronological `P`-fold subdivision and Euler dilation. Its objects and refinement maps must be fixed from integer divisibility before selecting `ρ`.
4. Prove **QSR (quasi-shuffle refinement coherence):** simultaneous level-one closure for all deletion moduli forces at least one nonzero chronological Hermitian second level to identify chronological replication with Euler dilation.
5. Apply the proved scale law to QSR. Nonzero bracket cancels, leaving `P=P^(2-2 Re(ρ))`, hence `Re(ρ)=1/2` directly; no left/right symmetry is required.

### Live falsification gates

- **Endpoint gate:** a closed path may have nontrivial signature. Level-one closure alone does not imply QSR; making that inference retires the route.
- **Balance gate:** QSR must follow from all-modulus arithmetic compatibility. Assuming equality of the two quadratic scales is exactly assuming the desired exponent in disguise.
- **Renormalization gate:** infinite iterated sums must receive a canonical, cofinal definition independent of cutoff schedule. An adaptive subtraction depending on `ρ` is forbidden.
- **Non-`L²` gate:** square summability at `σ>1/2` is only the domain where the level-two object can exist. It is not a contradiction and cannot serve as the producer.
- **Source gate:** modulus system, chronological refinement, and bracket must be fixed before the zero. No functional equation, `1-s`, Γ, θ, spectral operator, Möbius inversion, or Weil positivity may enter QSR.
- **Novelty gate:** iterated-sums/quasi-shuffle signatures and tree-like signature theory are published mathematics; only the Euler-deletion refinement synthesis survived exact-phrase searches. This is bounded negative evidence, not proof of novelty.
- **Nearby-corpus gate:** `EulerSquarefreeWickQuadraticCommonRefinementDescent` is a `2×2` reflection descent whose target already carries a half-density and whose all-zero statement is RH-equivalent; `CycleDeletionShiftedHankelRankOneUniversalityLaw` is shape-blind shifted-Hankel rank one. Both violate scope and neither contains chronological deletion-word scaling. Do not import their “common refinement” vocabulary or results into QSR.

### Current conjecture ladder

- **QSR-0 — proved:** every finite deletion block has zero level one and bracket `P(P-1)`.
- **QSR-1 — proved:** finite Hermitian quasi-shuffle identity, exact concatenation cross term, closed-source replication law, amplitude-scaling law, and the actual deletion-word specialization. Chronological second-level coherence at a nonzero deletion word forces `σ=1/2`.
- **QSR-2 — next:** define cutoff-independent second-level deletion signatures on `Re(s)>1/2` from chronological iterated sums and prove their Euler dilation/interleaving law.
- **QSR-3 — unproved producer:** derive refinement coherence from simultaneous zero endpoints for all `P`, using all-modulus compatibility rather than generic tree-like closure.
- **QSR-4 — later:** extend or renormalize the construction to all `Re(s)>0` without importing reflection; then attach the actual zeta-zero landing.

## Rejected proposal: ordered unequal-time lattice responses

Retain independent integration times, parity sectors, and integer labels in products of the *fixed* theta source's causal/anti-causal responses. Apply lattice reindexing before integrating or projecting to a single source channel. The new research object would be the resulting hierarchy of ordered, coupled-lattice response integrals. It differs from changing normalized rank-one theta amplitudes, and from assuming products stay in the original one-source equation.

The proposed residual operation was never constructed. Its ancestry and intended starting point violate the user's scope. Do not treat the absence of a literal search match for the combined description as novelty.

## Discrete and exact-algebra audit after the correction

| Seed | Exact evidence inspected | Assessment |
|---|---|---|
| Word rewriting | `HTGeometry/ConstitutiveCriticalCompletionMechanics.lean`, lines 1–215: each rule decreases the number of `a` letters; each finite rulebook has an explicit nonjoining critical pair; the next joining rule is already an old semantic equality. | Separates execution from equivalence. No literal integer-arithmetic construction or RH consequence. Repeating this toy is not a new architecture. |
| Sequential repair | `HTGeometry/ConstitutiveSequentialRepairHeredity.lean`, lines 1–210: Arens topology has two sequential-closure layers while ordinary closure is stationary. | Known topological mechanism. No arithmetic realization selected. |
| Primitive execution | `HTGeometry/ConstitutivePrimitiveExecutionGenesis.lean`, lines 1–200: positive locally admitted laws decompose by induction on degree; bounded grammar completeness is equivalent to a bound on indecomposable degrees. | Exact abstract resource theorem. The required arithmetic family and its primitive structure were not constructed. |
| Carry identities | `research` plus `rg` in `ConstraintFrameRelativity/WittCarryBoolean.lean`, `ConstitutiveExchangeCentralPromotion.lean`, and `ConstitutiveCoefficientLiftTransgression.lean`. The inspected Boolean carry is intersection; the integer identity separates a squared gcd factor. | Neither Boolean addition nor a central carry can silently stand for the full addition/multiplication of integers. No qualifying synthesis produced. |
| Multiplication fibres | `RHTower/Sieve/FiniteFiberPartition.lean` and `MollifiedTwistedDiagonalProductEnergy.lean` provide generic fibre counts and product-coefficient square energies; `HTGeometry/ConstitutiveTVConflictColoring.lean`, `SignedCancellationQuotient.lean`, `ConstitutiveCausalJordanFormation.lean`, and `AbelianRepairLeastAction.lean` provide exact overlap, quotient loss, reserve cocycle, and odometer semantics. | Retired. Source-separated cancellation is already generic corpus machinery; expected cofinal count factors through `ζ²`. Literal `2×3` no-go/positive certificate retained. |
| Deletion quasi-shuffle refinement | Corpus queries for rough paths, iterated-sum signatures, antisymmetric sums, path dilation, tree-like reduction, and quadratic-variation scaling; exact inspection of `CompleteResolutionClockAreaTransgression.lean`, `EulerSquarefreeWickQuadraticCommonRefinementDescent.lean`, `CycleDeletionShiftedHankelRankOneUniversalityLaw.lean`, and generic shuffle/cocycle modules. | Ordinary signature/area mechanisms exist. Nearby “common refinement” uses an inserted half-density/reflection and nearby cycle deletion is shifted-Hankel; neither contains chronological deletion-word scaling. Provisional only; QSR producer is completely open. |
| Arithmetic differential curvature | Exact-phrase corpus queries for Fermat quotient, p-derivation, delta ring, Wieferich, and arithmetic curvature, followed by `rg` of candidate source files. | Search misses did not establish novelty. Barrett–Buium already construct curvature from Fermat quotient operations: [arXiv:1512.02525](https://arxiv.org/abs/1512.02525). Rejected as a new field claim. |
| Second-kind arithmetic cohomology | Primary abstract of Efimov, [arXiv:1506.00257](https://arxiv.org/abs/1506.00257). | This is published mathematics. Its displayed all-localization nontriviality condition is equivalent to infinitude of Wieferich primes, so assuming that condition would introduce another unresolved arithmetic question. No such premise adopted. |

## Coverage and verification

- Index snapshot: 32,233 files, 392,125 declarations, 3,855 gap markers. All-index search scope is not a proof-body audit of all declarations.
- 114 saved numbered corpus queries. Query wording and capped hit counts are in the adjacent search manifest. Search terms are OR-ed; ranked results can omit relevant low-ranked declarations. Exact `rg` searches supplied definition and proof-body checks. No absence or completeness theorem follows from search misses.
- Lean modules `CoprimeBlockCarryTransgression`, `CoprimeBlockMultiplicationFiber`, and `EulerDeletionQuasiShuffleScaling` compile directly and passed targeted leaf builds; all three are wired into `RHTower.lean`. The new premise-free capstone proves zero level one, exact deletion bracket, and uniqueness of the half exponent under quadratic scale equality. `/tmp/hgt_coprime_fiber_axioms.lean` reports only standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound` for all three capstones and the finite refinement implication. No full build ran; every owned Lean/Lake command exited.
- The repository-wide formal lint gate passed before unrelated concurrent Brizard additions, then failed only on an unreachable module under `GaloisForLFunctions.HTGeometry.DispersivePDE` (latest observed: `BrizardElasticaJacobiSystem`). This audit did not edit that disjoint work. Targeted modules have no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declarations.
- A multicore exact-integer Runpod scan was prepared to test defect sign beyond the `2×3` cell, then retired before execution because the generic corpus collision and `ζ²` factorization already killed the route. An initial SSH probe used an incorrectly transcribed host and is disregarded; authentication to the exact supplied endpoint `157.157.221.29:27094` was later verified. `2-fully-proven/computations/coprime-deletion-multiplication-fibres/REPORT.md` records this; no numerical conclusion was drawn and no local substitute ran.
- `universal-law-field/STATUS.md` records only route-independent finite source facts, retired mechanisms, and the live refinement-coherence requirement.
- The goal remains active. A radical source architecture has passed two finite gates; cutoff-independent signature construction, QSR, zero landing, novelty audit, and any RH implication remain open. Rejected C1--C5 branches are not approved continuations.
