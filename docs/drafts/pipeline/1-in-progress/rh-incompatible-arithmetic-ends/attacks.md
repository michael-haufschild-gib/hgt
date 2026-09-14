# Candidate attacks and whole-route verdicts

No candidate below passed the primary-conjecture gate. These are rejected mechanisms and bridge tests, not a new RH route or new mathematical theorems.

## A. Complete all finite proofs of compatibility

**Proposed mechanism.** Every finite arithmetic stage is exact and every fixed coordinate stabilizes; infer one compatible infinite realization. Use its existence to exclude an off-line zero.

**Proof attempt.** Pass exactness through the coordinate limit. The missing step is continuity in the topology retaining the source relation, rather than in the coordinate topology.

**Exact failure.** The existing literal tower satisfies both finite exactness and coordinate stabilization for every grade. On its physical strip, failure of source-provenance convergence is equivalent to nonzero grade. `RouteRCompletionPhantomNoether.lean` proves the whole conjunction, not merely an abstract counterexample. On Xi support its global absence is exactly RH. `RouteRXiInterfinityStableCompletion.lean` identifies the same obstruction with the surviving stable class.

**Positive content retained.** A precise distinction between coordinate convergence and survival of an arithmetic relation, already formalized in those modules. No new positive theorem is being claimed.

**Whole-route verdict.** The proposed completion principle is neither supplied by finite exactness nor new. Retire this as a candidate for the requested new route; do not retire every possible source-specific infinite compatibility theorem. Moreover, this old defect survives *off* the line; merely calling it a meeting failure does not provide the user's requested explanation of actual on-line zeros.

## B. Force agreement by simultaneous rational refinement

**Proposed mechanism.** The two reflected arithmetic refinement processes must agree because the same moduli compose in either order.

**Exact source.** For positive integer n and Re(s)>0, define

    R_n(s) = [sum_{k=0}^{n-1} zeta_H(s+1,(1+k)/n)] / [n zeta(s+1)].

Every series is in its absolute-convergence domain. `rationalHurwitzFiberResponse_eq_cpow` proves R_n(s)=n^s. Thus R_mn(s)=R_m(s)R_n(s), at every such s; this is a source identity, not an assumption about zeros.

**Proof attempt and failure.** Set A_n=R_n(conj(s))^(-1), B_n=R_n(1-s)^(-1), D_n=A_n-B_n. Both compositions give

    D_mn = D_m A_n + B_m D_n = D_n A_m + B_n D_m.

Subtracting the two expressions gives D_m D_n-D_n D_m=0. It places no additional condition on D. Commuting refinement therefore cannot supply D_n=0. The corpus already proves this crossed identity (`rationalHurwitzFiberReducedReflectionSeam_mul_comm_relation`). Separately, agreement of the reflected packets for n>1 is exactly Re(s)=1/2 (`rationalHurwitzFiberResponse_reflection_fixed_iff`). No zero equation is used in either reduction.

**Positive content retained.** Exact finite source realization of each scale response and exact crossed composition, already proved in the corpus. They show exactly which information normalization discarded.

**Whole-route verdict.** A law that only uses these normalized responses is the existing scale/reflection receiver. Any successor must retain different source information and derive a new relation using actual arithmetic. The argument above does not refute agreement *at zeta zeros*; it shows why the proposed composition argument does not prove it.

## C. Read a square-root threshold from gluing topology

**Proposed mechanism.** A generic transition in the ability to join increasingly large patterns selects square-root scale, hence the critical line.

**Hostile test from current literature.** Salo–Törmä, [Two block gluing constructions](https://arxiv.org/html/2605.31237v1), Theorem 2, realizes a wide class of prescribed growth functions as gluing gaps, including square-root growth. The theorem supplies no arithmetic reason to select that member of the class. Introduction and definitions were read; the full construction was not audited or formalized here.

**Whole-route verdict.** Reject the inference from generic gluing topology to the exponent. This is not a theorem excluding all topological RH arguments. A literal arithmetic object and its scale law remain necessary. No new no-go theorem or positive survivor is asserted.

## D. Recent external mechanisms

- [Anabelian Geometry in Families](https://arxiv.org/html/2608.21232v1), Theorem A and its stated scope: a rigidity result over a finite-type base with a hyperbolic-curve target. Excluded by the user's no-rigidity rule; no RH transfer attempted.
- [Resurgence of high-energy string amplitudes](https://arxiv.org/html/2604.07444v1): introduction, section outline and intersection-pairing conclusion inspected. It relates different asymptotic sectors through actual contour/connection data. No arithmetic/zeta source connection has been constructed here; finite string-amplitude thimbles cannot be asserted to model the required infinite arithmetic process. Treat as a methodological lead, not an adopted route or imported theorem.
- [On adelic Hurwitz zeta measures](https://arxiv.org/abs/1711.03505), abstract only: profinite-valued interpolation of p-adic functions. No complex-valued measure or Archimedean comparison follows from that abstract. Not a new paper or a new route.

## Right-problem checkpoint

The unresolved task remains construction of a new arithmetic primitive and law, not another equivalence or completion library. None of A–D provides one. No primary conjecture has been frozen by weakening the goal toward an easy Lean statement. Next candidate must explain which source information it retains, why the old countertests no longer apply, how its failure corresponds to actual zeros, and what risky consequence distinguishes it from existing families.

## E. Put the incompatibility into descent at the Archimedean place

**Proposed mechanism.** A difference between ordinary and lax descent at infinity supplies a previously missing compatibility condition.

**Current source.** Ming Ng, [The Archimedean Place is a Blurred Interval at Infinity](https://arxiv.org/html/2609.09117v1), 8 September 2026. Theorem 5.9 identifies the Archimedean lax-descent quotient with an upper-real interval. Discussion 7.11 observes that simultaneous exponent rescaling preserves the product formula. Problems 7.9 and 7.12 leave global assembly and the completion family open. The introduction, theorem statements, Conclusion 6.9 and final local-global discussion were inspected; no claim of auditing the full proof.

**Proof attempt.** Try to make a complex parameter visible through the scalar transports already supplied by the arithmetic refinement law. That law is `R_n(s)=n^s` from B, in its proved domain. For nonzero weights `w(x)`, transports `v ↦ w(y) v / w(x)` become identity maps after the fibre coordinates change to `v/w(x)`. They are invertible scalar comparisons at every parameter where the weights are nonzero. This algebraic observation is a screening calculation, not a new formalized theorem about the paper's topos.

**Failure and positive content.** No map from an actual zeta zero into the paper's noninvertible descent data was constructed. The surviving scalar data are the same exact scale responses already proved in B. Identifying the paper's normalization parameter with `Re(s)`, or declaring the reflection fixed point to be the only admissible point, would insert the missing condition.

**Whole-route verdict.** The paper offers a different description of infinity, but this proposed scalar transfer does not turn it into a new RH route. This does not rule out a future construction using genuinely noninvertible arithmetic comparisons. No new topos theorem or no-go theorem is claimed.

## F. Retain every finite arithmetic cylinder and chronological word

**Proposed mechanism.** The individual arithmetic fibres might retain a cross-process constraint lost by the normalized response in B.

**Actual corpus test.** `EulerDeletionCylinderReconstruction.lean` already reconstructs the product-modulus channels and finite cylinder channels in both directions, at every finite word length and cutoff, also with arbitrary conjugation choices. Its `cylinder_zeroEndpoints_iff_base` proves that simultaneous cylinder endpoint closure is equivalent to the original channel closure. `coordinate_norm_sum` gives the exact row cost `2^(card S)-1`, and `orderedWord_coefficient_norm_sum` multiplies those costs across word positions. Separately, `EulerDeletionWordHistory.lean` admits one infinite carrier uniformly over all word lengths for each fixed deletion modulus and `Re(s)>1/2`.

**Proof attempt and failure.** Finite reconstruction does not provide a bounded coordinate change as the arithmetic family grows. The explicit row cost grows with the family. The all-word convergence theorem fixes the modulus and cannot be used as a uniform theorem in that additional variable. No bound on the actual arithmetic source in this joint limit was proved here.

**Positive content retained.** Exact finite correspondence and its explicit expansion cost, already in the cited source. This is source inspection, not a fresh Lean certification of those two modules.

**Whole-route verdict.** Retaining these finite fibres is existing Euler-deletion machinery. A new joint-limit law would be substantive work on that existing family, so it would still need to pass the user's prohibition on redressing old candidates. No new candidate is admitted by this test.

## Current right-problem checkpoint

E changes the ambient geometry but has no arithmetic zero correspondence. F retains arithmetic information but is already an existing family. Neither supplies the requested new primitive and source-derived law. Optimizing the Hurwitz bridge is work on the user's Lean-code request; it is not mathematical progress toward RH.

## G. Use inequivalent notions of ends of an arithmetic graph

**External stimulus.** Aurichi, Magalhães Júnior and Pinto, [Edge-ends versus topological ends of graphs](https://arxiv.org/html/2602.14943v1), February 2026. Theorem 2.6 characterizes when distinct undominated vertex-ends remain distinct after passing to edge-ends. Definitions and the displayed characterization proof were read; no theorem from the paper was formalized here.

**Proposed transfer and failure.** Compare the additive and multiplicative ends of an integer-operation graph. Merely labelling its fixed edges by nonzero complex powers changes neither its vertex cuts nor its edge cuts. No parameter-dependent graph, distinguished ray, or zero correspondence was constructed. The graph theorem does not create that missing arithmetic dependence.

**Whole-route verdict.** This is an uninstantiated analogy, not a route or a new no-go theorem. The paper's positive classification remains a possible tool only after an actual arithmetic graph with the required dependence is supplied. The existing `CoherenceEnds`/SEC interface must also be passed in a novelty audit.

## H. An infinite forward-shift law from integer translation

**Corpus stimulus.** `ArithmeticLDifferenceHolder.lean` rules out every nonzero finite homogeneous linear shift equation over rational functions for a finite-abscissa Dirichlet series with infinite support. The actual zeta specialization was checked in `/tmp/hgt-iae-shift-frontier.lean`: exit 0; standard foundation axioms only. This checks an existing compiled result, not a new theorem or a fresh build of that source.

**Trial mechanism.** Replace finite shift closure by simultaneous infinite integer-translation and exponent-shift summation. With `(s)_k` the rising factorial, the trial law is

    sum_(k>=1) (s)_k/k! * (zeta(s+k)-1) = 1,    Re(s)>0.

**Analytic screening derivation.** Expand the individual positive-base translation:

    (n-1)^(-s)-n^(-s)
      = sum_(k>=1) (s)_k/k! * n^(-s-k),          n>=2.

The required double series is absolutely convergent. Write `sigma=Re(s)>0` and choose an integer `M>=max(1,abs(s))`. The coefficient modulus is at most `binomial(M+k-1,k)`, a polynomial-growth sequence in `k`. Also

    sum_(n>=2) n^(-sigma-k)
      <= 2^(-(k-1)) * sum_(n>=2) n^(-sigma-1).

The rightmost series converges and the remaining polynomial times geometric series converges. Thus the two summation orders agree. Summing over `n` telescopes to `1-N^(-s)`, whose limit is `1`. Every zeta value in the shift sum lies in absolute convergence. No zero equation enters this argument. This is a paper derivation of a classical identity, not a newly kernel-checked result.

**Exact priority check.** [DLMF 25.8.2](https://dlmf.nist.gov/25.8.E2), attributed there to Landau, states

    sum_(j>=0) Gamma(u+j)/(j+1)! * (zeta(u+j)-1) = Gamma(u-1).

Substitute `u=s+1`, put `k=j+1`, and divide by `Gamma(s)`. For `Re(s)>0` this is exactly the trial law above.

**Failure and positive survivor.** The two infinite processes meet throughout this half-plane; at a zeta zero their common value is still the nonzero endpoint contribution `1`. The exact surviving affine law is classical. No new mathematical theorem or Lean formalization is claimed, and the identity is not promoted as a new route component merely because this exact formula was not found in the corpus search.

**Whole-route verdict.** Reject the proposed meeting-failure interpretation and the novelty claim. Absence of a finite shift recurrence does not make an arbitrary infinite shift law a new zero mechanism. Reciprocal division by zeta would insert the zero obstruction afterward rather than derive it from this law. No new proof route has passed the primary-conjecture gate.

## I. Euclidean blowup geometry and the coprime-pair source

**External stimulus.** Popescu-Pampu, [The Euclidean algorithm, lotuses and singularities](https://arxiv.org/html/2606.05211v1), dated 26 May 2026, connects subtraction on positive coprime integer pairs with successive blowups of binomial curves. Proposition 3.1 and Definitions 4.1–4.2 were inspected. Its universal lotus assembles lattice-basis triangles; each positive rational direction determines a finite subcomplex. This supplies actual arithmetic geometry, but no parameter-dependent zeta-zero correspondence.

**Trial and discriminating test.** Compare infinite lattice assembly by primitive direction with assembly by common gcd scale. Before constructing a new geometric wrapper, retain the complete two-variable arithmetic weight and identify its value. The corpus already defines this exact source:

    V(s,t) = sum_(a,b>=1, gcd(a,b)=1) a^(-s) b^(-t).
    V(s,t) * zeta(s+t) = zeta(s) * zeta(t),  Re(s)>1, Re(t)>1.

`XiCTaylorThetaTailPrimitiveRayArithmeticPartition.lean` gives the actual direction/scale equivalence. `VisibleCoprimeMellinSymbol.lean` proves summability, the product identity and the quotient identity, retaining every scale. Thus these summation processes meet in their proved convergence domain. The optimized full-source scratch of the latter module passes Lean with standard foundation axioms only; the identities are existing mathematics, not new results of this trial.

For a nontrivial zeta zero `rho`, the quotient's numerator vanishes at `(rho, conjugate(rho))`. If `1/2<Re(rho)<1`, its denominator is nonzero because `Re(rho+conjugate(rho))>1`. This conditional algebraic observation supplies no contradiction to a hypothetical off-line zero and asserts no existence of one. It also does not identify the continued quotient with the literal coprime sum outside the proved convergence domain. At the pole hyperplane, continuation needs the regular reciprocal used by the existing zero-jet source; Lean's totalized division is not a replacement for that analytic argument.

**Priority and positive survivor.** The current frontier's reference ledger explicitly lists “Visible-coprime orientation”: its mixed zero jet is already a side-of-line receiver, and finite multiplicity-truncated enlargement retains only its top corner. Exact primitive-ray disintegration and the absolutely convergent zeta quotient are the retained positive content, already formalized. No additional no-go theorem is claimed here. Changing the drawing to a lotus does not change the arithmetic identities or supply the missing source-derived location law.

**Whole-route verdict.** Reject this trial as a new route. This is not a claim against every construction retaining ordered Euclidean quotients: no zero correspondence for such a different construction has been supplied. The right problem remains an independently defined arithmetic law that yields location, beyond scalar zero detection and beyond this existing coprime candidate.

**Other paper screens.** The June/August [matroid cobordism paper](https://arxiv.org/abs/2606.12645) supplies ring presentations, not a zeta source. The May [dynamical cobordism paper](https://arxiv.org/abs/2605.06793) proposes a physical conjecture; it cannot provide an unconditional proof premise. Only their abstracts were inspected. Neither was promoted to a mathematical ingredient.

## J. Retain the ordered Euclidean branches

**Source-grounded trial.** Trial I discarded branch labels when it summed the coprime family. Test whether retaining the two Euclidean cones produces a new compatibility law or a convergence failure particular to zeros. Deep searches for `continued fraction arithmetic boundary` and `ordered double zeta triangle boundary` included candidate lemmas, source arguments and method suggestions. The useful finite-triangle partition is already in `HTGeometry.WeylDifferencing`; continued-fraction definitions and unrelated contour receivers do not provide a zeta correspondence. Generated descriptions claiming that all partial numerators equal to one proves continuity, or that a prime-tail approximation uses continued fractions, were rejected after checking the actual source objects.

**Exact paper test, including the finite root.** Work first with `Re(s)>1`, `Re(t)>1`, where the relevant families are absolutely summable. Define

    U(s,t) = sum_(a,b>=1, gcd(a,b)=1) a^(-s) (a+b)^(-t),
    H(s,t) = sum_(n>=1) n^(-s) * sum_(1<=m<=n) m^(-t).

The only coprime pair on the diagonal is `(1,1)`. On the cone `a<b`, the inverse Euclidean operation `(a,b) -> (a,b-a)` is a bijection onto positive coprime pairs; the other cone gives the swapped operation. Thus

    V(s,t) = 1 + U(s,t) + U(t,s).

Every pair `1<=m<n` has a unique gcd scale and a coprime pair `(m/d,(n-m)/d)`. Absolute regrouping therefore gives

    zeta(s+t) * U(s,t) = H(t,s) - zeta(s+t).

Substitution into the existing product formula for `V` yields exactly

    H(s,t) + H(t,s) = zeta(s)*zeta(t) + zeta(s+t).

**Priority and failure.** This is classical Euler-sum reciprocity, [DLMF 25.16.12](https://dlmf.nist.gov/25.16.E12), with `H` defined in [25.16.11](https://dlmf.nist.gov/25.16.E11). The safe domain used above is absolute convergence in both variables. No branch-continuation regularity theorem at hypothetical zeros was proved here. In particular, a zero of a continued total does not force both branches to be zero; the finite root cannot be dropped. This calculation is a paper screening of a classical law, not a newly formalized Euclidean theorem or a novel mechanism.

**Sharp positive boundary.** The complete family satisfies

    Summable(visibleCoprimeMellinTerm s t) <-> Re(s)>1 and Re(t)>1.

For necessity, restrict a summable complex family to the injective prime subfamilies `(p,1)` and `(1,p)`. Their norms are `|p^(-s)|` and `|p^(-t)|`. The existing exact prime-power absolute-abscissa theorem forces the two strict inequalities. The existing coprime-pair summability theorem proves the converse. This paper proof has no zeta-zero or RH premise.

The exact iff is now closed in `VisibleCoprimeMellinSummability.lean` as `RHTower.summable_visibleCoprimeMellinTerm_iff`. Full scratch check and axiom audit passed; the only axioms reported are `propext`, `Classical.choice`, `Quot.sound`. Targeted final leaf build passed, and the new leaf is imported by the umbrella. No heartbeat override or numerical computation was used. This is a new formal source-domain classification in this task, not a claim of new research mathematics.

**External transfer tests.** Broad June–August 2026 substitution searches supplied two specific tests:

- Zeng, Zeng, Xue and He, [Gromov hyperbolicity of substitution graphs](https://arxiv.org/html/2608.22836v1), August 24. Definition 1 and Theorem 2 with its proof were inspected. The criterion uses zero path-counting matrices for sufficiently long shortest horizontal paths. A nonzero count witnesses a lifted path. A complex weighted sum can vanish by cancellation while paths still exist, so substituting such a sum for the count invalidates that implication. No arithmetic graph with the required zero correspondence was constructed. The positive graph criterion belongs to the paper; it was not formalized here.
- Vereshchagin, [Matching Rules for Substitution and Hierarchical Tilings for any Substitution with Finite Local Complexity](https://arxiv.org/html/2606.25005v1), June 23. Definitions, Theorem 1 (side-to-side supertiles) and Theorem 2 (finite local complexity) were inspected. They provide sofic descriptions of substitution and hierarchical tiling families, retaining infinite composition histories. They specify no arithmetic tiling, complex parameter, or zeta-zero incidence. Generic representation of an infinite hierarchy does not fill that missing map.

**Whole-route verdict and scope.** Retire this raw-summability trial: its exact failure set contains the entire critical strip, so it cannot distinguish critical-line zeros. Preserve the sharp iff theorem above. The Euclidean two-cone identity itself is classical. This verdict does not rule out every ordered or renormalized construction, but none has supplied the missing arithmetic zero-location law or passed the new-route gate. The next useful problem is that law, not further vocabulary for this partition.

## K. Fold the infinite arithmetic operation graph

**Discriminating question.** Can a genuine obstruction to folding infinite operations provide information lost by the scalar coprime sum? The trial must first define the arithmetic graph and satisfy the proposed geometric theorem's hypotheses. It must then identify a zeta-zero condition independently of the critical line. Four whole-corpus deep searches inspected candidates, source arguments and available generated method/premise proposals; none supplied that missing implication.

**External stimulus and failed direct transfer.** Silberberg, [Folding of cluster algebras and quantum toroidal algebras](https://arxiv.org/html/2601.02221v1), January 5, 2026. Definitions 4.1–4.9, the relevant orbit-mutation argument, and Theorem 5.4 were inspected. Strong global folding requires a locally finite quiver and a free permutation action preserving arrow counts, together with restrictions on orbit loops and oriented two-paths. The theorem characterizes the periodic infinite-line case by the orientation of the finite cycle.

Test the literal arithmetic graph on positive integers with edges `n -> p*n` for every prime `p`, together with successor edges. At `n=1`, distinct primes give infinitely many distinct outgoing neighbours, contradicting local finiteness. Multiplication by `p>1` is not a permutation of positive integers because `1` has no preimage. It also sends a successor edge to a path of length `p`, not a successor edge. Passing to positive rationals repairs invertibility of multiplication but leaves infinite prime degree and the successor-edge problem. Thus the paper's theorem does not apply to this proposed graph. This is an input-hypothesis failure, not an impossibility theorem for every arithmetic quiver or a zeta-zero correspondence.

**Pivot to actual subdivision; exact paper test.** Retain that path rather than falsely treating dilation as a graph automorphism. For a sequence `F`, let

    dF(n) = F(n+1)-F(n),
    B_q(u)(n) = sum_(0<=a<q) u(q*n+a).

Finite telescoping gives

    B_q(dF)(n) = F(q*(n+1))-F(q*n).

If `F` is completely multiplicative, this is `F(q)*dF(n)`. The identity holds for every such `F`; it contains no zero equation. The corpus already formalizes this exact carrier in `CCMFirstClockBlockSubdivisionTransfer.lean`, including its physical logarithmic clock and finite von Mangoldt source coordinate. CANNOT-291 already rejects its bare subdivision identity as a square-root cancellation producer. This is therefore an existing construction, and preserving its arithmetic endpoints does not produce a new route.

**Second pivot: common ranges instead of scalar averages.** The same source already proves the strongest ordinary range statement. If `V_q(v)(k)=v(floor(k/q))`, then for positive `m,n`, `range(V_m) intersect range(V_n)=range(V_lcm(m,n))`; the intersection over every `q>=2` consists exactly of constant sequences. In the finite meet, an adjacent change is permitted only at a multiple of both block lengths. In the infinite meet, choose a block length larger than the adjacent index to forbid that change. These source-range facts are independent of the complex parameter and of zeros. They retain an exact classification, not a location law. No newly named completion or rigidity argument is proposed for RH.

**Geometric construction is not arithmetic identification.** A September 2 [review by Rippon](https://arxiv.org/html/2609.02806v1) led to Bishop's original [Models for the Eremenko-Lyubich class](https://www.math.stonybrook.edu/~bishop/papers/EL-models.pdf), manuscript dated May 2014, published in 2015. The original model definition and Theorem 1.1 were read. The theorem realizes suitable infinite tracts by an entire function after a quasiconformal change of coordinates; it does not identify that function with zeta or Xi, or identify the coordinate change with the identity. The proposed transfer would still need an arithmetic model and an exact source-identification theorem. No such model was constructed. The review is a recent discovery lead, not a new 2026 theorem or an RH ingredient.

**Method-search audit.** A generated proposal said local noncommutativity is equivalent to a nonsplit Brauer class. The retrieved theorem gives only the direction from nonsplitness. `ABHN/HasseAlgebraCommutativity.lean` explicitly distinguishes splitness from commutativity: matrix algebras are split and need not commute. Its actual positive statements are that field extension preserves and reflects commutativity, and a commutative central simple algebra is its scalar field. The generated converse was rejected; no defect in the Lean theorem is alleged, and no arithmetic zero-incidence theorem follows from it.

**Lean and whole-route verdict.** `lake env lean /tmp/hgt-iae-folding-audit.lean` exited 0. Six existing declaration signatures were checked; the telescoping law, both range classifications and scalar-extension commutativity equivalence reported only `propext`, `Classical.choice`, `Quot.sound`. This audits existing compiled declarations, not newly proved mathematics or a fresh source build. Both inspected source files are unchanged. All retained positive classifications already exist, so no duplicate module was written. Reject these transfers at the route-admission gate. They establish neither a new arithmetic zero correspondence nor zero confinement. The infinite-quiver problem is not repaired by ignoring its incidence hypotheses, and the exact subdivision repair is already in the frontier.

## L. Extend evaluation through the full formal coefficient algebra

**Source-grounded trial.** The retrieved `ArithmeticFunction.zetaUnit` and `dirichletInverse` suggest a literal conflict between infinite formal inversion and analytic evaluation. Test the conjecture that failure to extend evaluation to the full coefficient algebra could identify the relevant zero parameters. This is a proposed full-domain mechanism, not a claim that ordinary convergent Dirichlet evaluation is defective.

**Exact obstruction and strongest positive classification.** Let `A=ArithmeticFunction complex`, with Dirichlet convolution as multiplication and unit `delta_1`. Mathlib proves `f` is a unit in `A` iff `f(1)` is a nonzero complex number. For any complex algebra homomorphism `h:A -> complex` and `f in A`, suppose `h(f)!=f(1)`. Then

    g = f - h(f)*delta_1

has nonzero coefficient `g(1)=f(1)-h(f)`, so `g` is a unit. But `h(g)=h(f)-h(f)=0`, contradicting preservation of units. Hence

    h(f)=f(1), for every complex algebra homomorphism h and every f.

Evaluation at coefficient `1` itself preserves addition, convolution, the unit and complex scalars. Therefore this is the exact classification of all such maps, including discontinuous ones, not merely a negative existence statement. No zero equation, real-part bound, summability assumption or topological premise enters.

**Why the trial fails.** A finite atom `delta_n`, `n>1`, has coefficient at `1` equal to zero, while its ordinary Dirichlet value `n^(-s)` is nonzero for every complex `s`. Thus ordinary Dirichlet evaluation cannot extend as a complex algebra homomorphism to the full formal coefficient algebra at any parameter. Equivalently, the formal unit `delta_1-n^s*delta_n` already has zero Dirichlet value. The failure is universal, not peculiar to zeros of zeta. This finite-atom explanation is a paper consequence of the complete classification; no separate analytic continuation theorem is claimed.

The exact positive classification is newly formalized in `ArithmeticFunctionScalarEvaluation.lean`: `arithmeticFunctionAugmentation`, `arithmeticFunctionAlgHom_apply`, and `arithmeticFunctionAlgHom_eq_augmentation` in namespace `RHTower`. Full scratch check passed, both theorem axiom lists contain only `propext`, `Classical.choice`, `Quot.sound`, and the targeted final leaf build passed. The new leaf is wired into `RHTower.lean`. The argument is an elementary consequence of the existing unit criterion; no claim of new research mathematics or a new RH route is made.

**Novelty and scope audit.** Three deep corpus searches included candidate lemmas, source arguments and available method suggestions. The decisive ingredient is Mathlib's `ArithmeticFunction.isUnit_iff_isUnit_apply_one`; exhaustive project-source search found no prior use of that lemma, and no matching scalar-evaluation classification was located. These searches do not establish global mathematical novelty. Full formal compositional inversion of the alternating arithmetic series is separately covered by F20j; it is a different operation and was not used here. Ramanujan retrieval recovered existing finite arithmetic source identities, including the two-level Möbius conservation already recorded at F659, not a new evaluation-extension law.

**Recent-paper screens.** Lim, [The combinatorics of sector renormalization](https://arxiv.org/html/2607.11408v1), July 13, 2026: the definitions and Theorems A–B encode irrational-rotation dynamics and their compactification with infinite return times. Theorem B identifies the minimal compactification retaining either the segment embedding or the full cyclic-order record. No map from the arithmetic coefficient algebra or a zeta-zero correspondence was provided by this trial. Natarajan et al., [Topology of Multi-species Localization](https://arxiv.org/html/2603.03237v1), March 3, 2026: Section 1.3 defines gluing from disjoint copies of colour-subset filtrations to the full filtration and studies the induced kernel, image and cokernel. No arithmetic coloured source or source-to-zero identification was constructed here. Neither paper's topology overrides the algebraic obstruction above, and neither is promoted as an RH ingredient.

**Whole-route consequence.** Retire the proposed full-domain extension selector. Its exact surviving map is augmentation, and its failure set cannot distinguish a zero from a nonzero. A possible future analytic construction needs a specified proper coefficient domain and a proof of its source admission; merely changing the topology of the unchanged full algebra cannot create the required scalar evaluations. This leaves conditional convergence, proper subalgebras and other algebraic structures open; it establishes no zero-location law. The route-independent constraint is recorded in universal STATUS.

## M. Delayed merging of finite arithmetic records

**Trial and source.** Instead of the full formal algebra in L, use finite arithmetic coefficient families. At logarithmic cutoff `t>=0`, retain coefficients supported on positive integers `n<=exp(t)`; increasing `t` embeds the same family by extension by zero. Convolution takes cutoffs `t,u` into cutoff `t+u`. Test whether a mismatch between two operations on these records can disappear at a later cutoff, using the merging-distance construction in Olave and Munch, [Bounding the interleaving distance on concrete categories using a loss function](https://arxiv.org/html/2601.09034v1). The arXiv version header is January 13, 2026; the displayed manuscript date is August 11, 2026. Definition 3.1, Theorem 3.4 and its proof, and Definitions 3.8–3.10 were inspected. Merging distance is the infimum of forward shifts making two images equal; a fixed assignment's loss measures discrepancies in its naturality and round-trip diagrams.

**Proof/fail.** Every transition in the proposed arithmetic filtration is injective: equality of the extended coefficient families implies equality at every original index. Consequently the set of merging times is all nonnegative shifts when the records agree, and empty otherwise. The exact merging-distance classification is therefore `0` for equal records and `infinity` for unequal records. The same distinction holds for the paper's loss of a fixed assignment: zero precisely when all its diagrams already commute, infinity if any diagram has unequal outputs. This is an inference from the inspected definitions for this injective filtration. It is not a classification of the interleaving distance between arbitrary pairs of filtrations, which allows different assignments and shifts.

**Pivot to the infinite algebraic colimit; positive invariant.** Taking every cutoff does not erase a fixed discrepancy. In a directed colimit, equality of representatives means equality at a common later stage. The transition's injectivity then reflects that equality back to the original stage. Thus every original coefficient record is faithfully retained in the colimit. The exact general statement already exists as Mathlib's `DirectLimit.mk_injective` and the project's `HTGeometry.directLimit_of_injective`; both source proofs were read. `DirectLimit.exists_eq_mk₂` also supplies the common-stage representation. This is the retained positive invariant, not newly claimed mathematics. An analytic completion or a quotient by convergent scalar sums is a different construction and is outside this argument.

**Novelty and audit.** Three deep whole-corpus queries inspected candidate lemmas, source arguments and generated method proposals. Pointwise logarithmic weighting versus convolution already has its exact derivation law in `DirichletLogDerivation.lean`; depth-two chronological comparison is already constrained by F692 and CANNOT-317. Generic associativity does not itself supply an arithmetic interchange law. The other April interleaving paper, [A distance between maps via interleavings of relative Sullivan algebras](https://arxiv.org/html/2604.06800v1), was screened through its introduction: it requires actual maps and their persistence CDGA models. No such arithmetic map was constructed, and its stronger invariant is not promoted as an ingredient.

`lake env lean /tmp/hgt-iae-merging-audit.lean` exited 0: five existing signatures checked, four axiom lists restricted to standard foundation axioms. This audits compiled direct-limit and injective-consumer results; the real-indexed arithmetic filtration and the paper's numerical-valued distance were not separately formalized. No duplicate module, final build or umbrella change was needed. The source-level argument and its exact general positive invariant are distinguished from a new arithmetic theorem.

**Whole-route consequence.** Reject delayed merging through coefficient-preserving cutoff inclusions as the proposed mechanism. Neither adding all cutoffs nor renaming their fixed mismatch as persistence creates a zero correspondence. A different completion must define the map that changes equality and prove its arithmetic meaning. That missing map, together with zero confinement, remains the hard obstacle. This trial supplies no new route-independent RH constraint beyond the existing distinction between exact retention and completion, so universal STATUS is unchanged.

## N. Finite-prime tail quotient and the topology of a divisor readout

**Trial.** Identify prime-phase records differing at finitely many primes. Unlike M's injective cutoff maps, this quotient changes equality. Test whether its topology could supply a new meeting-failure mechanism for an arithmetic zero detector. Three whole-corpus deep searches and direct source inspection found the complete proposed mechanism already present.

**Arithmetic positive statement, already formal.** For `p>1`, unit-modulus phases `u,v`, and `Re(s)>0`,

    (1-u*p^(-s))/(1-v*p^(-s))

is a nonzero holomorphic function of `s`; the same holds for every finite product of these ratios. Indeed, `|p^(-s)|=exp(-Re(s)*log(p))<1`, so both local factors are nonzero. Thus multiplication by this finite correction preserves the zeros and poles, including their orders, of a meromorphic source wherever that continuation is supplied. `FiniteGaugeTailCharge.lean` already proves the finite correction holomorphic and nonzero. `HelsonEulerModification.lean` separately constructs the full-plane meromorphic finite modifications of the actual zeta function. Its unrestricted complex phase statement alone does not give divisor preservation: unit modulus is essential for the stated positive-half-plane protection.

**Topological conjecture and failure.** Could a nonconstant separated divisor readout descend continuously to this quotient from the product topology on phases? No. Every finite-coordinate cylinder contains a representative of every finite-modification class: copy the prescribed finitely many coordinates into any representative. Consequently every class is dense, and the quotient topology has only the empty and whole sets as opens. Any continuous readout into a `T0` space is constant. More sharply, for a `T1` target, continuity at even one record forces an invariant readout to be constant everywhere. These are existing exact theorems in `FiniteGaugeTailCharge.lean` and `TailQuotientSeparationLaw.lean`, not newly proved facts. This argument does not assert that every prime phase has a meromorphic continuation or a globally defined divisor readout.

**Novelty audit and a rejected extra identification.** `EulerGaugeSingularIncidenceLaw.lean` already applies the same obstruction to the stronger exponent-zero Euler gauges; `ExponentZeroIsodivisorialContinuation.lean` preserves every local signed divisor order under those admitted gauge changes. A new tail-space name would therefore duplicate existing work. The project's Boolean projective quotient additionally identifies global complement. That relation classifies its specified palette fields; it was not used as an unproved identification of Euler divisors. The generic finite-modification theorem suffices for the present test without that extra quotient.

**Recent-paper transfer test.** Elsayed, [Levine Equivalence in Aura Topological Spaces: Reachability, Alexandrov Structure, and Quotient Frames](https://arxiv.org/html/2608.18269v1), August 18, 2026: Definitions 2.2–2.3 and Theorem 3.1 with proof were inspected. Its scope at each point must be open in the input topology; forward reachability determines an Alexandrov topology. Choosing the finite-modification class as the scope fails that hypothesis in the phase product: each such class has empty interior. For Boolean phases, any cylinder admits an infinite overwrite outside its finite prescribed coordinates, producing a point outside the chosen tail class. Declaring classes open changes the topology; it does not repair admission in the original product. The retained positive description is explicit: product-open sets saturated under finite changes are only empty and whole. This is the same quotient classification above, not a new arithmetic law.

Other broad corona, phantom, telescope and asymptotic-cone searches produced no admitted arithmetic transfer. The June coarse-median paper was inspected at its definitions, without constructing an arithmetic metric or applying its theorem. No theorem from these screens is an ingredient of this route.

**Lean audit and whole-route consequence.** `lake env lean /tmp/hgt-iae-tail-topology-audit.lean` exited 0 without warnings: six existing signatures and five axiom lists checked, only `propext`, `Classical.choice`, `Quot.sound` reported. This is an audit of compiled statements, not a new source build or a formalization of the external paper. Both retained positive results already exist; no duplicate module or umbrella edit was made. Reject this candidate at the novelty gate. Generic tail quotients and their discontinuous readouts do not select the critical line. The next useful problem is a new relation satisfied by the actual arithmetic continuation; neither density nor the word 'nonlocal' provides it. Universal STATUS records the precise coefficientwise-topology limitation, with its full-product and continuation scope explicit.

## O. Recover through the full multiplicative-cutoff boundary

**Actual problem.** The corpus now proves that the raw truncated Möbius head cannot recover the literal finite zeta continuation at a nontrivial zero: their product tends to zero. Test whether deriving the required counterterm from the exact finite convolution supplies a new recovery mechanism. This attacks the specified boundary directly; it does not assume a Möbius cancellation estimate or insert reciprocal zeta.

**Exact paper identity.** Put

    D_N(f,s) = sum_(1<=n<=N) f(n)*n^(-s),
    O_N(f,g;s) = sum_(1<=d,m<=N; N<d*m) f(d)*g(m)*(d*m)^(-s).

For all complex `s` and all natural `N`, rectangle partition and Dirichlet convolution give

    D_N(f,s)*D_N(g,s) = D_N(f*g,s)+O_N(f,g;s).

The inner overflow row is exactly `Icc(1,N) \ Icc(1,floor(N/d))`; no factor pair is discarded. The underlying unweighted theorem holds over every semiring. Weight transport uses the existing `LSeries.term_convolution`, and the hyperbola regrouping is the existing `RHTower.sum_Icc_mul_apply`. With Möbius and constant-one arithmetic coefficients, `mu*1=delta_1`, so

    M_N(s)*Z_N(s) = 1+O_N(mu,1;s)                  (N>=1).

The Lean theorem retains the empty-cutoff endpoint as well: the unit term is `if 1<=N then 1 else 0`. This is a full finite source identity, not an estimate or an infinite rearrangement.

**Conjecture/fail: does the boundary correction select zeros?** Let `F_N` be the literal continued finite head from `ArithmeticFiniteSourceContour.lean`, and retain its entire correction `P_N=Z_N-F_N`. The identity becomes

    M_N*F_N = 1 + O_N(mu,1;s) - M_N*P_N.

Subtracting the complete right-hand defect makes the scalar expression equal to one for every parameter. It therefore does not distinguish a zero from a nonzero and does not construct a new factor reciprocal to `F_N`. A multiplicative recovery would additionally require an admitted factorization of the counterterm through `F_N`, with control at its zeros. Dividing by `F_N` without that audit reintroduces the same reciprocal problem.

At every nontrivial zeta zero, the existing raw-head theorem gives `M_N*F_N -> 0`. Hence the retained boundary `O_N-M_N*P_N -> -1`. This last limit is a paper consequence of the exact identity and the existing `FiniteMobiusRecoveryGluingNoGo.lean` source theorem; no separate new Lean declaration for that rewritten limit is claimed. In particular, the complete boundary does not disappear at such a zero. Nothing in this argument singles out its real part.

**Positive survivor and novelty.** The complete rectangle/hyperbola decomposition, its exact support, and its Möbius specialization are now closed in `FiniteDirichletConvolutionOverflow.lean`. This is new formalization in this task, not new research mathematics. Three deep corpus searches inspected candidates, source arguments and method proposals; direct source inspection located the exact generic hyperbola theorem. No prior project declaration with the new boundary definitions or theorem names was found. This check does not prove global mathematical novelty. The finite decomposition is classical and is not promoted as a new RH route.

**Recent-paper test.** Kordalis and Trevezas, [Discrete time-multidimensional renewal theory and applications](https://arxiv.org/html/2606.31455v1), June 30, 2026: Section 2.1.2 Lemma 2.1 and Section 2.1.3 Theorem 2.1 with proofs were read. Their convolution inverse exists when the constant coefficient is nonzero; each coefficient of the inverse uses only finitely many convolution powers. This is coefficientwise formal inversion. It supplies no exchange with analytic evaluation at a zero and no bound for the signed Möbius boundary. The paper's probabilistic limit theorems and numerical schemes were not used. The corresponding full formal arithmetic-unit obstruction is already recorded in attack L.

**Verification and whole-route consequence.** The final scratch check exited 0 without warnings; the weighted identity, Möbius identity and support theorem report only `propext`, `Classical.choice`, `Quot.sound`. The targeted final build compiled only the new leaf, and the umbrella imports it once. No heartbeat override or numerical experiment. Reject the proposed additive-counterterm selector, retaining the full exact source boundary as the positive result. The hard obstacle is a new arithmetic factorization or cancellation law for that complete boundary, not its definition or deletion. RH and the route-admission gates remain open.

## P. Three-product coherence and geometric gluing

**Trial.** Could the full scalar overflow in O support an independent obstruction when three arithmetic products are composed? Write `E(f)=D_N(f,s)` and `B(f,g)=O_N(f,g;s)`, with convolution denoted by `*`. The previously proved identity is `E(f)E(g)=E(f*g)+B(f,g)`. Retain every term when comparing the two parenthesizations.

**Proof/fail and exact survivor.** Expanding `(E(f)E(g))E(h)=E(f)(E(g)E(h))` using that identity gives the same `E(f*g*h)` on both sides. Cancelling that common term proves

    B(f*g,h) + B(f,g) E(h) = B(f,g*h) + E(f) B(g,h).

This holds for every natural cutoff and every complex parameter, for arbitrary complex arithmetic coefficient families. Thus this complete three-product comparison is identically zero; it cannot select a zeta zero or a real part. It is an associativity identity, not by itself a Hochschild cohomology construction: multiplication by `E(f)` has not been shown to give a module action of the convolution algebra. In particular, that action would itself require the multiplicativity whose defect is being studied.

The strongest retained two-input symmetry is also exact:

    B(f,g)=B(g,f).

Proof: write both boundaries as `E(f)E(g)-E(f*g)` and use commutativity of complex multiplication and convolution. The Lean proof instead cancels the common term, avoiding subtraction expansion. The new declarations `finiteDirichletOverflow_assoc` and `finiteDirichletOverflow_comm` are in the existing `FiniteDirichletConvolutionOverflow.lean` leaf. They are elementary consequences of the complete boundary law, not new RH mathematics.

**Pivot: can the same scalar boundary be an intersection operation?** A direct identification with a scalar-valued skew operation would force it to vanish: symmetry and skew symmetry give `2B(f,g)=0` over the complex numbers. This is a paper consequence, not a claim that all nonscalar geometric lifts are impossible. A lift retaining paths and their endpoints would be additional data, with a new arithmetic admission obligation. Merely assigning a gluing name to the scalar boundary supplies none.

**Recent source test.** Ashton and Rivera, [Splitting the Goldman–Turaev Lie bialgebra along a simple separating curve](https://arxiv.org/html/2607.11370v1): arXiv header July 13, displayed manuscript August 24, 2026. The introduction, boundary-path definitions, Theorem 4.1's surjectivity argument and Theorem 4.2's stated kernel relations were inspected. Their reconstruction retains cyclic words of paths alternating between the two surface pieces, with endpoint data and intersection operations. This trial has no arithmetic surface, corresponding paths, or map preserving those operations. Its scalar boundary identity cannot establish those missing inputs. No theorem from the paper is applied to zeta.

Bais and Kjuchukova, [Cobordism groups of dihedral branched covers](https://arxiv.org/html/2608.07788v1), August 7, 2026: introduction and Definitions 2.1–2.3, Remark 2.4 inspected. Their invariant retains a specified dihedral monodromy; the covering map alone can lose it. This is a warning about the data needed by that particular construction, not an arithmetic invariant supplied by the paper. No arithmetic branched cover or monodromy was constructed here. Other broad excision, sewing, compactification and homotopy screens yielded no admitted transfer; excluded geometric rigidity and positivity methods were not used.

**Novelty, verification and whole-route decision.** Three deep searches returned partial retrieval; candidate statements, source arguments, method suggestions and unfinished stages are retained in search evidence. The generated pinching proposal uses excluded positivity and was discarded. Exact source-name searches found no prior declarations for the two new identities; this does not establish mathematical novelty. Existing universal constraints CANNOT-316, MUST-220 and F693 already exclude nearby generic associator proposals. The present multiplicative boundary identity makes the specific current candidate's failure explicit.

Scratch `lake env lean /tmp/hgt-iae-overflow-coherence.lean` exited 0; both axiom lists contain only `propext`, `Classical.choice`, `Quot.sound`. The theorem bodies in the source match scratch exactly. Final targeted build passed, compiling only the existing leaf (6.2s); no full build, new umbrella import, heartbeat override or numerical experiment. Retire this scalar three-product selector, retaining the two exact source identities. The whole-route problem remains an independently defined arithmetic incompatibility with a proved zero correspondence; no such construction or confinement theorem is established here.

## Q. Persistent prime-product topology and the prime-two contraction

**Admission and trial.** Direct inspection of `MobiusBoundaryOppositeSignTransport.lean` found that its one-to-two and one-to-four prime replacements are explicitly the existing Route E graph. They cannot be relabelled as a new route. Instead test a retained geometric object: at cutoff `N`, take finite prime subsets whose product is at most `N`. This is downward closed. Could reduced cycles persisting to infinity encode the requested incompatibility? The cone test must precede any claimed connection to zeros.

**Paper proof and strongest survivor.** Work over any commutative ring `R`. The degree-`k` module is the exterior power of the free `R`-module on primes. Let `C_k(N)` be the span of ordered prime atoms with product at most `N`; repeated vertices vanish. The augmented boundary contracts by the functional taking each prime to `1`. Every removed vertex is a prime at least two, so deleting it cannot increase the product. Thus the boundary preserves `C_k(N)`.

Adjoining a prime `p` on the left sends `C_k(N)` into `C_(k+1)(pN)`. The already proved Cartan identity gives `d h_p+h_p d=id`, since the functional takes `p` to `1`. Consequently every reduced cycle in `C_(k+1)(N)` is the boundary of the explicit chain `h_2(x)` in `C_(k+2)(2N)`. The degree-zero augmented chain also bounds by cutoff `2N`, using the separate bottom-degree identity. This is a uniform support statement in every degree, over every commutative coefficient ring, not merely a dimension count or a claim that the direct limit happens to be acyclic.

**Fail and weighted pivot.** The unweighted persistence proposal fails: doubling the cutoff kills every class. Test the actual Dirichlet weights rather than adding arbitrary parameter labels. Define the boundary functional on the prime basis by `phi_s(p)=p^(-s)`. The same deletion argument preserves the product cutoff for every complex `s`. Since `2^s 2^(-s)=1`, the explicit homotopy is now

    h_s(x) = 2^s (e_2 wedge x),
    d_s h_s + h_s d_s = id.

Scalar multiplication changes no support, so this homotopy again maps cutoff `N` to `2N`. Every weighted reduced cycle, including the bottom augmented degree, therefore bounds by twice its cutoff at every complex parameter. No real-part, zero-location, summability or RH assumption enters. The weighted pivot fails as a selector as well.

**Precise limits.** In logarithmic cutoff, no class in this chain model survives a shift of `log 2`. This does not bound the number or size of classes born as the cutoff grows. It does not prove continuity or boundedness of the homotopy on an independently chosen analytic completion, and it does not identify any zeta zero with a class. The geometric face inclusion is coned by adjoining vertex two; its continuous-realization interpretation is a paper observation. The exact all-degree filtered chain contraction and fillings, rather than a separate topological-realization API, are what is formalized.

**Lean and novelty audit.** The existing ingredient is `HTGeometry/KoszulCartanContraction.lean`, whose complete Cartan and exactness proofs were read. New `PrimeProductCutoffContraction.lean` supplies the prime-product submodules, cutoff preservation for every contraction functional, adjoining-prime support control, unweighted fillings over arbitrary rings, and Dirichlet-weighted fillings for every complex parameter. The central declarations are `primeChainDifferential_cutoff`, `primeChainCutoff_cycle_bounds_in_double`, `primeChainCutoff_zero_bounds_in_double`, `dirichletPrimeChainCutoff_cycle_bounds_in_double`, and `dirichletPrimeChainCutoff_zero_bounds_in_double`. This is an elementary arithmetic filtration of the existing cone identity, not a novel RH theorem. Exact source-name searches found no prior declarations with these names; the partial corpus searches do not establish global novelty.

The final scratch `lake env lean /tmp/hgt-iae-prime-cutoff.lean` exited 0. All five central axiom lists contain only `propext`, `Classical.choice`, `Quot.sound`. Earlier elaboration failures concerned subtype/comap annotations, a missing membership lemma, a finite-product annotation and excessive `ext` descent; they are not proof certificates. Direct lemmas and explicit annotations resolved them without heartbeat changes. The final module's proof tokens match successful scratch modulo comments.

**External source audit.** Ahuja and Iyer, [Persistent Simple-homotopy invariants via discrete Morse theory](https://arxiv.org/html/2604.10192v1), April 11, 2026: Definition 3.1 and Theorem 3.4 with its proof were read. The claimed invariance proof omits configurations where the selected free face is matched downward while its coface is matched to a different face. For a filled triangle `abc`, the acyclic matching `(a,ab),(b,bc),(ac,abc)` has one critical vertex; the free pair `(ab,abc)` is not matched together and neither simplex is critical. The proof's cases do not cover it. This diagnoses an incomplete argument, not a counterexample to that theorem by itself. The invariance claim is not used. The paper's face and cone definitions were only a screening prompt; the actual support proof above is independent.

Pamuk and Varlı, [Component-Perfect Multidimensional Discrete Morse Functions](https://arxiv.org/html/2607.21767v1), July 23, 2026: screened definitions of multidimensional Morse data and the stated component-perfection result. These concern additional finite-CW dynamics; no such arithmetic data or zero correspondence was supplied, and no theorem is applied here. The June topological-flow paper uses a Laplacian-derived drift and was discarded. Four deep searches and one lexical search are retained with their coverage; generated transfer suggestions were not accepted as proofs.

**Whole-route decision.** Retire the proposed long-lived homology selector on this prime-product complex, retaining its complete doubled-cutoff filling law. The same failure survives literal Dirichlet weighting. Any next candidate using this carrier must supply genuinely additional arithmetic data and a proved zero correspondence; an infinite number of finite faces, or calling the weighting nonlocal, supplies neither. No qualifying new route or zero confinement is established.

## R. Infinite face rows and removal of Dirichlet weights

**Trial and exact carrier.** Q leaves analytic completion unclassified. Test all complex coefficient families on finite prime subsets, with the product topology. For a face `A`, its boundary coefficient is the sum over primes `p` outside `A` of `(-1)^(number of q in A below p) * p^(-s) * c(A union {p})`. Admit a coefficient family precisely when each such row is unconditionally summable. This specifies a domain and a boundary graph; row summability alone is not asserted to make the domain a chain complex or the boundary continuous.

**Paper proof and formalized survivor.** Let `w_s(A)=product_(p in A) p^(-s)` and `G_s(c)(A)=w_s(A)c(A)`. Every weight is nonzero, so coordinate multiplication has a continuous coordinatewise inverse on the product topology, with no bound across faces required. For `p` outside `A`, `w_s(A union {p})=p^(-s)w_s(A)`. Consequently every unweighted boundary row of `G_s(c)` is the corresponding weighted row of `c`, multiplied by the one nonzero constant `w_s(A)`. Thus row summability is equivalent in both directions, and `d_0 G_s=G_s d_s` on the admitted domain. The pair map `(G_s,G_s)` transports the entire boundary graph to the unweighted graph. Its composite with the inverse transport for `t` identifies the graphs at any two complex parameters.

**Scope and whole-route effect.** Topological invariants of this boundary graph alone cannot produce exceptional parameters. This does not identify the boundary graphs with the finite exterior-chain model, prove square-zero on the row domain, or transport an independently fixed norm, source vector, analytic continuation or extra arithmetic law. It supplies no zeta-zero correspondence. The candidate would need additional data that are not transported by this coordinate equivalence; merely naming a maximal coefficient domain a completion does not provide them.

**Stronger survivor, proved and checked.** The diagonal coordinate changes also depend continuously on `s`: each face contains only finitely many primes, and `p^(-s)` and its reciprocal are entire functions of `s`. The pair map therefore trivializes the total boundary-graph family over the whole complex plane, preserving the parameter. This is now the explicit Lean homeomorphism `primeFaceBoundaryGraphTrivialization`. Its target is the constant graph condition `PrimeFaceBoundaryGraph 0`, with a freely varying complex parameter. Joint continuity and a continuous inverse are checked; no holomorphy theorem is claimed as separately formalized.

**Corpus and external admission audit.** `ExFlag.ExactCompletionDiagram.physical_exact` in `ProvenanceContinuousCompletion.lean` preserves eventual exactness under its specified provenance topology and convergence obligations. It is not a theorem about every analytic completion. `DeningerBarContraction.lean` already supplies an explicit contraction of its completed word-height bar source. Neither identifies that source with the present coefficient domain. The five new search records inspect candidates, source arguments and generated method proposals; one is partial. The generated norm-contraction proposal assumes the norm inequality that a new source would need to prove. It is rejected as an unconditional producer.

Li and Gao, [A Low-Regularity Semigroup Sewing Lemma via Quotient Structures](https://arxiv.org/html/2606.16164v1), June 15, 2026: introduction, Definitions 6.1 and 6.3, Lemma 6.5 and Theorem 6.6 with proof inspected. Passing from quotient classes to actual representatives requires a chosen linear splitting domain. The hypotheses include bounds on the recursively generated child residuals, a strict contraction threshold, and uniform continuity of the semigroup on those residuals. The theorem supplies a continuous representative after these inputs are established; it does not construct them for prime-face coefficients or connect the regularity exponent to a zeta parameter. No arithmetic semigroup with those properties was admitted here. The heat-equation application is not used. Other broad bornology, completion and sewing searches yielded no admitted arithmetic transfer; abstract screens are not treated as proofs.


**Verification and decision.** New leaf `PrimeFaceBoundaryGauge.lean` formalizes the exact row identity, summability equivalence, graph fibre equivalences, and the stronger global trivialization. All four central scratch axiom lists contain only `propext`, `Classical.choice`, `Quot.sound`. The separate API checks are included in the successful scratch but not the source. Early failed elaborations are not certificates. In particular, the nested continuity-composition proof reached the default 200,000-heartbeat limit; explicit coordinate continuity proofs resolved it without changing any limit. Source proof tokens match the successful scratch modulo documentation. Final targeted build compiled only this leaf (3.3s), within a 2,009-job cached dependency graph; its umbrella import is appended once.

This is an elementary coordinate transport with an exact infinite-domain audit, not a novel RH theorem. The corpus contains adjacent finite diagonal and completion no-gos; the exact row-domain and joint-parameter statements were not found in the inspected hits or source-name search. That is not a global novelty certificate. Retire this graph-only selector and retain its explicit global equivalence as the positive result. Do not keep developing this carrier without independently specified arithmetic constraints that invalidate the equivalence as a comparison of the full data. No zero correspondence or confinement law has been constructed, and the original route gates remain open.

## S. Divisor classes, retained sections, and geometric realizability

**Question and trial.** Can simultaneous triviality of geometrically defined line bundles supply an arithmetic meeting failure that the coefficient-graph gauge in R cannot erase? The July double-ramification paper makes such loci concrete, but their bundles must first be constructed from the arithmetic source. Test the immediate proposed assignment: take the principal divisor of a global meromorphic source and pass to its class.

**Proof/fail.** A quotient by principal divisors sends that principal divisor to the neutral class. This operation therefore cannot distinguish whether the given function vanishes at a particular point. It is essential not to replace this assertion by “the divisor vanishes.” The generated corpus method made precisely that jump; its cited `SUnitGroup.divisorCoordinate_one` proves only that the identity element has zero divisor coordinates.

The literal arithmetic check retains the lost data. For every prime `p`, its exponent in the integer factorization of `p` is `1`, while the invertible fractional ideal of the same rational number has neutral ideal class. The existing theorem `ClassGroup.mk_eq_one_iff` classifies this: neutrality is principality, not zero valuation coordinates. Scratch checks the prime specialization using `toPrincipalIdeal`, alongside `Nat.Prime.factorization_self`. These are existing arithmetic facts, not a new RH mechanism. No identification of an algebraic ideal class group with an analytic Picard group is claimed.

**Pivot: retain the section and its inclusion.** The existing analytic-germ theorem proves that a germ is invertible exactly when its value is nonzero. Applying it to the literal entire Xi function gives, at every point `p`,

    span{germ_p(Xi)} = whole germ ring  iff  Xi(p) != 0.

This exact zero-aware criterion survives, unlike the class-only assignment. It still supplies no constraint on `Re(p)`: making every off-line germ invertible would be the unproved zero-free assertion. The scratch proof is a direct specialization of `Ideal.span_singleton_eq_top` and `isUnit_analyticGerm_iff`, with Xi analyticity discharged by `RiemannTower`. It is an audit of available local algebra, not a new route or new source construction. Keeping sections prevents information loss; it does not produce an independent arithmetic law.

A different bundle on a quotient space remains a separate possibility, but it requires an actual descent construction and its transition data. A meromorphic function upstairs is not automatically a meromorphic function downstairs. Conversely, when a global function really is supplied on the same base, passing to its principal class still erases the information above. This distinction prevents both a false general no-go for line-bundle methods and a false claim that the present assignment has constructed one.

**Actual source admission audit.** `DeningerArithmeticRealArakelovEndpoint.lean` explicitly defines the graph `d -> (d,-weight(d))` on an arbitrary finite-divisor module. Its principal-map injectivity and exactness with the degree map are checked, but the source documentation explicitly says it does not construct the principal-divisor map from arithmetic units or functions. Thus the returned exactness theorem cannot be used as the missing arithmetic realization. Likewise `ArithmeticInteractionScaleLaw.lean` already reconstructs the complete integer-scale response; a zero-associated deformation and its bounded returns are still not supplied. Neither item is promoted under a new geometric name.

**Recent-paper scope.** Amini, Chou, Herr, Holmes, Huq-Kuruvilla and Lee, [On the K-theoretic logarithmic double ramification class](https://arxiv.org/html/2607.13376v1), arXiv July 15, displayed manuscript August 24, 2026: introduction and Theorems 1.2–1.4 inspected. The product law concerns simultaneous triviality of specified tuples of line bundles; the class equality belongs to colimit log K-theory and is not asserted on the naive compactified base. No arithmetic curve, line bundles, log model or comparison with Xi is constructed by our proposed assignment. The theorem's proof was not audited and no result is applied here.

Zhu, [Which Holonomy Signatures Are Realizable? A Complete Answer for Closed Surfaces](https://arxiv.org/html/2608.01444v1), August 2, 2026: introduction and Proposition 6.7 with proof, Corollaries 6.8–6.9 inspected. The fixed-curve condition is linear equivalence of a prescribed divisor with a power of the canonical divisor. The realizability classification permits the conformal structure and marked points to vary. It therefore does not prove the condition for a fixed arithmetic source. Its boundary discussion also leaves the prescribed real-involution realization question open. No rigidity or holonomy theorem from this paper is used as an RH argument.

Barcau and Paşol, [Iterated extensions and the ramification dichotomy](https://arxiv.org/html/2606.29310v1), June 28, 2026: introduction, main theorem statement and derivative-growth lemma with proof screened. The construction requires a specified local field, integral polynomial with inseparable reduction, and one compatible inverse branch. No such data varying with a complex zero parameter, or comparison with Xi, was supplied. Its ramification and perfectoid conclusions are not transferred. Other broad holonomy, fracture, collage, factorization and ends searches yielded no admitted source law; abstract screens are not proofs.

**Positive survivor and whole-route decision.** Retain the exact distinction between divisor coordinates, divisor class, and the section's local invertibility. Its standard algebraic components are already formalized; the prime and actual-Xi specializations are scratch-checked instead of adding duplicate repository lemmas. Reject the principal-class-only selector and the unproved transfer of variable-geometry existence to a fixed arithmetic object. The complete route remains missing an independently constructed infinite arithmetic geometry and a source-derived zero-location law. This audit does not exclude other divisor-class constructions and does not admit a new RH route.

**Final audit.** `lake env lean /tmp/hgt-iae-divisor-section-audit.lean` exited 0 without warnings; six selected axiom lists contain only standard foundations. This is an audit of existing declarations and their literal specializations, not new repository formalization or a fresh build of those source modules. Four further retrieval records bring the evidence to 61 unique queries, with partial and missing coverage retained. No new module, umbrella change, full build, heartbeat increase or numerical experiment. All owned tool sessions are terminal.

## T. Exact contour periods and the retained pole

**Question.** Can an infinite contour decomposition turn a zero into the disappearance of a contour contribution, supplying the missing geometric location law? First test the exact arithmetic source. A saddle approximation or a picture of thimbles cannot replace this admission test.

**Literal source.** The corpus defines `F(s,x,w)=zeta(s+w) x^w exp(w^2)/w`. `SmoothAFEZetaResidueDecomposition.lean` splits it, away from `0` and `1-s`, into `zeta(s)/w + R(s,x)/(w-(1-s)) + H(s,x,w)`, where `H` is entire for `x>0` and `R(s,x)=x^(1-s) exp((1-s)^2)/(1-s)`. These are actual source residues; no thimble interpretation is part of that theorem.

**Conjecture/fail.** Suppose equality of the two uncorrected infinite edge periods `D(s,x)` and `M(s,x,c)` were the proposed meeting condition at a zero. The exact arbitrary-edge identity is `zeta(s)=D-M-R`, for `x>0`, `c>0`, `s!=1`, `0<Re(s)<1+c`. Every factor in `R` is nonzero on this domain. Thus at a zero, `D-M=R!=0`, contradicting the proposed equality. This is a direct source test, with the tails and shifted pole retained, not a truncation argument.

**Positive replacement and second test.** The sharp correct statement is `zeta(s)=0 iff D-M=R`. It holds at every base point in the stated domain. The corpus also proves that every admissible negative depth gives exactly the same `M` as depth one when `0<Re(s)<2`. Consequently neither the edge choice nor correction of the meeting condition supplies a new half-line restriction. Subtracting the known residue recovers an existing zero receiver. The zero-location implication is still missing, and assuming it for this receiver would not prove it.

The strongest positive survivor here is the already formalized exact two-pole decomposition and arbitrary-depth independence. Scratch checks the nonzero residue and both literal zero specializations; these are direct consequences, not duplicate new repository modules or a research novelty claim. No claim about twisted homology, vanishing cycles, or every possible contour construction follows. The proposed Hankel local-system model was not constructed and is not counted as a result.

**Recent-paper scope.** Hayashi and Ünsal, [From Self-Dual to Physical CP^(N-1)](https://arxiv.org/html/2608.30160), August 31, 2026: introduction and Appendix E through the Airy boundary-action formulas inspected. It distinguishes saddle and boundary contributions and describes a coefficient disappearing during a boundary Stokes transition. That is not a statement that the entire period vanishes. Moreover, its displayed negative-gradient flow (210) gives `d Re(S)/du=-abs(S')^2`, contrary to the following sentence's increasing-sign assertion. No theorem from this paper is transferred, and no inference about its main physical conclusions is made.

Si Li, Yong Li and Xinxing Tang, [Picard–Lefschetz theory and alien calculus: a case study](https://arxiv.org/html/2605.08867v1), May 9, 2026: basic data, the flow lemma with proof, and the Gamma model's setup and displayed change of thimble basis inspected. The framework needs an action, volume form, and admissible decay cycle. The Gamma model has infinitely many saddles and a change of basis involving an infinite triangular sum; it does not supply these data or a zero correspondence for the arithmetic source above. Its full Gamma-model proof was not audited. No result is applied. Other broad 2026 dislocation, avalanche, Stokes, WKB, resurgence and thimble hits were abstract screens only; prohibited machinery was excluded.

**Whole-route decision.** Reject the raw-edge meeting selector. Retain the corrected identity and the exact independence of depth as existing arithmetic facts. The distinguishing obstacle remains an independently derived arithmetic relation forcing the corrected zero condition onto the critical line. Repeating generic contour or quotient constructions without that relation would not move this route forward. No new RH route is admitted.

**Final validation.** Optimized the existing edge-independence proof by replacing two `linear_combination` calls with successive subtraction cancellation. Its statement, imports and heartbeat settings are unchanged. The first full-source scratch exposed reversed cancellation-lemma names and a nonexistent convenience cpow lemma; those were corrected using this toolchain's actual statements. Final `lake env lean /tmp/hgt-iae-contour-edge-after.lean` exited 0 without warnings, with five selected axiom lists containing only standard foundations. The scratch includes the literal residue and zero specializations. The edited repository source matches `/tmp/hgt-iae-contour-edge-after-source.lean` exactly.

Final `LEAN_NUM_THREADS=1 lake build GaloisForLFunctions.RHTower.SmoothAFEZetaArbitraryNegativeEdge` exited 0; only the edited leaf was built (42s). The reported 9,122 jobs describe its target graph, not fresh compilations. Its existing umbrella import occurs exactly once. No full or umbrella build ran. `scripts/formal_tools.py lint` exited 1 solely for the existing, unrelated `Sieve.KloostermanGlobalCollisionCoprime` umbrella reachability error. Scoped whitespace and source comparisons passed. All owned scratch, search, build and lint processes are terminal. Three further retrieval records bring the evidence to 64 unique queries. No new module, added axioms, numerical experiment, heartbeat increase, commit or push. Removing tactic calls is a proof-code simplification; no measured end-to-end speedup or mathematical novelty is claimed.

## U. Prime-word relations and their nonzero infinite completion

**Question and admission test.** Could a relation among the actual multiplicative prime letters, absent at each finite stage but present in an infinite completion, supply a geometric meeting obstruction within the critical strip? The retrieved `arithmetic_zero_relationLattice_infinite_corank` does not mention a zeta zero: its zero is the bottom submodule. `KroneckerFlow.lean` supplies the relevant literal arithmetic datum, the injective integer frequency `ell(m)=sum_p m_p log p` on finitely supported prime exponent vectors.

**Finite conjecture/proof.** For `Re(s)!=0`,

    product_p (p^(-s))^(m_p) = 1  iff  m=0.

For finite support the product is exactly `exp(-s ell(m))`. Exponential periodicity forces its exponent to be an integer multiple of `2 pi i`. Taking real parts gives `Re(s) ell(m)=0`; unique factorization, via the existing prime-log frequency theorem, gives `m=0`. The converse is the empty word. This is a source-specific specialization of classical arithmetic, not an RH theorem. It already rules out a finite multiplicative relation as a selector anywhere in the critical strip.

**Infinite pivot and complete nonzero-limit classification.** The finite result alone would not settle the proposed completion. Allow an arbitrary integer family `m : primes -> integers`, and take products over the directed set of finite prime subsets, using `HasProd`. For `Re(s)!=0`, such a product has a nonzero complex limit if and only if `m` has finite support. Moreover, its limit is one if and only if `m=0`.

Paper proof: if finite products tend to `a!=0`, continuity of log modulus and the exact identity

    log |product_(p in S) (p^(-s))^(m_p)|
      = -Re(s) sum_(p in S) m_p log p

give an ordinary convergent sum of the real prime-log terms. Every nonzero term has absolute value at least `log 2`, since the coefficient is a nonzero integer and the prime is at least two. The cofinite term convergence test therefore forces finite support. Conversely, finite support gives its finite product, with every factor nonzero. The finite theorem then classifies limit one. The proof retains the nonzero limit throughout; it does not apply continuity of logarithm at zero.

**Sharp boundary and scope.** For each prime `p`, the nonzero purely imaginary parameter `s=-2 pi i/log p` makes the one-letter word with exponent one equal to one. Thus the real-part restriction cannot be discarded. The theorem concerns integer powers of the individual Dirichlet prime letters and unconditional products indexed by finite prime sets. It does not classify zero-valued products, Euler factors `(1-p^(-s))^-1`, grouped or renormalized products, or additive Dirichlet sums. An infinite sum vanishing is not a finite multiplicative relation among its atoms.

**Whole-route implication.** The proposed nonzero prime-word completion introduces no new relations when `Re(s)!=0`; it is equally restrictive throughout the critical strip. Thus this completion cannot produce the requested critical-line selector. Retain its exact nonzero-limit classification as the positive survivor. A different completion must specify which arithmetic operation and convergence law change, and must still prove the source-to-zero correspondence. This does not exclude all geometric or infinite methods and does not admit a new route.

**Method-search audit.** The generated infinite-product plan cites `finprod_of_infinite_mulSupport`, which assigns a conventional finite-product value on infinite support. That does not prove convergence. The proof above uses an actual `HasProd` hypothesis with a nonzero target. The lattice-period search returned an interval phase theorem with additional operator machinery; only the independent scalar exponential-period identity from mathlib is used. Five new deep searches are saved with full partial/coverage metadata, bringing the evidence to 69 unique queries. All five completed nonpartially, but source indexing remains incomplete and semantic coverage unavailable.

**Recent-paper admission audit.** Nguyen and Weisman, [Stability for boundary actions of cocompact lattices in Euclidean buildings](https://arxiv.org/html/2607.14668v1), July 2026: abstract, theorem search and coding conditions inspected. It needs a specified group action and compatible coding/interpolation conditions; no action of the arithmetic source satisfying them was constructed. No stability theorem is transferred.

Hughes and Ng, [Cobordism, spin structures, and profinite completions](https://arxiv.org/html/2601.05706v1), January 9, 2026: Theorems A–B and their surrounding hypotheses inspected. The conclusion concerns given aspherical manifolds with good fundamental groups and isomorphic profinite completions. Such manifolds, goodness and the comparison are not supplied here. The proof was not audited and no result is applied.

Yildirim, [Classification of Legendrian doubles and suspensions](https://arxiv.org/html/2609.08557v1), September 8, 2026: introduction and Theorems 1.1–1.3 inspected. Doubling starts from a specified exact Lagrangian filling in an open-book page. Its filling/classification conclusions do not construct that arithmetic input or identify a zero parameter. No theorem is applied.

Falcón, González-Regadera and Gudiel, [Fundamentals of the cocyclic development of Hadamard matrices over loops](https://arxiv.org/html/2609.08553v1), September 8, 2026: introduction, Definition 2.1, Lemma 2.2 and the associativity-obstruction definitions inspected. The proposed transfer would require an actual nonassociative source operation. Literal Dirichlet convolution is associative; the full scalar cutoff correction in P already obeys its exact three-product coherence identity. No new arithmetic associator is obtained by invoking loop cohomology. No enumeration, numerical result or Hadamard argument is used.

The September paper [Small undecidable groups and unrecognizable 4-manifolds](https://arxiv.org/abs/2609.10461) was screened at abstract level only. Its machine-checked group construction does not supply a source map to zeta. Other broad Dehn, dilation, filling, cobordism and braiding hits were search screens, not theorem applications.

**Final formal status.** New `formal/GaloisForLFunctions/RHTower/PrimeDirichletWordCompletion.lean` proves all the stated finite-word, nonzero infinite-product and imaginary-axis results. Final `lake env lean /tmp/hgt-iae-prime-word-final.lean` exited 0 without warnings; all ten axiom lists contain only `propext`, `Classical.choice`, `Quot.sound`. Earlier scratch failures were API/elaboration issues, including the imaginary-axis coordinate simplification, and are resolved. The finite-word exponential identity now reuses the finite-product identity directly. No heartbeat setting is present. Repository source matches `/tmp/hgt-iae-prime-word-final-source.lean` and the checked scratch proof text; only the explanatory sentence about the topology was clarified after scratch.

Final `LEAN_NUM_THREADS=1 lake build GaloisForLFunctions.RHTower.PrimeDirichletWordCompletion` exited 0, compiling only this leaf (1.0s). The 3,000 reported jobs describe its target graph, not fresh compilations. Its import was appended to `RHTower.lean`, preserving other work, and occurs exactly once. No full or umbrella build ran. Global lint exited 1 for two unrelated umbrella reachability errors: `FiniteCutoffCompensatingInfinityNoGo` and `Sieve.KloostermanGlobalCollisionCoprime`. It reports no error in the new leaf. Source comparison and whitespace checks passed; all owned search, scratch, build and lint commands are terminal. No added axioms, numerical computations, heartbeat increases, commits or pushes. These are elementary source-domain results, not a research novelty claim or progress in zero confinement.

## V. Fixed arithmetic orderings and the retained additive endpoint

**Question and source test.** Can a failure of different arithmetic summation orders to meet distinguish critical-line zeros? U tested multiplicative prime words and could not access additive cancellation. This test uses the literal alternating Dirichlet source. For fixed positive integers `a,b`, take `a` odd terms, then `b` even terms, repeatedly, with the original signs and weights. At the end of round `N`,

    C_N(a,b;s) = sum_(0<=n<aN) (2n+1)^(-s)
                - sum_(0<=n<bN) (2n+2)^(-s).

Both parity lists exhaust their classes; the ordering is specified before choosing the complex parameter or any zero. The Lean theorems below concern these complete-round prefixes. No arbitrary rearrangement or unordered tsum is assumed.

**First conjecture and exact endpoint.** The inspected corpus theorem `ZetaPartialSumStrip.tendsto_sum_cpow_sub_pow` supplies the actual partial-sum asymptotic

    H_N(s) - N^(1-s)/(1-s) -> zeta(s),  Re(s)>0, s!=1.

The finite odd/even partition gives, without a limit interchange,

    C_N = H_(2aN) - 2^(-s) H_(aN) - 2^(-s) H_(bN).

Insert the three asymptotics and use positive-integer-base complex-power multiplication. The exact leading coefficient and common finite part are

    B(a,b;s) = 2^(-s) (a^(1-s)-b^(1-s))/(1-s),
    E(s)     = (1-2^(1-s)) zeta(s),
    C_N - B(a,b;s) N^(1-s) -> E(s).

This proves the complete endpoint formula on `Re(s)>0`, `s!=1`; it does not infer convergence of the uncorrected sums from analytic continuation. All finite parity identities, dilation limits and the complete centered limit are closed in Lean.

**Failure and stronger positive survivor.** For `0<Re(s)<1`, the coefficient `B` is zero exactly when `a=b`. Indeed, equality of the two positive-base complex powers implies equality of their norms, hence `a^(1-Re(s))=b^(1-Re(s))`; injectivity of that real power gives `a=b`. The factors `2^(-s)` and `1-s` are nonzero on this domain. Multiplying the centered formula by `N^(s-1)` then gives

    C_N N^(s-1) -> B(a,b;s).

If `a!=b`, its nonzero limiting magnitude implies `|C_N| -> infinity`. If `a=b`, the endpoint is identically zero and `C_N -> E(s)`. Thus, throughout the strip,

    (exists a finite complex limit of C_N) iff a=b.

The fixed two-odd/one-even ordering already diverges throughout the entire strip, including at any zeta zero there. The stronger positive survivor is this exact classification together with the full finite-part and normalized asymptotics. On `Re(s)>1`, every positive quota converges to the usual eta value because its endpoint decays; this is also proved. The line `Re(s)=1`, variable quotas, arbitrary permutations and other summation procedures are not classified here.

**Whole-route implication.** Fixed arithmetic-order disagreement is not a zero selector: it occurs uniformly in the strip, without a zero hypothesis. Correcting the disagreement by its complete endpoint recovers the same eta value for every quota, so it supplies no independent location law. A valid new construction still needs source-derived compatibility that changes specifically at the relevant zeros. Neither unrestricted order invariance nor removing an explicit endpoint supplies that law. This test is closed as an admission failure, with its positive boundary formalized; it is not an admitted route. These are classical summation asymptotics, not a research novelty claim.

**Corpus and method audit.** Five additional queries are saved in `search-evidence.json` (74 unique queries total). Four completed nonpartially with 57,931 inventoried files, 57,930 indexed and one failed; compiler metadata is largely pending and semantic coverage unavailable. The periodic-order query is partial, with deadline and `filter_and_judge` unfinished and no coverage snapshot. Available hits were used without assuming exhaustive coverage. The generated plans confused cancellation in an `Additive` type tag with cancellation of series, offered a finite `Fin 4` permutation theorem as an infinite rearrangement step, and proposed eta tsum identities whose admitted domain is `Re(s)>1`. None proves the strip rearrangement claim. The proof instead uses exact finite sums and the retrieved partial-sum theorem.

`PrimeRelabellingScalarAudit.lean` was read in full: its scalar equality to zeta is proved on absolute convergence, while its finite comparison retains the transported cutoff. `SummationGraphDenseCollapse.lean` was read in full but its Hilbert closure argument is not used in this construction. The chronological-schedule source was inspected through its exact domain and diagonal identity; it already retains a nonzero boundary under its own cutoff assumptions. The quartic prime-compression comparison was screened at definitions and theorem statements and is an existing source comparison, not a new zero-free law. None is repackaged as a new route.

**Recent-paper admission tests.** Rodrigues, [On the Possible Values of the Rearrangement Number](https://arxiv.org/html/2607.18726v1), July 21, 2026: introduction, invariant definitions and the finite reflection-bijection proof were inspected. Its invariant quantifies over families disrupting every conditionally convergent real series, and its new conclusions concern forcing models. It supplies neither a fixed arithmetic ordering nor a theorem about complex zeta parameters. No forcing or cardinal-characteristic theorem is used. Its quantifier distinction motivated testing a parameter-independent literal ordering rather than invoking a rearrangement selected to force a desired value.

Blokh, Oversteegen and Timorin, [Limit cubic laminations](https://arxiv.org/html/2607.26812v1), July 29, 2026: introduction through Theorem 1.1 and Corollary 1.2 inspected. The setup concerns limits of critical portraits of cubic polynomial dynamics, with specified connected and locally connected filled Julia sets. No arithmetic polynomial sequence, invariant lamination or zero correspondence was constructed, so no theorem is transferred. The word “critical” in this setting does not identify a zeta critical line.

Other broad searches included sewing, defect, condensation, fracture, tilings, separability and Arens. Robotics, numerical optimization and excluded operator results were screened out. [Soft tilings](https://arxiv.org/abs/2604.18545) was inspected only through its abstract; no tiling theorem is applied. The June semigroup-sewing paper returned again but supplies no new arithmetic realization beyond the admission issue already recorded in R. No numerical experiment or paper computation was performed.

**Final formal audit.** New `formal/GaloisForLFunctions/RHTower/EtaArithmeticRoundConvergence.lean` contains the exact source and classification. Final `lake env lean /tmp/hgt-iae-eta-rounds-final.lean` exited 0 without warnings. All nineteen public definitions/theorems were axiom-audited and use only `propext`, `Classical.choice`, `Quot.sound` (some use fewer). Earlier scratch failures concerned casts, nested power normalization, a wrongly qualified limit-lemma name, and a missing `sub_self` simplification; all were resolved without heartbeat changes. A direct natural-number power wrapper is reused throughout the finite and asymptotic proofs.

Final `LEAN_NUM_THREADS=1 lake build GaloisForLFunctions.RHTower.EtaArithmeticRoundConvergence` exited 0; only this leaf was built (8.8s). The 3,163 reported jobs describe its dependency graph, not fresh compilations. Its umbrella import was appended without replacing other work and occurs exactly once. Global lint exited 1 solely for the unrelated `Sieve.KloostermanGlobalCollisionCoprime` umbrella omission. The new source matches its canonical snapshot and the checked scratch proof text exactly; scoped whitespace and forbidden-token checks passed. All owned search, scratch, build and lint commands are terminal. No full or umbrella build, added axioms, numerical computation, heartbeat increase, commit or push.

## W. Character-point descent: source admission remains open

**Question and whole-route gate.** Does the retrieved arithmetic point construction supply both multiplication and enough independent addition to constrain zeta zeros? A scientist must distinguish the kernel of a multiplicative map from a zero of a formed Dirichlet function before transferring either geometry or a descent statement. No new route is admitted.

**Source facts inspected.** `DeningerDynSysValuedPointsAffine.lean` defines `DeningerAdditiveOnZeros Q` as `Q f' = 0 → Q (f+f') = Q f`, for all `f,f'`. This is translation invariance along a zero fibre, not full additivity. `DeningerDynSysAffineTopology.lean` defines affine points using this predicate, induces their topology from evaluations, and projects through the kernel prime ideal. `DeningerDynSysWittValuedPoint.lean` already supplies `deningerFieldPointedEquivChar`, an exact equivalence between pointed multiplicative maps of fields and unit-group characters. The character evaluations retain information beyond the base projection. `DeningerDynSysWittCharPoints.lean` requires algebraically closed residue fields for its Witt/character equivalence; those assumptions cannot be discarded on ordinary arithmetic fibres.

**Unfinished mathematical test.** The expected field specialization makes zero-fibre translation automatic, since nonzero field elements are units. This is an elementary consequence of the inspected multiplicative structure, but no new Lean theorem or complete topological classification was audited in W. In particular, constant kernel projection would not make the character space constant or identify its characters with zeta zeros. The next route-relevant obligation is an independently specified arithmetic operation on this surviving data and a proved zero correspondence. Another abstract quotient or a kernel lemma alone would not remove that obligation.

**Search controls.** Four deep searches are persisted in `search-evidence.json`: arithmetic descent at infinity, two arithmetic laws, affine generic points, and character phase topology. All returned nonpartial source snapshots with 57,932 inventoried files, 57,931 indexed and one failed; compiler coverage remains mostly pending and semantic coverage unavailable. Candidate/source names and proposed ingredient plans were inspected. Generic additive type tags, a conditional exact-descent package, finite elliptic coordinates, and a generated density-to-zero-census plan do not construct the needed arithmetic source or incidence.

**September primary-paper screening; no result transferred.**

- Luan–Li, [A continuous 3-distributive frame that is not ω-distributive](https://arxiv.org/html/2609.11671v1), submitted 10 September 2026: inspected the abstract, definitions, early finite-arity proof and portions of the final construction. Open-frame meets are interiors of set intersections. An empty open meet therefore must not be read as an empty intersection of points. The finite-versus-unbounded-arity distinction supplies no arithmetic realization here; the complete final proof was not audited.
- Gaucher, [The homotopy types of directed path and trace spaces](https://arxiv.org/html/2609.11454v1), submitted 10 September 2026: inspected the abstract, hypotheses and fibre construction. Its directed path/trace quotient can lose homotopy information; no corresponding arithmetic path space or quotient has been constructed. The whole proof was not audited.
- Kupers–Miller–Patzt, [The Morita classes are nonzero](https://arxiv.org/html/2609.12951v1), submitted 11 September 2026: inspected stated results and the specified unipotent cycle construction, not the main proof. The cycles concern automorphism groups of free groups and integer linear groups. No cycle respecting the actual additive Dirichlet source was supplied.

**Outcome.** Source admission remains open, and no positive-survivor theorem is claimed for W. This screen does not retire the full arithmetic character construction. Work switched to the user's explicit Lean optimization request; its validation is recorded separately on the card.

## X. The literal degree-zero twisted arithmetic source

**Discriminating question.** Can an infinite arithmetic twisted-trace quotient retain a new obstruction at a zeta zero, before a zero condition is inserted? This is the explicit ordinary-ring construction in Sun's September paper, not an analogy with a physical trace. The previous turn's optimization was verified engineering progress; it did not close the source law.

**Current-corpus starting point.** `OperatorTailDirichletMatroid.lean` already defines the exact coefficient shift `T_s f(n)=n^(-s)f(n)` and proves its addition/convolution laws. `FiniteAbscissaDirichletUpperEnd.lean` already supplies the finite-abscissa algebra and its stability under complex shifts. `ArithmeticFunctionScalarEvaluation.lean` classifies algebra homomorphisms from the unrestricted coefficient algebra, but does not classify linear twisted traces on analytic domains. The new audit reuses the existing shift; it does not rename that operation as a new primitive. STATUS CANNOT-89/MUST-64 already exclude assuming an additive lift as a substitute for constructing it.

**Conjecture → exact source test.** For the commutative Dirichlet-convolution algebra `A`, the degree-zero twisted relation is `T_s(u)*v-v*u`. Set `P_s f(n)=f(n)/(n^(-s)-1)`. For `Re(s)!=0` and `n>1`, taking norms in `n^(-s)=1` would give `n^(-Re(s))=1`, hence `n=1`, a contradiction. At index one `P_s f` is zero by the field's zero-division convention; the difference equation retains the coefficient-one remainder explicitly. Coefficientwise cancellation proves

`T_s(P_s f)-P_s f = f - f(1)*1_A`.

Every twisted relation has coefficient one zero because convolution multiplies coefficient one and `T_s` fixes it. Conversely, every family with that coefficient zero is the single relation above with `v=1_A`. Therefore the set of relations itself is the augmentation ideal, before taking an additive span or ideal span. The quotient is canonically `ℂ`, and the class of `f` vanishes exactly when `f(1)=0`. The automorphism's inverse is `T_(-s)`.

**Whole-route consequence of the first result.** For fixed arithmetic coefficients, this quotient reads a coefficient already specified before forming the Dirichlet function. In particular a source with first coefficient one has a nonzero quotient class at every parameter covered by the theorem. It cannot supply the proposed zeta-zero obstruction. An independently formed parameter-dependent first coefficient would be additional source data, not information recovered by this quotient.

**Fail → analytic-domain pivot.** An unrestricted formal solution need not belong to an analytic source. Test that escape rather than retire a larger family. If `σ=Re(s)>0`, put `d=1-2^(-σ)>0`. For `n>=2`, `norm(n^(-s))<=2^(-σ)`, so the reverse triangle inequality gives `norm(n^(-s)-1)>=d`. Thus

`norm(P_s f(n)) <= norm(f(n))/d`

for every index; the zero and one indices are checked separately. Comparing absolute Dirichlet terms proves that `P_s` preserves each point of absolute convergence, with no shift of its abscissa. It consequently belongs to the corpus's finite-abscissa algebra whenever `f` does, and the exact difference equation holds inside that algebra. Applying any complex-linear functional invariant under `T_s` gives `tau(f)=f(1)*tau(1)`.

**Whole-route consequence of the analytic result.** Restricting to this actual finite-abscissa source does not restore the information discarded by the twisted readout. This closes the tested analytic-domain escape throughout the strict right half-plane. It does not classify higher homology, nonregular bimodules, parameter-dependent source formation, or other domains lacking the proved inverse. No RH or novelty claim is made; the positive survivor is the exact primitive, quotient classification and analytic preservation theorem.

**Primary-paper transfer audit.**

- Sun, [Twisted Bicategorical Shadows and Traces](https://arxiv.org/html/2609.04660v1), submitted 4 September 2026: read the abstract, ordinary degree-zero definition and Example 4.25(1). The latter is an additive quotient by `g(r)m-mr` for a ring with an automorphism action. Taking the existing Mellin automorphism and regular bimodule realizes precisely those relations; their literal set is already the augmentation ideal here. Higher equivariant results, perfect-module comparisons and topological constructions were not applied or claimed audited.
- Ren, [Frobenius–Cartier duality via lax equalizers](https://arxiv.org/html/2609.10140v1), submitted 9 September 2026: read the initial definitions/theorems and final Ind–Pro statement/proof outline. The application requires a fixed Noetherian F-finite scheme of characteristic p with a unit dualizing complex. Its final extension starts from an already constructed small-category duality. These conditions supply no missing arithmetic source correspondence here; no theorem was transferred.
- Bottegoni–Ferri–Saracco, [Frobenius functors and one-sided Hopf algebras in braided monoidal categories](https://arxiv.org/html/2609.13028v1), submitted 11 September 2026: abstract screen only. No bimonoid or free Hopf-module functor from the proposed source was supplied, and no result was used.

**Search evidence.** Four deep queries are persisted: character addition/source, arithmetic completion/reciprocity, twisted arithmetic trace, and bounded inverse/analytic domain. All report nonpartial snapshots, 57,933 inventoried files, 57,932 indexed, one failed, 45,097 compiler entries pending, and unavailable semantic coverage. Every candidate/source name and proposed ingredient-step obligation was inspected. The generated routes from `add_zero`, finite reciprocity, coefficient tags, convolution summability or scalar multiplication do not establish the required coefficientwise inverse; the source proof above does.

**Final formal audit.** `ArithmeticDirichletTwistedBoundary.lean` matches `/tmp/hgt-iae-twisted-source-final-source.lean`. Full-source `lake env lean /tmp/hgt-iae-twisted-source-final.lean` exited 0 without warnings; all 22 declaration axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`. Final `LEAN_NUM_THREADS=1 lake build GaloisForLFunctions.RHTower.ArithmeticDirichletTwistedBoundary` exited 0, rebuilding only this leaf in 13s (8,694 reported target-graph jobs). Its umbrella import was appended atomically and appears once. Global lint has only the unrelated `Sieve.KloostermanGlobalCollisionCoprime` umbrella error. No heartbeat option, added axiom, numerical experiment or full/umbrella build. All owned processes are terminal. This closes the tested degree-zero receiver and its stated analytic-domain escape; it does not promote this card to a proof route.


## Y. Squarefree topology and Lambert boundary: existing frontiers; X proof optimization

**Scientific question.** Can the literal Möbius source acquire a new cancellation law through its squarefree topology or its generating-function boundary? The discriminator is a source-derived bound, not a new name for the same missing bound.

**First screen and whole-route consequence.** The current universal ledger already records `CANNOT-349`: the natural squarefree product complex has linearly many independent classes and consequently cannot admit an acyclic matching with only square-root many critical faces. That paper result was read from the ledger, not newly proved or Lean-audited here. Allowing non-acyclic arithmetic matchings returns to existing route E. Neither change admits a new route; no duplicate no-go module was added.

**Second screen and positive statement already present.** Source inspection of `MobiusLaplaceCriterionFrontier.lean` identifies the literal series `Phi(x)=sum mu(n) exp(-n*x)`, its absolute convergence at each positive scale, and the exact absolutely summable dilation law `sum_(k>=1) Phi(k*x)=exp(-x)`. The file already proves `MobiusDiscreteLaplaceHalfDecay -> RiemannHypothesis`; the half-decay definition explicitly asks for `norm(Phi(x)) <= C*x^(-1/2)` near zero. The retrieved Lambert inversion laws do not prove that bound. Whole-route consequence: the proposed starting object and correspondence already exist, while the arithmetic cancellation remains open. This is failure of novelty/admission, not a proof that all boundary-geometric approaches fail. No natural-boundary theorem or infinite cyclotomic product was asserted.

**Recent-paper screen.** Alon, Haxell, Milojevic and Verstraete, [Spanning subhypergraphs with degree constraints](https://arxiv.org/html/2609.13002v1), submitted 11 September 2026: read abstract and introduction through Theorems 1.1–1.4 and Conjecture 1.5. Their bounded-degree spanning subhypergraphs require a regular uniform hypergraph. No such arithmetic regularity was established here; their result supplies neither the missing incidence law nor an RH transfer. August [monodromy surfaces](https://arxiv.org/abs/2608.25594) and July [monodromy defects](https://arxiv.org/abs/2607.06669) were abstract-only screens; no result was used. Recent-list metadata is not a proof audit.

**Corpus controls.** Three research screens plus one optimization search used whole-corpus deep retrieval with source arguments and generated ingredient sets. Each reported 57,935 inventoried files, 57,934 indexed, one failed, and 45,099 compiler-pending files. All returned nonpartial, with source/semantic warnings; some snapshot-generation warnings also occurred. The generated torus-characteristic/physical-cutoff bridge supplies no map from squarefree faces; division congruence is not signed cancellation; the proposed manifold `boundary_product` does not describe an infinite Lambert boundary. The optimization query's Hahn/Witt zero-coefficient plan does not apply to arithmetic-function scalar evaluation. Relevant actual APIs were read directly and checked in scratch. These rejected suggestions are recorded as retrieval failures, not mathematical proofs.

**Requested optimization, independently of RH progress.** Four proof bodies in X's `ArithmeticDirichletTwistedBoundary.lean` now use explicit coefficient identities, the specific arithmetic-function extensionality theorem, and bounded simplifier sets. All mathematical statements, imports and constructions are preserved. Tactic-form heartbeat measurement (which does not change the heartbeat limit) covers fourteen standalone proof bodies, excluding structure-field proofs and elaboration outside those bodies. Baseline 9,275,827 internal ticks; candidate 7,097,105, a 23.5% reduction in this single-run comparison. The primitive identity alone drops from 2,084,732 to 876,996 ticks (57.9%). No end-to-end speedup is inferred. Full candidate scratch passed, including API checks and all 22 declaration axiom reports; only `propext`, `Classical.choice`, `Quot.sound` occur. Final `LEAN_NUM_THREADS=1 lake build GaloisForLFunctions.RHTower.ArithmeticDirichletTwistedBoundary` exited 0 and rebuilt only this leaf (26s; 8,694 target-graph jobs reported). Lint exited 1 solely for the existing unrelated `RHTower.Sieve.KloostermanGlobalCollisionCoprime` umbrella omission; remaining output is large-file warnings. Source/snapshot identity, the four-proof-only diff, unique umbrella import, whitespace and 87 unique search records were checked. All owned commands are terminal. No full builds, heartbeat increases, new mathematical hypotheses, added axioms or numerical experiments were used. Logs and validated source snapshots use `/tmp/hgt-iae-twisted-opt-`.

**Right-problem check.** The optimization answers the explicit code request; it is not evidence of a new RH route. The next research obligation remains an independent arithmetic law that proves cancellation while retaining the full source. The five admission gates remain unchecked.


## Z. Finite-abscissa inversion and the scalar-point obstruction

**Previous turn classification.** Y completed verified proof optimization and changed the next research action by identifying duplicate source constructions. It did not advance zero confinement. Z tests the remaining analytic-domain escape from L and X, rather than re-proving either statement.

**Candidate and discriminator.** Could the entire finite-abscissa arithmetic algebra provide additional complex algebra evaluations from which to construct two independent geometric foliations? X only classified shift-invariant linear readouts there, and L classified algebra maps on the larger full formal algebra. Conjecture Z: the finite-abscissa algebra itself is closed under formal inversion at every family with nonzero first coefficient. If true, its scalar algebra maps already collapse without assuming shift invariance or continuity.

**Source-grounded proof.** Write A for the actual `finiteAbscissaArithmeticSubalgebra`. Its elements admit some half-plane of absolute Dirichlet convergence; that half-plane may depend on the element.

1. If an arithmetic family `w` has `w(1)=1` and its absolute tail sum is at most one, its formal Dirichlet inverse `g` satisfies `norm(g(n))<=1` at every index. The retrieved proper-divisor recursion gives the induction step. Each proper divisor `d` of nonzero `n` has cofactor `n/d>1`; the cofactor map is injective, since applying `n/(-)` again recovers `d`. Consequently the sum of `norm(w(n/d))` over these cofactors is bounded by the full absolute tail. Every earlier inverse coefficient is at most one, closing the induction. Index zero and index one are treated separately. This uses an actual convergent tail sum, not the default value of a nonsummable `tsum`.
2. For an element `h` of A with `h(1)=0`, the arithmetic family with coefficients `norm(h(n))`, embedded in the complex numbers, is also in A. The existing `LSeries.tendsto_atTop` theorem makes its Dirichlet series tend to zero along the real axis. At a sufficiently large real `b`, it is absolutely summable and at most one. Its individual terms are exactly the embedded real numbers `norm(T_b h(n))`. Thus the needed small absolute tail is produced, rather than assumed.
3. For `f(1)=1`, apply step 2 to `h=f-1`. The shifted family `w=T_b f` satisfies step 1, hence has a bounded inverse. Bounded coefficient families belong to A. Applying `T_(-b)` to the inverse equation gives an inverse of `f` in A because the existing shifts are algebra automorphisms and preserve A.
4. For `f(1)!=0`, normalize by the scalar `f(1)^(-1)`. The normalized product is a unit by step 3, so `f` is a unit. Conversely any unit has nonzero first coefficient by augmentation. The resulting exact theorem is `IsUnit f iff f(1)!=0`. The canonical formal inverse equals the inverse in A by multiplying the two inverse equations; its membership in A is also proved explicitly.
5. For a complex algebra map `phi:A->C`, suppose `phi(f)!=f(1)`. Then `f-phi(f)*1` has nonzero first coefficient and is a unit by step 4, while its image under `phi` is zero. Since a unital homomorphism sends units to units, this is impossible. Therefore `phi(f)=f(1)` for every `f`, and the map is exactly augmentation.

**Whole-route consequence.** Passing from all formal coefficient families to the union of all finite-abscissa domains does not recover scalar arithmetic points: the attempted receiver still forgets every higher coefficient. This closes the specific analytic-domain escape and removes X's shift-invariance premise for algebra maps. The retained positive statement is the exact unit criterion and canonical inverse closure. It does not keep an inverse's original convergence abscissa, rule out scalar evaluation on smaller domains, classify merely multiplicative characters, or discard the faithful germ-valued realization of A. No zero-location law, RH proof, or mathematical novelty claim is made. W's broader character-space question remains unadmitted rather than retired wholesale.

**Recent geometric input and transfer limit.** Sagman and Saric, [Holomorphic realizations of pairs of foliations on Riemann surfaces](https://arxiv.org/html/2609.12217v1), submitted 10 September 2026: inspected abstract and introduction through Theorem 1.1 and its discussion. Their existence theorem needs two finite-Dirichlet-integral laminations that fill the surface, and constructs a possibly different conformal surface. We supplied neither arithmetic laminations satisfying those conditions nor identification of the resulting marked conformal structure with an arithmetic source. Its geometric construction was motivation for the discriminator, not an applied theorem. No energy-minimization or uniqueness argument was imported.

**Corpus and novelty audit.** Six deep queries search the whole indexed corpus and installed dependencies; all report nonpartial results, 57,935 inventoried files, 57,934 indexed, one failed, 45,099 compiler-pending entries, incomplete-source and unavailable-semantic-coverage warnings. Source-name/proof search found the formal inverse recursion and the existing shifts. Direct API inspection found the far-right limit theorem. An additional source scan checked all 39 files containing the exact finite-abscissa algebra name for unit/inverse/augmentation markers; no existing statement of this criterion or scalar classification was found. This is not a claim of exhaustive literature novelty. Generated plans based on finite-set convolution inversion, bare cohomology projections, unspecified limit exchange, or foliation rescaling supply none of the required inverse bound. The tail plan's nonnegative-Mobius premise is false and its bounded-coefficient convergence claim on `Re(s)>0` is insufficient; neither was used.

**Lean final audit.** `FiniteAbscissaArithmeticUnits.lean` contains four public theorems: `isUnit_iff`, `dirichletInverse_mem`, `algHom_apply`, and `algHom_eq_augmentation`, in namespace `RHTower.FiniteAbscissaUnits`. Full canonical-source scratch `/tmp/hgt-iae-finite-unit-final.lean` exited 0 without warnings; all twelve declaration axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`. The final `LEAN_NUM_THREADS=1 lake build GaloisForLFunctions.RHTower.FiniteAbscissaArithmeticUnits` exited 0 and rebuilt only this leaf (22s; 8,695 target-graph jobs). Its import was appended once to the umbrella. Lint exited 1 solely for the existing unrelated `RHTower.Sieve.KloostermanGlobalCollisionCoprime` umbrella omission; remaining output is large-file warnings. Source/scratch identity, whitespace, forbidden declarations, unique import and 93 unique retrieval records were checked. All owned commands are terminal. No heartbeat changes, numerical experiments, added axioms or full builds. Canonical source snapshot: `/tmp/hgt-iae-finite-unit-final-source.lean`; final/build/lint logs share the `/tmp/hgt-iae-finite-unit-` prefix.

**Right-problem check and next obligation.** This result removes a concrete proposed source receiver, not the RH obstruction itself. A subsequent construction must retain the individual arithmetic evaluation domains or use a genuinely different source-valued geometric map. Merely renaming that domain diagram would return to the existing completion frontier; a new law must be identified before it is admitted as a route.


## AA. Domain admission screen and inverse-closure proof optimization

**Hard obstacle and whole-route test.** Z excludes complex algebra evaluations on the entire finite-abscissa algebra. Retaining individual domains is necessary for that proposed repair, but does not itself construct a new arithmetic law. Four further deep queries supplied no source-to-zero or location implication. Their exact candidates, generated methods and coverage warnings are retained in `search-evidence.json` (97 unique records). None reports partial completion, but source indexing is incomplete and semantic coverage unavailable; compiler verification remains mostly pending. The first two also report older-generation coverage snapshots.

**Proposed transfers, rejected at admission.** Rydval's [Deciding Amalgamation Beyond Arity Two: The Semantic Horn Case](https://arxiv.org/html/2608.12206v1), submitted 12 August 2026, was inspected through its abstract, introductory theorem statements and mechanism discussion. Its finite relational completion template and bounded-width certificate require a specified semantic-Horn class. No arithmetic template, relation-preserving encoding, or source equality was supplied. The paper is not an applied theorem here. Broad braiding, welding, winding and universality searches mostly returned unrelated material; exceptional-point learning uses excluded machinery and was discarded at abstract screening. The recent dynamical-systems title listing was only partly inspected, and supplies no theorem evidence.

The recurrence query returned generic analytic-domain and separation statements. Its suggested Fourier-delta/continuation plan does not prove arithmetic recurrence. `ParabolicOrbitRigidity.lean` concerns a positive-measure Cauchy source and is not an admissible zeta argument. The blowup query returned existing `XiSourceNormalConeDivisorConservation.lean`: its endpoint chart already divides a given carrier by its value at the retained coordinate, and its exceptional section is `f(0)/f(u)`. Reusing that construction does not independently derive the missing arithmetic incidence. Conditional Sonin criteria and arbitrary blowup-order injectivity likewise supply no acceptable new law. These are admission failures, not proofs that every domain or blowup mechanism is impossible. No route was retired or newly admitted; universal STATUS receives no duplicate or route-specific entry.

**Optimization experiment.** Preserve every statement, import and heartbeat limit in `FiniteAbscissaArithmeticUnits.lean`. Use tactic-form heartbeat counters on the nine standalone tactic proof bodies, with no command-form limit override. Compare direct inverse uniqueness, direct algebra-map extensionality, and explicit map identities with the original proofs. The private definitional bodies and elaboration outside measured tactics are outside the measurement. This answers the user's code request; it does not advance zero confinement.

**Execution correction.** A profiling scratch command was accidentally started while the candidate scratch was still running. Its exact owned Lake/Lean PIDs were terminated immediately and the handle exited 143. No other process was touched. The remaining candidate completed before the profile was restarted. The restarted profile's proof bodies elaborated, but two uninstantiated API probes failed universe inference; it is not a successful audit. The subsequent full-source audit must instantiate those probes explicitly. No limit was raised.

**Optimization result and final audit.** Retained four proof changes: explicit map subtraction/product identities and coefficient evaluation in `isUnit_of_one`; the source-verified `left_inv_eq_right_inv` in `dirichletInverse_mem`; direct nonzero image-of-unit contradiction in `algHom_apply`; and `AlgHom.ext` in `algHom_eq_augmentation`. Nine standalone tactic bodies measured 11,002,605 internal heartbeats before and 9,599,690 after, a 12.8% reduction. The largest extensionality improvement is 903,985 to 64,787 ticks. The unit-construction body falls from 4,473,979 to 3,999,641. These are single-run tactic measurements, not an end-to-end build speedup. The final equality-transport variant measured 9,601,250, slightly higher, and was discarded as a whole.

The retained full-source scratch `/tmp/hgt-iae-unit-opt-second-counts.lean` exited 0 without warnings; all twelve declaration axiom lists contain only `propext`, `Classical.choice`, `Quot.sound`. The subsequent variant also passed, including explicitly instantiated `left_inv_eq_right_inv` and `AlgHom.ext` API probes; only its proof replacements were discarded. Canonical source exactly matches the retained checked scratch after removing measurement/audit scaffolding. Erasing the four changed proof bodies makes the before/after source identical; no statements, imports, constructions or options changed.

`LEAN_NUM_THREADS=1 lake build GaloisForLFunctions.RHTower.FiniteAbscissaArithmeticUnits` exited 0 and rebuilt only this leaf (16s; 8,695 target-graph jobs). The umbrella import remains unique. `scripts/formal_tools.py lint` exited 1 solely for the existing unrelated `RHTower.Sieve.KloostermanGlobalCollisionCoprime` umbrella omission, plus large-file warnings. Source whitespace, forbidden-declaration checks and 97 unique search records passed. All owned search, scratch, build and lint commands are terminal; the final process scan found no owned Lean process. No heartbeat limit was raised, no numerical mathematical experiment was run, and no full build, commit or push occurred. Source snapshots, measurements JSON and logs use `/tmp/hgt-iae-unit-opt-`.

**Right-problem check.** This is a completed scoped optimization, not an advance in zero confinement. The mathematical admission screen supplies no new primitive or source law. Keep the RH goal open; the next research attack must produce arithmetic incidence and a location implication before expanding another geometric candidate.


## AB. Ordinary cusp periods of the literal Dirichlet source

**Previous turn and hard obstacle.** AA completed scoped optimization and rejected ungrounded geometric transfers; it did not advance zero confinement. The current test asks whether a concrete two-point projective construction can be admitted on the literal infinite arithmetic source. A new zero-location law remains absent.

**Candidate, proof/failure, pivot.** Saber and Sebbar's [Projective Kernels and Replicability in Modular Function Theory](https://arxiv.org/html/2609.12838v1), submitted 11 September 2026, compares diagonal differential data with Faber–Grunsky coefficients in an ordinary cusp expansion. We inspected the abstract and introduction through the initial higher-Schwarzian formulas. Its normalized cusp requires a fixed translation period; modular replication is an additional law, not a consequence of general coefficient multiplicativity. Its rigidity/classification results are not imported. First test the direct arithmetic candidate: could the literal zeta source have such a period far to the right? The source coefficient test below says no. Pivot: use a primitive so that zeta zeros are critical points rather than values. A periodic primitive would have periodic derivative on that domain, and hence fails the same test. This does not address arbitrary nonlinear changes of source coordinate or infinite-order projective monodromy.

**Exact positive survivor, dependency-closed paper proof.** For a finite-abscissa arithmetic family f and a complex translation a, equality `L_f(x+a)=L_f(x)` for all sufficiently large real x is equivalent to `T_a f=f`. The existing shift identity converts the two functions to L-series of f and T_a f, both with finite abscissa. Existing coefficient uniqueness then gives equality at every positive index; both arithmetic families vanish at zero. Conversely coefficient equality gives equality of the full L-series functions through the exact shift identity. Coefficientwise this is precisely `n^(-a)=1` at every nonzero supported coefficient.

For the actual zeta source, all positive coefficients equal one. Thus `n^(-a)=1` for every positive integer. Taking the norm at n=2 forces `Re(a)=0` by real-power injectivity. If a were nonzero it could not be an integer, since an integer with real part zero is zero. The already proved Hurwitz non-rationality theorem rules out the eventual polynomial ratio `n^(-a)=1/1` for such a. Therefore a=0. Conversely zero translation is immediate. This argument does not assume RH, any zero information, or an unproved convergence estimate.

For a function whose derivative equals zeta on a right half-plane, a translation period there differentiates locally to the same period of zeta, taking x large enough that x and x+a belong to that domain. Uniqueness of derivatives and the preceding result force a=0. These exact statements are now scratch-checked in `DirichletTranslationPeriod.lean`; the targeted final audit follows. No new RH route is admitted.

**Whole-route consequence and scope.** The raw source cannot be identified with an ordinary periodic cusp merely by interpreting its frequencies as Fourier indices. The retained invariant is the exact support-dependent period criterion, including sources for which nonzero periods do exist. It does not turn absence of a function period into absence of arithmetic progressions in its zero set. The corpus's `PeriodicityDichotomy` explicitly retains a separate progression-exclusion hypothesis; it is not discharged here. A different arithmetic map would need its own proved source and replication law.

**Stronger statement exposed by differentiation.** The same proof also excludes a constant additive increment `F(z+a)=F(z)+b` for a primitive of zeta on a right half-plane. Differentiating removes b, so a=0; evaluating the original identity then gives b=0. This is the precise stronger statement chosen for Lean. It excludes additive monodromy in the unchanged source coordinate, not arbitrary fractional-linear monodromy. The first scratch attempt failed only when a rewrite did not reduce an applied lambda; its generated `sorryAx` reports are not certificates. Direct composition of the already proved shift equality removes that tactic failure without changing a limit or assumption.

**Other retrieved methods and primary-paper scope.** Lastra and Malek, [Formal solution and strong asymptotic expansion of some initial value problem in two complex time variables, infinite order irregular singularities and Mahler transforms](https://arxiv.org/html/2609.12654v1), submitted 11 September 2026: inspected abstract and introduction, including the displayed equation, hypotheses and description of Theorem 1. Their formal equation, forcing restrictions and transforms have not been realized by the arithmetic source; their introduction explicitly separates strong asymptotic realization from an analytic solution of the original infinite-order problem. No theorem is transferred. The corpus's Mahler embeddings and unrelated norm-dilation identities do not discharge those requirements. Broad sewing, obstruction, ends, extension, compactification and gluing searches mostly returned unrelated or old material; the Complex Variables recent page was inspected only through the displayed first 28 titles, not all 66 entries.

Five deep queries are recorded with exact coverage and generated methods, bringing the own evidence file to 102 unique records. All report nonpartial results, 57,938 inventoried files, 57,937 indexed, one failed and 45,102 compiler-pending entries; source indexing remains incomplete and semantic coverage unavailable. The period query additionally reports an older-generation snapshot. Generic extension obstruction, kernel continuity, lcm/gcd multiplicativity and unrelated dilation norms are not accepted as arithmetic occurrence or replication proofs. Relevant shift, coefficient-uniqueness, non-rationality and local-derivative APIs were inspected directly before scratch checking.

**Scratch closure.** New leaf `formal/GaloisForLFunctions/RHTower/DirichletTranslationPeriod.lean` proves the full finite-abscissa period/support equivalences, `zeta_eventually_shift_eq_iff`, and `primitive_additive_period_trivial`. The exact canonical-source scratch `/tmp/hgt-iae-dirichlet-period-final.lean` exited 0 without warnings. All six declaration axiom lists contain only `propext`, `Classical.choice`, `Quot.sound`; source-verified coefficient-uniqueness, non-rationality and arithmetic-function extensionality probes passed. The successful preceding scratch had the same proof text. The import was appended once to `RHTower.lean`, preserving existing content. No heartbeat or recursion setting was changed, and no numerical experiment or decision computation appears in the new source. The result is a classical consequence of existing source theorems, not a mathematical novelty claim.

**Final targeted audit and whole-route status.** `LEAN_NUM_THREADS=1 lake build GaloisForLFunctions.RHTower.DirichletTranslationPeriod` exited 0, rebuilding only this leaf (32s; 8,845 target-graph jobs). Its umbrella import occurs once. `scripts/formal_tools.py lint` exited 1 solely for the existing unrelated `RHTower.Sieve.KloostermanGlobalCollisionCoprime` umbrella omission, with 159 large-file warnings. Source/scratch identity, source and own-document whitespace, forbidden declarations, unique import, and 102 unique research records were checked. Universal STATUS records the exact function-period obstruction without inferring anything about periodic patterns of zeros. All owned searches, scratch attempts, final build and lint commands are terminal; the final scan found no owned Lean process. No full build, heartbeat change, added axiom, numerical experiment, decision computation, commit or push. Source and logs use `/tmp/hgt-iae-dirichlet-period-`.

The completed result changes admission of this particular source construction, not the truth of RH: the direct ordinary-cusp map and its additive-primitive repair fail. The next useful step needs a different explicit arithmetic map together with its proved compatibility law. The five route gates remain open; do not treat the new auxiliary classification as a new proof route.
