# Corpus-wide search for an arithmetic proof architecture

- **ID:** RH-CORPUS-20260905
- **Stage:** 1-in-progress
- **Type:** CANDIDATE SEARCH; no RH implication or novelty claim established
- **Source:** `scripts/formal_tools.py research`; current frontier map; audited Lean declarations; primary literature.
- **Statement:** Find a source-derived operation whose exact arithmetic constraints can distinguish horizontal displacement without importing an RH-equivalent estimate or selecting the desired zeros in its definition.

**Current result: NO QUALIFYING NOVEL RH ARCHITECTURE VERIFIED.** The intended chain is a literal
arithmetic construction, a new relation forced by a zeta zero, and an independently proved
incompatibility of that relation with an off-line zero. The last two links remain missing.

The earlier multiplicative curvature is a proved source invariant, but its unrestricted
annihilation at zeros is false: the continued ordered charge is nonzero even at genuine
critical-line zeros. A proposed restriction to the strict right half-plane would still need
its own arithmetic proof. Finite endpoint closure, complete multiplicativity, compatible
attenuation, and linear completion have not supplied it. The later mixed-area rank proposal
is numerically disfavored, without a certified infinite counterexample. No successor has
passed both the source and novelty gates. The chronological account below retains earlier
conjectures for reference; their provisional wording does not supersede these outcomes.

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

- **Joint polygon arithmetic verified:** the literal coprime deletion polygon closes and every
  polynomial one-form of coefficient degree at most three integrates to zero. Nevertheless
  `integral x*y^3 dx=P(P-1)Q(Q-1)(Q-2)/120`; the moduli-2-and-3 value is `1/10`.
  Lean proves the general formula from the actual source, not an assigned scalar invariant.
  Standard polynomial-moment/signature machinery is published. Lean now constructs the actual
  two-and-three joint exponential product in every complete complex normed unital algebra for
  `Re(s)>1/5`, including every prefix and a unit limit. A fixed six-coordinate target has exact
  positive-real convergence boundary `1/5`; its actual varying-weight sharpness proof is closed.
  The zero-specific arithmetic relation remains missing. Convergence cannot select the critical line.
  [Exact construction, formal certificate, and ancestry audit](euler-deletion-joint-polygon-moment.md).

- **Adjacent nonperiodic digital extension rejected:** the published Thue–Morse two-column zeta
  identity loses its zeta term identically after centering. Its residual relation holds for every
  parameter in the convergence domain, so zero specialization creates no new arithmetic constraint.
  The exact relation is already published. [Source and cancellation audit](../5-failed/adjacent-digital-zeta-cancellation-audit.md).
- **Finite affine-pattern extension rejected:** even an arbitrary nonlinear rule on finitely many
  bits `[q_j divides a_j*n+c_j]`, with overlapping moduli and non-invertible slopes, remains a
  function of one finite residue class. Scratch Lean verifies its exact reduction to mathlib's
  existing periodic L-series/Hurwitz representation. This does not cover growing moduli or
  chronological infinite histories. [Conjecture, second pass, and verified reduction](../5-failed/affine-congruence-pattern-architecture-audit.md).
- **Source-scope correction:** `SmoothMultiplicativeDichotomy` compares named records with assigned
  rational exponents and contains assigned applicability flags. It does not prove that all methods
  fall into two exhausted families. Source comments and the exact downstream citations were
  corrected; no theorem body changed. Such bookkeeping must not exclude possible architectures.
  [Definitions, scope, and Lean validation](corpus-method-model-semantics-audit.md).
- Existing source/receiver boundaries forbid treating an RH equivalence as a producer.
- The earlier normalized rank-one theta sewing realization has zero tangent already at first order; it supplies no selective nonlinear obstruction. The arithmetic formal-deformation obstruction still lacks an independently constructed Xi-linked source satisfying its bounds.
- Existing working-tree changes predate this audit and are preserved.
- The literal Euler-deletion coefficient `a_q(n)=1-q[q∣n]` is already in the corpus. Its scalar Dirichlet series is only `(1-q^(1-s))ζ(s)`, so scalar combinations are forbidden as producers.
- Pointwise `2×3` fusion has zero block mass and an integer first moment, but that moment is origin-sensitive and trivial modulo the canonical period. This kills the first attempted carry-orientation detector.
- Multiplication-fibre stabilization passed its literal `2×3` test but failed the generic-mechanism and factorization gates. Corpus modules already contain the exact Jordan overlap `min(positive mass, negative mass)`, signed quotient loss, reserve fusion cocycle, abelian odometer, and product-sign decomposition. The proposed stabilized count is therefore a specialization of existing machinery; its expected Dirichlet series also factors through `ζ(s)^2`.
- The current survivor keeps chronological order rather than multiplication fibres. A modulus-`P` Euler-deletion block is the jump word `(1,…,1,1-P)`: level one is exactly `0`, while the quasi-shuffle bracket `Σ jump²` is `P(P-1)`. Replicating a nonzero quadratic source `P` times scales its bracket by `P`; Euler dilation scales it by `|P^(1-s)|²=P^(2-2 Re(s))`. Equality of these independently defined refinements forces `Re(s)=1/2`.
- The weighted deletion path has bounded coefficient partial sums and therefore converges for `Re(s)>0`. Exact finite dilation plus pole-cleared analytic uniqueness proves its sum is `(1-P^(1-s))ζ(s)` throughout that half-plane. Every positive-real-part zeta zero closes every deletion endpoint without functional equation, reflection, or completed zeta.
- For a hypothetical zero with `Re(rho)>1/2`, diagonal energy is finite and strictly positive. The finite quasi-shuffle identity forces the real chronological second prefix to converge to exactly `-energy/2`. This is a canonical nonzero shadow, but not refinement coherence.
- The uniform Abel tail estimate strengthens that shadow: every complex self level and every ordered cross-modulus level converges absolutely at such a zero. Their limits obey the exact polarized quasi-shuffle relation `H(P,Q)+conjugate(H(Q,P))+E(P,Q)=0`. This constructs the depth-two target without assigning it any sign or dilation coherence.
- Every nonempty finite product of pairwise-coprime deletion channels is an alternating sum of single channels: `prod_(P in B) a_P = sum_(empty != S subset B) (-1)^(|S|+1) a_(prod S)`. Its zero endpoint is derived from the original all-modulus closure, not stronger independent data. Lean now proves reverse reconstruction as well: the product-modulus channels and cylinder channels recover each other, as do all finite chronological words with arbitrary conjugation choices. Simultaneous zero endpoints are equivalent in the two presentations. Their absolute word-expansion coefficients have exact mass `prod_j (2^(|B_j|)-1)`; no uniform infinite-completion estimate follows from finite reconstruction alone.
- This closure is squarefree, not algebraic. Pointwise repetition obeys `a_P^2=(P-1)+(2-P)a_P`; in particular `a_2^2=1` and its first `N` unweighted square coefficients sum to `N`. The bounded-partial-sum Abel mechanism therefore leaves the source class as soon as one generator repeats.
- Centering does not repair this with new information: subtracting the constant square component leaves `(2-P)a_P`, and kills the dyadic square completely. Corpus interaction-cohomology and augmentation-ideal modules already contain the generic algebraic mechanism, so relabelling centering/Wick projection is not a new producer.
- Literal modulus composition is an exact interleaving, `source_(PQ)=source_P+insert_P(source_Q)`, but its two legs have strictly negative overlap throughout `Re(s)>1/2`. Composite energy is strictly below independent-copy energy. Therefore the natural arithmetic refinement does not realize QSR's replication premise.
- For coprime `P,Q`, the inserted coefficient has the exact squarefree grading
  `insert_P(a_Q)=a_Q-a_Pa_Q`. On one common `PQ` block, grade one and grade two are uniformly
  orthogonal; their Pythagorean splitting gives insertion energy exactly `P` times dense
  `Q`-channel energy. Thus the desired arithmetic replication factor exists before Mellin weighting,
  without independent copies.
- Mellin weighting does not preserve that grading. For every `alpha>1`, the grade-one/grade-two
  Dirichlet cross term is explicitly
  `Z(alpha)(1-P P^(-alpha))(1+Q(Q-2)Q^(-alpha))`, hence strictly positive for coprime
  `P,Q>1`. Literal weighted interference is therefore not a static boundary in the convergent
  chamber.
- Exact weight recovery followed by arithmetic averaging makes interference vanish and returns
  factor `P` for every complex exponent. This proves that uniform-mean or unweighted associated
  grading cannot select the critical exponent; retaining the Mellin deformation is mandatory.
- Noncommutative ordered exponential development exists for every deletion channel on `Re(s)>0`. Its commutative shadow is exactly the exponential of the mapped scalar deletion prefix, hence equals the unit at every positive-half-plane zeta zero. Any remaining information must live beyond commutative observation; ordinary scalar or commutative development is exhausted.
- A concurrent corpus module, `EulerDeletionDirichletGram.lean`, computes the absolutely convergent source Gram law and coprime centered orthogonality. This confirms that pointwise covariance is standard `lcm` arithmetic; it cannot replace chronological carry or supply QSR.

## Transfer gate after the joint-product theorem

The completed two-modulus product and its exact one-fifth boundary establish an arithmetic
object with higher interaction information. They do not establish a relation forced by a zeta
zero. A usable successor must specify that relation on the literal weighted object and prove
it from zero data; an abstract theorem accepting the desired relation as a hypothesis does
not supply the missing step.

Three further corpus mechanisms were checked in their definitions and proof bodies:

- `ConstitutiveCentralAdmissionExchange.compensatorAdmitted_iff_carrierClosed` equates closure
  under a corrected operation with the correction lying in a supplied quotient kernel.
  `admittedPromotedBinary_associative_of_ambient` explicitly requires that admission hypothesis.
  The module's integer/parity countermodel shows ambient associativity does not provide it.
  Applying this result to the arithmetic curvature still requires constructing and proving the
  zero-defined admission map; no such map is obtained from the product convergence theorem.
- `Octonion.CayleySecondaryObstruction` inserts an arbitrary real `grade` in an explicit
  two-by-two matrix, then detects that same grade in a higher obstruction. Its vanishing
  equivalence is verified, but contains no arithmetic producer for the grade and no zero-forced
  extension theorem. Relabelling an off-line displacement as this grade supplies neither.
- `TateFractureObstructionBianchiAmplitudeLaw` proves that a literally supported bigraded
  family has no components beyond its support width. `BundledHasVerticalAmplitude` means
  every type outside a finite vertical interval is a subsingleton. It is not a norm bound or
  an analytic convergence statement. The new Banach-algebra product cannot be fed into that
  theorem as finite support without a separate arithmetic construction and proof.

These are scope audits of possible transfers, not exclusions of their whole mathematical
families. None supplies the missing zero-forced relation. Additional searches for scissors,
Dehn, Fox derivative, and conjugacy-reconstruction mechanisms returned no own-tree matches;
those misses establish no novelty or impossibility claim.

## Open obligations

**Finite endpoint-to-curvature inference falsified:** `EulerDeletionBalancedPeriodFreedom` proves
that the apparent cubic coefficient is exactly
`k=(Q-1)(a_(PQ)-a_Q+R(a_(QR)-a_(PQR)))`. Its single-weight sum is therefore controlled by the
original endpoints; its squared-weight sum is a different observation. On the literal integers
`1,...,60`, two strictly positive weight assignments keep every divisor-of-30 deletion endpoint
zero but give quadratic `2×3×5` curvature `+3` and `-3`. The general positive survivor is exact:
opposite weight perturbations on two copies preserve every periodic linear observation and change
the quadratic observation by `2 sum f h^2`. This rejects a finite algebraic annihilation inference,
not a theorem using the actual infinite Mellin weights. The extra property distinguishing those
weights must be stated and proved. [Proof, countermodels, corpus audit, and Lean certificate](../3-formalized/euler-deletion-balanced-period-freedom.md).

**Complete multiplicativity does not repair that finite inference.** The new
`EulerDeletionPairedPrimeFreedom` constructs global strictly positive completely multiplicative
weights with every divisor-of-thirty deletion endpoint zero through 930, yet quadratic
curvature `-72` or `3`. The negative example changes only prime values 59 and 61; the positive
example changes 251 and 257. Their multiples have matched cofactor cutoffs. The strongest
positive survivor classifies every scalar observation `F`: its weighted sum is the baseline
times `F(1)`, plus a shorter coefficient sum times
`F(1+t)+F(1-t)-2F(1)`. This identity and the unconditional countermodels are Lean-closed;
the exploratory Runpod matrices are not proof certificates. The actual infinite Mellin
weights still require an additional source-specific relation.
[Proof and validation](../3-formalized/euler-deletion-paired-prime-freedom.md).

**The proposed infinite prime-perturbation extension fails its admission gate.** For the literal
global coefficients `b(n)=c^(v_p(n))`, the exact digit remainder
`R(N)=(p-c)*sum_(n<=N)b(n)-(p-1)*N` lies in `[0,p-1]`. A deletion multiplier `ell` gives
bounded coefficient prefixes exactly when `ell*c=p`, and the repaired prefix is exactly
`N mod p-R(floor(N/p))`. For `0<=c<1`, retaining the original multiplier `p` leaves a
positive harmonic drift and excludes ordinary Dirichlet convergence at every `Re(s)<1`.
The repaired multiplier recovers convergence throughout `Re(s)>0`. Thus preserving an
analytic zero divisor under an Euler-factor quotient does not preserve the original
conditionally convergent source. This is a proved domain distinction, not a new RH mechanism.
[Exact source proof and certificate](../3-formalized/euler-deletion-prime-attenuation-admission.md).

**Compatible attenuation also fails to change the curvature obstruction.** With actual
coefficients `A_d(n)=1-(d/b(d))*[d|n]` and mass `b(n)^2*n^(-alpha)`, Lean proves the exact
four-channel factorization for positive contractive completely multiplicative `b`. Its final
factor remains `1-r^(2-alpha)`: the changed coefficient cancels the attenuation at the third
label. The curvature stays strictly negative on `1<alpha<2`, vanishes exactly at two, and is
strictly positive above two. If `b(p)=b(q)=1`, curvature divided by its actual total mass is
identical to the original normalized curvature. This includes all `c^(v_5(n))`, `0<c<=1`,
with the compatible `2,3,5` coefficients. This is an exact positive invariant of the failed
repair, not a zero-forced identity or an RH architecture. General ordinary admission is not
claimed for arbitrary `b`. [Proof and certificate](../3-formalized/euler-deletion-compatible-curvature.md).

**Complete finite static audit:** every real function of finitely many positive pairwise-coprime divisibility bits has exactly the product-distribution expectation with one-coordinate probabilities `p^(-alpha)`, under the actual normalized Dirichlet weight for `alpha>1`. Lean now proves the full atom law, arbitrary-observable formula, summability, and vanishing of all nonempty centered products. This mechanism is published zeta-distribution independence: Golomb (1970), and Cranston–Peltzer, equations (5)–(9). It supplies no unexplained higher static coupling. Chronological dependence is outside the theorem, not established as a new mechanism by eliminating static alternatives. Proof and precise scope: [finite-statistic classification](../3-formalized/euler-deletion-finite-statistic-law.md).

**Linear completion is also a classical identification.** The literal deletion prefix is
`N mod p=p*fract(N/p)`. `EulerDeletionLinearSpanAudit` proves the exact source dictionary,
finite-combination coefficient change, both span inclusions, equality of closures in any
fixed topology on the sequence carrier, and the tail-cell identity with the actual
Báez-Duarte generator. The weighted sequence formulation is published in Bagchi (2005),
Theorem 1. Growing the modulus family and nonzero scalar reweighting therefore do not make
this linear approximation problem new. No new positive architectural salvage was found in
that completion; the exact dictionary is audit evidence, not a claimed novel theorem.
[Formal identification and primary sources](../3-formalized/euler-deletion-linear-span-audit.md).

**Other source candidates inspected in the same broad search do not supply the missing law.**
`FormationPotentialCriterion.riemannHypothesis_tfae_divisibleLift` explicitly leaves an
RH-equivalent global lift/potential condition. `InvolutiveProjectiveWedgeTransportLaw`
requires the logarithmic jet to factor through the proposed quotient. Those conclusions
cannot be imported without proving their source hypotheses. `HighExponentShellHypertranscendence`
does retain a positive coefficient partition and joint differential independence, but the
actual shell parent proves `S_m(s)=zeta(s)*(1/zeta((m+1)s)-1/zeta(ms))`. For `m>=12` its
multiplier is analytic and nonzero throughout the strict right half-plane, so its zero
divisor is exactly the old zeta divisor. Finite differential independence is therefore
compatible with the same common zero information; it does not supply the missing new
constraint. The shell route was not adopted. Search hits using spectral, theta, Gamma,
Möbius, or other excluded mechanisms were not used as candidates.

**Holomorphic mixed-area rank gate is computationally disfavored.** The literal four-channel
area for moduli 2,3,5,7 was tested at approximate zeta zeros 1,2,5 on the specified Runpod.
Its Pfaffian remains substantially nonzero through cutoff 860,160, with independent recurrence
and precision checks. This is numerical evidence against zero-forced decomposability, not a
formal counterexample. Endpoint Pluecker identities, scalar rescaling, unweighted coprime-word
cancellation, and the existing four-wedge dilation identity supply no repair. A second pass
found no new positive survivor. The general Pfaffian/iterated-integral representation is itself
published mathematics; it cannot be promoted as a new RH mechanism.
[Candidate, exact limits, primary sources, and computation artifacts](euler-deletion-mixed-area-rank.md).

**A false class-level barrier was corrected.** `no_polynomial_surgery` excludes the specified
multiplier `P(s)G(s)`; it does not exclude all finite divisor changes with an extra nonvanishing
factor. The current prescribed-divisor Helson theorem gives a premise-free Lean instance with
unimodular completely multiplicative coefficients and continued divisor exactly one simple
zero at `3/4+i`. Source comments and every direct downstream citation that broadened the
polynomial theorem were corrected. This uses published mathematics to repair the research
map; it is not a new RH architecture. [Verified scope audit](dirichlet-polynomial-surgery-scope-audit.md).

**Exact finite zeta coefficients do not remove that freedom.** For every cutoff, the new
premise-free `HelsonFinitePrefixDivisor.finite_prefix_singleton_divisor` constructs globally
completely multiplicative unit-modulus coefficients equal to one through that cutoff. Their
ordinary Dirichlet series admits meromorphic continuation with just the simple divisor at
`3/4+i` in the positive half-plane. A finite Euler correction fixes the initial prime values
and is analytic and nonzero throughout that half-plane. The witness may change with the cutoff;
no functional equation, full literal coefficient identity, or analytic tail control is assumed.
This is a formalized consequence of published Helson flexibility, not a new proof architecture.
[Paper construction, precise quantifiers, and validation](../3-formalized/not_new_scientific_knowledge/helson-finite-prefix-zero-freedom.md).

**Positive coefficients and weighted convergence still do not control continuation limits.**
`PrimeTailTranslation.positive_zero_free_tail_approximation` gives strictly positive bounded
completely multiplicative coefficients, exact zeta prefixes of every prescribed length, and
convergence to all-one coefficients in every weighted square distance with exponent `sigma>1/2`.
Their ordinary series continue to analytic zero-free functions on `Re(s)>0`, yet fail to
converge to zeta at every real point of `(0,1)`. The sign difference at these nonzero values
proves failure of the limit; zero-freeness alone would not. This is a classical shifted-Euler
audit witness, not a qualifying successor. The capstone and all 26 public theorems passed
the imported axiom audit; direct checking, the serialized leaf build, and formal lint passed.
[Exact construction, proof, ancestry, and limits](../3-formalized/not_new_scientific_knowledge/positive-prime-tail-translation.md).

**Prime-factor relabelling does not produce a new scalar zero relation.** A further
[30-query discovery pass](rh-corpus-architecture-audit-2026-09-06-prime-permutation-searches.tsv)
checked exact deformation, sparse prime encodings, coupled prime profiles, and prime-word
constructions before testing actual prime-factor permutations. Unique factorization extends
each such permutation to a multiplicative positive-integer bijection. Its norm-summable scalar
series is exactly zeta on `Re(s)>1`, so comparing two scalar continuations adds no zero-specific
identity. A second pass retains the finite boundary: only entering and exiting integers remain,
and composition necessarily transports the cutoff. These exact positive identities are classical
and closed in Lean; no zero-forced boundary law or qualifying architecture follows.
[Source definitions, complete scope, and no-go closure](../5-failed/prime-permutation-scalar-source-audit.md).

No RH-producing theorem has passed the gates. In particular, a generic zero-closure argument
cannot be used to annihilate the old multiplicative curvature: the corpus already proves
`DeletionCriticalCurvature.not_global_zero_curvature_annihilation`. A strict-right-only
replacement has no source proof here. The continuing objective is to construct and test a
different zero-forced relation, not to treat this missing condition as established or novel.

**All-depth finite-period audit:** every nonempty unweighted chronological word with positive pairwise-coprime labels has an exactly periodic prefix and is zero at complete product periods, even with independent phase shifts of the letters. The proof works for arbitrary zero-mean periodic sources. Thus complete-period observations on disjoint prime supports cannot produce a nonzero class; weighted within-period variation and overlapping supports remain separate obligations. This reinforces the need to retain weighting, but supplies no zero-specific transgression. Exact statement, proof, and Lean evidence: [coprime-word periodicity](../3-formalized/euler-deletion-coprime-word-periodicity.md).

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

The finite cell alone does not establish that the retained count escapes scalar arithmetic. For the cofinal rectangular grid, every fixed positive product `k` contains all divisor pairs once both cutoffs reach `k`. Let `C(k)` be their signed sum, `A(k)` their total absolute source mass, and `O(k)` the number of opposite-sign unit pairs cancelled. Lean now proves the exact classification

`2 O(k) = A(k) - |C(k)|`.

For the literal `2,3` deletion source, put `D_r(k) = d(k/r)` when `r` divides `k`, and zero otherwise, where `d` counts positive divisors. The stronger identity is also closed in Lean for every natural `k`:

`O = D_2 + D_3 - D_4 - D_9 - D_6 + D_12 + 2 D_18 - 2 D_36`.

The direct paper corollary on the absolute-convergence half-plane is

`[x+y-x^2-y^2-xy+x^2 y+2xy^2-2x^2 y^2] zeta(s)^2`,

with `x=2^(-s)`, `y=3^(-s)`. That fails the candidate's factorization gate for the specified count. `RHTower.CoprimeFiberStabilization.coprimeFiberStabilization_closed` proves the coefficient identity, the signed/absolute mass law, and rectangular stabilization unconditionally. The strongest positive survivor and full proof are recorded in `3-formalized/coprime-fibre-stabilization-collapse.md`. This does not classify arbitrary labelled histories or an unspecified infinite-modulus construction. No further multiplication-fibre scan is a priority.

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

The first attempt to promote the source to a pointwise cylinder algebra is false. Direct finite
arithmetic gives

`a_P(n)^2=(P-1)+(2-P)a_P(n)`.

Thus repetition creates a constant channel. At `P=2`, `a_2(n)^2=1` pointwise and the length-`N`
coefficient prefix is exactly `N`, so the bounded-prefix Abel admission used by the deletion paths
is lost. The surviving input category is only squarefree multilinear in pairwise-coprime moduli.

**C7: source-fixed centering repairs the failed cylinder algebra and supplies a new quadratic
class. Rejected.** The exact centered square is only
`a_P²-(P-1)=(2-P)a_P`; at `P=2` it is zero. Centering either recycles the level-one channel or
erases the dyadic quadratic source. The corpus already owns generic centered-covariance,
augmentation-ideal, Walsh, and finite interaction-cohomology machinery. Positive survivor:
squarefree mixed products retain genuine marginal-invisible interaction directions.

**C8: literal composite deletion realizes QSR's independent replication. Rejected.** The actual
coefficient source has exact interleaving
`source_(PQ)=source_P+insert_P(source_Q)`, where the inserted leg carries Euler amplitude. Its
cross term is strictly negative throughout the doubled-abscissa chamber, and composite energy is
strictly smaller than independent energy. Positive survivor: exact source interference is now a
mandatory correction term rather than an ignored error.

**C9: static factorization-graded quasi-shuffle descent. Rejected.** For coprime `P,Q`, define

`I_(P,Q)=a_Q-a_Pa_Q`.

This is not an invented quotient: Lean proves that it is the literal inserted `Q` deletion source
on the common clock. Uniform counting on one product block makes `a_Q` orthogonal to `a_Pa_Q`,
and gives

`energy_uniform(I_(P,Q)) = P energy_uniform(a_Q)`.

That initially supplied the missing arithmetic replication factor. It does not select an exponent.
The corpus's exact mean-descent calculation strips the prescribed Mellin weight, averages the
remaining coefficient energy, and obtains the same factor `P` for every complex `s`. The exponent
terms cancel as `P^(2-2sigma) P^(2sigma) / P=P`. Conversely, retaining the actual Dirichlet weight
makes the grade cross term strictly positive throughout `alpha=2sigma>1`; it is not a boundary.

- **Exact killing mechanism:** unweighted/mean grading is exponent-blind; weighted grading is not
  orthogonal.
- **Strongest positive survivor:** literal insertion has an exact squarefree Pythagorean grading
  and an explicit positive Mellin deformation defect.
- **New insight:** the relevant unknown cannot be a static quotient. It must be a zero-specific
  chronological chain law that retains, then cancels, the weighted defect.
- **Status:** finite grading and Mellin defect formalized; no RH consequence.

**C10: nested cofactor-cutoff associator. Rejected.** Generic cofactor insertion is an exact
multiplicative action, `I_P I_Q=I_(PQ)=I_Q I_P`, and its scalar cutoffs satisfy
`floor(floor(N/P)/Q)=floor(floor(N/Q)/P)=floor(N/(PQ))`. Thus neither factor order nor nested
one-dimensional floors carry a transgression before chronological summation. The strongest positive
survivor is a sharper localization: only strict multi-index order regions such as `Pm<Qn`, together
with conditional grouping, can still distinguish schedules. The corpus's general floor-transform
composition theorem confirms the same flatness at the transform level.

**C11: two-index strict-schedule annihilation. Rejected.** The two complementary strict order
regions and their diagonal are already the polarized quasi-shuffle identity. At a simultaneous
zero, endpoint closure gives

`forward(P,Q)+conjugate(reverse(Q,P))=-weighted_diagonal(P,Q)`.

For the singleton/interaction grade pair, that diagonal is the strictly positive defect from C9,
so the natural schedule symmetrization is nonzero rather than annihilated. The strongest positive
survivor is that the Mellin defect is a literal diagonal boundary between the two schedules. A
selector must operate at depth at least three and detect a conditional grouping anomaly not forced
by ordinary quasi-shuffle associativity.

**C12: ordinary additive depth-three associator. Rejected; multiplicative curvature survives.** For
the finite same-clock weighted pairing `B_alpha,N(x,y)=sum_(n<N)x(n)y(n)n^(-alpha)`, bilinearity
forces

`B(x,y)+B(x+y,z)-B(y,z)-B(x,y+z)=0`.

The corpus promotion-associator and central-admission laws predict the same flatness for every
bilinear carry. The pivot is to rebracket the *modulus multiplication* inside the already proved
Mellin grade defect `D`, not source addition. For pairwise-coprime `P,Q,R`, direct expansion gives

`K_alpha(P,Q,R)=Z(alpha)(Q Q^(-alpha))(1-P P^(-alpha))(Q-1)(1-R^(2-alpha))`.

This is strictly negative on the full convergence chamber relevant to a right-half zero,
`alpha=2 Re(rho) in (1,2)`. The strongest survivor is an exact, source-specific multiplicative
curvature with a complete sign classification. It does not yet constrain zeros: endpoint closure
has not been shown to annihilate `K`. Status: formalized, live only through that kill gate.

The most direct coherence interpretation was then tested and rejected. On `Nat × Real`, define

`(P,a) star_alpha (Q,b)=(PQ,a+b+D_alpha(P,Q))`.

The second-coordinate associator of `star_alpha` is exactly `K_alpha(P,Q,R)`, so `star_alpha` is
provably nonassociative for `1<alpha<2`. Associativity of the base modulus product therefore does
not make the defect-graded lift associative. Any successful zero argument needs a separately
constructed quotient or observation that kills `K` on the zero fibre.

### Provisional successor: multiplicative factorization-curvature transgression

1. Treat every periodic deletion `a_P(n)=1-P[P∣n]` as a deterministic chronological path and keep
   its diagonal quasi-shuffle bracket.
2. Use the exact squarefree factorization
   `insert_P(a_Q)=a_Q-a_Pa_Q`. This defines grade-one and grade-two source pieces without repeated
   generators or independent copies.
3. Use uniform product-block orthogonality only as the undeformed reference form. Mellin weighting
   deforms it by the proved cross term
   `D_(P,Q)(alpha)=Z(alpha)(1-P P^(-alpha))(1+Q(Q-2)Q^(-alpha))`, positive for
   `alpha>1` and `P,Q>1`.
4. Rebracket modulus multiplication inside `D`, obtaining the source-defined curvature
   `K_alpha(P,Q,R)=D(P,Q)+D(PQ,R)-D(Q,R)-D(P,QR)` before choosing any zero.
5. Use the proved formula and sign law: `K_alpha<0` for `1<alpha<2`, `K_alpha=0` iff `alpha=2`, and
   `K_alpha>0` for `alpha>2`, under pairwise coprimality and nontrivial moduli.
6. At a hypothetical zero `rho` with `Re(rho)>1/2`, construct a chronological three-channel object
   whose two factorization-tree boundary evaluations differ by `K_(2 Re(rho))`.
7. Prove **MDFGT-1d:** simultaneous squarefree endpoint closure makes those two evaluations equal.
   The proved strict negativity would then exclude every right-half critical-strip zero.
8. Reject immediately if equality is assumed from associativity, if additive bilinearity makes the
   boundary zero before modulus composition, or if a conditional rearrangement is left unproved.

### Live falsification gates

- **Endpoint gate:** a closed path may have nontrivial signature. Level-one closure alone does not imply QSR; making that inference retires the route.
- **Balance gate:** QSR must follow from all-modulus arithmetic compatibility. Assuming equality of the two quadratic scales is exactly assuming the desired exponent in disguise.
- **Renormalization gate:** infinite iterated sums must receive a canonical, cofinal definition independent of cutoff schedule. An adaptive subtraction depending on `ρ` is forbidden.
- **Non-`L²` gate:** square summability at `σ>1/2` is only the domain where the level-two object can exist. It is not a contradiction and cannot serve as the producer.
- **Source gate:** modulus system, chronological refinement, and bracket must be fixed before the zero. No functional equation, `1-s`, Γ, θ, spectral operator, Möbius inversion, or Weil positivity may enter QSR.
- **Repetition gate:** the source cannot silently use a unital pointwise algebra. Repeated generators create the constant stream; admitting it through zeta continuation would move analytic continuation into the producer and make the source-first claim false.
- **Interference gate:** literal modulus composition is not orthogonal replication. Any descent must reproduce the exact negative overlap and prove it becomes a boundary in the chosen associated grade; deleting it assumes the desired refinement.
- **Static-grade gate:** uniform block orthogonality and recovered coefficient means hold for every
  exponent. They cannot select `1/2`. The decisive equation must retain the original Mellin weight.
- **Weighted-defect gate:** the actual grade-one/grade-two Dirichlet cross term is strictly positive
  for `Re(s)>1/2`. Calling it a coboundary is insufficient; a constructed chronological boundary
  map and a separately proved zero-closure annihilation theorem are required.
- **Abelian-shadow gate:** commutative ordered-exponential development is exactly the exponential of level one and becomes the unit at every zero. A useful lift must retain quasi-shuffle diagonal variation, not merely rename an abelian or ordinary Magnus invariant.
- **Novelty gate:** iterated-sums/quasi-shuffle signatures and tree-like signature theory are published mathematics. Double-shuffle and distribution relations for Euler sums are also published: Zhao, [arXiv:0705.2267](https://arxiv.org/abs/0705.2267), and Guo--Paycha--Xie--Zhang, [arXiv:0906.0092](https://arxiv.org/abs/0906.0092). More directly, the literal ordered periodic-coefficient double series fits Kelliher–Masri, [equation (1.4) and §9.2](https://math.ucr.edu/~kelliher/papers/LFunctionsFull.pdf). Magnus expansion is standard [arXiv:0810.5488](https://arxiv.org/abs/0810.5488), and an unrelated abelian-holonomy RH proposal already exists [arXiv:1005.4299](https://arxiv.org/abs/1005.4299); generic “noncommutative” or “holonomy” language cannot support novelty. The analytic objects and generic machinery are therefore not new. Any novelty would have to reside in the exact source-derived Euler-deletion factorization-grade descent law, which has not been constructed. Exact-phrase search misses do not establish it.
- **Nearby-corpus gate:** `EulerSquarefreeWickQuadraticCommonRefinementDescent` is a `2×2` reflection descent whose target already carries a half-density and whose all-zero statement is RH-equivalent; `CycleDeletionShiftedHankelRankOneUniversalityLaw` is shape-blind shifted-Hankel rank one. Both violate scope and neither contains chronological deletion-word scaling. Do not import their “common refinement” vocabulary or results into QSR.

### Current conjecture ladder

- **QSR-0 — proved:** every finite deletion block has zero level one and bracket `P(P-1)`.
- **QSR-1 — proved:** finite Hermitian quasi-shuffle identity, exact concatenation cross term, closed-source replication law, amplitude-scaling law, and the actual deletion-word specialization. Chronological second-level coherence at a nonzero deletion word forces `σ=1/2`.
- **QSR-2 — proved for the real shadow:** exact finite prefixes, conditional convergence on `Re(s)>0`, finite Euler-dilation identity, pole-cleared zero landing, square summability on `Re(s)>1/2`, and convergence of the real chronological second level at a zero to the strictly negative value `-energy/2`.
- **QSR-2.5 — proved for the grouped ordered dilation expression:** at a right-half zeta zero, full complex self and cross levels converge absolutely and satisfy polarized quasi-shuffle. More generally, chronological cross cutoffs converge without any zero assumption when both exponent real parts are positive and their sum exceeds one. The exact finite four-wedge Euler-dilation formula retains every strict floor boundary, and its complete grouped expression has the same limit. Separate limits of its four terms are neither asserted nor needed. Proof: `EulerDeletionQuasiShuffleCrossDomain` and `EulerDeletionQuasiShuffleOrderedDilation`.
- **QSR-3 — partially proved and sharply delimited:** all nonempty finite pairwise-coprime squarefree cylinder products close. Repeated-generator closure fails already at `a_2^2=1`. Constructing cofinal refinement maps that never require repetition, yet derive a nontrivial replication--dilation identification before continuation, remains open.
- **QSR-3.5 — failed for both obvious repairs:** centering collapses squares to old channels, while literal composite interleaving has strictly destructive interference and is not independent replication.
- **FGQD-0 — proved:** commutative development collapses to the unit at every zero.
- **FGQD-1 — proved, then rejected as producer:** literal insertion is grade one minus squarefree
  grade two; uniform grades are orthogonal and insertion energy has factor `P`. Exact unweighting
  recovers this for every exponent, so static factorization grading is selection-blind.
- **MDFGT-0 — proved:** actual Mellin weighting creates an explicit strictly positive cross-grade
  defect throughout `Re(s)>1/2`.
- **MDFGT-1a — rejected:** cofactor insertion and nested scalar floor cutoffs commute exactly, so
  they have no factorization-order associator.
- **MDFGT-1b — rejected at depth two:** complementary strict regions plus their diagonal are exactly
  polarized quasi-shuffle. Zero closure identifies their symmetrization with the negative nonzero
  weighted defect; it does not annihilate it.
- **MDFGT-1c — partially proved and pivoted:** every additive factorization-tree associator built
  only from the same-clock weighted pairing is zero. Rebracketing modulus multiplication inside the
  defect instead produces exact curvature `K_alpha`, negative for `1<alpha<2`, zero exactly at `2`,
  and positive above `2`.
- **MDFGT-1d — next kill gate:** construct a three-channel chronological realization whose two
  factorization-tree boundaries differ by `K_(2 Re(rho))`, and prove zero closure makes them equal.
  If equality requires factorization-order invariance as a premise, retire the architecture.
- **MDFGT-1e — rejected as an automatic bridge:** central extension by `D_alpha` has associator
  exactly `K_alpha` and is nonassociative on `1<alpha<2`. Associativity of ordinary modulus
  multiplication supplies no equality after the defect coordinate is added.
- **MDFGT-2 — later:** extend a successful right-half exclusion to a complete RH argument without
  importing a banned classical route. No such extension is claimed.

### Producer pivot: Euler-deletion cylinder-signature pro-system

The finite-enrichment audit is closed in `EulerDeletionCylinderReconstruction`: the cylinder and
product-modulus source charts mutually reconstruct every finite ordered observable, including
Hermitian words. This retires the claim that adjoining finite cylinders provides independent
source information. It does not rule out proving a new theorem using that presentation, or a new
completion with additional control. Paper proof, exact coefficient cost, and scope:
`3-formalized/euler-deletion-cylinder-reconstruction.md`. The successor must supply an actual new
operation and a proved law; changing the finite chart does not supply either.

The full cross-level sum with exponents `s,t` is now Lean-proved to converge on `Re(s)>0`, `Re(t)>0`, `Re(s)+Re(t)>1`, without a zero endpoint. Bounded weighted inner prefixes and summable increments of their product with the outer Dirichlet kernel prove this domain theorem. Exact deletion of the two coordinates gives four ordered wedges with inner cutoff `floor((qn-1)/p)`; their grouped combination agrees with the chronological prefix for every cutoff and converges on the same domain. These are source-construction theorems, not zero-location producers. Paper proof and precise limits are in `3-formalized/euler-deletion-cross-domain-and-ordered-dilation.md`.

The naive version is false as a producer. Pointwise deletion operators commute, and expanding every
term in a commuting square only proves a tautology. Closed endpoints also do not determine second
levels: the closed words `(1,-1)` and `(2,-2)` have distinct chronological second values, now
formalized in `closed_endpoint_does_not_determine_chronologicalSecond`.

The proposed analytic-continuation holonomy is rejected. If chronological/stuffle and
Euler-dilation/distribution formulae agree on their common absolute-convergence region and both are
analytic continuations on one connected domain, identity uniqueness makes them equal for every
`s`. Their lattice-wedge boundary formula may be useful, but cannot become a zero-specific
constraint. A discrepancy would mean that at least one construction is not a continuation of the
same function.

The source base is the finite squarefree multilinear coprime-cylinder system generated by
the literal deletion coefficients. Lean proves the full finite-degree formula: every squarefree
product is the alternating sum of single deletion channels over nonempty products of pairwise-
coprime moduli, and every such path closes at a positive-half-plane zeta zero. Lean also proves why
this cannot be called a pointwise algebra: `a_P^2=(P-1)+(2-P)a_P`, with `a_2^2=1` and linear square
prefix growth. All surviving operations and common cutoffs exist before choosing a zero. The
required new object is a cofinal signature refinement functor on this squarefree system whose
finite product identities force, rather than assume, one nonzero replication--dilation equality
without ever multiplying a generator by itself.

The first natural functor is now rejected. Literal composite deletion is not independent
replication: its inserted Euler-dilated leg has strictly negative overlap with the base leg, and
their energy includes that exact correction. Centering the pointwise product is also terminal,
because its square is only a scalar multiple of the original deletion channel and the dyadic
centered square vanishes.

Static factorization grading is now constructed and rejected as producer. Literal insertion is
exactly grade one minus squarefree grade two; the grades are orthogonal in the uniform product-block
form and yield factor `P`. But weight recovery makes this law true for every exponent, while the
actual Dirichlet form has a strictly positive grade-mixing defect on `Re(s)>1/2`. The provisional
successor must therefore retain the Mellin weight and construct a chronological transgression whose
boundary is that explicit defect. Generic Magnus, Chen-signature, bar, augmentation, Walsh, and
interaction-cohomology machinery is known and already present in the corpus; novelty could only
lie in a source-derived zero-annihilation law for this exact weighted defect. The first higher
candidate is now concrete: additive pairing associators are flat, but modulus multiplication leaves
the exact signed curvature `K_alpha`. Nonzero curvature alone is not a contradiction; the route now
lives or dies on an independent zero-fibre annihilation theorem.

Two tempting substitutes are already rejected. The corpus reset-and-carry tomography has
order-dependent intermediate states, but its iterated prime differences depend only on the final
winning face, so its higher source closure is flat. Standard analytic continuation is also flat by
uniqueness. Numerical scans retire universal sign and universal vanishing: self and cross carries
take both signs at known zeros, and no cross-modulus logarithmic drift was observed. The next cycle
must construct or kill MDFGT-1d: a zero-fibre chronological realization of multiplicative curvature.
Scalar insertion, nested floors, additive bilinear associators, and depth-two strict schedules are
proved flat or tautological. Ordinary quasi-shuffle associativity cannot supply the needed equality.

## Rejected proposal: ordered unequal-time lattice responses

Retain independent integration times, parity sectors, and integer labels in products of the *fixed* theta source's causal/anti-causal responses. Apply lattice reindexing before integrating or projecting to a single source channel. The new research object would be the resulting hierarchy of ordered, coupled-lattice response integrals. It differs from changing normalized rank-one theta amplitudes, and from assuming products stay in the original one-source equation.

The proposed residual operation was never constructed. Its ancestry and intended starting point violate the user's scope. Do not treat the absence of a literal search match for the combined description as novelty.

## Discrete and exact-algebra audit after the correction

| Seed | Exact evidence inspected | Assessment |
|---|---|---|
| Controlled arithmetic deformation | `HTGeometry/ArithmeticSecondOrderObstruction.lean`, lines 1–170: a Leibniz map with a bilinear second-order primitive whose additive defect has a proved linear bound has zero bilinear source; reduced-algebra formal deformations with controlled even coefficients are constant. | The generic rigidity theorem is present. No zero-derived arithmetic primitive with the required bound was constructed. Assuming that bound would leave the producer open. |
| Free observed histories | `HTGeometry/FreeObservedTwoField.lean`, lines 180–285: every global boundary or observation defect reconstructs from primitive generator defects. Extension theorems take compatible generator assignments as input. | A free construction transports supplied source identities; it does not manufacture their compatibility. No qualifying arithmetic generator assignment was found. |
| Literal integer carry execution | `QuantumAlg/Primitives/Arithmetic/PlainAdder/Schedule.lean`, lines 2860–2935: natural addition carries satisfy exact shifted-addend and bit identities, with the source explicitly attributed to VBE carry circuits. | Supplies a verified integer execution law, not a new mathematical object or a zero-location law. No source-derived bridge to a zeta zero was constructed. |
| Word rewriting | `HTGeometry/ConstitutiveCriticalCompletionMechanics.lean`, lines 1–215: each rule decreases the number of `a` letters; each finite rulebook has an explicit nonjoining critical pair; the next joining rule is already an old semantic equality. | Separates execution from equivalence. No literal integer-arithmetic construction or RH consequence. Repeating this toy is not a new architecture. |
| Sequential repair | `HTGeometry/ConstitutiveSequentialRepairHeredity.lean`, lines 1–210: Arens topology has two sequential-closure layers while ordinary closure is stationary. | Known topological mechanism. No arithmetic realization selected. |
| Primitive execution | `HTGeometry/ConstitutivePrimitiveExecutionGenesis.lean`, lines 1–200: positive locally admitted laws decompose by induction on degree; bounded grammar completeness is equivalent to a bound on indecomposable degrees. | Exact abstract resource theorem. The required arithmetic family and its primitive structure were not constructed. |
| Carry identities | `research` plus `rg` in `ConstraintFrameRelativity/WittCarryBoolean.lean`, `ConstitutiveExchangeCentralPromotion.lean`, and `ConstitutiveCoefficientLiftTransgression.lean`. The inspected Boolean carry is intersection; the integer identity separates a squared gcd factor. | Neither Boolean addition nor a central carry can silently stand for the full addition/multiplication of integers. No qualifying synthesis produced. |
| Multiplication fibres | `RHTower/Sieve/FiniteFiberPartition.lean` and `MollifiedTwistedDiagonalProductEnergy.lean` provide generic fibre counts and product-coefficient square energies; `HTGeometry/ConstitutiveTVConflictColoring.lean`, `SignedCancellationQuotient.lean`, `ConstitutiveCausalJordanFormation.lean`, and `AbelianRepairLeastAction.lean` provide exact overlap, quotient loss, reserve cocycle, and odometer semantics. | Retired. Source-separated cancellation is already generic corpus machinery; expected cofinal count factors through `ζ²`. Literal `2×3` no-go/positive certificate retained. |
| Deletion cylinder/signature refinement | Corpus queries for rough paths, iterated sums, profinite cylinder density, congruence separation, path dilation, double-series distribution, lattice carries, cocycles, constant-stream divergence, centering, augmentation ideals, Walsh/ANOVA decomposition, noncommutative Abel development, composite-source interference, factorization grading, and Mellin grade deformation; exact inspection of `CompleteResolutionClockAreaTransgression.lean`, `PrimeDilationTropicalBoundaryTomography.lean`, `ProfiniteLocallyConstantL2Density.lean`, `FiniteQuotientInteractionCohomology.lean`, `CoprimePrimeResidueInteraction.lean`, `BiasedWalshInteractionMechanics.lean`, `NoncommutativeAbelDevelopment.lean`, and deletion mean-descent modules. | Ordinary signature/Magnus/bar/Walsh machinery and finite interaction cohomology exist. Static factorization grading is exact but exponent-blind after unweighting; actual Mellin grading has strictly positive mixing. Only a weighted, zero-specific chronological transgression remains open. |
| Arithmetic differential curvature | Exact-phrase corpus queries for Fermat quotient, p-derivation, delta ring, Wieferich, and arithmetic curvature, followed by `rg` of candidate source files. | Search misses did not establish novelty. Barrett–Buium already construct curvature from Fermat quotient operations: [arXiv:1512.02525](https://arxiv.org/abs/1512.02525). Rejected as a new field claim. |
| Second-kind arithmetic cohomology | Primary abstract of Efimov, [arXiv:1506.00257](https://arxiv.org/abs/1506.00257). | This is published mathematics. Its displayed all-localization nontriviality condition is equivalent to infinitude of Wieferich primes, so assuming that condition would introduce another unresolved arithmetic question. No such premise adopted. |

## Arithmetic fusion, nested sums, and radix transfer: intake audit

**Outcome:** no qualifying successor. These checks test whether existing source laws provide the
missing zero-forced relation. They establish neither a new impossibility theorem nor a general
exclusion of these mathematical areas.

| Proposed transfer | Exact source check | Consequence for this search |
|---|---|---|
| Treat prime-ray fusion as a new arithmetic multiplication | `HTGeometry/PrimeRadialFusionNaturality.lean:133`, `primeRadialFusion_eq_positivePrimePowerProjection_mul`, identifies it with projected Dirichlet convolution when both inputs are supported on positive prime powers. | This operation alone supplies no new zero-forced relation. The support conditions must be retained. |
| Use chronological fusion to change the zeta zero condition | `HTGeometry/ChronologicalTensor/FusionDivisor.lean` defines an explicit Gamma prefactor, proves it analytic and nonzero on its open strip, and proves equality of zero multiplicities there. | Outside the user's allowed source ancestry; its scalar response also preserves the existing divisor. No such construction is adopted. |
| Derive linear growth from rational-Hurwitz mesh refinement | `RHTower/XiRationalHurwitzDyadicRefinement.lean:824` proves `E(n^2)=4E(n)(1+E(n))` throughout the open unit strip. Lines 855–864 identify linear refinement at a modulus greater than one with real part one-half; lines 891–913 give the all-zero RH equivalence. | Removing the quadratic remainder is precisely the missing assertion. Neither finite residue refinement nor changing the modulus proves it. |
| Convert closed endpoints of two nested sums into cancellation | Existing `EulerDeletionQuasiShuffleSecondConvergence` gives the sum of the two complementary orderings as minus their diagonal bracket at closed endpoints; `STATUS.md`, F692/CANNOT-317, records the positive diagonal for the specified deletion grades. | The existing depth-two argument cannot be restarted as a new zero-annihilation law. This says nothing general about all deeper sums. |
| Apply homogeneous radix-substitution rigidity | `HTGeometry/MahlerHomogeneousRigidity.lean:21` requires a formal-series identity `Y(X^k)=cY`. `MahlerInhomogeneousSolve.lean:41` instead constructs a unique solution for every forcing series when `k>=2` and `c` differs from zero and one. | No literal zeta source was shown to satisfy the required homogeneous identity at a zero. General solvability with arbitrary forcing supplies no missing restriction. |

The independent mixed-radix card
`universal-law-field/mixed-radix-formation-geometry/mixed-radix-gauge-critical-normal-geometry-conjecture.md`
concerns digits of **prime multiplicities**, a limiting statistical kernel, and localization of the
divisor in the first factor. It explicitly does not eliminate that divisor. It is not a source
theorem about changing the additive radix of the integer index.

There is also a retrieval ambiguity to avoid: the shifted powers in
`Hurwitz/NonRationality.lean:372` are `n^(-(s+i))`, with shifts in the **exponent**. That theorem does
not establish independence of arithmetic subsequences `(bn+r)^(-s)`, which shift the **argument**.
No finite-dimensional radix-kernel collapse or its negation was proved in this intake audit.

Automatic Dirichlet-series methods have established predecessors:
[Allouche–Mendès France–Peyrière's 1999 preprint record](https://www.imo.universite-paris-saclay.fr/~biblio/pub/1999/abs/ppo1999_40.html),
[Allouche–Shallit–Stipulanti, revised March 2025](https://arxiv.org/abs/2401.13524v4), and
[Li's multivariable construction, revised 2019](https://arxiv.org/abs/1701.08603v2).
The latter two abstracts cover digit/block restrictions and polynomial-denominator multivariable
series respectively. This establishes ancestry for those ideas, not absence of every possible
radix-based RH architecture. The publisher's full 2000 article returned HTTP 403; it was not read.

[The 53-query snapshot](rh-corpus-architecture-audit-2026-09-06-arithmetic-transfer-searches.tsv)
rechecks the discovery terms against the cached index with common settings: AND/prefix matching,
one result per module, 25 ranked hits, five exploration hits, and no module exclusions. These
normalized snapshots are not the exact settings of every earlier exploratory call. `rg` supplied
statement, proof-body, mathlib, and pipeline checks. Returned declarations are discovery locations,
not a claim that every returned proof was read. Some broad outputs were truncated. Search misses
for terms such as `stuffle`, `Beatty`, and `quadrature rigidity` establish no novelty.

No new mathematical statement reached paper closure or Lean admission. No new Lean file, build,
numerical experiment, or `STATUS.md` entry is associated with this intake audit. Its useful result
is the exact list of unsupported transfers above; the two missing links in the target RH chain
remain missing.

## Scope correction for continuous countermodels

The addition/multiplication intake exposed an unsupported search restriction: the old Beurling
countermodel had been used to make exact integer occurrence and coupled arithmetic execution
mandatory for every RH architecture. Its theorem instead chooses its continuous model separately
for each error exponent and proves no counting estimate. Matching selected assumptions does not
show that a countermodel satisfies every hypothesis of an arbitrary candidate.

The [completed auxiliary audit](../3-formalized/not_new_scientific_knowledge/continuous-beurling-logarithmic-error-audit.md)
repairs the mathematical evidence with one explicit pair of positive continuous densities. Their
common rational transform has a zero at `2/3+i`; the same counting function has an exact quadratic
logarithmic remainder and `o(x^e)` error for every `e>0`. These statements, both integrability and
transform identities, and an instantiated capstone are closed in Lean. No discrete realization or
functional equation is asserted. The repair cannot be used to restore the withdrawn universal
restriction on RH proof architecture.

The positive survivor is this exact density/counting decomposition. No novel zero-forced relation
or off-line contradiction for ordinary zeta was found. This correction changes which candidates
may be excluded by the existing evidence; it supplies no RH proof step.

## Relation, arithmetic-family, and code intake after the scope correction

**Outcome:** no qualifying architecture and no new RH proof step. The following checks concern
specific proposed transfers. They do not rule out their mathematical fields or reinstate a
universal prescription that every proof must use one pair of arithmetic operations.

| Proposed transfer | Current source evidence | Disposition and strongest surviving content |
|---|---|---|
| A zero gives a polynomial relation; pointwise jet nondegeneracy should contradict it | `HTGeometry/PatternRelationConfinement.lean:29` assumes an expanded pattern relation before placing evaluation packets. The definition at line 78 asks each point to avoid every nonzero polynomial over `ℂ`; its own preceding comment explains why `X_j-C(a_j)` defeats that condition for a nonempty coordinate set. | Reject this pointwise nondegeneracy input. The surviving placement theorem transports an already supplied relation. Global independence or a nonvanishing evaluation minor cannot be silently substituted for pointwise avoidance of every polynomial. No relation on literal zeta was constructed. |
| Certify off-line impossibility by growing arithmetic circuit cost | `HTGeometry/ExactPenaltyCircuitBellman.lean:501` identifies approximate complexity with the greatest value of a Bellman subsolution, under isometry, inverse, compact-gate/continuity and reachability assumptions. Its penalty threshold is defined using the very approximate complexity to recover. | Exact duality survives, but gives no arithmetic lower bound or zeta-zero-to-state map. Declaring a large calibration would leave the desired lower bound unproved. |
| Use permanent coefficients to extract a forbidden finite relation from the zeta source | `HTGeometry/PermanentCoefficientIdentity.lean:83` requires a series supported on a super-increasing gap set. The resulting uniqueness of source multisets reduces its coefficient proof to surviving permutation assignments. | The exact coefficient identity remains available for those sparse sources. Ordinary all-one Dirichlet coefficients do not establish these formal-power-series support hypotheses; no faithful encoding preserving a zeta zero was supplied. |
| Use simultaneous reflected admission of arithmetic shells | `HTGeometry/ConstitutiveReflectedShellCofinalSelection.lean` defines admission as summability of both real tilts at every base point above one and proves it equivalent to zero tilt for the specified shell family. | The exact summability boundary is already closed. No zero of ordinary zeta is shown to satisfy this global admission condition. This is an existing conditional endpoint, not a new zero-forced law. |
| Assemble complete divisor packets into an RH selector | `HTGeometry/MultiplicativeCenteredDivisorOrientation.lean:87` identifies prime-power packets; the later finite-product current formula proves orientation from that of the factors. | Finite product orientation is the positive content. No corresponding infinite arithmetic limit or joint zero constraint was obtained. The identity cannot itself justify replacing a product by a sum of packets. |
| Use Hasse rows as a fresh zero-forced relation | `RHTower/HasseSondowRowMellin.lean:337` already gives the relation, derived through Gamma-normalized Mellin integrals and the Fermi kernel. The packet-formation cards already formalize its observer consequences. | Existing construction with excluded ancestry. No Hasse/Fermi architecture adopted. |
| Use visible-coprime mixed jets as a fresh relation | `RHTower/VisibleCoprimeZetaZeroJet.lean:129` defines the continued symbol as `ζ(s)ζ(t)invZeta(s+t)`. Its top mixed jet is the squared leading zeta jet times the reciprocal at twice the real part. The current frontier map already records the finite jet extension as a rank-one endpoint. | Existing quotient/jet construction, with excluded Möbius and spectral ancestry in its source chain. No new arithmetic restriction follows merely from its exact sign formula. |
| Build finite codes whose zero-location theorem passes to zeta | `RHTower/DuursmaDoubleRepetition.lean` proves the degree-two extraction and critical-circle law for `(1+2T^2)/3`; it constructs no ordinary-zeta source code. The existing card `prime-syndrome-duursma-code-zeta-limit-rh.md` already proposes a cofinal code limit but requires Gamma/theta marking and leaves source realization, the code-zero theorem and the limit unproved. | Reject this existing proposal under the present exclusions. The finite nonmultiplicativity example is already formalized and labelled not new scientific knowledge. Removing forbidden names would not prove its missing inputs. No replacement source-code family was constructed. |

The code-theoretic ancestry is independently confirmed by
[Duursma's primary paper](https://arxiv.org/abs/math/0302172) and
[Chinen's explicit invariant-polynomial construction](https://arxiv.org/abs/0704.3903).
The opened abstracts concern code enumerators, duality and finite zero-location constructions;
they supply no limit from ordinary zeta coefficients. Duursma's 2001 publisher page returned 403,
so its full text was not read. These checks establish ancestry, not an exhaustive novelty result
or the current status of every code-RH conjecture.

[Four saved query snapshots](rh-corpus-architecture-audit-2026-09-06-source-intake-searches.jsonl)
retain actual indexed results and options: `zero relation` (830 hits in 465 modules), both pages
of `arithmetic` restricted to `HTGeometry` (665 hits in 208 modules), and the phrase `"zeta zero"`
with named-module exclusions (218 hits in 93 modules). Module caps and keyword exclusions are
retrieval settings, not evidence of mathematical independence. In particular, files without a
forbidden word in their name can import forbidden machinery. Some display output was truncated;
the snapshots retain the returned rows. This is declaration discovery, not a proof-body audit of
all those modules. Supplementary targeted queries and `rg` supplied the statement, proof, import,
and prior-card checks summarized above.

No new theorem reached paper closure in this intake. Existing positive statements and their
hypotheses are retained; no new Lean module or numerical experiment was warranted. `STATUS.md`
receives no new mathematical restriction from this pass. The next candidate must supply an
actual construction and a proposed transfer beyond those explicitly missing here; repeated
retrieval of these endpoints is not a new architecture.

## Coverage and verification

- `EulerDeletionFiniteStatisticLaw` passed scratch compilation, a targeted leaf build, an imported five-capstone axiom audit, and repository-wide formal lint. It is wired into `RHTower.lean`. The capstones use only `propext`, `Classical.choice`, and `Quot.sound`. The full finite static law is closed and explicitly attributed to its classical ancestry; it is not a novel RH architecture.
- `EulerDeletionCoprimeWordPeriodicity` passed scratch compilation, its targeted leaf build, and an imported audit of six capstones. It is wired into `RHTower.lean`; all audited dependencies are only `propext`, `Classical.choice`, and `Quot.sound`. The subsequent repository-wide formal lint run passed, with existing large-file warnings. The all-depth finite residue classification and independent-phase vanishing supply a boundary test, not a weighted refinement law.
- `EulerDeletionCylinderReconstruction` passed scratch compilation, a targeted leaf build, and an imported audit of eight capstones. All audited dependencies are only `propext`, `Classical.choice`, and `Quot.sound`. It is wired into `RHTower.lean`. The source equivalence, every-length word transport, arbitrary conjugation choices, exact coefficient costs, and zero-endpoint equivalence are closed; no associated-graded RH descent was proved.
- Index snapshot: 32,233 files, 392,125 declarations, 3,855 gap markers. All-index search scope is not a proof-body audit of all declarations.
- 196 saved numbered corpus queries. Query wording and capped hit counts are in the adjacent search manifest. Those historical queries used the former OR-default tool. The current tool uses AND for spaces and explicit `--any` for OR; ranked results can still omit relevant low-ranked declarations. Exact `rg` searches supplied definition and proof-body checks. No absence or completeness theorem follows from search misses.
- Lean modules `CoprimeBlockCarryTransgression`, `CoprimeBlockMultiplicationFiber`, `EulerDeletionQuasiShuffleScaling`, `EulerDeletionQuasiShuffleConvergence`, `EulerDeletionQuasiShuffleZeroLanding`, `EulerDeletionQuasiShuffleSecondShadow`, `EulerDeletionQuasiShuffleSecondConvergence`, `EulerDeletionQuasiShuffleCylinderClosure`, `EulerDeletionQuasiShuffleCylinderSquareNoGo`, and `EulerDeletionNoncommutativeAbelianShadow` compile directly; targeted leaf builds cover the new leaves, and all are wired into `RHTower.lean`. Capstones prove exact finite dilation, positive-half-plane zero landing, positive energy, cutoff-independent complex self/cross levels, nonvanishing self level, limiting polarized quasi-shuffle, squarefree cylinder closure, repeated-generator obstruction, and commutative-shadow collapse. `/tmp/hgt_edqs_axioms.lean` reports only standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound` for audited capstones. No full build ran.
- `EulerDeletionQuasiShuffleCrossDomain` and `EulerDeletionQuasiShuffleOrderedDilation` also passed scratch checks and targeted leaf builds. They are wired into `RHTower.lean`. The imported audit `/tmp/hgt-deletion-cross-limit-VJDXsM/FinalAudit.lean` checked seven capstones and reported only `propext`, `Classical.choice`, and `Quot.sound`. These close the zero-independent chronological domain and exact grouped dilation formula; they do not supply refinement coherence.
- `EulerDeletionFactorizationGraded` passed scratch and direct compilation and is wired into
  `RHTower.lean`. Its capstones prove flat cofactor insertion/cutoff order, literal squarefree
  insertion, exact uniform orthogonality and replication scale, and the strictly positive Mellin
  cross-grade defect. The independently present
  `EulerDeletionMeanInterferenceDescent` also compiles directly and proves why unweighting this
  structure is exponent-blind. A targeted leaf build passed; `/tmp/hgt_edfg_axioms.lean` reports
  only `propext`, `Classical.choice`, and `Quot.sound` for nine capstones. These results reject
  static FGQD and define MDFGT's exact target.
- `EulerDeletionFactorizationCurvature` passed scratch and direct compilation, a targeted leaf
  build, and an imported nine-capstone axiom audit. It is wired into `RHTower.lean`; audited
  dependencies are only `propext`, `Classical.choice`, and `Quot.sound`. It proves additive
  associator flatness, the exact multiplicative curvature formula, and its negative/zero/positive
  trichotomy. It also proves that the natural central defect lift has associator `K` and is
  nonassociative throughout `1<alpha<2`. It does not prove zero-fibre annihilation or an RH
  implication.
- A primary-literature collision screen found the generic quasi-shuffle associativity framework and
  adjacent zeta-distribution work, but no exact match for this four-term Euler-deletion curvature.
  Search misses are not a novelty certificate; the construction remains a candidate, not a
  literature-priority claim.
- The repository-wide formal lint scan passes, with large-file warnings only. Owned Lean files have
  no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `decide`, or `native_decide`; an earlier finite
  proof's `decide` was replaced by an explicit singleton-cardinality argument.
- Multicore Runpod scans at the supplied endpoint tested self and cross chronological levels for the first 12 known zeros, four moduli, and cutoffs through two million. Quasi-shuffle residuals stayed below `4.27e-14`; raw self and cross carries were nonzero with both signs, while fitted tail drift was small. This kills universal sign/vanishing as producer but is not proof of convergence and says nothing about hypothetical off-line zeros. Scripts, raw JSON, and interpretation are in `2-fully-proven/computations/euler-deletion-quasi-shuffle-second-level/REPORT.md`.
- `universal-law-field/STATUS.md` records only route-independent finite source facts, retired mechanisms, and the live refinement-coherence requirement.
- The goal remains active; no qualifying novel RH architecture or sole successor is established.
  The finite scaling, conditional zero landing, complex second levels, squarefree cylinder
  closure, factorization grading, weighted defect, and curvature theorems remain closed auxiliary
  results. They do not supply a new zero-forced relation or an off-line contradiction.
  Unrestricted zero-curvature annihilation is already refuted, and the mixed-area replacement
  is computationally disfavored. The positive prime-tail approximation above adds a closed
  constraint on coefficient-only continuation arguments. Rejected additive, raw-sign,
  analytic-continuation holonomy, ordinary commutative development, independent replication,
  unweighted mean descent, and full-algebra branches are not approved continuations.


## Growing-modulus scalar admission boundary

The fixed-modulus all-depth history theorem does not extend to one ordinary cutoff controlling
all deletion moduli. `EulerDeletionGrowingModulus` now proves the exact replacement: for every
`0<Re(s)<=1` and arbitrary natural-valued budget `A(N)`, uniform Cauchy tails of the literal
modulus-`q+1` prefixes over `q<=A(N)` hold iff `A(N)(N+1)^(-Re(s)) -> 0`. No monotonicity of A
and no zeta-zero premise enters. A finite Abel block estimate and the next literal deletion
supply matching upper/lower rates. In particular all-modulus uniformity fails in the critical
strip. The positive classification, not only that failure, is closed in Lean.

This rejects this uniformity demand as the missing cross-modulus relation. It does not reject
separate relations between completed histories, and does not establish a new RH architecture.
The derivation uses classical periodic Abel theory; there is no literature-novelty claim.
Ten theorem axiom audits, direct Lean check, and serialized narrow leaf build passed.
[Exact theorem, paper proof, source audit, and scope](../3-formalized/not_new_scientific_knowledge/euler-deletion-growing-modulus-boundary.md).
STATUS F20h records the self-contained admission fact. No new zero-forced relation or off-line
contradiction was obtained.

## Zero-relation intake and the vanishing-source classification

The next intake searched both RH and non-RH areas for arithmetic relations, nonlinear
cancellation, semirings, cyclic sources, divisibility, and contracting homotopies. Corpus
searches were paired with `rg` on candidate statements, proof bodies, imports, and pipeline
cards. The uncapped phrase query `research '"zeta zero"' --limit 1000 --per-module 0
--explore 0 --json --no-refresh`, excluding the module substrings Suzuki, Hedenmalm, Weil,
Connes, Burnol, HilbertPolya, Spectral, Gamma, Mobius, Theta, and Xi, returned 277 declarations
in 117 modules. [The complete retrieval snapshot](rh-corpus-architecture-audit-2026-09-06-zero-relation-search.json)
is saved. This counts retrieval, not inspection of every proof. Filename filters do not remove
excluded dependencies; those still require import and definition checks.

The inspected proposals fail at different, explicit gates:

- **Associator as a boundary.** A scalar identity `K(s)=ζ(s)H(s)` would force zero curvature,
  but defining H by division away from zeros supplies no independent construction of H at a
  zero. `EulerDeletionCurvatureCriticalBoundary.exists_actual_zero_with_nonzero_charge`
  already refutes a globally regular realization of this identity for the literal curvature.
  The arithmetic curvature's zero wall is Re(s)=1, not 1/2. A construction only in the strict
  right half of the strip remains unproved. The abstract associator/homotopy identity itself
  is standard: [Keller, *A-infinity algebras, modules and functor categories*, section 2.1](https://webusers.imj-prg.fr/~bernhard.keller/publ/ainffun.pdf).
  The corpus's `FormationAnchoredCubicHomotopyDefect` uses operator ideals and therefore fails
  the user's source restrictions as well. The strongest available positive survivor is the
  already formalized exact curvature and its nonzero critical-line boundary; this intake
  produces no additional positive theorem for the scalar homotopy proposal.
- **Alternating-prefix decay rate.** `DQPTPartialSumRate` distinguishes zero and nonzero
  values by a logarithmic rate, but that criterion is already the subject of
  [*The Riemann Hypothesis manifested in dynamical quantum phase transitions*](https://www.nature.com/articles/s41467-026-74935-8).
  Its engineered energy spectrum also fails the user's restrictions. The local
  `dqpt-rh-paper-lean-formalization` card and failed `nature-dqpt-alternating-tail-rh-route`
  card already distinguish the valid rate theorem from the false ordinary-coherence
  selector. These existing exact rate results supply the positive survivor; no new RH
  mechanism is obtained by renaming them.
- **Missing echo coefficient.** `HeatApertureEchoParity.riemannZeta_eq_zero_iff_echoLadder`
  detects a zero by a missing initial coefficient, but its defining `HeatApertureEchoLadder`
  explicitly uses Gamma factors and backward shifts. This is excluded ancestry, not a new
  arithmetic zero relation. The existing coefficient classification remains the positive
  theorem; this intake adds none.
- **Negative Euler sheet.** `ProjectiveEulerCanonicalPolarity` defines the response as
  `ζ(2s)/ζ(s)` and proves its pole multiplicity at a zeta zero. The identity transports the
  divisor to poles; it does not independently exclude those poles. Its already proved exact
  divisor-order classification is the positive survivor, with no new regularity producer.
- **Vanishing cyclic source.** `SourceOrientation.srcIncompatEquiv` and
  `annihilator_srcIncompatModule` require both q and c to be units. Substituting c=ζ(s)
  precisely loses that premise at a zero. The original theorem is correct. The new
  `SourceScalarBoundary` now classifies the literal quotient without either unit assumption:
  `R/(c) × R/(cq(q−1))`, with annihilator `(cq(q−1))`. The same result holds for every
  invariant surjective source trace. Over a field its dimension is 2 at c=0 for every q,
  1 at nonzero c and q in {0,1}, and 0 otherwise. Thus quotient survival at a zeta zero
  cannot select q in this construction.

The last classification is the closed positive survivor of that proposed substitution.
Fourteen public theorems, four definitions, and two abbreviations passed direct Lean checking,
the standard-axiom audit, and the serialized narrow leaf build; the umbrella import is wired.
It is elementary module algebra, filed under `not_new_scientific_knowledge`, with no claim
of absence from literature. [Paper proof, exact formal statements, and verification](../3-formalized/not_new_scientific_knowledge/cyclic-source-nonunit-scalar-audit.md).
STATUS F20i records the self-contained scalar-specialization fact. No numerical experiment
was needed. None of these intakes supplies a qualifying architecture, a new zero-forced
relation, or an off-line contradiction; the RH goal remains open.

## Literal alternating source and inverse-branch intake

The next search covered arithmetic obstruction, nonlinear relations, additive/multiplicative
compatibility, deformation, integer rigidity, confluence, coefficient operations, and formal
compositional inversion. These queries range across the indexed tree; capped results are
discovery only. Exact bodies were inspected for `TwoProductDiagonalGaugeRigidity`,
`TwoRecordResolvedConnection`, `ConstitutiveBiFormationInterference`, the initial source
and imports of `PrimeValuationNormalCornerDuality`, and the construction and specialization
of `FormalCompositionalInverseFreeness`.

The first three constructions do not supply zero-forced laws: simultaneous preservation of
two packet products is an assumption; a normalized two-record connection is generically a
coboundary; bounded copies of a nonzero cubic current require an independent bound. The
prime-valuation tomography module explicitly uses Gamma coordinates and spectral machinery,
so it fails the user's source restrictions. Its finite coefficient partition alone gives
no zero-location relation. The previously audited word-rewriting toy remains a separation
of execution and equivalence, without a new literal arithmetic realization.

Formal compositional inversion suggested a specific new intake test on the actual coefficients:
`F_s(z)=sum_(n>=1) (-1)^(n-1)n^(-s)z^n`. Its distinguished radial boundary value is eta(s).
The proposed first conjecture was global disk injectivity for every Re(s)>1/2, as a possible
precursor to an obstruction to the boundary collision F_s(0)=F_s(1)=0. The classical exterior
area theorem rejects this stronger conjecture: the necessary bound `|a3-a2^2|<=1` fails
at the explicit height `pi/(log4-log3)` for real parts in an interval immediately right
of 1/2. Open-disk injectivity and boundary injectivity must in any case be distinguished.

The positive scalar result is now closed in `AlternatingInverseCoefficientBoundary`: the
literal formal series has both inverse identities at every complex parameter, while its
third coefficient defect has the sharp attained horizontal maximum
`3^(-sigma)+4^(-sigma)`. The unit ceiling has a unique cutoff strictly between 1/2 and 1.
This is elementary coefficient analysis, not a qualifying novel RH architecture. The full
geometric noninjectivity conclusion remains a paper application of the published area
theorem; it is not claimed as a Lean result. A smaller inverse corridor aimed only at z=1
has no independently constructed arithmetic control yet and is not an approved successor.

[Exact conjecture, falsification, classical sources, formal positive theorem, and limits](alternating-source-inverse-branch-intake.md).
STATUS F20j records only the self-contained formal-inversion/coefficient-control separation.
No numerical experiment was required. The new zero-forced relation and off-line contradiction
remain missing.

## Arithmetic incidence and zero-transfer intake

**Outcome: no qualifying successor architecture.** This intake tested whether an actual integer
operation could send a hypothetical zero to another arithmetic scale, or force a finite incidence
relation with an independently impossible boundary. It did not construct either implication.

[Complete retrieval for seven precise cached queries](rh-corpus-architecture-audit-2026-09-06-incidence-transfer-searches.json)
records the query arguments and all returned declarations, with no per-module cap or exploration
extras. Counts are: `arithmetic incidence` 7 declarations/6 modules; `integer compatibility` 1/1;
`zero propagation` 28/21; `zeta dilation` 108/26; `arithmetic automaton` 0/0; `prime word` 124/21;
`nonlinear` 231/127. Counts overlap. These are complete retrievals for the saved filename filters,
not proof audits of every hit or evidence that an idea is absent from literature. Additional
discovery used arithmetic outside RHTower/HTGeometry, finite obstruction, reciprocity, integer
transport, multiplicative/additive compatibility, coefficient ideals and reconstruction, and
shuffle queries. `rg` then located the relevant statements, definitions, and imports.

The concrete source checks give these decisions:

- `RHProofLab.EulerProductArithmetic` proves the finite subset expansion and disjoint-product
  identities for arbitrary coefficients in a commutative ring. The inspected portion of
  `RHProofLab.PositivitySelector` encodes zero defect as a sum of squares for an already supplied
  finite point family. Neither supplies a new relation forced by a zero of literal zeta.
- `BigWittArakelovSourceEndomorphismTerminal` was inspected to detect excluded ancestry, not
  adopted. Its coordinate power law does not preserve the analytic source: the induced square
  map is `rho^2/(2*rho-1)` and has a pole at `1/2`; actual cover maps and Euler jet dilation are
  different operations. Its requested zero-divisor stability is already RH-equivalent. The
  existing positive results are the exact reporter power law and the source-correct jet
  dilation `X -> nX`. They supply no new zero-transfer theorem.
- `PowerSievedLiouvilleRecurrence.LSeries_sievedLiouville_mul_riemannZeta` requires `Re(s)>1`.
  The identity `L(a_m,s)*zeta(s)=zeta(ms)` therefore cannot be specialized to a hypothetical
  strip zero using its stated hypotheses. Extending the quotient regularly there would be a
  new obligation; the quotient identity does not establish it. This is the existing
  Liouville/divisor-quotient route, not a radical successor. The exact convolution/Dirichlet
  identity is the already formalized positive survivor.
- `ProjectiveHorizonCausticQSystem.qSystem_zero_propagation` assumes both the quadratic relation
  `center^2=left*right+up*down` and two neighboring zeros, `center=left=0`. It then gives
  `up=0` or `down=0`. The arithmetic realization and second zero are absent from this intake;
  one zeta zero cannot be substituted for both hypotheses. Its determinant identity remains
  the existing positive statement, without a new arithmetic construction.
- `PerfectComplexDoublingDerivedLimitCountermodel` starts with the integer tower whose maps
  multiply by two. Ordinary-limit vanishing and a nontrivial derived-limit class are real
  integer phenomena, but no literal zeta coefficient or zero-to-class map was constructed.
  Only its initial tower and explicit obstruction proof were inspected here.
- `CoprimeBlockMultiplicationFiber` retains an exact finite multiplication collision invisible
  to row and column sums. Its six-cell coefficient and cancellation classification is already
  formalized and already covered by the earlier multiplication-fibre intake. No new infinite
  source law follows from rereading it.
- `PrimeWordSupportSelector` and `PrimeWordMatchingIncidenceNoGo` retain finite support and
  incidence distinctions. The downstream `PrimeWordSynchronizedCluster` instead uses explicit
  two-state ferromagnetic blocks and does not identify their product with zeta. Its initial
  definitions and norm/localization proof expose that missing identification. This returns to
  an existing Lee--Yang construction and fails the requested novelty gate.
- `SourceZeroHorizontalCarrier` explicitly takes Xi-zero copies as inputs and uses Gamma
  coefficients. The inspected adjacent-tail reader gives exactly
  `(1/2-Re(rho))*log(2)`. It measures the horizontal position and does not prove its vanishing;
  it also fails the user's source restrictions. The finite Euler-flux tangent map inspected in
  `PrimeExponentialHolomorphicDeterminingSourceImage` allows arbitrary complex coefficients
  and proves density of their images, not an identity for the fixed all-one coefficients.

**Scope correction, not another no-go.** `AdjacentDilationZetaBase` gives differential
independence over the zeta differential field, preserved under nonzero base gauges. This excludes
certain identities of functions, not relations at an individual zero. For a finite analytic
family independent over a field containing `C(s)`, the common factor `s-a` preserves differential
independence while making all values at `a` vanish. The triangular Leibniz law in
`BaseGaugeDifferentialIndependence.differentialIndependent_mulBase_iff` supplies the independence
statement; evaluation at `a` supplies the common zero. No assertion that these altered functions
are the original arithmetic source is made.

STATUS F03 now replaces the overbroad “finite arithmetic syzygy route is closed” assertion with
this distinction. `/tmp/hgt-zero-transfer-audit-b1fbXR/ExistingDeclarations.lean` checked the
generic gauge theorem and its actual zeta-dilation application with `lake env lean`; both axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`. This verifies existing
declarations, not a new formal RH theorem. No Lean source changed, no build or numerical experiment
was needed, and no Lean process remains owned by this intake. The previous unrelated global-lint
reachability failures are not resolved or claimed to pass by this documentation change.

The next architecture must supply an actual relation at a zeta zero. It is premature to require
that relation to hold as an identity for every parameter, or to exclude it using functional
independence alone. No particular such relation has yet been constructed or selected.

## Thin-deletion boundary: failed rejection and published ancestry

The next intake searched zero specialization, point relations, zero congruences, arithmetic
endpoints, algebraic zeta families, and cancellation. `rg` checked the retrieved definitions
and references. `SpecializationFaithfulnessBoundary` supplies a generic polynomial evaluation
kernel, not an arithmetic relation. `ArithmeticDilationDeterminantZeros` explicitly uses a
Fredholm/spectral construction and was rejected on source restrictions. No candidate was
selected from either.

`ThinDeletionEssentialSingularity` suggested testing whether a deletion could create a boundary
defect that a finite-order zero could not absorb. Reading both its exact hypotheses and the
parent card uncovered a failed rejection instead: the proposal counts deleted primes on the
scale `x^gamma/log x`, while its alleged no-go switches to `x^gamma`. These produce logarithmic
and reciprocal-distance divergence respectively. The proved scalar inequality applies only
to the latter, exponentially flat bound.

The conjecture that mere divergent logarithmic deficit prevents analytic extension is false:
`exp(-m*log(1/t))=t^m` for t>0. A symbolic scratch Lean proof closes that precise positive
boundary. No deletion set is claimed to realize this scalar model. The existing finite sieve
identity and exponential-versus-power theorem remain valid; neither proves the random error
bounds. A same-order uncontrolled remainder also prevents the card's positive-tail argument
from supplying a lower bound for the complete counting error.

The primary paper already uses thin random prime deletion; its section 5 distinguishes
logarithmic singularities from zeros after exponentiation and retains an RH-dependent
reciprocal-zeta estimate. [Broucke–Debruyne–Révész](https://arxiv.org/html/2309.01567v2#S5).
Thus the proposal fails the novelty requirement, while the claimed universal mathematical
rejection is also unsupported. This is not an approved RH successor.

The [parent card](thin-random-deletion-beurling-alpha-beta.md) now states the original unproved
random bounds, exact source mismatch, published ancestry, and strongest existing positive
results. Its [downstream formalized card](../3-formalized/beurling-zero-certification-barriers.md)
now distinguishes a fixed geometric lattice from arbitrary self-similarity and restricts
modification nonvanishing to the actual convergence region. Claims of an exhaustive
classification and a universal `beta>=gamma` implication were removed. Only comments changed
in the three cited Lean modules; no theorem statement or proof changed. STATUS F186 records
the self-contained logarithm-versus-function boundary distinction.

Scratch `/tmp/hgt-thin-deletion-scope-tOIrDU/Audit.lean` passed with `lake env lean`: the scalar
identity and seven existing declarations use only `propext`, `Classical.choice`, and
`Quot.sound`. All three direct source checks passed. The final foreground command
`LEAN_NUM_THREADS=1 lake build --old` with exactly those three leaves passed; its only newly
built modules were those leaves. Existing umbrella imports remain in place. Index refresh
and `scripts/formal_tools.py lint` passed. All owned Lean processes finished. Logs are in
the scratch directory. No numerical experiment was run. Both decisive RH links remain
missing; these corrections do not constitute progress on the missing implication.

The subsequent direct attack on ordered products returned to an already established boundary.
`EulerDeletionQuasiShuffleSecondShadow` proves that a hypothetical strict-right zero forces
the real second ordered level to equal minus half the positive diagonal energy. It does not
force that level to vanish. In `EulerDeletionQuasiShuffleScaling`, the equality between
replication and arithmetic dilation is explicitly the `hcoherence` premise. No derivation
of that premise was obtained. This is an unresolved proof obligation, not a new architecture.

A proposed fallback through zero motion of the literal Abel-damped alternating series was
also not admitted. A primary-source search located earlier polylogarithm zero-motion and
bracketing proposals. The precise negative-argument family differs from the branch-point
family in that note; the evidence establishes ancestry, not equivalence of every conjecture.
See the additional source assessment in
[the alternating-source card](alternating-source-inverse-branch-intake.md).

## Alternating replacement: a sharp coefficient-growth obstruction

The next proposed producer used `eta(rho)=0` to repeat the replacement represented by
`1-eta`, seeking uniform control from square summability in the strict half-strip.
The needed coefficient estimate is false. Odd product outputs receive contributions of
one common sign. For `r` odd labels of total positive weight `A`, their depth-`k`
coefficient energy lies between `A^(2k)/(k+1)^r` and `A^(2k)`.

The exact odd-sector survivor is closed in `RHTower/OddDirichletPowerGrowth.lean`:
a finite exponential bound uniform in cutoff and depth exists iff `sigma>1`, while
the initial square-sum threshold is `sigma>1/2`. It includes actual integer-product
grouping and literal replacement-coefficient sign laws. This is an obstruction to the
proposed coefficient completion, with no zero-location conclusion or scientific novelty
claim. [Paper proof, ancestry rejection, and precise formal scope](../5-failed/alternating-substitution-collision-growth.md).

All 19 public declarations passed the scratch axiom audit with only the standard three
logical axioms. Scratch and direct leaf checks, the serialized build of this one new leaf,
umbrella wiring, index refresh, and global lint passed. No computation was run and no
owned Lean process remains. STATUS records the self-contained threshold distinction as
ODD-POWER-001. The missing implication from a zeta zero to a contradiction remains open.

## Reflected closure and finite real coefficients: intake boundary

The attempted chain was simultaneous closure of the literal deletion sums at `s` and
`1-conj(s)`, followed by an arithmetic identity exchanging their two chronological orders,
then exclusion of unequal real parts. The jump sequences differ by the positive weight
`n^(2*Re(s)-1)`. The existing endpoint-tail theorem supplies closure and decay; the polarized
quasi-shuffle identity supplies the **sum** of the complementary ordered terms and their
diagonal correction. Neither inspected theorem identifies the two ordered terms. No proof
of that additional arithmetic identity was obtained. This is not an approved RH architecture.

Corpus intake used `research 'zero tail'`, `research 'simultaneous zero'`,
`research 'positive reweight'`, `research 'ordered reflection'`, and
`research 'weighted summation'`, followed by `rg` of the deletion modules and existing audit.
The actual prefix bound and polarized identity were read in
`EulerDeletionQuasiShuffleSecondConvergence.lean`. Broad searches had result caps; no complete
proof-body audit or novelty conclusion is claimed.

The fallback that real, finite-range, integral coefficients might escape known Euler-product
counterexamples is contradicted by [Bochkov, Theorem 2(2), page 3](https://arxiv.org/pdf/2207.08659).
Its exact scope is recorded as MUST-SIGN1 in STATUS. This is published source evidence,
not a newly proved theorem or a Lean premise. No general obstruction to the literal all-one
sequence follows. No qualifying successor or new Lean proof of the RH implication was obtained.
