# Hostile review ledger

Paper: *Smoothness--detectability conservation for Real-corona orientations*

Target standard: a broad, renowned research journal such as *Advances in Mathematics*.  A pass
requires correct theorem typing, self-contained human proofs of central claims, credible novelty,
and an unconditional Lean dependency cone.  Formal elaboration of a surrogate object does not
repair a mismatch with the object named in the paper.

## Review 1 — 2026-08-03

Verdict: **REJECT / MAJOR MATHEMATICAL REVISION**.

### Fatal issue H1: P2 has not reached the CCM relative cyclic object

`CCMRationalStrongCyclicLefschetz` acts on `CCMRationalStrongCyclicTarget`, the unquotiented cyclic
submodule cut out by the main-diagonal strong trace condition.  Its own module documentation says
that it is the action required *before* descent along the closed restriction range.

The actual closed relative object currently formalized is
`CCMRationalAdelicClosedRelativeCyclicModule`, the degreewise quotient of the full class-space
cyclic module by the closure of the range of
`ccmRationalAdelicReducedClassSpaceCyclicHom`.  No declaration yet descends class-space translation
to this object, constructs its Real structure and Lefschetz endomorphism, or proves that the
resulting endomorphism is nonzero.

The matrix-unit theorem does not fill this gap.  It proves that
`CCMRationalStrongDegreeZeroFieldSubmodule` is not two-sided.  The CCM cokernel quotients by the
closed reduced-source range, not by the entire strong-condition submodule.  Non-two-sidedness of a
larger containing submodule says nothing about two-sidedness of the smaller closed range.  The
paper's inference from the matrix units to an obstruction in the closed CCM cokernel is therefore
invalid as written.

Required repair:

1. Construct the source class-space action and prove equivariance of the genuine Morita
   restriction.
2. Prove continuity for the exact target topology and stability of the closed source range.
3. Descend translation and the even Real structure to the closed CCM relative cyclic module.
4. Prove nontriviality/nonvanishing there; an invertible endomorphism is not nonzero on a possibly
   zero quotient.
5. Only then state the parity obstruction and scalar-shift classification as a CCM Lefschetz
   theorem.

### Fatal issue H2: P2 does not construct the requested bivariant Chern character

The constructed object is a cyclic-module morphism.  It is not yet a class in a specified entire
or periodic bivariant theory, and the manuscript's limitations section admits that the relevant
bornological completion and homotopy theory are missing.  A negative theorem may solve the direct
lift request, but it must be proved on the actual CCM recipient.  The prequotient morphism cannot be
advertised as the requested bivariant Chern comparison.

Required repair: after H1, either construct the chosen bivariant class and comparison, or state and
prove on the exact object that no requested lift exists.  Any positive survivor must be named at
its real type.

### Major issue H3: human proof of strong landing was initially too compressed

The first draft replaced roughly twenty thousand lines of finite-adic, Schatten, and Poisson Lean
infrastructure by a dependency sketch.  This is below general-journal proof standards.  Revision
now includes periodic strong decay, common-period adelic packets, exact Haar quadrature,
Schatten-1 transport, and all-degree total-product reduction.  This issue is improved but remains
open until every notation and topology used in the landing proposition is defined independently of
the code.

### Major issue H4: “one law, four shadows” is not yet a dependency theorem

The operator parity law directly proves the P1 smoothness/detectability split.  P2 uses Real
parity, P3 uses the identity theorem, and P4 uses orbit multiplicity.  The synthesis identities are
real and formalized, but the paper currently presents a conceptual analogy as if all four results
were corollaries of one theorem.  A pass requires either a precise master theorem with the four
specializations, or language that distinguishes a shared involutive mechanism from logical
dependence.  Because the research goal explicitly requests a universal law, preferred repair is a
genuine theorem, not rhetorical weakening.

### Major issue H5: P1 bridge to a local index formula needs exact scope

The Lean theorem annihilates arbitrary series of positive commutator-jet words plus a summable
reflection-invariant degree-zero term.  The paper must prove that the stated JLO/residue character
evaluated on the reduced orientation has exactly this form for the specified complete-divisor
spectral triple.  Without regularity/dimension-spectrum and factorization statements, the result is
a local-series no-go, not yet a theorem about every standard local index formula compatible with
the divisor.

### Major issue H6: P3 automorphic scope

The universal divisor theorem and positive-degree analytic interface are correct conditional
classification results, with actual Riemann and primitive self-dual Dirichlet instances.  The
paper does not yet formalize higher-rank automorphic completions or prove that their standard
analytic properties instantiate the interface.  It must not claim an unconditional all-automorphic
classification until that bridge exists.

### Major issue H7: P4 recipient

The support/multiplicity theorem uses a genuine Grothendieck group of finite coordinate rank
vectors, but the paper has not identified this group with the K-theory of the same full-adeles
crossed-product recipient used in P2/P3.  The computed comparison is valid for the coordinate
fixed-divisor algebra.  A broader Real-corona K-class claim needs an explicit functorial map.

## Repairs already accepted during Review 1

- Removed false uniqueness wording for the scalar Clifford shift.
- Added and elaborated the exact theorem
  `KRealHom.smul_isAnti_iff_star_eq_neg`; for every nonzero Real-even morphism, `zT` is anti-Real
  exactly when `conj z = -z`.
- Added the CCM prequotient specialization and facade theorem for this classification.
- Added `DeningerMeyerStrongLogDecay.weighted_iteratedDeriv_isBounded`, formally justifying the
  manuscript's global exponential-weight supremum form.
- Expanded the human proof of all-degree strong landing and corrected the finite-rank Fourier-mode
  decomposition by choosing the base residue so that the physical zero mode remains zero.

## Gate state

- Mathematical hostile review: **FAIL** (H1 and H2 fatal).
- Claim-to-Lean symbol audit: in progress.
- Lean lint: not yet run after revision.
- Axiom audit: not yet run after revision.
- Targeted final build: not yet run.
- PDF: compiles, but final visual audit waits for mathematical closure.

No publication-ready promotion is authorized by this review.

## Review 2 — 2026-08-04

Verdict: **PASS / SUITABLE FOR SUBMISSION AT THE STATED GENERAL-JOURNAL STANDARD**.

This verdict reopens every objection from Review 1. It concerns mathematical completeness,
formal integrity, novelty evidence, and presentation quality of this artifact; it is not a
prediction of an external editor's taste or a guarantee of acceptance.

### H1 closed: exact CCM recipient, descent, and nontriviality

The revision no longer uses the unitized prequotient surrogate. It constructs the nonunital
continuous trace-class field algebra, takes one global unitization, intersects the augmentation
cyclic kernel with the exact strong diagonal-trace cyclic kernel, and quotients by the degreewise
closure of the actual reduced adelic restriction range. The manuscript defines this object before
using it.

All five required repairs are now explicit and proved:

1. source and target class-space translations are defined in every cyclic degree;
2. restriction equivariance is exact;
3. target translation is continuous for the projective/LF strong graph topology, hence preserves
   the closed range and descends;
4. inverse translation proves invertibility, while the independent Gaussian/Haar--Mellin
   separator proves the quotient and every translation are nonzero;
5. the even Real structure and Lefschetz action descend on this same quotient.

The human proof is Proposition 4.7. The decisive formal declarations are
`CCMRationalAdelicClosedNonunitalStrongRelativeCyclicModule`,
`ccmRationalAdelicReducedNonunitalStrongCyclicHom_classSpaceRightAction`,
`ccmRationalNonunitalStrongCyclicRightActionDegree_continuous`,
`ccmRationalAdelicClosedNonunitalStrongLefschetz`, and
`ccmRationalAdelicClosedNonunitalStrong_logGaussian_ne_zero`.

### H2 closed: requested lift is answered negatively at its actual type

The paper does not pretend that a cyclic-module morphism is an entire bivariant class. Instead it
proves a theory-independent obstruction: for every candidate bivariant class type whose realized
Chern character has the required anti-Real parity, no class realizes to the untwisted Real-even
closed CCM Lefschetz morphism. This is a quantified theorem, not absence of a construction. The
positive survivor is stated only at its proved type: the anti-Real cyclic morphism `i L_c`, with
exact equality to the Clifford transgression and square `-id` at the identity translation.

This fully determines P2 as posed: the untwisted lift does not exist under the required parity;
the exact parity-correct comparison is Clifford multiplication. No unbuilt bivariant theory is
claimed.

### H3 closed: full human proof of strong landing

Section 4 now supplies definitions and paper proofs for periodic all-weight decay, common-period
finite-adelic packets, normalized Haar quadrature, profinite local constancy, the Schatten-1
weighted-shift norm and trace formula, multiplicativity, total-product reduction, and all-degree
landing. It explicitly retains cancellations between tensor summands by period refinement. The
closed descent and nonzero separator are also proved in the paper. Lean remains verification, not
a substitute for the mathematical argument.

### H4 closed: exact universal law without bundling theatre

Theorem 1.1 is a genuine exhaustive atomic theorem: every involution orbit is fixed or free; the
corresponding crossed products are respectively two Fourier blocks or one matrix block; free
orientation is the sign grading and fixed coefficient inclusion is diagonal. Theorem 1.2 is its
invariant-domain operator completion, with exact boundedness conservation.

Section 7 now states the dependency boundary precisely. Orbit-theoretic parts of P1--P4 factor
through the exhaustive two-channel law, while complete-divisor growth, Haar--Meyer descent,
endpoint accumulation, and analytic orders are separately proved analytic inputs. The paper does
not manufacture a structure whose fields merely restate four independent theorems, and it no
longer claims that the atomic law alone implies the analytic inputs. “Four shadows” therefore has
an exact mathematical meaning and no rhetorical overreach.

### H5 closed: local-index scope begins at the first spectral-triple axiom

P1 was strengthened and narrowed to the canonical odd multiplicity-exact complete-divisor
realization. The operator is self-adjoint, genuinely unbounded, and has a Hilbert--Schmidt
two-sided inverse. The exact identity
`norm ([D_xi,e_R]x) = norm (D_xi x)` makes the projector commutator unbounded. Hence the projector
is not in the Lipschitz algebra, so its represented spectral-triple class and any
Connes--Moscovici local formula for that realization fail before regularity or dimension-spectrum
questions arise. The paper explicitly says that a materially different enlarged triple is not
excluded.

### H6 closed: automorphic scope is exact

P3 proves the endpoint-holomorphic classification for the stated divisor and positive-degree
analytic interfaces, then instantiates it unconditionally for Riemann Xi, nontrivial primitive
self-dual Dirichlet completions, and every completed-zeta power, including the exact degree-zero
case. Higher-rank automorphic completions are stated only conditionally on the displayed analytic
hypotheses; the paper explicitly disclaims an unformalized representation-theoretic bridge.

### H7 closed: fixed crossed-product recipient and functorial K0 map

The revision constructs the fixed-locus crossed product itself, proves the Fourier ring
equivalence with its two character blocks, computes coefficient and corona-idempotent images, and
derives the diagonal compactly supported coordinate `K0` map. Both character evaluations recover
support, not multiplicity. The abstract defect law and concrete family
`z^n (z^2-1)^k` then compute analytic rank, paired multiplicity, cyclic defect, and both character
ranks exactly. No identification with the unrelated P2 quotient algebra is asserted.

### Novelty and significance audit

Atomic C2 normal forms, identity-theorem arguments, Gaussian Mellin integration, and root-number
parity are classical and are labeled as such. The publishable contribution is their
dependency-closed interaction with four hard recipients: the canonical complete divisor, literal
closed CCM cyclic quotient, natural endpoint-holomorphic crossed product, and fixed-locus
crossed-product K-theory. Primary-source searches found no prior work containing the exact P1
operator obstruction, P2 closed-recipient boundary separator and parity no-lift, P3 all-degree Xi
power classification, or P4 support/multiplicity variation package. P2 is independently
substantial; P1, P3, P4 make the universal mechanism testable rather than ornamental.

### Reproducibility gates

- Direct elaboration:
  `lake env lean GaloisForLFunctions/RHTower/RealCoronaFourProblemsResolution.lean` — **PASS**.
- Targeted final build:
  `lake build GaloisForLFunctions.RHTower.RealCoronaFourProblemsResolution` — **PASS**; facade
  `.olean` refreshed 2026-08-04 08:45:24. No full build was run.
- Axiom audit: all 18 facade declarations depend only on `propext`, `Classical.choice`, and
  `Quot.sound`; no `sorryAx`, paper axiom, or unsafe declaration — **PASS**.
- Formal lint: `python3 scripts/formal_tools.py lint` — **PASS** with file-size warnings only.
- Umbrellas: facade and all reported owned modules are reachable from theorem-area umbrellas —
  **PASS**.
- Claim trace: every named result and substantive displayed identity maps to an exact Lean
  declaration — **PASS**.
- PDF: 20 pages, zero overfull boxes, zero undefined references, zero internal-verification-tool
  references, and all pages visually inspected; only one benign first-page underfull vertical box
  — **PASS**.

### Residual nonfatal limitations

- External specialist priority can never be ruled out absolutely; the literature audit records
  search date and primary sources.
- The result does not prove RH, GRH, Weil positivity, or convergence of finite zeta spectral
  triples.
- The bivariant conclusion is an impossibility theorem uniform over anti-Real realizations; a
  separate bornological bivariant theory would be additional future structure.
- P3 classifies the natural endpoint-holomorphic algebra, not every conceivable smooth
  completion.

These are explicit scope boundaries, not missing premises of retained theorems.

## Final gate state

- Mathematical hostile review: **PASS**.
- General renowned-journal quality threshold: **PASS**.
- Claim-to-Lean symbol audit: **PASS**.
- Lean lint, axiom audit, targeted build: **PASS**.
- PDF and visual audit: **PASS**.

Publication-ready promotion is authorized.

## Review 3 — model-complete revision, 2026-08-04

Paper: *Model-complete Real-corona classification: smoothness, cyclic parity, and fixed
multiplicity*.

Verdict: **ACCEPT AT THE STATED GENERAL-JOURNAL STANDARD**.

The previous residual model-scope objections are superseded.  A literal impossibility theorem
over every conceivable model is false: block-diagonal unbounded operators and function algebras
containing the sector idempotent are countermodels.  The revision states those countermodels and
proves the strongest valid replacement:

1. For every invariant-domain operator realization,
   `norm ([D,(1+m)/2]x) = norm (D_odd x)`.  Projector Lipschitz regularity is therefore equivalent
   to boundedness of the odd channel; for unbounded `D`, every repair moves all unboundedness to
   the commuting even channel.
2. For every unital complex function subalgebra, the sector idempotent belongs to the algebra if
   and only if arbitrary algebra elements can be patched independently across the sector and its
   complement.
3. P2 remains uniform over every anti-Real bivariant realization, and P4 remains exact over every
   completed self-dual analytic family.  The four channels are thus classified by parity
   decoupling, sector patching, Clifford parity, and multiplicity excess.

The separate ingredients are positioned honestly: operator parity is compared with unbounded
`KK` theory, and idempotent patching with Peirce decomposition.  Novelty is claimed only for the
combined Real-corona classification and its four exact recipients.

### Verification disposition

- New module and facade elaborate unconditionally.
- Targeted builds of `RealCoronaModelCompleteEvasionClassification` and
  `RealCoronaFourProblemsResolution` pass.
- All eight new declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- New module contains no `sorry`, `admit`, custom `axiom`, `opaque`, or `unsafe` declaration and is
  wired through the `RHTower` umbrella.
- Claim trace covers both new classification theorems and their exact norm/membership identities.
- PDF: 22 pages; zero overfull boxes, undefined references, or internal verification references;
  all pages visually inspected.  One benign first-page underfull vertical box remains.

No mathematical objection or open dependency remains in the paper's stated categories.
