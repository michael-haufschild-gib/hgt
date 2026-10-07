# Joint cubic Galois groups of the actual marked Xi channels

- **ID:** RH-XIJCG-20261007
- **Stage:** 3-formalized; ten source leaves and all 59 public axiom closures audited
- **Parent:** `../1-in-progress/xi-marked-joint-monodromy.md`
- **Predecessor:** `../3-formalized/xi-cubic-lift-strip-decay.md`
- **Verdict:** BRIDGE; actual finite joint cubic quotient closed, no scientific novelty certified

## Exact conjecture

Let K be the actual global meromorphic plane field. For every finite set S of
distinct integers n>=2, let L_S be the compositum, in one algebraic closure of K,
of the splitting fields of

    Q_n(X)=X^3-3X-(2+4 Xi(s) exp(-s log n)).

The restriction map Gal(L_S/K) -> product_(n in S) S3 is an isomorphism.
In particular [L_S:K]=6^|S|. This is a finite nonabelian quotient statement,
not the full free-group monodromy conjecture C1 or an RH selection law.

Competing possibility: a higher entanglement survives despite independent
discriminant square classes. The group argument below is intended to exclude
exactly that possibility; it must be checked in the actual field construction.

## Actual inputs already located

The single-channel card proves actual irreducibility, nonsquare discriminant,
S3 and degree six. Eight final source checks and 38 public axiom audits pass.

`R:XiSignedFactorSquareClasses.signed_factor_packet_isSquare_iff` proves the
independence of Xi and every signed factor `1 +/- Xi n^(-s)` in K. Its complete
statement and proof were read. Thus the discriminant classes

    [-432 d_n(d_n+1)] = [Xi (1+d_n)]

are independent: the constant -432 and exponential mark are squares in K,
and any nonempty product retains a nonempty positive-factor packet. The same
source also proves positive-factor independence after the infinite marked
radical adjunction. No generic independence specialization is being assumed.

Corpus search completed with partial=false, complete inventory 68156, and
substantial pending/stale compiler coverage:
`/tmp/rh-xi-joint-cubic-squareclasses-search-20261007.json`.
Its broad ranked hits did not supply a ready joint-S3 theorem. Exact signed
square-class input above was verified directly in its full source proof.

## Paper mechanism

Independent discriminants give a multiquadratic subextension of L_S with group
C2^S. The discriminant square root transforms by the sign of the permutation
of the three roots. Hence the image H of Gal(L_S/K) in S3^S surjects onto C2^S.
Each coordinate projection of H is S3, by normal-extension restriction.

Here is an explicit subgroup argument, avoiding an unproved general assertion
that pairwise disjoint fields are jointly disjoint. For each i, coordinate
surjectivity gives x in H whose i-coordinate is a nontrivial three-cycle.
Put r=x^2. Every coordinate of r is even, and r_i is still nontrivial. Choose
h in H with odd sign only in coordinate i.
Conjugation by an even permutation is trivial on A3; conjugation by an odd
permutation inverts A3. Thus h r h^-1 r^-1 is identity off i and equals r_i^-2,
which equals r_i because A3 has exponent three. It generates the entire
i-coordinate A3. Repeating for every i gives A3^S <= H. Surjectivity on signs
then gives H=S3^S.

All these transports now have exact Lean proofs. The common-field sign action
is realized by extending individual radical conjugations, as recorded below.
Ten source leaves are promoted, wired and fully audited.

### Dependency-closed field and sign construction

Index labels by n+2 with n natural. For finite S, use the splitting field L of
the product of the Q_(n+2), n in S. This places all roots in one field without
assuming distinct cubics have disjoint root sets. In characteristic zero this
finite normal extension is Galois, regardless of repeated factors of the
product. Restriction is injective on the product of the individual splitting
groups because their roots generate L, and every coordinate restriction is
surjective by extension of embeddings in a normal extension.

Choose an ordering of each cubic's three distinct roots in L. Their Vandermonde
product r_n satisfies r_n^2=Delta_n, and an automorphism multiplies r_n by the
sign of its corresponding root permutation. The sign identity is exactly the
existing `vandermondeProd_comp`, with `map_vandermondeProd_ringHom` handling
the field automorphism. Reordering only conjugates the permutation coordinates.

Put c=i*sqrt(432) in C and u_n=constPlane(c)*betaElement(n). Then u_n is nonzero
and Delta_n=u_n^2*xiElement*augmentationElement(n+2). For any nonempty S,
the product of Delta_n equals a nonzero square times
xiElement^|S| times the product of the positive companions. The signed-factor
packet theorem excludes a square of that latter element. This proves the
exact independent-discriminant hypothesis, including every finite packet.

The subfield M=K(r_n:n in S) therefore has degree 2^|S| by the fully read
`H:MultiquadraticAdjoinDegree.multiquadratic_degree_and_twists`. It is Galois:
it is the splitting field in L of the product of X^2-Delta_n. Automorphisms
act on its nonzero generators by signs, giving an injection into C2^S;
the equal cardinalities make this injection surjective. Every automorphism
of M extends to L, so the joint root-permutation image has all sign patterns.
The square-and-conjugation subgroup argument above now proves the full product.
Empty S gives the base field and the trivial group separately. No simplicity
of Xi zeros, RH, or independence of generic parameters is assumed.

## Scientific and scope audit

The group argument and discriminant method are classical. Value lies in closing
an actual coupled Xi quotient using the corpus's exact signed-factor theorem.
Even success would not prove C1: larger finite covers and infinite monodromy
can retain obstructions invisible to every channel's cubic quotient.

Primary sources checked: Conrad's
[cubic Galois notes](https://kconrad.math.uconn.edu/blurbs/galoistheory/cubicquarticallchar.pdf),
Theorem 1.1 and Section 2, give the discriminant/sign mechanism. The
[Stacks Project, Section 9.27](https://stacks.math.columbia.edu/tag/09IC),
defines linear disjointness relative to embeddings into a common field; this
is why the conjecture fixes one algebraic closure. Neither source is being
cited as a theorem specifically about the actual Xi family or the full joint
conclusion; that conclusion still needs the written group argument and exact
field transport.

Further corpus search completed with partial=true, complete inventory 68158,
and substantial pending/stale compiler coverage:
`/tmp/rh-xi-joint-cubic-subdirect-search-20261007.json`. Its broad hits were not
accepted as a ready subgroup theorem. Exact source audit found
`H:VandermondeSign.vandermondeProd_comp` and
`H:VandermondeFixed.map_vandermondeProd_ringHom`; both files were read in full.
These provide the sign transport for actual enumerated roots. Mathlib's
`alternatingGroup.commutator_perm_eq` found by source search requires at least
five letters and is not applicable to S3. The square trick above avoids it.

- [x] Finish predecessor's final audits and cleanup.
- [x] Complete corpus/primary parent audit and verify all actual-field inputs.
- [x] Dependency-closed paper proof including field/topology distinctions.
- [x] Formalize actual independent discriminant classes.
- [x] Formalize joint field/group transport without added premises.
- [x] Audit every public axiom closure and actual source; record exact C1 boundary.

## Formalization checkpoint

Prepared `/tmp/rh-xi-joint-cubic-discriminants.lean`: literal transport from
the tilted cubic parameter to the existing marked factor, explicit nonzero
unit `constPlane(sqrt(432)*i)*betaElement(n)`, discriminant factorization, and
the exact finite-packet square criterion. Exact API and complete scratch checks
now pass with empty logs. This toolchain lacks `Complex.sq_sqrt`; the unit uses
the explicit constant sqrt(432)*i, whose square is -432. Promoted and wired
`R:XiCubicDiscriminantPackets`; targeted build is running.

Prepared `/tmp/rh-s3-sign-conjugation.lean`: A3 cardinality and exponent,
generation by a nontrivial even permutation, and inversion under odd
conjugation, using two explicit transpositions. No exhaustive permutation
enumeration is used. Its API/proof checks are queued in the same Lean chain.

Prepared `/tmp/rh-xi-cubic-quadratic-stage.lean`: actual discriminant roots in
the fixed algebraic closure, finite sign-stage degree 2^|S|, square-class twist
criterion, and survival of each unused discriminant. This is queued after
the group API/proof check. Neither prepared scratch is yet claimed verified.

The packet target build now passes. Generic A3 generation and odd-conjugation
inversion also pass API and scratch with empty logs, after resolving the
explicit transposition action and its involution cancellation. Promoted/wired
`H:S3SignConjugation`; targeted build will follow the current quadratic-stage
check. Prepared `/tmp/rh-s3-product-sign.lean` for the full subgroup theorem;
it has not run yet.

The quadratic-stage scratch now passes with an empty log. Its former type
inference failure was removed by fixing the index type to natural numbers and
the base/ambient fields explicitly. Promoted/wired `R:XiCubicQuadraticStage`.
The full subgroup proof also passes after a dependent exponent rewrite was
replaced with a typed `change`. Promoted/wired `H:S3ProductSign`. Both targeted
builds pass; final actual-source and axiom audits remain pending for this cycle.

Field transport refinement: the existing `H:QuadraticRootConjugation` permits
a shorter dependency-closed realization of individual signs. For coordinate i,
adjoin all other radicals to E; square-class independence keeps Delta_i
nonsquare in E. Conjugation of E(r_i)/E fixes all other radicals and negates
r_i. Restrict its scalars to K and extend to the normal ambient splitting
field. Products of these flips realize all sign patterns. This avoids a
separate normality/cardinality proof for the multiquadratic subfield.
Prepared `/tmp/rh-multiquadratic-normal-flips.lean` for this exact transport;
its API/proof checks are running. No new mathematical hypothesis was added.

The independent-radical flip API and proof now pass with empty logs. The
only extra field-tower instance is proved definitionally by equality of the
actual algebra maps. Promoted/wired `H:MultiquadraticNormalFlips`; targeted
build is queued after the current ordered-root checks. Prepared
`/tmp/rh-cubic-root-sign.lean`: discriminant radical from ordered cubic roots,
its exact square and sign covariance, and coordinate surjectivity in a normal
splitting ambient field. Prepared `/tmp/rh-s3-action-flips.lean` to combine
individual sign flips using the existing full-product subgroup theorem.

Normal flips and the ordered-root sign/covariance checks now pass; all three
target builds pass. Promoted/wired `H:CubicRootSign` and `H:S3ActionFlips`.
The simultaneous action theorem `H:CubicFamilyAction` also passes scratch and
target build: independent discriminants give surjectivity onto every S3
coordinate simultaneously in any common normal splitting ambient field.

Prepared `/tmp/rh-cubic-family-splitting.lean` for the product splitting field,
faithfulness on its union of roots, full Galois equivalence, and degree 6^|S|.
The first check needed only an explicit local root coercion and reduction of
3 factorial; both are under recheck. Prepared actual no-premise specialization
`/tmp/rh-xi-joint-cubic-galois.lean`, not yet checked. Final audits still pending.

## Final audited result

For every finite set S of natural labels (channel n means integer mark n+2),
`RHTower.xiJointCubicGaloisEquiv S` is an unconditional equivalence

    (xiJointCubicPolynomial S).Gal ≃* (S → Equiv.Perm (Fin 3)).

`RHTower.xiJointCubic_splittingField_finrank S` proves degree 6^S.card.
`xiJointCubicPolynomial_eq_prod` identifies the presenting polynomial with
exactly the finite product of the actual marked Xi cubics. The empty set is
included. No pairwise root-disjointness, simple-zero, RH or generic-parameter
independence hypothesis is present.

Promoted/wired leaves: H:S3SignConjugation, H:S3ProductSign,
H:MultiquadraticNormalFlips, H:CubicRootSign, H:S3ActionFlips,
H:CubicFamilyAction, H:CubicFamilySplittingGroup,
R:XiCubicDiscriminantPackets, R:XiCubicQuadraticStage,
R:XiJointCubicGalois. Each targeted build and each final `lake env lean`
actual-source audit passes. All 59 named public declarations have only
propext, Classical.choice and Quot.sound in their axiom closures.
All ten umbrella imports are unique. All ten obsolete proof scratches were
removed only after comparison against their promoted sources, ignoring the
added module documentation.

Evidence: `/tmp/rh-joint-cubic-final-modules.txt`,
`/tmp/rh-joint-cubic-audit-names.txt`, `/tmp/rh-joint-cubic-axioms.log`,
ten `/tmp/rh-joint-final-<Leaf>.lean.log` files (all empty), and the individual
target-build logs. Index refresh passes. Formal lint reports six unrelated
unwired leaves: R:ZetaLineResonatorLargeValues; H:ApertureConeCalculus,
ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal,
BoundaryCoronaCStarAlgebra. Thus no global lint pass is claimed. Those files
were not modified. Logs: `/tmp/rh-joint-cubic-index.log` and
`/tmp/rh-joint-cubic-lint.log`.

## Anti-theatre and next conjecture

The actual finite nonabelian quotient frontier moved: discriminant independence
now excludes every residual entanglement among these S3 extensions. This is a
classical group/Galois mechanism applied to actual corpus inputs, so scientific
novelty is not certified. It neither closes the full fundamental-group image
C1 nor supplies any critical-line selection law. The next cycle targets the
larger obstruction rather than another automatic finite-product corollary:
`../1-in-progress/xi-polynomial-left-factors.md`, classifying every polynomial
left factor of the actual exponentially tilted Xi source. A primary
Biernacki separation theorem may exclude the remaining two-fiber geometry;
its exact application and Lean proof remain under audit.
