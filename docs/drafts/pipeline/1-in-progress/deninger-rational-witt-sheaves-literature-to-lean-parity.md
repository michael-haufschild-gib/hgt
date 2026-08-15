# Deninger rational-Witt sheaves literature-to-Lean parity

- **ID:** `deninger-rational-witt-sheaves-literature-to-lean-parity`
- **Stage:** 1-in-progress
- **Type:** PRIMARY-LITERATURE COVERAGE AUDIT
- **Route:** L — rational-Witt source foundation
- **Primary source:** Christopher Deninger, *Rational Witt vectors and associated sheaves*,
  arXiv:2508.05329v1 (7 August 2025).

## Why this is on Route L

The paper is newer than the rational-Witt implementation used by Route L and proves structural
facts about the exact source functor: localization, Galois descent, sheafification, the
Hazewinkel ind-ring scheme, and finite-correspondence interpretation.  These are source
theorems, not optional analogies.

## Primary-source theorem inventory

The v1 source contains thirty theorem-level declarations:

- §1: three propositions, six theorems, three corollaries, and one lemma, including Proposition
  1.1 and Theorem 1.2.
- §2: two propositions, two lemmas, one theorem, and one corollary.
- §3: two propositions and two theorems, including Theorems 3.3 and 3.4.
- §4: six propositions, three corollaries, and one theorem/corollary chain for sheafified reduced
  monoid algebras and rational Witt vectors.
- §5: one theorem and one proposition identifying rational Witt vectors of a normal domain with
  universally integral finite correspondences.

Exact numbering/statements are being transcribed from arXiv source.  Each result will receive a
closed arithmetic specialization before Route L returns to conjectural frontier work.

## Confirmed corpus gap

`DeningerRationalWittFiniteEvaluationBridge.lean` defines
`DeningerPrimeComplexifiedRationalWittPresentation` to be the complex monoid algebra of
algebraic-closure units and cites the published identification with `W_rat`.  It does not define
the rational Witt ring or prove that identification.  Therefore the 2025 source theorems are not
formalized by that `Presentation` abbreviation.

`DeningerRationalWittSource.lean` now constructs the literal source underlying additive group:
the kernel of evaluation at zero on the units of `A[T]` localized at polynomials with constant
coefficient one.  It proves that this localization embeds into `A[[T]]` over every commutative ring
and that every kernel element has a normalized `P/Q` representative with `P(0)=Q(0)=1`.  This
closes the missing localized-rational-function carrier.  It also constructs coefficientwise
functoriality, proves identity/composition and Teichmüller naturality, proves preservation of
monomorphisms, and gives the literal injective inclusion into `1+TA[[T]]`.  The ambient canonical
big-Witt multiplication is now supplied over every commutative ring by
`DeningerBigWittRing.lean`, including rings with nilpotents. The literature-level word
"canonical" is no longer only a label: `DeningerBigWittCanonicity.lean` proves Lenstra's global
uniqueness theorem. Every functorial multiplication distributive for literal series multiplication
and satisfying `[a][b]=[ab]` equals the constructed gcd--lcm product. Naturality itself yields a
finite universal integer polynomial for each output coefficient, so no continuity or target ghost
injectivity premise is imported.
`DeningerRationalWittCanonicalMultiplication.lean` now proves the formerly missing distinct hard
statement: the literal rational subcarrier is closed under ambient multiplication over every
commutative ring.  It constructs an explicit fixed-degree resultant product, descends its
big-Witt compatibility through a universal integer polynomial ring, gives the cross-product
fraction representative, and transfers the resulting image subring back to a literal
commutative-ring carrier. `DeningerRationalWittLocalization.lean` now closes Proposition 1.1 at
its full arbitrary-ring strength: coefficient localization is exactly localization at the
Teichmüller submonoid, including with nilpotents, zero divisors, and a noninjective coefficient
map.
The reduced-monoid-algebra comparison is supplied by the algebraically closed-field modules below.

`DeningerRationalWittAlgebraicallyClosedPresentation.lean` now constructs the actual additive
comparison `ℤ[Kˣ] → W_rat(K)` for a field `K`; it does not alias `W_rat(K)` to the presentation.
For every algebraically closed field it proves the exact normalized factorization

`P(0)=1  ⇒  P(T)=∏_{r∈roots(P)}(1-r⁻¹T)`

and uses this to prove comparison-map surjectivity.  The closed specialization to
`K = AlgebraicClosure (ZMod p)` says every literal rational Witt vector is represented by a finite
integral sum of nonzero Teichmüller atoms.  This is new source-level parity: it closes the
surjective half of the field case of Deninger's reduced-monoid-algebra comparison.

The same module now also proves the injective half over every field.  Roots of a finite product of
`1-aT` recover the complete atom multiset; every integral group-ring element is a difference of two
positive atom sums.  Hence the literal additive comparison is an equivalence over every
algebraically closed field, including a closed arithmetic-closure specialization.

`DeningerRationalWittAlgebraicallyClosedRing.lean` resolves the notation collision between
rational-function multiplication (Witt addition) and Witt multiplication by wrapping the literal
carrier.  It transports a `CommRing` structure across the proved comparison, proves that ring
addition is exactly literal rational-function multiplication, and proves `[a] * [b] = [ab]` for
all field elements, including zero.  It gives a closed ring equivalence

`ℤ[(AlgebraicClosure (ZMod p))ˣ] ≃+* W_rat(AlgebraicClosure (ZMod p))`.

Thus the field-level reduced-monoid-algebra theorem is now formalized as an actual literal-carrier
ring equivalence, not merely a presentation convention.

`DeningerRationalWittLiteralGaloisDescent.lean` next proves the integral fixed-point theorem on
`ℤ[(AlgebraicClosure (ZMod p))ˣ]` and conjugates the action through that literal ring equivalence.
For every literal rational Witt vector over the arithmetic closure it proves unconditionally

`Frobenius(w)=w ↔ ∀g ∈ Gal(AlgebraicClosure(F_p)/F_p), g(w)=w`.

This removes the earlier presentation-only qualifier from the fixed-point equivalence.

`DeningerRationalWittBaseFieldDescent.lean` now closes the exact prime-field specialization of
Theorem 1.2, equation (4).  It proves unconditionally that

`Frobenius(w)=w ↔ w lies in image(W_rat(F_p) → W_rat(AlgebraicClosure(F_p)))`.

The forward proof does not descend Teichmüller atoms individually (which would be false).  It
canonically separates positive and negative atom multiplicities, proves both multisets are
Frobenius-stable, multiplies each orbit into a normalized Frobenius-fixed polynomial, descends its
coefficients to `F_p`, and reconstructs an explicit literal normalized fraction over `F_p`.  The
reverse proof establishes naturality of the literal comparison under coefficient automorphisms.
Thus base-field image identification is closed.  It does not establish generic-domain
inseparability or integral-closure descent; the unrestricted version is refuted below.

`DeningerRationalWittPerfectFieldGaloisDescent.lean` strengthens that prime-field result to every
perfect field `K`, proving the exact field case of Theorem 1.2, equation (4):

`W_rat(K) = W_rat(AlgebraicClosure(K))^Gal(AlgebraicClosure(K)/K)`.

The proof descends invariant normalized numerator and denominator coefficients using the infinite
Galois fixed-field theorem.  It is literal-carrier descent, not merely an equality in the reduced
monoid-algebra presentation.  This proves the field case, not the source's unrestricted
integral-domain equality, which is refuted below.  Remaining legitimate work is a corrected
normal-domain theorem and the inseparability-divisibility subring required when the quotient field
is imperfect.

`DeningerRationalWittPerfectFieldRing.lean` upgrades this carrier equality to the literal ring
statement.  It constructs the absolute-Galois fixed subring of the algebraic-closure Witt ring,
proves the base literal carrier equivalent to it, transports the commutative ring structure, and
verifies both literal rational-function addition and `[a] * [b] = [ab]`.  Hence the perfect-field
case now has an actual fixed-subring ring equivalence rather than only an existential image theorem.

`DeningerRationalWittAICDomainComparison.lean` closes the older Deninger Proposition 1.1(a)
comparison that the 2025 paper invokes for the integral closure.  For every integrally closed
domain `A` whose quotient field is algebraically closed, it proves an additive equivalence

`ℤ[A \ {0}] ≃+ W_rat(A)`

on the literal localized-polynomial carrier, transports the corresponding commutative-ring
structure, and proves both literal rational-function addition and `[a] * [b] = [ab]`.  The
surjectivity proof is not a field-case alias: for every normalized polynomial over `A`, the inverse
of each quotient-field root satisfies the monic reverse polynomial, hence is integral and descends
to `A`; algebraic closedness then yields exact factorization into nonzero base-ring Teichmüller
atoms.  This is the aic-domain foundation used by Theorem 1.2.  It does not yet prove the 2025
paper's Proposition 1.1 localization theorem by itself; that theorem is now closed separately by
`DeningerRationalWittLocalization.lean`. The generic-domain fixed-ring intersection and
inseparability statement is false for nonnormal domains, as recorded below.

`DeningerRationalWittFieldIntersection.lean` closes Corollary 1.10(1) (source label `t1.8`) for every field extension
`L/K` on the literal carriers:

`W_rat(L) ∩ W(K) = W_rat(K)` inside `W(L)`.

The Lean statement expresses both intersections as equality of images under the proved injective
coefficient maps.  Its proof splits `K → L` by a `K`-linear retraction and applies that retraction
coefficientwise to an arbitrary normalized `P/Q` over `L`.  Linearity commutes with multiplication
by the base power series, producing normalized numerator and denominator in `K[T]`.  This is a
direct, closed descent proof and does not assume Kronecker's Hankel theorem.  Corollary 1.10(2),
Fatou-domain descent, is now closed by the next module.

`DeningerRationalWittFatouIntersection.lean` formulates the source Fatou equality literally as the
descent of every localized polynomial over `Frac(A)` whose power series lies over `A`.  This is a
property of all of `A[T]_S`, not a renamed rational-Witt intersection premise.  It proves that a
localized element with evaluation one is already a unit, derives fraction-field rational-Witt
descent from the Fatou property, and then proves Corollary 1.10(2) for every injective extension of
domains `A → B`:

`W_rat(B) ∩ W(A) = W_rat(A)` inside `W(B)`.

The proof maps through `Frac(B)`, applies the already formalized field-intersection theorem to
`Frac(A) → Frac(B)`, uses Fatou descent back to `A`, and reflects equality through the injective
map `B → Frac(B)`.  It also adds functorial composition and injectivity for literal big-Witt
additive maps.  No Noetherian, normality, separability, or Hankel-rank premise is introduced.

`DeningerRationalWittFieldEqualizer.lean` closes Corollary 1.12(1) (source label `t1.10`) for every field extension
`L/K` on the literal rational-Witt carrier:

`W_rat(K) = Eq(W_rat(L) ⇉ W_rat(L ⊗_K L))`.

Equality of the two tensor-square pullbacks descends every power-series coefficient using
mathlib's faithfully-flat effectiveness theorem
`K → L ⇉ L ⊗_K L`.  The resulting power series over `K` is then converted to a literal rational
presentation by the already proved field-intersection theorem.  Conversely, the two pullbacks of
every base vector agree by functorial composition and the tensor-product algebra relation.  The
proof does not assume fpqc descent for `W_rat`; it proves this field equalizer directly.

`DeningerRationalWittNilpotentKernel.lean` closes Remark 1.3.  It constructs the actual quotient
ring `ℤ[A]/((0))`, descends the Teichmüller comparison to its underlying additive group, and proves
the advertised kernel witnesses.  If `a ≠ 0` and `a² = 0`, the class `2(a) - (2a)` is nonzero but
maps to zero.  If `A` has characteristic a prime `p`, `a ≠ 0`, and `a^p = 0`, then `[a]` is nonzero
in literal `W_rat(A)`, `p(a)` is nonzero in the reduced monoid algebra, and `p[a] = 0`.  The module
deduces noninjectivity of both the comparison and `p`-multiplication; all quotient nonvanishing
claims are proved coefficientwise.

`DeningerDeterminantalLaplace.lean` and `DeningerHazewinkelHankelDescent.lean` close the next hard
§2 block.  A division-free exterior-product proof establishes `I_(r+s) <= I_r I_s` and
`I_(n*k) <= I_n^k` for arbitrary infinite matrices over arbitrary commutative rings.  Applied to
the universal Hankel matrix, it proves Lemma 2.2 exactly:
`J_(n*k-1) <= J_(n-1)^k`.  For every ring map with `(ker f)^k=0`, the same containment proves the
rank bound `rank H(map f w)<n -> rank H(w)<n*k` and finite-Hankel-rank cartesianity.  Explicit
coefficient lifts along surjective ring maps then prove formal smoothness of `W_J`, while subtype
uniqueness proves the formal-étale unique lifting property of `W_J -> W`.  Thus Proposition
2.1(c,d) is now unconditional Lean over nonreduced rings; no ghost-injectivity or reduced-target
shortcut is used.

`DeningerRationalWittHazewinkelHankel.lean` closes Proposition 2.1(a) and Proposition 2.10.  Every
normalized rational fraction now produces an explicit eventual coefficient recurrence; strong
induction converts it into finite Hankel-column generation, and rectangular matrix factorization
annihilates the next minor over every commutative ring.  Hence the literal inclusion
`W_rat(A) ⊆ W_J(A)` no longer relies on a domain reduction or Kronecker as a black box.  For a
nilpotent kernel `(ker f)^k=0`, a separate Leibniz proof shows every `(k+1)` Hankel minor of a
big-Witt kernel vector vanishes: every determinant monomial has at least `k` positive-index kernel
factors, with repeated selectors dispatched by alternatingness.  Lean packages the resulting
equalities `W(ker f)=W_J(ker f)=W_J^{≤k}(ker f)` together with Hazewinkel-map surjectivity, and
specializes them to the nilradical quotient.  This is exact §2 literature parity, not an RH
advance; it removes another source-algebra infrastructure ambiguity before returning to the
singular source-to-physical frontier.

The next source claim cannot be formalized as written.  Equation (15), Lemma 2.6, and Theorem 2.8
place both Witt addition and Witt multiplication of stages `(n,m)` in stage `n+m`.
`DeningerHazewinkelStageBoundCounterexample.lean` proves this false over `ℤ`.  If `E_r` is the
Witt-additive sum of `r` copies of `[1]`, then its literal series is `(1-T)^r`, its exact
Hazewinkel stage is `r+1`, and `E_r⊙E_s=E_(rs)`.  Hence stage-`3` `E_2` times stage-`5` `E_4`
has exact stage `9`, not the asserted target stage `8`.  The nonzero top minor is proved
symbolically by row reversal and triangularity.  The qualitative ind-subring conclusion may
survive with a corrected multiplicative stage function; its published `n+m` multiplication
factorization and corresponding ideal containment do not.  This is recorded as a failed-route
card with the exact packet-stage law as formalized positive survivor.

The corrected qualitative closure has now been reduced to its exact commutative-algebra core.
`DeningerHazewinkelCorrectedRationalStage.lean` constructs a rational presentation of the product
and proves the uniform stage bound

`B(n,m) = (n-1)(m-1) + nm + 1`

over every commutative ring, including nilpotent rings. `DeningerKroneckerFieldStage.lean` proves
the full field Kronecker equivalence between Hankel rank `< n` and a normalized rational
presentation of stage `n`, then derives the corrected field multiplication bound.
`DeningerHazewinkelReducedMultiplication.lean` descends through all prime quotients: over an
arbitrary ring every corrected-size product minor is nilpotent, and over a reduced ring it
vanishes. These are new closed theorems; none imports Deninger's false additive stage estimate.

For nonreduced targets, `DeningerHazewinkelUniversalMultiplicationDescent.lean` constructs the
two-block universal coordinate ring and proves that reducedness of its quotient forces the exact
corrected multiplication rank after evaluation into every target ring, nilpotents included.
`DeningerHazewinkelUniversalQuotient.lean` proves positive-stage characteristic zero directly from
tail containment. Finally, `DeningerHazewinkelPairTensorEquiv.lean` gives explicit mutually inverse
ring maps and the canonical equivalence

`ℤ[X,Y]/(J_n(X)+J_m(Y)) ≃+* (ℤ[X]/J_n) ⊗_ℤ (ℤ[Y]/J_m)`.

It also proves reducedness equivalent across this isomorphism. Consequently no Witt, descent, or
nilpotent-target ambiguity remains. `DeningerCharacteristicZeroTensorReduced.lean` now removes the
entire tensor-product input: it proves that tensor products of arbitrary field extensions over a
perfect field are reduced, then proves that `A ⊗_ℤ B` is reduced for arbitrary characteristic-zero
domains `A,B`. The proof handles non-finitely-generated field extensions by finitely generated
subalgebra descent and handles finitely generated extensions by a separating transcendence basis.
`DeningerHazewinkelPrimeReduction.lean` consequently reduces corrected multiplication over every
commutative ring, nilpotents included, to one theorem only:

`∀ n > 0, (deningerHazewinkelIdeal n).IsPrime`.

The first positive case is closed in `DeningerHazewinkelStageOnePrime.lean`: `J₁` is identified
exactly with the kernel of `X_j ↦ T^(j+1)` into `ℤ[T]`. This also gives the unconditional stage-one
product law `rank(H(u))<2 ∧ rank(H(v))<2 ⇒ rank(H(u⊙v))<3` over every commutative ring.
`DeningerHazewinkelLeadingLocalization.lean` formalizes the next all-stage localization layer. An
explicit equal-weight `n`-atomic rational moment sequence annihilates `J_n`; its leading minor is a
product of two Vandermonde determinants and a nonzero diagonal determinant. Hence Hazewinkel's
leading determinant `D_n` survives in `ℤ[X]/J_n` for every `n>0`. The module also proves the exact
localization criterion: regularity of `D_n mod J_n`, together with integrality after inversion,
implies primeness. The remaining §2 core is therefore neither tensor reducedness nor mere
nonvanishing. `DeningerHazewinkelLocalizedCoordinates.lean`,
`DeningerHazewinkelLocalizedRetraction.lean`, and
`DeningerHazewinkelLocalizedEquivalence.lean` construct the finite coefficient chart, prove both
coordinate composites, and identify the localized universal stage with an explicit localized
polynomial domain. The sole remaining §2 core is Hazewinkel's integral Sylvester saturation theorem
`(J_n : D_n) = J_n` for general `n`. Appendix A.1 is now formal: the Cramer/adjugate form of
Sylvester exchange yields the special-minor containment
`D_n J_n^fixed ≤ K_n ≤ J_n^fixed ≤ J_n`. Appendix A.2 still requires the realization-theoretic
equality `J_n^fixed = J_n` and integral saturation of that fixed-row ideal.

## Falsified source theorem: arbitrary-domain perfect Galois descent

The perfect-quotient-field assertion in displayed Theorem 1.2 (source label `t1.1`, equation label
`eq:4`) is false for arbitrary integral domains.  Let

`A = ℚ[X²,X³] = {P ∈ ℚ[X] | coeff_X(P)=0}`

and let `t=X³/X²` in `Frac(A)`.  Then `t²=X²`, so `t` is integral over `A`, while comparison of the
`X³` coefficient in `aX²=X³` proves `t∉A`.  The Teichmüller vector `[t]` comes from the absolute
normalization and, because `Frac(A)` has characteristic zero and hence is perfect, its lift to an
algebraic closure is fixed by every absolute Galois automorphism.  It cannot come from
`W_rat(A)`: functoriality into power series would force its degree-one coefficient `-t` to lie in
the image of `A`.

`DeningerRationalWittDomainDescentCounterexample.lean` formalizes every part of this counterexample
on the literal carrier.  Its final theorem
`deningerCuspPerfectGaloisFixed_counterexample` simultaneously proves Galois fixedness, an absolute
normalization preimage, and absence of a base rational-Witt preimage.  The module also proves the
sharp structural survivor

`deningerRationalWittTeichmullerDescent_implies_integralClosedness`:

if every integral element of `Frac(A)` has a Teichmüller preimage from `W_rat(A)`, then every such
element lies in `A`.  Thus the source descent conclusion itself forces integral closedness;
normality is a necessary hypothesis, not a technical proof gap.  No Lean formalization may state
the published arbitrary-domain equality as an axiom or hypothesis disguised as infrastructure.

`DeningerRationalWittNormalDomainGaloisIntersection.lean` now proves the sharp corrected theorem.
For every integrally closed domain `A` with perfect fraction field, a literal rational-Witt vector
over the algebraic closure is absolute-Galois-fixed and comes from the absolute normalization iff
it comes from `W_rat(A)`.  The forward proof transports the normalization presentation to the
reduced monoid algebra, proves every positive and negative atom integral over `A`, descends the two
canonical Galois-stable atom polynomials to `Frac(A)`, and applies normality coefficientwise.
No Fatou-domain premise or desired descent conclusion is assumed.  Together with the cusp module,
this closes the exact corrected perfect-quotient-field intersection and proves normality sharp.

## Newly closed presentation theorem

`DeningerRationalWittCyclotomicExhaustion.lean` proves two global facts that the previous finite
packet modules did not provide:

- every unit of `AlgebraicClosure (ZMod p)` has finite order prime to `p`, hence lies in one of the
  chosen finite cyclotomic root embeddings;
- every element of the full complexified monoid-algebra presentation, and every
  arithmetic-Frobenius-fixed element, descends to one finite cyclotomic stage (fixed at that stage
  in the latter case).

These are closed arithmetic theorems about the concrete presentation and remove a real gap between
the finite packet tower and its global union.  They do **not** identify that presentation with
literal `W_rat(AlgebraicClosure (F_p))`, so they do not count as Proposition 1.1, Theorem 1.2, or
any other 2025 rational-Witt theorem.

`DeningerRationalWittGaloisFixedDescent.lean` now closes the next presentation-level gap.  It proves
that every absolute Galois automorphism agrees with one arithmetic Frobenius power on any finite
cyclotomic stage, using restriction to a finite intermediate field.  Combining this with global
cyclotomic exhaustion gives the unconditional equivalence

`Frobenius(w) = w ↔ ∀ g ∈ Gal(AlgebraicClosure(F_p)/F_p), g(w) = w`.

This is the perfect-prime-field Galois fixed-point theorem on the concrete complexified
monoid-algebra presentation.  It is not yet the paper's literal equality with `W_rat(F_p)` because
the missing rational-Witt comparison is logically prior.

## Formalization order

1. **Open hard §2 core.** Prove Hazewinkel's integral Sylvester saturation
   `(J_n : D_n) = J_n`, specifically fixed-row generation plus saturation after the now-formal
   Sylvester exchange containment; then close `J_n.IsPrime` for every positive `n`. Localized
   coordinate-domain theorem, tensor reducedness, and stage `n=1` are already closed.
2. **Closed.** Imperfect-field inseparability-divisibility classification and its sharp
   normal-domain/normalization descent consequence are Lean-formalized. No perfectness hypothesis
   remains in the corrected theorem.
3. Replace presentation-only claims in finite packet modules by comparison maps to the constructed
   rational-Witt ring, then formalize sheaf and correspondence theorems in source order.

## Log

- 2026-08-13 — removed the characteristic-zero tensor-product premise completely. Lean proves
  reducedness of arbitrary field tensor products over perfect fields and of `A ⊗_ℤ B` for all
  characteristic-zero domains. General corrected multiplication now depends only on one-stage
  Hazewinkel primeness. Proved `J₁` prime by an exact monomial-moment kernel presentation and
  obtained unconditional stage-one multiplication over arbitrary rings. For every positive `n`,
  constructed an explicit rational rank-`n` moment evaluation annihilating `J_n` and proved the
  leading determinant survives by Vandermonde factorization. Formalized the regular-element
  localization implication. Constructed the finite localized coefficient chart, derived the
  universal recurrence from arbitrary Hankel minors by a Schur complement, proved both coordinate
  composites, and obtained a ring equivalence with an explicit localized polynomial domain. Exact
  open theorem is now only integral Sylvester saturation/regularity of the surviving determinant.
  Formalized Appendix A.1 as a general determinant-exchange identity and its Hankel application:
  `K_n ≤ J_n^fixed ≤ J_n` and `D_n J_n^fixed ≤ K_n`. This separates remaining A.2 into
  fixed-row generation and saturation, with neither assumed.

- 2026-08-13 — proved the corrected rational multiplication bound, field Kronecker equivalence,
  nilpotence of corrected product minors over arbitrary rings, and exact vanishing over reduced
  rings. Constructed the universal two-block quotient and proved its arbitrary-target descent.
  Explicit inverse maps now identify that quotient with
  `(ℤ[X]/J_n) ⊗_ℤ (ℤ[Y]/J_m)` and transport reducedness both ways. At that checkpoint §2 source
  core was Hazewinkel primeness plus reducedness of characteristic-zero field tensor products; the
  next log entry records elimination of the latter.

- 2026-08-13 — refuted the published additive stage bound for Witt multiplication in equation
  (15), Lemma 2.6, and Theorem 2.8.  Lean proves the general exact law
  `stage(E_r)=r+1`, `E_r⊙E_s=E_(rs)` and the concrete stage `3 × 5 -> 9`, contradicting claimed
  stage `3+5=8`.  Corrected qualitative ind-ring closure remains open.

- 2026-08-13 — closed Proposition 2.1(a) and Proposition 2.10 over arbitrary commutative rings.
  Normalized fractions yield explicit recurrences and rectangular Hankel factorizations; nilpotent
  big-Witt kernels satisfy the sharp rank-at-most-`k` bound by a formal Leibniz ideal-power count.
  Exact kernel equalities, surjectivity, and the nilradical specialization are umbrella-reachable.

- 2026-08-13 — formalized generalized Laplace containment without factorial division, specialized
  it to Hazewinkel's universal Hankel ideals to prove `J_(nk-1) <= J_(n-1)^k`, and derived
  Deninger's nilpotent-kernel rank multiplication, cartesian square, formal smoothness, and formal
  étaleness.  All targets are arbitrary commutative rings, including nilpotents.

- 2026-08-13 — closed the imperfect-field clause. Minimal-polynomial roots form complete absolute-
  Galois orbit blocks with multiplicity exactly the finite inseparability degree; invariant
  divisible multisets peel into reversed-minimal-polynomial factors. Conversely every mapped
  base polynomial has root multiplicities divisible by that degree. This yields the exact
  field-image classification and, after normalization incidence plus normality, a corrected
  arbitrary-characteristic domain theorem with no perfectness assumption.

- 2026-08-11 — primary arXiv search located this 2025 paper; existing Route-L map did not cite it.
  Initial audit found that the corpus names a rational-Witt presentation but does not construct
  `W_rat` or prove the new paper's comparison theorems.
- 2026-08-11 — proved global finite-stage exhaustion and fixed finite-stage descent for the
  complexified arithmetic-closure monoid-algebra presentation.  Literal rational-Witt comparison
  remains the source-level blocker.
- 2026-08-11 — proved that arithmetic-Frobenius invariants in the full presentation are exactly
  absolute-Galois invariants.  Proof passes through finite intermediate fields and uses no descent
  hypothesis; transport to literal `W_rat` remains open.
- 2026-08-11 — constructed the literal localized-polynomial/kernel carrier, proved its faithful
  embedding into formal power series, and proved normalized-fraction existence.  Witt-ring
  multiplication and comparison remain the next hard source layer.
- 2026-08-11 — completed source functoriality, monomorphism preservation, Teichmüller naturality,
  and the literal injection into the big-Witt additive carrier.  Constructed the reduced
  monoid-algebra comparison over fields and proved it surjective over every algebraically closed
  field by exact root factorization, including the closed arithmetic-closure specialization.
  Injectivity/unique factorization was then proved by root-multiset recovery and integral
  positive/negative atom decomposition.  Transported the commutative Witt-ring structure to the
  literal carrier and proved the full Teichmüller multiplication law.  Field-level comparison is
  now closed; localization and literal Galois descent are next.
- 2026-08-11 — proved integral and literal-carrier Frobenius/Galois fixed-point equivalence over
  the prime-field arithmetic closure.  The proof uses finite support plus finite-field Frobenius
  generation, and transports through the actual rational-Witt ring equivalence.  Base-field image
  identification, not presentation transport, is now the exact Galois-descent blocker.
- 2026-08-11 — proved exact literal base-field image descent, the closed prime-field specialization
  of Theorem 1.2, equation (4).  Frobenius-stable positive/negative atom orbit products descend coefficientwise
  to normalized numerator/denominator polynomials over `F_p`; comparison naturality proves the
  converse.  The arithmetic-closure fixed ring is now exactly the image of literal `W_rat(F_p)`.
- 2026-08-12 — generalized literal fixed-point descent from prime fields to every perfect field,
  closing the field case of Theorem 1.2, equation (4).  Absolute-Galois invariance of canonical orbit-product
  polynomials descends coefficients through infinite Galois theory and reconstructs a base-field
  normalized fraction.  Integral-domain intersection/integral-closure descent remains open.
- 2026-08-12 — constructed the perfect-field literal rational-Witt `CommRing` as the proved
  absolute-Galois fixed subring over the algebraic closure.  The ring equivalence preserves the
  literal normalized-rational-function carrier; Witt addition and Teichmüller multiplication are
  verified explicitly.
- 2026-08-12 — proved the exact aic-domain reduced-monoid-algebra comparison cited in the 2025
  source.  Reverse-polynomial integrality descends inverse roots from the algebraically closed
  quotient field to the integrally closed domain; this gives literal normalized factorization,
  comparison bijectivity, the induced Witt-ring equivalence, and the full Teichmüller
  multiplication law.  The current paper's localization proposition remains open; the
  arbitrary-domain Galois intersection was subsequently refuted rather than left as a proof gap.
- 2026-08-12 — proved Corollary 1.10(1) exactly for every field extension.  A coefficientwise linear
  retraction descends a normalized rational presentation whenever its power series lies over the
  base field, yielding equality of the literal rational-Witt/base-big-Witt intersection with the
  image of base rational Witt vectors.  No Hankel-rank premise or separability hypothesis is used.
- 2026-08-12 — proved Corollary 1.10(2) exactly for every injective extension of domains with Fatou
  base.  The Fatou condition is stated on the full localized-polynomial carrier; fraction-field
  intersection and unit reflection then give the rational-Witt intersection in the extension.
- 2026-08-12 — proved Corollary 1.12(1) exactly for every field extension.  Faithfully-flat
  effectiveness descends the coefficients equalized in `L ⊗_K L`; field intersection then
  reconstructs the base rational-Witt vector without assuming the desired fpqc sheaf property.
- 2026-08-12 — formalized Remark 1.3 on the exact reduced monoid-algebra quotient and literal
  rational-Witt carrier.  The square-zero class `2(a)-(2a)` and prime-characteristic class `p(a)`
  are proved nonzero before their images are proved zero; noninjectivity of both `ω` and
  `p`-multiplication follows unconditionally from the stated ring-theoretic hypotheses.
- 2026-08-12 — refuted the paper's arbitrary-domain perfect-quotient-field Galois-descent theorem
  by the cusp ring `ℚ[X²,X³]`.  Lean proves the integral element `t=X³/X²` yields an
  absolute-Galois-fixed Teichmüller vector coming from the absolute normalization but not from the
  base rational-Witt carrier.  The positive survivor is stronger than a counterexample:
  Teichmüller descent for all integral fraction-field elements forces integral closedness.
- 2026-08-12 — closed canonical big-Witt multiplication over every commutative ring, with universal
  integer-polynomial descent of all ring laws and exact preservation/reflection of Teichmüller
  nilpotence.  Proposition 1.1 now reduces to proving that normalized rational functions form a
  subring of this ambient construction and that coefficient localization is the corresponding
  Teichmüller localization.
- 2026-08-13 — closed the missing canonicity half of Lenstra's theorem. Lean packages arbitrary
  natural distributive Teichmüller multiplication laws, proves each output coefficient is the
  evaluation of a finite universal integer polynomial, truncates beyond its actual variable
  support, splits finite Euler polynomials after an injective algebraic-closure map, and proves the
  law type is a subsingleton over arbitrary commutative rings. Nilpotent targets enter only by
  universal evaluation and are not reduced or embedded into fields.
- 2026-08-15 — exposed the defining gcd--lcm identity as an unconditional public Lean theorem for
  literal positive-degree Euler factors. For all commutative rings, including nonreduced rings, the
  canonical product of degrees `m,n` is the `gcd(m,n)`-fold Witt sum of the degree `lcm(m,n)` factor
  with coefficient `a^(lcm/m)b^(lcm/n)`. Ghost injectivity is used only in the free integer
  polynomial source before natural evaluation into the target.
- 2026-08-12 — closed the first half of that reduction.  Fixed-degree resultants multiply
  normalized polynomials without degree-specialization failure; algebraically closed splitting,
  universal integer-polynomial descent, and coefficient evaluation prove compatibility over
  arbitrary rings including nilpotent ones.  Cross-products close all normalized fractions, and
  the literal carrier now has a functorial canonical `CommRing` embedded in `W(A)`.  Deninger
  At this checkpoint Proposition 1.1 reduced to the localization universal property; the next log
  entry records its closure.
- 2026-08-12 — closed Proposition 1.1 at full arbitrary-ring strength.  Universal-polynomial
  descent proves `[b]⊙f(T)=f(bT)` without ghost injectivity; weighted common-denominator lifts give
  surjectivity; finite product annihilators give the kernel condition when coefficient localization
  is noninjective.  Lean installs `IsLocalization ([M]) W_rat(M⁻¹A)` and the canonical ring
  equivalence. Nilpotents and zero-divisor denominators are retained.
- 2026-08-12 — proved the corrected normal-domain Galois intersection.  Absolute-normalization
  incidence makes canonical positive and negative atom-polynomial coefficients integral; perfect
  fixed-field descent lands them in `Frac(A)`; normality returns them to `A`.  The cusp
  counterexample proves this repair sharp.  Remaining source-literature frontier starts with the
  imperfect-field inseparability-divisibility subring, not generic multiplication or perfect-field
  normal-domain descent.
