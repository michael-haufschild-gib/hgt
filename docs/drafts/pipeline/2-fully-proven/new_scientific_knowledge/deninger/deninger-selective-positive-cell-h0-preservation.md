# Selective positive cells preserve arithmetic constants

- **ID:** `deninger-selective-positive-cell-h0-preservation`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Parent:** `deninger-derived-mw-rational-witt-coefficient`
- **Statement:** Selective positive-degree relation attachments preserve degree zero, monic
  finite-flat rational-Witt generators lift through Milnor--Witt correspondences, and the
  subsequent multiplicative rank quotient preserves the ordinary coefficient constants.

## Grading convention

All stable objects on the coefficient site use homotopy grading:
\[
 H^q_{\mathrm{arith}}(E):=\pi_q(E),\qquad q\geq 0.
\]
Thus a degree-two Steinberg class is represented by
\(\Sigma^2\mathbbm1\to E\).  This convention is essential: it makes the connective
\(t\)-structure and the first-quadrant bar spectral sequence used below unambiguous.

## Positive-cell theorem

Let \(\mathcal C^\otimes\) be a presentable symmetric monoidal stable
\(\infty\)-category with a tensor-compatible accessible \(t\)-structure.  Assume the tensor
product preserves colimits separately, connective commutative algebras are closed under
pushout, and \(\pi_0\) of a pushout of connective commutative algebras is the classical
pushout of the \(\pi_0\)-algebras.  These hypotheses hold for connective
\(E_\infty\)-ring spectra and objectwise for connective \(E_\infty\)-algebra presheaves;
sheafification gives the corresponding statement for sheaves.

Let \(A\) be a connective commutative algebra, \(K\in\mathcal C_{\geq1}\), and
\(u:K\to A\).  Put
\[
 A//K:=
 A\mathop{\otimes}^{\mathbb L}_{\operatorname{Free}_{E_\infty}^{+}(K)}
 \mathbbm1,                                                            \tag{1}
\]
where the right map is the zero augmentation.

`[PROVED HERE] [DAC_POSITIVE_CELL_PI0_INVARIANCE]`
\[
 \pi_0(A//K)\xrightarrow{\sim}\pi_0A.                                  \tag{2}
\]

### Proof

Tensor compatibility implies
\[
 \operatorname{Free}_{E_\infty}^{+}(K)
 \simeq
 \mathbbm1\oplus K\oplus\operatorname{Sym}^2(K)\oplus\cdots .
\]
Every positive symmetric power is \(1\)-connective, so
\[
 \pi_0\operatorname{Free}_{E_\infty}^{+}(K)
 \cong\pi_0\mathbbm1.
\]
The connective pushout formula for \(\pi_0\) now gives
\[
 \pi_0(A//K)
 \cong
 \pi_0A
 \otimes_{\pi_0\operatorname{Free}_{E_\infty}^{+}(K)}
 \pi_0\mathbbm1
 \cong\pi_0A.
\]
For sheaves, compute the presheaf pushout, apply the same argument objectwise, and
sheafify.  Sheafification of abelian presheaves is exact, so the resulting isomorphism is an
isomorphism of \(\pi_0\)-sheaves.

The claim is deliberately only about \(\pi_0\).  Positive cells can and generally do change
higher homotopy.

## Equivariant universal property

Let a monoid \(G\) act coherently on \(A\) and \(K\), and suppose \(u\) and the zero
augmentation are \(G\)-equivariant.  Then the action descends uniquely up to contractible
choice to \(A//K\).

### Proof

Every \(g\in G\) gives a morphism of the pushout span
\[
 A\longleftarrow\operatorname{Free}_{E_\infty}^{+}(K)
 \longrightarrow\mathbbm1.
\]
Functoriality of colimits gives the induced endomorphism of `(1)`.  Coherent multiplication
and unit homotopies descend because colimit is an \(\infty\)-functor.  Hence relations among
the \(G\)-operations remain relations after attachment.

## Monic Milnor--Witt lift theorem

Let \(X=\operatorname{Spec}A\) be normal Noetherian affine and let
\[
 Z_P=\operatorname{Spec}B,\qquad B=A[T]/(P),
\]
where \(P\in A[T]\) is monic and irreducible.  Then the integral finite-flat
correspondence \(Z_P\subset X\times\mathbb A^1\) has a canonical oriented
Milnor--Witt fundamental lift whose underlying ordinary cycle is \([Z_P]\).

### Proof

Monicity makes \(B\) finite free over \(A\), and \(P\) is a non-zero-divisor in
\(A[T]\).  Hence \(Z_P\hookrightarrow\mathbb A^1_X\) is a regular codimension-one
immersion.  Its cotangent complex has the two-term presentation
\[
 L_{B/A}\simeq
 \left[(P)/(P^2)\xrightarrow{\,dP\,}
       \Omega^1_{A[T]/A}\otimes_{A[T]}B\right].
\]
The classes of \(P\) and \(dT\) trivialize its two determinant lines, and therefore
canonically trivialize the determinant twist of the Milnor--Witt fundamental class.
Choose the unit quadratic orientation \(\langle1\rangle\).  The resulting MW Gysin
fundamental class forgets to the ordinary fundamental cycle of the regular immersion,
namely \([Z_P]\).

Deninger's finite-correspondence theorem says that these \(Z_P\) freely generate the ordinary
rational-Witt correspondence group after killing the zero section.  The lift is compatible
with the zero-section quotient.  Therefore the rank/forgetful map
\[
 \pi_0M_{\mathrm{res}}\longrightarrow W_{\mathrm{rat}}                 \tag{3}
\]
is surjective whenever \(M_{\mathrm{res}}\) receives the raw MW fundamental classes without
altering them in degree zero.

## Unit-amalgamated arithmetic corollary

Let \(\mathcal C_F^{MW,(\lambda)}\) be an intermediate connective stage in the relative
cellular presentation of the Milnor--Witt symbol algebra over the free unit algebra.  If
\[
 K_\lambda\longrightarrow\mathcal C_F^{MW,(\lambda)}
\]
is the next coproduct of positive relation cells, define
\[
 \mathcal C_F^{MW,(\lambda+1)}
 =
 \mathcal C_F^{MW,(\lambda)}
 \mathop{\otimes}^{\mathbb L}_{
   \operatorname{Free}_{E_\infty}^{+}(K_\lambda)}
 \mathbbm1.
\]
Then `(2)` gives
\[
 \pi_0\mathcal C_F^{MW,(\lambda+1)}
 \cong\pi_0\mathcal C_F^{MW,(\lambda)}.                                \tag{4}
\]
At limit stages, filtered-colimit compatibility of \(\pi_0\) gives the same conclusion.
Hence the full positive relative cellular presentation preserves degree zero.
In particular, the rank map
\(r:\mathcal C_F^{MW}\to\mathcal C_F^M\) remains
surjective on \(\pi_0\).
Its fiber \(F_{\mathrm W}\) is therefore connective, and
\[
 J_{\mathrm W}:=\tau_{\leq0}F_{\mathrm W}
 \simeq H\ker(\pi_0r)                                                   \tag{5}
\]
is discrete.  Applying `DAC_DERIVED_RANK_QUOTIENT_PI0` to
\[
 \mathcal C_F^{MW}
 \mathop{\otimes}^{\mathbb L}_{
   \operatorname{Free}_{E_\infty}^{+}(J_{\mathrm W})}
 \mathbbm1
\]
gives
\[
 \pi_0\mathcal A_F^{\mathrm{der}}
 \cong
 \pi_0\mathcal C_F^{MW}/\langle\ker(\pi_0r)\rangle
 \cong\pi_0\mathcal C_F^M.                                             \tag{6}
\]
When the ordinary Milnor comparison holds, the last ring is \(\mathbb Z\).
On an algebraically closed geometric character chart,
`DAC_GEOMETRIC_MW_RANK_COLLAPSE` gives \(\ker(\pi_0r)=0\) and makes `(6)` the identity;
there is then no rank-induced degree-one Tor problem.

Thus the degree-zero part of the proposed unit-amalgamated correction is closed.  Remaining
arithmetic construction is exactly:

1. construct the unit-amalgamated ordinary and MW cochain algebras;
2. prove their relative bar comparison with Milnor and Milnor--Witt \(K\)-theory;
3. construct twisted Rost--Schmid/Galois and archimedean rank/signature descent;
4. construct coherent Frobenius/Verschiebung actions on the full relative cell family.

## Hostile audit

- The theorem does not construct the unit-amalgamated cochain algebras.
- It does not identify any positive homotopy group after either cell attachment.
- A degree-zero relation attachment would change \(\pi_0\); positivity of
  \(K_{\mathrm{rel}}\) is indispensable.
- Full \(\mathbb A^1\)-localization is still forbidden: it kills the represented
  rational-Witt coordinate before `(1)` is formed.
- The determinant trivialization above orients a monic hypersurface fundamental class.  It
  does not by itself supply all coherent power-map Gysin compatibilities.

## References

- Jacob Lurie, *Derived Algebraic Geometry III: Commutative Algebra*, proof of Proposition
  4.2.22, especially the connective pushout formula
  \(\pi_0(A'\otimes_A A'')\cong\pi_0A'\otimes_{\pi_0A}\pi_0A''\):
  https://www.math.ias.edu/~lurie/papers/DAG-III.pdf
- Jacob Lurie, *Higher Algebra*, §§3.1.3 and 3.2.3:
  https://www.math.ias.edu/~lurie/papers/HA.pdf
- Christopher Deninger, *Rational Witt vectors and associated sheaves*, Theorem 5.1:
  https://arxiv.org/abs/2508.05329
- Frédéric Déglise, Niels Feld, Fangzhou Jin,
  *Homotopy coherent Gysin functoriality*:
  https://arxiv.org/abs/2605.01855

## Log

- 2026-07-26 — proved positive-cell \(\pi_0\)-invariance and monic MW lift.
- 2026-07-26 — corrected the arithmetic application: rational-Witt is geometry; the rank
  quotient preserves the ordinary coefficient constants.

## Lean status

### What landed

`formal/GaloisForLFunctions/RHTower/DeningerPositiveCellDegreeZero.lean`.  Axiom audit for all 5
declarations: `propext, Classical.choice, Quot.sound`.

- `deningerPositiveCell_span_le_ker`, `deningerPositiveCell_degreeZero_injective`,
  `deningerPositiveCell_quotient_injOn` — **`(2)` in its graded shadow**: attaching relations of
  positive degree means dividing by the ideal they generate, the degree-zero projection of a graded
  ring is a ring homomorphism killing every positive-degree generator, hence the whole ideal, so no
  nonzero degree-zero element dies in the quotient.  Degree zero is preserved, and — as the card
  insists — only degree zero: nothing here constrains higher degrees.
- `deningerMonicQuotient_powerBasis`, `deningerMonic_isRegular` — the two ring-theoretic inputs of
  the monic lift theorem: monicity makes `A[T]/(P)` finite free over `A` via a power basis, and a
  monic polynomial is a non-zero-divisor, which is what makes the immersion regular of codimension
  one.

### What cannot be stated in Lean, and why

The `∞`-categorical formulation of `(1)`--`(2)` — the free `E_∞`-algebra on a `1`-connective
object, the homotopy pushout, the connectivity of positive symmetric powers and the `π₀` pushout
formula — has no mathlib counterpart, so the graded-ring statement above is the available shadow.
The Milnor--Witt lift itself needs the cotangent complex, determinant twists and MW fundamental
classes; the equivariant descent needs coherent group actions.  The card therefore stays at
stage 2 with its degree-zero theorem and the monic inputs formalized.

### The equivariant universal property `[NEW]`

The previous record listed the equivariant descent under "cannot be stated ... needs coherent group
actions".  That is true of the coherent `∞`-categorical action, but the card's own proof of the
equivariant universal property is a one-categorical argument — "every `g ∈ G` gives a morphism of the
pushout span, functoriality of colimits gives the induced endomorphism, hence relations among the
`G`-operations remain relations after attachment" — and that argument is now formalized.

`formal/GaloisForLFunctions/RHTower/DeningerPositiveCellEquivariance.lean`; axiom audit for all
declarations: `propext, Classical.choice, Quot.sound`.

- `deningerCellAction` — **the descended operation**: an operation of the monoid compatible with the
  relation map (`σ g ∘ j = j ∘ τ g`) sends the ideal generated by the relations into itself, hence
  descends to the attachment.
- `deningerCellAction_mk`, `deningerCellAction_comp` — it acts on representatives by the original
  operation.
- `deningerCellAction_unique` — **the descent is unique**: it is the only algebra map on the
  attachment agreeing with the operation on representatives.  This is where "descends uniquely up to
  contractible choice" becomes an actual uniqueness statement.
- `deningerCellAction_one`, `deningerCellAction_mul` — **the descent is functorial**, and this is
  proved *from* uniqueness, exactly as the card argues.  It is the precise form of "relations among
  the `G`-operations remain relations after attachment": a monoid relation among the `σ g` is
  transported to the same relation among the descended operations.

Together with the degree-zero shadow already recorded, the two theorems of the card's abstract half
— positive-cell `π₀`-invariance and the equivariant universal property — now both have proved
one-categorical counterparts.  What stays out of reach is unchanged: the `E_∞` free algebra and
homotopy pushout themselves, the Milnor--Witt fundamental class with its cotangent-complex
determinant twist, and any statement about positive homotopy.

### The conormal trivialization of the monic lift `[NEW]`

The monic Milnor--Witt lift theorem trivializes two determinant lines, by the classes of `P` and
`dT`.  The first of those trivializations is ordinary commutative algebra and is now proved; only
the Milnor--Witt fundamental class it orients remains out of reach.

`formal/GaloisForLFunctions/RHTower/DeningerPrincipalConormal.lean`; axiom audit for all
declarations: `propext, Classical.choice, Quot.sound`.

- `deningerConormal_mul_mem_sq_iff` — a multiple of a regular generator lies in the square of the
  principal ideal exactly when its cofactor lies in the ideal.  This is the whole content:
  cancellation by the generator.
- `deningerConormalMap`, `_apply`, `_surjective`, `_ker` — multiplication by the generator followed
  by the conormal projection is onto with kernel the ideal itself.
- `deningerConormalPrincipalEquiv` — **the conormal module `I/I²` of an ideal generated by a
  non-zero-divisor is free of rank one on the class of the generator**, via the induced isomorphism
  from the quotient by the ideal.
- `deningerMonicConormalEquiv` — the case of a monic polynomial: `(P)/(P²)` is free of rank one on
  the class of `P`, so the conormal determinant line of the closed immersion `Z_P ⊂ 𝔸¹_X` is
  trivialized by that class.  This uses the card's already-formalized `deningerMonic_isRegular`.

The second trivialization, by `dT`, is the freeness of `Ω¹_{A[T]/A} ⊗ B` on `dT`; the fundamental
class itself, its determinant twist and the Gysin forgetful map to the ordinary cycle `[Z_P]` need
Milnor--Witt sheaves and remain unformalizable here.

### The differential trivialization of the monic lift `[NEW]`

The second of the two determinant-line trivializations of the monic lift theorem — the one by the
class of `dT` — is also ordinary commutative algebra and is now proved, so both terms of the
two-term presentation of `L_{B/A}` are formalized as free of rank one, and its differential is
identified.

`formal/GaloisForLFunctions/RHTower/DeningerMonicKaehlerLine.lean`; axiom audit for all
declarations: `propext, Classical.choice, Quot.sound`.

- `deningerKaehlerBaseChangeEquiv` — **the base change `Ω¹_{A[T]/A} ⊗_{A[T]} B` is free of rank
  one**, from mathlib's freeness of `Ω¹_{A[T]/A}` on `dT` composed with the unit of the tensor
  product.
- `deningerKaehlerBaseChangeEquiv_D` — under the trivialization the differential of a polynomial is
  its derivative.
- `deningerKaehlerBaseChangeEquiv_D_X` — **the trivialization by `dT`**: the class of `dT` is sent
  to the unit, so it generates.
- `deningerKaehlerBaseChangeEquiv_D_self` — the differential of the defining polynomial is `P'`.
  Combined with the conormal trivialization by the class of `P`, this says that in the two-term
  presentation
  `L_{B/A} ≃ [(P)/(P²) → Ω¹_{A[T]/A} ⊗ B]`
  both terms are free of rank one and the differential is multiplication by `P'` — which is exactly
  what "the classes of `P` and `dT` trivialize its two determinant lines" asserts.

What remains of the monic lift theorem is only the Milnor--Witt layer itself: the oriented
fundamental class, its determinant twist, and the Gysin forgetful map to the ordinary cycle `[Z_P]`.
Those need Milnor--Witt sheaves, which mathlib does not have.

### Milnor--Witt `K`-theory is now built — 2026-08-07

`formal/GaloisForLFunctions/HTGeometry/MilnorWittKTheory.lean`.  Axiom audit for all thirteen
declarations: `propext, Classical.choice, Quot.sound`.

The absence of Milnor--Witt `K`-theory is named here as a reason a statement cannot be written down.
Morel's presentation is elementary and is now built, in the same shape as the corpus's Milnor
`K`-theory: the free `ℤ`-algebra on a symbol `[u]` for every unit together with one further symbol
`η`, modulo the four relations.

- `MilnorWittGen`, `MilnorWittRel`, `MilnorWittK`, `mwMk` — the generators, **Morel's four
  relations** (Steinberg `[u][1-u] = 0`, twisted additivity `[uv] = [u] + [v] + η[u][v]`, the
  centrality of `η`, and the hyperbolic relation `η(η[-1] + 2) = 0`), and the ring.
- `milnorWittSymbol`, `milnorWittEta`, `milnorWittSymbol_mul`, `milnorWittSymbol_mul_oneSub`,
  `milnorWittEta_comm`, `milnorWittEta_hyperbolic` — the generators and the four relations as
  theorems about them.
- `milnorWittForget`, `milnorWittForget_symbol`, `milnorWittForget_eta` — **killing `η` gives Milnor
  `K`-theory**: twisted additivity becomes ordinary additivity, centrality and the hyperbolic
  relation become `0 = 0`, and Steinberg is Steinberg.

The corpus already held a second presentation of the same object, with the form identities, the
comparison with the Witt ring and the quotient by `η` built on it.  The two are now one: the base
module carries the names the rest of the tree uses, and `milnorWittSymbol_one` — **the symbol of `1`
vanishes** — is the *unconditional* proof from `MilnorWittFormIdentities.lean`, which multiplies the
hyperbolic relation by that symbol, rather than an earlier version that assumed the field has a unit
other than `1`.

What this does not build is the Milnor--Witt *sheaf* theory — the oriented fundamental class, its
determinant twist and the Gysin map — which is what the remaining geometric statements need.  The
ring itself is no longer a gap.

### The cotangent complex of the monic lift `[NEW]`

`formal/GaloisForLFunctions/RHTower/DeningerMonicCotangentComplex.lean`.  Axiom audit for all
declarations: `propext, Classical.choice, Quot.sound`.

The card's monic lift asserts the two-term presentation

`L_{B/A} ≃ [(P)/(P²) --dP--> Ω¹_{A[T]/A} ⊗ B]`.

Both terms were already trivialized — the conormal one by the class of `P`, the differential one by
the class of `dT` — but the two-term complex itself had not been identified with the cotangent
complex.  It now is, against mathlib's own `Algebra.Extension.cotangentComplex`:

- `deningerMonicExtension` — the polynomial algebra `A[T]`, with the quotient map to `B = A[T]/(P)`
  and a set-theoretic section, as an `Algebra.Extension A B`.  Its cotangent module is by
  definition `(P)/(P²)` and its cotangent space is `B ⊗_{A[T]} Ω¹_{A[T]/A}`, exactly the two terms
  of the card.
- `deningerMonicExtension_ker` — the kernel of the presentation is the principal ideal `(P)`, so
  the cotangent module *is* the conormal module already trivialized.
- **`deningerMonicCotangentComplex_mk`** — the differential.  The class of `qP` maps to
  `1 ⊗ d(qP) = q ⊗ dP + 1 ⊗ P·dq`; the Leibniz term dies because `P` is zero in `B`; and
  `dP = P'·dT`, so under the two trivializations the cotangent complex is **multiplication by the
  derivative of `P`**.

This closes the commutative-algebra half of the monic Milnor--Witt lift: the two-term presentation
of the cotangent complex, its two determinant lines and its differential are all proved.  What
remains of that theorem is only the Milnor--Witt layer — the oriented fundamental class, its
determinant twist, and the Gysin forgetful map to the ordinary cycle `[Z_P]`.

### The degree-zero cell and the rank quotient `[NEW]`

`formal/GaloisForLFunctions/RHTower/DeningerDegreeZeroCell.lean`.  Axiom audit for all
declarations: `propext, Classical.choice, Quot.sound`.

The card's `(5)`--`(6)` are the counterpart of its `(2)`: positive cells leave degree zero
untouched, degree-zero cells quotient it by exactly the ideal they generate.  In the same graded
shadow in which `(2)` is already proved:

- **`deningerDegreeZeroCell_proj_mem`** — an ideal generated in degree zero is stable under the
  degree-zero projection, because that projection is a ring homomorphism fixing degree zero.  So a
  degree-zero element lies in the ideal exactly when it is a degree-zero combination of the
  generators (`deningerDegreeZeroCell_mem_iff`): unlike a positive cell, a degree-zero cell does
  act on degree zero, and it acts by exactly its own ideal.
- **`deningerRankQuotient_equiv`** — dividing the degree-zero ring by the kernel of a surjective
  rank map returns the target, and `deningerRankQuotient_span_ker` records that the ideal generated
  by that kernel is the kernel itself, so no relations beyond the rank are imposed.  This is `(6)`:
  `π₀ 𝒜_F^der ≅ π₀𝒞_F^{MW}/⟨ker(π₀ r)⟩ ≅ π₀𝒞_F^M`.

With `(2)` and its equivariant universal property, this completes the abstract half of the card in
the graded shadow.  What remains is only the Milnor--Witt geometric layer: the oriented fundamental
class, its determinant twist and the Gysin map, which need Milnor--Witt sheaf theory.

### The first homology of the monic cotangent complex `[NEW]`

`deningerMonicH1Cotangent_subsingleton` in
`formal/GaloisForLFunctions/RHTower/DeningerMonicCotangentComplex.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

With the two-term presentation identified and its differential computed, the homology of the
cotangent complex of a monic hypersurface is now determined: since the differential is
multiplication by `P'`, the first homology vanishes exactly when the class of `P'` is a
non-zero-divisor in `B`.  The proof is the closing computation of the regular-immersion picture: a
cotangent class is `[qP]`, its image is `P'·q̄`, and `P'·q̄ = 0` forces `q ∈ (P)`, hence
`qP ∈ (P)²`, hence the class was already zero.

So the monic hypersurface's cotangent complex is completely described: both terms free of rank one,
differential multiplication by `P'`, and first homology the annihilator of `P'`.  This is the whole
commutative-algebra content of the monic Milnor--Witt lift; only the Milnor--Witt layer itself — the
oriented fundamental class, its determinant twist and the Gysin map — is outstanding.

### The determinant twist and the oriented fundamental class `[NEW]`

`formal/GaloisForLFunctions/HTGeometry/MilnorWittFormAction.lean`,
`MilnorWittTwist.lean`, `MilnorWittFundamentalClass.lean`,
`MilnorWittKFunctoriality.lean`, and
`formal/GaloisForLFunctions/RHTower/DeningerMonicFundamentalClass.lean`.  Axiom audit for all
declarations: `propext, Classical.choice, Quot.sound`.

The monic lift theorem was recorded as blocked on "Milnor--Witt sheaf theory": the oriented
fundamental class, its determinant twist, and the Gysin forgetful map.  Two of those three are no
longer missing.  What they need is not sheaf theory but the twisted coefficients of Milnor--Witt
`K`-theory, and those are now built on the corpus's graded `MilnorWittKDeg`.

- `mwFormAct` — **multiplication by the unit form `⟨a⟩ = 1 + η[a]`**, realized on words as
  prepending `a` with one extra `η`.  `mwFormAct_one` (`[1] = 0`) and `mwFormAct_mul` (twisted
  multiplicativity in the prepended slot) make this an action of `Fˣ` on every graded piece
  (`mwFormActEquiv`, `mwFormMulAction`).  This is the group by which an oriented class is
  indeterminate.
- `MWTwist` — **`K_n^{MW}(F)` twisted by an `Fˣ`-set**: finitely supported families of Milnor--Witt
  classes indexed by the set, modulo `mwTwistMk_smul`, the relation that moving the index by `u`
  multiplies the coefficient by `⟨u⟩`.  `mwTwistEquiv` — **a simply transitive base point
  trivializes the twist** — and `mwTwistTriv_smul` — **changing the base point by `u` changes the
  trivialization by `⟨u⟩`** — are the determinant twist in exactly the card's sense: a chosen
  generator of the determinant line makes the class an honest Milnor--Witt class, another generator
  changes it by the unit form of the ratio.  `MWLinePoints`, `mwLineTwistEquiv` specialize this to
  the nonzero vectors of a one-dimensional vector space, the case of an actual determinant line.
- `mwOne`, `mwRank` — the unit `⟨1⟩` and the rank `K_0^{MW}(F) → K_0^M(F) ≅ ℤ`.
  `mwFormAct_mwOne` is `⟨a⟩ = 1 + η[a]`, and `mwRank_formAct_mwOne` is **every unit form has rank
  one**: the rank kills every word carrying an `η`.
- `mwFundamentalClass` — **the oriented Milnor--Witt fundamental class of a line**: the unit
  quadratic orientation `⟨1⟩` placed at a generator.  `mwRank_fundamentalClass` — **its rank is one
  for every trivialization**, because a change of generator moves it by a unit form and the rank
  does not see unit forms.  This is precisely the card's "choose the unit quadratic orientation
  `⟨1⟩`; the resulting class forgets to the ordinary fundamental cycle".
- `deningerConormalGen`, `deningerConormalGen_span`, `deningerConormalGen_ne_zero` — the conormal
  line of a regular generator of a maximal ideal is one-dimensional over the residue field on the
  class of the generator, so the already-proved conormal trivialization by `P` is now a *basis of a
  vector space*, which is what the twist consumes.
- **`deningerFundamentalClass`**, **`deningerFundamentalClass_rank`**, and the monic case
  `deningerMonicFundamentalClass_rank` — **the oriented Milnor--Witt fundamental class of the
  divisor `Z_P`, and the proof that its rank is one for every trivialization of the conormal
  determinant line**: the underlying ordinary cycle is `[Z_P]` with multiplicity one.
- `mwKDegMap` — functoriality of graded Milnor--Witt `K`-theory along a field homomorphism, with
  `mwKDegMap_id`, `mwKDegMap_comp`, multiplicativity `mwKDegMap_mul` and compatibility with `η`.
  This is the base-change needed to move a fundamental class between residue fields.

What remains of the monic lift is now only the Gysin *map* itself — the pushforward along the closed
immersion, whose local model is Morel's residue `∂_π : K_n^{MW}(K) → K_{n-1}^{MW}(k)` — together
with the compatibility with the zero-section quotient in Deninger's finite-correspondence theorem.
The fundamental class it is meant to produce, and the determinant twist that class lives in, are
proved.

### The cycle group and the forgetful map: the lift covers `[Z_P]` `[NEW]`

`formal/GaloisForLFunctions/HTGeometry/MilnorWittCycles.lean` and the new material in
`MilnorWittFundamentalClass.lean` and `RHTower/DeningerMonicFundamentalClass.lean`.  Axiom audit for
all declarations: `propext, Classical.choice, Quot.sound`.

The previous entry proved the fundamental class has rank one *after* choosing a generator of the
determinant line.  That choice is now removed, and the statement is upgraded from a number to a
cycle.

- **`mwRank_formAct`** — **the rank is invariant under the unit forms.**  Multiplying by `⟨u⟩` adds
  a word carrying one more `η`, and `mwRank_class_succ` says every such word has rank zero.  So the
  rank is constant on the orbits by which the twist is defined.
- **`mwTwistRank`** — consequently the rank descends to the twist: `MWTwist F 0 T →+ ℤ` with **no
  trivialization chosen at all**.  `mwTwistRank_fundamentalClass` — the oriented fundamental class
  of a line has rank one, basis-free.
- `ClosedPoint`, `MWPointGroup`, **`MWCycles`**, `Cycles` — the codimension-one cycle group with
  Milnor--Witt coefficients: a finitely supported family assigning to each closed point a class in
  `K_0^{MW}` of its residue field twisted by the conormal line of that point, together with the
  ordinary cycle group.  **`mwCyclesRank`** is the pointwise rank, the forgetful map from oriented
  to ordinary intersection theory in codimension one.
- **`deningerMWCycle`** — the oriented fundamental class of the divisor cut out by `P`, placed at
  the closed point it is supported on: an actual Milnor--Witt cycle on the ambient space.
- **`mwCyclesRank_deningerMWCycle`** — **its underlying ordinary cycle is `[Z_P]`, with multiplicity
  one.**

This is the card's sentence "the resulting MW Gysin fundamental class forgets to the ordinary
fundamental cycle of the regular immersion, namely `[Z_P]`", proved as an identity of cycles.  The
Gysin pushforward along the closed immersion, at the level of codimension-one cycles, is the
inclusion of the summand at the point — which is what `deningerMWCycle` performs; no residue map is
involved in the fundamental class itself.  Morel's residue is what would be needed to descend these
cycles to Chow--Witt groups, i.e. to quotient by the image of the Rost--Schmid differential, and
that is not asserted by the card.

### Surjectivity of the rank map, and the general codimension-one point `[NEW]`

Same modules; axiom audit for all declarations: `propext, Classical.choice, Quot.sound`.

The card's `(3)` is the surjectivity of the rank/forgetful map, argued from "the `Z_P` freely
generate the ordinary correspondence group and the lift is compatible with the zero-section
quotient".  In the cycle-level shadow that argument is now a theorem.

- **`mwCyclesRank_surjective`** — **the forgetful map onto ordinary codimension-one cycles is
  surjective**, as soon as every closed point has a nonzero conormal class: the unit orientation
  placed at such a class has rank one, and the classes of the points generate the ordinary cycle
  group, so every ordinary cycle is the underlying cycle of a Milnor--Witt one.  This is `(3)` for
  the cycle groups: the raw Milnor--Witt fundamental classes are received without altering degree
  zero, and the rank stays onto.
- `deningerIrreducible_span_isMaximal`, `deningerIrreducible_isRegular`,
  **`mwCyclesRank_deningerMWCycle_irreducible`** — the fundamental cycle and its rank-one identity
  hold at **every codimension-one point of a principal ideal domain**.  That covers the local ring
  at a codimension-one point of a normal Noetherian scheme (a discrete valuation ring) as well as
  the closed points `Z_P ⊂ 𝔸¹` of the card, so the monic lift is no longer tied to the affine line
  over a field.

### The Gysin pushforward, and interior-slot vanishing `[NEW]`

`formal/GaloisForLFunctions/HTGeometry/MilnorWittGradedAppend.lean` and new material in
`MilnorWittCycles.lean` and `RHTower/DeningerMonicFundamentalClass.lean`.  Axiom audit for all
declarations: `propext, Classical.choice, Quot.sound`.

- **`mwGysin`** — **the Gysin pushforward of the closed immersion of a point**, on codimension-one
  cycles: a twisted Milnor--Witt class at the point becomes the cycle supported there.  For a
  regular closed immersion of codimension one this is the whole pushforward — the points of the
  closed subscheme are points of the ambient one, and the determinant twist is transported along the
  conormal trivialization, which is exactly what the twist by `MWLinePoints` records.  It is
  injective (`mwGysin_injective`) and it **covers the ordinary pushforward**
  (`mwCyclesRank_mwGysin`).
- **`mwCyclesRank_gysin_fundamentalClass`** — **the monic Milnor--Witt lift in full**: the Gysin
  pushforward along the closed immersion of the divisor, applied to the unit quadratic orientation
  `⟨1⟩` in the twist by the conormal determinant line, is a Milnor--Witt cycle on the ambient space
  whose underlying ordinary cycle is `[Z_P]` with multiplicity one.  `deningerMWCycle_eq_gysin`
  records that the fundamental cycle *is* that Gysin image.
- `mwClassDeg_mul_eq_zero_left`, `mwClassDeg_mul_eq_zero_right`,
  `mwClassDeg_eq_zero_of_prefix_eq_zero`, `mwSymbol_mul_neg_self_infix` — infrastructure for the
  Milnor--Witt word calculus: the graded product is additive in each variable, so a vanishing word
  keeps vanishing inside any longer word.  This upgrades every identity proved for a word to an
  identity at an arbitrary interior slot, which is what Morel's residue construction needs.  The
  first application is `[a][-a] = 0` at an arbitrary interior slot.

With this the card's monic Milnor--Witt lift theorem is formalized end to end: regular immersion,
two-term cotangent complex with both determinant lines trivialized and differential `P'`, first
homology, the determinant twist, the oriented fundamental class with the `⟨1⟩` orientation, the
Gysin pushforward, and the forgetful identity with the ordinary cycle `[Z_P]`.
