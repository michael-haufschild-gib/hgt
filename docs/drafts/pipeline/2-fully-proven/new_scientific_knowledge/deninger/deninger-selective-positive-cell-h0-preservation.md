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
