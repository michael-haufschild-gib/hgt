# Universal descent of real Milnor residues through unit amalgamation

- **ID:** `deninger-unit-amalgamation-residue-universal-descent`
- **Stage:** 3-formalized
- **Type:** CATEGORICAL SOURCE-REDUCTION THEOREM
- **Label:** `DAC_UNIT_AMALGAMATION_RESIDUE_UNIVERSAL_DESCENT`
- **Parent:** `deninger-derived-stratum-kummer-arithmetic-coefficient`
- **Statement:** after realification, a single compatible Kummer-boundary
  square extends uniquely through the derived unit-amalgamation pushout;
  all Steinberg relations and all higher relative cells then descend
  automatically.

## Categorical theorem

Let \(\mathcal C\) be a presentable stable symmetric-monoidal
\(\infty\)-category in which tensor product preserves colimits separately,
and work in \(\operatorname{CAlg}(\mathcal C)\).  Suppose
\[
 P\longrightarrow T,\qquad P\longrightarrow K,\qquad
 A=T\mathop{\otimes}^{\mathbb L}_{P}K                              \tag{1}
\]
is a homotopy pushout.  Let \(B\) be a commutative algebra, \(M\) a
\(B\)-module, and
\[
 B\oplus M[-1]\longrightarrow B                                   \tag{2}
\]
the split square-zero algebra.  Assume given algebra maps
\[
 \widetilde s_T:T\longrightarrow B\oplus M[-1],\qquad
 \widetilde s_K:K\longrightarrow B\oplus M[-1]                     \tag{3}
\]
whose restrictions to \(P\) are homotopic through a specified homotopy.

`[PROVED HERE] [DAC_UNIT_AMALGAMATION_RESIDUE_UNIVERSAL_DESCENT]`

There is a contractible space of maps
\[
 \widetilde s_A:A\longrightarrow B\oplus M[-1]                     \tag{4}
\]
restricting to `(3)` and the specified homotopy.  Projection along `(2)`
gives a specialization map \(s_A:A\to B\); the square-zero component of
`(4)` is the unique degree \(-1\), \(s_A\)-linear derivation extending the
two components in `(3)`.

The statement is valid objectwise for sheaves of commutative algebras and
therefore for equivariant sheaves.  It is also natural in any operation
preserving `(1)`--`(3)`, including restriction and compatible power,
Galois, and finite-correspondence maps.

### Proof

The defining mapping-space property of the homotopy pushout `(1)` gives
\[
 \operatorname{Map}_{\mathrm{CAlg}}
   (A,B\oplus M[-1])
 \simeq
 \operatorname{Map}(T,B\oplus M[-1])
 \mathop{\times}_{\operatorname{Map}(P,B\oplus M[-1])}
 \operatorname{Map}(K,B\oplus M[-1]).                              \tag{5}
\]
The pair `(3)` and its compatibility homotopy is exactly a point of the
right side.  Its fiber in the space of extensions is contractible, proving
existence and uniqueness in the homotopical sense.  A map to a split
square-zero extension over \(B\) is equivalently a derivation into the
shifted module.  This proves the second assertion.

Limits, colimits, square-zero extensions, and `(5)` are computed
objectwise in sheaves before localization.  Descent localizes the same
universal diagram.  Naturality follows from functoriality of the mapping
space pullback.

## Real Milnor-residue input

Let \((F,v)\) be a discretely valued field, \(k\) its residue field, and
\(\pi\) a uniformizer.  Write
\[
 K_{\mathbb R}^M(F)=K_*^M(F)_{\mathrm{tf}}\otimes_{\mathbb Z}\mathbb R,
 \qquad
 K_{\mathbb R}^M(k)=K_*^M(k)_{\mathrm{tf}}\otimes_{\mathbb Z}\mathbb R.
\]
Milnor's specialization construction is a homomorphism of graded rings
\[
 D_\pi:K_*^M(F)\longrightarrow
 K_*^M(k)[\Pi]\big/
   \bigl(\Pi^2-\{-1\}\Pi\bigr),\qquad |\Pi|=1,                      \tag{6}
\]
whose degree-zero-in-\(\Pi\) component is specialization
\(s_v^\pi\) and whose coefficient of \(\Pi\) is the tame residue
\(\partial_v\).  In particular,
\[
 \partial_v\{\pi,u_2,\ldots,u_n\}
  =\{\bar u_2,\ldots,\bar u_n\},\qquad
 \partial_v\{u_1,\ldots,u_n\}=0                                   \tag{7}
\]
for units \(u_i\).

The class \(\{-1\}\in K_1^M(k)=k^\times\) is \(2\)-torsion.  Hence it
vanishes after tensoring with \(\mathbb R\), and `(6)` becomes an algebra
map
\[
 D_{\pi,\mathbb R}:K_{\mathbb R}^M(F)\longrightarrow
 K_{\mathbb R}^M(k)\oplus
 K_{\mathbb R}^M(k)(-1)[-1]                                      \tag{8}
\]
to a genuinely square-zero extension.  Thus the real tame residue is a
degree \(-1\) derivation relative to specialization.  The integral
quadratic correction in `(6)` explains why this reduction must not be
asserted before realification.

## Application to Deninger's coefficient

On a generic suspension-cover chart use the already constructed pushout
\[
 \widetilde{\mathscr A}_\eta^M
 =
 \mathscr T_\eta
 \mathop{\otimes}^{\mathbb L}_{\mathscr P_\eta}
 \underline{\mathcal K}_{\eta,\mathbb R}^M.                       \tag{9}
\]
For a prime \(p\), put
\[
 B_p=\widetilde{\mathscr A}_p^M,\qquad
 M_p=B_p(-1).
\]
The algebraic map in `(3)` is `(8)`.  The analytic map in `(3)` is a
square-zero lift
\[
 \widetilde s_{\mathscr T,p}:
 \mathscr T_\eta\longrightarrow B_p\oplus M_p[-1]                 \tag{10}
\]
whose linear term is the boundary of Deninger's Tate--Kummer class.
Compatibility on the free unit algebra \(\mathscr P_\eta\) says exactly
\[
 \partial_{\mathrm{an},p}\bigl(\kappa_\eta(a)\bigr)
 =
 \operatorname{ord}_p(a)\,\mathbf 1_{B_p}(-1)                     \tag{11}
\]
for every local Kummer generator \(a\).  The multiplicity-one
normalization in `(11)` is supplied on the arithmetic base by
`DAC_ARITHMETIC_PRO_LOG_KUMMER_DIVISOR_RESOLUTION`.

If `(10)` and `(11)` hold, the categorical theorem gives a unique residue
\[
 \widetilde\partial_p:
 \widetilde{\mathscr A}_\eta^M
 \longrightarrow
 B_p(-1)[-1]                                                       \tag{12}
\]
on the complete sheafified Tate--Milnor coefficient.  No separate check is
needed for:

1. Steinberg symbols;
2. products of any Tate weight;
3. higher syzygy or relative-cell attachments;
4. homotopies used to present the derived tensor product.

All four are already encoded in the homotopy pushout `(9)` and the algebra
map `(4)`.

For a positive power \(q\), valuation scales by
\(\operatorname{ord}_p(a^q)=q\operatorname{ord}_p(a)\), while the target
normal line has Tate weight \(-1\).  The factors \(q\) and \(q^{-1}\)
cancel, so `(11)` is power-equivariant.  The standard residue/norm
compatibility for Milnor cycle modules gives finite-correspondence
naturality once the analytic lift `(10)` has the same compatibility.

## Exact reduction of the open gate

This theorem closes the formal “all Tate--Milnor cells” part of
`DAC_SOURCE_STRATUM_RESIDUE_SHEAF_MORPHISM`.  The finite-prime part of that
gate is now precisely:

1. construct the analytic square-zero Kummer-boundary lift `(10)` on the
   true \(p\)-packet model;
2. prove the generator equality `(11)` with the pulled-back pro-log
   coordinate;
3. prove closedness/continuity in the selected pro-Stein and mixed
   \(L^1/L^2\) topologies;
4. descend `(12)` through degreewise coarse invariants and assemble all
   primes.

It does **not** prove these four analytic statements, the restricted prime
completion, or the real signature component.

## Hostile audit

- The tame residue is not an ordinary integral derivation:
  \(\Pi^2=\{-1\}\Pi\) in `(6)`.  Realification kills exactly this
  obstruction.
- Checking `(11)` only on global units is insufficient.  It must hold
  sheafwise on the pro-log Kummer generator.
- The universal property extends a compatible map; it does not manufacture
  the analytic lift `(10)`.
- No identification of Deninger's actual prime-packet topology with a
  mapping torus is used.
- No quotient stack, derived group invariants, CCM object, zeta zero, or RH
  premise occurs.

## References

- John Milnor, *Introduction to Algebraic K-Theory*, discrete-valuation
  specialization and tame residue.
- Philippe Gille and Tamás Szamuely, *Central Simple Algebras and Galois
  Cohomology*, Proposition 7.1.4.
- Jacob Lurie, *Derived Algebraic Geometry IV: Deformation Theory*, §3.1,
  derivations and square-zero extensions:
  https://www.math.ias.edu/~lurie/papers/DAG-IV.pdf
- Markus Rost, *Chow Groups with Coefficients*, residue, restriction,
  corestriction, and cycle-module compatibilities.
- `DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE`
- `DAC_ARITHMETIC_PRO_LOG_KUMMER_DIVISOR_RESOLUTION`

## Novelty audit

Milnor's residue algebra and the homotopy-pushout universal property are
standard.  New program-level knowledge is the exact reduction: after
realification, every higher Steinberg/Tate coherence condition follows from
one source Kummer-boundary square.  The unresolved analytic content is
therefore isolated to `(10)`--`(11)` and topology, rather than an
unbounded cell-by-cell proof.

**Verdict:** `FULLY PROVEN ON PAPER; FORMAL CATEGORICAL REDUCTION ONLY;
ANALYTIC GENERATOR SQUARE REMAINS OPEN`.

## Lean status

### The categorical reduction landed, in the setting mathlib supports

`formal/GaloisForLFunctions/RHTower/DeningerAmalgamationUniversalDescent.lean`.  Axiom audit for
all 18 declarations: `propext, Classical.choice, Quot.sound` or less.

mathlib has no ∞-categories, so the statement `(5)` about mapping *spaces* cannot be written.  What
is formalized is its ordinary-algebra shadow, which is exactly the content the card uses: the
amalgamation is the tensor product, a compatible pair of maps out of the two factors extends to it,
and the extension is **unique** — the `π₀` and `π₁`-triviality of the contractible space of `(4)`.

- `deningerAmalgamationLift`, `deningerAmalgamationLift_tmul`, `_left`, `_right` — **existence in
  `(4)`**: the pair `(3)` extends to the amalgamation `(1)`, restricting to the two given maps.
- `deningerAmalgamationLift_unique` — **uniqueness**: two maps out of the amalgamation that agree
  on both factors are equal.  This is the formal statement of "no separate check is needed" for the
  Steinberg symbols, the products of any Tate weight, and the higher relative cells of items 1--3:
  they are relations already satisfied in the factors, and the extension exists regardless.  Item 4
  — homotopies presenting the derived tensor product — is inherently ∞-categorical and has no
  1-categorical content.
- `deningerAmalgamSpecialization`, `deningerAmalgamResidue`, `_apply` — the two components of a map
  into a split square-zero extension `(2)`: the specialization `s_A` and the square-zero part.
- `deningerAmalgamResidue_add`, `deningerAmalgamResidue_one`, `deningerAmalgamResidue_leibniz` —
  **the second assertion of the theorem**: the square-zero component is a derivation over the
  specialization; its Leibniz rule is literally the multiplication rule of the split square-zero
  extension.
- `deningerAmalgamResidue_left/_right`, `deningerAmalgamSpecialization_left/_right` — the descended
  boundary square restricts to the two given specializations and residues, which is the
  compatibility asserted after `(12)`.
- `deningerQuadraticCorrection_eq_zero`, `deningerResidueDirection_sq_eq_zero` — the passage
  `(6)` → `(8)`: the class `{-1}` is `2`-torsion, hence zero in a vector space where `2` is
  invertible, so Milnor's `Π² = {-1}Π` becomes `Π² = 0` and the target is genuinely square zero.
  This is the card's warning that the reduction must not be asserted before realification.
- Power equivariance of `(11)` — the cancellation of `q` against the weight `-1` Tate line — is
  `deningerTateNormalizedResidue` and `deningerRationalTwist_cancel` in
  `DeningerProLogCuspHodge.lean` and `DeningerEquivariantTateRegulator.lean`.

### Remaining

Nothing categorical.  The four analytic obligations the card isolates — constructing the analytic
square-zero Kummer-boundary lift `(10)`, the generator equality `(11)` sheafwise, closedness in the
pro-Stein and mixed `L¹/L²` topologies, and the descent of `(12)` through coarse invariants over
all primes — are explicitly outside this theorem and stay open, as does the real signature
component.
