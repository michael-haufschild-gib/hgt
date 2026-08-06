# Spherical exponents act faithfully by semilocal Weyl multipliers

- **ID:** `field-one-spherical-weyl-multiplier-bridge`
- **Stage:** 3-formalized
- **Type:** THEOREM / CONSTRUCTION / BRIDGE
- **Parent:** `field-one-relative-picard-hodge-passivity`
- **Labels:** `[PAPER-PROVED] [FORMALIZED]`
- **Statement:** the \(p\)-perfect spherical stalk has a faithful Frobenius-compatible
  representation by unitary multipliers of each semilocal Bruhat--Schwartz space containing
  \(p\), although it does not map into the Bruhat--Schwartz algebra itself.

## Source boundary

For a prime \(p\), Connes--Consani identify the absolute spherical stalk as
\[
  \mathcal F_p=\mathbb F_1[T^{H_p^+}],
  \qquad
  H_p^+=\mathbb Z[1/p]_+,
\]
and prove that the \(p\)-power Frobenius is invertible on this stalk. Their semilocal analytic
sheaf has
\[
  \mathscr O(S^c)=\mathcal S(\mathbb A_S),\qquad
  (\mathscr O\rtimes\mathbf G_m)(S^c)
  =
  \mathcal S(\mathbb A_S)\rtimes\mathbb Z_S^\times
\]
for finite \(S\ni\infty\). Their explicit formula fixes a nontrivial additive character of the
adeles.

Fix finite \(S\) containing \(\infty\) and \(p\). Let
\(\alpha_S:\mathbb A_S\to S^1\) be the restriction of a nontrivial global additive character.
For \(h\in H_p=\mathbb Z[1/p]\), define
\[
  \chi_h(x)=\alpha_S(hx),\qquad
  (W_hf)(x)=\chi_h(x)f(x)
  \quad(f\in\mathcal S(\mathbb A_S)).
\]

## Theorem

`[PAPER-PROVED]` The operators \(W_h\) satisfy:

1. \(W_h\) is a continuous linear automorphism of
   \(\mathcal S(\mathbb A_S)\), with inverse \(W_{-h}\).
2. \(W_0=1\) and \(W_{h+k}=W_hW_k\).
3. The representation \(h\mapsto W_h\) is faithful.
4. \(W_h\) extends to a unitary operator on \(L^2(\mathbb A_S)\).
5. \(W_{h/p}^{\,p}=W_h\); hence the representation carries exact \(p\)-perfection.
6. For the scaling action
   \((\theta(u)f)(x)=f(u^{-1}x)\),
   \[
     \theta(u)W_h\theta(u)^{-1}=W_{u^{-1}h}.
   \]

Restricting \(h\) to \(H_p^+\) gives a multiplicative-monoid morphism from the generating monoid
of \(\mathcal F_p\) to continuous automorphisms of \(\mathcal S(\mathbb A_S)\). By the spherical
base-change adjunction this is the correctly typed local analytic realization of the stalk.

## Proof

The Bruhat--Schwartz space on \(\mathbb A_S\) is the tensor product of ordinary Schwartz space at
the archimedean component with locally constant compactly supported test functions at finite
components.

At a finite place, multiplication by a continuous additive character preserves local constancy
and does not enlarge support. At the archimedean place, every derivative of
\(x\mapsto\alpha_\infty(hx)\) is a constant multiple of the same unit-modulus function. Leibniz'
rule therefore shows that multiplication by \(\chi_h\) preserves every Schwartz seminorm and is
continuous. The same argument with \(-h\) gives the inverse.

Additivity of \(\alpha_S\) gives
\[
  \chi_{h+k}(x)=\alpha_S(hx+kx)
  =\chi_h(x)\chi_k(x),
\]
which proves Items 1 and 2. It also gives
\[
  \chi_{h/p}(x)^p=\alpha_S(hx)=\chi_h(x),
\]
proving Item 5.

For faithfulness, suppose \(h\ne k\). Multiplication by the nonzero rational \(h-k\) is an
automorphism of \(\mathbb A_S\). Since \(\alpha_S\) is nontrivial, choose \(y\) with
\(\alpha_S(y)\ne1\) and put \(x=(h-k)^{-1}y\). Then
\(\chi_h(x)\ne\chi_k(x)\). A Bruhat--Schwartz test function nonzero at \(x\) distinguishes
\(W_h\) from \(W_k\).

Since \(|\chi_h|=1\), Haar integration gives
\(\|W_hf\|_2=\|f\|_2\), proving Item 4. Finally,
\[
\begin{aligned}
  (\theta(u)W_h\theta(u)^{-1}f)(x)
  &=\alpha_S(hu^{-1}x)f(x)\\
  &=(W_{u^{-1}h}f)(x),
\end{aligned}
\]
which proves Item 6. No zero of Xi, positivity premise, or RH statement enters.

## Hostile audit

### Direct map into \(\mathcal S(\mathbb A_S)\)

`[FALSIFIED AS ILL-TYPED]` A nonzero additive character has unit modulus and full support. It is
not a Bruhat--Schwartz function on noncompact \(\mathbb A_S\). Thus the spherical monomial cannot
be sent to \(\chi_h\) as an element of the coefficient algebra.

### Positive survivor

The character is a multiplier: multiplication by it preserves the Bruhat--Schwartz algebra and
its \(L^2\) completion. The multiplier/endomorphism target is therefore forced, not optional.

### What this does not prove

- Compatibility of these local multiplier representations with every restriction map of the
  semilocal sheaf is now proved in
  `GaloisForLFunctions.RHTower.FieldOneSemilocalStageRestrictionWeyl`.
- No extension across the compactified arithmetic curve or derived Abel--Jacobi pushforward is
  constructed.
- A faithful coefficient representation does not imply Hodge positivity or RH.

## Gates

- [x] 0 → 1: exact source and target types identified
- [x] 1 → 2: dependency-closed semilocal paper proof and hostile audit complete
- [x] 2 → 3: complete.  Items 1-14 below are all formalized: the abstract multiplier
      representation, the archimedean and generic finite-place laws, canonical all-depth
      conductor-\(\mathbb Z_p\) characters, finite restricted-product character assembly,
      diagonal-product compatibility on every \(\mathbb Z[1/p]\) and then on all of
      \(\mathbb Q\), algebraic real--finite tensor assembly, full semilocal faithfulness,
      finite-adele and product-Haar \(L^2\) unitarity, the canonical Bruhat-tensor map into
      product-Haar \(L^2\) with exact Weyl equivariance and injectivity, its Hilbert completion,
      full-product density identifying that completion with the whole semilocal \(L^2\), the
      independent factorwise completed-tensor comparison, and restriction-compatible sheaf
      assembly with Weyl compatibility.  Axioms audited; umbrella build green
- [ ] 3 → 4: publication-ready integration

## Formalization decomposition

1. [x] Abstract additive-character multiplier representation and faithfulness:
   `GaloisForLFunctions.HTGeometry.FieldOneWeylCharacterBridge`.
2. [x] Archimedean preservation, inverse law, root law, and faithfulness on
   `SchwartzMap ℝ ℂ`:
   `GaloisForLFunctions.HTGeometry.FieldOneArchimedeanWeylMultiplier`.
   Full \(L^2(\mathbb R)\) phase-multiplier unitarity is already formalized independently in
   `GaloisForLFunctions.RHTower.L2MellinUnitary`, up to its \(2\pi\) parameter normalization.
3. [x] Generic finite-place locally constant compact-support preservation, inverse/root laws,
   and scaling covariance:
   `GaloisForLFunctions.RHTower.FieldOneLocallyConstantWeylMultiplier`.
4. [x] Existence at every prime of a nontrivial locally constant character of \(\mathbb Q_p\)
   trivial on \(\mathbb Z_p\), with exact depth-one normalization, and its Weyl specialization:
   `GaloisForLFunctions.RHTower.FieldOnePadicWeylCharacter`.
   The stronger module
   `GaloisForLFunctions.RHTower.FieldOnePadicStandardWeylCharacter` constructs the canonical
   compatible character on all \(p^{-n}\mathbb Z_p\), proves exact normalization at every
   depth and kernel exactly \(\mathbb Z_p\), and removes the arbitrary extension choice.
5. [x] Restricted finite-place character assembly, local constancy, nontriviality, and the
   finite-adele Weyl action:
   `GaloisForLFunctions.RHTower.FieldOneFiniteAdeleWeylCharacter`.
6. [x] Diagonal-product compatibility on every fixed-prime exponent lattice
   \(\mathbb Z[1/p]\):
   `GaloisForLFunctions.RHTower.FieldOneFiniteAdeleDiagonalReciprocity`.
7. [x] Arbitrary-denominator reciprocity by pairwise-coprime prime-power decomposition:
   `GaloisForLFunctions.RHTower.FieldOneRationalPrimaryReciprocity`.
8. [x] Algebraic real--finite Bruhat tensor assembly, inverse/additive laws, compact-open
   integral finite Bruhat test, finite-zero contraction, and rational diagonal faithfulness:
   `GaloisForLFunctions.RHTower.FieldOneSemilocalBruhatWeylTensor`,
   `GaloisForLFunctions.RHTower.FieldOneFiniteAdeleIntegralBruhatTest`,
   `GaloisForLFunctions.RHTower.FieldOneSemilocalArchimedeanFaithfulness`.
9. [x] Measure-independent unit-modulus \(L^2\) multiplier and finite-adele Borel Haar
   specialization, including exact compatibility with embedded Bruhat tests:
   `GaloisForLFunctions.RHTower.UnitModulusL2Multiplier`,
   `GaloisForLFunctions.RHTower.FieldOneFiniteAdeleL2WeylMultiplier`.
10. [x] Product-Haar semilocal \(L^2\) unitary action, finite-character primitivity,
    faithful finite Bruhat action, and full algebraic semilocal faithfulness:
    `GaloisForLFunctions.RHTower.FieldOneSemilocalL2WeylMultiplier`,
    `GaloisForLFunctions.RHTower.FieldOneFiniteAdeleSelfDuality`,
    `GaloisForLFunctions.RHTower.FieldOneSemilocalFullFaithfulness`.
11. [x] Canonical algebraic Schwartz--Bruhat realization in product-Haar \(L^2\), including
    exact Weyl equivariance:
    `GaloisForLFunctions.RHTower.FieldOneSemilocalBruhatToL2`.
12. [x] Algebraic uniqueness of separated-function tensors, open-positive swapped product
    measure, continuous representative, and injectivity:
    `GaloisForLFunctions.RHTower.FunctionTensorProduct`,
    `GaloisForLFunctions.RHTower.FieldOneSemilocalBruhatL2Embedding`.
13. [x] Pulled-back Hilbert completion, isometric identification with the closed algebraic
    \(L^2\) image, and completed Weyl intertwining:
    `GaloisForLFunctions.RHTower.FieldOneSemilocalBruhatHilbertCompletion`.
14. [x] Full-product density: Haar regularity plus the compact-open basis of the rational
    finite adeles makes finite-adele Bruhat--Schwartz functions dense in Haar \(L^2\), and the
    separated-product density theorem then makes the algebraic semilocal Bruhat realization dense
    in product-Haar \(L^2\).  Its abstract completion is therefore the whole semilocal
    \(L^2\), and the completed Weyl action is injective:
    `GaloisForLFunctions.RHTower.FieldOneFiniteBruhatL2Density`,
    `GaloisForLFunctions.RHTower.FieldOneSemilocalBruhatL2Density`.
15. [x] Independent factorwise completed-tensor comparison: the pointwise separated-product map
    preserves the algebraic tensor inner product, so the Hilbert completion of
    \(L^2(\mu)\otimes L^2(\nu)\) is isometric to \(L^2(\mu\otimes\nu)\), and the semilocal
    Bruhat completion agrees with the factorwise Hilbert tensor product on pure tensors:
    `GaloisForLFunctions.RHTower.L2HilbertTensorProduct`,
    `GaloisForLFunctions.RHTower.FieldOneSemilocalFactorwiseHilbertTensor`.
16. [x] Restriction-compatible sheaf assembly: for finite sets \(S\subseteq T\) of finite
    places the sheaf restriction extends a section on \(A_S\) by the indicator of the integral
    part at the places of \(T\) outside \(S\).  These maps are functorial, and the Weyl
    multiplier of any rational integral outside \(S\) -- in particular of any \(m/p^n\) with
    \(p\) a place of \(S\) -- commutes with every one of them, because the standard local
    character is trivial on the local integers:
    `GaloisForLFunctions.RHTower.FieldOneSemilocalStageRestrictionWeyl`.

## Log

- 2026-07-26 — Extracted after ordinary scalar extension was ruled out. Primary-source typing
  forces a multiplier target; paper proof closes every fixed semilocal stage without computation.
- 2026-07-26 — Lean formalized abstract character/root/faithfulness laws and the full
  archimedean Schwartz multiplier with inverse and faithfulness. Existing Mellin \(L^2\) module
  supplies unitary phase multiplication.
- 2026-07-26 — Lean formalized generic finite-place Bruhat preservation, inverse/root laws, and
  scaling covariance. It also constructs unconditionally at every prime a nontrivial locally
  constant character trivial on \(\mathbb Z_p\), normalized on the class of \(p^{-1}\), and its
  Weyl multiplier. Hostile audit records the noncanonical all-depth extension; standard local
  normalization and semilocal \(L^2\) remained at that stage.
- 2026-07-26 — Lean replaced the noncanonical extension with the standard compatible
  denominator-stage character, proving all-depth normalization, exact kernel \(\mathbb Z_p\),
  local constancy, nontriviality, and the Weyl composition law. The finite-adele module then
  assembles these characters through eventual integrality and `finsum`, proving canonical
  restricted-product local constancy, nontriviality, and the global finite-place Weyl law.
  The diagonal-reciprocity module then proves, without a product-formula premise, that this
  character cancels the negative real character on every \(\mathbb Z[1/p]\). The rational
  primary-decomposition module derives the same law for every rational denominator using
  pairwise coprimality and Bézout coefficients.
- 2026-07-26 — Lean assembled the algebraic real--finite Schwartz--Bruhat tensor with exact
  additive and inverse laws. Compactness of integral finite adeles produced a canonical nonzero
  finite Bruhat test and finite-zero contraction; this proves rational diagonal faithfulness
  without assuming full finite-adele self-duality. A general unit-modulus \(L^2\) construction
  and its finite-adele Borel Haar specialization prove finite-place unitarity and exact
  compatibility with embedded Bruhat tests.
- 2026-07-26 — Lean proved product-Haar semilocal \(L^2\) unitarity. A one-coordinate
  inverse-principal-part argument proves the finite standard character primitive; translated
  compact-open tests make the finite Bruhat action faithful. Archimedean-zero contraction
  against the Gaussian combines this with finite-zero contraction to prove full algebraic
  semilocal faithfulness.
- 2026-07-26 — Lean constructed the canonical algebraic Schwartz--Bruhat map into
  product-Haar \(L^2\), proving square-integrability without sigma-finite Haar and exact
  intertwining of the algebraic and analytic Weyl actions.
- 2026-07-26 — Lean proved injectivity. A general Hamel-coordinate theorem gives uniqueness of
  algebraic separated-function tensors. Forming product measure with the real factor on
  `Measure.prod`'s sigma-finite side and transporting by swap gives open positivity without a
  finite-adele sigma-finiteness theorem; continuous representatives then upgrade \(L^2\)
  equality to pointwise equality.
- 2026-07-26 — Lean constructed the induced pre-Hilbert structure and proved its abstract
  completion canonically isometric to the closure of the algebraic product-\(L^2\) image.
  Algebraic Weyl automorphisms extend to completed unitaries with exact ambient intertwining and
  additive law. Full-product density, independent factorwise completed-tensor comparison, and
  sheaf compatibility remain.
- 2026-07-30 — Lean proved full-product density.  Haar regularity and the compact-open basis of
  the rational finite adeles approximate every finite-measure indicator by an indicator of a
  compact-open set, which is a Bruhat–Schwartz function; `Lp.induction` then gives dense range in
  finite-adele Haar \(L^2\).  Combined with real Schwartz density and the separated-product
  density theorem, the algebraic semilocal Bruhat realization is dense in product-Haar \(L^2\), so
  its abstract Hilbert completion is canonically the whole semilocal \(L^2\) and the completed
  Weyl action is injective.  The completed Hilbert tensor product of the two \(L^2\) factors was
  constructed independently and shown to agree with that completion on pure tensors.
- 2026-08-05 — Lean closed the last item, restriction-compatible sheaf assembly.  For
  \(S\subseteq T\) the semilocal restriction extends a section on \(A_S\) by the indicator of the
  integral part at the places of \(T\) outside \(S\); these maps are functorial
  (`fieldOneFiniteStageRestrict_self`, `fieldOneFiniteStageRestrict_comp`), the stage Weyl
  multipliers form an additive representation (`fieldOneFiniteStageWeyl_zero`,
  `fieldOneFiniteStageWeyl_add`), and every restriction map intertwines them for a rational
  integral outside \(S\) (`fieldOneFiniteStageRestrict_weyl`), in particular for every \(m/p^n\)
  with \(p\) a place of \(S\) (`fieldOneFiniteStageRestrict_weyl_int_div_pow`).  The mechanism is
  that the standard local character is trivial on the local integers, so the places of
  \(T\setminus S\) contribute nothing to the character on the image of the restriction.  All
  declarations audited with `#print axioms`; they use only `propext`, `Classical.choice`, and
  `Quot.sound`.  The card's hostile-audit item "compatibility of these local multiplier
  representations with every restriction map of the semilocal sheaf is not yet proved" is now
  discharged.
