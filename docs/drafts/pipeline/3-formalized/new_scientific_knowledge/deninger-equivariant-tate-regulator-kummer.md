# Deninger's equivariant Tate-regulator Kummer class

- **ID:** `deninger-equivariant-tate-regulator-kummer`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper; literature extraction)
- **Label:** `DAC_DENINGER_EQUIVARIANT_TATE_REGULATOR_KUMMER`
- **Parent:** `deninger-derived-mw-rational-witt-coefficient`
- **Statement:** Deninger's suspension cover already carries the canonical
  Tate-twisted degree-one Kummer class required by the arithmetic coefficient.

## Source theorem

Let
\[
 \widetilde X=\check X(\mathbb C)\times\mathbb R_{>0},\qquad
 \widetilde G=G\times\mathbb Q_{>0},
\]
with
\[
 (\check P,u)(\sigma,q)=(F_q(\check P^\sigma),q^{-1}u).
\]
For
\[
 Q_0=\mathbb Z[p^{-1}\mid p\in\operatorname{char}N_0],
\]
Deninger defines the equivariant Tate sheaf \(Q_0(1)\) by letting \(q\)
act on its fiber as multiplication by \(q^{-1}\).  On \(\widetilde X\)
he proves the exact equivariant exponential sequence
\[
 0\longrightarrow Q_0(1)
 \longrightarrow \mathcal C
 \xrightarrow{\,E\,}
 \mathcal C^\times\otimes Q_0(1)
 \longrightarrow 1,                                                  \tag{1}
\]
where
\[
 E(\alpha)=\exp(2\pi i\,u^{-1}\alpha)\otimes1.                        \tag{2}
\]
The \(u^{-1}\) factor is forced by equivariance; it is not an optional
normalization.

For an integral normal \(X_0\), the Teichmüller evaluation of an invertible
regular function gives
\[
 [\,\cdot\,]:
 \Gamma(X_0,\mathcal O^\times)\otimes Q_0
 \longrightarrow
 \Gamma(\widetilde X,
   \mathcal O^\times_{\mathcal F c}\otimes Q_0(1))^{\widetilde G}.     \tag{3}
\]
The connecting morphism of `(1)` therefore gives Deninger's regulator
\[
 r:
 \Gamma(X_0,\mathcal O^\times)\otimes Q_0
 \longrightarrow
 H^1(\widetilde X,Q_0(1))^{\widetilde G}.                             \tag{4}
\]
Deninger's Proposition 12.1 proves that the kernel of `(4)` is contained
in the prime-to-\(N_0\) roots of unity.

## Character-component calculation

For the generic algebraic field \(K\), set
\[
 V_K=K^\times\otimes_{\mathbb Z}\mathbb Q
     =K^\times/\mu(K)\otimes_{\mathbb Z}\mathbb Q
\]
and
\[
 Y_K=\operatorname{Hom}(V_K,S^1).
\]
The natural inclusion \(Y_K\hookrightarrow\widetilde X\) restricts `(4)`
to the connecting map of
\[
 0\longrightarrow Q_0
 \longrightarrow\mathcal C
 \longrightarrow\mathcal C^\times\otimes Q_0
 \longrightarrow1                                                   \tag{5}
\]
on \(Y_K\).  Kucharczyk--Scholze's pro-torus calculation gives
\[
 H^\bullet(Y_K,Q_0)
 \cong\Lambda^\bullet_{\mathbb Q}(V_K).                              \tag{6}
\]
Under `(6)`, the restricted connecting map sends
\[
 f\otimes1\longmapsto f\otimes1\in V_K=H^1(Y_K,Q_0).                 \tag{7}
\]
Indeed, after projecting to the one-dimensional rational line generated
by \(f\), the class is the obstruction to a continuous logarithm of the
first-coordinate character on the solenoid
\(\varprojlim_n S^1\); its pullback to \(S^1\) is the standard generator
of \(H^1(S^1,\mathbb Z)\).

Consequently the degree-one Kummer map used in the arithmetic coefficient
is source-defined and injective modulo torsion.  It is not a conjectural
map
\[
 V_F\to H^1(X_F,\mathcal R_{X_F})
\]
with an unspecified twist.  Its correct source is the equivariant Tate
local system \(Q_0(1)\) on Deninger's suspension cover, and its real form
uses \(\mathbb R(1)\).

## New consequence for the construction

Let \(\mathcal P_F^{\mathrm{Den}}\) be the free positive
\(E_\infty\)-algebra on the regulator morphism `(7)` in the equivariant
derived sheaf category.  The two source maps
\[
 \mathcal P_F^{\mathrm{Den}}\longrightarrow
 \mathcal C^\bullet(Y_F,\mathbb R(1)),
 \qquad
 \mathcal P_F^{\mathrm{Den}}\longrightarrow
 \mathcal K^M_{F,\mathbb R}
\]
are therefore canonical and power-natural: Frobenius sends a unit to its
\(q\)-th power while the Tate fiber contributes \(q^{-1}\).
Their derived base change is the correctly twisted local
unit-amalgamation.  The algebraic calculation that this base change has
cohomology
\[
 \mathbb R\oplus
 ((F^\times/\mu_\infty)\otimes\mathbb R)[-1]
\]
is `DAC_ALGEBRAIC_CYCLOTOMIC_MILNOR_AMPLITUDE`.

This closes existence, injectivity modulo torsion, and the missing Tate
twist of the local Kummer input.  It does **not** prove that a sheaf
pushout on the coarse suspension commutes with derived global sections,
nor does it construct finite-place residues, the archimedean orientation,
or Hodge positivity.

## Hostile audit

- Ordinary groupoid-derived invariants are not silently substituted for
  Deninger's invariant group in `(4)`.  Non-properness is exactly why he
  uses \(H^1(\widetilde X,Q_0(1))^{\widetilde G}\) as a replacement for
  \(H^1(X_0,Q_0(1))\).
- The weight-one twist is fixed by `(2)` and cannot be dropped.
- `(6)` is an exterior algebra in all degrees.  Milnor--Steinberg
  correction remains necessary; the pro-torus by itself is not the
  desired arithmetic coefficient.
- For \(X_0=\operatorname{Spec}\mathbb Z\), global algebraic units alone
  are too small.  The construction must retain generic character classes
  before Galois, residue, and suspension descent.

**Verdict:** `FULLY PROVEN ON PAPER; LOCAL KUMMER INPUT AND TATE TWIST
CLOSED`.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  §12, especially equations (128)--(138) and Proposition 12.1:
  https://arxiv.org/abs/1807.06400
- Robert A. Kucharczyk and Peter Scholze,
  *Topological realisations of absolute Galois groups*, Proposition 3.8:
  https://people.mpim-bonn.mpg.de/scholze/GaloisTop.pdf

## Log

- 2026-07-26 — Extracted Deninger's source-defined equivariant
  Tate-regulator class; replaced the untwisted conjectural Kummer input.

## Lean status

### The source-defined content landed

`formal/GaloisForLFunctions/RHTower/DeningerEquivariantTateRegulator.lean`.  Axiom audit for all
15 declarations: `propext, Classical.choice, Quot.sound`.

Deninger's Proposition 12.1 and Kucharczyk--Scholze's Proposition 3.8 are the imported literature
inputs; what is formalized is the source structure this card extracts from them.

- `deningerTateExp` — the equivariant exponential `(2)`, with the suspension parameter in the
  exponent: `E_u(α) = exp(2πi α/u)`.  `deningerTateExp_add` is its additivity and
  `deningerTateExp_ne_zero` lands it in the invertible functions.
- `deningerTateExp_eq_one_iff` — **the kernel of `(1)` is the Tate lattice `uℤ`**, the fibre of the
  equivariant Tate sheaf `Q₀(1)` at parameter `u`.
- `deningerTateExp_surjective` — the exponential is onto the invertible functions, so `(1)` is
  right exact.
- `deningerTateExp_exact` — the exactness of `(1)` as a `Function.Exact` statement: the lattice
  is exactly the kernel.
- `deningerTateExp_equivariant` — scaling the suspension parameter and the weight-one coefficient
  by the same positive rational leaves the exponential unchanged.
- `deningerExpScalar_injective`, `deningerTateWeight_forced` — **the `u⁻¹` factor is forced**: a
  family `exp(2πi c(u)α)` with that invariance has `c(u) = c(1)/u`.  This is the card's claim that
  the weight-one twist of `(2)` is not an optional normalization, proved rather than asserted; the
  first lemma is the separating step (an exponential character determines its linear coefficient).
- `deningerRationalTwist_cancel` — **power-naturality**: on the rationalization, the `q`-th power
  of a unit paired with the Tate fibre `q⁻¹` is the original class.  This is exactly "Frobenius
  sends a unit to its `q`-th power while the Tate fibre contributes `q⁻¹`".
- `deningerRationalization_isLocalizedModule`, `deningerRationalization_eq_zero_iff` — the
  rationalization is the localization at the nonzero integers, so its kernel is exactly the
  torsion.
- `deningerKummerKernel_isTorsion`, `deningerKummerKernel_of_root` — **injectivity modulo
  torsion**: on a field the kernel of the rationalized Kummer class is exactly the roots of unity,
  which is the character-component form of Proposition 12.1's conclusion and the sense in which
  `V_K = K^×⊗ℚ = (K^×/μ(K))⊗ℚ` of the card's setup is legitimate.

### Remaining

Nothing source-defined.  The imported inputs stay imported: Deninger's Proposition 12.1 itself,
Kucharczyk--Scholze's pro-torus computation `(6)` — mathlib has no sheaf or singular cohomology of
a solenoid, so `(6)` and the identification of `(7)` with the generator of `H¹(S¹,ℤ)` cannot be
stated there.  The card's own exclusions — the sheaf pushout commuting with derived global
sections, finite-place residues, the archimedean orientation, and Hodge positivity — remain open.
