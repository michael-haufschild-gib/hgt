# Equivariant Tate-graded leafwise unit amalgamation

- **ID:** `deninger-leafwise-sheafified-unit-amalgamation`
- **Stage:** 1-in-progress
- **Type:** PRIMARY SOURCE CONSTRUCTION / DESCENT CONJECTURE
- **Labels:** `DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE`,
  `DAC_SHEAFIFIED_UNIT_AMALGAMATION_COMPARISON`
- **Parent:** `deninger-relative-sullivan-milnor-character-space`
- **Target:** equivariant derived coefficient on Deninger's suspension cover,
  followed by a coefficient complex on the rational-Witt approximation;
  optional \(R\alpha_*\mathscr G\) realization

## Deninger's actual leafwise coefficient

For a suspension
\[
 \pi:\widetilde X=M\times\mathbb R_{>0}
 \longrightarrow X=M\times_Q\mathbb R_{>0},
\]
Deninger defines \(\mathcal R_{\widetilde X}\) to be the sheaf of
real-valued functions that are continuous and locally constant in the
\(M\)-variable at fixed transverse coordinate.  He then defines
\[
 \mathcal R_X=(\pi_*\mathcal R_{\widetilde X})^Q                     \tag{1}
\]
and
\[
 H^\bullet_{\mathcal F}(X)=H^\bullet(X,\mathcal R_X).                \tag{2}
\]
The flow acts on `(2)`.  Deninger's Theorem 10.2 proves
\[
 H^0_{\mathcal F}(X)=\mathbb R                                      \tag{3}
\]
for the connected arithmetic systems in his paper.

Deninger explicitly gives complexes of sheaves on the rational-Witt
approximation as the direct route when the true space is unavailable.
Accordingly, the construction below starts on Deninger's equivariant
suspension cover and only then descends to the coarse flow space.  A later map
\(\alpha_F:X_F^M\to X_F\) with
\(R\alpha_{F,*}\mathbb R\simeq\mathscr A^M_{F,\mathrm{geom}}\) would
geometrize it, but arithmetic descent does not wait for that optional
enhancement.  A chartwise cochain algebra is its expected derived global
section, not a stalk.

## Source correction: Tate-graded cover first

The previous formulation postulated an untwisted Kummer map into
\(H^1(X_F,\mathcal R_{X_F})\).  Deninger's §12 constructs a different and
more rigid source object: the equivariant Tate sheaf \(Q_0(1)\) on
\(\widetilde X\), its exponential sequence, and a regulator into
\[
 H^1(\widetilde X,Q_0(1))^{\widetilde G}.
\]
`DAC_DENINGER_EQUIVARIANT_TATE_REGULATOR_KUMMER` proves that restriction
to the generic pro-torus is the canonical inclusion of units modulo
torsion into degree-one cohomology.  The \(u^{-1}\) factor in Deninger's
exponential and the Tate twist are forced by power equivariance.

Products of weight-one symbols require every nonnegative Tate weight, while
`DAC_PURE_SUSPENSION_SCALAR_SPECTRUM_NO_GO` proves that the pure symbol
algebra cannot supply the zeta spectrum.  Retain the analytic leafwise
factor of `DAC_PRO_STEIN_CYLINDER_ANALYTIC_LEAF` and define
\[
 \mathscr T_{\widetilde X}
 :=\Omega^\bullet_{\mathrm{cyl},F}
   \widehat\otimes\bigoplus_{n\ge0}\mathbb R(n),\qquad
 \mathbb R(m)\otimes\mathbb R(n)\to\mathbb R(m+n),                   \tag{4}
\]
with unit in de Rham degree zero and Tate weight zero.  The analytic
Frobenius action is non-scalar on chains even though its action on local
Milnor cohomology is pure.

## Formal equivariant sheaf construction

Fix a cyclotomic component \(\widetilde X_F\) of the suspension cover.
Let \(\mathscr V_F(1)\) be the weight-one real equivariant local system
associated with
\[
 V_F=(F^\times/\mu_\infty)\otimes_{\mathbb Z}\mathbb R .
\]
The source regulator gives
\[
 \kappa_F:V_F\longrightarrow
 H^1(\widetilde X_F,\mathbb R(1))                                    \tag{5}
\]
and, by the constant-sheaf/global-section adjunction, a morphism
\[
 H\mathscr V_F(1)[-1]\longrightarrow\mathscr T_{\widetilde X_F}.      \tag{6}
\]
By the free bigraded commutative-algebra adjunction, `(6)` extends
uniquely to
\[
 \mathscr P_F
 :=
 \operatorname{Free}^{+}_{E_\infty,\mathscr T}
   (H\mathscr V_F(1)[-1])
 \longrightarrow\mathscr T_{\widetilde X_F}.                         \tag{7}
\]

Let \(\underline{\mathcal K}^{M}_{F,\mathbb R}\) and
\(\underline{\mathcal K}^{MW}_{F,\mathbb R}\) denote the locally constant
Tate-graded sheaf \(E_\infty\)-algebras obtained from the real diagonal
motivic symbol algebras, with \(K_n\) in weight \(n\).  Their unit symbols
give maps from \(\mathscr P_F\).  Define on the cover
\[
 \widetilde{\mathscr A}^M_{F,\mathrm{geom}}
 :=
 \mathscr T_{\widetilde X_F}
 \mathop{\otimes}^{\mathbb L}_{\mathscr P_F}
 \underline{\mathcal K}^{M}_{F,\mathbb R},                           \tag{8}
\]
\[
 \widetilde{\mathscr A}^{MW}_{F,\mathrm{geom}}
 :=
 \mathscr T_{\widetilde X_F}
 \mathop{\otimes}^{\mathbb L}_{\mathscr P_F}
 \underline{\mathcal K}^{MW}_{F,\mathbb R}.                          \tag{9}
\]

`[PAPER-PROVED] [DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE]`

The Kummer input `(5)` is source-proved.  Constructions `(7)`--`(9)` exist
functorially by the constant-sheaf/global-section adjunction, the free
bigraded \(E_\infty\)-algebra adjunction, and the homotopy-pushout universal
property.  They preserve restriction, Galois, power, and Tate-weight maps
and are genuine equivariant derived coefficient sheaves on the suspension
cover.  This formal existence theorem asserts neither a cohomology
calculation nor effective descent to the coarse quotient.

`DAC_KUMMER_SHEAF_STALK_TOR_OBSTRUCTION` proves that `(8)` is generally not
two-term on stalks.  A Kummer class becomes null after taking a stalk, so the
stalkwise pushout contains
\[
 \operatorname{Tor}_1^{\Lambda(V_F)}
   (\mathbb R,\mathbb R\oplus V_F)
 \cong\Lambda^2V_F.
\]
This does not disqualify `(8)` as a derived coefficient: derived sheaves
can have complicated stalks.  It does disqualify every
argument that transfers chartwise global amplitude directly to homotopy
sheaves.

## Comparison conjecture

`[CONJECTURE] [DAC_SHEAFIFIED_UNIT_AMALGAMATION_COMPARISON]`

The sheaf construction satisfies:

1. **Chartwise derived sections.**
   \[
   R\Gamma(\widetilde X_F,
     \widetilde{\mathscr A}^M_{F,\mathrm{geom}})
   \simeq
   C^*_{\mathrm{sh}}(\widetilde X_F;\mathscr T)
   \mathop{\otimes}^{\mathbb L}_{\mathcal P_{F,\mathbb R}}
   \mathcal K^M_{F,\mathbb R}.                                      \tag{10}
   \]
   Thus `DAC_CHARACTER_SHAPE_FORMALITY`,
   `DAC_RELATIVE_SULLIVAN_MILNOR_RESOLUTION`, and
   `DAC_ALGEBRAIC_CYCLOTOMIC_MILNOR_AMPLITUDE` imply that `(10)` is the
   two-term algebra
   \[
   \mathbb R\oplus V_F[-1]
   \]
   with square-zero positive part.
   No stalkwise amplitude assertion is included.

   `DAC_PRO_STEIN_RELATIVE_CELL_GLOBAL_SECTIONS` proves this clause for
   the pro-Stein cylinder-analytic refinement.  The remaining comparison
   is from those pro-Ind analytic sections to ordinary coarse-suspension
   derived sections.

2. **Geometric MW collapse.**
   The map from the MW object to the ordinary object in `(8)`--`(9)` is
   an equivalence for
   \(F=\overline{\mathbb Q}\), and is an equivalence after realification for
   every nonreal cyclotomic character field.

3. **Descent.**
   The sheaves `(8)`--`(9)`, their Kummer maps, and every relative motivic
   cell descend coherently under Galois maps, finite correspondences,
   Rost--Schmid residues, and power maps.

4. **Deninger degree zero.**
   Unit amalgamation does not change the leafwise constant sheaf in degree
   zero.  After the connected \(Q\)-suspension descent, `(3)` remains the
   global \(H^0\).

5. **Coarse invariant-sheaf localization.**
   Form the degreewise invariant sheaf
   \((\pi_*\widetilde{\mathscr A})^{\mathbb Q_{>0}}\) before derived
   global sections, as in Deninger's Definition 10.1.  Then apply the
   separate prime Rost--Schmid differential of
   `DAC_COARSE_INVARIANT_SHEAF_ROST_SCHMID_DESCENT`.  Deninger's
   cover-invariant regulator is an edge map, not the whole spectral
   cohomology.

6. **Optional pushforward realization.**  If
   `DAC_RELATIVE_MILNOR_CHARACTER_REALIZATION` is constructed, then
   \[
     R\alpha_{F,*}\mathbb R
     \simeq \mathscr A^M_{F,\mathrm{geom}}.                           \tag{11}
   \]

## Remaining proof after the pro-Stein comparison

Derived global sections do not generally preserve homotopy pushouts of
commutative algebra sheaves.  The finite-stage pro-Stein construction
establishes the relative-cell comparison using Cartan theorem B.  To pass
to Deninger's coarse suspension one must establish one of:

1. the relevant \(\mathscr P_F\)-modules are dualizable and the projection
   formula applies;
2. `(8)` has a relative cellular presentation whose cells are
   \(\Gamma\)-acyclic, so global sections commute with its geometric
   realization;
3. a monoidal Čech/hypercover descent theorem identifies both sides.

Shape formality of the already-global cochain algebra proves neither
the sheaf comparison `(10)`, diagonal localization descent, nor the optional
pushforward comparison `(11)`.

## Step-by-step proof program

1. Use `DAC_DENINGER_EQUIVARIANT_TATE_REGULATOR_KUMMER` for the unit local
   system and sheaf-level Kummer morphism `(6)` on the suspension cover.
2. Construct the free algebra `(7)` and the locally constant motivic symbol
   algebra sheaves.
3. Give `(8)` a relative positive-cell presentation, including Steinberg and
   every higher syzygy cell.
4. Prove restriction and Galois compatibility cell by cell.
5. Apply `DAC_PRO_STEIN_RELATIVE_CELL_GLOBAL_SECTIONS` to obtain `(10)` on
   the analytic refinement; prove comparison to the coarse suspension.
6. Construct `DAC_COARSE_INVARIANT_SHEAF_ROST_SCHMID_DESCENT` and compare
   its degree-one regulator edge with Deninger's source target.
7. Apply the proved global shape formality theorem only after `(10)`.
8. Transport twisted MW residue/Gysin operations before invoking geometric
   MW collapse.
9. Optional: construct \(\alpha_F\) and prove the Eilenberg--Moore
   pushforward comparison `(11)`.

## Hostile audit and falsifiers

- Kummer existence and its Tate twist are source-proved.  Failure can now
  occur in the Milnor cell comparison or coarse suspension descent, not in
  existence of the degree-one regulator.
- Failure of a relative pro-realization \(\alpha_F\) blocks the optional
  geometric interpretation, not the sheaf-defined arithmetic cohomology.
- If global sections fail to commute with the relative cell realization,
  the previously proved chartwise algebra cannot compute `(8)`.
- Treating the already-global chart cochains as a sheaf would repeat the
  failed chart-cochains-as-sheaf route and lose local residue maps.  The
  genuine equivariant sheaf pushout `(8)` avoids that type error.
- Treating the chartwise two-term result as a stalkwise two-term result is
  false by `DAC_KUMMER_SHEAF_STALK_TOR_OBSTRUCTION`.
- Full \(\mathbb A^1\)-localization remains forbidden because scaling
  contracts Deninger's reduced rational-Witt coordinate.
- This construction fixes the coefficient sheaf but does not prove the
  two-column acyclicity, signature window, cup duality, Hodge positivity, or
  Lefschetz formula.

**Verdict:** `EQUIVARIANT TATE-GRADED COVER SHEAF EXISTENCE PAPER-PROVED;
GLOBAL-SECTION, EXACT-WEIGHT COARSE DESCENT, AND ARITHMETIC-OPERATION
COMPARISONS OPEN; OPTIONAL GEOMETRIC PUSHFORWARD OPEN; STALK AMPLITUDE
FALSIFIED`.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  Definition 10.1, Theorem 10.2, §12, and Proposition 12.1:
  https://arxiv.org/abs/1807.06400
- Robert A. Kucharczyk and Peter Scholze,
  *Topological realisations of absolute Galois groups*:
  https://people.mpim-bonn.mpg.de/scholze/GaloisTop.pdf
- Jacob Lurie, *Higher Algebra*:
  https://www.math.ias.edu/~lurie/papers/HA.pdf
