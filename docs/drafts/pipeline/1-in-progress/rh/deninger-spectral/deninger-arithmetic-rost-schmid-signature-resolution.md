# Arithmetic Rost--Schmid/signature resolution on Deninger's flow space

- **ID:** `deninger-arithmetic-rost-schmid-signature-resolution`
- **Stage:** 1-in-progress
- **Type:** SOURCE CONJECTURE
- **Label:** `DAC_ARITHMETIC_ROST_SCHMID_SIGNATURE_RESOLUTION`
- **Parent:** `deninger-derived-mw-rational-witt-coefficient`
- **Target:** concrete analytic Tate--Milnor coefficient and its
  \(H^0,H^1,H^2\); optional \(R\alpha_*\mathscr G\) realization

## Source constraints

Deninger's rational-Witt construction supplies the space, prime packets,
power maps, connected subsystem, and suspension flow.  It does not supply the
relevant coefficient complex.  His primary paper explicitly formulates the
missing object as a complex of sheaves \(R\alpha_*\mathscr G\) on the
rational-Witt approximation and also states that the approximation is
infinite-dimensional and has no established analytic structure.

On a cyclotomic character field algebraic over \(\mathbb Q\),
`DAC_DENINGER_EQUIVARIANT_TATE_REGULATOR_KUMMER`,
`DAC_PRO_STEIN_CYLINDER_ANALYTIC_LEAF`,
`DAC_PRO_STEIN_RELATIVE_CELL_GLOBAL_SECTIONS`,
`DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE`,
`DAC_CHARACTER_SHAPE_FORMALITY`,
`DAC_GEOMETRIC_MW_RANK_COLLAPSE`, and
`DAC_ALGEBRAIC_CYCLOTOMIC_MILNOR_AMPLITUDE` prove that the real geometric
analytic Tate--Milnor coefficient has a proved pro-Stein chartwise
derived-section algebra having only
\[
 H^0=\mathbb R,\qquad
 H^1=(F^\times/\mu_\infty)\otimes\mathbb R.                           \tag{1}
\]
This is a statement about chartwise derived sections, not stalks.
`DAC_KUMMER_SHEAF_STALK_TOR_OBSTRUCTION` proves that the sheafified pushout
can have extra stalk Tor.  Quadratic information is absent from the
nonreal chartwise geometric section algebra and survives in twisted
residue/Gysin maps and at real places.

Déglise--Feld--Jin's Theorem 4.4.20 supplies a decisive boundary condition.
For a Dedekind domain \(R\) with \(r\) real places, positive Milnor--Witt
weights above one retain a copy of \(\mathbb Z^r\).  Thus a full realified
Milnor--Witt signature tower would create unwanted classes in every higher
degree.  Deninger's arithmetic-curve complex must retain the degree-two
orientation class but not the higher signature tower.

## Conjecture

`[CONJECTURE] [DAC_ARITHMETIC_ROST_SCHMID_SIGNATURE_RESOLUTION]`

Let
\[
 X_W=\check X_0(\mathbb C)_E\times_{\mathbb Q_{>0}}\mathbb R_{>0},
 \qquad X_0=\operatorname{Spec}\mathbb Z .
\]
There is a functorial connective \(E_\infty\)-algebra sheaf
\(\mathscr A_{\mathrm{arith}}\) on \(X_W\), constructed from the analytic
Tate--Milnor character coefficient, coherent Galois descent, diagonal
rational-power/prime localization, and the real signature boundary, with
the following properties.

### 1. Arithmetic-curve derived-section window

Let \(\mathscr A_{\mathrm{raw}}\) be the unital rank/signature pullback of
the sheafified unit-amalgamated coefficient.  Its stalks are not assumed
two-term.  There is instead a multiplicative, power-natural window on its
**arithmetic derived-section descent diagram** which retains:

1. the connected generic rank in derived-section degree zero;
2. the chartwise unit-amalgamated character algebra in degree one;
3. one real orientation \(\mathbb R(-1)\) in degree two;
4. no higher real signature weights.

This window is constructed before taking the zeta comparison.  It may be
realized by a source-natural Postnikov localization of the descent diagram,
but it is not asserted to be the ordinary stalkwise truncation of
\(\mathscr A_{\mathrm{raw}}\).

### 2. Two-level arithmetic localization descent

There is a derived localization/descent equivalence
\[
 R\Gamma(X_W,\mathscr A_{\mathrm{arith}})
 \simeq
 \operatorname{Tot}\!\left(
   G^{0,\bullet}\xrightarrow{\partial}G^{1,\bullet}
   \ ;\ \mathbb R(-1)[-2]
 \right),                                                            \tag{2}
\]
where:

1. \(G^{0,\bullet}\) is the Galois-coinduced derived section complex on
   generic cyclotomic character charts;
2. \(G^{1,\bullet}\) is the restricted product of derived section
   complexes on prime packets with twisted MW residue coefficients;
3. \(\partial\) is the Rost--Schmid boundary of
   `DAC_COARSE_INVARIANT_SHEAF_ROST_SCHMID_DESCENT`, transported through
   Deninger's universally integral finite correspondences; the
   non-proper suspension quotient was already formed degreewise at the
   sheaf level and is not a second differential;
4. after `DAC_SHEAFIFIED_UNIT_AMALGAMATION_COMPARISON`, both
   \(G^{0,\bullet}\) and \(G^{1,\bullet}\) have amplitude \([0,1]\);
5. the last summand is the archimedean signature orientation.

Thus the required two columns are columns of an arithmetic
localization/hypercover model for **derived sections**.  They are not claimed
to be resolutions of two-term homotopy sheaves.

### 3. Concrete three-term complex

Choose two-term representatives
\(G^{p,0}\to G^{p,1}\) for the two derived-section columns in `(2)`.
Write
\[
 h_0:G^{0,0}\to G^{1,0},\qquad
 h_1:G^{0,1}\to G^{1,1}                                             \tag{3}
\]
for the horizontal Rost--Schmid boundaries,
\[
 v_0:G^{0,0}\to G^{0,1},\qquad
 v_1:G^{1,0}\to G^{1,1}                                             \tag{4}
\]
for the internal coefficient differentials, and
\[
 \sigma_{10}:G^{1,0}\to\mathbb R(-1),\qquad
 \sigma_{01}:G^{0,1}\to\mathbb R(-1)                                \tag{5}
\]
for the two real-signature boundaries.  The exact required identities are
\[
 v_1h_0=h_1v_0,\qquad
 \sigma_{10}h_0+\sigma_{01}v_0=0.                                   \tag{6}
\]
The first is residue/internal compatibility; the second is global
signature reciprocity.

Derived global sections are then quasi-isomorphic to
\[
 L^0=G^{0,0},                                                        \tag{7}
\]
\[
 L^1=G^{1,0}\oplus G^{0,1},                                         \tag{8}
\]
\[
 L^2=G^{1,1}\oplus\mathbb R(-1),                                    \tag{9}
\]
with differential
\[
 d^0(a)=(h_0a,v_0a),                                                \tag{10}
\]
\[
 d^1(c,b)=
 \bigl(v_1c-h_1b,\ \sigma_{10}c+\sigma_{01}b\bigr).                 \tag{11}
\]
Equations `(6)` give \(d^1d^0=0\) term by term.
`DAC_TWO_COLUMN_HYPERCOHOMOLOGY_AMPLITUDE` then proves, without a dimension
assumption on \(X_W\), that
\[
 H^n(R\Gamma(X_W,\mathscr A_{\mathrm{arith}}))=0
 \quad(n\notin\{0,1,2\}).                                           \tag{12}
\]

This algebraic totalization and the implication `(6)` \(\Rightarrow\)
\(d^1d^0=0\) are formalized unconditionally in
`DeningerArithmeticTwoColumnSignatureTotalization.lean`; direct Lean
verification awaits a low-load window.

### 4. Endpoints and middle degree

Deninger's connectedness theorem and the unital descent square identify
\[
 H^0=\mathbb R(0).                                                   \tag{13}
\]
There is a chain-level arithmetic trace
\[
 \operatorname{tr}:L^2\longrightarrow\mathbb R(-1)                  \tag{14}
\]
whose finite residue and real signature components satisfy global
reciprocity.  The multiplicative residue adjunction makes the pairing of the
three-term complex self-dual with total weight one.  Hence the induced
pairing is perfect and `(13)` forces
\[
 H^2=\mathbb R(-1).                                                  \tag{15}
\]
The reduced middle group is infinite-dimensional because the descended
character-unit term in `(8)` has a noncompact leafwise completion not killed
by the prime-residue image.

### 5. Power and flow naturality

Proper pushforward and coherent Gysin pullback for every power map preserve
`(2)`--`(11)`, the trace, and the duality pairing.  After
\(\mathbb Q_{>0}\)-localization and suspension they induce a strongly
continuous flow acting by cochain automorphisms.  Its generator \(\Theta\)
commutes with \(d\); it is not a cohomological differential.

## Step-by-step construction

1. Build the Galois-coinduced generic coefficient from the pro-Stein
   analytic Tate--Milnor complex; form Deninger's degreewise invariant
   sheaf on the coarse suspension and prove the internal-amplitude part of
   `DAC_COARSE_INVARIANT_SHEAF_ROST_SCHMID_DESCENT`.
2. Build the prime-packet derived-section complex from twisted MW residue
   targets and prove finite-correspondence descent.
3. Construct \(\partial_0,\partial_1\), including ramified Gysin coherence.
4. Prove the arithmetic localization/hypercover comparison `(2)`.  A valid
   proof must use the actual sheaf coefficient and cannot replace it by its
   chartwise global algebra.
5. Construct the unital real Betti/signature pullback and its multiplicative
   arithmetic derived-section window.
6. Identify its extension class with the two signature maps in `(5)`;
   prove both identities `(6)` and obtain `(7)`--`(11)`.
7. Prove connected constants `(13)`, construct the trace `(14)`, and prove
   chain-level self-duality; derive `(15)`.
8. Prove survival and infinite-dimensionality of reduced \(H^1\).
9. Descend Frobenius/Verschiebung and suspend to the transverse flow.

## Hostile audit and falsifiers

- **Full MW tower fails.**  Déglise--Feld--Jin compute a real-place
  \(\mathbb Z^r\) in every MW weight \(q>1\).  If the construction retains
  these groups in the same cohomological theory, `(12)` is false.
- **Local amplitude is insufficient.**  The failed route
  `deninger-local-amplitude-implies-global-amplitude` shows that `(1)` does
  not imply `(12)` without the derived localization equivalence `(2)`.
- **Stalk amplitude is false for the naïve pushout.**
  `DAC_KUMMER_SHEAF_STALK_TOR_OBSTRUCTION` produces
  \(\Lambda^2V_F\) in stalk Tor.  The two-column model must be a theorem
  about arithmetic derived-section descent, not a fabricated homotopy-sheaf
  resolution.
- **Plain arithmetic Rost--Schmid homology is too small.**  Its groups over a
  one-dimensional arithmetic scheme are finitely generated.  Infinite
  \(H^1\) must come from the character/leafwise sheaves on \(X_W\), not from
  bare \(\operatorname{Spec}\mathbb Z\).
- **Smooth foliation citations do not establish `(2)`.**  Deninger's
  present approximation is infinite-dimensional and has no constructed
  analytic atlas or partition of unity.
- **Orientation is not positivity.**  The signature line and determinant
  twists can provide trace duality but do not supply the positive Hodge
  metric required for RH.
- **Postnikov truncation must be source-natural.**  Failure of the
  arithmetic-curve window to preserve multiplication, residues, or power
  maps falsifies the conjecture.
- **Global cochains are not sheaves.**  The residue resolution must be built
  from the sheafified unit-amalgamated coefficient.  A chartwise
  global-section algebra has no restriction or residue maps by itself.

## Literature status

- Deninger constructs the rational-Witt flow space and states the missing
  \(R\alpha_*\mathscr G\) problem, but does not construct `(2)`--`(11)`.
- Déglise--Feld--Jin construct the arithmetic Rost--Schmid operations and
  compute the real signature survivor, but not their realization on
  Deninger's flow space.
- Smooth leafwise de Rham theory supplies analogous three-term complexes only
  after a smooth finite-dimensional foliation is given.

No cited source proves this conjecture.

**Verdict:** `SURVIVES SECOND HOSTILE AUDIT`.  Exact open core is the
sheafified chart comparison, the arithmetic localization equivalence `(2)`,
the multiplicative derived-section signature window, and chain-level
reciprocity/duality.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*:
  https://arxiv.org/abs/1807.06400
- Christopher Deninger, *Rational Witt vectors and associated sheaves*:
  https://arxiv.org/abs/2508.05329
- Frédéric Déglise, Niels Feld, Fangzhou Jin,
  *Homological Milnor-Witt modules and Chow-Witt groups over general bases*,
  especially §1.3 and Theorem 4.4.20:
  https://arxiv.org/abs/2512.09876
- Frédéric Déglise, Niels Feld, Fangzhou Jin,
  *Homotopy coherent Gysin functoriality*:
  https://arxiv.org/abs/2605.01855
