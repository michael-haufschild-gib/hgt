# Relative Sullivan Milnor character space

- **ID:** `deninger-relative-sullivan-milnor-character-space`
- **Stage:** 1-in-progress
- **Type:** SOURCE REALIZATION CONJECTURE
- **Label:** `DAC_RELATIVE_MILNOR_CHARACTER_REALIZATION`
- **Parent:** `deninger-leafwise-sheafified-unit-amalgamation`
- **Target:** construct the local map \(\alpha_F:X_F^M\to X_F\)

## Motivation

Kucharczyk--Scholze construct \(X_F\) with the correct finite covering
theory, but its integral cohomology is the exterior algebra on
\(F^\times/\mu_\infty\).  Their Question 1.10 asks for a corrected space
whose cohomology is torsion-free Milnor \(K\)-theory.  Deninger identifies
the corresponding global gap as a map
\[
 \alpha:X_{\mathrm{arith}}\longrightarrow X_W
\]
and the coefficient complex \(R\alpha_*\mathscr G\).

For an algebraic cyclotomic \(F/\mathbb Q\), the real target algebra is
\[
 K^M_\ast(F)\otimes\mathbb R
 \cong
 \mathbb R\oplus
 ((F^\times/\mu_\infty)\otimes\mathbb R)[-1],                         \tag{1}
\]
with square-zero positive part.  The map on cohomology must have direction
\[
 \Lambda(V_F)\longrightarrow\mathbb R\oplus V_F,                     \tag{2}
\]
so the geometric map must have direction \(X_F^M\to X_F\).

## Algebraic input

`DAC_RELATIVE_SULLIVAN_MILNOR_RESOLUTION` constructs an unconditional
relative Sullivan factorization
\[
 \Lambda(V_F)
 \longrightarrow
 Q_F
 \xrightarrow{\sim}
 \mathbb R\oplus V_F.                                                 \tag{3}
\]
The first relative generators have degree one and transgress to the
Steinberg/higher degree-two products.  Subsequent generators kill the
syzygies created by earlier stages.

## Conjecture

`[CONJECTURE] [DAC_RELATIVE_MILNOR_CHARACTER_REALIZATION]`

For every algebraic characteristic-zero field \(F\supset\mu_\infty\), there
is a functorial pro-space or derived topological stack \(X_F^M\) and a map
\[
 \alpha_F:X_F^M\longrightarrow X_F                                  \tag{4}
\]
with the following properties.

1. **Real cochains.**
   There is an \(E_\infty\)-quasi-isomorphism under
   \(C^*(X_F;\mathbb R)\):
   \[
   C^*(X_F^M;\mathbb R)\simeq Q_F.                                   \tag{5}
   \]
   Hence
   \[
   H^\ast(X_F^M;\mathbb R)
   \cong K_\ast^M(F)\otimes\mathbb R,                                \tag{6}
   \]
   and \(\alpha_F^\ast\) is the Milnor quotient `(2)`.

2. **Finite-cover invariance.**
   The finite Baumslag packet fibers are connected and aspherical, with
   uniquely divisible fundamental group.  Their coherent pro-assembly
   preserves that exact surjective \(\pi_1\) structure, and every finite
   cover descends effectively to a finite stage.  Then
   `DAC_DIVISIBLE_FIBER_FINITE_COVER_INVARIANCE` induces an equivalence of finite covering
   categories
   \[
   \operatorname{FEC}(X_F^M)\simeq\operatorname{FEC}(X_F),            \tag{7}
   \]
   so both have profinite fundamental group \(G_F\).

3. **Integral refinement.**
   There is an integral/profinite enhancement whose cohomology is
   \(K_\ast^M(F)_{\mathrm{tf}}\), not merely its realification, and whose
   real realization is `(4)`--`(6)`.

4. **Milnor--Witt operations.**
   Twisted MW residues, transfers, and determinant-line orientations act on
   the system before realification.  On nonreal geometric charts the
   nonnegative MW and ordinary realizations agree; the quadratic channel is
   retained in residue/Gysin functoriality.

5. **Naturality.**
   The maps `(4)` are homotopy-coherently compatible with field
   embeddings, Galois descent, finite correspondences, and the power maps
   producing Frobenius and Verschiebung.

6. **Coefficient comparison.**
   The derived pushforward
   \[
   \mathscr A_{F,\mathrm{geom}}
   :=R\alpha_{F,*}\mathbb R                                          \tag{8}
   \]
   is equivalent to the sheafified unit-amalgamated candidate of
   `DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE`.  Consequently
   \[
   R\Gamma(X_F,\mathscr A_{F,\mathrm{geom}})
   \simeq C^*(X_F^M;\mathbb R),                                      \tag{9}
   \]
   proving `DAC_SHEAFIFIED_UNIT_AMALGAMATION_COMPARISON`.

## Step-by-step construction

1. Use the finite Baumslag free-rational packets of
   `DAC_BAUMSLAG_FREE_RATIONAL_MILNOR_PACKET` and construct their
   basis-independent, inclusion-functorial fiberwise homotopy pullbacks in
   `DAC_BAUMSLAG_MILNOR_PRO_REALIZATION`.
2. Prove the twisted relative Eilenberg--Moore comparison at each finite
   unit stage.
3. Form the inverse pro-object and compare its continuous cochains with the
   paper-proved algebraic finite-unit colimit.
4. Prove coherent transition maps preserve the connected, exact,
   divisible packet fibers.
5. Prove effective pro-cover descent and apply
   `DAC_DIVISIBLE_FIBER_FINITE_COVER_INVARIANCE` stagewise to obtain `(7)`.
6. Construct the integral/profinite enhancement using the full motivic
   symbol cell algebra rather than only the real square-zero quotient.
7. Transport Galois, residue, and power operations through the functorial
   cell filtration.
8. Prove the Eilenberg--Moore/derived-pushforward comparison `(8)`.

## Hostile audit and falsifiers

- Classical Sullivan realization applies to nilpotent finite-type spaces.
  \(X_F\) and \(V_F\) are not known to satisfy those hypotheses.  A
  non-Sullivan realization theorem is mandatory.  More strongly,
  `deninger-one-shot-infinite-sullivan-realization` uses Zhou's theorem to
  rule out ordinary one-shot realization because \(H^1\) is
  infinite-dimensional, and
  `deninger-fiberwise-finite-sullivan-pro-realization` rules it out already
  at finite rank two because Malcev completion creates \(H_2\).
- A rational pro-space cannot alone recover integral finite covers or
  torsion-free integral Milnor groups.  Clause 3 is independent work.
- Unique divisibility of each Baumslag packet kernel is paper-proved, but
  it must survive the coherent pro-assembly.  It cannot be inferred merely
  from rational coefficients in `(3)`.
- A divisible kernel has no finite quotient, but an uncontrolled action,
  failure of exactness, or ineffective pro-cover descent can still spoil
  `(7)`.
- Exact preservation of \(\pi_1\) is not a stronger acceptable substitute:
  `deninger-exact-pi1-preserving-milnor-correction` proves that it forces
  nonzero rational \(H^2\) on every finite torus stage of rank at least two.
  The divisible kernel is therefore necessary.
- The naïve sheaf pushout has the stalk Tor computed by
  `DAC_KUMMER_SHEAF_STALK_TOR_OBSTRUCTION`.  Clause 6 must reproduce, not
  discard, such derived-pushforward stalk structure.
- A wedge of circles realizes `(1)` as a cohomology algebra but changes the
  finite covering group.  It does not satisfy `(7)`; the exact no-go and
  surviving relative-fiber mechanism are recorded in
  `deninger-wedge-of-circles-milnor-realization`.
- None of `(4)`--`(9)` supplies the global prime residues, archimedean
  signature, Poincaré duality, Hodge positivity, or zeta determinant.

## Positive content already closed

- Correct cohomology algebra `(1)`.
- Correct map direction `(4)`.
- Functorial algebraic relative Sullivan resolution `(3)`.
- Basis-chosen finite Baumslag packet with square-zero rational cohomology,
  formal CDGA cochains, and connected divisible fiber.
- Stagewise finite-cover invariance from
  `DAC_DIVISIBLE_FIBER_FINITE_COVER_INVARIANCE`.

**Verdict:** `SURVIVES FOURTH HOSTILE AUDIT`.  Ordinary Sullivan
realization is literature-falsified both globally and at rank two.
`DAC_BAUMSLAG_FREE_RATIONAL_MILNOR_PACKET` supplies a paper-proved
finite-stage replacement with square-zero rational cohomology and divisible
kernel.  Exact open core is its basis-independent coherent assembly,
twisted Eilenberg--Moore theorem, continuous-cochain colimit, and effective
pro-cover descent, followed by integral/profinite and arithmetic-operation
enhancement.  Stagewise finite-cover invariance is paper-closed.

## References

- Robert A. Kucharczyk and Peter Scholze,
  *Topological realisations of absolute Galois groups*, Question 1.10:
  https://people.mpim-bonn.mpg.de/scholze/GaloisTop.pdf
- Christopher Deninger, *Dynamical systems for arithmetic schemes*:
  https://arxiv.org/abs/1807.06400
- Dennis Sullivan, *Infinitesimal computations in topology*.
- Yves Félix, Stephen Halperin, Jean-Claude Thomas,
  *Rational Homotopy Theory*.
