# Baumslag Milnor pro-realization

- **ID:** `deninger-baumslag-milnor-pro-realization`
- **Stage:** 1-in-progress
- **Type:** SOURCE REALIZATION CONJECTURE
- **Label:** `DAC_BAUMSLAG_MILNOR_PRO_REALIZATION`
- **Parent:** `deninger-relative-sullivan-milnor-character-space`
- **Target:** construct the rational pro-space underlying
  \(\alpha_F:X_F^M\to X_F\)

## Finite-stage construction

Let
\[
 V_{F,\mathbb Q}=(F^\times/\mu_\infty)\otimes\mathbb Q.
\]
For a finite-dimensional \(U\subset V_{F,\mathbb Q}\), put
\(A_U=U^\vee\).  The finite Kummer classes give
\[
 \kappa_U:X_F\longrightarrow BA_U.                                 \tag{1}
\]
`DAC_BAUMSLAG_FREE_RATIONAL_MILNOR_PACKET` supplies, after choosing a
basis, a map
\[
 BR_U\longrightarrow BA_U                                         \tag{2}
\]
with square-zero rational cohomology and connected divisible fiber.
Define
\[
 X^M_{F,U}:=X_F\mathop{\times}^{h}_{BA_U}BR_U.                      \tag{3}
\]
The projection \(\alpha_{F,U}:X^M_{F,U}\to X_F\) preserves every finite
cover unconditionally.

Unlike Sullivan/\(\mathbb Q\)-completion, Baumslag rationalization retains
the rational homology of a free group.  The failed alternative is recorded
in `deninger-fiberwise-finite-sullivan-pro-realization`.

## Conjecture

`[CONJECTURE] [DAC_BAUMSLAG_MILNOR_PRO_REALIZATION]`

The packets `(2)` admit a basis-independent homotopy-coherent refinement
over the filtered category of finite-dimensional unit subspaces such that:

1. **Twisted pullback cochains.**
   \[
   C^\ast(X^M_{F,U};\mathbb Q)
   \simeq
   C^\ast(X_F;\mathbb Q)
   \mathop{\otimes}^{\mathbb L}_{\Lambda(U)}
   (\mathbb Q\oplus U).                                             \tag{4}
   \]
2. **Continuous pro-cochains.**  For the inverse system
   \[
   X_F^M:=\{X^M_{F,U}\}_U,
   \]
   \[
   C^\ast_{\mathrm{cont}}(X_F^M;\mathbb Q)
   \simeq\mathbb Q\oplus V_{F,\mathbb Q}[-1].                       \tag{5}
   \]
   The algebraic colimit is already proved by
   `DAC_FINITE_UNIT_MILNOR_COLIMIT`.
3. **Pro-cover descent.**  Every finite cover of \(X_F^M\) descends
   effectively to a finite stage.  The stagewise equivalences therefore
   give
   \[
   \operatorname{FEC}(X_F^M)\simeq\operatorname{FEC}(X_F).          \tag{6}
   \]
4. **Pushforward comparison.**
   \[
   R\alpha_{F,*}\mathbb Q
   \simeq\mathscr A^M_{F,\mathrm{geom},\mathbb Q},                  \tag{7}
   \]
   the leafwise sheafified unit-amalgamated coefficient.
5. **Arithmetic naturality.**  The system is compatible with field
   embeddings, Galois action, finite correspondences, and power maps.
6. **Integral/MW enhancement.**  An integral/profinite cell refinement has
   cohomology \(K_\ast^M(F)_{\mathrm{tf}}\) and transports twisted MW
   residues, transfers, and orientations.

Tensoring `(4)`--`(7)` with \(\mathbb R\) gives Deninger's local real
coefficient.

## Closed content

- Each basis-chosen finite packet `(2)` exists and has the exact target
  rational cohomology, and `DAC_TWO_TERM_CDGA_FORMALITY` identifies its
  connected rational CDGA cochains with the square-zero algebra.
- Its connected kernel is uniquely divisible.
- Each finite pullback `(3)` preserves finite-cover categories.
- The algebraic filtered colimit of the right side of `(4)` is exactly the
  full square-zero Milnor algebra.
- Exact preservation of \(\pi_1\) is impossible by
  `deninger-exact-pi1-preserving-milnor-correction`; the divisible kernel is
  forced.

## Exact open core

1. Replace basis choices by a homotopy-coherent group-valued functor of
   \(U\).  Equivalently, construct coherent lifts of rational linear maps
   through automorphisms and correspondences of free rational groups.
2. Prove the non-simply-connected, local-coefficient
   Eilenberg--Moore comparison `(4)`.
3. Prove continuous pro-cochains commute with the filtered algebraic
   colimit, with no derived-limit correction.
4. Prove effective pro-cover descent `(6)`.
5. Prove the leafwise monadic pushforward comparison `(7)`.
6. Construct integral/profinite and MW-operation enhancements.

## Hostile audit

- A basis change acts on \(U\) through \(GL(U)\), but a strict coherent lift
  to automorphisms of a free rational group is not supplied by ordinary
  Nielsen generators.  Homotopy coherence is an actual obstruction.
- The Eilenberg--Moore formula over \(BA_U\) is not automatic.  Its
  fundamental-group action must be included.
- Baumslag rationalization is not Malcev completion and is not represented
  by the relative Sullivan algebra.  A comparison can only be asserted at
  the cochain level after `(4)` is proved.
- Rational group homology does not supply integral Milnor symbols or MW
  residues.
- Stagewise finite-cover equivalence does not itself prove effective
  descent for the pro-object.

**Verdict:** `SURVIVES FIRST HOSTILE AUDIT`; it is the first finite-stage
topological packet found with both square-zero rational cohomology and a
finite-quotient-invisible relative kernel.

## References

- Gilbert Baumslag, *Some aspects of groups with unique roots*.
- Carles Casacuberta and Georg Peschke, *Localizing with respect to
  self-maps of the circle*.
- Sergei O. Ivanov, *An overview of rationalization theories of
  non-simply connected spaces and non-nilpotent groups*:
  https://arxiv.org/abs/2111.10694
