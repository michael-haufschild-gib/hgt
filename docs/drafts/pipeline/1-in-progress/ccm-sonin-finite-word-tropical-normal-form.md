# CCM Sonin finite-word tropical normal form

- **ID:** `ccm-sonin-finite-word-tropical-normal-form`
- **Stage:** 1-in-progress
- **Type:** THEOREM PROGRAM / OPERATOR-ALGEBRA STRUCTURE
- **Scientific register:** `[CONJECTURE]` until the finite-word operator theorem is proved;
  the two-factor input is `[PROVED]`
- **Route:** Connes--Consani quasi-inner/Sonin spaces and the semilocal CCM operator program

## Main theorem target

Fix the even Sonin projection at aperture `a>0`.  For scales `p,q>1`, let

\[
G_a(p,q)=L_p^*L_q,
\qquad
L_p=(1-Q_a)(U_p+U_p^{-1})Q_a.
\]

For every nonempty finite word

\[
W=G_a(p_1,q_1)\cdots G_a(p_n,q_n),
\]

define the associated multiplicative interval data by repeatedly intersecting the current shell
with the inverse-dilated shell of the next factor and multiplying the dilation coordinates.  The
canonical datum is a ceiling `C(W)`, floor `F(W)`, and displacement `x(W)>0`, normalized by

\[
F(W)\ge a,
\qquad
x(W)F(W)\ge a,
\qquad
F(W)\le C(W).
\]

`[CONJECTURE]` The following hold.

1. **Finite-word normal form.**  Modulo compact operators, `W` is the sum of the physical and
   Fourier window translations determined by `(C(W),F(W),x(W))`.
2. **Sharp compactness law.**  `W` is compact if and only if `F(W)=C(W)`.
3. **Polar law.**  If `F(W)<C(W)`, then the Calkin class of `W` is a partial isometry.  Its initial
   and final projections are the two-polarization shells obtained from the domain and range
   intervals of the canonical datum.
4. **Faithful normal form.**  Two nondegenerate canonical window translations are compactly equal
   if and only if their ceiling, floor, and displacement data agree.

For a composable path

\[
G_a(r_0,r_1)G_a(r_1,r_2)\cdots G_a(r_{n-1},r_n),
\]

the normal form simplifies: its shell thickness is

\[
\min_{0\le j\le n}r_j,
\]

and it is compactly equal to the direct entry `G_a(r_0,r_n)` exactly when the minimum of the path
is attained at an endpoint.  Thus the Calkin product retains the minimum scale visited as a
tropical memory coordinate.

## Positive carrier law

The successful semilocal carrier is forced to retain an interval-valued partial symmetry, not only
a scalar boundary character or a finite projection spectrum.  Each local Gram entry transports a
two-polarization shell.  Finite products intersect and translate those shells, while compactness is
exactly degeneration of the transported interval.  On prime-labelled paths the retained memory is
an arithmetic minimum and cannot be removed by compact quotienting.

## Existing unconditional foundation

The current Lean corpus already proves:

- pair normal forms and initial/final Calkin projections in
  `SoninEulerCalkinPartialIsometry.lean`;
- matching-middle three-scale composition, pinch rigidity, and the minimum-of-three thickness law
  in `SoninEulerTripleShellOverlap.lean`;
- independent-middle intersection/translation, the exact two-factor compactness criterion, and
  the cross-window initial projection in `SoninEulerCrossShellOverlap.lean`;
- finite prime matrix injectivity modulo compacts in `SoninEulerFiniteGramLower.lean`.

These are inputs, not a proof of the finite-word theorem.

## Parent-theory attack

- `[SEARCH]` Partial translations of intervals form an inverse semigroup; inverse-semigroup and
  Wiener--Hopf groupoid theory are classical.
- `[SEARCH]` Products of truncated Toeplitz and Wiener--Hopf operators have extensive parent
  theories.
- `[SURVIVING RESIDUE]` The prospective content is the exact two-polarization realization on the
  genuine Sonin constraint, the compact decoupling of physical and Fourier branches, and the full
  finite-word compactness classification for the CCM Gram operators.
- `[RETIREMENT CONDITION]` If a primary source already identifies the same Sonin Gram-generated
  Calkin inverse semigroup or proves the same finite-word normal form, classify this as a bridge.

## Proof program

1. Define canonical multiplicative window data and its normalized composition law.
2. Prove the general physical and Fourier window multiplication formulas.
3. Prove normalization against the central Sonin complement.
4. Induct over nonempty finite words to obtain the operator normal form.
5. Prove interval-shell rigidity modulo compact operators.
6. Derive compactness, polar data, and uniqueness of canonical normal forms.
7. Specialize to composable paths and prime-labelled paths.

## Gates

- [x] Exact nontrivial residue isolated after the scalar Frostman result reduced to parent theory.
- [x] Existing two-factor operator theorem and sharp zero-divisor criterion located in Lean.
- [ ] Complete finite-word paper proof.
- [ ] Complete unconditional Lean formalization with no hypotheses hiding analytic content.
- [ ] Full primary-source inverse-semigroup/Wiener--Hopf/Sonin priority audit.
- [ ] Standalone paper only if the final theorem scores at least 90/100.

## Current score

- Scalar transverse profile alone: **68/100** (`[BRIDGE]`).
- Existing two-factor cross law: **84/100**, novelty unverified.
- Full faithful finite-word normal form, if proved and priority-clean: **91/100** provisionally.

The score is mathematical, not formal: Lean verification cannot increase it.
