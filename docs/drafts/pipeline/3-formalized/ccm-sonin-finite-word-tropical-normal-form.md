# CCM Sonin finite-word tropical normal form

- **ID:** `ccm-sonin-finite-word-tropical-normal-form`
- **Stage:** 3-formalized theorem; publication and priority audit remain in progress
- **Type:** THEOREM / OPERATOR-ALGEBRA STRUCTURE
- **Scientific register:** `[PROVED]`; `[NOVELTY-PENDING]` until the final primary-source audit
- **Route:** Connes--Consani quasi-inner/Sonin spaces and the semilocal CCM operator program

## Main theorem

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

`[PROVED]` The following hold.

1. **Finite-word normal form.**  Modulo compact operators, `W` is the sum of the physical and
   Fourier window translations determined by `(C(W),F(W),x(W))`.
2. **Sharp compactness law.**  `W` is compact if and only if `F(W)=C(W)`.
3. **Polar law.**  If `F(W)<C(W)`, then the Calkin class of `W` is a partial isometry.  Its initial
   and final projections are the two-polarization shells obtained from the domain and range
   intervals of the canonical datum.
4. **Faithful normal form.**  Two nondegenerate canonical window translations are compactly equal
   if and only if their ceiling, floor, and displacement data agree.
5. **Faithful word classification.**  Two arbitrary nonempty words of genuine CCM Gram corners
   are compactly equal if and only if their recursively computed zero/live states are literally
   equal.
6. **Regular involutive semigroup law.**  At every positive base aperture, the canonical states
   form an associative semigroup with absorbing zero.  The involution
   \[
   (C,F,x)^*=(xC,xF,x^{-1})
   \]
   is carried exactly by Hilbert-space adjunction, reverses products, is involutive, and satisfies
   both regularity identities.  Canonical source and range states are idempotent, canonical range
   idempotents commute, and every state is represented by a Calkin partial isometry.
7. **Inverse-semigroup rigidity.**  Every idempotent is fixed by the involution, all idempotents
   commute, and the displayed involution is the unique algebraic inverse of every canonical
   state.

`[PROVED]` For a composable path

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

The successful semilocal carrier retains an interval-valued partial symmetry, not only a scalar
boundary character or a finite projection spectrum.  Each local Gram entry transports a
two-polarization shell.  Finite products intersect and translate those shells, while compactness is
exactly degeneration of the transported interval.  The compact quotient retains the complete
zero/live interval state faithfully, and adjunction supplies its canonical inverse.

## Unconditional formal theorem surface

The corpus proves the complete theorem without project axioms or analytic interfaces in:

- `formal/GaloisForLFunctions/RHTower/CCMSoninFiniteWordNormalForm.lean`;
- `formal/GaloisForLFunctions/RHTower/CCMSoninFiniteWordFaithfulness.lean`;
- `formal/GaloisForLFunctions/RHTower/CCMSoninInverseSemigroup.lean`;
- `formal/GaloisForLFunctions/RHTower/CCMSoninPathTropicalMemory.lean`.

The capstones are:

- `finiteSoninGramWord_compactEq_state`;
- `finiteSoninGramWord_isCompactOperator_iff_state_zero`;
- `finiteSoninGramWords_compactEq_iff_normalState_eq`;
- `SoninLiveWindow.operator_compactEq_iff`;
- `composeSoninWindowStates_assoc`;
- `composeSoninWindowStates_inverse`;
- `composeSoninWindowStates_inverse_regular` and its dual;
- `composeSoninWindowStates_range_idempotent` and the source analogue;
- `composeSoninWindowStates_range_comm`;
- `ccmSoninFiniteWord_faithful_regular_star_semigroup`;
- `ccmSoninWindowState_inverseSemigroup`;
- `SoninScalePath.operator_compactEq_window`;
- `SoninScalePath.pathWindow_eq_iff_minimum_eq`;
- `SoninScalePath.operator_not_isCompactOperator`;
- `SoninScalePath.operator_compactEq_direct_iff_minimum_eq_endpointMin`.

The prior inputs remain:

- pair normal forms and initial/final Calkin projections in
  `SoninEulerCalkinPartialIsometry.lean`;
- matching-middle three-scale composition, pinch rigidity, and the minimum-of-three thickness law
  in `SoninEulerTripleShellOverlap.lean`;
- independent-middle intersection/translation, the exact two-factor compactness criterion, and
  the cross-window initial projection in `SoninEulerCrossShellOverlap.lean`;
- finite prime matrix injectivity modulo compacts in `SoninEulerFiniteGramLower.lean`.

The finite-word modules convert those inputs into the complete classification above.

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

## Proof architecture

1. Define canonical multiplicative window data and its normalized composition law.
2. Prove the general physical and Fourier window multiplication formulas.
3. Prove normalization against the central Sonin complement.
4. Induct over nonempty finite words to obtain the operator normal form.
5. Prove two-polarization shell endpoint rigidity modulo compact operators.
6. Recover ceiling, floor, and displacement from the final and initial Calkin projections.
7. Transfer operator associativity and adjunction back through faithfulness to obtain the exact
   regular involutive state semigroup.
8. Prove commutation of canonical range idempotents by physical/Fourier shell decoupling.
9. Deduce uniqueness of the algebraic inverse from regularity and commutation of all idempotents.
10. Specialize a composable scale path and prove that its Calkin class remembers exactly its two
    endpoints and the minimum scale visited.

## Gates

- [x] Exact nontrivial residue isolated after the scalar Frostman result reduced to parent theory.
- [x] Existing two-factor operator theorem and sharp zero-divisor criterion located in Lean.
- [x] Complete finite-word mathematical proof.
- [x] Complete unconditional Lean formalization with no hypotheses hiding analytic content.
- [x] Exact target-module build.
- [x] Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
- [ ] Full primary-source inverse-semigroup/Wiener--Hopf/Sonin priority audit.
- [ ] Standalone paper only if the final theorem scores at least 90/100.

## Current score

- Scalar transverse profile alone: **68/100** (`[BRIDGE]`).
- Existing two-factor cross law: **84/100**, novelty unverified.
- Faithful finite-word inverse-semigroup and tropical path-memory theorem: **84/100**.  The exact
  Sonin realization and compact-faithful path invariant appear nontrivial, but the abstract
  inverse-semigroup mechanism has classical Wiener--Hopf and partial-translation parents.  It is
  retained as useful CCM structure, not promoted as the 90/100 paper theorem.

The score is mathematical, not formal: Lean verification cannot increase it.
