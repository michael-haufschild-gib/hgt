# Xi Arakelov--Hurwitz differential-dependence collision

- **ID:** `xi-arakelov-hurwitz-differential-dependence-collision`
- **Stage:** 3-formalized
- **Type:** TOP-DOWN FUNCTION-VALUE RELATION / ARITHMETIC COLLISION
- **Scientific status:** `[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean module:** `formal/GaloisForLFunctions/RHTower/XiArakelovHurwitzDependenceCollision.lean`

## Exact two-function value law

For nonintegral exponents `s,t`, Lean packages the two analytically continued Hurwitz functions in
the shift variable and proves

\[
\widetilde\zeta(s,\cdot),\widetilde\zeta(t,\cdot)
\text{ are differentially dependent over }\mathbb C(a)
\iff
e^{-2\pi i s}=e^{-2\pi i t}.
\]

Thus an actual algebraic differential relation transfers the monodromy-character value. It is not
necessary to postulate equality of the characters directly.

## Determinant-one rank-two trace reformulation

Pair Hurwitz functional-equation eigencharacters as

\[
q(s),\qquad q(s)^{-1}=q(1-s).
\]

Their determinant is identically `1`; define unlabelled characteristic-polynomial coefficient

\[
T(s)=q(s)+q(s)^{-1}.
\]

Lean proves exact algebraicity law

\[
T(s)\in\overline{\mathbb Q}
\iff q(s)\in\overline{\mathbb Q}.
\]

Nontrivial direction is quadratic, not choice of square-root branch.  If `T` is algebraic, then

\[
(2q-T)^2=T^2-4;
\]

algebraicity of square forces `2q-T` algebraic, hence `q` algebraic.  This packages source target as
algebraic trace of determinant-one rank-two character rather than selected eigenvalue.  Resulting
global right-half predicate is proved exactly equivalent to original character predicate and hence
exactly equivalent to RH.

Hostile direction is explicit: if `w(s)` is algebraic and `s` is nonreal, then `T(s)` is
transcendental.  Therefore trace packaging improves geometric source interface but supplies no
unconditional algebraicity producer.

## Pair-anchor chain to RH

Suppose every hypothetical right-half Xi divisor point `rho` has:

1. algebraic Arakelov coordinate `w(rho)=1-1/rho`; and
2. a nonintegral Hurwitz anchor `tau` whose character `q(tau)` is algebraic and whose continued
   Hurwitz function is differentially dependent with the function indexed by `rho`.

Then

\[
\begin{aligned}
\widetilde\zeta(\rho,\cdot)
  \text{ dependent with }\widetilde\zeta(\tau,\cdot)
&\Longrightarrow q(\rho)=q(\tau),\\
q(\tau)\in\overline{\mathbb Q}
&\Longrightarrow q(\rho)\in\overline{\mathbb Q},\\
w(\rho),q(\rho)\in\overline{\mathbb Q}
&\Longrightarrow \rho\in\mathbb R,\\
\xi(\rho)=0,\quad0<\Re\rho<1,\quad\rho\in\mathbb R
&\Longrightarrow\bot.
\end{aligned}
\]

Therefore RH follows.

## Finite-anchor strengthening

Lean also proves a finite differential-matroid closure version. Let

\[
\{\widetilde\zeta(\tau_i,\cdot):i\in I\}
\]

be a finite family of nonintegral anchors with pairwise distinct algebraic monodromy characters.
If adjoining `widetilde zeta(rho,.)` destroys differential independence, then

\[
q(\rho)=q(\tau_i)
\]

for some anchor `i`. Hence one finite algebraic-character Hurwitz atlas which captures every
hypothetical right-half Xi function, together with algebraicity of the corresponding Arakelov
coordinates, forces RH.

The complete chain is

```text
finite algebraic-character Hurwitz anchor family
  + Xi Hurwitz functions lie in its differential-matroid closure
  -> every right-half Xi monodromy character is algebraic

right-half Xi Arakelov coordinates are algebraic
  + algebraic Xi monodromy characters
  -> Gelfond--Schneider exponent rationality
  -> no right-half Xi zero
  -> RH.
```

## Anti-redressing attack

The factors have different blind spots.

- Differential dependence with an anchor fixes only the exponent class modulo `Z`. The anchor can
  be nonreal and need not belong to the RH chamber.
- Algebraicity of the anchor characters supplies arithmetic but no critical-line orientation.
- Algebraicity of the Xi Arakelov coordinate makes the exponent algebraic but does not locate it.
- Only the simultaneous Arakelov and monodromy algebraicity invokes Gelfond--Schneider and forces
  rationality.

The finite-anchor theorem is stronger than merely assuming an algebraic Xi character because it
asks for a concrete differential relation with a finite source family. Nevertheless, the exact
Hurwitz differential-matroid classification makes the transfer a bridge rather than new scientific
knowledge.

## Open core

`[OPEN CORE]` Construct a finite nonintegral Hurwitz anchor family with algebraic, pairwise distinct
monodromy characters and prove that every hypothetical right-half Xi-indexed continued-Hurwitz
function lies in its differential-matroid closure. Independently, construct algebraic Arakelov
coordinates for those hypothetical divisor points.

The value relation must be supplied by an actual algebraic differential identity or a source module
whose differential rank is bounded by the anchor family. Restating equality of monodromy characters
does not discharge the task.

This is a fringe route. Unconditional Xi-indexed Hurwitz differential independence makes such a
finite capture highly restrictive, and no algebraic Arakelov divisor model is currently present.

## Formal verification

Lean proves:

- `continuedHurwitzPairDifferentiallyDependent_iff_monoScalar_eq`;
- `hurwitzFECharacterTrace`;
- `hurwitzFECharacterDet`;
- `hurwitzFECharacterDet_eq_one`;
- `hurwitzFECharacterTrace_isAlgebraic_iff_monoScalar_isAlgebraic`;
- `hurwitzFECharacterTrace_transcendental_of_arakelovW_algebraic_of_im_ne_zero`;
- `xiRightArakelovHurwitzAlgebraic_of_dependentOnAlgebraicCharacter`;
- `riemannHypothesis_of_xiRightArakelovAlgebraicHurwitzDependentOnAlgebraicCharacter`;
- `exists_anchor_monoScalar_eq_of_continuedHurwitzDependentOverAnchors`;
- `monoScalar_isAlgebraic_of_continuedHurwitzDependentOverAlgebraicAnchors`;
- `riemannHypothesis_of_xiRightArakelovAlgebraic_of_finiteHurwitzAnchorCapture`;
- `XiRightArakelovAlgebraicHurwitzDependentOnAlgebraicFETrace`;
- `xiRightArakelovAlgebraicHurwitzDependentOnAlgebraicFETrace_iff_character`;
- `riemannHypothesis_of_xiRightArakelovAlgebraicHurwitzDependentOnAlgebraicFETrace`;
- `xiRightArakelovAlgebraicHurwitzDependentOnAlgebraicFETrace_iff_riemannHypothesis`.

The module contains no new axiom or admitted proof.

## Finite-anchor closure classification — 2026-07-22

The finite-anchor result above initially recorded only the forward implication. Under the stated
nonintegrality and monodromy-separation hypotheses, the intrinsic continued-Hurwitz differential
matroid gives the exact equivalence

\[
\widetilde\zeta(s,\cdot)\text{ lies in the finite-anchor differential closure}
\iff
\exists i,\ q(s)=q(\tau_i).                                  \tag{F1}
\]

The forward direction is the existing finite matroid theorem. Conversely, if
`q(s)=q(tau_i)`, then the augmented character map on `Option I` identifies `none` with `some i`.
The intrinsic matroid law says differential independence is equivalent to injectivity of this
character map, so the augmented family is dependent. This closes the proof of (F1).

If every anchor character is algebraic while `arakelovW(s)` is algebraic and `Im(s) != 0`, (F1)
cannot hold: capture makes `q(s)` equal an algebraic anchor character, while the
Gelfond--Schneider collision makes `q(s)` transcendental. Therefore

\[
\operatorname{Im}s\ne0,\quad W(s)\in\overline{\mathbb Q}
\quad\Longrightarrow\quad
\widetilde\zeta(s,\cdot)\text{ is independent over every finite separated
algebraic-character atlas}.                                  \tag{F2}
\]

Verdict: `[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`. Equations (F1)–(F2) are exact positive
classification/no-capture statements inside the project-specific Hurwitz matroid. They close the
possibility that a noncanonical finite algebraic atlas evades the pair-anchor obstruction. Any
surviving Xi source must abandon at least one of: finite separated atlas, algebraic anchor
characters, algebraic Arakelov coordinate, or nonreal divisor point.

Lean declarations added for this closure:

- `continuedHurwitzDifferentiallyDependentOverAnchors_iff_exists_monoScalar_eq`;
- `not_continuedHurwitzDependentOverAlgebraicAnchors_of_arakelovW_algebraic_of_im_ne_zero`.

Direct source verification passes.  Both declarations use only `propext`, `Classical.choice`, and
`Quot.sound` under `#print axioms`.
