# Three-term cup product and Poincaré descent

- **ID:** `deninger-three-term-cup-poincare-descent`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Parent:** `deninger-three-term-arithmetic-cohomology`
- **Statement:** A degree-two cochain pairing satisfying graded differential adjunction descends
  to \(H^0\times H^2\) and \(H^1\times H^1\); exact cochain radicals characterize
  Poincaré nondegeneracy.

## Goal

Supply the cup/trace/Poincaré step of Deninger's arithmetic cohomology independently of any
analytic zeta model.  The theorem identifies exactly what the derived rational-Witt coefficient
must prove at chain level.

## Gates

- [x] 0 → 1 in-progress: source-pure statement and falsifiable hypotheses
- [x] 1 → 2 fully-proven: dependency-closed proof below
- [x] 2 → 3 formalized: `DeningerArithmeticThreeTermCupDescent.lean` checks and builds
- [ ] 3 → 4 publication-ready: instantiate on arithmetic coefficient complex

## Theorem

`[PROVED HERE] [DAC_THREE_TERM_CUP_DESCENT]`

Let
\[
 A^0\xrightarrow{d^0}A^1\xrightarrow{d^1}A^2,\qquad d^1d^0=0
\]
be a complex over a commutative ring \(R\).  Suppose there are bilinear pairings
\[
 b_{02}:A^0\times A^2\to R,\qquad b_{11}:A^1\times A^1\to R
\]
such that
\[
 b_{11}(d^0x,y)+b_{02}(x,d^1y)=0                                    \tag{1}
\]
and
\[
 b_{11}(x,y)=-b_{11}(y,x).                                           \tag{2}
\]
Then:

1. \(b_{02}\) descends canonically to
   \[
     \bar b_{02}:H^0(A)\times H^2(A)\to R;                            \tag{3}
   \]
2. \(b_{11}\) descends canonically to
   \[
     \bar b_{11}:H^1(A)\times H^1(A)\to R;                            \tag{4}
   \]
3. `(4)` remains skew-symmetric.

Define cochain radicals inside the cocycles \(Z^1=\ker d^1\):
\[
\begin{aligned}
 \operatorname{Rad}_L
   &=\{x\in Z^1:\forall y\in Z^1,\ b_{11}(x,y)=0\},\\
 \operatorname{Rad}_R
   &=\{y\in Z^1:\forall x\in Z^1,\ b_{11}(x,y)=0\}.
\end{aligned}
\]
Writing \(B^1=\operatorname{im}d^0\), equations `(1)` and `(2)` imply
\[
 B^1\subseteq\operatorname{Rad}_L\cap\operatorname{Rad}_R.            \tag{5}
\]
The descended pairing `(4)` separates both variables exactly when
\[
 \operatorname{Rad}_L=B^1=\operatorname{Rad}_R.                       \tag{6}
\]
For a skew pairing the two radical equalities are equivalent.

## Proof

If \(x\in H^0=\ker d^0\) and \(z=d^1y\), `(1)` gives
\[
 b_{02}(x,z)=-b_{11}(d^0x,y)=0,
\]
so \(b_{02}(x,-)\) kills \(B^2=\operatorname{im}d^1\) and factors uniquely through
\(H^2=A^2/B^2\).  Linearity in \(x\) gives `(3)`.

If \(u=d^0x\in B^1\) and \(y\in Z^1\), `(1)` gives
\[
 b_{11}(u,y)=-b_{02}(x,d^1y)=0.
\]
Thus \(B^1\) is contained in the left radical on cocycles.  By `(2)` it is also contained
in the right radical.  The universal property of the quotient
\(H^1=Z^1/B^1\) gives `(4)`, and `(2)` survives quotienting.

The left radical of `(4)` is exactly
\(\operatorname{Rad}_L/B^1\), and its right radical is exactly
\(\operatorname{Rad}_R/B^1\).  Therefore both vanish exactly under `(6)`.  Finally `(2)`
exchanges left and right radicals, proving the last assertion.

## Flow compatibility

`[PROVED HERE] [DAC_THREE_TERM_CUP_FLOW_DESCENT]`

Assume commuting cochain endomorphisms \(\Theta_q\) additionally satisfy
\[
\begin{aligned}
 b_{02}(\Theta_0x,z)+b_{02}(x,\Theta_2z)&=b_{02}(x,z),\\
 b_{11}(\Theta_1x,y)+b_{11}(x,\Theta_1y)&=b_{11}(x,y).                 \tag{7}
\end{aligned}
\]
Since \(\Theta\) preserves cycles and boundaries, equations `(7)` pass to `(3)` and `(4)`.
Thus the induced cohomological generator has weight one for Poincaré duality.  Centering
degree one gives the skew relation for \(\Theta_1-\tfrac12\) once a positive Hodge metric
identifies cup duality with the Hilbert adjoint.

## Arithmetic obligations

For the derived Milnor--Witt rational-Witt coefficient, it is enough to prove:

1. Rost--Schmid residue adjunction `(1)`;
2. graded commutativity `(2)`;
3. exact radical identity `(6)`;
4. Frobenius projection formula `(7)`.

Items 1, 2, and 4 are structural transfer statements.  Item 3 is the genuine Poincaré
perfectness theorem; nondegeneracy cannot be inferred merely from a nonzero trace.

## Hostile audit

- Bare Grothendieck--Witt transfer may satisfy `(1)` while being indefinite.  This theorem
  proves algebraic duality, not Hodge positivity.
- A pairing on cochains is not automatically perfect on cohomology.  Failure of `(6)` gives
  the exact obstruction.
- The existing Xi-divisor pairing can instantiate this theorem as a comparison target, but
  cannot establish `(6)` for the arithmetic coefficient source.

## Log

- 2026-07-26 — paper theorem completed; exact radical criterion isolates source Poincaré gate.
- 2026-07-26 — unconditional generic Lean module written for endpoint descent, middle
  two-variable quotient descent, skewness, and exact radical/separation equivalence.  No build
  launched while shared Lean load is saturated.

## Unconditional Lean formalization

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerArithmeticThreeTermCupDescent.lean` checks with
`lake env lean` and builds; axiom audit `propext, Classical.choice, Quot.sound`.

- `DeningerArithmeticThreeTermCupPairing` — the chain data: `pair02`, `pair11`, the differential
  adjunction `(1)` and the skewness `(2)`.
- `boundaries2_le_pair02_ker`, `pairH02`, `pairH02Linear`, `pairH02Linear_mkQ` — clause 1,
  equation `(3)`: `b₀₂` descends to `H⁰ × H²`.
- `boundaries1_le_pairCycles11_ker`, `pairH11Left`, `cycles1ToH1Dual`,
  `boundaries1_le_cycles1ToH1Dual_ker`, `pairH11`, `pairH11_mkQ_mkQ` — clause 2, equation `(4)`,
  including the two-variable descent through `(5)` `B¹ ⊆ Rad_L ∩ Rad_R`.
- `pairH11_skew` — clause 3.
- `radical1`, `pairH11_separating_iff_radical1_eq_boundaries1` — the exact criterion `(6)`:
  the descended middle pairing separates exactly when the cochain radical equals `B¹`.
- `DeningerArithmeticThreeTermWeightOneCup`, `endpoint_weight_on_cohomology`,
  `middle_weight_on_cohomology`, `thetaH2_eq_id` — the flow-compatibility half
  `DAC_THREE_TERM_CUP_FLOW_DESCENT`, equation `(7)` and its descent.

All four arithmetic obligations remain hypotheses of the Lean statements, as the card requires.
