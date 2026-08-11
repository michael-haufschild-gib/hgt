# Centered Bregman evenization, fibre current, and jet reconstruction law

- **ID:** ULF-RFCM-1
- **Stage:** 2-fully-proven
- **Type:** FORMATION / COMPLETION / INFORMATION-LOSS CLASSIFICATION THEOREM
- **Statement:** A centered two-endpoint first jet modulo affine gauge is classified by one
  symmetric response and one directed fibre current; these reconstruct both directed Bregman
  works, while reflection evenization preserves the symmetric response and erases exactly the
  current.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE] [AFFINE-GAUGE COMPLETE]
  [JOINT RECONSTRUCTION] [EVENIZATION LOSS CLASSIFICATION] [SELECTION INTERFACE]
  [NOVELTY UNVERIFIED] [NOT RH] [LEAN 4 FORMALIZED]

## 1. Setup

Fix a real center (c) and a half-span (a>0).  A centered first-jet packet is four real numbers

\[
 J=(v_-,v_+,m_-,m_+),
 \tag{RFC.1}
\]

thought of as the values and slopes of a differentiable potential at (c-a,c+a).  No function is
needed for the algebraic theorem.

Define the two directed Bregman works

\[
 \begin{aligned}
 B_{-+}(J)&=v_- -v_+ +2a m_+,\\
 B_{+-}(J)&=v_+ -v_- -2a m_-.
 \end{aligned}
 \tag{RFC.2}
\]

Define four centered coordinates

\[
 \begin{aligned}
 E(J)&=\frac{v_-+v_+}{2},
 &S(J)&=\frac{m_+-m_-}{2},\\
 M(J)&=\frac{m_++m_-}{2},
 &H(J)&=aM(J)-\frac{v_+-v_-}{2}.
 \end{aligned}
 \tag{RFC.3}

(E) is the even value, (S) the even/transverse response, (M) the odd/longitudinal response,
and (H) the relative formation current.

The affine gauge group acts by adding \(\alpha t+\beta\) to the potential:

\[
 \begin{aligned}
 v_-&\mapsto v_-+\alpha(c-a)+\beta,&m_-&\mapsto m_-+\alpha,\\
 v_+&\mapsto v_++\alpha(c+a)+\beta,&m_+&\mapsto m_++\alpha.
 \end{aligned}
 \tag{RFC.4}

## 2. Main theorem

### Theorem 2.1 — centered reconstruction and complete affine quotient

For every centered jet (J):

1. **Full jet reconstruction**
   \[
   \boxed{
   \begin{aligned}
   v_+&=E+aM-H,&v_-&=E-aM+H,\\
   m_+&=M+S,&m_-&=M-S.
   \end{aligned}}
   \tag{RFC.5}
   \]

2. **Directed-work reconstruction**
   \[
   \boxed{
   B_{-+}=2aS+2H,
   \qquad
   B_{+-}=2aS-2H.}
   \tag{RFC.6}
   \]
   Consequently
   \[
   \boxed{
   B_{-+}+B_{+-}=4aS,
   \qquad
   B_{-+}-B_{+-}=4H.}
   \tag{RFC.7}
   \]

3. **Affine invariance and completeness.**  (S,H,B_{-+},B_{+-}) are invariant under
   `(RFC.4)`.  Two centered jets are related by a unique affine gauge transformation exactly when
   they have the same pair ((S,H)).  Thus
   \[
      \boxed{\{\text{centered first jets}\}/\operatorname{Aff}_1
      \simeq \mathbb R^2,qquad [J]\mapsto(S(J),H(J)).}
   \tag{RFC.8}
   \]

4. **Positive-work cone.**  Both directed works are nonnegative exactly when
   \[
      \boxed{S\ge0\quad\text{and}\quad |H|\le aS.}
   \tag{RFC.9}
   \]
   Hence the quotient of positive centered jets is the closed Lorentz wedge in the ((aS,H))
   plane.  Its central axis (H=0) is the unoriented/even locus; its two boundary rays are the
   one-direction-zero laws.

### Proof

From `(RFC.3)`,

\[
 \frac{v_+-v_-}{2}=aM-H,
 \qquad
 \frac{v_-+v_+}{2}=E.
\]

Adding and subtracting proves the value formulas in `(RFC.5)`.  The slope formulas follow directly
from the definitions of (M,S).

Substitute `(RFC.5)` into `(RFC.2)`:

\[
 \begin{aligned}
 B_{-+}
 &=(-2aM+2H)+2a(M+S)=2aS+2H,\\
 B_{+-}
 &=(2aM-2H)-2a(M-S)=2aS-2H.
 \end{aligned}
\]

This proves `(RFC.6)` and `(RFC.7)`.

Under `(RFC.4)`, (S) is unchanged and (Mmapsto M+alpha).  The half-difference of the values
changes by (alpha a), so

\[
 H\mapsto a(M+alpha)-\left(\frac{v_+-v_-}{2}+\alpha a\right)=H.
\]

Equations `(RFC.6)` then give invariance of both directed works.

Suppose (J_1,J_2) have the same (S,H).  Put

\[
 \alpha=M(J_2)-M(J_1),
 \qquad
 \beta=E(J_2)-E(J_1)-\alpha c.
\]

The affine transform of (J_1) has (M=M(J_2)), (E=E(J_2)), and unchanged (S,H).  Full
reconstruction `(RFC.5)` makes all four transformed coordinates equal those of (J_2).  The
required \((\alpha,\beta)\) are unique because (M) and (E) determine them.  Conversely, affine
equivalence preserves (S,H).  This proves `(RFC.8)`.

Finally, `(RFC.6)` makes simultaneous nonnegativity equivalent to

\[
 aS+H\ge0,
 \qquad
 aS-H\ge0,
\]

which is exactly (Sge0) and (|H|\le aS), proving `(RFC.9)`. QED.

## 3. Reflection evenization

Define the reflection-evenized jet

\[
 \operatorname{Ev}(J)=(E,E,-S,S).
 \tag{RFC.10}

This is the first jet at (pm a) of the even part of any differentiable potential producing (J).

### Theorem 3.1 — exact completion-loss law

\[
 \boxed{
 S(\operatorname{Ev}J)=S(J),
 \qquad
 H(\operatorname{Ev}J)=0.}
 \tag{RFC.11}

Moreover,

\[
 \boxed{
 B_{-+}(\operatorname{Ev}J)
 =B_{+-}(\operatorname{Ev}J)=2aS(J).}
 \tag{RFC.12}

Therefore evenization preserves the symmetric/Jeffreys work

\[
 B_{-+}+B_{+-}=4aS
 \tag{RFC.13}

but erases exactly the directed current

\[
 \chi(J):=B_{-+}-B_{+-}=4H.
 \tag{RFC.14}

On the affine quotient `(RFC.8)`, evenization is the idempotent projection

\[
 \boxed{(S,H)\longmapsto(S,0).}
 \tag{RFC.15}

Its fixed locus is exactly (H=0), and the lost coordinate is exactly (H).

### Proof

For `(RFC.10)`, the average slope is zero, the half-difference of values is zero, and the slope
half-difference is (S).  Thus `(RFC.11)` holds.  Theorem 2.1 gives `(RFC.12)`--`(RFC.15)`.
Applying evenization twice changes nothing, so the quotient map is idempotent. QED.

## 4. Differentiable-potential form

Let (A) be differentiable at (c-a,c+a), and take

\[
 v_\pm=A(c\pm a),
 \qquad
 m_\pm=A'(c\pm a).
\]

Write the centered odd part

\[
 O_A(c,a)=\frac{A(c+a)-A(c-a)}2.
 \tag{RFC.16}

Then

\[
 \boxed{
 H_A(c,a)=a\,\partial_aO_A(c,a)-O_A(c,a),
 \qquad
 \chi_A(c-a,c+a)=4H_A(c,a).}
 \tag{RFC.17}

Thus (H) is the Euler homogeneity defect of the odd source potential.  It vanishes identically on
an interval of positive (a) exactly when (O_A(c,a)/a) is constant there; equivalently, the odd
part is linear.  This is sharp because Bregman divergence is insensitive to affine functions.

### Proof

The chain rule gives

\[
 \partial_aO_A(c,a)=\frac{A'(c+a)+A'(c-a)}2=M.
\]

The first identity in `(RFC.17)` is the definition of (H); the second is `(RFC.14)`.  For
(a>0), the quotient rule gives

\[
 \partial_a\left(\frac{O_A(c,a)}a\right)
 =\frac{a\partial_aO_A(c,a)-O_A(c,a)}{a^2}
 =\frac{H_A(c,a)}{a^2}.
\]

Hence (H=0) on an interval exactly when (O_A/a) is constant there. QED.

## 5. Joint reconstruction and the selection interface

Theorem 2.1 changes the source/completion question.  A completed even observer does not need the
full source potential.  It needs exactly one additional relative coordinate (H):

\[
 \boxed{
 (\text{even work }S,\ \text{fibre current }H)
 \longleftrightarrow
 (B_{-+},B_{+-}).}
 \tag{RFC.18}

If a source family has strict centered chronology

\[
 a>0\Longrightarrow H_A(c,a)\ne0,
 \tag{RFC.19}

then any comparison which is both

1. reflection-even at the completed level, and
2. sufficient for both directed source works,

forces (a=0).  Indeed, evenization makes the completed chirality zero, sufficiency preserves the
two directed works and therefore their difference, and `(RFC.14)` gives (H_A(c,a)=0), contradicting
`(RFC.19)` unless (a=0).

For the positive-jump exponential formations in the existing corpus, strict chronology is already
paper-proved.  The unresolved arithmetic issue is not the selector theorem but construction of the
pre-zero sufficient relative comparison.

## 6. Fusion across structurally different organs

| Organ | Exact coordinate | Law |
|---|---|---|
| positive/information geometry | (aS) | symmetric directed-work budget |
| formation chronology | (H) | orientation/chirality current |
| reflection completion | ((S,H)\mapsto(S,0)) | positive work retained, orientation erased |
| observer hidden history | vertical (H) | exact fibre obligation under reversible observation |
| affine/source gauge | ((E,M)) | quotiented without changing Bregman packet |

The theorem does not identify these organs as one object.  It proves they are exact coordinates and
shadows of one centered formation experiment.

## 7. Fourth-organ prediction

For every proposed reflected physical completion, the two directed source works must satisfy one
of two mutually exclusive outcomes off neutrality:

1. they remain unequal, so the completion has a visible reflection defect; or
2. they become equal, so an exact hidden fibre current of magnitude (|4H|) has been created.

There is no third option in a sufficient comparison.  A completion claiming exact reflection,
pair sufficiency, and zero hidden current is therefore falsified by any nonzero source (H).

## 8. Hostile boundaries

1. **Evenness does not prove selection.**  It sets the visible current to zero for every (a).
2. **Jeffreys work does not recover chronology.**  It is (4aS) and forgets (H).
3. **Chirality zero does not imply an even potential.**  Affine odd drift is invisible; affine
   quotienting is load-bearing.
4. **Signed current is not positive curvature.**  (H) may have either sign.  The positive cone is
   the wedge `(RFC.9)`.
5. **The finite theorem does not construct an arithmetic comparison.**  It gives the exact data
   that comparison must retain.
6. **Sufficiency is not automatic.**  It requires likelihood-ratio factorization or an equality
   case of data processing before specialization.
7. **No RH conclusion.**  The source-to-completion relative extension and its current law remain
   open.

## 9. External collision audit

Bregman geometry of exponential families, sufficient-statistic invariance, data processing,
recovery, and hidden entropy production are established mathematics.  Relevant primary parents:

- Ay--Jost--Lê--Schwachhöfer, <https://arxiv.org/abs/1207.6736>;
- Chowdhury--Saux--Maillard--Gopalan, <https://arxiv.org/abs/2201.07306>;
- Kawaguchi--Nakayama, <https://arxiv.org/abs/1209.6333>;
- Junge--Renner--Sutter--Wilde--Winter, <https://arxiv.org/abs/1509.07127>.

The algebraic identities are therefore classified `[BRIDGE]`.  The source-specific residue is the
exact coupling to reflection completion and the prediction that all erased chronology is one
relative current (H).

## 10. Gates

- [x] internal corpus and failed-route audit;
- [x] external parent audit;
- [x] complete algebraic reconstruction proof;
- [x] affine quotient classification;
- [x] reflection-evenization loss theorem;
- [x] positive-work cone classification;
- [x] hostile scope audit;
- [x] Lean formalization of the exact finite theorem;
- [ ] literal arithmetic relative-completion realization.

## 11. Log

- 2026-08-11 — direct bounded-conservation premise rejected; representation changed from one
  source work to a relative even-completion packet.
- 2026-08-11 — centered jet quotient, directed-work reconstruction, Lorentz wedge, and exact
  evenization loss proved.
- 2026-08-11 — exact reconstruction, affine quotient, work cone, and evenization theorem accepted
  by Lean in `ConstitutiveRelativeFormationCompletion.lean` and wired into the universal-law
  umbrella.
