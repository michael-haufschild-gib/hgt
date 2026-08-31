# Infinite-orbit defect induction, essentialization, information amplification, and selection law

- **ID:** ULF-OISM-1
- **Stage:** 3 — formalised in Lean 4
- **Type:** UNIVERSAL FORMATION / GLOBAL PROPERNESS / SELECTION THEOREM
- **Parent field:** Orbit-Induction Selection Mechanics
- **Statement:** Inducing one local law defect over an infinite source orbit turns every nonzero
  compact defect into a global essential obstruction of exactly the same norm, replicates every
  local kernel or cokernel with infinite multiplicity, and turns every positive local information
  separation into linearly divergent cofinal work.  Functional-equation permutation and common
  recovery preserve all three effects.  Consequently compact global defect, Fredholm global
  formation, or bounded cofinal information work forces exact local neutrality.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [ROUTE-INDEPENDENT]
  [MECHANISM-FIRST] [INFINITE-ORBIT FORMATION] [ESSENTIAL-NORM EXACT]
  [FREDHOLM CLASSIFICATION] [COMMON-RECOVERY CONSERVATIVE]
  [GLOBAL PROPERNESS] [SELECTION SURVIVOR] [LEAN FORMALIZED 2026-08-30] [NOT RH]

## 1. Why this is a higher mechanism

Many corpus routes reach the same local endpoint:

1. a one-scale error is compact, finite-rank, trace-class, or information-small;
2. every finite aperture is repairable;
3. functional reflection merely permutes equivalent local charts;
4. the cofinal/global theorem still fails.

The missing operation is **orbit induction**.  A source symmetry does not merely move one defect.
It forms one copy at every point of an infinite orbit.  Infinite formation changes the ideal class:
a compact local defect becomes a noncompact global defect, and a finite local ambiguity becomes an
infinite-dimensional global ambiguity.  The same formation sends a positive local information
cost to a linearly divergent global cost.

This is not curvature language.  It is a precise incompatibility between three operations:

\[
 \text{local quotient},\qquad
 \text{source-orbit induction},\qquad
 \text{global recovery/admission}.
\tag{OI.1}
\]

## 2. Unitary orbit induction

Let \(I\) be a countably infinite set, let \(H,K\) be Hilbert spaces, and let

\[
 D:H\longrightarrow K
\tag{OI.2}
\]

be bounded.  For every \(i\in I\), choose unitaries \(U_i:H\to H\) and
\(V_i:K\to K\), and put

\[
 D_i=V_iDU_i^{-1}.
\tag{OI.3}
\]

The orbit-induced operator is the block formation

\[
 \operatorname{Ind}_I(D):\ell^2(I;H)\longrightarrow\ell^2(I;K),
 \qquad
 (x_i)_i\longmapsto(D_ix_i)_i.
\tag{OI.4}
\]

All local blocks are unitarily equivalent, but the global operator is not a local block.

### Theorem 2.1 -- exact operator induction laws

For every bounded \(D\):

1. \(\operatorname{Ind}_I(D)\) is bounded and
   \[
   \boxed{\|\operatorname{Ind}_I(D)\|=\|D\|.}
   \tag{OI.5}
   \]
2. Its kernel is
   \[
   \boxed{
   \ker\operatorname{Ind}_I(D)
   =\bigoplus_{i\in I}^{\ell^2}U_i(\ker D).}
   \tag{OI.6}
   \]
3. Its range is closed exactly when \(\operatorname{ran}D\) is closed.
4. Its reduced minimum modulus is unchanged:
   \[
   \boxed{\gamma(\operatorname{Ind}_I(D))=\gamma(D).}
   \tag{OI.7}
   \]
5. The same statements hold for the adjoint and cokernel.

#### Proof

For \(x=(x_i)\), unitary invariance gives

\[
 \|\operatorname{Ind}_I(D)x\|^2
 =\sum_i\|DU_i^{-1}x_i\|^2
 \le \|D\|^2\sum_i\|x_i\|^2.
\]

Putting a norm-approximating unit vector into one block proves equality in `(OI.5)`.
Equation `(OI.6)` follows blockwise.  On the orthogonal complement of the kernel, every coordinate
lies in a unitary copy of \((\ker D)^\perp\); hence the sharp lower bound in every block is
\(\gamma(D)\), and summing squares proves `(OI.7)`.  A bounded operator between Hilbert spaces has
closed range exactly when its reduced minimum modulus is positive, proving item 3.  Applying the
same argument to \(D^*\) proves the cokernel statement.  QED.

### Corollary 2.2 -- infinite-orbit semi-Fredholm classification

Because \(I\) is infinite:

1. \(\operatorname{Ind}_I(D)\) is upper semi-Fredholm exactly when \(D\) is bounded below;
2. it is lower semi-Fredholm exactly when \(D\) is surjective;
3. it is Fredholm exactly when \(D\) is invertible.

Indeed a nonzero local kernel or cokernel is repeated in every block and therefore has infinite
global dimension.  Closed range is governed by Theorem 2.1.  If \(D\) is invertible, the direct sum
of the conjugated inverses is a bounded inverse of norm \(\|D^{-1}\|\).

This is the first formation selection law: on an infinite homogeneous orbit, Fredholm admission
does not tolerate even one local zero-mode.

## 3. Compact defect becomes essential

### Theorem 3.1 -- exact essentialization

For every bounded \(D\),

\[
 \boxed{
 \operatorname{Ind}_I(D)\text{ is compact}
 \quad\Longleftrightarrow\quad D=0.}
\tag{OI.8}
\]

more sharply,

\[
 \boxed{
 \|\operatorname{Ind}_I(D)\|_{\mathrm{ess}}=\|D\|.}
\tag{OI.9}
\]

Thus every nonzero local finite-rank, trace-class, or Schatten defect becomes a global noncompact
essential obstruction.  In particular, for every finite \(p\), a nonzero compact \(D\) gives

\[
 \operatorname{Ind}_I(D)\notin\mathcal S_p.
\tag{OI.10}
\]

#### Proof

The upper bound in `(OI.9)` is the operator norm identity `(OI.5)`.  Fix a unit vector \(x\in H\).
For distinct \(i\), let \(\xi_i\) be the vector supported in the \(i\)-th block with value
\(U_ix\).  The sequence \((\xi_i)\) is orthonormal and hence weakly null.  For every compact
operator \(C:\ell^2(I;H)\to\ell^2(I;K)\), compactness gives \(C\xi_i\to0\), whereas

\[
 \|\operatorname{Ind}_I(D)\xi_i\|=\|Dx\|.
\]

Therefore

\[
 \|\operatorname{Ind}_I(D)-C\|\ge\|Dx\|.
\]

Taking the supremum over unit \(x\) and then the infimum over compact \(C\) proves `(OI.9)`.
Equation `(OI.8)` follows.  Every Schatten operator is compact, so `(OI.10)` follows as well. QED.

### Corollary 3.2 -- quotient and formation do not commute

Let \(q_{\mathrm{loc}}\) and \(q_{\mathrm{glob}}\) be the local and global Calkin quotient maps.
For compact \(D\), every local class vanishes:

\[
 q_{\mathrm{loc}}(D_i)=0\qquad(i\in I),
\]

but if \(D\ne0\),

\[
 \boxed{
 q_{\mathrm{glob}}(\operatorname{Ind}_I(D))\ne0,
 \qquad
 \|q_{\mathrm{glob}}(\operatorname{Ind}_I(D))\|=\|D\|.}
\tag{OI.11}
\]

Hence “take the local quotient, then form the orbit” loses exactly the obstruction retained by
“form the orbit, then take the global quotient.”  The comparison defect has no small remainder:
its norm is the full local norm.

## 4. Rank and multiplicity amplification

### Corollary 4.1 -- finite local complexity becomes infinite global complexity

If \(D\ne0\), then \(\operatorname{Ind}_I(D)\) has infinite-dimensional range.  If \(D\) has
finite positive rank \(r\), every finite subformation over \(F\subset I\) has rank

\[
 \boxed{\operatorname{rank}\operatorname{Ind}_F(D)=|F|r,}
\tag{OI.12}
\]

and the cofinal rank diverges.

This does **not** identify hypertranscendence with rank.  It proves the exact fourth-organ
prediction that an infinite source orbit converts one nonzero finite response direction into
unbounded formation rank.  Any route claiming a uniformly finite global response model must
either kill the local response or break orbit homogeneity.

### Theorem 4.2 -- positive Gram is a phase quotient, not an essentiality quotient

Let \(\mathcal D=\operatorname{Ind}_I(D)\).  Then

\[
 \boxed{
 \mathcal D^*\mathcal D
 =\bigoplus_{i\in I}U_i(D^*D)U_i^{-1}.}
 \tag{OI.G1}
\]

In particular, all output unitaries \(V_i\) disappear from the positive Gram operator, while

\[
 \ker(\mathcal D^*\mathcal D)=\ker\mathcal D,
 \qquad
 \gamma(\mathcal D^*\mathcal D)=\gamma(D)^2.
 \tag{OI.G2}
\]

If \(D\ne0\) is compact, the positive Gram is still noncompact and

\[
 \boxed{
 \|\mathcal D^*\mathcal D\|_{\mathrm{ess}}=\|D\|^2.}
 \tag{OI.G3}
\]

#### Proof

Taking block adjoints gives

\[
 D_i^*D_i=U_iD^*V_i^{-1}V_iDU_i^{-1}=U_i(D^*D)U_i^{-1},
\]

which proves `(OI.G1)`.  The kernel identity is the standard equality
\(\ker D^*D=\ker D\); the reduced spectral gap is squared.  Apply Theorem 3.1 to the nonzero
compact operator \(D^*D\), whose norm is \(\|D\|^2\), to obtain `(OI.G3)`. QED.

This is the exact meaning of “positivity is a phase quotient” in the present mechanism.  Gram
formation forgets output phase/polarization \(V_i\), but it does not forget multiplicity,
zero-modes, closed-range failure, or global essentiality.

## 5. Information induction and common recovery

Let \(P,Q\) be probability measures on a standard Borel space \(X\).  Let \(M:X\leadsto Y\) be one
Markov kernel used identically for both laws, and write

\[
 E_M(P)=P\otimes M,
 \qquad E_M(Q)=Q\otimes M.
\tag{OI.13}
\]

For a nonempty finite \(F\subset I\), form independent orbit packets

\[
 P_F=P^{\otimes F},\qquad Q_F=Q^{\otimes F},
\tag{OI.14}
\]

and their common-recovery lifts

\[
 \widetilde P_F=E_M(P)^{\otimes F},
 \qquad
 \widetilde Q_F=E_M(Q)^{\otimes F}.
\tag{OI.15}
\]

### Theorem 5.1 -- exact information amplification

With extended values allowed,

\[
 \boxed{
 D_{\mathrm{KL}}(P_F\Vert Q_F)
 =|F|D_{\mathrm{KL}}(P\Vert Q),}
\tag{OI.16}
\]

and common recovery is exactly neutral:

\[
 \boxed{
 D_{\mathrm{KL}}(\widetilde P_F\Vert\widetilde Q_F)
 =D_{\mathrm{KL}}(P_F\Vert Q_F).}
\tag{OI.17}
\]

Consequently Jeffreys work satisfies

\[
 \boxed{
 J(\widetilde P_F,\widetilde Q_F)
 =|F|J(P,Q).}
\tag{OI.18}
\]

#### Proof

Relative entropy is additive on finite products, proving `(OI.16)`.  The split chain rule for a
common conditional kernel gives

\[
 D_{\mathrm{KL}}(P\otimes M\Vert Q\otimes M)
 =D_{\mathrm{KL}}(P\Vert Q)
 +\int D_{\mathrm{KL}}(M_x\Vert M_x)\,dP(x)
 =D_{\mathrm{KL}}(P\Vert Q).
\]

Apply finite-product additivity once more to obtain `(OI.17)`.  Applying both directions and adding
proves `(OI.18)`. QED.

### Corollary 5.2 -- cofinal information properness

For any exhaustion \(F_1\subset F_2\subset\cdots\subset I\) with \(|F_n|\to\infty\),

\[
 \boxed{
 \sup_nJ(\widetilde P_{F_n},\widetilde Q_{F_n})<\infty
 \quad\Longleftrightarrow\quad P=Q.}
\tag{OI.19}
\]

If the local Jeffreys work is positive and finite, the global work grows exactly linearly in
\(|F_n|\).  If it is infinite, global work is already infinite at one block.  If it vanishes,
both directed relative entropies vanish and \(P=Q\).

Thus information-neutral common recovery is not defect-neutral.  It transports every local bit of
distinguishability isometrically, and orbit formation amplifies that bit into a global properness
law.

## 6. Functional-equation lift is information-neutral

Let \(\sigma:I\to I\) be an involutive permutation and let \(J_H,J_K\) be unitary involutions.
Assume the local blocks obey the reciprocal law

\[
 J_KD_{\sigma(i)}=D_iJ_H.
\tag{OI.20}
\]

Define

\[
 (W_Hx)_i=J_Hx_{\sigma(i)},
 \qquad
 (W_Ky)_i=J_Ky_{\sigma(i)}.
\tag{OI.21}
\]

### Theorem 6.1 -- induced functional equation

The maps \(W_H,W_K\) are unitary involutions and

\[
 \boxed{
 W_K\operatorname{Ind}_I(D)
 =\operatorname{Ind}_I(D)W_H.}
\tag{OI.22}
\]

Hence functional reflection preserves operator norm, essential norm, reduced minimum modulus,
kernel/cokernel multiplicity, and every conclusion of Sections 2--4.  If packet reflection acts by
a measurable bijection and the common recovery kernel is equivariant, it also preserves every
relative entropy in Section 5.

#### Proof

Unitarity and involutivity follow from permutation of orthogonal coordinates and the involution
laws for \(J_H,J_K\).  In coordinate \(i\), the left side of `(OI.22)` is

\[
 J_KD_{\sigma(i)}x_{\sigma(i)},
\]

while the right side is \(D_iJ_Hx_{\sigma(i)}\); these are equal by `(OI.20)`.  All listed
operator invariants are unitary invariants.  Relative entropy is invariant under measurable
bijections, and the common-kernel lift is an isometry by Theorem 5.1. QED.

Functional equation is therefore a **neutral symmetry of the induced obstruction**.  It neither
creates nor cancels the selection work.

## 7. Global formation-selection theorem

### Theorem 7.1 -- three independent global admissions force local neutrality

Let a local law parameter \(\theta\) determine a compact operator defect \(D_\theta\), a bounded
formation block \(T_\theta\), and an observer pair \((P_\theta,Q_\theta)\).  Suppose the neutral
locus is characterized by

\[
 D_\theta=0
 \quad\Longleftrightarrow\quad
 P_\theta=Q_\theta
 \quad\Longleftrightarrow\quad
 T_\theta\text{ is invertible}.
\tag{OI.23}
\]

Induce the defect and packet pair over one countably infinite homogeneous source orbit.  Each of
the following global admission laws forces \(\theta\) to be neutral:

1. the induced operator defect is compact (hence also if it is Schatten or trace-class);
2. \(\operatorname{Ind}_I(T_\theta)\) is Fredholm;
3. the cofinal common-recovery Jeffreys work is bounded.

#### Proof

Item 1 and Theorem 3.1 give \(D_\theta=0\).  Item 2 and Corollary 2.2 give invertibility of
\(T_\theta\).  Item 3 and Corollary 5.2 give \(P_\theta=Q_\theta\).  The equivalence
`(OI.23)` identifies the same neutral locus. QED.

The theorem is unconditional.  An RH application still requires one source-specific handoff:
construct \(D_\theta,P_\theta,Q_\theta\) before zero specialization, prove `(OI.23)`, and prove one
of the three global admission statements from the literal source.  The universal mechanism then
performs the selection; no route-specific positivity trick remains.

## 8. Fusion across five structural organs

The theorem does not summarize proof routes.  It identifies one operation with exact outputs in
four nonisomorphic mathematical organs:

| organ | local datum | orbit-induced law |
|---|---|---|
| operator quotient/topology | compact \(D\) | essential norm \(\|D\|\), not compact |
| Fredholm/admission | finite local kernel/cokernel | infinite multiplicity; Fredholm iff invertible |
| information geometry | local Jeffreys work \(j\) | exact cofinal work \(|F|j\) |
| response/prolongation rank | finite positive rank \(r\) | exact rank \(|F|r\) and unbounded cofinal rank |
| positive Gram/polar quotient | \(D^*D\) | phases vanish, but essential norm is \(\|D\|^2\) |

The common conservation identity is **multiplicity**.  Orbit induction preserves local size while
repeating local incidence:

\[
 \|\operatorname{Ind}D\|_{\mathrm{ess}}=\|D\|,
 \qquad
 J_F=|F|J_1,
 \qquad
 \operatorname{rank}D_F=|F|\operatorname{rank}D.
\tag{OI.24}
\]

Norm records amplitude; information and rank record multiplicity.  A scalar determinant or one
finite quotient cannot reconstruct both.

## 9. Fourth-organ prediction and falsifier

### Prediction 9.1 -- compact shell residuals cannot remain globally negligible

Suppose a source supplies infinitely many orthogonal shell blocks and a nonzero one-shell compact
residual \(K\), with all shell residuals unitarily transported copies of \(K\).  Then the assembled
all-shell residual has

\[
 \boxed{\|K_{\mathrm{all}}\|_{\mathrm{ess}}=\|K\|>0.}
\tag{OI.25}
\]

Therefore pointwise Calkin equality on every shell cannot imply global Calkin equality.  A claimed
all-scale compact repair is false unless at least one of the following occurs:

1. the local residual is exactly zero;
2. shell amplitudes decay to zero, breaking homogeneous induction;
3. off-diagonal shell interactions create a genuinely non-block cancellation;
4. the source does not admit the infinite orbit formation.

This is directly testable on the corpus all-scale Sonin residuals.  Existing one-aperture
compact/Hilbert--Schmidt theorems establish the local premise, not the unitary-homogeneous assembly.
The next literal theorem must measure shell transport amplitudes or prove off-diagonal cancellation.
Repeating another local compactness proof cannot help.

### Theorem 9.2 -- literal reciprocal time--band calibration

Let (P_a) be physical cutoff to ([-a,a]), let
(Q_b=mathcal F^{-1}P_bmathcal F) be Fourier cutoff, and let (D_r) be normalized dilation,
where (a,b>0) and (r>0).  Put

\[
 C_{a,b}=Q_bP_a.
 \tag{OI.26}
\]

Then:

1. (C_{a,b}) is compact and nonzero;
2. dilation acts by reciprocal transport,
   \[
   \boxed{
   D_rC_{a,b}D_r^{-1}=C_{a/r,,rb};}
   \tag{OI.27}
   \]
3. the product (kappa=ab) is invariant, while
   (u=\tfrac12\log(b/a)) transforms by (u\mapsto u+\log r);
4. Fourier exchange sends ((a,b)) to ((b,a)), hence (u\mapsto-u), and conjugates
   (C_{a,b}) to the adjoint of (C_{b,a});
5. for (r>1), the all-rapidity formation
   \[
   \mathcal C_{a,b,r}
   =\bigoplus_{n\in\mathbb Z}C_{a/r^n,,r^nb}
   \tag{OI.28}
   \]
   satisfies
   \[
   \boxed{
   \|\mathcal C_{a,b,r}\|_{\mathrm{ess}}=\|C_{a,b}\|>0.}
   \tag{OI.29}
   \]

#### Proof

The time--band product (Q_bP_a) is compact because restriction to finite physical and frequency
intervals is Hilbert--Schmidt.  It is nonzero: take the nonzero indicator of ([-a,a]).  Its
Fourier transform is continuous and has value (2a) at frequency zero, so its restriction to the
nonempty interval ([-b,b]) is nonzero.

The exact cutoff covariance laws are

\[
 P_aD_r=D_rP_{ra},
 \qquad
 Q_bD_r=D_rQ_{b/r}.
\]

Multiplying them gives

\[
 C_{a,b}D_r=D_rC_{ra,b/r},
\]

which is equivalent to `(OI.27)`.  The formulas for (kappa) and (u) are direct.  Fourier
conjugates physical and frequency cutoffs; reversal of product order gives the adjoint statement.
Iterating `(OI.27)` makes every block in `(OI.28)` a unitary conjugate of (C_{a,b}), so Theorem
3.1 gives `(OI.29)`. QED.

This is a literal calibration, not the RH selector.  In fact it supplies a hostile boundary:
the time--band residual is nonzero even at the self-dual point (a=b).  Therefore global compact
admission of this particular residual is impossible at every rapidity.  A successful arithmetic
application needs a different local defect that vanishes at neutrality; functional symmetry and
reciprocal carrier geometry alone do not manufacture that zero locus.

## 10. Sharp counterexamples and scope

1. **Finite orbit.** If \(I\) is finite, a finite sum of compact blocks is compact and finite
   kernel multiplicities remain finite.  Infinite orbit is load-bearing.
2. **Decaying amplitudes.** For blocks \(a_iV_iDU_i^{-1}\) with \(a_i\to0\), the direct sum is
   compact when \(D\) is compact.  Homogeneous amplitude is load-bearing.
3. **Correlated packets.** Product additivity `(OI.16)` uses independent formation.  Arbitrary
   correlations can change total KL.  The operator theorems do not need independence.
4. **Quotient first.** Killing every local compact class before induction erases the global
   essential class by construction.  Corollary 3.2 proves that procedure is not conservative.
5. **Functional equation.** Reflection only permutes/conjugates blocks.  It does not supply compact
   global admission and cannot select neutrality alone.
6. **Local smallness.** Replacing \(D\) by \(\varepsilon D\) changes the global essential norm to
   \(\varepsilon\|D\|\), but it remains nonzero for every \(\varepsilon>0\).  Approximate local
   neutrality is not exact global compactness.
7. **RH scope.** The theorem contains no zero, Xi value, prime estimate, or RH-equivalent premise.
   It supplies the universal selection engine, not the source-specific admission handoff.

## 11. Mechanism laws

Orbit-Induction Selection Mechanics is governed here by six laws:

1. **formation:** source symmetry forms one transported copy per orbit point;
2. **amplitude conservation:** unitary transport preserves local norm and reduced gap;
3. **multiplicity growth:** kernel, cokernel, rank, and information add over independent blocks;
4. **ideal transmutation:** nonzero compact local data become essential global data;
5. **duality neutrality:** functional equation permutes blocks without changing induced invariants;
6. **global selection:** compactness, Fredholmness, or bounded cofinal work forces local neutrality.

These are laws of a mechanism, not a proposed universal object.

## 12. No-go closure

- **Killed mechanism:** local compactness, finite-rank repair, or information-neutral recovery cannot
  justify a global all-scale quotient.
- **Strongest positive survivor:** infinite homogeneous orbit induction is an exact zero detector:
  global compactness/Schatten admission, Fredholm admission, or bounded cofinal information work
  forces the local defect to vanish.
- **New field consequence:** local quotient and orbit formation are noncommuting operations, with
  exact comparison norm `(OI.11)`.
- **Open source gate:** construct one literal pre-zero orbit whose local defect vanishes exactly at
  neutrality and prove homogeneous or quantitatively controlled induction.
- **Lean status:** paper proof dependency-closed; formalization intentionally deferred in the active
  read-only Lean phase.

## Log

- 2026-08-12 -- extracted after pointwise Calkin coverage was shown insufficient for global
  formation properness.
- 2026-08-12 -- fused operator essentiality, Fredholm multiplicity, packet information, and
  cofinal response rank into one orbit-induction law.
