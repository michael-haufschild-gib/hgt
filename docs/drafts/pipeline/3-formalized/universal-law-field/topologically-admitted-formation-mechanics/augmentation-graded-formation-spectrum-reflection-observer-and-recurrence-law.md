# Augmentation-graded formation spectrum, reflection, observer, and recurrence law

- **ID:** ULF-TAFM-24
- **Stage:** 3-formalized
- **Type:** universal mechanism / filtered formation law / cross-organ prediction
- **Parents:** ULF-TAFM-14, ULF-TAFM-19, ULF-TAFM-23
- **Status:** Formalized in Lean 4

## 1. Mechanism, not another route object

Observer jets from ULF-TAFM-23 are coordinates, not the underlying object.  The underlying object is
the augmentation-filtered algebra of finite formation histories.  In its rank-one universal chart,

\[
  \mathcal A_R=R[\mathbb Z]=R[T,T^{-1}],
  \qquad
  \varepsilon\!\left(\sum_k q_kT^k\right)=\sum_kq_k,
  \qquad
  I=\ker\varepsilon=(T-1).                              \tag{AF.1}
\]

Its powers

\[
  \mathcal A_R\supset I\supset I^2\supset\cdots          \tag{AF.2}
\]

are formation-memory orders.  A closed observer sees the augmentation quotient
`A_R/I`; an open lifted history occupies higher powers.  The associated grades

\[
  \operatorname{gr}_I^r\mathcal A_R=I^r/I^{r+1}          \tag{AF.3}
\]

are coordinate-free even though the generator `T-1` supplies a chart.

This one filtered object carries four previously separate organs:

1. recovery is multiplication by `(T-1)^r`;
2. observer clocks are dual and see `r`-th finite differences;
3. functional-equation reflection is the Hopf antipode `T mapsto T^{-1}`;
4. compact recurrence is the quotient relation `T^p=1`, whose open lift retains winding.

The theorem below does not claim an RH proof.  It proves one common law, produces a theorem in the
recurrence organ from the reflection/recovery/clock fusion, and gives a falsifiable typing rule for
literal route comparisons.

Throughout the paper proof, let `R` be a characteristic-zero commutative integral domain.  The
Lean certificate uses the closed universal integral model `R=Z`; scalar extension gives the real
and complex observer charts.

## 2. Formation boundary and observer pairing

For `r >= 0`, define the order-`r` recovery map

\[
  B_r(P)=(T-1)^rP.                                      \tag{AF.4}
\]

Because `A_R` is a domain, every `B_r` is injective.  Thus higher formation does not itself erase
history.

For a bilateral observer clock `lambda:Z -> R`, define

\[
  \langle \sum_kq_kT^k,\lambda\rangle
     =\sum_kq_k\lambda_k,
  \qquad
  \Delta\lambda_k=\lambda_{k+1}-\lambda_k.             \tag{AF.5}
\]

### Theorem 2.1 -- all-order source--observer Green law

For every finite history `P`, observer clock `lambda`, and `r >= 0`,

\[
  \boxed{\langle B_r(P),\lambda\rangle
       =\langle P,\Delta^r\lambda\rangle.}              \tag{AF.6}
\]

Consequently the annihilator of `I^r` in the algebraic clock dual is exactly

\[
  \operatorname{Ann}(I^r)=\ker\Delta^r.                \tag{AF.7}
\]

Over characteristic zero, these are precisely polynomial clocks of degree below `r`.  Hence an
order-`r` formed source sees an observer only modulo lower-degree gauges.

#### Proof

The binomial identity gives

\[
 (T-1)^rT^j=\sum_{i=0}^r(-1)^{r-i}{r\choose i}T^{j+i}.
\]

Pairing this with `lambda` gives `Delta^r lambda_j`.  Extend linearly over the finite support of
`P`; this proves `(AF.6)`.  If `Delta^r lambda=0`, `(AF.6)` annihilates every element of `I^r`.
Conversely, apply an annihilator of `I^r` to every `B_r(T^j)` to obtain
`Delta^r lambda_j=0` for all `j`.  The standard finite-difference classification in
characteristic zero gives the final statement. QED.

### Corollary 2.2 -- observer order is intrinsic

If `Delta^r lambda` is bounded but `Delta^(r-1) lambda` is unbounded, then `r` is the least
formation order on which the clock acts boundedly under the coefficient `l1` action transported
through `B_r`.  ULF-TAFM-23 is the anchored `r=2` chart of this law.

#### Proof

In history coordinates, `(AF.6)` identifies the response with the `l1`--`linfinity` pairing
against `Delta^r lambda`.  Unit histories `T^j` prove necessity and the triangle inequality proves
sufficiency.  Minimality follows from the assumed failure at order `r-1`. QED.

## 3. Functional-equation action and lossless lift

Let the reflection antipode be

\[
  \iota(T^k)=T^{-k}.                                    \tag{AF.8}
\]

Define its order-`r` history lift by

\[
  H_r(P)=T^{-r}\iota(P).                                \tag{AF.9}
\]

### Theorem 3.1 -- exact reflected-recovery intertwining

For all `P` and `r`,

\[
  \boxed{\iota(B_r(P))=(-1)^rB_r(H_r(P)).}              \tag{AF.10}
\]

Moreover,

\[
  H_r^2=\operatorname{id},                              \tag{AF.11}
\]

and `B_r` is injective.  Therefore functional-equation action lifted through the common recovery
kernel is information-neutral: it is an involutive conjugate action on complete history, with only
the intrinsic grade parity exposed at the recovered level.

#### Proof

Since

\[
 T^{-1}-1=-T^{-1}(T-1),
\]

we obtain

\[
 \iota((T-1)^rP)
 =(-1)^rT^{-r}(T-1)^r\iota(P)
 =(-1)^rB_r(T^{-r}\iota(P)).
\]

Also

\[
 H_r(H_r(P))
 =T^{-r}\iota(T^{-r}\iota(P))
 =T^{-r}T^rP=P.
\]

Injectivity was proved after `(AF.4)`. QED.

### Theorem 3.2 -- associated-grade parity law

Reflection preserves every augmentation power and acts on its associated grade by

\[
  \boxed{\operatorname{gr}_I^r(\iota)=(-1)^r.}          \tag{AF.12}
\]

Equivalently,

\[
  \iota(B_r(P))-(-1)^rB_r(P)\in I^{r+1}.               \tag{AF.13}
\]

#### Proof

Equation `(AF.10)` reduces the difference to

\[
 (-1)^r(T-1)^r(H_r(P)-P).
\]

The augmentation of `H_r(P)` equals that of `P`, since both multiplication by `T^{-r}` and
inversion evaluate to one under `epsilon`.  Thus `H_r(P)-P` belongs to `I`; multiplying by
`I^r` proves `(AF.13)`. QED.

This is not the corpus's existing degree-one parity suspension.  It classifies functional-equation
action simultaneously on every source-memory order and ties that action to the observer derivative
of exactly the same order through `(AF.6)`.

## 4. Closed recurrence has open winding residue

For a positive period `p`, let

\[
  W_p=1+T+\cdots+T^{p-1}.                               \tag{AF.14}
\]

The closed recurrence relation is `T^p=1`; its lifted closure defect is `C_p=T^p-1`.

### Theorem 4.1 -- recurrence factorisation and first-grade winding

For every `p >= 0`,

\[
  C_p=(T-1)W_p,\qquad \varepsilon(W_p)=p.              \tag{AF.15}
\]

More sharply, with

\[
  K_p=\sum_{j=0}^{p-1}\sum_{i=0}^{j-1}T^i,
\]

one has the exact decomposition

\[
  \boxed{T^p-1=p(T-1)+(T-1)^2K_p.}                    \tag{AF.16}
\]

Therefore

\[
  [T^p-1]=p[T-1]\quad\text{in }I/I^2.                 \tag{AF.17}
\]

A closed observer may impose `T^p=1`, but its open lift retains the integer winding `p` as first
formation residue.  In characteristic zero this residue cannot disappear.

#### Proof

The first identity is the geometric-sum factorisation, and augmentation of `p` monomials is `p`.
For each `j`,

\[
 T^j-1=(T-1)\sum_{i=0}^{j-1}T^i.
\]

Hence

\[
 W_p-p=\sum_{j=0}^{p-1}(T^j-1)=(T-1)K_p.
\]

Substitute `W_p=p+(T-1)K_p` into `C_p=(T-1)W_p` to obtain `(AF.16)` and `(AF.17)`. QED.

### Corollary 4.2 -- reflection predicts winding reversal

Reflection sends the first recurrence grade to its negative:

\[
 [\iota(T^p-1)]=-p[T-1]\quad\text{in }I/I^2.          \tag{AF.18}
\]

#### Proof

Apply the grade-one case of `(AF.12)` to `(AF.17)`. QED.

This theorem is a prediction in a fourth organ.  It was not assumed from compact-recurrence or
lattice-carry models; it follows from the same filtered algebra that produced recovery, observer
finite differences, and functional-equation parity.

## 5. Positive observers and adjacent-grade orientation

Let `V_r=gr_I^r A_R`.  Reflection is `(-1)^r` on `V_r`.  Therefore every diagonal quadratic
energy `Q_r(v)=B_r(v,v)` is reflection invariant: even grades are fixed already, while odd-grade
sign is squared away.  In contrast, an adjacent-grade polarized term satisfies

\[
 B_{r,r+1}(\iota v,\iota w)
 =(-1)^r(-1)^{r+1}B_{r,r+1}(v,w)
 =-B_{r,r+1}(v,w).                                    \tag{AF.19}
\]

Thus positivity is a phase quotient in a precise graded sense.  A diagonal positive receiver can
measure magnitude but cannot orient reflection.  The least graded positive architecture capable of
retaining orientation must preserve a polarized cross term between opposite-parity grades, or an
equivalent odd connecting operator.  This predicts why corpus constructions that diagonalize,
take absolute values, square, or pass to ordinary Gram energy repeatedly stop at RH-equivalent
receivers.

## 6. Joint reconstruction law

The common object admits three exact, mutually determining readings:

\[
\begin{array}{c|c|c}
\text{source history} & \text{observer clock} & \text{symmetry/closure}\\ \hline
B_r(P)\in I^r & \Delta^r\lambda & (-1)^r\text{ under reflection}\\
T^p-1 & p[T-1]\in I/I^2 & T^p=1\text{ after closed projection}.
\end{array}                                             \tag{AF.20}
\]

Recovery is injective, observer response is exactly conserved, reflection lift is involutive, and
closed recurrence has exact open residue.  No organ supplies an additional independent coordinate
at this algebraic level.

## 7. Hostile collision audit

### 7.1 Existing results this does not rename

The corpus already proves:

- many information-neutral functional-equation lifts through common kernels;
- a faithful degree-one parity suspension and literal Xi conormal oddness;
- isolated augmentation ideals, `I/I^2` co-Lie objects, and point derivations;
- compact recurrence with hidden winding/carry;
- local phase quotients and positive-energy blindness;
- first- and second-order summation-by-parts laws.

Those are local shadows of `(AF.20)`.  None found in the corpus supplies the full tower `I^r`, the
all-order duality with `Delta^r`, the antipode action on every associated grade, and the exact
recurrence residue in one object.  If such a module is later found, this card must be merged rather
than counted twice.

### 7.2 Falsifiers

This mechanism is not the universal field core if any literal comparison violates:

1. formation order maps to augmentation order functorially;
2. its observer response maps to the corresponding finite-difference clock;
3. functional-equation reflection acts by grade parity after transport;
4. compact return retains the predicted first-grade winding residue;
5. orientation-sensitive positive constructions fail to contain any opposite-parity cross term or
   odd connecting map.

It also fails as an RH architecture if the literal completed source cannot be placed in a completed
augmentation/Rees object without erasing prime labels or if its source action estimate is merely
another RH-equivalent receiver premise.

## 8. Hypertranscendence correction: differential Rees frontier

Bare infinite augmentation depth does **not** characterize hypertranscendence.  Differentially
algebraic functions such as an exponential can occupy infinitely many augmentation grades.  The
correct next object is therefore not only the `I`-adic filtration but its differential Rees
geometry.

In the completed rank-one chart `R[[u]]`, `u=T-1`, the formation-number operator

\[
  \mathcal N=u\frac d{du}                               \tag{AF.21}
\]

acts on grade `r` by eigenvalue `r`.  Finite `N`-spectrum implies a polynomial in `u`, hence a
differentially algebraic germ.  Hypertranscendence therefore forces unbounded formation spectrum,
but the converse is false.  What must encode hypertranscendence is absence of finite differential-
algebraic closure among the infinitely many graded source coefficients, not their mere existence.

This differential-Rees comparison is a Stage-1 research frontier, not part of the theorem proved
in this card.  It is the required refinement if hypertranscendence is to become a genuine source of
noncompactness rather than a slogan.

## 9. RH selection architecture exposed by the law

ULF-TAFM-23 proves that the literal harmonic-to-square-root clock has minimal formation order two.
The present law explains that statement invariantly: the completed charge must land in the
weighted completion of `I^2`, and the Riesz observer is its `Delta^2` dual.

The remaining producer is not a new receiver.  It is the source theorem that the literal completed
arithmetic history has bounded weighted order-two action.  In the coordinates of ULF-TAFM-23 this
is the signed estimate

\[
 |m_1^{(M)}|+
 \sum_{j\le M-4}\frac{|A_j^{(M)}|}{\sqrt{j+1}}=O(M).    \tag{AF.22}
\]

The field-level improvement is that `(AF.22)` is no longer an isolated summation trick.  It is one
chart of a source landing statement in a filtered formation algebra, constrained simultaneously by
functional-equation parity and recurrence residue.  A valid final architecture must derive that
landing/action law from prime-source formation and then invoke the existing closed Riesz/RH
selection equivalence.

## 10. External boundary

Ingredients are classical: group algebras, augmentation ideals, associated graded/Rees algebras,
Hopf antipodes, finite-difference calculus, and polarized quadratic forms.  Novelty is deliberately
not a gate.  The research claim is the joint interpretation and its falsifiable cross-organ typing,
not invention of these ingredients separately.

Related external boundaries include augmentation-ideal filtrations of group rings, Hopf-algebra
antipodes, Rees constructions, and distributional multipoles.  None supplies the literal HGT/RH
source comparison or estimate `(AF.22)`.

## Lean certificate

Formalized exactly in:

- `GaloisForLFunctions.HTGeometry.AugmentationGradedFormationSpectrum`: injective all-order
  recovery, source--observer Green law, involutive reflected lift, associated-grade parity,
  recurrence factorization and first-grade residue, and adjacent-grade orientation;
- `GaloisForLFunctions.HTGeometry.AugmentationGradedFormationSpectrumCompletion`: exact equality
  of the boundary annihilator with the iterated-difference kernel, genuine complex-polynomial
  classification of every integer-valued clock in that kernel with degree `< r`, exact
  coefficient-`ℓ¹` bounded-response equivalence, least bounded observer order, reflected winding
  reversal modulo `I²`, and a zero-argument completion certificate.

Direct foreground elaboration and targeted leaf build pass. Completion module is wired into
`HTGeometry` without an umbrella build. Batched axiom audit of every new public theorem uses only
`propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] common filtered formation object defined
- [x] exact all-order recovery/observer conservation
- [x] exact information-neutral functional-equation lift
- [x] associated-grade parity law
- [x] theorem predicted and proved in compact-recurrence organ
- [x] positivity/orientation typing prediction
- [x] collision and falsifier audit
- [ ] differential Rees comparison for literal hypertranscendental organs
- [ ] literal prime-labelled source functor into completed formation spectrum
- [ ] unconditional source action estimate `(AF.22)`
- [ ] RH selection consequence
- [x] Lean certification

## Log

- 2026-08-31 -- created after ULF-TAFM-23 exposed observer jets as coordinates.  Whole-corpus
  collision audit separated existing degree-one augmentation/parity and information-neutral lifts
  from the missing all-order filtered mechanism.  Proved recovery--clock duality, lossless
  reflection lift, associated-grade parity, and recurrence winding residue.  Rejected bare infinite
  augmentation depth as a characterization of hypertranscendence and opened differential Rees
  refinement.
- 2026-08-31 -- Lean-certified the integral universal chart: injective recovery, all-order
  observer duality, involutive reflection lift, associated-grade parity, exact recurrence residue,
  and adjacent-grade orientation law.  Direct check, targeted module build, and axiom audit pass.
- 2026-09-01 -- exactness audit closed previously omitted annihilator, polynomial-clock,
  coefficient-`ℓ¹` minimal-order, and reflected winding theorems in
  `AugmentationGradedFormationSpectrumCompletion`; direct check, leaf build, umbrella wiring, and
  new-declaration axiom audit pass.
