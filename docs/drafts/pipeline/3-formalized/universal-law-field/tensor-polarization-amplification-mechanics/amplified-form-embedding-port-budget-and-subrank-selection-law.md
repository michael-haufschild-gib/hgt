# Amplified form embedding, port budget, and subrank selection law

- **ID:** ULF-TPAM-2
- **Stage:** 3-formalized
- **Type:** UNIVERSAL LAW-FIELD THEOREM / AMPLIFIED REALIZATION SELECTION
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [ROUTE-INDEPENDENT]`
  `[FORMATION + POLARIZATION + REALIZATION + PORT BUDGET]`
  `[LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS] [CONDITIONAL RH INTERFACE] [NOT RH]`
- **Statement:** A form-preserving realization cannot reduce negative index.  Repeated tensor
  formation of one genuinely mixed packet has at least the previous total tensor rank in negative
  directions.  Consequently one realized formation depth whose target port budget is smaller than
  that rank forces the original packet to be positive.

## 1. Mechanism

The previous tensor-polarization theorem required one uniform negative-index budget at every
formation depth.  That is stronger than selection needs and makes the arithmetic interface look
artificially rigid.

The correct mechanism is comparative:

\[
 \boxed{
 \text{tensor formation growth}
 \;\xrightarrow{\text{form-preserving realization}}\;
 \text{geometric port budget}.}
 \tag{APR.1}
\]

The two sides are not identified.  Tensor product is the source formation.  A Stokes, Hodge,
Krein, trace, or boundary carrier is a separate target.  The only legal bridge is an injective map
preserving the Hermitian form.  Inertia monotonicity then compares them.

This prevents the invalid shortcut of calling additive Stokes fusion a tensor product.

## 2. Inertia cannot decrease under realization

Let \(H\) be a Hermitian form on a finite-dimensional complex vector space \(V\), let \(Q\) be a
Hermitian form on \(W\), and let

\[
 \iota:V\longrightarrow W
 \tag{APR.2}
\]

be injective with

\[
 Q(\iota x,\iota y)=H(x,y)
 \qquad(x,y\in V).
 \tag{APR.3}
\]

### Theorem 2.1 -- form-embedding inertia monotonicity

\[
 \boxed{\operatorname{ind}_{-}(H)\leq \operatorname{ind}_{-}(Q).}
 \tag{APR.4}
\]

### Proof

Choose a negative-definite subspace \(N\subseteq V\) of dimension
\(\operatorname{ind}_{-}(H)\).  Injectivity gives
\(\dim\iota(N)=\dim N\).  Equation `(APR.3)` makes \(Q\) negative definite on \(\iota(N)\).
The maximal dimension of a negative-definite subspace of \(W\) is therefore at least
\(\dim N\).  QED.

The same proof works for quadratic-form preservation; polarization is not needed for `(APR.4)`.

## 3. Tensor formation lower law

Let the active base packet have \(p>0\) positive channels and \(q\geq0\) negative channels.  Let
\(P_d,N_d\) be its positive and negative indices after \(d\) tensor formations.  The already
proved fusion recurrence is

\[
 P_{d+1}=pP_d+qN_d,
 \qquad
 N_{d+1}=qP_d+pN_d,
 \tag{APR.5}
\]

with

\[
 P_d+N_d=(p+q)^d.
 \tag{APR.6}
\]

### Theorem 3.1 -- mixed-polarity amplification floor

If \(q>0\), then for every \(d\geq0\),

\[
 \boxed{N_{d+1}\geq (p+q)^d.}
 \tag{APR.7}
\]

### Proof

Since positive integers \(p,q\) are at least one,

\[
 N_{d+1}=qP_d+pN_d\geq P_d+N_d=(p+q)^d.
\]

QED.

This is deliberately a coarse floor.  The exact value remains

\[
 2N_d=(p+q)^d-(p-q)^d.
 \tag{APR.8}
\]

The coarse floor has the advantage that no asymptotic analysis is needed.

## 4. Subrank port-budget selection

Suppose the depth-\((d+1)\) tensor packet is realized isometrically as a subform of a target
carrier \(Q_{d+1}\), and suppose a source-independent geometric theorem gives

\[
 \operatorname{ind}_{-}(Q_{d+1})\leq B_{d+1}.
 \tag{APR.9}
\]

### Theorem 4.1 -- one-depth amplified selection

If

\[
 B_{d+1}<(p+q)^d,
 \tag{APR.10}
\]

then

\[
 \boxed{q=0.}
 \tag{APR.11}
\]

### Proof

If \(q>0\), Theorem 3.1 and Theorem 2.1 give

\[
 (p+q)^d\leq N_{d+1}
 \leq\operatorname{ind}_{-}(Q_{d+1})
 \leq B_{d+1},
\]

contradicting `(APR.10)`.  QED.

### Corollary 4.2 -- eventual subrank selection

Let \(B:\mathbb N\to\mathbb N\) be any target budget.  If every tensor depth is realized and

\[
 \exists d\quad B_{d+1}<(p+q)^d,
 \tag{APR.12}
\]

then \(q=0\).  In particular, no uniform budget is required.  Any bounded, polynomial, or more
generally eventually subrank budget suffices once `(APR.12)` is proved directly.

No limit notion is load-bearing: the exact finite witness `(APR.12)` is the theorem.

## 5. Global properness interpretation

For a target family with budget \(B_d\), define its admissible depth set

\[
 \mathcal D_B(p,q)=\{d:N_d\leq B_d\}.
 \tag{APR.13}
\]

When \(p,q>0\), every depth satisfying \(B_{d+1}<(p+q)^d\) is excluded.  Thus an eventually
subrank family has finite admissible formation depth.  The positive chamber \(q=0\) has
\(N_d=0\) at every depth and survives every nonnegative budget.

This is formation properness relative to port capacity: mixed polarity escapes every target family
whose allowed negative directions grow strictly slower than source tensor rank.

## 6. Exact organ fusion and prediction

The theorem fuses four independent organs without identifying them:

| organ | exact role |
|---|---|
| tensor/species formation | creates \((p+q)^d\) formed words |
| Hermitian/Krein polarization | classifies formed words by sign |
| realization/descent | embeds the source form into a target carrier |
| geometric port/index theory | supplies the budget \(B_d\) |

It predicts a sharp obstruction in any proposed fifth organ:

> A connected one-port or polynomial-port geometric family cannot contain form-preserving copies
> of all tensor powers of one mixed-polarity packet.

Therefore failure of an attempted comparison has only three possible typed causes:

1. tensor formation is not source-native;
2. the comparison is not injective or not form-preserving;
3. target port budget grows at least as fast as source tensor rank.

This trichotomy is a useful theorem even when selection is not reached.

## 7. RH-facing architecture

Existing corpus carriers identify off-critical-line divisor data with negative Hermitian/Krein
channels.  Existing Stokes and boundary theories produce low-port target forms.  The theorem shows
exactly what a final amplification proof must construct:

1. one literal pre-divisor packet whose negative index counts the unwanted Xi sector;
2. source-native independent tensor formations of that packet;
3. at one sufficiently deep degree, an injective form-preserving realization into a target whose
   port bound is below the previous tensor rank.

The old two-premise gate “tensor formation plus a uniform budget” is replaced by one comparison
problem: construct an amplified realization with a strict rank advantage.

If the target has one negative port, depth two already selects whenever the base active rank
\(p+q>1\).  More generally a polynomial port family only needs one finite degree where exponential
tensor rank overtakes it.

This card does not construct that source realization and therefore does not prove RH.

## 8. Sharp boundaries and hostile checks

1. **Additive fusion is not tensor formation.**  Rank-fibre-product Stokes fusion cannot be inserted
   into `(APR.5)` without a separate form-preserving comparison theorem.
2. **An arbitrary embedding is insufficient.**  It must preserve the form; linear injection alone
   says nothing about inertia.
3. **A quotient is insufficient.**  Negative directions can be killed by a quotient.  Selection
   needs injection of the formed packet into the budgeted carrier.
4. **Budget equal to total rank is blind.**  The strict inequality `(APR.10)` is load-bearing.
5. **Purely negative rank one is excluded by \(p>0\).**  Its tensor signs alternate and the floor
   `(APR.7)` is false.
6. **Radicals require an active quotient.**  Null channels are removed before counting \(p,q\).
7. **Post-divisor tensoring is circular.**  Formal tensor powers of an already specialized receiver
   do not establish a source-native formation functor.

## 9. Lean certificate

Formal module:

`GaloisForLFunctions.HTGeometry.ConstitutiveAmplifiedPortBudgetSelection`

Certified declarations:

- `negIndex_le_of_injective_formEmbedding`;
- `tensorPolar_zero_of_strict_portBudget`;
- `tensorPolar_zero_of_eventual_subrankBudget`;
- `tensorPolar_zero_of_formEmbedding_portBudget`;
- `amplifiedPortBudgetSelection_closed`.

The capstone is a closed proposition quantifying over all finite matrices, realization maps, and
budgets.  The module contains no `sorry`, `admit`, new axiom, `opaque`, or `unsafe` declaration.
Scratch elaboration, direct leaf elaboration, and the targeted leaf build

`lake build GaloisForLFunctions.HTGeometry.ConstitutiveAmplifiedPortBudgetSelection`

pass.  Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.  The module is
wired into `HTGeometry.UniversalLawField`; that umbrella was not built.

## Gates

- [x] formation/polarization fusion and exact rank conservation
- [x] realization inertia monotonicity on paper
- [x] strict subrank selection on paper
- [x] Lean core
- [ ] literal pre-divisor amplified Xi realization
