# Order-two multiple Gamma has a rational period-deletion depth phase split

- **ID:** `order-two-multiple-gamma-period-deletion-phase-split`
- **Stage:** 2-fully-proven / needs independent audit
- **Type:** THEOREM (paper) / NATURAL NONPRODUCT JOINT-REALIZATION LAW
- **Scientific status:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [PAPER-PROVED]`
  `[UNCONDITIONAL LEAN PROOF OPEN AT THE ORDER-ONE ANALYTIC PARENT] [NOT AN RH RESULT]`
- **Parents:**
  `elliptic-gamma-rank-three-da-spectrum`;
  `multiple-elliptic-gamma-transverse-constraint-depth`;
  Masaki Kato, *Differential Algebraicity of the Multiple Elliptic Gamma Function for a Rational
  Period* (2021)
- **Failed predecessor:**
  `../../5-failed/hypertranscendental-gale-kolchin-duality.md`
- **Successor:**
  `../../1-in-progress/multiple-gamma-period-deletion-annihilator-law.md`
- **Statement:** Two explicit order-two multiple-elliptic-gamma sources have the same total
  rational period rank three and the same rank excess one, but their minimum transverse DA depths
  are respectively two and one.  The split is exactly whether deletion of one structural period
  leaves a Kato-rational face; total rank and real Gale geometry do not determine the depth.

## Goal

Programme 3 asks for a natural nonproduct theorem: separately varying marginals must obey a joint
restriction not obtained by storing those marginals in a larger stack.  This card supplies such a
restriction in the multiple-Gamma hierarchy.  The marginal number

```text
rank_Q{1,tau_0,tau_1,tau_2}-2
```

is the same in two sources, while their DA depth differs.  The missing joint datum is the labelled
rational deletion geometry of the period frame.

## Setup

Let

```text
Psi_2(z;tau_0,tau_1,tau_2)=d/dz log G_2(z;tau_0,tau_1,tau_2)
```

be the logarithmic derivative of Nishizawa's order-two multiple elliptic gamma function, with all
parameters in the upper half-plane.  Put

```text
x_j=T_(tau_j)-1.
```

Define the distinct-direction transverse DA depth by

```text
d_DA(Psi_2;tau)
  = min {|J| : J subset {0,1,2}, product_(j in J) x_j Psi_2 is DA},        (1)
```

where the empty product is allowed.  The hierarchy relation is

```text
x_j Psi_2(z;tau)=Psi_1(z;tau with tau_j deleted),                          (2)
```

up to the standard DA normalization, and two distinct differences reduce to the DA order-zero
theta logarithmic derivative.

Consider the two frames

```text
tau^circ=(i, sqrt(2)+i, sqrt(2)+2i),                                       (3)
tau^col =(i, 2i,          sqrt(2)+i).                                     (4)
```

The first has the full-support rational relation

```text
tau^circ_2=tau^circ_0+tau^circ_1,                                         (5)
```

while in the second the first two parameters are commensurable:

```text
tau^col_1=2*tau^col_0.                                                     (6)
```

## Main theorem `[PROVED HERE]`

For the frames `(3)` and `(4)`:

```text
rank_Q{1,tau_0,tau_1,tau_2}=3,
rank_Q{1,tau_0,tau_1,tau_2}-2=1,                                         (7)
```

but

```text
d_DA(Psi_2;tau^circ)=2,
d_DA(Psi_2;tau^col)=1.                                                     (8)
```

More precisely:

1. in the circuit frame `(3)`, deleting any one parameter leaves `1` and the two remaining
   parameters rationally independent, so every singleton difference `x_j Psi_2` is HT;
2. in the coloop frame `(4)`, deleting `tau^col_2` leaves the Kato-rational pair `(i,2i)`, so
   `x_2 Psi_2` is DA;
3. the coloop-frame source `Psi_2` itself is HT, because its `x_0`-difference is the HT order-one
   source with periods `(2i,sqrt(2)+i)`.

Thus total rational rank does not determine transverse DA depth outside the fully independent
stratum.  The labelled deletion geometry does.

## Proof

### 1. Rational ranks

The numbers `1`, `i`, and `sqrt(2)+i` are rationally independent.  Indeed, a rational relation

```text
a+b*i+c*(sqrt(2)+i)=0
```

has real part `a+c*sqrt(2)=0`, hence `a=c=0` by irrationality of `sqrt(2)`, and then its imaginary
part gives `b=0`.

For `(3)`, relation `(5)` shows that the four labelled periods have rank at most three, while the
preceding independent triple shows rank exactly three.  Every deletion still leaves rank three:

- deleting `tau^circ_2` leaves the independent triple just treated;
- deleting `tau^circ_1` leaves `1,i,sqrt(2)+2i`, independent by the same real/imaginary argument;
- if
  `a+b*(sqrt(2)+i)+c*(sqrt(2)+2i)=0`, its real part gives `a=0` and `b+c=0`, while its imaginary
  part then gives `c=0`, so deleting `tau^circ_0` also leaves an independent triple.

For `(4)`, relation `(6)` and independence of `1,i,sqrt(2)+i` give rank exactly three.  Deleting
`tau^col_2` drops the rank to two; deleting either of the first two parameters retains rank three.
This proves `(7)` and identifies the deletion geometries.

### 2. Circuit-frame depth

By `(2)`, each singleton difference of `Psi_2(z;tau^circ)` is an order-one elliptic-gamma
logarithmic derivative on one of the three residual pairs.  The rank calculation above says that
`1` and each residual pair are rationally independent.  The exact order-one elliptic-gamma theorem
therefore makes all three singleton differences HT.

On the other hand, applying any two distinct structural differences descends through the hierarchy
to an order-zero theta logarithmic derivative, which is DA.  Hence no set of zero or one distinct
directions reaches the DA field, while every two-direction set does.  Therefore

```text
d_DA(Psi_2;tau^circ)=2.                                                     (9)
```

The zero-direction case follows automatically: if `Psi_2` were DA, all its translation differences
would be DA, contradicting the HT singleton differences.

### 3. Coloop-frame depth

Deleting `tau^col_2` gives the order-one parameter pair `(i,2i)=i*(1,2)`.  Kato's rational-period
theorem makes the corresponding elliptic gamma function DA; logarithmic differentiation preserves
DA.  Equation `(2)` therefore gives

```text
x_2 Psi_2(z;tau^col) is DA.                                                (10)
```

The source itself is not DA.  Its `x_0`-difference is the order-one source with parameters
`(2i,sqrt(2)+i)`.  The triple `1,2i,sqrt(2)+i` is rationally independent, so the exact order-one
theorem makes this difference HT.  A translation difference of a DA function is DA, contradiction.
Thus `Psi_2(z;tau^col)` is HT, while `(10)` reaches DA in one direction, proving

```text
d_DA(Psi_2;tau^col)=1.                                                      (11)
```

Equations `(9)` and `(11)` prove `(8)`. `QED`

## What the theorem rules out

1. **Rank excess alone.** Both sources have excess one, but one needs two transverse differences.
   The generic identity `depth=rank excess` remains correct on the fully independent stratum; it
   does not extend to dependent frames.
2. **Real Gale control.** Real collinearity data cannot recover the exact DA depth.  The stronger
   counterexample in the failed predecessor keeps the entire DA ideal fixed while the real Gale
   matroid changes.
3. **A product of marginals.** Order, total rank, ambient real dimension, and existence of a
   rational relation do not independently determine the answer.  The support of that relation
   under labelled deletion is load-bearing.

## Positive joint-realization law

For order two, one structural difference is DA exactly in the directions whose deletion leaves a
DA order-one face.  In the two frames above this is already a forbidden-combination theorem:

```text
same order + same total rational rank + same ambient dimension
does not permit an arbitrary depth;
the residual face selected by the deleted label decides the phase.                         (12)
```

The live all-order conjecture replaces the scalar rank marginal by the complete rational
period-deletion ideal.

## Parent-theory and novelty attack

- Nishizawa and Narukawa supply the multiple-elliptic-gamma hierarchy and its functional
  equations; they do not classify DA depth on dependent period strata.
- Kato proves DA when the complete period vector is rational, in the sense of lying in one
  rational ray, and explicitly leaves non-rational periods open.  His theorem supplies the DA
  residual face in `(10)`, not the phase split `(8)`.
- Matroid deletion, coloops, circuits, and cogirth are classical.  The terminology is not new.
- Parameterized difference Galois theory supplies the parent mechanism for proving HT from
  nonsummable residual faces.  No located theorem computes this dependent-period depth split for
  multiple elliptic gamma functions.

Targeted exact/equivalent/stronger searches through July 2026 located no paper stating `(8)`, no
classification of dependent-period multiple-elliptic-gamma annihilator ideals, and no theorem
identifying their DA depth with labelled rational deletion geometry.  This is a preliminary
absence result, not a final priority claim.  The scientific content is the natural special-function
phase split, not the classical matroid vocabulary.

Primary sources:

- M. Nishizawa, *An elliptic analogue of the multiple gamma function*, J. Phys. A 34 (2001),
  7411--7421.
- A. Narukawa, *The modular properties and the integral representations of the multiple elliptic
  gamma functions*, Adv. Math. 189 (2004), 247--267,
  `https://arxiv.org/abs/math/0306164`.
- M. Kato, *Differential Algebraicity of the Multiple Elliptic Gamma Function for a Rational
  Period*, Funkcialaj Ekvacioj 64 (2021), 225--235,
  `https://doi.org/10.1619/fesi.64.225`.

## Unconditional Lean boundary

No Lean theorem is claimed for `(8)`.  The hierarchy identities for the project's actual
meromorphic multiple-elliptic-gamma kernels and the squarefree combinatorial ideal core already
exist.  The missing load-bearing input is the unconditional Lean formalization of the exact
order-one non-rational elliptic-gamma HT/defect theorem.  Introducing that result as an axiom or as
a hypothesis would violate the project standard, so this card remains Stage 2.

No Lean build was needed for this paper proof: the existing generated API and source declarations
were audited before the theorem was formulated.

## Gates

- [x] exact natural-family claim isolated
- [x] rational-rank and deletion calculations proved symbolically
- [x] circuit-frame depth two proved from the exact order-one parent and hierarchy
- [x] coloop-frame depth one proved from Kato plus the exact order-one parent
- [x] hostile rank-excess and real-Gale attacks passed
- [x] preliminary exact/equivalent/stronger literature search completed
- [ ] independent specialist proof and priority audit
- [ ] unconditional Lean proof of the exact order-one analytic parent
- [ ] unconditional Lean formalization of `(8)`

## Log

- 2026-07-17 — Opened from programme 3 of `docs/reports/rh-status-1707.md` after the proposed real
  Gale--Kolchin control law failed on a natural order-two multiple-Gamma frame.
- 2026-07-17 — Proved the equal-rank/different-depth phase split and promoted it to Stage 2; isolated
  the all-order rational period-deletion annihilator as the successor.
