# CCM-FU: compensation with newly created nonempty defects

- **Stage:** 3-formalized
- **Type:** exact source decomposition and sharp compensation classification
- **Parent:** [complete reserve extension](../1-in-progress/ccm-fu-reserve-extension-induction.md)
- **Boundary:** Complete signed source estimate and RH remain open.

## Exact result

Let the current oriented head be `-b<=0` and all current nonempty oriented
coordinates be nonnegative. Select prime q with singleton a. Over every
nonempty q-free label retain `x=A(R)`, `y=A(R+q)` and set

`T=sum(max(x-y,0)^2)`, `U=sum(max(y-x,0)^2)`, `C=sum(x*y)`.

The complete before/after good and defect energies are exactly

`G=a^2+T+U+2C`, `D=b^2`, `G'=T`, `D'=(a+b)^2+U`.

With `v=sqrt(G)-sqrt(T)>=0`, contraction of the geometric radius
`sqrt(G)+sqrt(D)` is equivalent to

`sqrt(T)*v-C <= b*(v-a)`.

Every new nonempty negative coordinate contributes to U. This removes the
previous requirement that each partner y be at most parent x. It covers
transitions out of the head-supported sign class, including the type of
successful exit exposed by the [saved-field diagnostic](../2-fully-proven/computations/ccm-fu-head-supported-defect-path-2026-09-07/README.md).
No numerical witness enters the proof.

The sharp capacity of a fixed transverse field is also formal: for arbitrary
nonnegative a,T,U,C, some finite b>=0 contracts the radius exactly when

`2*a*sqrt(T)<U+2*C`, or `U=0 and a*sqrt(T)<=C`.

Positive U requires a strict margin; equality cannot be repaired by a
finite head. This classifies a frozen field's head parameter. It does not
assert that an arithmetic schedule can choose that parameter independently.

## Dependency-closed proof

Split the full powerset into head, selected singleton and every nonempty
q-free pair. Current nonempty positivity and
`max(x-y,0)^2+max(y-x,0)^2+2xy=x^2+y^2` give G and D. The literal merger
maps each pair to x-y, kills q-containing labels, and changes the head to
`-(a+b)`, giving G' and D'.

The radius inequality becomes `sqrt((a+b)^2+U)<=b+v`. Squaring its
nonnegative sides and using `v^2+2v sqrt(T)=a^2+U+2C` gives the threshold.
It implies v>=a; equality forces U=0. If v>a, choose
`b=(a^2+U)/(2*(v-a))>=0` and square to verify the inequality. If U=0 and
v>=a, choose b=0. Comparing nonnegative squares identifies v>a with the
strict condition above and, when U=0, v>=a with `C>=a sqrt(T)`.

## Lean and scope

`RHTower/MobiusDivisorMixedTransverseCompensation.lean` contains two source
definitions and three public theorems:

- `mobiusDivisorMixedTransverse_decomposition`;
- `mobiusDivisorMixedTransverse_compensation_iff`;
- `mixedTransverseHeadRepair_iff`.

Scratch and exact-file `lake env lean` checks passed. Only this new leaf's
olean was emitted. All five new public declarations were axiom-audited once:
only `propext`, `Classical.choice`, and `Quot.sound`. No computed arithmetic
value, added axiom or proof placeholder enters the module. It is wired once
into `RHTower.lean`; no full or umbrella build ran. A dependency-rebuilding
Lake audit remains unperformed because the established module-only preflight
reports stale dependency traces.

The formal index was refreshed. Global `scripts/formal_tools.py lint`
passed with existing large-file warnings only. All owned scratch/audit files
were removed and all owned Lean processes terminated normally.

The input still requires nonnegative nonempty coordinates. Subsequent
transitions from already mixed fields, arithmetic payment of the threshold,
and complete compatible ordering remain unproved. No unconditional RH or
SD1 conclusion follows from these theorems.
