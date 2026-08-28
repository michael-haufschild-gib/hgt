# HB fixed-weight orbit Ward symmetry no-go

Status: failed/retired
Route: HB
Closed: 2026-08-28

## Proposed route

Use FE reflection, Schwarz conjugation, Stokes orientation, or a fixed real group character to
force universal vanishing of the four-sector HC16 Peierls orbit trace without adding a physical
stationarity theorem.

## Exact obstruction

HC17 classifies every fixed reflection-invariant pair weighting:

`WardIdentity(n,a,b) ↔ a+b=0 ∨ RiemannHypothesis`.

Symmetry alone supplies only the zero-total choice `b=-a`. That identity cancels identically for
every Xi zero, including tilted zeros, so it is RH-blind. Every nonzero-total choice, including all
positive physical averages, is not a formal symmetry consequence: its universal vanishing is
equivalent to RH.

## Positive survivor

The sharp survivor is the nonzero-total Ward endpoint. A gauge-fixed action or boundary theorem
that independently proves

`HBXiPeierlsFESchwarzFixedWeightWardIdentity n a b`

for one fixed pair with `a+b ≠ 0` proves RH. Equal positive weights `a=b=1` give the canonical
endpoint. This survivor is dependency-closed and formalized in
`ThetaCuspHawkingBMFESchwarzFixedWeightWardDichotomy.lean`.

## Lean status

- Formalized theorem: `hbXiPeierlsFESchwarzFixedWeightWardIdentity_iff`
- Nonzero-total endpoint: `hbXiPeierlsFESchwarzFixedWeightWardIdentity_iff_rh_of_sum_ne_zero`
- Positive endpoint: `hbXiPeierlsFESchwarzPositiveWeightWardIdentity_iff_rh`
- Blind cancellation: `hbXiPeierlsFESchwarzZeroTotalWardIdentity`
- Target build passed; axiom audit contains only Lean/mathlib foundational axioms

## No-go conclusion

Retire fixed-weight orbit symmetry as a source of useful stationarity. It either chooses a
zero-total, information-erasing character or assumes/proves the full missing RH content. Continue
only through a literal physical derivation of a nonzero-total Ward law.
