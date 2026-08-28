# HC28: FZZ parity independent radial-phase incidence classification (2026-08-28)

Route: FZZ-P. Status: formalized sharp no-go with positive survivor.

Module:
`formal/GaloisForLFunctions/RHTower/FZZCigarParityIndependentRadialPhaseIncidenceClassification.lean`.

Using HC27's literal Fermi clock `r(beta)=-Re y(beta)` and HC25's complete quintic phase
`q(gamma)=y(gamma)^5`, define independent contracting `r*q`, unit `q`, and expanding `r^-1*q`
encodings. Lean proves exact incidence for the dyadic Mellin character: contracting iff
`Re rho<1/2`, unit iff equality, expanding iff `Re rho>1/2`. Every character belongs to exactly one
sector.

No-go: allowing independent radial/phase scales and arbitrary sector selection makes incidence
universal, including on every open-strip zeta divisor. It cannot detect RH.

Positive survivor: unique sector class is the exact sign of `Re rho-1/2`; viable dynamics must
force the unit sector or a restrictive same-scale coupling.

Audit: direct Lean and target-only build passed (9765 jobs); seven endpoints use only `propext`,
`Classical.choice`, and `Quot.sound`. Frontier map was not edited.
