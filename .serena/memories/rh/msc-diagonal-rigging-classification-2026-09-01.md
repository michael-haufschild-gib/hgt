# MSC arbitrary diagonal rigging classification (2026-09-01)

Formal module: `formal/GaloisForLFunctions/RHTower/HedenmalmGammaSewnSquarefreeFisherDiagonalRiggingNoGo.lean`.

For physical MSC column `c_n(rho,sigma)` and literal base Möbius overlap covector `b_n(sigma)`, Lean proves exact invariant
`|c_n||b_n| = squarefreeMobiusMass rho.re n / squarefreeMobiusTotal sigma`.

A reciprocal positive diagonal Hilbert rigging exists for both sequences iff `1 < rho.re`. Necessity: weighted AM-GM/Cauchy--Schwarz forces summability of the invariant product. Sufficiency: canonical balanced weight `exp ((rho.re-sigma) log n)` makes both weighted square densities equal the invariant product.

Thus every strict-right Xi zero (`1/2 < Re rho < 1`) forbids every coefficient-faithful reciprocal diagonal Hilbert/Gelfand realization of the physical MSC overlap denominator. Capstone: `strictRightXiZero_mscPhysicalOverlapDiagonalRiggingNoGo`, retaining existing residue split and four-unit regular-germ energy.

Positive survivor: non-diagonal or genuinely distributional completion only. Targeted build passed; axioms only `propext`, `Classical.choice`, `Quot.sound`. Umbrella wired. Literature through Aug 2026: no collision found.