# Golden normalized cubing preserves determinant and loses point-count positivity

- **ID:** biarithmetic-golden-normalized-cube
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean; exact source counterexample)
- **Parent:** [Fixed-determinant cubic amplification](../1-in-progress/biarithmetic-fixed-determinant-cube-amplification.md)
- **Statement:** Cubing each actual golden root and dividing by five preserves their product five, gives trace ten, and changes the first two point counts to minus four and minus sixty-four. The original actual golden datum has nonnegative point counts at every degree.

For the actual roots `alpha,beta`, the checked identities
`alpha+beta=alpha*beta=5` give

`(alpha^3/5)(beta^3/5)=5`,
`alpha^3/5+beta^3/5=((alpha+beta)^3-3alpha*beta*(alpha+beta))/5=10`.

The transformed counts are therefore `5+1-10=-4` and
`25+1-(10^2-2*5)=-64`. The original nonnegative-count theorem is reused
from ACS and included in the transitive audit.

Lean: `BiarithmeticGeometry/GoldenNormalizedCube.lean`.
Main declarations: `goldenNormalizedCube_product`, `goldenNormalizedCube_sum`,
`goldenNormalizedCubePointCount_two`,
`golden_pointCount_positive_but_normalizedCube_negative`.

- [x] Direct repository check with `lake --old env lean`.
- [x] Umbrella import wired; umbrella not compiled.
- [x] Four transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.

Fixed determinant is not a definition of analytic conductor. General
bounded-conductor amplification remains open. The parent route is not
retired: its full integral trace classification is still being formalized.
