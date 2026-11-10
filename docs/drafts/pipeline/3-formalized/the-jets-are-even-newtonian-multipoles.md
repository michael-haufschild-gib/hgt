# The jets are even Newtonian multipoles

- **Stage:** 3-formalized
- **Assembly:** A97, multipoles and rulings.
- **Module:** `HodgeTheoryOfAFixedPart/TheJetsAreEvenNewtonianMultipoles.lean`.

For distinct positive integers `m,n`, the even Newtonian kernel on an axis in Euclidean three-space is

`(1/|m−n| + 1/(m+n))/2 = Σ_{j≥0} min(m,n)^(2j)/max(m,n)^(2j+1)`.

The summands are exactly `jetLevel j m n`. The Euclidean distance identity reduces the left side to `jetKernel`; `hasSum_jetLevel` supplies convergence. Declaration: `hasSum_even_newtonianMultipoles`.

At weight zero, evaluation at the origin is `1/n`. Beyond every charge, multiplication by the radius gives `1` exactly. Finite pairings therefore give `degOne` and `degTwo`, respectively. Declarations: `sum_axialMultipole_origin_eq_degOne`, `sum_normalized_axialMultipole_eq_degTwo`, `tendsto_normalized_axialMultipole_zero`.

Direct Lean audit passed. All four declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.
