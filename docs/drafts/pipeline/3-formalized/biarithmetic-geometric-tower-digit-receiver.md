# The geometric tower has an exact weighted-digit receiver

- **ID:** biarithmetic-geometric-tower-digit-receiver
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Golden digital module](../1-in-progress/biarithmetic-golden-digital-module.md)
- **Statement:** For `|a|<5`, the geometric prime-five source `I_a(5^r)=a^r` has absolutely convergent mean `5/(5-a)` and exact centered prefix `A_(I_a)(n)=-a/(5-a) D_a(n)`.

## Proof

The injection `r -> 5^r` enumerates the support. Its mean series becomes the geometric
series `sum_r(a/5)^r`; its absolute mean is summable because `|a|/5<1`.

The already formalized Dirichlet identity is `(delta_1-a delta_5)*I_a=delta_1`. The exact
finite-horizon local-factor prefix identity, with `m=5/(5-a)`, reads

`0=A(n)-a A(floor(n/5))+a m [n/5-floor(n/5)]`.

Here the new mean is `m-a m/5=1`, and the unit source at mean one has zero centered prefix.
Euclidean division gives `n/5-floor(n/5)=(n mod5)/5`. Hence

`A(n)=a A(floor(n/5))-[a/(5-a)](n mod5)`.

The row `-[a/(5-a)] D_a(n)` obeys exactly this recursion and vanishes at zero. Strong
induction, using `floor(n/5)<n` for positive `n`, proves equality at every integer horizon.
The finite algebraic identity holds for every `a!=5` at the displayed explicit mean; the
restriction `|a|<5` identifies that mean with the actual convergent source mean.

## Scope and verification

This establishes the ordinary-floor source bridge directly from convolution and Euclidean
division. It does not require the later bilateral profile, periodization, or Riemann-sum
limit. Those remain necessary for the complete escape-module classification.

- [x] Dependency-closed paper proof and exact source normalization.
- [x] Lean mean series, finite recurrence, and actual centered-prefix identity.
- [x] Direct repository check of `GeometricTowerDigitReceiver.lean` and umbrella import.
- [x] Five main declarations transitively audited: only `propext`, `Classical.choice`, and `Quot.sound`.

Lean declarations: `hasSum_fiveTower_div`, `summable_abs_fiveTower_div`,
`fiveTower_centeredPrefix_rec`, `fiveTower_centeredPrefix_eq_digitRow`, and
`fiveTower_actualPrefix_eq_digitRow`, in
`GaloisForLFunctions.BiarithmeticGeometry.GeometricTowerDigitReceiver`.
