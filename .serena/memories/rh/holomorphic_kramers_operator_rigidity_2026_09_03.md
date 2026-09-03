# Dimension-free bounded same-fibre Kramers rigidity (2026-09-03)

Let `A : ℂ → H →L[ℂ] H` have holomorphic weak matrix coefficients on connected open `U`. If a fixed map `J` is antiunitary at inner-product level and commutes fibrewise with `A(z)`, then `inner (Jx) (A(z)(Jy)) = conj(inner x (A(z)y))`. Both sides are holomorphic coefficient functions, so scalar conjugate-pair/open-mapping rigidity makes every coefficient constant. Inner-product separation makes `A` constant.

Formalized in `formal/GaloisForLFunctions/RHTower/HolomorphicKramersOperatorRigidity.lean` as `RHTower.weaklyHolomorphic_fixedAntiunitary_operator_constant`. Direct Lean and targeted build pass; axioms only `propext`, `Classical.choice`, `Quot.sound`. Wired into `RHTower.lean`.

A second theorem removes boundedness entirely for a fixed domain: if `A : ℂ → D → H` has holomorphic weak coefficients and fixed domain/codomain antiunitary maps intertwine it, then `A(z)y` is constant for every `y : D`.

This closes bounded same-fibre holomorphic Kramers/Fredholm families and fixed-domain unbounded variants in arbitrary Hilbert dimension. Only parameter reversal, genuinely parameter-dependent domains, or non-pointwise source laws survive.