# Suzuki causal-depth Gamma trace-class feature no-go

## Status

- Stage: Formalized in Lean 4
- Route: CCM-FU
- Claim: C28
- Module: `GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaTraceClassFeatureRobinTraceNoGo`

## Closed result

The actual causal-depth Gamma feature operator `F` is Schatten-one before Gram formation. Its
prime-depth weights `A_p r_p^e` are jointly `ℓ¹`: `A_p` has the corpus's summable
`(1+log p)p^(-5/4)` majorant and every `r_p` lies below one fixed geometric cap. Each canonical
column of `F` has norm at most its weight, hence the canonical rank-one column expansion is
nuclear.

Therefore every response family with one uniform operator-norm ceiling, at arbitrary finite or
infinite rank, has bounded pre-Gram relative trace against `F`. The correction is `o(N)` and cannot
semibound the rectangular transition-core Ward defect.

Main declarations:

- `summable_suzukiCausalDepthGammaWeight_allPrime`
- `suzukiCausalDepthGammaFeatureOperator_memSchattenClass_one`
- `suzukiCausalDepthGammaTraceClassFeatureCorrection_eq_quadraticRankHSCorrection`
- `suzukiCausalDepthGammaTraceClassFeatureCorrection_sublinear`
- `no_suzukiCausalDepthGammaTraceClassFeatureWardProducer`

## RH-chain consequence

`F∈S¹` -> bounded response trace is `O(1)` without rank restriction -> correction is sublinear ->
`no_sublinear_transitionCore_rectangularWardProducer`. C27's superquadratic-rank escape is closed.
Survivor requires response norm blow-up, moving/non-`S¹` source, or singular relative trace outside
bounded trace duality.

## Audit

- Direct `lake env lean` passed.
- Targeted module build passed.
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
- No computation and no RH premise.
