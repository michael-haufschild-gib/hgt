# Route L authoritative frontier — relevant-complex Green/Paugam descent (2026-08-07)

## Carrier audit

Actual arithmetic coefficient is already constructed as pro-Stein derived residue fibre
`E_arith^S = Fib(partial_ar^S)`, with strict restricted prime/real target. Its strict Poisson model is

- `C^0 = C ⊕ H_cap`
- `C^1 = H_- ⊕ P_Q`
- `C^2 = D_Ar,Q`
- `d0(a,f) = (Zf,0)`
- `d1(g,u) = pr(u)`.

Cohomology is strict/Hausdorff:
`H^0=C`, `H^1=M_zeta`, `H^2=C(-1)`.
Flow, three-term operations, algebraic cup surface, endpoints, and comparison are formalized.

The raw coarse invariant-sheaf Rost-Schmid/signature two-column totalization is optional. Do not use it as definition of relevant coefficient.

## Retired false frontier

`DAC_FULL_CAUCHY_RECOLLEMENT_FIBRE_ENDPOINT_LAW` is retired as authoritative Route-L source theorem. No actual restriction map was constructed with endpoint-only fibre, and that stronger fibre is not necessary.

Survivor: `DeningerArithmeticThreeTermChainMap.mapH1_injective_of_fiberH1_exact` is a valid unconditional generic theorem. Full-packet Cauchy/Bessel conservativity remains one optional sufficient proof of Green-energy radical.

Card moved to:
`docs/drafts/pipeline/5-failed/deninger-full-cauchy-recollement-fibre-endpoint-law.md`.

## First unresolved source theorem

`DAC_RELEVANT_GREEN_PAUGAM_CHAIN_TRANSGRESSION`.

For constructed strict comparison
`Phi : E_arith^bullet -> C_PZ^bullet`,
construct source leafwise Calderon-Green cup/trace `Omega_geom` and explicit nuclear cochain transgression `T`, before divisor decomposition, such that

`Omega_geom - Phi^*(Omega_Meyer/Paugam) = d_Hom T`.

`T` must use Meyer's common-cutoff corrections
`M_phi - Z M_phi Z^-1` and
`M_phi - F J M_phi J F`,
and commute with all Tate-Milnor attaching maps, residue/corestriction, and real orientation descent.

On H1:
`tr_arith(x cup y) = psi_Paugam(H1(Phi)x, H1(Phi)y)`.

This is source-pure and strictly upstream of RH because it compares alternating forms and asserts no sign.

## Remaining Route-L chain

1. `DAC_RELEVANT_GREEN_PAUGAM_CHAIN_TRANSGRESSION`.
2. `DAC_GLOBAL_GREEN_ENERGY_RADICAL`: source Hodge rotation, closability, nonnegative energy, radical exactly closed middle boundaries. Full-packet Cauchy/Bessel comparison is optional sufficient method.
3. `DAC_ARITHMETIC_HODGE_SCHWARTZ_RESOLVENT_CORE`: density in nuclear Meyer quotient and off-axis resolvent preservation.
4. Existing purity theorems then imply RH. Fixed Green-BV/two-prime transports are RH-equivalent endpoint tests, not inputs.

## Calderon-Witt role correction

Local/all-prime Calderon-Witt cup, refinements, zero radical before incidence, exterior-cup surjectivity, exact Milnor incidence, Green contractions, and H0/H1/H2 vanishing are formalized.

Later grading theorem proves reciprocal positive regulator form pulls back identically to zero on endpoint-global middle cycles. It is transverse/degree-two source data and endpoint witness, not M_zeta middle Hodge metric.

Formalized survivor card:
`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/deninger-calderon-witt-derived-cup-incidence-source.md`.

Failed middle-Hodge role:
`docs/drafts/pipeline/5-failed/deninger-calderon-witt-derived-cup-source.md`.

## Formal anchors

- `DeningerArithmeticThreeTermAssembly.lean`
- `DeningerSquareZeroAmalgamation.lean`
- `DeningerThreeTermTotalization.lean`
- `DeningerThreeTermCupProduct.lean`
- `DeningerMeyerPoissonCalderonGraph.lean`
- `DeningerMultiplicativeGreenTransgression.lean`
- `DeningerCalderonWittDerivedCupSource.lean`
- `DeningerCalderonWittMilnorIncidence.lean`
- `DeningerMeyerPaugamGradingObstruction.lean`
- `DeningerPolarSignLift.lean`
- `DeningerPolarSignCFC.lean`
- `DeningerPolarSignFredholm.lean`.

Do not rediscover coefficient construction, Paugam alternating cup, finite Calderon-Witt cup/incidence, polar-sign lift, or generic full-Cauchy injectivity. Hard frontier is source-geometric Green/Paugam chain transgression, then exact energy radical and nuclear resolvent faithfulness.
