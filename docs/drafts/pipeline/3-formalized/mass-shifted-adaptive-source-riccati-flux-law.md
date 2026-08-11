# Adaptive Arithmetic Source Riccati-Flux Law

- **ID:** mass-shifted-adaptive-source-riccati-flux-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3 exact open core
- **Statement:** Current admission's literal completed rational--Gamma-minus-von-Mangoldt source
  is exact negative forcing in a velocity-free cumulative Jacobi Riccati law. Forced
  multiplicity normalization yields degree-independent contraction `U′ < -U²`, which makes current
  flux strictly positive on every complete terminal shifted-Xi positive chamber.

## Theorem [PROVED HERE]

Let `s_y(k)=Re m_k(y)` and suppose its Hankel block through order `n+2` is positive definite,
with `n>0`. Write

`F_n=2 sum_(j<n) alpha_j+alpha_n`,

`D_n=2 sum_(j<n) alpha_j^2+alpha_n^2
     +4 sum_(j<n) beta_j+2(n+1)(beta_n+beta_(n+1))`,

and let `E_n` be adaptive Jacobi energy. Existing moving-admission transport gives `F_n'=-D_n`.
Direct expansion of completed squares gives exact source identity

`2E_n=D_n+alpha_n F_n+2n alpha_n^2`.

Therefore

`F_n'=alpha_n F_n+2n alpha_n^2-2E_n`.

At `y=w^2`, canonical source law is

`A_n^sharp(w)=2 h_n E_n`,

so literal arithmetic forcing is

`F_n'(w^2)=alpha_n F_n+2n alpha_n^2-A_n^sharp(w)/h_n`.

This is source-first: amplitude is current inverse-Hankel admission, completed arithmetic source is
formed before observation, and no fixed reporter or orientation map occurs.

Gaussian-visible bulk `V_n=E_n-(n+1)beta_(n+1)>0` gives equivalent exact law

`F_n'=alpha_n F_n+2n alpha_n^2-2V_n-2(n+1)beta_(n+1)`.

Weighted Cauchy for multiplicities `2,...,2,1` proves

`F_n^2 <= (2n+1)(2 sum_(j<n) alpha_j^2+alpha_n^2)`.

Positive beta contribution is strict, hence

`(2n+1)F_n' < -F_n^2`.

Define forced degree-normalized current `U_n=F_n/(2n+1)`. Then every positive chamber obeys

`U_n' < -U_n^2`,

with no degree-dependent constant. If a differentiable function on a complete right ray satisfies
this strict Riccati law and is nonpositive once, strict decrease makes it negative thereafter.
For `g=1/U-y`, the Riccati inequality gives `g'>0`; choosing
`b=y-1/U(y)>y` forces `1/U(b)>0`, contradicting `U(b)<0`. Thus `U>0` on the ray.

Far-right shifted-Xi Hankel positivity supplies such complete terminal chamber for every fixed
degree. Consequently each fixed-degree actual normalized current flux is unconditionally strictly
positive throughout its terminal positive chamber; no asymptotic rate is assumed.

## Conjecture / proof-or-fail loop

1. **Conjecture:** arithmetic source only supplies static positive energy. **Failed.** Admission
   velocity cancels in cumulative trace and source is exact negative Riccati forcing.
2. **Conjecture:** Gaussian observation discards shape needed by evolution. **Failed at first
   defect.** Missing part is exactly `(n+1)beta_(n+1)`; positive visible bulk remains explicit.
3. **Conjecture:** Riccati contraction degenerates as degree grows. **Failed after forced
   normalization.** Dividing by trace multiplicity `2n+1` gives universal `U′ < -U²`.
4. **Conjecture:** terminal flux sign still needs arcsine recession or a convergence rate.
   **Failed.** Finite-time blow-down prohibits `U<=0` on any complete right ray.
5. **Survivor:** current-chamber source and sign are complete. Remaining obstruction is relational:
   compare frozen crossing history with later current admission uniformly while degree changes.

## Novelty and theatre audit

- Algebraic weighted Cauchy and scalar Riccati blow-down are standard individually.
- New corpus knowledge is their forced identification with actual adaptive completed shifted-Xi
  arithmetic source, exact Gaussian edge split, and multiplicity normalization selected by
  cumulative admission connection.
- Result is not RH. It removes current-chamber sign and fixed-degree recession from open core.
  It does not yet prove cross-degree/frozen-current holonomy needed to exclude cofinal escape.
- Every statement above is a proved equality or strict inequality; no numerical experiment,
  orientation choice, or finite-classifier claim is used.

## Lean certificate

Module `RHTower.XiShiftedCanonicalAdmissionGaussRiccatiSource` proves:

- `xiShiftedCanonicalAdmissionRelativeGaussBulk_eq_visibleEnergy`
- `xiShiftedCanonicalAdmissionRelativeGaussBulk_pos`
- `two_mul_adaptiveOrthoJacobiEnergy_eq_cumulativeDissipation_add_riccatiDrift`
- `hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_sourceRiccati`
- `hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_gaussRiccati`
- `hasDerivAt_xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_literalArithmeticRiccati`
- `cumulativeJacobiTrace_sq_le_mul_alphaEnergy`
- `xiShiftedCanonicalAdmissionCumulativeJacobiFlux_sq_lt_mul_dissipation`
- `deriv_xiShiftedCanonicalAdmissionRenormalizedJacobiFlux_lt_neg_sq`
- `pos_of_deriv_lt_neg_sq_on_Ioi`
- `xiShiftedCanonicalAdmissionRenormalizedJacobiFlux_pos_of_terminalChamber`
- `exists_xiShiftedCanonicalAdmissionRenormalizedJacobiFlux_terminal_pos`

## Gates

- [x] 0 -> 1: source-first conjectures and hostile failures isolated
- [x] 1 -> 2: dependency-closed paper proof above
- [x] 2 -> 3: unconditional Lean proof; direct check and targeted build pass; axiom audit pass
- [ ] 3 -> 4: specialist novelty review and standalone exposition

## Log

- 2026-08-11 — Exact literal and Gaussian Riccati source laws proved.
- 2026-08-11 — Degree-uniform normalized contraction and terminal chamber positivity proved without
  computation. Lean capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.
