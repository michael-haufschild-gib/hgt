# Mass-shifted completed-source/nodal-history bridge

- **ID:** mass-shifted-completed-source-nodal-history-bridge
- **Stage:** 3-formalized
- **Type:** THEOREM + EXACT FRONTIER
- **Source:** mass-shifted spectral-face §9.3; bridge between degree-centered arithmetic source and
  faithful apex-centered nodal producer

## Frozen conjecture

For finite positive degree `n>=2`, degree-centered causal Jacobi history equals

`sum_(P_n(x)=0) x^2 + alpha_n * sum_(P_n(x)=0) x`.

Consequently literal rational--Gamma-minus-von-Mangoldt completed source satisfies a division-free
balance law with total faithful apex-centered residues:

`y^2 S_n = 2 h_n (R_n(y) + n + y^2 alpha_n T_n)`,

where `y=w^2`, `R_n(y)=sum_x((y*x)^2-1)`, and `T_n=sum_x x`.

## Falsifiers

- Any index mismatch in beta inventory or current alpha term kills conjecture.
- Source equality must use literal degree-centered completed arithmetic source and finite positive
  block only; no global moment measure or RH assumption.
- Balance must be division-free.  A quotient by norm may be recorded only as corollary.
- Even if true, signed total does not control positive null-flag mass; record this boundary.

## Attack

Combine exact root trace and root-square Jacobi identities already in corpus with finite-block
degree-centered source/history theorem, then eliminate quadratic nodal energy using exact centered
residue total.

## Proof `[PROVED HERE]`

Finite positive-block Vieta/Jacobi laws give

`sum_x x = sum_(j<n) alpha_j`,

`sum_x x^2 = sum_(j<n) alpha_j^2 + 2 sum_(j<n) beta_j`.

Substitution into definition

`H_n = sum alpha_j^2 + alpha_n sum alpha_j + 2 sum beta_j`

proves

`H_n = sum_x x^2 + alpha_n sum_x x`.

Finite-block degree-centered source theorem gives literal completed arithmetic source

`S_n = 2 h_n H_n`.

For `y=w^2`, direct finite summation gives

`R_n(y)=sum_x((yx)^2-1)=y^2 sum_x x^2-n`.

Eliminating `sum_x x^2` between these identities yields division-free balance

`y^2 S_n = 2 h_n (R_n(y)+n+y^2 alpha_n T_n)`.

Since finite positivity makes `h_n>0`, division gives exact recovery formula for `R_n`.  No global
moment form, measure, limit, computation, or RH premise enters.

## Hostile audit

- Index audit passes: beta inventory is precisely root-square energy; current `alpha_n` survives as
  diagonal/root-trace coupling.
- Source audit passes: `S_n` is literal degree-centered rational--Gamma-minus-von-Mangoldt source
  formed from canonical admission before evaluation.
- Division-free balance passes; quotient is only corollary under proved norm positivity.
- Positivity closure fails: `R_n` is signed total.  Negative sub-apex residues can cancel positive
  super-apex residues.  Existing nodewise null-flag shear remains necessary.

This is positive no-go closure: coefficient source and nodal producer are one exact account, but
source total alone cannot replace pre-aggregation positive shear.  Remaining theorem must control
positive variation rather than signed total.

## Lean certificate

`RHTower/XiShiftedCanonicalAdmissionCenteredSourceJacobiBridge.lean` proves nodal Jacobi-history
realization, literal completed-source/root-history law, division-free balance, and quotient
recovery.  Targeted build passes.  Axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.  Umbrella wired.  Route-specific bridge remains `[NOVELTY UNVERIFIED]`.

## Log

- 2026-08-13 — corpus collision exposed missing bridge between coefficient-level arithmetic source
  and new faithful pole/log-derivative carrier; conjecture frozen.
- 2026-08-13 — conjecture proved on paper and unconditionally in Lean; signed-total cancellation
  isolated as exact remaining positive-variation frontier.
