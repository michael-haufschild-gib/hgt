# Route U sparse-parabolic source-capital no-go

- **ID:** `route-u-sparse-parabolic-source-capital-no-go`
- **Stage:** 3-formalized
- **Type:** FALSIFIED proof class / exact scalar countermodel
- **Source:** `rh-current-frontier-map.md` · Route U `COF` gate
- **Statement:** Route U's proved parabolic synchronization, fixed-degree source capital,
  renormalized source divergence, degree coercivity, and positive finite all-degree reserve do not
  imply nonsummable cofinal renewal cost.

## Goal

Hostile-test current Route U completion, not its RH-equivalent endpoint. Decide whether existing
source laws force false-RH cofinal strict renewals to spend infinite common source capital.

## Gates

- [x] 0 → 1 in-progress: exact countermodel and source-law comparison fixed
- [x] 1 → 2 fully-proven: dependency-closed paper proof and hostile audit complete
- [x] 2 → 3 formalized: closed unconditional Lean theorem, leaf build and axiom audit
- [ ] 3 → 4 publication-ready: standalone proof and external priority audit

## Countermodel

For integer degree `n>=1` and mass `y>0`, put

```text
F_n(y) = n/y,
J_n(y) = n/y^2.
```

Use sparse strict degrees and their intrinsic parabolic masses

```text
n_k = 2^k,
y_k = n_k^2.
```

Then:

1. `F_n'(y)=-J_n(y)`, `J_n(y)>0`, `F_n(y)->0`, and
   `integral_[a,infinity) J_n(y) dy=F_n(a)`. Thus exact fixed-degree source flow and finite tail
   capital hold.
2. `F_(n+1)-F_n=1/y`, hence
   `(F_(n+1)-F_n)^2 < (3/2)J_(n+1)` for every `n>=1`. This is stronger than needed for current
   adjacent-degree coercivity.
3. Summing all internal connector squares below degree `n` gives
   `E_n(y)=(n-1)/y^2`, and

   ```text
   2J_n(y)=E_n(y)+(n+1)/y^2.
   ```

   Therefore one top source account pays every lower connector and retains explicit strict
   positive reserve, matching strongest scalar consequence of all-degree capital law.
4. Schedule is exactly parabolic, cofinal, and has divergent renormalized source:

   ```text
   y_k=n_k^2,
   y_k^2 J_(n_k)(y_k)=n_k -> infinity.
   ```

5. Nevertheless entry budgets are geometric:

   ```text
   F_(n_k)(y_k)=1/n_k=2^(-k),
   sum_k F_(n_k)(y_k)<infinity.
   ```

6. Even a degree-uniform anti-spike window of fixed multiplicative width does not help. For every
   fixed `c>1`,

   ```text
   integral_[y_k,c*y_k] J_(n_k)(y) dy=(1-1/c)/n_k,
   ```

   which is still geometrically summable.

Every displayed identity is elementary and exact. No numerical experiment, RH premise, zero
computation, or representing measure enters.

## Hostile verdict

`[KILLED]` Current **cofinal source-capital inference**. Cofinality permits exponentially sparse
strict degrees. Pointwise divergence of `y^2 J_n`, finite fixed-degree tail capital, local
degree coercivity, and positive all-degree reserve are jointly compatible with finite total cost
on the canonical quadratic mass scale.

This does **not** falsify Route U's RH-equivalent shifted-Hankel criterion or exclude a new
Xi-specific global identity. It falsifies treating present scalar accounting laws plus generic
anti-spike propagation as sufficient closure.

## No-go closure

- **Exact killing theorem/mechanism:** sparse parabolic reindexing converts degree-`n` entry cost
  `n/y` into `1/n`; choosing `n_k=2^k` makes total cofinal cost finite while renormalized pointwise
  action still diverges.
- **Strongest positive survivor:** any viable Route U completion must prove at least one genuinely
  new source-specific statement: (i) renewal density such as `sum_k 1/n_k=+infinity`, (ii) a
  degree-independent lower bound on integrated contact cost, or (iii) one common cross-degree
  signed prime--Gamma budget that cannot be reused under cofinal reindexing. Fixed multiplicative
  pulse width alone is insufficient.
- **New insight:** missing primitive is not another mass regularity estimate. It is a
  **degree-density/common-budget law**. This moves Route U's open core from `upper accounting` to
  exclusion of exponentially sparse, quadratically synchronized renewal.
- **Status:** dependency-closed paper proof and closed Lean capstone complete. External Jacobi sum
  rules require one fixed infinite Jacobi operator and therefore do not supply this moving
  finite-section degree-density law.

## Lean certificate

`RHTower.routeUSparseParabolicCapitalEscape` is a closed theorem: it has no parameters, premises,
local hypotheses, or added axioms. It packages the exact quadratic sparse schedule, fixed-degree
source law, connector coercivity, positive all-degree reserve, divergent renormalized action, and
summable geometric entry costs.

- Module: `GaloisForLFunctions.RHTower.XiShiftedRouteUSparseParabolicCapitalEscape`
- Direct check: `lake env lean GaloisForLFunctions/RHTower/XiShiftedRouteUSparseParabolicCapitalEscape.lean`
- Targeted final audit: `lake build GaloisForLFunctions.RHTower.XiShiftedRouteUSparseParabolicCapitalEscape`
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` only

## Literature boundary

Killip--Simon positive sum rules control one fixed Jacobi matrix relative to free background under
Hilbert--Schmidt hypotheses. Toda/isomonodromic deformation theory controls one coherent varying
measure, and double-scaling orthogonal-polynomial asymptotics require explicit uniform varying
weights. Route U under false RH supplies only moving finite positive blocks at sparse terminal
frontiers. None of these parent theories supplies strict-degree density or a common finite budget
for that staircase.

## Log

- 2026-08-28 — exact sparse-parabolic escape found after auditing Route U's parabolic horizon,
  source integral law, degree coercivity, all-degree capital, hyperbolic reset, arcsine-vacuum
  renormalization, and normalization--fidelity no-gos.
- 2026-08-28 — closed escape theorem checked directly, built as a leaf module, audited with
  `#print axioms`, and wired into `GaloisForLFunctions.RHTower` without building the umbrella.
