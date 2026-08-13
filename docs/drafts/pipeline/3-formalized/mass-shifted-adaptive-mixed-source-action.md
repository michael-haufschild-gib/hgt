# Mass-shifted adaptive mixed/completed source action

- **ID:** `mass-shifted-adaptive-mixed-source-action`
- **Stage:** 3-formalized
- **Route:** mass-shifted spectral face, §9.3 exact open core
- **Type:** THEOREM / degree--mass source law
- **Scientific status:** `[PROVED HERE] [LEAN-PROVED] [CORPUS-NOVEL] [EXTERNAL NOVELTY UNVERIFIED] [NOT RH]`
- **Depends on:** literal adaptive mixed completed arithmetic source, cumulative Jacobi-flux law,
  projective arithmetic surplus

## Frozen claim

Let `S_n(w)` be literal adaptive mixed rational--Gamma-minus-von-Mangoldt source formed from
current canonical admission `P_n^sharp`, let `h_n` be admitted norm, `alpha_n` current Jacobi
diagonal, and `F_n` cumulative Jacobi flux.  The drift-removed source

```text
J_n = S_n / h_n - alpha_n * F_n - 2*n*alpha_n^2
```

is exact positive mass action.  It is not an orientation character or fixed reporter:

```text
J_n = cumulativeJacobiDissipation_n > 0,
F_n' = -J_n.
```

Writing `c_n=2*n+1`, projective surplus `Pi_n`, and `U_n=F_n/c_n`, same literal producer obeys

```text
Pi_n = c_n*J_n - F_n^2 > 0,
U_n' = -U_n^2 - Pi_n/c_n^2.
```

Adjacent degree and mass transport form exact plaquette:

```text
F_(n+1)-F_n = alpha_n+alpha_(n+1),
(F_(n+1)-F_n)' = J_n-J_(n+1).
```

## Falsifiers

- Source must be literal adaptive mixed/completed `P^sharp` aggregate formed before reflection.
- Drift subtraction must be endogenous to current admission.
- Result must identify exact positive action and exact derivative, not only sign/orientation.
- Degree renewal must use moving source action at both grades, not fixed coefficients.
- No RH premise, computation, representing measure, or added axiom.

## Conjecture -> proof/fail loop

1. **Fixed-mass source transgression supplies missing curvature.** Failed novelty and mechanism
   audit: corpus already proves transgression is exact at fixed mass; repeating it is theatre.
2. **Full newborn determinant generating series is source aggregate.** Failed at current proof
   burden: only first live coefficient is linear in Padé defect; higher determinant coefficients
   contain nonlinear cofactor interactions and do not give immediate common budget.
3. **Strict Riccati inequality is enough.** Failed: inequality hides literal arithmetic term and
   can be reproduced on unconditional far-right positive schedules.
4. **Projective surplus is exact nonlinear defect of literal adaptive source action.** Survives.
   Existing source identity and cumulative-flux derivative share same dissipation. Eliminating it
   gives exact source action and normalized Riccati law.
5. **Degree edge closes same action.** Survives locally. Jacobi trace renewal gives adjacent
   diagonal edge; differentiating fluxes gives exact action difference.
6. **Local plaquette proves RH.** Failed. Connector `alpha_n+alpha_(n+1)` has no common cofinal
   boundary/tightness estimate; action can migrate with degree.

## Dependency-closed proof

Existing literal source theorem gives

```text
S_n/h_n = 2 * adaptiveOrthoJacobiEnergy_n.
```

Exact energy decomposition gives

```text
2 * adaptiveOrthoJacobiEnergy_n
  = cumulativeJacobiDissipation_n
    + alpha_n*F_n + 2*n*alpha_n^2.
```

Subtract endogenous drift to obtain `J_n=D_n`. Finite positive admission makes `D_n>0`.
Cumulative flux law gives `F_n'=-D_n`, hence `F_n'=-J_n`.

Definition of literal projective surplus expands to `Pi_n=c_n*J_n-F_n^2`. Divide by `c_n^2`
and use `U_n=F_n/c_n` to get

```text
U_n' = -U_n^2-Pi_n/c_n^2.
```

Finally finite trace formula

```text
F_n = 2*sum_{j<n} alpha_j+alpha_n
```

implies `F_(n+1)-F_n=alpha_n+alpha_(n+1)`. Subtract two exact source-action flow laws to obtain
mass derivative `J_n-J_(n+1)`.

## Lean

- `formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionAdaptiveMixedSourceAction.lean`
- wired into `formal/GaloisForLFunctions/RHTower.lean`
- direct `lake env lean` check: PASS
- targeted module build: PASS (`11789/11789`)
- thirteen-capstone axiom audit: `propext`, `Classical.choice`, `Quot.sound` only
- no computation, RH premise, representing measure, infinite extension, or added axiom

## Sharp boundary

Missing producer is closed at finite degree: literal completed source is exact positive nonlinear
mass action, and degree renewal has exact plaquette. Missing global theorem is now source-action
properness: control adjacent diagonal connector across cofinal degree--mass frontiers strongly
enough that forced native contact weight spends one common finite capital. Neither pointwise
positivity nor fixed-degree Riccati action supplies this synchronization; unconditional far-right
positive schedules obey same local laws.
