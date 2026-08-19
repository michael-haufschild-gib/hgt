# Gamma-completed zero jets of literal Burnol co-Poisson windows

- **ID:** burnol-completed-zero-jets
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta function*, Theorem 2.2 and §3; literal co-Poisson subwindow source
- **Statement:** Every positive logarithmic co-Poisson subwindow has, at an actual Xi divisor, zero Gamma-completed Mellin jets below the exact zeta multiplicity and a nonzero leading jet.

## Exact theorem

For `L > 0` and `rho : XiDivisorSupport`, define the literal Sonine evaluation

```text
F_L(w) = M_gamma(coPoissonSubWindow [exp(-L), 1])(w).
```

The formal module proves

```text
j < ord_rho(zeta)  -> iteratedDeriv j F_L rho = 0,
iteratedDeriv (ord_rho(zeta)) F_L rho != 0.
```

It also proves analyticity of the archimedean completion on the right half-plane.  The argument
does not differentiate an improper integral: it transports the already proved literal
co-Poisson identity through equality on the open strip and the locality of iterated derivatives.

## Lean artifact

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonCompletedZeroJets.lean
```

Principal declarations:

- `iteratedDeriv_burnolCoPoissonExpWindowCompletedEvaluation_eq_zero_of_lt`
- `iteratedDeriv_burnolCoPoissonExpWindowCompletedEvaluation_ne_zero`

## Boundary

This closes an actual source-side multiplicity/jet producer.  It does **not** formalize Burnol’s
Theorems 3.1–3.3: no theorem here proves bounded derivative evaluators on all `L_a`, the closed
span/complement equality `Y_aᗮ = P_a`, aperture-dependent completeness/minimality, projection to
`K_a`, or the two-jet deletion at `a = 1`.  Those are distinct Hilbert/Hardy-space steps and must
not be inferred from the subwindow result.

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/BurnolCoPoissonCompletedZeroJets.lean
lake build GaloisForLFunctions.RHTower.BurnolCoPoissonCompletedZeroJets
```

Both were run after the module was wired into `RHTower.lean`; no umbrella build was run.
