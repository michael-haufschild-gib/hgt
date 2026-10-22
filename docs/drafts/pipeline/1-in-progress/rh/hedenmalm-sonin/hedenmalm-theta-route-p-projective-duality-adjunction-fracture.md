# Route-P projective duality--adjunction fracture

- **ID:** `P-G54`
- **Stage:** `1-in-progress`
- **Type:** exact pre-divisor source comparison / non-scalar naturality gate
- **Status:** `[PAPER-PROVED] [LEAN DIRECT GREEN] [UMBRELLA-WIRED] [NOT RH]`
- **Parent:** `hedenmalm-theta-mobius-prime-cell-squarefree-current.md`
- **Corpus parents:**
  - `../../3-formalized/new_scientific_knowledge/other/projective-prime-weyl-leakage-fock-normal-cone.md`;
  - `../../5-failed/hedenmalm-prime-normal-jordan-grade-separation.md`.

## Conjecture

For a prime `p` and positive squarefree source rate `sigma`, set

```text
z_p(sigma) = (1-sigma) log(p)/2.
```

The marked odds of the projective natural-cone state are then exactly `p^(-sigma)`.  Therefore
the squared projective fidelity of rates `sigma,tau` should be the Route-P squarefree parity Gram.

Residue Weyl adjunction transports the marked point and preserves `sigma`.  Centered
functional-equation duality transports `sigma` to `2-sigma`, hence negates `z_p(sigma)`.  The two
resulting projective vectors should coincide exactly at `sigma=1`.

## Hostile novelty boundary

Projective natural-cone vectors, Weyl transport, their Hellinger Gram, and the scalar Kadison
fracture already exist.  Candidate delta is their exact weld to P-G51's full alternating
Gamma/co-Poisson current at the forced Route-P rates, retaining the two competing transported
vectors before scalarization.  This theorem will classify the missing source-naturality equation;
it will not assert that the equation holds on Xi divisors.

## Result

Let `U_p(sigma)` be the producer natural-cone state at infinity, let `W_p` be residue Weyl
inversion, and let `V_p(sigma)` be the reporter state at zero.  Lean proves

```text
W_p U_p(sigma) = V_p(sigma),
V_p(2-sigma) uses weight -z_p(sigma),
W_p U_p(sigma) = V_p(2-sigma)  iff  sigma=1.             (P-G54a)
```

For arbitrary rates,

```text
|<U_p(sigma),U_p(tau)>|^2
 = (1+p^(-(sigma+tau)/2))^2
   / ((1+p^(-sigma))(1+p^(-tau))).                       (P-G54b)
```

At the forced affine Route-P rates this is the literal squarefree prime-cell Gram.  Consequently

```text
log |<U_p(1+x epsilon),U_p(1+z epsilon)>|^2
 = S_p(1+x epsilon)+S_p(1+z epsilon)
   -2 S_p(1+(x+z)epsilon/2),                              (P-G54c)
```

where `S_p` is P-G51's full alternating primitive Gamma/co-Poisson current.  Thus the current is
not merely numerically equal to a Bernoulli free energy: it is the logarithmic Gram current of the
actual finite projective producer.  Equation `(P-G54a)` is exact non-scalar form of
duality--adjunction fracture.

**Honest boundary.**  `(P-G54a)` proves that transport equality selects centered rate.  It does
not derive transport equality from the completed source; imposing it at a divisor remains the RH
receiver isolated by C21.

## Gate

- [x] exact projective weight and reflected-weight laws
- [x] literal projective fidelity equals Route-P parity Gram
- [x] logarithmic fidelity equals full Gamma/co-Poisson second difference
- [x] Weyl-adjoint and FE-dual vectors coincide iff `sigma=1`
- [ ] final module build, lint, axiom audit

## Lean realization

Module:
`formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaRoutePProjectiveDualityAdjunctionFracture.lean`

Headline declarations:

- `routePProjectiveAdjointState_eq_reporter`;
- `routePProjectiveNaturalWeight_reflection`;
- `routePProjectiveAdjointState_eq_dualState_iff`;
- `routePProjectiveFidelitySq_eq_squarefreePrimeParityGramSq`;
- `routePProjectiveFidelitySq_eq_squarefreeMobiusPrimeCellGramSq`;
- `log_routePProjectiveFidelitySq_eq_squarefreeGammaCoPoissonSecondDifference`.
