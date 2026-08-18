# Source-horizontal BV/Krein selected-residue third-jet descent

- **ID:** P-G212
- **Stage:** 3-formalized
- **Type:** LEAN-PROVED / NOVELTY UNVERIFIED
- **Source:** Wold BV Green--Stokes conservation + CCM/Gamma Schwarz residue + shared Julia orbit

## Exact claim

For terminal prime clock `N`, define the genuine BV endpoint defect

```text
E_N(u) = sinh(u) - sourceHorizontalWoldBVGreenStokesInteriorCurrent(N,u)
```

and its normalized cubic charge

```text
epsilon_N = - sourceHorizontalWoldResidualPrimitiveCubicCoefficient(N)
              / xiMassNthPrimeLogHeight(N)^3.
```

The first claim is the literal source identity

```text
iteratedDeriv 3 E_N 0 = epsilon_N,
epsilon_N -> 2/3.
```

For one retained strict-right Xi copy `q`, coefficient `c`, and the existing complex CCM/Gamma
first landing `F_q,N(v)`, put

```text
A_c,q,N(v) = 4 ||c||^2 * (-F_q,N(v)) / (4 Re(q-1/2)^3),
G_c,N      = 8 ||c||^2 epsilon_N.
```

Then selected residue at the Schwarz-mate pole satisfies

```text
A_c,q,N(v) -> G_c,N.
```

Consequently the pre-divisor signed block

```text
K_c,q,N(v) = diag(A_c,q,N(v), -G_c,N)
```

lands in `diag(G_c,N,-G_c,N)`, whose signed trace is zero.  Applying the fixed Krein fundamental
symmetry `J=diag(1,-1)` only after the selected landing gives `diag(G_c,N,G_c,N)`, positive
semidefinite whenever `epsilon_N >= 0` and strictly positive in both channels for `c != 0` once
`N` is cofinal.  The positive corner is exactly the existing finite literal Wold--Julia orbit
response, not a fitted scalar.

## Frontier and hostile audit

- `[CORPUS]` `sourceHorizontalWoldBVGreenStokes_finite_conservation` identifies the full
  coefficient-faithful Wold profile with actual prime-labelled BV boundaries.
- `[CORPUS]` `tendsto_frankensteinCCMGammaSchwarzCenteredCubicFirstLanding` gives the selected
  complex CCM/Gamma residue with analytic multiplicity retained per Xi copy.
- `[CORPUS]` `sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse` is the literal pivot-resistant
  four-orientation orbit current.
- `[CORPUS]` ordinary pre-divisor Loewner order and positive Gram conservation are equivalent to
  RH, so positivity cannot be imposed before the selected fibre.
- `[LITERATURE]` [generalized Schur--Nevanlinna/Pontryagin realization theory](https://link.springer.com/article/10.1007/s00020-020-02600-w)
  supplies abstract J-inner dilations but no arithmetic identification of this BV third jet with a
  Xi residue.
- `[LITERATURE]` [Connes--Consani](https://arxiv.org/abs/2006.13771) obtain archimedean Sonin/Weil
  positivity; their semilocal/global extension remains the RH-bearing step.
- `[FALSIFIED]` Weighting the orbit by the endpoint defect value has wrong normalization.  Literal
  orbit uses the third neutral jet; the defect value starts with `u^3/9`, while its third jet is
  `2/3`.
- `[PAPER-PROVED]` P-G212 replaces value transport by third-jet transport.  It is unconditional and
  does not assert primitive-budget domination.

## Paper proof obligations

1. Rewrite `E_N` using finite BV conservation and the exact prime-clock residual deformation.
2. Apply the cubic chain rule and the existing literal third-jet theorem for the residual primitive.
3. Negate the normalized cubic coefficient limit to obtain `epsilon_N -> 2/3` and eventual
   positivity.
4. Use `primeDepthBVWoldXiCenteredRate(q)=2 Re(q-1/2)` to cancel the conormal cubic denominator
   exactly, proving the finite identity
   `sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse(c,q,N)=G_c,N`.
5. Transport the complex first landing entrywise through the selected residue and prove the
   signed/positive matrix identities.

All five obligations close using the named corpus theorems and finite-dimensional matrix algebra.
No source order, RH premise, simplicity premise, or unproved analytic interchange is used.

## Lean status

Formalized unconditionally in
`GaloisForLFunctions.RHTower.SourceHorizontalWoldBVKreinSelectedResidueThirdJetDescent`.
Main declarations:

- `iteratedDeriv_sourceHorizontalWoldBVGreenStokesEndpointDefect_three`
- `sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse_eq_endpointThirdJet`
- `tendsto_frankensteinCCMGammaWoldBVKreinComplexFirstLanding`
- `tendsto_frankensteinCCMGammaWoldBVKreinSignedSourceBlock`
- `frankensteinCCMGammaWoldBVKreinSignedSourceBlock_not_posSemidef`
- `sourceHorizontalWoldBVKreinSignedLanding_not_posSemidef`
- `sourceHorizontalWoldBVKreinPhysicalLanding_posSemidef_iff`
- `sourceHorizontalWoldBVKreinPhysicalLanding_posDef`
- `eventually_frankensteinCCMGammaWoldBVKrein_selectedResidue_phaseChange`

Verification:

- direct `lake env lean` check passed;
- exact leaf `lake build` passed;
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`;
- module contains no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration;
- wired into the `RHTower` umbrella without running an umbrella build.

## Exact limitation

This descent supplies the requested non-Loewner Krein-to-positive fibre rotation.  It does not
bound `G_c,N` by primitive Euler budget: the existing firewall proves that additional comparison
equivalent to RH.  New mathematical information is sharper: at every finite clock the literal
orbit current is exactly the third jet of the genuine BV endpoint defect, independently of the
off-line horizontal distance after conormal normalization.
