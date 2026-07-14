# Theta-cusp Morse/Fisher hypervirial reduction

- **ID:** `theta-cusp-morse-fisher-hypervirial-reduction`
- **Stage:** 3-formalized
- **Type:** `[PROVEN] [PHYSICS VALUE BRIDGE] [LEAN] [DIRECT CONSUMER]`
- **Lean source:** `PrimeArchThetaQuadraticVirialMorseReduction.lean`
- **Statement:** The first-radial quadratic virial energy is an exact polynomial source value plus
  a polynomial Morse Gibbs value and one positive Fisher residual; the residual has a sharp
  endpoint bound yielding a finite-moment sufficient certificate for the existing Hankel gate.

## Claim

Put

```text
t = thetaCuspMorseScale 1,
q = t-3/2,
psi^2 = thetaCuspLiouvilleGibbsAtom 1,
P = x-x^2/2,
F = x^2*P^2.
```

The Born--Witten state is the observable reweighting `chi^2=4*q*psi^2`.  The shifted Morse density

```text
g=(q+1)*psi^2
```

obeys the exact hypervirial value relation

```text
g'=(5/2)*g-2*t*q*psi^2.                                (H)
```

The endpoint current `F*g` vanishes at zero and infinity.  Integrating `(H)` therefore gives

```text
integral 4*F*t*q*psi^2
  = integral (5*F+2*F')*(q+1)*psi^2.                   (V)
```

Substitution into the already-formalized local-virial law yields

```text
E_virial = E_source + E_gibbs + 6*R_F,
R_F = integral F*(t/q)*psi^2 >= 0.                     (D)
```

Since `t>=pi` and `q=t-3/2`, cross multiplication gives the sharp endpoint estimate

```text
t/q <= c := pi/(pi-3/2).                               (B)
```

Combining `(D)` and `(B)` gives `E_virial <= U`, where, with
`R_m=thetaCuspBornWittenRadialPowerMoment m 1 1` and
`L_m=thetaCuspLiouvilleGibbsMoment m 1`, Lean proves the literal finite-moment identity

```text
U = 3*R_0/4 + R_1 - 7*R_2/8 - R_3/2 + 5*R_4/16
    + 8*L_3 + (6*c-5)*L_4 - (2+6*c)*L_5 + (5/4+3*c/2)*L_6.
```

## Direct corpus application

`ThetaCuspFirstRadialQuadraticMorseMomentUpperCertificate` is the old source-specific energy
certificate with `E_virial` replaced by the explicit upper value `U`.  The theorem

```text
forall_primeArchSourceTraceHankel_linear_nonneg_of_morseMomentUpper
```

passes it directly to the existing linear prime--archimedean Hankel consumer.  Thus the sufficient
proof surface contains only already-defined radial power moments, Liouville Gibbs moments, and the
fixed endpoint constant `c`.  It has no rational superpotential, inverse observable, or additional
integrability hypothesis.

This is a useful bridge, not a proof of the remaining finite inequality and not a claim of new
scientific knowledge.

## Physics provenance

- C. V. Sukumar, *Generalised Virial theorems in Classical and Quantum Physics*,
  <https://arxiv.org/abs/1410.5592>.
- F. Cooper, A. Khare, and U. Sukhatme, *Supersymmetry and Quantum Mechanics*,
  <https://arxiv.org/abs/hep-th/9405029>.
- C. Quesne, B. Bagchi, A. Banerjee, and V. M. Tkachuk, *Hamiltonians with position-dependent
  mass, deformations and supersymmetry*, <https://arxiv.org/abs/quant-ph/0512046>.
- D. Berenstein and G. Hulsey, *Anomalous Bootstrap on the Half Line*,
  <https://arxiv.org/abs/2206.01765>.

The literature supplies the generalized hypervirial, supersymmetric ground-state transform, and
deformed first-order generator mechanisms.  The theta-specific identities `(H)`--`(B)`, the finite
value `U`, and its Hankel consumer are proved directly in Lean.

## Formalization

Principal declarations:

- `hasDerivAt_thetaCuspFirstAtomMorseShiftDensity`
- `thetaCuspFirstAtom_morseScale_div_weight_le_pi`
- `thetaCuspFirstRadialQuadraticVirial_morseFisher_decomposition`
- `integral_four_morseScale_weight_eq_hypervirial`
- `thetaCuspFirstRadialQuadraticVirialEnergy_eq_morseReducedEnergy`
- `thetaCuspFirstRadialQuadraticMorseFisherResidual_nonneg`
- `thetaCuspFirstRadialQuadraticMorseFisherResidual_le_endpoint`
- `thetaCuspFirstRadialQuadraticVirialEnergy_le_morseMomentUpperEnergy`
- `thetaCuspFirstRadialQuadraticMorseMomentUpperEnergy_eq_finiteMoments`
- `thetaCusp_quadraticVirialEnergyCertificate_of_morseMomentUpper`
- `thetaCusp_firstRadial_upper_of_morseMomentUpper`
- `forall_primeArchSourceTraceHankel_linear_nonneg_of_morseMomentUpper`

## Gates

- [x] existing Morse, hypervirial, local-virial, and failed-route corpus checked
- [x] primary physics mechanisms identified
- [x] exact theta observable reweighting differentiated
- [x] half-line current and endpoint limits proved
- [x] Fisher residual isolated and proved nonnegative
- [x] sharp endpoint multiplier proved
- [x] upper value converted to a literal finite moment combination
- [x] sufficient finite-moment certificate connected to the existing Hankel consumer
- [ ] prove the finite-moment certificate
- [ ] RH

## Log

- 2026-07-14 — hypervirial reweighting, Fisher bound, finite-moment value, and Hankel interface
  formalized.
