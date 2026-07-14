# Theta-Cusp Quadratic Stein--Robertson Law

- **ID:** theta-cusp-quadratic-stein-robertson-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** affine quantum mechanics, generalized Robertson uncertainty, and the half-line quantum bootstrap
- **Statement:** The first radial theta atom obeys the exact half-line Stein covariance and Robertson uncertainty for the quadratic vector field `P(x)=x-x^2/2`; one explicit squared-generator energy certificate implies the buffered upper first-atom moment inequality used by the linear prime--archimedean Hankel consumer.

## Goal

Import a physics value relation that is strictly stronger than ordinary position-moment Hankel positivity and applies directly to the remaining first-atom theorem surface.  The useful output is not a quantum interpretation: it is an exact replacement of the open upper three-even-moment hypothesis by one source-native generator-energy inequality.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorems, targeted and `HTGeometry` umbrella builds green, axiom audit and formal lint green
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Physics transfer

For a half-line amplitude `eta`, density `rho=eta^2`, and logarithmic derivative

```text
eta' = -W eta,
```

let `P` be a differentiable vector field and define the symmetric first-order score

```text
S_P = P W - P'/2.
```

The identity `rho'=-2W rho` and half-line integration by parts give

```text
integral f S_P rho = (1/2) integral f' P rho.            (S)
```

This is the static integral form of the generalized Robertson commutator.  Cauchy--Schwarz turns `(S)` into the corresponding uncertainty bound.

## Theta specialization

Take the exact `k=1,n=1` radial theta state

```text
eta(x)=x*chi_1(x),
W(x)=B_1(x)-1/x,
J_r=integral x^r eta(x)^2 dx,
```

and the quadratic field

```text
P(x)=x-x^2/2.
```

Its score has the nonsingular source expression

```text
S_P(x)=(x-x^2/2) B_1(x)+x-3/2.
```

With `f(x)=J_0*x^2-J_2`, define

```text
C = integral (x^2-x^3/2) eta^2,
E = integral S_P^2 eta^2.
```

Then `(S)` and Cauchy--Schwarz give the exact value relation

```text
(J_0*C)^2 <= (J_0^2*J_4-J_0*J_2^2)*E.                  (R)
```

The energy `E` is finite and strictly positive: the Born--Witten weight floor bounds the rational superpotential by the Morse scale, after which the energy density is dominated by a finite sum of already-integrable polynomial--Gaussian atoms.  Therefore the scalar source certificate

```text
(14*(3005/2997)^2-9)*J_2^2*E <= 9*J_0*C^2              (Q)
```

implies

```text
14*((3005/2997)*J_2)^2 <= 9*J_0*J_4,                   (H)
```

which is exactly the open upper moment hypothesis for the first radial atom.

## Proof

**[PROVED HERE]** Differentiating `P rho` gives

```text
(P rho)' = P' rho - 2 P W rho = -2 S_P rho.
```

If the boundary current `f P rho` vanishes at zero and infinity, integration by parts yields `(S)`.  For the theta radial state, the Dirichlet value at zero and the already-proved polynomial-Gaussian decay at infinity verify both boundary terms.  Substituting `f=J_0*x^2-J_2` yields

```text
integral f S_P rho = J_0*C.
```

Its squared norm is

```text
integral f^2 rho = J_0^2*J_4-J_0*J_2^2.
```

Integral Cauchy--Schwarz proves `(R)`.  Cancelling the positive factors `J_0` and `E` between `(R)` and `(Q)` gives `(H)` by elementary algebra.

## Lean certificate and corpus applications

- `HTGeometry/HalfLineSteinRobertson.lean` formalizes the reusable covariance identity and square-integrability form of integral Cauchy--Schwarz.
- `PrimeArchThetaQuadraticSteinRobertson.lean` formalizes arbitrary radial power moments, the Morse-scale energy majorant, unconditional generator-energy integrability and positivity, the quadratic field, score, coupling, both boundary limits, the exact covariance, the centered norm, and `(R)`.
- `thetaCusp_firstRadial_upper_of_quadraticSteinEnergyCertificate` proves `(Q) -> (H)`.
- `forall_primeArchSourceTraceHankel_linear_nonneg_of_quadraticSteinEnergy` feeds `(H)` directly into the existing linear prime--archimedean Hankel consumer.

The pure dilation choice `P=x` was rejected: its required energy cap is numerically false.  The quadratic field is not cosmetic optimization; it is the first tested low-degree generator whose Robertson value clears the required buffered variance threshold.

## Remaining open core

`[CONJECTURE]` Prove `(Q)` for the explicit first radial theta state.  High-precision quadrature pre-certifies about `0.749%` margin.  That computation selects the certificate but is not part of the Lean proof.

## Physics references

- Klauder, *A Simple Factor in Canonical Quantization yields Affine Quantization Even for Quantum Gravity*, arXiv:2108.04083.
- Han--Hartnoll--Kruthoff, *Bootstrapping Matrix Quantum Mechanics*, arXiv:2004.10212.
- Berenstein--Hulsey, *Anomalous Bootstrap on the Half Line*, arXiv:2206.01765.

## Log

- 2026-07-14 — exact Stein covariance, quadratic Robertson inequality, positivity facts, scalar energy reduction, and direct Hankel consumer formalized.

## Local-virial curvature form

`[PROVED IN LEAN]` The reusable half-line module now contains
`hasDerivAt_halfLineSteinVirialCurrent` and
`halfLineSteinScore_sq_mul_eq_curvature_sub_deriv`.  The theta specialization proves:

- exact cancellation of the virial current into polynomial--Gaussian theta atoms;
- zero current at the Dirichlet endpoint and at infinity;
- integrability of the curvature form through an explicit polynomial--Gaussian majorant;
- `thetaCuspFirstRadialQuadraticSteinEnergy_eq_virialEnergy`;
- positivity of the new virial energy;
- equivalence of the score and curvature energy certificates; and
- a direct curvature-certificate input to the existing linear Hankel consumer.

Thus the remaining open certificate is no longer tied to a squared rational superpotential.  It is
an inequality for a positive curvature/field-gradient density, with the exact radial centrifugal
term retained.

Additional primary physics reference: C. V. Sukumar, *Generalised Virial theorems in Classical and
Quantum Physics*, arXiv:1410.5592.

- 2026-07-14 — integrated local-virial identity and curvature-energy Hankel interface formalized.
