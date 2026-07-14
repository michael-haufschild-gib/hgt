# Theta-Cusp Quadratic Stein--Robertson Certificate

- **ID:** theta-cusp-quadratic-stein-robertson-certificate
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** affine quantum mechanics, generalized Robertson uncertainty, and the half-line quantum bootstrap
- **Statement:** The radial first theta atom obeys an exact Stein--Robertson covariance for every admissible vector field; the quadratic field `P(x)=x-x^2/2` reduces the open upper first-atom moment inequality to one explicit squared-generator energy certificate.

## Goal

Replace the open three-even-moment hypothesis for the `k=1,n=1` radial theta state by a source-native quantum-generator norm inequality with a verified positive numerical margin.  The transfer must prove the uncertainty/covariance relation itself and wire the surviving scalar certificate into the existing first-atom Hankel consumer; it must not assume the original moment inequality under a new name.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Let `eta=x*chi_1`, `rho=eta^2`, and `W=B_1-1/x`, so `eta'=-W eta` and `rho'=-2W rho`.  For a differentiable real vector field `P`, define the symmetric quantum-generator score

```text
S_P = P W - P'/2.
```

Half-line integration by parts gives the exact Stein/Robertson relation

```text
integral f S_P rho = (1/2) integral f' P rho
```

whenever the boundary current `f P rho` vanishes.  With `f=x^2-J_1/J_0`, Cauchy--Schwarz gives

```text
J_0 (integral x P rho)^2
  <= (J_0 J_2-J_1^2) (integral S_P^2 rho).
```

The pure dilation field `P=x` is almost sharp but its required energy cap is false.  The quadratic field

```text
P(x)=x-x^2/2
```

has score `S_P=(x-x^2/2)B_1+x-3/2`, contains no half-line `1/x` singularity, and numerically gives a Robertson lower bound about `1.00749` times the required buffered variance threshold.  The remaining scalar certificate is therefore

```text
(14*(3005/2997)^2-9) * J_1^2 * integral S_P^2 rho
  <= 9 * J_0 * (integral (x^2-x^3/2) rho)^2.
```

Together with the exact Stein--Robertson inequality and strict positivity of the generator energy, this implies

```text
14*((3005/2997)*J_1)^2 <= 9*J_0*J_2.
```

## Status

- `[FALSIFIED]` The one-generator affine cap for `P=x` is slightly too strong: the source has `K/J_0 approximately 1.78720`, while the required cap is approximately `1.77345`.
- `[PROVED IN LEAN]` The quadratic generator energy is automatically integrable and strictly positive; the certificate carries no finiteness hypothesis.
- `[CONJECTURE]` The displayed quadratic energy certificate holds for the exact first radial atom.  High-precision quadrature gives about `0.749%` margin; this selects the certificate but is not its proof.
- `[OPEN CORE]` Prove the quadratic energy certificate by rigorous source bounds or an exact mixed Hamiltonian value relation.

The covariance, Robertson inequality, strict mass and energy positivity, implication from the scalar certificate to the buffered upper moment inequality, and direct linear-Hankel consumer are formalized in `PrimeArchThetaQuadraticSteinRobertson.lean`.  Their Stage-3 card is `theta-cusp-quadratic-stein-robertson-law.md`.  Only the displayed source-specific scalar energy estimate remains open here.

## Physics provenance

The positive-coordinate commutator `[Q,D]=i hbar Q` is the affine-quantization input.  The use of polynomial test operators and positive mixed moment/Gram matrices is the quantum-bootstrap input.  The theta-specific radial state, optimized field, covariance, and scalar certificate are derived in this project.

Primary sources: Klauder, *A Simple Factor in Canonical Quantization yields Affine Quantization Even for Quantum Gravity*, arXiv:2108.04083; Han--Hartnoll--Kruthoff, *Bootstrapping Matrix Quantum Mechanics*, arXiv:2004.10212; Berenstein--Hulsey, *Anomalous Bootstrap on the Half Line*, arXiv:2206.01765.

## Log

- 2026-07-14 — created after the pure dilation cap was falsified and the quadratic vector field survived the direct first-atom numerical gate.

## 2026-07-14 local-virial reduction

`[PROVED IN LEAN]` The generalized quantum virial identity applies directly to the selected
quadratic generator.  For any zero-mode density `rho'=-2*W*rho`, the local current obeys

```text
S_P^2*rho
  = (P^2*W'/2 + (P')^2/4)*rho - (P^2*W*rho)'/2.
```

For the first radial theta state, both endpoint values of `P^2*W*rho` vanish.  Hence

```text
thetaCuspFirstRadialQuadraticSteinEnergy
  = thetaCuspFirstRadialQuadraticVirialEnergy
  = integral (P^2*thetaCuspBornWittenRadialCurvature 1 1/2
      + (P')^2/4) * rho.
```

The rational superpotential square has disappeared.  Its current is exactly a linear combination
of two polynomial--Gaussian theta atoms, while the remaining radial curvature is positive and has
the formal upper envelope

```text
thetaCuspBornWittenRadialCurvature 1 1 x
  <= 5*thetaCuspMorseScale 1 x + 1/x^2,   x>0.
```

The open scalar certificate is therefore equivalently
`ThetaCuspFirstRadialQuadraticVirialEnergyCertificate`.  This is a real simplification of the open
core: future bounds may work linearly with the already-formalized curvature and centrifugal term,
rather than estimating the square of a rational logarithmic derivative.  It does not by itself
prove the certificate; the numerical margin remains only a pre-certification.

## 2026-07-14 Morse/Fisher hypervirial reduction

`[PROVED IN LEAN]` Write `t=thetaCuspMorseScale 1`, `q=t-3/2`,
`psi^2=thetaCuspLiouvilleGibbsAtom 1`, and

```text
F=x^2*P^2=x^4-x^5+x^6/4.
```

The source amplitude is the square-root reweighting `chi^2=4*q*psi^2`.  The shifted Morse density
`g=(q+1)*psi^2` has the exact derivative

```text
g'=(5/2)*g-2*t*q*psi^2.
```

Since `F*g` vanishes at both half-line endpoints, hypervirial integration removes the full
`t*q*psi^2` insertion.  The virial energy becomes a finite polynomial source value, a finite
polynomial Morse Gibbs value, and one positive Fisher residual

```text
R_F = integral F*(t/q)*psi^2.
```

The multiplier has the sharp endpoint bound

```text
t/q <= pi/(pi-3/2),   x>=0.
```

Let `c=pi/(pi-3/2)`, `R_m=thetaCuspBornWittenRadialPowerMoment m 1 1`, and
`L_m=thetaCuspLiouvilleGibbsMoment m 1`.  Lean proves that the exact virial energy is bounded by
the literal finite-moment value

```text
U = 3*R_0/4 + R_1 - 7*R_2/8 - R_3/2 + 5*R_4/16
    + 8*L_3 + (6*c-5)*L_4 - (2+6*c)*L_5 + (5/4+3*c/2)*L_6.
```

`ThetaCuspFirstRadialQuadraticMorseMomentUpperCertificate` replaces the open energy by `U`, and
`forall_primeArchSourceTraceHankel_linear_nonneg_of_morseMomentUpper` feeds that certificate
directly into the existing prime--archimedean Hankel consumer.  This strictly changes the proof
surface: no rational superpotential, rational curvature, inverse observable, or analytic
integrability hypothesis remains in the sufficient certificate.  The finite inequality itself is
still `[OPEN CORE]`; this reduction does not claim it has been proved.

Primary physics sources: C. V. Sukumar, *Generalised Virial theorems in Classical and Quantum
Physics*, arXiv:1410.5592; F. Cooper, A. Khare, and U. Sukhatme, *Supersymmetry and Quantum
Mechanics*, arXiv:hep-th/9405029; C. Quesne et al., *Hamiltonians with position-dependent mass,
deformations and supersymmetry*, arXiv:quant-ph/0512046.  Boundary-current control remains aligned
with Berenstein--Hulsey, *Anomalous Bootstrap on the Half Line*, arXiv:2206.01765.
