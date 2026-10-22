# Suzuki Volterra Cartesian phase defect — Lean certificate

- **ID:** `suzuki-volterra-cartesian-phase-defect-formalized`
- **Stage:** 3-formalized
- **Type:** UNCONDITIONAL LEAN THEOREM / RH FRONTIER CONNECTOR
- **Scientific status:** `[LEAN-PROVED] [SOURCE-REPRESENTATION] [NOT RH]`
- **Paper proof:**
  `./suzuki-volterra-cartesian-phase-defect.md`
- **Lean:** `GaloisForLFunctions.RHTower.Suzuki.SuzukiVolterraCartesianPhaseDefect`
- **RH used:** no
- **Computation used:** no

## Formalized exact content

Lean proves:

1. Xi-real Cartesian response identity

   ```text
   -i(right_g-lambda right_r)
    =[(phase_g-lambda phase_r)-i(sym_g-lambda sym_r)]/2;
   ```

2. symmetric-coordinate blindness: two causal responses with same symmetric coordinate differ by
   exactly half their phase difference;
3. relative phase homogenization on `A u_lambda-lambda u_lambda=e`:

   ```text
   phase_g(u_lambda)-lambda phase_r(u_lambda)
    =(phase_g-phase_r*A)(u_lambda)+phase_r(e);
   ```

4. full two-resolvent projective chord of the Cartesian response, including fixed symmetric
   forcing and Neumann homogeneous coordinate;
5. rank-one Neumann mass/first-moment law and exact normalized holonomy numerator;
6. complex extension of existing real marked affine-secant tensor and exact specialization of
   weighted affine sewing to relative Volterra phase;
7. a direct connector: an analytic upper-half-plane Euler-defect source germ built from these
   actual Volterra boundary responses implies `RiemannHypothesis` by existing pole tomography.

Main declarations:

```text
suzukiXiRealRightVolterraResponse_eq_cartesian
suzukiXiRealCartesianResponse_sub_eq_phaseHalf
suzukiRelativeVolterraPhaseObservation
suzukiShiftedVolterraPhase_eq_relative_homogeneous
suzukiXiRealRightVolterraResponse_eq_relativePhaseHomogeneous
suzukiXiRealRightVolterraProjectiveChord_twoResolvents
suzukiNeumannVolterraSkewMomentResponse_of_zeroMass
suzukiNeumannXiRealEvenTriangle_eq_projectiveHolonomyNumerator
suzukiComplexProjectiveAffineSecantTensor_ofReal
suzukiShiftedVolterraPhase_affineSecant_twoResolvents
riemannHypothesis_of_suzukiVolterraPhaseEulerDefect_source_germ_weld
```

## Boundary of formalization

Lean certificate formalizes exact source algebra and RH implication.  Analytic Fubini realization
of `T_R` as Fourier observation of `V_k`, adjoint identity `V_k+V_k^*=C_k`, parity split, and
prime--Gamma commutator `H_g=-i[X,Q_g]` remain dependency-closed paper theorems because repository
does not yet contain Suzuki's continuous integral operators.

Open RH-bearing theorem is not hidden in this card: construct analytic source Green/CD germ for
marked affine-secant tensor built from relative phase operator `H_g-H_r*A`.  That is precisely
premise consumed by final Lean connector.

## Verification

- [x] direct `lake env lean` check
- [x] final targeted module build
- [x] axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- [x] formal lint run; global gate remains red only because unrelated owned module
  `GaloisForLFunctions.RHTower.MobiusLaplaceAdditiveTriangle` is unreachable from umbrella
