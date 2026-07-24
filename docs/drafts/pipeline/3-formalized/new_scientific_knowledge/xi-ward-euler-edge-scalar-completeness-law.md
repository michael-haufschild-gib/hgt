# Xi Ward Euler-edge scalar completeness law

- **ID:** `xi-ward-euler-edge-scalar-completeness-law`
- **Stage:** 3-formalized
- **Type:** `[THEOREM] [CCM ENDPOINT REDUCTION]`
- **Scientific status:** `[PAPER PROOF COMPLETE] [LEAN FORMALIZED] [NOT RH]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusXiWardEulerEdgeCompleteness.lean`
- **Parent:** `../3-formalized/new_scientific_knowledge/xi-ward-zero-adapted-four-unit-boundary-charge-law.md`

For a strict-right centered Xi zero `lambda=a+ib`, the previous adapted witness used
`w=conj(lambda)`.  Move it horizontally to the fixed Euler edge

```text
w=1/2-ib.
```

The matching Schwarz-pair summand has real part `2/(a+1/2)`, every other paired summand has
positive real part, and `0<a<1/2`.  Therefore

```text
Re r(w)>2/(a+1/2)>2,
|r(w)|^2>4=4G(w,w).
```

Consequently

```text
RH
<->
forall t:R, |continuedXiAntiCausalWardResponse(1/2+i*t)|^2 <= 4.
```

The actual augmented Gram has the parallel fixed-line law

```text
RH
<->
for every finite packet P on Re(w)=1/2,
  W_P=[[G_P,r_P],[r_P*,4]] is positive semidefinite.
```

This places the complete CCM Ward obstruction on one fixed vertical source line. It removes
interior packet geometry from the remaining source problem but does not prove the scalar source
bound.

## Gates

- [x] corpus audit
- [x] symbolic feasibility proof
- [x] Lean theorem
- [x] fixed-line augmented-Gram law
- [x] umbrella wiring
- [x] direct `lake env lean` check
- [x] targeted `lake build GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardEulerEdgeCompleteness`
- [x] axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- [x] formal lint checked; repository lint stops on unrelated pre-existing unreachable
  `GaloisForLFunctions.RHTower.XiHedenmalmKummerRootRH`
- [ ] RH
