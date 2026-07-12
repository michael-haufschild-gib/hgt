# Quadratic scale-spectrum criterion for RH

- **ID:** `quadratic-scale-spectral-rh-criterion`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM (paper + Lean), BRIDGE
- **Statement:** Every zero `rho` of the completed xi function has real quadratic scale energy
  `-rho(rho-1)` if and only if the Riemann hypothesis holds.

## Theorem

Put

```text
lambda(w) = -w(w-1) = 1/4 - (w-1/2)^2.
```

Then

```text
(forall rho, xi(rho)=0 -> Im(lambda(rho))=0) <-> RH.
```

## Proof `[PROVED]`

Write `rho=a+ib`.  Direct expansion gives

```text
Im(-rho(rho-1)) = b(1-2a).
```

Under RH, every xi zero has `a=1/2`, so the energy is real.  Conversely, every xi zero lies
unconditionally in `0<a<1`, and xi has no real zero in that interval.  Hence `b` is nonzero at a
xi zero.  Reality of the energy therefore forces `1-2a=0`, so `a=1/2`.

## Source interpretation

For `D=t d/dt` on `L²(R_+,dt)`, the formal adjoint is `D*=-D-1`; hence

```text
H_0 = -D(D+1) = D*D.
```

The power profile `t^(-w)` has energy `lambda(w)`.  The weight-one inversion
`Jf(t)=t^(-1)f(t^(-1))` is unitary on this Hilbert space, exchanges `w` with `1-w`, and commutes
with the quadratic Hamiltonian.  Thus the critical line maps to the real continuum
`lambda=1/4+gamma^2`.

This interpretation does not prove RH by itself.  Its exact non-circular successor is to construct
from the theta--Euler--Gamma source a self-adjoint boundary or scattering realization whose
spectral determinant is Xi in the parameter `lambda`, without selecting the domain from the Xi
divisor.

## Lean

Module:
`formal/GaloisForLFunctions/RHTower/QuadraticScaleSpectralRH.lean`.

- `quadraticScaleEnergy`
- `quadraticScaleEnergy_eq_centered`
- `XiQuadraticSpectralReality`
- `xiQuadraticSpectralReality_of_rh`
- `riemannHypothesis_of_xiQuadraticSpectralReality`
- `xiQuadraticSpectralReality_iff_riemannHypothesis`

The focused module build passes.  The theorem uses the already formalized open-strip location of
xi zeros and the source proof that xi is nonzero on the real open strip.

## Novelty

The equivalence is an elementary repackaging of the critical-line equation in the natural
quadratic spectral parameter.  It is useful infrastructure for the scale-Hamiltonian detour but
is not new scientific knowledge.

## Gates

- [x] 0 -> 1: exact non-circular proposition and source interpretation stated
- [x] 1 -> 2: paper proof complete
- [x] 2 -> 3: Lean theorem complete; focused build passes
- [ ] 3 -> 4: not selected for standalone publication

