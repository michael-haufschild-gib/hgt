# CHMD: stationary ground-state domain and self-adjoint generators

Status: paper proof closed; Lean audits in progress. Parent task: `../1-in-progress/chmd-archimedean-operator-core-2026-10-16.md`. RH goal remains active.

## Exact result

Write Theta for the actual Riemann kernel, c(x)=cosh(x/2), mu=Theta*c dx, and kappa for the actual CHMD archimedean Levy density. Set S u=Theta*u and

    E0(f)=integral_{t>0,x} kappa(t)(f(x)-f(x+t))^2,
    V(x)=c(x)^(-1) integral_{t>0} kappa(t)
      (Theta(x+t)+Theta(x-t)-2Theta(x)).

For every mass-L2 source u, membership in the complete arithmetic form domain is equivalent to finite E0(S u). On that maximal domain,

    E_full(u)=E0(S u)+< (P+M_V)u,u >_mu.

Here P is the already constructed bounded full prime generator and M_V is multiplication by the explicit bounded real V. The stationary pullback graph is complete and continuously linearly equivalent to the full graph, preserving its source coordinate.

Let R and Rg be the full and stationary-pullback Riesz resolvents. They are injective and self-adjoint, and satisfy

    Rg(w-(P+M_V)Rw)=Rw,
    R(w+(P+M_V)Rg w)=Rg w.

The actual operators L=R^(-1)-I and G=Rg^(-1)-I are densely defined, closed, nonnegative and self-adjoint. Their operator domains coincide and L=G+P+M_V on that common domain.

## Proof mechanism

The exact pointwise cancellation is

    Theta(x)Theta(y)(u(x)-u(y))^2-(Theta(x)u(x)-Theta(y)u(y))^2
      =(Theta(y)-Theta(x))(Theta(x)u(x)^2-Theta(y)u(y)^2).

The global Lipschitz constant of Theta and finite first displacement moment of kappa make its absolute value integrable for every mass-L2 u. This proves both directions of maximal-domain admission. Translation of the backward row and Fubini identify the integrated defect as M_V. Almost-everywhere subsequences close the literal stationary pullback graph; the closed graph theorem gives the source-preserving graph equivalence. Polarisation gives the exact bilinear identity and hence both Riesz identities.

Compact smooth functions are dense in mass-L2 and occur as literal graph sources, so both source projections have dense range and their resolvents are injective. For an adjoint-domain vector u of R^(-1)-I, testing against every Rz forces R(u+(R^(-1)-I)*u)=u. This places u in the original operator domain and proves self-adjointness. The generator forms are the literal edge inner products, proving nonnegativity.

## Lean leaves

- `formal/GaloisForLFunctions/RHTower/CHMDStationaryGroundDomain.lean`
- `formal/GaloisForLFunctions/RHTower/CHMDStationaryGroundPotential.lean`
- `formal/GaloisForLFunctions/RHTower/CHMDStationaryGroundGraph.lean`
- `formal/GaloisForLFunctions/RHTower/CHMDStationaryGroundEquivalence.lean`
- `formal/GaloisForLFunctions/RHTower/CHMDStationaryOperatorDomain.lean`
- `formal/GaloisForLFunctions/RHTower/CHMDStationaryGenerators.lean`

## Boundary

The common operator domain is the domain of the closed stationary pullback form's generator. Identifying it with the smaller-looking condition Theta*u in the ordinary stationary generator domain requires a separate argument. Compact smooth operator-core density, weak compact-test domain admission and the RH sign step remain open.

Corpus searches found no applicable compact operator-core theorem. The existing gamma-clock operator uses an extra 1/t in its kernel and therefore has a different domain; it cannot supply the missing stationary core by identification.

## Validation

Pending final direct Lean checks, all-declaration axiom audit, umbrella wiring and formal lint.
