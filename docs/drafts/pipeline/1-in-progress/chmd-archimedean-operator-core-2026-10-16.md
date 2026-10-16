# CHMD: compact operator core for the singular archimedean generator

Status: investigation. RH goal active. Previous continuation was verified progress: full arithmetic domain removal. Prior main operator/domain source hashes revalidated; no current operator-core theorem found in the CHMD leaves. Architecture/testing docs absent. Plan tooling unavailable; this card tracks the task.

## Intended structural result

Prove the actual compact smooth source class is an operator core for the archimedean generator, and transfer this to the full arithmetic generator using the now-proved bounded prime perturbation. This must close weak-domain admission; a form-core result, bound, generic receiver or assumed essential-selfadjointness premise does not suffice.

## Working plan

1. Reinspect current corpus for actual stationary/archimedean generators and operator-core infrastructure. Do not overwrite concurrent CHMDPointwiseGenerator work.
2. Close the paper proof, checking actual theta half-density, first Levy moment, square-root regularity, stationary compact core, and bounded-commutator selfadjointness.
3. Formalise the dependency-closed mechanism and instantiate it on the literal CHMD source, with no new premise or axiom.
4. Targeted --old leaf builds, direct Lean audits of every new module, all-declaration axiom audits, umbrella wiring, lint, exact scratch cleanup and memory.

## Candidate mechanism under audit

Write c=cosh(x/2), a=sqrt(Theta/c), Uu=sqrt(Theta*c)u. Candidate identity: U La U^-1=a A a+V, with A the stationary symmetric Levy generator and V=c^-1 integral kappa(t)(Theta(x+t)+Theta(x-t)-2Theta(x)) dt. First displacement moment and global theta Lipschitz regularity bound V. Positivity and globally bounded theta second derivative should make sqrt(theta), hence a, bounded Lipschitz. Then [A,a] is bounded.

If A has compact smooth operator core, the resolvent regularisers J_e=(1+eA)^-1 satisfy a bounded commutator [aAa,J_e] tending strongly to zero. This would approximate every adjoint-domain vector by Dom(A), prove essential selfadjointness of the sandwich, and transfer the compact core. This remains a candidate until its analytic/domain details are closed and formalised.

The stationary generator may be constructed by a Fourier multiplier already in the corpus or directly from its translation-invariant closed difference graph. Smoothing commutes with that generator; cutoffs have commutators controlled by the first displacement moment.

## Corpus audit and first exact reduction

The first deep query completed without a partial result; inventory coverage was 72746/72746 files, with many compiler records pending or stale. Candidate statements were checked in source. No applicable compact operator-core or essential-selfadjointness theorem was found. The gamma-clock spectral model has an extra factor 1/t in its Levy kernel and cannot be identified with this stationary operator.

Before constructing an operator core, formalise the actual maximal-domain ground-state cancellation. Put S u=Theta*u. Pointwise,

    Theta(x)Theta(y)(u(x)-u(y))^2 - (S u(x)-S u(y))^2
      = (Theta(y)-Theta(x))(Theta(x)u(x)^2-Theta(y)u(y)^2).

Global theta Lipschitz regularity bounds the absolute difference by C|x-y| times the sum of the two theta-weighted squares. The first Levy moment and mass-L2 admission make this integrable, without compact support, pointwise regularity of u, or square-root estimates. Consequently the maximal archimedean domain is exactly the pullback of the stationary jump domain by S. Fubini and translation turn the integrated defect into the bounded potential V above. This gives an exact closed-form and resolvent reduction, not yet an operator-core theorem. The compact-core target remains open.

The first two leaves now pass targeted Lean builds: `CHMDStationaryGroundDomain` proves the maximal domain cancellation, and `CHMDStationaryGroundPotential` identifies its defect with the explicit bounded multiplication operator. Closed pullback graph, graph equivalence and resolvent identities are being checked next.

Domain distinction: the source form domain is exactly the set of mass-L2 u for which Theta*u has stationary jump energy. The pullback generator is constructed from that closed form. No identification of its operator domain with `{u : Theta*u in Dom(A)}` is asserted; the weighted output condition can be weaker. No compact operator-core conclusion follows merely from the form-domain cancellation.

## Closed operator construction

The stationary pullback graph is closed by simultaneous almost-everywhere subsequences of source and edge coordinates. Its source-preserving equivalence with the archimedean graph is continuous by the closed graph theorem. The exact squared-norm identity polarises to an exact graph inner-product identity. Both graph equivalence and inner-product decomposition now pass targeted builds.

Put K=P+V. Riesz representation of the two complete graph inner products yields

    Rg(w-K Rw)=Rw,       R(w+K Rg w)=Rg w.

Thus the resolvent ranges coincide. To realise actual operators, first observe that the full source projection has dense range: every compact smooth mass-L2 class occurs as a genuine compact lift, and these classes are dense. The same holds for the stationary source projection by the proved domain equivalence. Their Riesz resolvents are injective and self-adjoint. Define A_R=R^{-1}-I on range(R). For u in Dom(A_R*), testing its adjoint identity on Rz for every z gives R(u+A_R*u)=u. Hence u lies in range(R), and the adjoint agrees with A_R. This is a dependency-closed self-adjointness argument, with no compact operator-core premise. The exact operator identity is A_full=A_ground+K on their common domain. The corresponding Lean leaves are being checked.
