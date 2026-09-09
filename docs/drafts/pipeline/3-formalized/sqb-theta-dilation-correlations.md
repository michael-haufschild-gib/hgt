# SQB: exact theta dilation correlations

The literal theta dilation source and both correlations entering its proposed
modular Gram calculation are formalized. Full modular Gram transport,
normalized occurrence and RH remain unproved.

## Source and theorem

Let Phi be the complete arithmetic theta source. For every complex rho, set

    g0(t) = (1/2) Phi(t/2) exp((rho+1/2)t/2),
    c = exp(-log(2)/2),
    g(t) = 2 g0(t) - c g0(t+log(2)),
    d(z) = 2 - c exp(i z log(2)),
    hat f(z) = integral_R exp(-i z t) f(t) dt.

The proved transform is

    hat g(z) = d(z) xiCent(rho+1/2-2iz).

For the literal complete correlations

    K(u) = integral_R conj(g(t)) g(t+u) dt,
    J(v) = integral_R conj(g(t)) g(v-t) dt,

the proved identities, for every complex z, are

    hat K(z) = conj(hat g(conj z)) hat g(z),
    hat J(z) = conj(hat g(-conj z)) hat g(z).

Every exponential twist of g, K and J is integrable. Thus these equations
include convergence, rather than only identities between totalized integrals.

At an actual multiplicity copy rho=beta+i gamma of the Xi divisor,

    hat g(-i/2) = xi(rho) = 0,
    hat K(-i/2) = hat J(-i/2) = 0,
    hat g(gamma/2) = d(gamma/2) xi(beta+1) != 0,
    Re(hat K(gamma/2)) = |hat g(gamma/2)|^2 > 0.

## Dependency-closed proof

1. Scale the actual bilateral theta integral by t/2. Its all-rate envelope
   proves integrability for every complex exponent, and its exact Xi
   transform gives the displayed argument rho+1/2-2iz.
2. Translate by log(2), retaining the half-density coefficient. Translation
   multiplies the transform by exp(i z log(2)); linearity gives d(z).
3. Identify J with convolution of conj(g) and g. After an arbitrary complex
   exponential twist it is convolution of the corresponding twisted factors.
   Both are integrable, so Bochner convolution integrability and the integral
   convolution theorem give the full reflected product transform.
4. Reflect the first factor to identify K with convolution of conj(g(-t))
   and g. The same integrability argument gives its product transform.
5. At -i/2 the dyadic factor equals one and the Xi argument is rho-1/2.
   Actual divisor membership supplies xi(rho)=0.
6. At gamma/2 the Xi argument is beta+1/2. The actual divisor strip gives
   beta>0, so xi(beta+1) is nonzero on the strict Euler side. On the real
   line the oscillatory term in d has norm c<=1<2. Both factors are therefore
   nonzero, and the translation correlation has strictly positive transform.

## Formal surface and limit

Module: `formal/GaloisForLFunctions/RHTower/SelbergThetaDilationTransform.lean`.
Namespace: `RHTower.SelbergThetaDilationTransform`.
There are 36 public declarations, wired once into `RHTower.lean`.

These theorems evaluate the actual arithmetic source factors needed for the
Gram comparison in [the positive occurrence loop](../1-in-progress/sqb-positive-occurrence-conjecturing-loop.md).
They do not identify the full modular norm with a real-line scattering norm,
prove a normalized residual estimate, or construct full-Xi occurrence.

Source checking and the final leaf build passed. The leaf audit used
`lake --old build GaloisForLFunctions.RHTower.SelbergThetaDilationTransform`:
only this leaf was built, against existing dependency artifacts. Ordinary
transitive preflight found stale unrelated dependencies; those dependencies
were not rebuilt. Replayed dependency diagnostics are retained in
`/tmp/sqb26_leaf_build.log`. This is not a fresh audit of the whole dependency
source tree. No full or umbrella build and no numerical experiment was run.

All 36 public declarations passed the `/tmp/sqb26_axioms.lean` audit with
only `propext`, `Classical.choice` and `Quot.sound`. Source checks produced
no diagnostics. Index regeneration and the scoped whitespace check passed.
Repository lint was run and failed on four unrelated, unwired HTGeometry
modules: `ConservativeDissipativeConstraints`, `ConservativeDissipativeFlow`,
`ConservativeDissipativeOperator` and `ConservativeDissipativeSpectrum`.
The new SQB module is reachable from its umbrella. The lint output is
`/tmp/sqb26_lint.log`; the axiom output is `/tmp/sqb26_axioms.log`.
