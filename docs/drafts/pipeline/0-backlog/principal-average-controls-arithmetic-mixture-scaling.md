# Principal average controls arithmetic mixture scaling

- **ID:** B130-principal-average-scaling
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** [Explicit arithmetic mixture](../3-formalized/arithmetic-two-profile-mixture-with-a-delayed-moving-pole.md), [endpoint moment obstruction](../3-formalized/endpoint-tangent-moment-obstructs-polynomial-scaling.md).

## Statement

Fix an integer `q≥1`. For each reduced residue class `a mod q`, let
`Φ_a` be analytic on a common disc of radius greater than one,
unimodular on `[0,1]`, with `Φ_a(0)=1` and `Φ_a(1)=-1`.
At primes not dividing `q`, use the actual phase `Φ_[p](p^-t)`;
at each prime dividing `q`, choose a profile with the same properties.
Let `L_t` be the resulting Euler product and
`Ψ=(1/φ(q))Σ_a Φ_a`, `Ψ(z)-1=Σ b_k z^k`.

Conjecture: locally uniformly on `Re w>0`,

`((1+tw)-1)L_t(1+tw)/t² → ζ(2)exp(-Σ_{k≥1}b_k log(w+k))`.

Thus the principal average alone determines the leading scaling;
nonprincipal arithmetic modulation disappears. No joint holomorphic
endpoint germ agrees with these actual Euler products, even if
agreement is required only at nearby positive real parameters and
real spectral values above one.

## Mathematical gap

Finite Dirichlet Fourier inversion is already proved by
`RHTower.dirichletCharacterFourier_expansion` in
`RHTower/SelbergClass/DirichletFourier.lean`. Bounded nonprincipal
prime-log continuation and summable shifts are proved in
`GaugeDeformations/CharacterPrimeLogContinuation.lean`.
`analyticPhase_affine_average_no_entire_scaling` excludes an entire
extension of the proposed mean profile.

Still needed: derive the actual Euler expansion for arbitrary residue
profiles, including every ramified prime; control its principal and
nonprincipal Taylor tails uniformly; and prove that a joint analytic
germ with this quadratic scaling would force a polynomial limit of
degree at most two. None of these conclusions is an assumption.

## Significance and boundary

The explicit modulo-four example has a fourth-order shifted zero and
a later second-order pole. This conjecture asks whether every finite
arithmetic mixture retains a singular shift, including mixtures with
infinitely many nonzero Taylor coefficients. The positive survivor is
the exact principal-average scaling law. It would classify this family
of proposed specialization paths; B130's arithmetic Stepanov estimate
would remain open.

Corpus searches found the explicit example, the mean-profile
obstruction, and finite Fourier inversion, but no general actual-mixture
scaling theorem. External novelty is unassessed. No complete paper
proof or Lean capstone is claimed.
