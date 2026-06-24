# Disconnected Böttcher monodromy survives every finite cover

- **ID:** bottcher-pruefer-monodromy-no-finite-cover
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / concrete C20 witness
- **Source:** C20 finite-cover descent failure; C11 dyadic monodromy theorem

## Statement

Let `f_c(z)=z^2+c` with `c notin M`, and let `phi_c` be the normalized direct
Böttcher coordinate germ at infinity:

`phi_c(f_c(z))=phi_c(z)^2`, `phi_c(z)/z -> 1`.

Let `Omega_c=C\K_c`. No finite unbranched cover

`pi:Y -> Omega_c`

makes the pulled-back germ `phi_c o pi` single-valued on `Y`.

Equivalently, the Böttcher monodromy cannot be killed by passing to any finite
cover of the basin of infinity. Its monodromy image contains the Prüfer `2`-group
of dyadic roots of unity, and that image survives every finite-index subgroup of
`pi_1(Omega_c)`.

## Proof

From `bottcher-dyadic-monodromy-finite-type-absence.md`, continuation of `phi_c`
defines a scalar monodromy homomorphism

`rho: pi_1(Omega_c,*) -> C^*`

whose image contains roots of unity of order `2^n` for every `n`. More precisely,
component loops around depth-`n` symbolic cylinders have multiplier
`exp(2*pi*i/2^n)`. Therefore `rho(pi_1(Omega_c,*))` contains the Prüfer group

`C_{2^infty} = union_n mu_{2^n}`.

Let `pi:Y -> Omega_c` be a finite connected unbranched cover and let

`H = pi_*(pi_1(Y,*_Y)) subset pi_1(Omega_c,*)`.

Then `H` has finite index in `pi_1(Omega_c,*)`. For any group homomorphism
`rho:G->A` and any finite-index subgroup `H subset G`, the subgroup `rho(H)` has
finite index in `rho(G)`, since `rho(G)/rho(H)` is a quotient of `G/H`.

Apply this to `G=pi_1(Omega_c,*)`. The image `rho(H)` has finite index in
`rho(G)`. But `C_{2^infty}` is divisible, hence has no proper finite-index
subgroups: multiplication by any positive integer is surjective, while a finite
quotient of a divisible abelian group is both divisible and finite, hence trivial.
Therefore `rho(H)` still contains an infinite dyadic subgroup; in particular,
`rho|_H` is nontrivial.

If `phi_c o pi` were single-valued on `Y`, all continuation along loops in
`pi_1(Y)` would have trivial scalar monodromy, i.e. `rho(H)=1`. This contradicts
the previous paragraph. Hence no finite unbranched cover of `Omega_c` kills the
monodromy. ∎

## Branched-cover reading

A finite algebraic cover of the `z`-plane, after removing its finite branch locus
inside `Omega_c`, restricts over a dense open subset of the basin to a finite
unbranched cover. If such a cover made a single-valued analytic branch on the
covered basin, then its restriction would kill monodromy on that finite unbranched
part. The theorem above forbids this. Thus finite ramification away from the
Cantor boundary is not an escape route.

## Relation to C20

C20 asks whether finite covers can expose a hidden finite handle for an HT object.
For disconnected quadratic Böttcher coordinates, they cannot even make the
continuation single-valued. The obstruction is stronger than differential-algebraic
descent: the topological monodromy image is an infinite divisible `2`-primary
group, and finite covers correspond only to finite-index subgroups.

## Significance

This is a concrete finite-cover descent failure theorem for a hypertranscendental
family. It is still bridge-grade because the ingredients are classical topology,
potential theory, and polynomial dynamics, but the obstruction is native to the
constraint-side view: a finite cover cannot absorb an infinite dyadic continuation
action around a Cantor boundary.

## 2026-06-24 finite-index clarification

The proof only needs that `rho(G)` contains `C_{2^infty}`, not that it equals it. If `B=rho(H)` has finite index in `A=rho(G)` and `D=C_{2^infty} subset A`, then `B cap D` has finite index in `D`, with

`[D : B cap D] <= [A : B]`.

Since `D` is divisible, it has no nontrivial finite quotient, hence no proper finite-index subgroup. Therefore `B cap D = D`, so `D subset B`. Thus every finite cover still sees the full dyadic monodromy subgroup.

## 2026-06-24 exact-image strengthening

The input monodromy theorem has been sharpened in
`bottcher-exact-pruefer-monodromy.md`: for `c notin M`, the scalar monodromy
image is not merely a group containing the dyadic Prüfer subgroup; it is exactly
`mu_{2^infty}`.

The finite-cover argument in this card only required containment, so the proof
above remains valid. The exact-image theorem makes the obstruction canonical:
every finite cover still sees the whole scalar monodromy group.
