# Disconnected Böttcher coordinates have dyadic infinite monodromy

- **ID:** bottcher-dyadic-monodromy-finite-type-absence
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / concrete C11 witness
- **Source:** C11 monodromy finite-type absence; Nguyen Q6.2 period lemma

## Statement

Let `f_c(z)=z^2+c` with `c notin M`, and let `phi_c` be the normalized direct
Böttcher coordinate germ at infinity:

`phi_c(f_c(z))=phi_c(z)^2`, `phi_c(z)/z -> 1`.

Then analytic continuation of `phi_c` on `Omega_c=C\K_c` has infinite dyadic
scalar monodromy. More precisely, for every `n>=1` there is a loop in `Omega_c`
whose continuation sends

`phi_c -> exp(2*pi*i/2^n) phi_c`.

Consequently, the continuation of `phi_c` is not captured by any finite branch
cover or finite monodromy permutation representation.

## Proof

Since `c notin M`, `K_c=J_c` is a Cantor set and `f_c|K_c` is conjugate to the
one-sided full two-shift. Let `mu_c` be the equilibrium measure of `K_c`.

For any depth-`n` symbolic cylinder `C_w subset K_c`, choose a loop, or finite
product of loops with the same basepoint, in `Omega_c` whose winding number is
`1` on `C_w` and `0` on `K_c\C_w`. This exists because `C_w` is clopen inside
the zero-dimensional compactum `K_c`.

The complex Green potential gives the multivalued logarithm of the Böttcher
coordinate:

`log phi_c(z) = int log(z-zeta) dmu_c(zeta)`,

normalized near infinity. Hence

`d log phi_c = int dz/(z-zeta) dmu_c(zeta)`.

For the separating loop `gamma`,

`int_gamma d log phi_c
 = int_K (int_gamma dz/(z-zeta)) dmu_c(zeta)
 = 2*pi*i int_K Ind(gamma,zeta) dmu_c(zeta)
 = 2*pi*i mu_c(C_w)`.

The equilibrium measure is the Brolin-Lyubich measure, i.e. the measure of
maximal entropy, and under the full two-shift coding it is the fair Bernoulli
measure. Therefore `mu_c(C_w)=2^-n`.

Thus continuation along `gamma` changes `log phi_c` by `2*pi*i/2^n` and sends

`phi_c -> exp(2*pi*i/2^n) phi_c`.

The orders of these multipliers are unbounded. A finite branch cover or finite
permutation monodromy representation has only finitely many possible branch
values over a generic basepoint. The dyadic monodromy orbit of a generic branch
contains roots of unity of order `2^n` for arbitrarily large `n`, hence is
infinite. Therefore no finite branch cover or finite monodromy representation
captures the continuation. ∎

## Relation to C11

C11 says that analytically continuable hypertranscendental functions should not
admit a finite algebraic monodromy controller. This theorem verifies that
mechanism for every disconnected nonexceptional quadratic Böttcher coordinate:
the obstruction is not a local finite branch point but an infinite period action
around the Cantor boundary.

## Source boundary

- De Marco's shift-locus notes record that shift-locus polynomial Julia sets are
  conjugate to the one-sided full shift.
- Binder--Braverman--Rojas--Yampolsky recall that, for polynomials, the
  Brolin-Lyubich measure coincides with harmonic measure of the basin of infinity.
- Schmidt's Compositio paper, §6, independently supports high-order root-of-unity
  monodromy for disconnected Böttcher uniformization.
- Becker--Bergweiler/Fernandes supply the hypertranscendence classification for
  nonexceptional Böttcher functions; this card isolates the topological monodromy
  obstruction, not the full differential-algebraic classification.

## Significance

This is a concrete, non-generic C11 theorem. It does not prove the generic C11
conjecture, and its ingredients are classical/source-supported. Its value is that
it identifies an exact finite-handle failure mode for a hypertranscendental family:
unbounded dyadic continuation monodromy around a Cantor boundary.

## 2026-06-24 exact-image strengthening

The exact scalar monodromy image is now recorded separately in
`bottcher-exact-pruefer-monodromy.md`: the period group of `d log phi_c` is
exactly `2*pi*i Z[1/2]`, and the multiplier image is exactly the Prüfer
`2`-group `mu_{2^infty}`.

This card should be read as the C11 finite-type consequence of that sharper
exact-image theorem.
