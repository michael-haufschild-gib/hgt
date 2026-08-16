# Suzuki's archimedean primitive has a forced sign change below the half shift

- **ID:** `suzuki-archimedean-primitive-forced-sign-change`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper), `[PROVED HERE; SEARCH/BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** Suzuki's explicit shifted-Xi Mellin kernel;
  `../../3-formalized/not_new_scientific_knowledge/shifted-euler-prime-orbit-pf2-failure.md`
- **Statement:** In the RH-relevant range `0<omega<1/2`, the integrated archimedean kernel entering
  Suzuki's one-sign criterion is negative near zero and positive near one.  Thus neither the
  archimedean factor alone nor positivity of the Euler dilation coefficients can give the required
  eventual sign by a pointwise sign-preservation argument.

## Setup

Let `g_omega` be Suzuki's compactly supported archimedean kernel on `(0,1)`, and define

```text
g_omega^(1)(x)
 =integral_x^1 sqrt(y/x) g_omega(y) dy/y,
                                                        0<x<1.               (1)
```

Suzuki's explicit kernel has the endpoint asymptotics

```text
g_omega(y)
 =A_omega(1-y)^(omega-1)+o((1-y)^(omega-1))             as y->1-,

A_omega=(2pi)^omega/Gamma(omega)>0,                     (2)
```

and, for `0<omega<3/2`,

```text
g_omega(y)
 =-B_omega y^(omega-1)+o(y^(omega-1))                   as y->0+,

B_omega=4omega pi^(omega-1/2)Gamma(3/2-omega)>0.        (3)
```

## Theorem: opposite endpoint signs

For `0<omega<1/2`,

```text
g_omega^(1)(x)
 ~-B_omega/(1/2-omega) x^(omega-1)                      as x->0+,             (4)

g_omega^(1)(x)
 ~ A_omega/omega (1-x)^omega                            as x->1-.             (5)
```

Consequently `g_omega^(1)` is negative on some interval `(0,epsilon_omega)` and positive on some
interval `(1-delta_omega,1)`.  In particular it changes sign on `(0,1)`.

### Proof near zero

Rewrite `(1)` as

```text
g_omega^(1)(x)
 =x^(-1/2) integral_x^1 y^(-1/2)g_omega(y)dy.           (6)
```

By `(3)`, the singular part of the integrand is

```text
-B_omega y^(omega-3/2).
```

Since `omega-1/2<0`,

```text
integral_x^delta y^(omega-3/2)dy
 ~x^(omega-1/2)/(1/2-omega).                            (7)
```

Multiplication by `-B_omega x^(-1/2)` gives `(4)`.  The integral over `[delta,1]` is
`O(x^(-1/2))`, which is lower order than `x^(omega-1)` because `omega<1/2`.  The `o` term in `(3)`
is handled by the same split with an arbitrary relative-error bound.

### Proof near one

On `[x,1]`, both `x^(-1/2)` and `y^(-1/2)` tend uniformly to one.  Insert `(2)` into `(6):

```text
integral_x^1 A_omega(1-y)^(omega-1)dy
 =A_omega/omega (1-x)^omega.
```

The integrated `o` term is lower order, proving `(5)`.

Continuity on `(0,1)` then gives the sign change.

## Route C consequence

Suzuki's causal source primitive is

```text
h_omega^(1)(x)
 =x^(-1) sum_(n<=x)c_omega(n)g_omega^(1)(n/x),
```

with positive `c_omega(n)`.  The summand kernel itself has both signs, and the coefficient sequence
fails PF2 on every prime orbit.  Therefore no pointwise-positive or variation-diminishing argument
forces `h_omega^(1)` to have the eventual single sign that would imply innerness.

The remaining possibility is a genuinely arithmetic cancellation theorem for the complete
prime-dilation mixture against the explicit archimedean sign change.  Such a theorem must use the
distribution of all prime powers quantitatively; neither factor separately has the required sign
rigidity.

## Scientific-novelty verdict

`[NOT NEW SCIENTIFIC KNOWLEDGE]` The endpoint expansions are direct integrations of Suzuki's
published kernel asymptotics.  The result is a route-local bridge and not new analysis.

## Gates

- [x] 0 -> 1: archimedean one-sign proposal and endpoint falsifier isolated.
- [x] 1 -> 2: both asymptotics and forced sign change proved on paper.
- [ ] 2 -> 3: no Lean formalization selected; the open theorem is the all-prime cancellation law.
- [ ] 3 -> 4: no scientific-novelty claim.
