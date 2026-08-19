# Bounded prime-screen observables cannot produce the completed Xi amplitude

- **ID:** `prime-screen-bounded-observable-almost-periodicity`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper); source-category no-go
- **Scientific status:** `[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `prime-poisson-superselection-screen.md`; arithmetic Kronecker flow
- **Statement:** The expectation of every bounded continuous observable of the prime-torus
  superselection screen is uniformly almost periodic in height.  Since completed Xi tends to zero
  at vertical infinity and is not identically zero, it cannot be such an expectation.  Any exact
  completion observable must contain a noncompact archimedean component or be unbounded,
  distributional, singular, or derived.

## Setup

Let

```text
G = product_(p prime) S^1
```

and let the arithmetic Kronecker homomorphism be

```text
r(t)_p=p^(it).
```

For any probability measure `mu` on `G`, write `mu_t` for its translate by `r(t)`.  The critical
prime Poisson states are of this form:

```text
mu_t=mu_(1/2+it).
```

Fix `f in C(G)`.  Its screen expectation is

```text
E_f(t)=integral_G f(z) d mu_t(z).
```

## Theorem

`[PROVED]` The function `E_f:R->C` is Bohr uniformly almost periodic.

### Proof

Define the convolution

```text
g_f(x)=integral_G f(xz) d mu(z).
```

Continuity of translation on the compact group and uniform continuity of `f` show that
`g_f in C(G)`.  By construction,

```text
E_f(t)=g_f(r(t))
```

up to the harmless inverse fixed by the translation convention.

Every continuous function on a compact abelian group is uniformly approximable by finite linear
combinations of characters.  Pulling a character back along `r` gives one exponential

```text
exp(it log q),   q in Q_(>0).
```

Hence `E_f` is a uniform limit of trigonometric polynomials on `R`, which is exactly Bohr uniform
almost periodicity.  QED.

The same proof works for a continuous observable with values in any Banach space.

## Vanishing-at-infinity obstruction

`[PROVED]` If a uniformly almost periodic function `E:R->C` satisfies

```text
E(t)->0 as |t|->infinity,
```

then `E` is identically zero.

Indeed, for every `epsilon>0`, the set of `epsilon`-almost periods is relatively dense and
therefore contains arbitrarily large positive numbers.  Given `x`, choose such a `tau` with
`x+tau` in the tail where `|E|<epsilon`.  Then

```text
|E(x)| <= |E(x)-E(x+tau)|+|E(x+tau)| < 2 epsilon.
```

Letting `epsilon` tend to zero proves the claim.

## Application to completed Xi

On the critical line, Stirling's formula for the Gamma factor and any standard polynomial
vertical-strip bound for zeta give

```text
xi(1/2+it) -> 0 as |t|->infinity.
```

The restriction is not identically zero, since otherwise the identity theorem would make the
entire completed function identically zero.  Therefore no `f in C(G)` satisfies

```text
integral_G f d mu_(1/2+it) = xi(1/2+it)
```

for every real `t`.

The same conclusion holds for any scalar matrix coefficient of a bounded norm-continuous
prime-screen observable whose height dependence is obtained solely by the Kronecker action.

## Route consequence

`[PROVED ROUTE GATE]` Passing from the Haar-normal bulk to the singular prime Poisson sectors fixes
the null-orbit and superselection problems, but it does not by itself produce the completed
amplitude.  The prime compact group can generate only almost-periodic height signals.  The
exponential vertical decay of completed Xi comes from the archimedean Gamma/theta place and cannot
be hidden in a bounded prime observable.

Thus a completion lock must be genuinely joint:

```text
compact prime phase algebra
  plus
noncompact archimedean/additive completion data.
```

An unbounded affiliated observable, a distributional matrix coefficient, a determinant line, or a
derived index remains possible.  Merely choosing a more elaborate bounded function of the full
prime density matrix does not.

This theorem does not localize zeros and does not prove RH.

## Parent and novelty verdict

The proof is a direct composition of compact-group Fourier approximation, the definition of Bohr
almost periodicity, the elementary fact `AP intersect C_0={0}`, and Stirling decay of completed Xi.
It is a sharp project route gate but not new scientific knowledge.


## 2026-08-19 — unconditional Lean formalization (stage 3)

Two new modules carry the card, both unconditional and axiom-clean
(`propext, Classical.choice, Quot.sound`).

**The compact-group almost-periodicity engine** —
`formal/GaloisForLFunctions/HTGeometry/CompactGroupAlmostPeriodic.lean`

Bohr almost periodicity is formalized as relative density of the `epsilon`-almost periods:

```text
IsBohrAlmostPeriodic F  <->  forall eps>0, exists L>0, forall x, exists tau in [x, x+L],
                             forall t, ‖F (t+tau) - F t‖ <= eps
```

| Card item | Lean declaration |
|---|---|
| uniform continuity of `f` under translation near `1` | `exists_nhds_one_norm_translate_sub_le` |
| relative density of the returns of the flow to a neighbourhood of `1` | `exists_relatively_dense_mem` |
| **Theorem: `E_f` is Bohr uniformly almost periodic** | `isBohrAlmostPeriodic_of_compact_flow` |
| **Vanishing-at-infinity obstruction: AP ∩ C_0 = {0}** | `eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero` |
| the convolution `g_f(x) = ∫ f(x z) d mu(z)` | `screenAverage` |
| `g_f in C(G)` | `continuous_screenAverage` |
| `E_f(t) = ∫ f d mu_t` is almost periodic | `isBohrAlmostPeriodic_screenExpectation` |
| Banach-space-valued observables | every statement is proved for a general normed space `E` |

The identity neighbourhood on which the observable moves by less than `epsilon` comes from the
tube lemma over the compact second factor; relative density comes from a finite subcover of the
compact orbit closure by translates of a small open set.  Continuity of the flow is not used: the
homomorphism property alone suffices, so the statement covers every one-parameter group of
translations of the compact screen.

**The prime-screen no-go** —
`formal/GaloisForLFunctions/RHTower/PrimeScreenAlmostPeriodicNoGo.lean`

| Card item | Lean declaration |
|---|---|
| `G = prod_p S^1` with its compact commutative group structure | `PrimeTorus` and its instances |
| the arithmetic Kronecker flow `r(t)_p = p^{it}` | `primeKronecker` |
| `r` is a continuous one-parameter group | `primeKronecker_add`, `continuous_primeKronecker` |
| `xi(1/2+it) -> 0` as `|t| -> infinity` | `tendsto_XiC_ofReal_atTop` |
| **no bounded continuous symbol on the screen equals completed Xi on the line** | `not_exists_primeScreen_symbol_eq_XiC` |
| **no bounded prime-screen observable expectation equals completed Xi** | `not_exists_primeScreen_observable_eq_XiC` |

The vertical decay input is the corpus theorem `exists_norm_XiC_ofReal_le`
(`‖XiC t‖ <= C e^{-delta|t|}` for `0 <= 2 delta < pi/2`, from the theta strip contour shift), used
at `delta = 1/2`; the nonvanishing input is `XiC_zero_ne`.  Stirling asymptotics and any zeta
convexity bound are therefore not needed anywhere in the formal chain.

## Gates

- [x] 0 -> 1: fixed observable category and exact height action stated
- [x] 1 -> 2: complete paper proof and Xi application
- [x] 2 -> 3: compact-group almost-periodicity lemma, the `AP ∩ C_0 = {0}` obstruction and the
  completed-Xi no-go are formalized unconditionally in Lean
