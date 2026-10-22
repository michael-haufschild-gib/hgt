# Homogeneous constraint maps become valuation--clock dilations

- **ID:** `homogeneous-constraint-valuation-clock-functoriality`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE] [MASTER THEOREM] [GENERAL HT LAW]`
- **Scientific status:** `[NOVELTY UNVERIFIED] [SIGNIFICANCE CANDIDATE]`
- **Source:** universal prime-valuation constraint realization, prime-power analytic dilation,
  and the single-source constraint-completeness law
- **Statement:** A homogeneous map of constraint degree `q` is transported by prime-valuation
  realization to a valuation dilation `m -> q m`; the arithmetic differential clock transforms
  covariantly as `D R_q = q R_q D`, and pullback of homogeneous relation layers is exact.

## Goal

Upgrade static constraint realization to a morphism law.  The current theorem realizes every
homogeneous vanishing ideal and Hilbert function, but arbitrary realization alone risks being only
an encoding result.  The proposed strengthening asks whether polynomial maps between constraint
geometries are forced to become canonical arithmetic renormalizations between their realized HT
systems.

The theorem is about the structure of prime-supported hypertranscendental fields.  RH is a
downstream selector test only.

## Master theorem `[CONJECTURE]`

Let `K subset C^sigma`, `L subset C^tau`, and let

```text
Phi : C^sigma -> C^tau
```

have homogeneous coordinate polynomials of one positive degree `q`, with `Phi(K) subset L`.
For every homogeneous `Q` of degree `m` on `C^tau`, its pullback `Q o Phi` is homogeneous of
degree `q m`.  Under the universal repeated-prime realizations, the following should hold.

1. **Exact constraint pullback.**  `Q` vanishing on `L` implies `Q o Phi` vanishes on `K`; if
   `L` is the Zariski closure of `Phi(K)`, the induced map on homogeneous coordinate quotients is
   injective.
2. **Valuation naturality.**  The prime coefficient column of `Q o Phi` is the coefficient column
   of `Q` after applying `Phi` to the source profile, but it occurs in valuation degree `q m`.
   Thus pullback is represented arithmetically by the dilation `R_q : p^m -> p^(q m)`.
3. **Clock covariance.**  For the rotated logarithmic derivation,

   ```text
   D R_q = q R_q D,
   D^k R_q = q^k R_q D^k.
   ```

   In the analytic Dirichlet realization this is the ordinary chain rule under `s -> q s`.
4. **Composition.**  Degree-`q` followed by degree-`r` constraint maps becomes valuation dilation
   by `qr`; the associated clock factors multiply.  Identity maps have degree one.
5. **Complete-relation compatibility.**  Because each realized system has a complete relation
   ideal, the pullback above transports all homogeneous relations and introduces no unrecorded
   differential relations.

The positive law is:

```text
projective degree is arithmetic time scale: nonlinear constraint morphisms are exactly
valuation-renormalizing, clock-covariant maps of the realized HT systems.
```

## Why this is not a wrapper

The homogeneous pullback law and the chain rule are separately classical.  The candidate content
is their forced identification inside one arithmetic differential realization whose full relation
ideal is known: geometric degree, prime valuation, analytic argument dilation, and derivative
weight become one invariant.  If this compatibility cannot be proved at the carrier level, the
card must be retired as vocabulary rather than promoted.

## External parent boundary

- homogeneous coordinate rings, Veronese subrings, and pullback along projective morphisms are
  classical;
- composition operators `f(s) -> f(qs)` on Dirichlet-series spaces are classical;
- the chain rule under `s -> q s` is classical;
- fully faithful homogeneous-coordinate functors exist in Cox-ring settings.

The novelty claim, if any, is restricted to the prime-valuation realization functor with exact
differential relation ideals and its degree--valuation--clock covariance.  A specialist priority
audit is required.

## RH pressure test

Finite zeta valuation windows are differentially free, while the canonical theta completion has
genuinely infinite support.  The proposed law says a finite homogeneous selector can only rescale
the valuation clock; it cannot create the missing completed reflection polarization.  An RH-capable
selector must therefore be compatible with the entire valuation-dilation system and also survive
its infinite archimedean completion.

## Gates

- [x] 0 -> 1 in-progress: well-posed carrier-level identities and anti-theatre attack stated
- [ ] 1 -> 2 fully-proven: complete paper proof including relation-layer compatibility
- [ ] 2 -> 3 formalized: unconditional declarations for pullback, valuation naturality, clock
  covariance, and composition
- [ ] external NOVEL gate: no parent theorem identifies projective degree with valuation and the
  differential clock in a complete arithmetic HT realization
- [ ] external SIGNIFICANT gate: functoriality materially strengthens static realization
- [ ] 3 -> 4 publication-ready: standalone paper restricted to the verified theorem surface

## Current open core

Formalize homogeneous polynomial substitution with exact degree multiplication, then prove that
the corresponding coefficient carriers agree after prime-power dilation.  Reuse the already proved
all-order arithmetic and analytic chain laws; do not reprove them.
