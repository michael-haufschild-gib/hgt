# Finite RG jets are blind to hypertranscendental generation

- **ID:** `finite-rg-jet-blindness-to-hypertranscendence`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / NONPERTURBATIVE NO-GO
- **Scientific status:** `[PROVED HERE] [BRIDGE] [PARENT-DERIVED]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Every finite Taylor jet of an analytically linearizable one-coupling RG map and
  its exact beta field is matched by an algebraic RG germ with an algebraic exact beta field.
  Consequently RG-generation HT cannot be certified from any finite collection of perturbative
  coupling coefficients alone.

## Setup

Translate a hyperbolic fixed point to zero.  Let `R` be an analytic germ with

```text
R(0)=0,              R'(0)=lambda,              0 < |lambda| != 1, (1)
```

and let `Phi` be its normalized Poincare germ:

```text
Phi(0)=0,            Phi'(0)=1,
R(Phi(z))=Phi(lambda z).                                         (2)
```

Write `kappa=Phi^(-1)`.  After choosing a logarithm of `lambda`, the exact local beta field is

```text
beta(t)=(log lambda) kappa(t)/kappa'(t).                          (3)
```

## Algebraic shadow theorem

For every integer `N >= 0`, there is an algebraic analytic germ `R_N` with the same `N`-jet as
`R` and an algebraic exact beta field `beta_N` with the same `N`-jet as `beta`.

More explicitly, let `P_N` be the Taylor polynomial of `Phi` through degree `N+1`.  Then

```text
P_N(z)-Phi(z)=O(z^(N+2)),             P_N(0)=0, P_N'(0)=1.        (4)
```

Let `Q_N` be its local compositional inverse and define

```text
R_N(t)=P_N(lambda Q_N(t)),
beta_N(t)=(log lambda) Q_N(t)/Q_N'(t).                            (5)
```

The polynomial equation `P_N(Q_N(t))=t` makes `Q_N` algebraic over `C(t)`.  Hence both `R_N` and
`beta_N` are algebraic germs.  They satisfy the exact identities

```text
R_N(P_N(z))=P_N(lambda z),
beta_N(R_N(t))=R_N'(t) beta_N(t).                                (6)
```

## Proof of jet agreement

We use the standard contact-order lemma: if two locally invertible germs tangent to the identity
differ by `O(z^M)`, then their local inverses also differ by `O(t^M)`.  Applying it to `(4)` gives

```text
Q_N(t)-kappa(t)=O(t^(N+2)).                                      (7)
```

For the step map, put `t=Phi(z)`.  Since `Q_N(Phi(z))=z+O(z^(N+2))`, equations `(2)` and `(5)` give

```text
R_N(Phi(z))
  =P_N(lambda z)+O(z^(N+2))
  =Phi(lambda z)+O(z^(N+2))
  =R(Phi(z))+O(z^(N+2)).                                        (8)
```

Because `Phi'(0)=1`, contact order in `z` and `t` agrees.  Thus `R_N-R=O(t^(N+2))`.

For the beta field, write `Q_N=kappa+delta`, where `(7)` gives
`delta=O(t^(N+2))` and `delta'=O(t^(N+1))`.  Then

```text
Q_N/Q_N' - kappa/kappa'
  =(delta kappa' - kappa delta')/(Q_N' kappa')
  =O(t^(N+2)),                                                   (9)
```

because `kappa(t)=t+O(t^2)` and both derivatives in the denominator are units.  Hence
`beta_N-beta=O(t^(N+2))`.  In particular the `N`-jets of both pairs agree.

## Sharp interpretation

The theorem does not say that a finite proof can never establish HT.  A finite functional
constraint plus global divisor, singularity, monodromy, or Galois information can do so.  It says
that finite Taylor data alone cannot:

```text
for each finite order N,
the observed RG and beta coefficients admit an exact algebraic completion.   (10)
```

The algebraic completion may depend on `N`; no single algebraic germ is asserted to match all
orders.  This dependence is precisely why successively longer perturbative series cannot by
themselves cross the HT boundary.

## Physical consequence

RG-generation HT is strictly nonperturbative in the jet sense.  A finite-loop beta function, a
finite normal-form calculation, or finitely many derivatives of a nonlinear scaling field cannot
distinguish

```text
an algebraically generated exact flow
from a hypertranscendentally generated exact flow.                (11)
```

The discriminator must see an all-order or global constraint: an infinite critical-preimage tree,
a natural boundary, monodromy, a differential Galois group, or incompatibility with every rational
invariant differential.

For the Abdesselam--Chandra--Guadagni p-adic RG, this kills a tempting but unproductive program:
computing more Taylor coefficients of the unstable scaling field, including its quadratic
curvature, cannot decide its HT status.  Their analytic continuation and complex singularity
geometry, not another perturbative coefficient, are the live objects.

## Anti-theatre and novelty gate

The proof is an elementary application of analytic conjugacy, Taylor truncation, algebraic local
inversion, and contact order.  It is useful field infrastructure, not new mathematics.  Its role is
to remove finite-jet and finite-loop theatre from the research program and to force the next move
onto global differential-Galois geometry.

## Lean boundary — resolved 2026-08-17

The local-germ composition/inversion layer this section waited for now exists, and the complete
statement `(4)`--`(9)` is formalized unconditionally.  See the Lean formalization section below.

## Parent sources

- T. L. Curtright and C. K. Zachos, *Renormalization Group Functional Equations*,
  <https://arxiv.org/abs/1010.5174>.
- G. Fernandes, *A survey on the hypertranscendence of the solutions of Schroeder's, Boettcher's
  and Abel's equations*, <https://arxiv.org/abs/2102.12168>.

## Gates

- [x] Algebraic shadow constructed at every finite jet order.
- [x] Exact step and beta constraints retained by the shadow.
- [x] Jet-agreement proof given for both the RG map and beta field.
- [x] Scope limited to finite Taylor data rather than finite mathematical proofs in general.

## Lean formalization — 2026-08-17

Module: `formal/GaloisForLFunctions/HTGeometry/FormalGermFiniteJetShadow.lean`
(wired into the `GaloisForLFunctions.HTGeometry` umbrella).

The card is formalized in the formal-germ category, which is where every one of its statements
lives: `Φ`, `κ`, `R`, `β`, `P_N`, `Q_N`, `R_N`, `β_N` are all formal power series over `ℂ`, jets are
truncations, and "same `N`-jet" is divisibility of the difference by `X^{N+2}`.  Analytic
convergence plays no role in any step of the card's proof, so nothing is lost.

**The layer that was missing** (now built, and reusable for every Schröder/Böttcher/Abel germ card):

| Lemma | Lean name |
|---|---|
| substitution of a positive-order germ preserves `X^M`-divisibility | `FormalGerm.X_pow_dvd_subst` |
| congruent series have congruent substitutions (outer argument) | `FormalGerm.X_pow_dvd_subst_sub_outer` |
| congruent germs give congruent substitutions (inner argument) | `FormalGerm.X_pow_dvd_subst_sub_inner` |
| compositional inverse of a germ with invertible linear coefficient | `FormalGerm.tangentInv`, `subst_tangentInv`, `tangentInv_subst`, `coeff_one_tangentInv`, `constantCoeff_tangentInv` |
| **the contact-order lemma** | `FormalGerm.X_pow_dvd_tangentInv_sub` |
| dilation and formal derivative respect congruences | `FormalGerm.X_pow_dvd_rescale_sub`, `FormalGerm.X_pow_dvd_derivativeFun_sub` |

**The card's own statements:**

| Card step | Lean name |
|---|---|
| `(5)` the shadow constructions `R_N`, `β_N` (as the same construction applied to `P_N`) | `FiniteJetShadow.rgMap`, `FiniteJetShadow.betaField`, `FiniteJetShadow.truncGerm` |
| `(4)` `P_N − Φ = O(z^{N+2})`, `P_N(0)=0`, `P_N'(0)=Φ'(0)` | `X_pow_dvd_truncGerm_sub`, `constantCoeff_truncGerm`, `coeff_one_truncGerm` |
| `(7)` `Q_N − κ = O(t^{N+2})` | `X_pow_dvd_tangentInv_truncGerm_sub` |
| `(8)` `R_N − R = O(t^{N+2})` | `X_pow_dvd_rgMap_truncGerm_sub` |
| `(9)` `β_N − β = O(t^{N+2})` | `X_pow_dvd_betaField_truncGerm_sub` |
| `(6)` the exact step conjugacy `R_N(P_N(z)) = P_N(λz)` | `subst_rgMap` |
| `Q_N` algebraic over `ℂ(t)` (from `P_N(Q_N(t)) = t`) | `isAlgebraic_tangentInv_truncGerm` |
| **the algebraic shadow theorem** | `algebraic_shadow` |

`algebraic_shadow` packages everything: for every germ `g` with `g(0)=0` and invertible linear
coefficient, every `λ`, every branch constant `L`, and every `N`, there is a *polynomial* `p` whose
coefficients agree with `g`'s through degree `N+1`, whose compositional inverse is algebraic over
`ℂ(t)`, which satisfies the exact conjugacy `R_p ∘ p = λ·p`, and whose RG map and beta field agree
coefficientwise with those of `g` through degree `N+1`.

**Route notes.**

1. The contact-order lemma `(7)` is proved without any inverse-function analysis: from `A(U) = X`
   and `B(V) = X`, congruence of `A` and `B` gives `A(V) ≡ A(U)`, and applying `U = A⁻¹` to both
   sides (using associativity of substitution) gives `V ≡ U`.  Only the two congruence lemmas above
   are needed.
2. The card's hyperbolicity hypothesis `0 < |λ| ≠ 1` is not needed for the shadow theorem and is not
   assumed: the construction and all four estimates hold for every `λ`.  Hyperbolicity is what makes
   the *analytic* Poincaré germ exist; the formal statement quantifies over the germ instead, which
   is strictly more general.
3. `β_N − β = O(t^{N+2})` is proved by the card's own cancellation
   `Q_Nκ' − κQ_N' = (Q_N−κ)κ' − κ(Q_N'−κ')`, with `X ∣ κ` supplying the extra order that makes the
   second term `O(t^{N+2})` rather than only `O(t^{N+1})`.

**Not formalized, and not an obligation of this card:** the beta cocycle
`β_N(R_N(t)) = R_N'(t)β_N(t)` displayed as the second half of `(6)`.  It is a consequence of the
conjugacy that requires a chain rule for the formal derivative under substitution, which mathlib
does not have; the card's own claim — that the shadow retains *the exact step constraint* — is the
first half of `(6)` and is proved (`subst_rgMap`).  Also not formalized: the analytic realization
(that a hyperbolic analytic germ has an analytic Poincaré germ), which is the classical
Koenigs/Poincaré linearization theorem and is an input to the setup, not a step of the theorem.

Verification: `lake build GaloisForLFunctions.HTGeometry.FormalGermFiniteJetShadow` — PASS;
`#print axioms` on all fourteen named results reports only
`[propext, Classical.choice, Quot.sound]`.

## Gates (2 → 3)

- [x] Whole theorem formalized unconditionally in Lean — `FiniteJetShadow.algebraic_shadow`.

## Log

- 2026-08-17 — Formalized unconditionally in Lean 4 and promoted to stage 3.  Built the formal-germ
  composition/inversion layer (substitution congruences in both arguments, compositional inverse of
  a germ tangent to the identity, and the contact-order lemma) and used it to prove the algebraic
  shadow theorem in full: jet agreement of the RG map and of the exact beta field, the exact step
  conjugacy, and algebraicity of the shadow's inverse germ.
