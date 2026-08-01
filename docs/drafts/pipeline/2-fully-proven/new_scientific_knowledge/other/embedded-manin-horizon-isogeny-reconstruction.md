# The embedded Manin horizon reconstructs a simple varying abelian bulk up to isogeny

- **ID:** embedded-manin-horizon-isogeny-reconstruction
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** abelian-multiplication-tail-manin-horizon + Manin-kernel rigidity
- **Statement:** The translation stabilizer of an embedded abelian multiplication tail is
  exactly the Manin kernel; for simple abelian varieties not descending to the constants, the
  nonorthogonality class of this horizon symmetry determines the bulk isogeny class.

## Goal

Recover precisely which global information is lost by the abstract no-hair theorem and which is
retained when the tail is kept together with its embedding and ambient translation action.

## Gates

- [x] 0 -> 1 in-progress: embedded stabilizer and reconstruction equivalence isolated
- [x] 1 -> 2 fully-proven: complete proof, `[PROVED HERE]`, Manin-kernel rigidity imported
- [ ] 2 -> 3 formalized: Kolchin topology and Manin kernels unavailable in current Lean
- [ ] 3 -> 4 publication-ready: expert novelty audit and standalone synthesis

## Setup

Let `(K,delta)` be differentially closed of characteristic zero, let `A/K` be an abelian variety,
let `m` satisfy `|m|>1`, and let

`T_A=Tail_m(A)=K<mu_A(a)> subset K<a>`

be the embedded multiplication tail of a differential-generic point `a`.

Define its differential translation stabilizer by

`Stab_A(T_A) = {h in A : f(a+h)=f(a) generically for every f in T_A}.`  (1)

The definition uses the ambient group law and the embedding of `T_A`; it is not an invariant of
the abstract differential field alone.

## Theorem A: exact horizon stabilizer

**[PROVED HERE]**

`Stab_A(T_A)=A^sharp.`                                              (2)

Thus the Manin kernel has a purely asymptotic-dynamical characterization: it is the complete
translation symmetry of the field visible through every depth of one multiplication tower.
Equation (2) is independent of the choice of `m` with `|m|>1`.

### Proof

The Manin-horizon theorem gives `T_A=K<mu_A(a)>` and `ker(mu_A)=A^sharp`.

If `h in A^sharp`, then

`mu_A(a+h)=mu_A(a)+mu_A(h)=mu_A(a)`,

so every element of `T_A` is invariant and `h` belongs to (1).

Conversely, the coordinate functions of `mu_A(a)` and all their derivatives lie in `T_A`.
If `h` stabilizes every tail element, then `mu_A(a+h)=mu_A(a)`.  Since `mu_A` is a group
homomorphism, `mu_A(h)=0`, hence `h in A^sharp`.  This proves (2).

## Theorem B: horizon Torelli theorem up to isogeny

**[PROVED HERE]** Let `A` and `B` be simple abelian varieties over the universal differential
field, neither descending to the constant field.  Then

`Stab_A(T_A)` and `Stab_B(T_B)` are nonorthogonal

if and only if

`A` and `B` are isogenous.                                          (3)

Consequently, the nonorthogonality class of the embedded horizon symmetry reconstructs the
isogeny class of a simple varying abelian bulk.

### Proof

By Theorem A, the two stabilizers are `A^sharp` and `B^sharp`.  For simple abelian varieties not
descending to constants, Manin-kernel rigidity states

`A^sharp nonorthogonal to B^sharp iff A isogenous to B`.

Substitution gives (3).  A published statement of this rigidity appears as Fact 5.6 in
Casale--Freitag--Nagloo: <https://arxiv.org/abs/1811.06583>.

## Corollary: exact abstract/embedded dichotomy

For fixed dimension and multiplier:

- the abstract tail dynamical fields of `A` and `B` are always isomorphic;
- their embedded horizon symmetries are nonorthogonal exactly when the simple varying bulks are
  isogenous.

The boundary field has no hair, but the way it sits in the ambient differential group has enough
hair to recover the bulk up to isogeny.

## Physical/topological reading

This is interpretation only.  The horizon algebra by itself is universal.  Its stabilizer inside
the ambient translation geometry is the differential fundamental symmetry `A^sharp`.  For a
simple varying bulk, the interaction class of that symmetry is a complete isogeny invariant.

This gives a precise version of holographic reconstruction with a sharp qualification: intrinsic
boundary observables do not reconstruct the bulk, but boundary observables plus their ambient
symmetry embedding do so up to isogeny.

## Novelty and significance gate

The inputs `ker(mu_A)=A^sharp` and Manin-kernel nonorthogonality/isogeny rigidity are classical.
The new theorem surface is the dynamical characterization (2) and its combination with rigidity
to obtain the embedded-horizon reconstruction criterion (3).  Targeted searches found no such
stable-tail formulation.  Novelty remains provisional pending expert review.

This supplies a genuine converse within the abelian sector and materially strengthens the HT
horizon theory.  It still does **not** clear the Fields-Medal gate because the decisive rigidity
input is imported and the new deduction is short.

## Lean status

`DeckClosureReconstruction.lean` formalizes the exact ordinary-Galois analogue: a stable core
recovers the topological closure of its total deck group as its fixing subgroup.  The present
Kolchin/Manin-kernel theorem remains paper-level; Krull closure and Kolchin closure are not
identified or conflated.

## RH impact audit

The theorem identifies the minimum extra structure an abelian-tail RH strategy must retain:
the embedded tail and its stabilizer, not merely the abstract boundary field.  Such data can
recover an isogeny class, but no known argument connects that class to zeta-zero location or RH
positivity.  The result sharpens architecture without proving an RH statement.

## Log

- 2026-07-15 -- [PROVED HERE] Tail stabilizer identified with the Manin kernel; simple
  nonconstant embedded horizons shown to reconstruct bulk isogeny class through
  nonorthogonality.
