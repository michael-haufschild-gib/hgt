# Marked-symmetry experiment quotient, recurrence, and lift law

- **ID:** ULF-MSQ-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** constitutive experimental mathematics
- **Statement:** Marking an intervention replaces the passive gauge group by its intervention stabilizer, and the homogeneous quotient controls identifiability, recurrence, and lifted memory.

## Goal

Extract a coordinate-free theorem from the Gaussian synthesis. This is the first general law proposed
by constitutive experimental mathematics.

## Gates

- [x] 0 → 1: compact-group/source-law formulation
- [x] 1 → 2: dependency-closed group-action proof
- [x] 2 → 3: Lean certified — `HTGeometry.ConstitutiveMarkedSymmetryQuotient`
- [ ] 3 → 4: no novelty/priority claim

## Setup

Let a compact Hausdorff group (H) act continuously on a Hausdorff space (X). Let
(\mathcal P(X)) be a Hausdorff space of probability laws on (X), with the induced pushforward
action. Choose:

- a passive source law (\mu\in\mathcal P(X)) invariant under all (H);
- a marked intervention law (\nu\in\mathcal P(X)).

Define its stabilizer

\[
K=\operatorname{Stab}_H(\nu)=\{h\in H:h_*\nu=\nu\}.
\tag{1}
\]

The passive response at (h) is (h_*\mu). The marked intervention response is (h_*\nu).

## Theorem 1 — relative gauge and exact experiment quotient

1. Every (h\in H) is invisible to passive observation:
   \[
   h_*\mu=\mu.
   \tag{2}
   \]
2. Two transformations (g,h\in H) have the same marked intervention response exactly when they
   lie in the same right (K)-coset:
   \[
   g_*\nu=h_*\nu
   \quad\Longleftrightarrow\quad
   h^{-1}g\in K.
   \tag{3}
   \]
3. The response map induces a continuous injection
   \[
   \overline\rho:H/K\hookrightarrow\mathcal P(X),
   \qquad gK\longmapsto g_*\nu.
   \tag{4}
   \]
   Since (H/K) is compact and (\mathcal P(X)) is Hausdorff, this is a homeomorphism onto its
   image.

Thus passive gauge group (H) shrinks to (K) after marking the intervention, and the exact
experiment phase space is the homogeneous space (H/K).

### Proof

Equation (2) is invariance. For (3), apply (h^{-1}_*) to both sides; equality becomes
((h^{-1}g)_*\nu=\nu). This is precisely membership in (K). Hence (4) is well-defined and
injective. Continuity follows from the action; compact-to-Hausdorff continuous injections are
embeddings. ∎

## Theorem 2 — compact response recurrence

Let (\gamma:\mathbb R\to H) be a continuous one-parameter subgroup. Then the intervention
response orbit

\[
t\longmapsto \gamma(t)K\in H/K
\tag{5}
\]

has compact closure and returns arbitrarily close to its initial point at arbitrarily large positive
times. If (\gamma(T)\in K) for some (T>0), it is exactly periodic with period (T).

### Proof

The closure (L=\overline{\gamma(\mathbb R)}\) is a compact abelian subgroup of (H). The positive
semiorbit has the same closure as the full subgroup orbit: its closure is a compact cancellative
subsemigroup of (L), hence a subgroup. Therefore the identity is approached at arbitrarily large
positive times unless it is hit periodically, and projection to (H/K) gives recurrence. Exact
periodicity follows from (\gamma(t+T)K=\gamma(t)\gamma(T)K=\gamma(t)K). ∎

## Theorem 3 — closed response and open lifted history

Suppose a path (\gamma:[0,T]\to H) starts at the identity and ends in (K). Its projected
response is a loop in (H/K). Let

\[
[\overline\gamma]\in\pi_1(H/K,K)
\tag{6}
\]

be its homotopy class. The lift of the response loop to the universal cover of (H/K), starting at a
chosen basepoint, is closed if and only if ([\overline\gamma]=0). Iterating a non-torsion class gives
a recurrent response whose lifted endpoints escape through distinct deck transformations.

### Proof

This is the path-lifting classification for universal covers. The endpoint of the lifted loop is the
deck transformation represented by (6). Iteration raises that deck transformation to successive
powers. ∎

## Corollary — positive phase erasure

Let (\chi:H\to U(1)) be a continuous character. Its positive modulus satisfies

\[
|\chi(h)|^2=1
\tag{7}
\]

for every (h), while a loop can have nontrivial (\chi)-winding. Thus a positive character norm
cannot recover phase history; a marked lift or phase-sensitive intervention is required.

## 2. Exact instantiation

For the isotropic Gaussian theorem:

- (H=SO(2));
- (\mu=N(0,I_2));
- (\nu\) is the law supported on the marked (e_2)-axis after
  (\operatorname{do}(U_1=0));
- (K=\{I,-I\}\);
- (H/K\cong\mathbb{RP}^1\cong S^1).

The half-turn path gives one nontrivial response loop and an open angle lift.

## 3. Hostile scope

This is classical compact-group action and covering-space theory. It does not say every source has a
compact symmetry group, every intervention is probabilistic, or every recurrent law has a nontrivial
lift. Its field content is a precise relative-gauge principle:

> gauge equivalence is the stabilizer of the declared experiment family, not an intrinsic property of
> a source transformation.

Any universal-law claim that calls routes gauges without constructing this stabilizer relation fails.

## Log

- 2026-08-09 — coordinate-free marked-symmetry response theorem created; no Lean.

## Lean certification status (2026-08-09) — COMPLETE

Module: `GaloisForLFunctions.HTGeometry.ConstitutiveMarkedSymmetryQuotient`
(wired into `HTGeometry.UniversalLawField`).

**Theorem 1 — relative gauge and exact experiment quotient.**  Clause (2) is `passive_invisible`.
Clause (3) is `smul_eq_smul_iff_mem_stabilizer`: `g • ν = h • ν ↔ h⁻¹g ∈ Stab_H(ν)`, stated for an
arbitrary group action, hence for the pushforward action on laws.  Clause (4) is `markedResponse`,
the descent of `g ↦ g • ν` to `H ⧸ Stab_H(ν)`, together with `markedResponse_injective`,
`markedResponse_continuous`, and `markedResponse_isClosedEmbedding`, which upgrades it to a closed
embedding when `H` is compact and the law space is Hausdorff.

**Theorem 2 — compact response recurrence.**  `oneParameter_recurrence` proves the recurrence
directly and unconditionally: for a continuous one-parameter subgroup `γ` of a compact topological
group, every neighbourhood `U` of `1` and every bound `M > 0` admit a time `t ≥ M` with `γ t ∈ U`.
The proof is a pigeonhole over the sample times `M, 2M, 3M, …` against a finite subcover of `H` by
right translates of a symmetric neighbourhood `V` with `V·V⁻¹ ⊆ U`, using `oneParameter_sub`
(`γ a · γ b⁻¹ = γ (a − b)`); this replaces the paper's closure-of-semigroup argument with an
argument that does not require identifying the closure as a group.  `oneParameter_periodic` is the
exact-periodicity clause `γ(t + T) • ν = γ(t) • ν` when `γ T ∈ Stab_H(ν)`.

**Theorem 3 — closed response and open lifted history.**  `liftPath_one_eq_of_nullhomotopicRel`:
a response loop null-homotopic rel endpoints has a closed lift in **any** covering of the response
space.  `monodromy_eq_self_iff_eq_one`: for a *universal* (simply connected) covering the converse
holds — the monodromy of a class fixes a point of the fibre exactly when the class is trivial — so
the lift closes if and only if `[γ̄] = 0`, which is (6).

The exact instantiation of §2 is certified concretely.  `halfTurnSubgroup` is the kernel of squaring
on `Circle`; `mem_halfTurnSubgroup_iff` proves it is exactly `{1, −1}` and
`exp_mem_halfTurnSubgroup_iff` proves it is exactly `πℤ` in the angle coordinate.
`stabilizer_markedAxis` proves `Stab_{SO(2)}(marked axis) = halfTurnSubgroup`, i.e. `K` really is
the stabilizer of a marking.  `responseQuotientEquiv : Circle ⧸ K ≃* Circle` identifies the
experiment quotient with `ℝP¹ ≅ S¹`, with projection the squaring map.  `halfTurnPath` starts at `1`
and ends at `−1 ∈ K` (`halfTurnPath_one_mem`), and `responseLoop_eq_sq` shows its projection is the
once-around loop `responseLoop 1`.  `liftedAngle n` is the genuine mathlib path lift of
`responseLoop n` along the covering `Circle.exp : ℝ → Circle`, computed exactly by
`liftedAngle_eq`; `liftedAngle_one` gives endpoint `2πn`, `liftedAngle_one_zsmul` exhibits it as the
`n`-th deck translation, `liftedAngle_one_injective` gives the escape through distinct deck
transformations, and `responseLoop_not_nullhomotopicRel` concludes that the winding response loop is
not null-homotopic.  `closed_response_open_lift` bundles all six clauses.

**Corollary — positive phase erasure.**  `character_norm_one`: `‖χ(h)‖ = 1` for every `h`, so a
positive character norm is constant and carries no phase history.

`#print axioms` on `smul_eq_smul_iff_mem_stabilizer`, `markedResponse_injective`,
`markedResponse_isClosedEmbedding`, `oneParameter_recurrence`, `oneParameter_periodic`,
`liftPath_one_eq_of_nullhomotopicRel`, `monodromy_eq_self_iff_eq_one`, `stabilizer_markedAxis`,
`responseQuotientEquiv`, `closed_response_open_lift`, and `character_norm_one` reports only
`propext`, `Classical.choice`, and `Quot.sound`.
