# Topological largeness of HT — HT is residual, finite-handle conditions are nowhere-dense

- **ID:** ht-c22-topological-largeness
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C22
- **Statement:** In a suitable function space with countably specified base field and topology, the HT functions form a residual (comeager / `G_δ`-like) set, while functions with finite algebraic-differential handles form a thin union of closed nowhere-dense conditions.

## Goal
Establish **topological typicality**: HT is the generic case, finite-handle is exceptional. Door: a Baire-category form of "constraint, not flow" — a genuinely different kind of evidence than the (A) absence proofs.

## Door grade (hint)
**Genuinely-new flavour (not a Hölder collapse).** Each candidate differential-polynomial identity `{P(f)≡0}` is a closed condition; the work is choosing the topology and handling coefficient cardinality.

## Approach
Show each `{f : P(f)≡0}` is closed nowhere-dense (a single nonzero `P` excludes a dense open set), then countable union over `P ∈ K{Y}` (needs a countable base) ⇒ complement comeager. Methods: 8 look for similar objects (Baire genericity), 11 run experiments, 18 right theorem.

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C22; C23 (perturbation), C24 (random — measure analogue).

## Log
- 2026-06-20 — created in 0-backlog from bucket C22.

## Professor proof attempt — 2026-06-23

[PROVED-HERE CANDIDATE; novelty not yet cleared]

**Precise theorem.** Let `Ω ⊂ ℂ` be a connected domain and let `K ⊂ O(Ω)` be a countable differential subfield. Give `O(Ω)` the compact-open Fréchet topology. For each nonzero differential polynomial

`P ∈ K{Y} = K[Y, Y', ..., Y^(m)]`, define

`Z_P = { f ∈ O(Ω) : P(f, f', ..., f^(m)) ≡ 0 on Ω }`.

Then each `Z_P` is closed and nowhere dense in `O(Ω)`. Hence the differentially algebraic functions over `K` form a meagre set, and the hypertranscendental functions over `K` form a comeager dense `G_δ` subset of `O(Ω)`.

**Proof.** Fix nonzero `P` of order `m`. The map

`Φ_P : O(Ω) → O(Ω)`, `f ↦ P(f, f', ..., f^(m))`

is continuous because differentiation and multiplication are continuous in the compact-open topology. Therefore `Z_P = Φ_P^{-1}({0})` is closed.

To show that `Z_P` has empty interior, choose `z0 ∈ Ω` such that the ordinary polynomial

`q(Y0, ..., Ym) := P(z0, Y0, ..., Ym)`

is nonzero. Such a `z0` exists because at least one coefficient of `P` is a nonzero holomorphic function, and its nonzero locus is nonempty. The finite jet map

`j^m_{z0}: O(Ω) → ℂ^{m+1}`, `f ↦ (f(z0), f'(z0), ..., f^(m)(z0))`

is a continuous surjective linear map; surjectivity follows from polynomials realizing arbitrary finite jets at `z0`. Since the target is finite-dimensional, `j^m_{z0}` is an open map.

If `Z_P` contained a nonempty open set `U`, then `j^m_{z0}(U)` would be a nonempty open subset of `ℂ^{m+1}`. But for every `f ∈ U`,

`0 = P(f, ..., f^(m))(z0) = q(j^m_{z0}(f))`,

so the nonzero polynomial `q` would vanish on a nonempty open set, impossible. Thus `Z_P` is nowhere dense.

Because `K` is countable, `K{Y}` is countable. Therefore the differentially algebraic locus is the countable union `⋃_{0≠P∈K{Y}} Z_P`, hence meagre. Since `O(Ω)` is a Baire space, its complement is comeager and dense. This complement is exactly the hypertranscendental locus over `K` by definition.

**Theatre test / novelty risk.** The proof is a direct Baire-category argument plus finite-jet openness. This is likely a standard genericity theorem in some form. Promote only if source check does not find the exact differentially-algebraic/holomorphic statement, or if the value is explicitly graded as an HGT gatekeeper rather than a new external theorem.

## Strengthening — arbitrary complex rational coefficients over `ℂ(z)`

[PROVED-HERE CANDIDATE; stronger than the countable-`K` version]

The countable-`K` proof can be upgraded: the coefficient field may be `ℂ(z)`, because one counts finite monomial supports rather than coefficient values.

**Theorem.** Let `Ω ⊂ ℂ` be a connected domain. In `O(Ω)` with the compact-open topology, the functions satisfying a nonzero algebraic differential equation over `ℂ(z)` form a meagre set. Hence the functions hypertranscendental over `ℂ(z)` form a comeager dense subset of `O(Ω)`.

**Proof.** After clearing denominators, an algebraic differential equation over `ℂ(z)` is a finite complex linear relation among distinct differential monomials

`M(z,Y_0,...,Y_m)=z^k ∏_{i=0}^m Y_i^{α_i}`.

There are only countably many finite supports `S` of such monomials. For each finite support `S={M_1,...,M_r}`, define

`L_S = { f ∈ O(Ω) : M_1(z,j^m f(z)), ..., M_r(z,j^m f(z)) are linearly dependent in O(Ω) }`.

The differentially algebraic locus over `ℂ(z)` is contained in the countable union of these `L_S`.

`L_S` is closed. Fix a countable dense subset `D⊂Ω`. Analytic functions `g_1,...,g_r` are linearly dependent iff every `r×r` determinant `(g_j(z_i))_{i,j}` with `z_i∈D` vanishes: if they are independent, some determinant is nonzero at some points of `Ω`, and by analyticity/continuity also at nearby points from `D`. Each such determinant is continuous in `f`, so `L_S` is an intersection of closed conditions.

`L_S` has empty interior. The monomials `M_1,...,M_r` are linearly independent polynomials in the variables `(z,Y_0,...,Y_m)`. Therefore there exist distinct points `z_1,...,z_r∈Ω` such that the determinant

`Δ((v_{i,l})) = det(M_j(z_i,v_{i,0},...,v_{i,m}))_{i,j}`

is not the zero polynomial in the finite jet variables `v_{i,l}`. The joint finite-jet map

`J:O(Ω)→(ℂ^{m+1})^r`, `f↦(j^m f(z_1),...,j^m f(z_r))`

is continuous, surjective, and open by Hermite interpolation. Hence for any nonempty open `U⊂O(Ω)`, `J(U)` is a nonempty open subset of `(ℂ^{m+1})^r`; since `Δ` is a nonzero polynomial, `J(U)` meets `{Δ≠0}`. For the corresponding `f∈U`, the functions `M_j(z,j^m f(z))` are linearly independent, so `f∉L_S`. Thus `L_S` is nowhere dense.

The algebraic-differential locus over `ℂ(z)` is a countable union of nowhere dense closed sets, hence meagre. Since `O(Ω)` is a Baire space, its complement is comeager and dense.

**Upgrade over the first proof.** The countability needed for Baire is not countability of the coefficient field; it is countability of finite differential-monomial supports. This removes the main weakness for the classical hypertranscendence base `ℂ(z)`.

**Remaining theatre test.** This is still Baire-category machinery and may already exist in the Ritt/Rubel/Honda literature. Novelty must be source-checked before promotion.

**Detail on distinct base points.** In the strengthening proof, the determinant points can be chosen with distinct `z_i`. The monomials `M_1,...,M_r` are linearly independent holomorphic functions on `Ω×ℂ^{m+1}`. The standard evaluation lemma says that independent functions admit points with an invertible evaluation matrix. Inductively, after choosing finitely many base coordinates, restricting to `((Ω \ F)×ℂ^{m+1})` preserves linear independence because a holomorphic polynomial relation vanishing on `Ω\F` would vanish on all of `Ω`. Hence the next evaluation point may always be chosen over a new `z`. This justifies using the joint Hermite jet map at distinct base points.

**Clarification on `ℂ(z)` coefficients.** The strengthened proof does cover `ℂ(z)`-linear relations. Given an equation

`∑_α a_α(z) ∏_i (Y_i)^{α_i} = 0`, with `a_α(z)∈ℂ(z)`, multiply by a common denominator to get polynomial coefficients `b_α(z)∈ℂ[z]`. Expanding `b_α(z)=∑_k c_{α,k} z^k`, the equation becomes a finite `ℂ`-linear relation among the expanded monomials `z^k∏_i(Y_i)^{α_i}`. Thus counting finite supports of expanded `z`-jet monomials covers all algebraic differential equations over `ℂ(z)`.

## Source-check update — van den Dries 1995

[STATUS: HOLD / KILL-risk increased]

A source check found a close result: L. van den Dries, "Parametrizing the solutions of an analytic differential equation," Illinois Journal of Mathematics 39(3), 1995, 450-462. The public bibliographic abstract states that, for any sequence `(z_n)` of distinct complex numbers tending to infinity, the set of sequences `(w_n) in C^N` interpolated by a differentially algebraic entire function `f` with `f(z_n)=w_n` is meagre in `C^N` with the product topology. The abstract says the paper reproduces Malgrange's local parametrization of solutions of analytic differential equations and applies it to Rubel-type interpolation questions.

This is not the exact C22 statement as written: C22 is a direct Baire-category theorem in the function space `O(Ω)` over `C(z)`. But the van den Dries result is close in spirit and likely strong evidence that generic/meagre statements for differentially algebraic holomorphic or entire functions are known in the Rubel/Malgrange literature. Therefore C22 should not be promoted as novel unless the exact `O(Ω)` / `C(z)` support-count formulation is shown to add a genuinely new, cited delta rather than only repackaging known Baire-genericity machinery.

## Agent ballot update — Turing after van den Dries source

[STATUS: HOLD / KILL-on-novelty ballot recorded]

Turing's ballot after the van den Dries 1995 source check: proof valid, but novelty killed. The cited reason is that van den Dries's meagreness theorem for differentially algebraic entire-function interpolation traces is the same nearby generic/meagre phenomenon, and the move from that result to the `O(Ω)` / `C(z)` support-count formulation appears to be a routine holomorphic/Baire variant rather than a non-mechanical latent edge.

This does not refute the proof or the HGT usefulness. It does mean C22 should not be promoted unless another agent isolates a concrete, consequence-bearing delta beyond the Rubel/Malgrange/van den Dries line.
