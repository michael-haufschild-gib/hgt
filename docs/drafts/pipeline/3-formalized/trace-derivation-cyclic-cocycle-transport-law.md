# Trace-derivation cyclic cocycle transport law

- **ID:** `trace-derivation-cyclic-cocycle-transport-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — universal law + connector
- **Source:** literature sweep (arXiv 2606.30513 *On the Cohomology of Cyclic Associative Algebras*,
  which places an intermediate theory between `HC^•` and `HH^•`) tested against Route R's
  `route-r-kummer-cyclic-one-cocycle-detector`
- **Statement:** for any associative ring with an additive trace `τ` and an additive derivation `D`,
  `φ(a,b) = τ(a·Db)` is a Hochschild one-cocycle; it is antisymmetric **iff** `τ∘D = 0` on products;
  and any additive multiplicative map intertwining the derivations and pulling back the trace pulls
  back `φ`, hence cannot annihilate anything on which `φ` is nonzero.

## Goal

Route R's KCC-1/KCC-2 proved cyclic antisymmetry and Hochschild-boundary annihilation for one
specific pair `(ε₀, ∂_ℓ)` on the rational adelic cyclic source, by hand. The remaining producer is

> construct the all-degree source-to-Xi comparison and prove it preserves `φ_ℓ`;
> degree-one rotation compatibility is insufficient.

That obligation was stated but had no reduction. This card supplies both the universal law that
KCC-1/KCC-2 instantiate, and the reduction of "preserves `φ_ℓ` and is coefficient-faithful on the
ordinary-prime top atom" to two intertwining equations.

## Gates

- [x] 0 → 1 in-progress: general model frozen (non-unital associative ring, additive trace and
      derivation, additive target group)
- [x] 1 → 2 fully-proven: complete algebraic proof; no analytic input, no unitality
- [x] 2 → 3 formalized: Lean modules below, axiom audit `[propext, Classical.choice, Quot.sound]`
- [ ] 3 → 4 publication-ready: not intended as standalone publication

## The law

Let `A` be a non-unital associative ring, `K` an abelian group, `τ : A →+ K`, `D : A →+ A`.
Put `φ(a,b) = τ(a · D b)`.

1. **Hochschild cocycle.** If `τ` is a trace and `D` a derivation, then for all `a,b,c`
   `φ(ab,c) - φ(a,bc) + φ(ca,b) = 0`. *Annihilation of the derivation by the trace is not needed
   here.*
2. **Antisymmetry criterion.** `(∀ a b, φ(a,b) = -φ(b,a)) ⟺ (∀ a b, τ(D(a·b)) = 0)`.
   So the hypothesis `τ ∘ D = 0` used in KCC-1 is exactly equivalent to cyclicity, not an artefact.
3. **Transport.** If `f : A →+ B` is multiplicative, `D_B ∘ f = f ∘ D_A`, and `τ_B ∘ f = τ_A`, then
   `φ_B(f a, f b) = φ_A(a,b)`.
4. **Non-erasure.** Under the hypotheses of 3, `φ_A(a,b) ≠ 0` forces `f a ≠ 0`, `f b ≠ 0`, and
   `φ_B(f a, f b) ≠ 0`.

## Route R consequence

Instantiating at `(ε₀, ∂_ℓ)` on `CCMRationalAdelicCyclicSourceAlgebra` recovers KCC-1 and KCC-2 as
corollaries, and the retained ordinary-prime atom has `φ_ℓ(u_p U_p, u_p U_{p⁻¹}) = -log p ≠ 0`.

Therefore, for **any** target ring `B` with a trace `τ_B` and derivation `D_B`, and any additive
multiplicative comparison `f` with

```text
D_B ∘ f = f ∘ ∂_ℓ        and        τ_B ∘ f = ε₀,
```

both legs of the ordinary-prime atom survive `f` and the transported cocycle value is exactly
`-log p`. Gate 3 of the `POLARIZED_ADELIC_STOKES` conjecture ("coefficient-faithful on the
ordinary-prime top atom") is thus *not* an extra requirement: it is implied by the two intertwining
identities. The producer is now exactly:

> exhibit a target `(B, τ_B, D_B)` reading the fixed Xi physical residue, and a multiplicative
> additive `f` with `D_B ∘ f = f ∘ ∂_ℓ` and `τ_B ∘ f = ε₀`.

Combined with `adelic-phase-defect-character-blindness-law`, the shape of the remaining work is
pinned from both sides: the comparison must transport the phase (defect-level data is provably
blind), and if it does transport it, non-erasure is automatic.

## Lean

- `formal/GaloisForLFunctions/HTGeometry/TraceDerivationCyclicCocycleLaw.lean`
  - `IsAlgebraTrace`, `IsAlgebraDerivation`, `traceDerivCocycle`
  - `traceDerivCocycle_antisymm_iff`, `traceDerivCocycle_antisymm`, `traceDerivCocycle_boundary`
  - `traceDerivCocycle_comp`, `ne_zero_of_traceDerivCocycle_ne_zero_left`,
    `ne_zero_of_traceDerivCocycle_ne_zero_right`, `traceDerivCocycle_image_ne_zero`
- `formal/GaloisForLFunctions/RHTower/RouteRCocycleTransportNonErasure.lean`
  - `ccmEpsilonZeroAdd_isAlgebraTrace`, `ccmKummerDerivAdd_isAlgebraDerivation`
  - `ccmKummerTraceDerivCocycle_antisymm`, `ccmKummerTraceDerivCocycle_boundary`
  - `ccmKummerTraceDerivCocycle_primeAtom`, `ccmKummerTraceDerivCocycle_primeAtom_ne_zero`
  - `ccmKummerTraceDerivCocycle_transport`, `primeAtom_not_erased`,
    `primeAtom_transported_value`

## Falsifier

Produce a trace `τ`, derivation `D`, and elements `a,b,c` with
`φ(ab,c) - φ(a,bc) + φ(ca,b) ≠ 0`; or a comparison satisfying both intertwining identities that
kills a leg of the ordinary-prime atom. Item 1 and item 4 exclude both.

## Log

- 2026-08-05 — created directly at stage 3; universal law and Route R instantiation formalized
