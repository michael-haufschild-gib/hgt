# Completed flux germ has a fixed all-order reflection law

- **ID:** completed-flux-cross-order-reflection
- **Stage:** 3-formalized
- **Type:** NOT-NEW / CROSS-ORDER BRIDGE
- **Source:** RHTower `SeamFluxCompletion` + `CompletedPrimeFluxFittingAttachment`
- **Statement:** `[PROVED]` Multiplying the completed flux `-ξ'/ξ` by the local coordinate and filling in the residue produces a canonical analytic germ at every point. The germ at `1-ρ`, expressed in the reflected local coordinate, equals the germ at `ρ`; hence one fixed Taylor-coefficient sequence satisfies every truncation simultaneously. At the central fixed point the germ is even and every odd Taylor coefficient vanishes.

## Goal

Construct the order-independent object demanded by the finite-prime jet no-go.  Unlike a family of
separately solved polynomial packets, this is one analytic germ whose complete Taylor sequence is
fixed before any truncation is selected.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: analytic removability and reflection proof complete
- [x] 2 → 3  formalized: focused build green, axiom audit PASS
- [ ] 3 → 4  publication-ready: requires arithmetic/Fitting integration and significance audit

## Definitions

Let `Ω(s)=-logDeriv ξ(s)`.  At `ρ`, define the local completed-flux germ by

`G_ρ(x) = x Ω(ρ+x)` for `x ≠ 0`, and
`G_ρ(0) = -ord_ρ(ξ)`.

The existing local factorization of `ξ` makes this singularity removable.

## Approach

1. Use the peeled factorization `ξ(z)=(z-ρ)^m h(z)` with `h` analytic and nonzero.  Locally,
   `G_ρ(x)=-m-x logDeriv h(ρ+x)`, which is analytic at zero and agrees with the piecewise
   definition there and off zero.
2. Completed-flux reciprocity gives `Ω(1-s)=-Ω(s)`, while order pairing gives
   `ord_(1-ρ)(ξ)=ord_ρ(ξ)`.  Therefore `G_(1-ρ)(-x)=G_ρ(x)` for every `x`.
3. Define the full Taylor sequence by iterated derivatives at zero.  Functional equality makes the
   paired sequences equal at every order, not just at a selected finite jet.
4. At `ρ=1/2`, reflection fixes the base point, so `G(-x)=G(x)` and odd derivatives vanish.

## Honest boundary

This supplies the missing fixed cross-order FE object.  It does not yet prove that the continued
finite-prime component alone maps nontrivially into the pinned-affine quotient, nor does its
existence force RH; those remain separate arithmetic and positivity obligations.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/CompletedFluxCrossOrderReflection.lean`
- Removability: `completedFluxGermAt_analyticAt_zero`
- Pointwise FE law: `completedFluxGermAt_reflection`
- All-order coefficient law: `completedFluxTaylorCoeff_reflection`
- Central odd vanishing: `completedFluxTaylorCoeff_central_odd_eq_zero`
- Build: `lake build GaloisForLFunctions.RHTower.CompletedFluxCrossOrderReflection` PASS
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
