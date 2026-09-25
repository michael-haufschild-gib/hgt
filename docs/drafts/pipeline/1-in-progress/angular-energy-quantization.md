# Angular energy quantization

Status: in progress (core law proved in Lean; the threshold bound is the open core)

## The move

The transverse-equilibrium chain ended at a *maximum* principle, and a maximum principle needs a
maximum: an attainment hypothesis `∃ρ₀ ∀ρ, Re ρ ≤ Re ρ₀` that nothing known supplies, and that the
ledger has independently identified as the intrinsic blind spot of every averaging argument.

The move is to stop using a maximum principle. Replace the extremal functional by an energy, which
has no extremal structure to attain.

For two distinct zeros put

    cos²θ(ρ,ρ') = (Re ρ − Re ρ')² / |ρ − ρ'|²,

the squared cosine of the angle of the segment joining them, measured from the real axis. Define the
**angular energy of a zero**

    E(ρ) = Σ_{ρ' ≠ ρ} cos²θ(ρ,ρ').

Every term lies in `[0,1]`. The sum converges for every `ρ`, because real parts are confined to the
critical strip, so `cos²θ ≤ 1/|ρ−ρ'|²`, and the zero network is locally finite.

The hypothesis holds exactly when every pair of zeros is joined by a vertical segment, i.e. when
`E ≡ 0`. That much is a restatement. The content is what follows.

## The quantum

Let `σρ = 1 − ρ̄` be the functional-equation partner. The segment from `ρ` to `σρ` is exactly
horizontal, of length `|2 Re ρ − 1|`. Its conductance `1/|ρ − σρ|²` and its squared displacement
`(2 Re ρ − 1)²` are reciprocal. Their product is

    cos²θ(ρ, σρ) = 1

for **every** off-line zero, independent of how close `Re ρ` is to `1/2`. Hence

    E(ρ) ≥ 1 whenever Re ρ ≠ 1/2,
    E(ρ) = 0 for all ρ when the hypothesis holds.

The energy is therefore quantized at the threshold: the family of angular energies never lies
entirely inside the open interval `(0,1)`. Either every zero sees every other zero vertically, or
some zero carries a full unit.

## Three consequences

1. **No attainment is used.** The chain `E < 1 ⟹ RH` quantifies over all zeros with a strict
   inequality. There is no maximum, no limit, no extremal zero, no escape-to-infinity case. The
   attainment obstruction was an artifact of the maximum principle, not a feature of the problem.

2. **The hypothesis is a threshold, not an equality.** Previous equivalents in this lane were exact
   identities — `Re(ξ''(ρ)/ξ'(ρ)) = 0`, vanishing Galois norm, slice cardinality `≤ 1`. Those are
   rigid: nothing weaker than the identity implies them. `E(ρ) < 1` is an inequality with a margin,
   and an unconditional upper bound anywhere below `1` would suffice. This is the first form of the
   hypothesis in this lane that an analytic estimate could in principle discharge.

3. **Deformation arguments provably cannot see it.** The partner term is `1` for every off-line `ρ`
   and `0` on the line. As a zero drifts toward the critical line its angular energy does not decay;
   it stays at least `1` and jumps to `0` only in the limit. Any argument whose functional is
   continuous under a motion of the zeros — the de Bruijn–Newman flow, `Λ → 0` continuity, any
   perturbative expansion in the off-line displacement — is measuring a quantity that is blind to
   this jump. That is an object-level reason, not an analogy, for the criticality wall already
   recorded in this field.

## Why the displacement cancels

The cancellation is exact because both the conductance and the displacement are homogeneous of
degree `−2` and `+2` in the off-line distance. The Cauchy kernel `1/|ρ−ρ'|²` carries conformal
weight zero against a squared length. Nothing in the geometry of the divisor is being used except
the functional equation, which forces the partner to lie *horizontally* opposite — and horizontal is
exactly the direction the kernel is scale-blind in. A zero at `Re ρ = 0.5001` and one at
`Re ρ = 0.9` are, in this energy, the same size.

## Open core

`[OPEN CORE]` An unconditional bound `E(ρ) < 1` for all zeros, or for even a single zero.

The difficulty is genuine and identifiable. Write

    cos²θ = 1/2 + (1/2) Re(Δ/Δ̄),   Δ = ρ − ρ'.

The second summand is not holomorphic in either zero, so the whole holomorphic toolkit of this
lane — Hadamard products, `ξ''/ξ'`, log-derivative expansions, the closed form
`Σ_{ρ'≠ρ} (ρ−ρ')⁻² = ξ''(ρ)²/(4ξ'(ρ)²) − ξ'''(ρ)/(3ξ'(ρ))` — computes `Σ Δ⁻²` and never `Σ Δ/Δ̄`.
The angular energy is a genuinely real-analytic functional of the divisor. This is a concrete
explanation for the saturation of the analytic toolkit recorded elsewhere: the missing object is not
a lemma but a non-holomorphic pairing.

## Lean

`formal/GaloisForLFunctions/RHTower/AngularEnergyQuantization.lean`, built on the locally-finite
network of `ZeroNetworkConductance`. Unconditional and axiom-clean.

## Relation to the rest of the lane

- The clock-degeneracy count `#slice = #fixed + 2·#left` is the cardinality shadow of this energy;
  the energy refines it by weighting each off-line pair by exactly one.
- The two-torsion reading (`RH = triviality of a ℤ/2-action`) says the free orbits are invisible to
  reflection-even readers. The angular energy is the first reader in this lane that is *odd enough*
  to see a free orbit and still converges: it reads each free orbit as the integer `1`.
- `TransverseAttainment.lean` retains the honest dichotomy from the maximum-principle route
  (identity + finite off-line set ⟹ hypothesis) as the record of what that route could reach.
