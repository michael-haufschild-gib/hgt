# Finite-clock fidelity WAY asymmetry

- **ID:** finite-clock-fidelity-way-asymmetry
- **Stage:** 3-formalized
- **Type:** PROVED IN LEAN / GENERAL HYPERTRANSCENDENCE BRIDGE / DISCRETE-CLOCK RESOURCE VALUE
- **Source:** quantitative Wigner--Araki--Yanase bounds for general symmetries
- **Statement:** For a normalized pure state of an involutive isometric clock, the squared fidelity deficit with its symmetry transform is exactly four times the product of its invariant and anti-invariant sector weights; logarithmic Sonin scattering satisfies the corresponding physical/nonphysical sector identity.

## Goal

Translate fidelity-based apparatus asymmetry from discrete-symmetry measurement theory into values
already native to the finite static clock geometry.  The relation must avoid symmetry generators
and must have a concrete logarithmic Sonin consumer.

## Gates

- [x] 0 → 1 in-progress: identified the transformed-state fidelity used by general quantitative WAY bounds
- [x] 1 → 2 fully-proven: derived the clock overlap, projective asymmetry, and squared-fidelity deficit from the two orthogonal clock sectors
- [x] 2 → 3 formalized: scratch certification, serialized exact-target builds, direct source checks, and axiom audit pass for both general and Sonin modules
- [ ] 3 → 4 publication-ready: construct a symmetry-constrained measurement or source-bearing observable implementation whose error term is represented in the existing corpus

## Physics source

A. Hokkyo and H. Tajima, *Quantitative Wigner-Araki-Yanase Theorems for Unitary and
Antiunitary Symmetries*, arXiv:2607.09075, proves fidelity-based lower bounds on the apparatus
asymmetry needed to implement symmetry-breaking projective measurements and unitary gates.  The
bounds apply to discrete unitary symmetries and do not require a continuous generator.

The Lean theorem is an exact evaluation of their pure-state asymmetry resource for the two-sector
clock geometry.  It does not formalize the paper's measurement/channel error inequality and makes
no novelty claim about WAY theory.

## Exact relation

Let `U` be an isometric involution and

```text
P = (1+U)/2,   a = P psi,   b = (1-P) psi.
```

Orthogonality gives `psi=a+b`, `U psi=a-b`, and hence

```text
<psi,U psi> = ||a||^2 - ||b||^2.                         (1)
```

For `||psi||=1`, write `A=||a||^2` and `B=||b||^2`.  Since `A+B=1`,

```text
1 - |<psi,U psi>|^2 = 1 - (A-B)^2 = 4 A B.              (2)
```

The left side is the squared pure-state fidelity deficit between the apparatus state and its
symmetry transform.  It is also the projective Gram distance between `psi` and `U psi`.  Thus the
entire discrete-clock asymmetry resource is the product of two static observability-sector weights.

For logarithmic Sonin scattering `S`, equation `(2)` becomes

```text
1 - |<psi,S psi>|^2
  = 4 ||P_S psi||^2 ||(1-P_S) psi||^2.                   (3)
```

## Formalization

`formal/GaloisForLFunctions/HTGeometry/FiniteInvolutiveClockFidelityAsymmetry.lean` proves:

- `inner_finiteInvolutiveClockTransform_eq_sectorNormSq_sub`;
- `finiteInvolutiveClock_projectiveAsymmetry_eq_four_mul_sectorWeights`;
- `finiteInvolutiveClock_pureStateFidelityDeficit_eq_four_mul_sectorWeights`.

`formal/GaloisForLFunctions/RHTower/SoninLogClockFidelityAsymmetry.lean` proves:

- `inner_soninLogFourierScattering_eq_sectorNormSq_sub`;
- `soninLogFourierScattering_pureStateFidelityDeficit_eq_four_mul_sectorWeights`;
- `soninLogFourierScattering_projectiveAsymmetry_eq_four_mul_sectorWeights`.

## Corpus value

The new relation gives the existing invariant/complement norm decomposition an operational
measurement-theoretic meaning that is exact rather than metaphorical.  Any later WAY-style error
bound for a finite clock can consume the native sector product directly; no generator variance,
continuous time parameter, or new fidelity hypothesis is needed.

The Sonin consumer distinguishes three regimes immediately: physical or anti-invariant states have
zero fidelity asymmetry, while maximal reference-frame asymmetry occurs at equal physical and
nonphysical weights.  A stationary constrained state is therefore not itself a symmetry-breaking
clock reference.  Any successful observer implementation must place the asymmetry in an apparatus
or observable sector outside the physical state, matching the existing clock-observability split.

## Status

[PROVED IN LEAN] Both exact targets and direct source checks pass.  The audited theorems use only
Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.  No numerical computation,
full project build, or concurrent Lean process was run.
