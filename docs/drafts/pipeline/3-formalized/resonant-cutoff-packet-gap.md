# Hecke gap for cutoff packets

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [arithmetic measure rigidity](../1-in-progress/resonant-state-arithmetic-measure-rigidity.md).

## Statement

Fix an actual resonant parameter `u`, with `-1/2<a=Re u<0`, `Im u>0`, and
`msA u=0`. For arbitrary finite complex coefficients `c_j` and heights `Y_j≥2`,
set `F=Σ_j c_j Λ_aut^(Y_j) E_u` and `λ=2^u+2^(-u)`. Then

`||(T₂−λ)F||² ≥ (2^a+2^(-a)−2)² ||F||²`.

Both norms are the original modular integrals on `fd`. The coefficient is
strictly positive for `a<0`, independently of the ordinate, coefficients,
number of terms, and cutoff heights.

## Proof

The exact joint cutoff Gram identity sends the packet to

`G(y)=Σ_j c_j B(u)y^(-u-1/2) 1_(0,Y_j](y)` in `L²(ℝ)`.

At every `Y_j≥2`, modular returns vanish. The genuine automorphic Hecke
residual has three cutoff terms, at `2Y_j`, `Y_j/2`, and `Y_j`. All are at
least one, so the same Gram identity transfers its full squared norm,
including every interference term.

Normalized dilation `DG(y)=√2 G(2y)` is unitary and satisfies
`D cuspCutoff(u,Y)=2^(-u) cuspCutoff(u,Y/2)`. Thus the transferred residual
is `(D+D⁻¹−λ)G`. For `q=2^u≠0`,

`D+D⁻¹−(q+q⁻¹) = −q⁻¹(D−q)(D⁻¹−q)`.

Applying the reverse triangle inequality to both factors gives

`||(D+D⁻¹−λ)G|| ≥ (|q|+|q|⁻¹−2)||G||`.

Since `|q|=2^a`, squaring proves the theorem. Strict positivity follows from
`r+r⁻¹−2=(1−r)²/r` with `0<r=2^a<1`.

## Positive survivor and scope

The exact residual isometry identifies the surviving source with the two
inverse unitary dilations and their scalar subtraction. It retains the full
packet and every cross term, rather than separate lower bounds on its summands.

Consequently, finite complex superpositions of cutoffs at least two cannot
cancel the normalized Hecke source at a fixed negative rate. This includes
the critical rate and supplies no critical-line selector. Packets using
cutoffs below two, and passage to arbitrary smooth profiles, require separate
statements. The arithmetic measure-rigidity problem remains open.

## Lean and audit

Modules in `RenormalizedIntersectionTheory/ResonantStates`:

- `CutoffDilation`: `cuspCutoff_memLp`, `cuspCutoff_dilation`,
  `unitary_pair_gap`, `dyadic_packet_gap_pos`.
- `CutoffPacketModel`: `cuspPacket_memLp`, `cuspPacket_residual_gap`.
- `CutoffPacketResidual`: `automorphicCutoffPacket_residual`,
  `cutoffPacket_residual_isometry`, `automorphicCutoffPacket_norm_eq`,
  `automorphicCutoffPacket_residual_gap`.

Direct Lean checks passed. The final automorphic theorem, residual isometry,
cusp-model bound and strict gap positivity have only `propext`,
`Classical.choice`, and `Quot.sound` as transitive axioms. The three modules
are imported by the umbrella.
