# Route Q mixed-incidence diagonal-budget no-go

- **ID:** `route-q-mixed-incidence-diagonal-budget-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM / source-polarization blow-up and strategy no-go
- **Routes:** Q primary
- **Source:** exact boundary hyperbolic plane and positive separated prime--Gamma saturation

## Status labels

`[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NO RH CLAIM]`

## Result

For Xi--Weil carrier vectors define real mixed incidence

```text
B(x,y) = Re <Jx,y>.
```

For actual finite separated continued-Cauchy packets `P,Q`, exact fusion polarization is

```text
Q(P.eval + Q.eval)
  = P.sourceEnergy + Q.sourceEnergy + 2 B(P.eval,Q.eval).   (Q-MIX)
```

The two canonical Route-Q null boundaries have exact mixed incidence

```text
B(b_plus,b_minus) = -xiHurwitzOrientationEnergy/2.         (Q-BOUND)
```

Hence every pair of separated packet reconstructions `P_n -> b_plus`, `Q_n -> b_minus` obeys

```text
B(P_n.eval,Q_n.eval) -> -E/2,
```

independently of packet choices and diagonal source signs.

The strongest closed form is unconditional:

```text
RH
or
there exist actual separated prime--Gamma packets P_n,Q_n such that
  sourceEnergy(P_n) > 0,
  sourceEnergy(Q_n) > 0,
  sourceEnergy(P_n), sourceEnergy(Q_n) -> 0,
  B(P_n.eval,Q_n.eval) -> -E/2,
  for every C>0, eventually
    C sqrt(sourceEnergy(P_n) sourceEnergy(Q_n)) < -B(P_n.eval,Q_n.eval).
```

Thus off RH the normalized negative mixed incidence diverges relative to every fixed geometric-
mean diagonal budget. No Cauchy--Schwarz-style inequality built from two diagonal source energies
can control target-aligned fusion.

## Heavy conjecture loop

### Q-M1 — positive diagonal boundary energies should control fusion cross term

**Conjecture.** Since both exact source packet sequences have positive energy, a uniform bound
`|B(P,Q)| <= C sqrt(Q(P)Q(Q))` may prevent fusion negativity or yield cofinal recurrence.

**Attack.** Polarize exact Xi--Weil quadratic, compute boundary value from
`Q(b_plus+b_minus)=-E`, and pass to arbitrary packet reconstructions by continuity.

**Verdict:** false maximally. Numerator tends `E/2` while both positive diagonal energies tend
zero, so every fixed `C` is eventually violated off RH.

### Q-M2 — failure may depend on badly chosen boundary approximants

**Conjecture.** Canonical or source-adapted packet choices could make mixed incidence vanish with
diagonal energies.

**Attack.** Mixed incidence is continuous and both target limits are fixed. Its limit is therefore
choice-independent for every pair of separated reconstructions.

**Verdict:** false. Limit `-E/2` is universal.

### Q-M3 — transverse compensation can be inferred from diagonal recurrence

**Conjecture.** Repeated returns of individual packets to positive chamber contain enough data to
reconstruct required reflection-fixed transverse budget.

**Attack.** Existing strictly positive boundary sequences already provide maximal diagonal
recurrence, yet `(Q-MIX)` and `(Q-BOUND)` force fused negative limit. The missing quantity stays
order one while diagonal budgets vanish.

**Verdict:** false. Mixed incidence is independent source coordinate, not bounded error term.

## Higher universal principle

**Null-boundary polarization in an indefinite source form is singular relative to diagonal
energy.** Two null rays can have finite nonzero mutual pairing; approaching them from positive
chamber drives diagonal energies to zero without shrinking cross incidence. Reasons Route Q got
stuck are shadows of this Krein-boundary principle: diagonal source energy is not a norm and cannot
support Cauchy--Schwarz control near null cone.

Route Q must therefore retain or construct a positive-definite reflection-fixed incidence norm
before diagonalization. Exact next target is not stronger recurrence of two scalar source
energies. It is source-first control of the fixed projection `x+Jx`, or an equivalent mixed
theta/prime--Gamma coordinate capable of paying full `E` budget from transverse-compensation law.

## Lean closure

Module:

- `formal/GaloisForLFunctions/RHTower/XiHurwitzOrientationBoundaryMixedIncidence.lean`.

Capstones:

- `xiWeilHilbertQuadratic_packetFusion_eq_sourceEnergy_add_mixed`;
- `xiWeilMixedIncidence_orientationBoundaries`;
- `tendsto_xiWeilMixedIncidence_boundaryPackets`;
- `eventually_mixedIncidence_neg_dominates_sourceGeometricMean_of_not_rh`;
- `riemannHypothesis_or_exists_positiveBoundaryPackets_mixedIncidenceDominates`.

Direct `lake env lean` passed. Exact leaf `lake build
GaloisForLFunctions.RHTower.XiHurwitzOrientationBoundaryMixedIncidence` passed. Axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`. Module is imported by `RHTower.lean`; no
umbrella build was run.

## Gates

- [x] 0 -> 1: diagonal-control, choice-dependence, and recurrence conjectures attacked
- [x] 1 -> 2: dependency-closed proof and corpus collision audit
- [x] 2 -> 3: direct Lean check, exact leaf build, axiom audit, umbrella wire
- [ ] 3 -> 4: independent significance audit and standalone exposition

## Log

- 2026-08-16 — Exact packet fusion polarization isolated.
- 2026-08-16 — Boundary mixed incidence computed as `-E/2`.
- 2026-08-16 — Choice-independent mixed limit proved for arbitrary separated reconstructions.
- 2026-08-16 — Geometric-mean diagonal domination proved off RH.
- 2026-08-16 — Unconditional RH-or-source-instability dichotomy formalized.
