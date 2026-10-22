# Marked Euler-shell Mellin–GNS, HT, recurrence, and normalization-wall law — Lean certificate

- **ID:** `cmr-marked-euler-shell-mellin-gns-ht-recurrence-wall-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `marked-euler-shell-mellin-gns-ht-recurrence-normalization-wall-law.md`
  (same directory).
- **Status:** `[UNCONDITIONAL]` `[NO SORRY / NO AXIOM / NO PROP INTERFACE]`

## Lean modules

- `formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/MarkedEulerShellSkeleton.lean`
  — §§2–3, the pure-prime skeleton and the moment object;
- `formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/MarkedEulerShellWall.lean`
  — §§4–5, 7–8, the Mellin–GNS realization, recurrence, the normalization wall and reporter
  nonfaithfulness.

Both live in namespace `HTGeometry.ConstraintMotiveRelativity` and are imported by
`GaloisForLFunctions.HTGeometry`.

The card's own Lean-return note listed the formal parents to reuse; they are imported rather than
re-derived:

- `RHTower/HighExponentShellZeroFree.lean` — `shellIndicator` (the mark `a_m`), `shellMultiplier`
  (`H_m`), `LSeries_shellIndicator` (`(ESG.22)`: `S_m = ζ·H_m`), `shellMultiplier_ne_zero` and
  `analyticAt_shellMultiplier` (zero-free holomorphy on `re s > 1/2` for `m ≥ 12`),
  `shellMultiplier_one_eq_ofReal_pos` (`(ESG.23)`);
- `RHTower/HighExponentShellCriticalClock.lean`, `RHTower/HighExponentShellClockMeasure.lean` —
  `shellMellin`, `shellMass`, `summable_shellMass`, `shellMellin_pos`, `shellProbability`,
  `hasSum_shellProbability`;
- `RHTower/HighExponentShellClockMoments.lean` — `shellLogMoment`, `ofReal_shellLogMoment`,
  `ofReal_shellMellin`;
- `RHTower/HighExponentShellHypertranscendence.lean` — §6's HT statement
  `highExponentShellArithmetic_differentialIndependent` and its `ζ`-relative form
  `zetaShellArithmetic_differentialIndependent`;
- `RHTower/DiagonalEllTwoOperator.lean`, `RHTower/Suzuki/SuzukiDiagonalResolventInstantiation.lean` —
  `diagonalOperator` and `isCompactOperator_diagonalOperator`;
- `ConstraintMotiveRelativity/PortRecurrenceJets.lean` — `portOrbit`,
  `isCompact_closure_range_portOrbit`, `portOrbit_recurrent`.

## Formal statement chain

### §2 — pure-power recovery and finite naturality

1. **`shellIndicator_prime_pow`** — `(ESG.2)`: the mark is one on every pure `m`-th prime power.
2. `shellJet` and **`shellJet_prime_pow`** — `(ESG.1)`, `(ESG.4)`: the diagonal prolongation
   `L = -δ` applied `k` times gives `(L^k a_m)(p^m) = (-m log p)^k`.
3. **`log_eq_shellJet`** — `(ESG.5)`: every prime logarithm is recovered from the marked skeleton.
4. `massCoeff`, `weilCoeff` and **`massCoeff_eq_shellJet`** `(ESG.7)`,
   **`weilCoeff_eq_shellJet`** `(ESG.8)`, **`primePhase_eq_shellJet`** `(ESG.9)` — the Mass
   half-density coefficient, the reflection-odd Weil tangent coefficient and the prime phase are
   all shell jets at `p^m`.
5. `chartDiag`, `chartMass`, `chartFlow`, `chartHistory`, `chartRestrict` — `(ESG.6)`: the finite
   prime chart with its diagonal clock, Mass vector, flow and logarithmic history.
6. **`chartRestrict_diag`**, **`chartRestrict_mass`**, **`chartRestrict_flow`**,
   **`chartRestrict_history`**, **`chartRestrict_comp`** — coordinate restriction commutes with
   every structure and restrictions compose: the comparison is pro-natural.

### §3 — the Mass/Weil moment object

7. `shellMoment` — `(ESG.10)`; **`shellMoment_eq_shellJet`** — `(ESG.11)`.
8. `primeWeight`, `primeWeight_pos` and **`hankel_quadratic`** — `(ESG.13)`: the moment Hankel form
   is the positive weighted sum of squares of polynomial values at the prime-log nodes.
9. `hankelBlock`, `shellGram`, **`hankelBlock_eq_gram`** and **`rank_hankelBlock`** — `(ESG.12)`:
   `rank H_R(F) = min(R+1, |F|)`.  The block is `AᵀA` for a weighted Vandermonde `A`; the upper
   bound is the two dimension bounds and the lower bound comes from an invertible
   `min(R+1,|F|)`-square weighted Vandermonde submatrix (`Matrix.det_vandermonde` at the distinct
   nodes `log p`).
10. **`exists_positive_moment_ambiguity`** — `(ESG.12)`, successor nonuniqueness: on `2R+2` distinct
    nodes two positive weight systems share every moment through `2R` and differ at `2R+1`.  The
    perturbation is the preimage of the last coordinate vector under the invertible full
    Vandermonde system.

### §4 — full positive shell and Mellin–GNS realization

11. **`shellIndicator_eq_rpow_mul_shellMass`**, **`shellIndicator_eq_shellMellin_mul_shellProbability`**
    — `(ESG.16)`: the marked pair `(Z, P)`, equivalently the unnormalized measure, is coefficient
    faithful.
12. `summable_shellMass_mul_log_pow`, `summable_shellProbability_mul_log_pow` — every logarithmic
    moment is admitted at `σ > 1`.
13. **`ofReal_shellMassMoment`** — `(ESG.17)`: `∫x^r dμ = (-1)^r S_m^{(r)}(σ)`.
14. `shellGNS`, `shellGNS_eq_shellLogMoment` and **`ofReal_shellGNS`** — `(ESG.18)`:
    `⟨D^iΩ, D^jΩ⟩ = (-1)^{i+j} S_m^{(i+j)}(σ)/S_m(σ)`.
15. **`shellGNS_quadratic`** and **`shellGNS_hankel_posDef`** — `(ESG.18)`: every finite Hankel
    block is strictly positive definite.  A nonzero polynomial cannot vanish at every logarithmic
    atom `log(p^m)`, because those form an infinite set
    (`Polynomial.eq_zero_of_infinite_isRoot`, `Nat.infinite_setOf_prime`) and each carries positive
    `P`-mass (`shellProbability_prime_pow_pos`).
16. **`shellCharacteristic`** — `(ESG.19)`: `⟨Ω, U_tΩ⟩ = S_m(σ+it)/S_m(σ)`.

### §5 — compact-resolvent recurrence with open lifted history

17. `shellVec`, `summable_normSq_shellVec`, `shellOrbit` — `(ESG.15)`: the observed orbit
    `U_tΩ` in the canonical coordinate model `ℓ²(ℕ)`.
18. **`isCompact_closure_shellOrbit`** — the orbit has compact norm closure.
19. **`shellOrbit_recurrent`** — the orbit returns to within `ε` of its start at arbitrarily late
    times.
20. **`shellGNS_two_pos`**, **`shellHistoryEnergy`** and **`tendsto_shellHistoryEnergy`** —
    `(ESG.20)`, `(ESG.21)`: the unwrapped logarithmic history has energy `t²·μ₂` with `μ₂ > 0`,
    hence divergent.
21. `norm_shellResolvent_le`, `tendsto_norm_shellResolvent` and
    **`isCompactOperator_shellResolvent`** — the logarithmic clock has compact resolvent: its
    diagonal resolvent entries `(log n + i)⁻¹` are bounded by one and tend to zero.

### §7 — the normalization wall

22. **`shell_pole_residue_pos`** — `(ESG.23)`: `H_m(1) = ζ(m+1)⁻¹ - ζ(m)⁻¹ > 0`.
23. **`normalization_forces_one`** — `(ESG.24)`: matching the pure-power radial weights
    `Z^{-1/2}(log p)p^{-mσ/2}` to the Mass weights `(log p)p^{-1/2}` up to one finite global
    normalization forces `mσ = 1`.  Two primes suffice: the logarithms of the two matchings differ
    by `log 2 - log 3 ≠ 0`.
24. **`normalization_wall`** — `(ESG.24)`: for `m ≥ 12` the matched abscissa satisfies `σ ≤ 1/12`,
    hence lies outside the convergence half-plane `σ > 1` of the shell measure.
25. **`not_summable_massCoeff_sq`** — `(ESG.25)`: `∑_p (log p)²/p = ∞`, so the target Mass vector
    itself has divergent squared norm.  Comparison with `(log 2)²·(1/p)` and
    `Nat.Primes.not_summable_one_div`.

### §8 — sharp reporter nonfaithfulness

26. `mixedPerturb`, **`prime_pow_ne_mixedAtom`** and **`mixedPerturb_prime_pow`** — the mixed-shell
    perturbation at `2^m·3` leaves every pure-power value, hence `(ESG.7)`–`(ESG.9)`, unchanged.
27. `summable_mixedPerturb_sub`, `summable_mixedPerturb`, **`tsum_mixedPerturb_sub`** and
    **`tsum_mixedPerturb_ne`** — the same perturbation changes the unnormalized measure by exactly
    one atom, so a nontrivial perturbation is detected by the unnormalized measure while being
    invisible to the pure-power reporters.

## Verification

```
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/MarkedEulerShellSkeleton.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/MarkedEulerShellWall.lean
lake build GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.MarkedEulerShellWall
```

Green with no warnings.  `#print axioms` on `shellIndicator_prime_pow`, `shellJet_prime_pow`,
`log_eq_shellJet`, `massCoeff_eq_shellJet`, `weilCoeff_eq_shellJet`, `primePhase_eq_shellJet`,
`chartRestrict_diag`, `shellMoment_eq_shellJet`, `hankel_quadratic`, `hankelBlock_eq_gram`,
`rank_hankelBlock`, `exists_positive_moment_ambiguity`,
`shellIndicator_eq_shellMellin_mul_shellProbability`, `ofReal_shellMassMoment`, `ofReal_shellGNS`,
`shellGNS_quadratic`, `shellGNS_hankel_posDef`, `shellCharacteristic`,
`isCompact_closure_shellOrbit`, `shellOrbit_recurrent`, `shellHistoryEnergy`,
`tendsto_shellHistoryEnergy`, `isCompactOperator_shellResolvent`, `shell_pole_residue_pos`,
`normalization_forces_one`, `normalization_wall`, `not_summable_massCoeff_sq`,
`mixedPerturb_prime_pow`, `tsum_mixedPerturb_sub` and `tsum_mixedPerturb_ne` reports only
`propext`, `Classical.choice`, `Quot.sound`.

## Scope notes

§6's genuine HT realization is not re-proved here: `(ESG.22)` is `RHTower.LSeries_shellIndicator`,
the holomorphic zero-free extension to `re s > 1/2` for `m ≥ 12` is
`RHTower.analyticAt_shellMultiplier` together with `RHTower.shellMultiplier_ne_zero`, and the joint
differential-algebraic independence over the differential field generated by `ζ` is
`RHTower.highExponentShellArithmetic_differentialIndependent`.  All are already Lean-proved in the
corpus and are imported by `MarkedEulerShellWall.lean`; duplicating them would be re-derivation.

§5's GNS space is realized in the canonical coordinate model `ℓ²(ℕ)` — the same model the card
itself uses in `(ESG.23a)` — rather than as `L²(P_{m,σ})` with an abstract measure.  The two are
unitarily identified by `f ↦ (√P_n · f(log n))_n` because `P_{m,σ}` is purely atomic with atoms
`log n`; every statement of §5 (compact resolvent, compact orbit closure, recurrence, divergent
lifted history) is a statement about that coordinate model.

`(ESG.24)` is formalized as the implication "matching all pure-power radial weights up to one
global constant ⟹ `mσ = 1`", which is the card's argument; the accompanying observation that the
matched fibre `σ = 1/m ≤ 1/12` lies where the shell measure is infinite is `normalization_wall`.
The divergence of `S_m(σ)` for real `σ ≤ 1` is the pole statement already carried by
`shell_pole_residue_pos` together with the pole of `ζ` at `1`.

§§9–11 are field consequences, hostile-loop bookkeeping and a corpus/literature boundary; they
claim no further theorem.
