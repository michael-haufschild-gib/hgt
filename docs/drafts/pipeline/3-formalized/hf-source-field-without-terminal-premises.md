# HF: the source field at every zero

- **ID:** hf-source-field-without-terminal-premises
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); source-identification bridge
- **Parent goal:** close HF unconditionally in Lean; this card does not redefine that goal.
- **Source:** `rh-current-frontier-map.md`, HF; `review-2710/route-obstacles.md`, §§1.1–1.3.

## Exact target

For every actual Xi zero copy `p`, write `ρ = p.1` and
`m = (xiZeroCopyFiber p.1).card`. Prove, without a terminal, right-half-plane,
simplicity or RH premise,

    xiTransverseField p =
      Re (laurentCoeff ((ζ′/ζ)²) ρ (-1) / (2m)) + Re (archFactor′/archFactor)(ρ).

Then identify the source work on finite collections with the corresponding
pair interaction and its explicitly retained exterior contribution. The
arithmetic source is the actual `Λ ⋆ Λ`, not a freely chosen coefficient sequence.

## Evidence and scope

Corpus search located `XiTerminalRegularField`: its regular-part existence and
absolute field convergence hold for every zero, but its field/source identification
requires a right quadratic terminal. The sole use of that restriction in the latter
proof is nonvanishing along a short outward ray. Isolation of an actual zero
discharges this restriction locally.

This is a source-identification bridge, not an arithmetic upper bound, not a new RH
criterion, and not proof of the user's requested significant closing estimate. In
particular, positive coefficients of `Λ ⋆ Λ` do not control its Laurent coefficient
inside the critical strip. The unit-charge energy in `TheTransverseEnergyOfTheZeroDivisor`
also must not be silently substituted for the multiplicity-weighted field here.

## Paper proof

1. The entire function `xi` is not identically zero (`xi_one`). The analytic identity
   theorem therefore gives a punctured zero-free neighbourhood of every `ρ`.
2. Approach `ρ` along `ρ+h`, `h↓0`, inside the critical strip and this neighbourhood.
3. Apply the absolutely convergent deflated reciprocal-field limit and the completed
   logarithmic derivative identity. Their limits identify the regular part at `ρ`.
4. Use the square's exact Laurent coefficient `2m B(ρ)` and the positive actual
   multiplicity to eliminate the auxiliary analytic regular part.
5. Keep the signed exterior interaction in any finite-window work formula.

More explicitly, set `K(p,q) = (Re p − Re q)/|p−q|²`, with the own-fibre
term interpreted as zero, and `δ(p) = Re p−1/2`. Existing
`xiTransverseField_norm_summable` proves absolute convergence for each row,
including multiplicity copies. For any finite set `S` of copies, split each row
into `S` and its complement. Since `K(q,p) = −K(p,q)`, exchanging the two finite
indices gives

    Σ(p∈S) δ(p) Σ(q∈S) K(p,q)
      = (1/2) Σ(p,q∈S) (δ(p)−δ(q)) K(p,q)
      = (1/2) Σ(p,q∈S) (Re p−Re q)²/|p−q|².

Consequently the source residue work is this finite energy plus
`Σ(p∈S) δ(p) Σ(q∉S) K(p,q)`. No interchange of two infinite sums is used.
No simplicity or finite off-line-support assumption is needed. The exterior
term is retained with its sign; dropping it would not follow from this proof.
This closes the dependencies of the two identities, not of the upper-bound core.

## Open core

Prove an arithmetic upper bound for this actual source field below the outward
terminal reserve, or prove full Weil positivity / vanishing Hecke defect directly.
Neither the source identity nor a finite-window identity supplies that bound.
No external search or novelty audit is being performed, as requested.

### Upper-bound attempt

Inspected the statements behind corpus searches for regular-part and logarithmic-
derivative upper bounds. `Sieve.ZetaLogDerivThreeFourOne.re_logDeriv_shift_le`
requires `1 < σ`: the arithmetic positivity argument is in the absolutely
convergent half-plane, not at a terminal inside the strip.
`ZetaTypicalLocalZeroCount.re_logDeriv_xi_le_of_norm_logDeriv_zeta_le` requires
the interior logarithmic-derivative bound `hB` as input.
`Sieve.ZetaLogDerivRegUniform.exists_bound_zetaLogDerivReg_uniform` controls
the pole-subtracted function near `Re s = 1`; it is not a bound for the zero's
regular part at arbitrary depth. None discharges the closing upper bound.
Extending a positive-coefficient inequality into the strip by analytic
continuation would require a separate sign argument; equality continuation
alone does not do it. This is an unresolved proof step, not a retired route.

## Verification

- [x] Dependency-closed paper proof of source identification and finite-window identity.
- [x] New module checked with `lake --old env lean` (exit 0).
- [x] `#print axioms` for both principal theorems reports only
  `propext`, `Classical.choice`, `Quot.sound`.
- [x] `ArithmeticCorrespondencePositivity.lean` imports the new module;
  the umbrella was not compiled.

Module: `GaloisForLFunctions/ArithmeticCorrespondencePositivity/EveryXiZeroHasASourceField.lean`.
Principal declarations:

- `xiSourceField_eq_transverseField`: actual source field at every zero, no terminal premise.
- `xiSourceField_finite_work`: exact multiplicity-weighted finite energy and exterior work.

Final audit, run from `formal/`:

    lake --old env lean GaloisForLFunctions/ArithmeticCorrespondencePositivity/EveryXiZeroHasASourceField.lean

**Assessment: BRIDGE.** Source identification extends to all zeros; no arithmetic
upper bound, full Hodge sign, vanishing defect, or RH theorem has been proved.
The full HF goal remains active. External novelty is not claimed or audited.

## Log

- 2026-10-27 — read HF frontier and scoped obstruction reports; inspected current source;
  isolated the terminal premise in the source-field identification.
- 2026-10-27 — completed paper proof and Lean formalization; fixed filter transport and
  oriented-kernel rewrites after the first check; final module and transitive axiom audit passed.
