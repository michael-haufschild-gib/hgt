# Invariant-positivity reversibility wall and KMS irreversibility measure — Lean certification

- **ID:** ULF-IPKMS-1
- **Paper card:** `invariant-positivity-reversibility-wall-and-kms-irreversibility-measure-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveInvariantPositivityKMSWall`
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## New reusable infrastructure

`continuous_of_isClosed_graph` — **a map into a compact Hausdorff space whose graph is closed is
continuous.**  Mathlib has no closed-graph criterion at all; this is proved here by an ultrafilter
argument (`IsCompact.ultrafilter_le_nhds`, `IsClosed.mem_of_tendsto`) and is reusable well beyond
this card.

## Certified declarations

### §1 — faithful invariant positivity forces reversibility

- `leftTranslate`, `continuous_leftTranslate`;
- `surjective_leftTranslate` — with an invariant probability of full support
  (`Measure.IsOpenPosMeasure`) on a compact Hausdorff monoid, every left translation is onto: the
  complement of the compact image would be a nonempty open set of measure zero;
- `isUnit_of_invariant_faithful` — every element is invertible;
- `nonempty_group_of_invariant_faithful` — the monoid carries a group structure;
- `continuous_inv_of_closed_graph` — inversion is continuous, its graph being
  `{p | p.1 * p.2 = 1 ∧ p.2 * p.1 = 1}`;
- `invariant_of_absorbing_zero` — the sharp countermodel: an absorbing zero forces `μ = δ₀`, so
  full support is load-bearing.

### §2 — KMS balance measures the defect

Stated from the defining equations of the setting, not from an opaque interface:

- `alg_map_pow_smul` — `σ v = q • v` propagates to `σ (vⁿ) = qⁿ • vⁿ`;
- `isometry_pow` — `w v = 1` propagates to `wⁿ vⁿ = 1`;
- `kms_range_mass` — equation (4): `φ(vⁿw ⁿ) = qⁿ`;
- `kms_defect_mass` — equation (5);
- `kms_layer_mass` — the boxed equation (6): `φ(vⁿ(1 − vw)wⁿ) = (1 − q)qⁿ`;
- `kms_forces_q_eq_one` — non-descent: if the image of `v` is invertible, the same identity forces
  `q = 1`, so no positive-temperature state survives the reversible quotient.

### §3 — the universal Toeplitz realization

- `basisVec`, `norm_basisVec`, `shiftOp_basisVec`, `defectOp_diag`;
- `toeplitzGibbsState` — equation (8), with `toeplitzGibbsState_eq_inner` identifying the coordinate
  form with the diagonal expectation `∑ₙ (1−q)qⁿ ⟨eₙ, a eₙ⟩`;
- `toeplitzGibbsState_one` — normalization;
- `toeplitzGibbsState_defect` — `1 − qⁿ`; `toeplitzGibbsState_rangeProj` — `qⁿ`;
- `historyLayer`, `historyLayer_diag`, `toeplitzGibbsState_layer` — `(1 − q)qⁿ`;
- `tsum_historyLayer_mass` — the layer masses sum to one: the full geometric history distribution;
- `toeplitzGibbsState_offDiagonal` — the gauge dynamics kills every `VᵐV*ⁿ` with `m ≠ n`;
- `toeplitzGibbsState_faithful` — faithfulness, via `Summable.le_tsum` on the nonnegative diagonal
  and `lp.hasSum_single` to pass from `b eₙ = 0` to `b = 0`;
- `invariant_positivity_wall_and_kms_measure` — the capstone.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveInvariantPositivityKMSWall.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Both pass with no warnings; the umbrella build completed 11,432 jobs.  `#print axioms` on the
sixteen declarations audited reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Scope, stated explicitly

Mathlib has **no** C\*-dynamical systems, **no** KMS states, and **no** Calkin algebra.  §2 is
therefore certified from the defining equations of the setting — an algebra endomorphism `σ` with
`σ v = q • v`, the isometry relation `w v = 1`, the exchange identity `φ(ab) = φ(b σ a)`, and
normalization — which is exactly the data the paper proof uses, rather than from a constructed KMS
framework.  §3 does not quote a uniqueness theorem for KMS states: the Gibbs state is **exhibited**
and every property the card asserts of it is verified by direct computation, including the two
ingredients on which the uniqueness argument rests (the diagonal values `qⁿ` and the vanishing of
every off-diagonal monomial).

## Exact field consequence

Invariant-state selection is dead: a faithful invariant probability on a compact monoid forces the
monoid to be a group, and dropping faithfulness lets the invariant measure erase the entire
irreversible sector.  What survives is a *marked law object with incompatible completions* — the
same rank-one defect that blocks the antipode is assigned strictly positive thermal mass `1 − q`,
and the reversible symbol quotient admits no positive-temperature state at all.  The incompatibility
is quantified by the whole geometric distribution `(1 − q)qⁿ`, which sums to one, not by a single
stable index.
