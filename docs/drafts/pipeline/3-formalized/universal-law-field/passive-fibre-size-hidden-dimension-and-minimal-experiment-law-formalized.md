# Passive fibre size, hidden dimension, minimal experiment — Lean certification

- **ID:** ULF-EXPDIM-1
- **Paper card:** `passive-fibre-size-hidden-dimension-and-minimal-experiment-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveExperimentalDimension`
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

### §1 — finite information

- `jointResponse` — equation (1);
- `experiments_injective_on_fibre` — on a passive fibre the experiments alone are injective;
- `card_passiveFibre_le` — equation (2): `|F_y| ≤ ∏ᵢ |Yᵢ|`;
- `card_passiveFibre_le_pow` — `|F_y| ≤ k^r` when every experiment has capacity at most `k`;
- `log_card_passiveFibre_le` — equation (3): `log_k |F_y| ≤ r`.

Stated with `Nat.card`, so no decidability instances are needed, and **without** assuming the state
space finite: the injection into the finite experimental codomain already forces each passive fibre
to be finite.  This is a mild strengthening of the card.

### §2 — linear hidden dimension

- `linearJointObserver q₀ ℓ = q₀.prod (LinearMap.pi ℓ)` — equation (4);
- `ker_linearJointObserver` — `ker Q = ker q₀ ⊓ ⨅ᵢ ker ℓᵢ`;
- `linearJointObserver_injective_iff` — equation (5);
- `hiddenRestriction`, `hiddenRestriction_injective` — the experiments restricted to the hidden
  space `ker q₀` remain injective;
- `finrank_ker_le_card` — the lower bound `r ≥ d`, by rank–nullity through
  `LinearMap.finrank_le_finrank_of_injective`;
- `exists_experiments` — the sufficiency half: `finBasis` of `ker q₀`, coordinate functionals
  extended to `V` by `LinearMap.exists_extend`, and `Basis.forall_coord_eq_zero_iff`.

### §3 — the experimental dimension

- `IsExperimentBudget q₀ r`, `edim q₀ = sInf {r | IsExperimentBudget q₀ r}`;
- `edim_eq_finrank_ker` — the boxed equation (6): `edim q₀ = dim ker q₀` whenever the hidden space
  is finite-dimensional;
- `not_isExperimentBudget_of_infinite` — the infinite case: if `ker q₀` is infinite-dimensional then
  no finite family of scalar experiments makes the joint observer injective;
- `isExperimentBudget_nonempty_iff` — a finite budget exists **iff** the hidden space is
  finite-dimensional, which is the precise sense in which both sides of (6) are "allowed to be
  infinite";
- `passive_fibre_forces_experiment_budget` — the capstone.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveExperimentalDimension.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Both pass with no warnings; the umbrella build completed 11,429 jobs.  `#print axioms` on the ten
declarations audited reports only `propext`, `Classical.choice`, and `Quot.sound`.  No project
axiom, placeholder, hypothesis interface, or computation proof is used.

The observer name had to be `linearJointObserver`: `jointObserver` is already taken in
`ConstitutiveDoctrineLattice`, and per-file `lake env lean` cannot see umbrella-level collisions —
only the umbrella build does.

## Exact field consequence

Fibre loss and intervention complexity are one coupled quantity, not two slots.  The passive
observer sets a hard floor on the experiment budget: exactly `dim ker q₀` scalar responses in the
finite-dimensional case, and *no finite number at all* when the hidden space is
infinite-dimensional.  Applied to a source theorem that produces an infinite-dimensional hidden jet
space, `not_isExperimentBudget_of_infinite` is the precise noncompactness statement — but, as the
card's hostile scope insists, only once a source theorem supplies the passive observer and names its
hidden space.
