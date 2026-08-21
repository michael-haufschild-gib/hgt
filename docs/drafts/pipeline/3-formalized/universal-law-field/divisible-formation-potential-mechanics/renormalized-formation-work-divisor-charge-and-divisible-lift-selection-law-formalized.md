# ULF-DFPM-1 — Lean certification record

**Card:** `renormalized-formation-work-divisor-charge-and-divisible-lift-selection-law.md`
**Status:** every theorem of the card is Lean-certified, unconditional and axiom-clean.

## Modules

| Module | Public declarations |
|---|---|
| `formal/GaloisForLFunctions/HTGeometry/ConstitutiveDivisibleFormationSelection.lean` | selection core (pre-existing) |
| `formal/GaloisForLFunctions/HTGeometry/GibbsDirichletCumulants.lean` | 8 (new, reusable) |
| `formal/GaloisForLFunctions/HTGeometry/IntegralFormationRootRigidity.lean` | 5 (new, reusable) |
| `formal/GaloisForLFunctions/RHTower/RenormalizedFormationWorkDivisor.lean` | 16 (new) |
| `formal/GaloisForLFunctions/RHTower/FormationPotentialCriterion.lean` | 19 (new) |
| `formal/GaloisForLFunctions/RHTower/SpectralCumulantShadow.lean` | 9 (new) |
| `formal/GaloisForLFunctions/RHTower/FormationContourCharge.lean` | 4 (new) |

All are wired into `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.HTGeometry` and
`GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Card result → Lean declaration

| Card | Statement | Lean |
|---|---|---|
| (DWP.5) | the meromorphic survival transfer | `survivalTransfer` |
| Thm 2.1 | numerator holomorphic and zero-free | `analyticAt_shellSource_natCast_mul`, `shellSource_natCast_mul_ne_zero` |
| Thm 2.1 | denominator carries exactly the zeta divisor | `analyticOrderAt_shellResidueUnit` |
| Thm 2.1 | poles are the strict-right zeta zeros with their multiplicity, no zeros | `meromorphicOrderAt_survivalTransfer`, `survivalTransfer_ne_zero` |
| Thm 2.1, (DWP.6) | holomorphic and nonzero at the normalization point, with its value | `analyticAt_survivalTransfer_one`, `survivalTransfer_one`, `survivalTransfer_one_ne_zero` |
| Cor 2.2, (DWP.8) | exact renormalization | `survivalTransfer_mul_sub_one` |
| Cor 2.2, (DWP.9) | the renormalized work at `σ = 1` is `log(H_{rm}(1)/S_m(r))` | `survivalTransfer_one_eq_ofReal_pos` (with `tsum_inv_pow_pos`, `riemannZeta_natCast_eq_ofReal_tsum`, `tsum_inv_pow_strict_lt`, `exists_pos_shellMultiplier_natCast`) |
| Thm 3.1, (DWP.11) | residue of `−d log R` at a zero of order `q` is `q` | `residue_neg_logDeriv_survivalTransfer` |
| Thm 3.1, (DWP.12) | contour charge counts the enclosed divisor | `circleIntegral_charge_survivalTransfer` |
| Cor 3.2, (DWP.13) | first cumulant shadow | `neg_logDeriv_survivalTransfer_eq_gibbs` |
| Cor 3.2, (DWP.14) | second cumulant shadow | `hasDerivAt_neg_logDeriv_survivalTransfer` |
| Thm 4.1 (1)⟺(2) | RH ⟺ the transfer is holomorphic | `riemannHypothesis_iff_analyticAt_survivalTransfer` |
| Thm 4.1 (2)⟺(3) | with nonvanishing | `riemannHypothesis_iff_analyticAt_and_ne_zero` |
| Thm 4.1 (2)⟺(4) | the work form is holomorphic | `riemannHypothesis_iff_analyticAt_logDeriv` |
| Thm 4.1 (3)⟺(5), (DWP.15) | a holomorphic potential exists | `riemannHypothesis_iff_exists_formationPotential` |
| Thm 4.1, (DWP.16) | the potential is pinned by its value at `1` | `exists_normalized_formationPotential` |
| Lemma 5.1 | unbounded root divisibility annihilates the divisor | `meromorphicOrderAt_eq_zero_of_eventual_roots` |
| Thm 5.2, (DWP.17)–(DWP.18) | divisible formation selection law | `riemannHypothesis_tfae_divisibleLift` |
| Cor 5.3, (DWP.19) | charge-divisibility conservation | `logDeriv_survivalTransfer_eq_nsmul` |
| Thm 5.4, (DWP.20)–(DWP.21) | integral formation-root rigidity | `powerSeries_eq_one_of_unbounded_roots` |
| Cor 5.5 | same-doctrine root no-go | immediate from Thm 5.4 |
| Thm 5.6, (DWP.22)–(DWP.24) | local Kummer descent, holonomy, and the three-way equivalence | `dvd_meromorphicOrderAt_of_root`, `root_branch_loop_factor`, `root_holonomy_eq_one_iff_dvd`, `exists_meromorphic_root_of_dvd` |
| Cor 5.7 | effective pro-Kummer selection | `meromorphicOrderAt_eq_zero_of_eventual_roots` + `riemannHypothesis_tfae_divisibleLift` |

## New reusable results

* `HTGeometry/GibbsDirichletCumulants.lean` — for any Dirichlet partition,
  `logDeriv (LSeries f) = −E[log n]` and `deriv (logDeriv (LSeries f)) = Var[log n]`.
* `HTGeometry/IntegralFormationRootRigidity.lean` — an integral power series with constant term one
  and integral roots at unboundedly many depths is `1`.
* `RHTower/RenormalizedFormationWorkDivisor.lean` — the positivity chain for `ζ` at natural
  arguments, including strict monotonicity in the exponent (the corpus's versions are `private`).
* `RHTower/FormationContourCharge.lean` — the contour charge of a logarithmic derivative on a
  zero-avoiding circle, built on the corpus's disc argument principle.

## Verification

* `lake env lean` on all six new modules: 0 errors, 0 warnings.
* `#print axioms` on all 60 public declarations: only `propext`, `Classical.choice`, `Quot.sound`.
* No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`. Hypotheses are exactly the card's own setting:
  `12 ≤ m`, `2 ≤ r`, and the domain conditions `Re s > 1/2` or `Re s > 1`.

## Not claimed

The card's declared open gate — the **source construction of effective roots** (status flag
`[SOURCE ROOT GENESIS OPEN]`) — is future work, not a theorem of the card.
