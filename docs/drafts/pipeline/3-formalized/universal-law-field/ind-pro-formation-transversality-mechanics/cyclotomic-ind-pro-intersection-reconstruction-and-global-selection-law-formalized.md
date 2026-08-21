# ULF-IPFTM-1 — Lean certification record

**Card:** `cyclotomic-ind-pro-intersection-reconstruction-and-global-selection-law.md`
**Status:** every theorem of the card is Lean-certified, unconditional and axiom-clean.

## Card result → Lean declaration

| Card | Statement | Lean |
|---|---|---|
| (IPT.1)–(IPT.3) | the two depth laws and pro-coherence | `ProHistory` (fields `pow_eq_one`, `coherent`) |
| (IPT.4) | ind-formation | `ProHistory.IsIndFormed` |
| Thm 2.1, (IPT.5) | ind-formed ⟺ trivial; one doubling suffices | `ProHistory.isIndFormed_iff`, `eq_one_of_sq_eq_self` |
| (IPT.6) | the integral charge history | `chargeUnit`, `chargeHistory`, `chargeUnit_pow`, `chargeUnit_eq_one_iff` |
| Cor 3.1 | only the zero charge is ind-formed | `chargeHistory_isIndFormed_iff` |
| Thm 3.2 | the complete pro-history reconstructs the charge | `eq_of_forall_chargeUnit_eq` |
| Thm 3.2, (IPT.7) | the doubling defect is `[−q]` and centred at `−q` | `ambidextrousDoublingDefect_eq`, `doublingDefect_reconstructs` (ULF-DFPM-5) |
| §4, group-like | a group-like element is exactly one basis element | `isGroupLikeElem_iff_exists_single` (with `maCoeff`, `coeffPair`, `coeffPair_comul`, `comul_single_eq`) |
| Cor 4.1 | group-like landing forces the trivial history | `eq_one_of_groupLike_landing`, `eq_zero_of_groupLike_landing` |
| §4, prime-to-`p` | the `p = 2` argument via the multipliers 3 and 5 | `eq_one_of_odd_of_pow_three_of_pow_five` |
| §5, (IPT.9)–(IPT.10) | the three shadows are one condition | `indPro_tfae` |
| §6 | reflection is neutral, not selecting | `not_isIndFormed_chargeHistory_of_zetaZero` |
| Cor 7.1, equivalence | ind-formation of every local history ⟺ RH | `riemannHypothesis_iff_forall_indFormed` |
| Cor 7.1, landing | group-like source landing at every local charge implies RH | `riemannHypothesis_of_groupLike_landing` |

## Modules

| Module | Public declarations |
|---|---|
| `formal/GaloisForLFunctions/HTGeometry/MonoidAlgebraGroupLike.lean` | 6 |
| `formal/GaloisForLFunctions/HTGeometry/CyclotomicIndProIntersection.lean` | 10 |
| `formal/GaloisForLFunctions/RHTower/IndProGroupLikeLandingSelection.lean` | 4 |

All wired into `GaloisForLFunctions.HTGeometry`, `GaloisForLFunctions.RHTower` and
`GaloisForLFunctions.HTGeometry.UniversalLawField`.

## New reusable result — a mathlib gap

`isGroupLikeElem_iff_exists_single`: over any commutative integral domain `R` and any index type
`G`, an element of `MonoidAlgebra R G` is group-like exactly when it is `single g 1`.  Mathlib has
`IsGroupLikeElem` and the bialgebra structure on `R[G]` but no classification.  The proof pairs the
comultiplication against two coefficient functionals — `coeffPair g h ∘ comul` isolates the
diagonal — which turns the group-like equation into the orthogonal-idempotent system
`a_g a_h = 0 (g ≠ h)`, `a_g² = a_g`, exactly the computation §4 of the card performs by hand.  Over
a domain that leaves one coefficient equal to `1`.

## Proof notes

Pro-histories are valued in `ℂˣ` rather than `ℂ`.  This makes the group-like landing statement
literal — the landing is `MonoidAlgebra.single (z m) 1` for a genuine group element — and lets the
`ξ² = ξ ⟹ ξ = 1` step be plain cancellation in a group instead of a nonvanishing argument.  The
coherence and root conditions are guarded by `1 ≤ n` and `1 ≤ m`, since depth zero carries no root
group.

## Verification

* `lake env lean` on all three modules: 0 errors, 0 warnings.
* `#print axioms` over the 20 public declarations: only `propext`, `Classical.choice`, `Quot.sound`.
* No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, and no added hypotheses.

## Not claimed

The card's declared gate — that the literal Euler-shell formation holonomy is group-like in the
already constructed rational-Witt filtered cyclotomic source — is future work.  Corollary 7.1 is
formalized in both directions available: the ind-formation criterion as an equivalence with RH, and
the group-like landing as a sufficient condition for it.
