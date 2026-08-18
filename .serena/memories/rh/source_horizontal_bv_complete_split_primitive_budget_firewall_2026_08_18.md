# Source-horizontal BV complete-split primitive-budget firewall (2026-08-18)

Formal module:
- formal/GaloisForLFunctions/RHTower/SourceHorizontalWoldBVCompleteSplitPrimitiveBudgetFirewall.lean
- wired into RHTower.lean; exact leaf build passed.
- standard axioms only: propext, Classical.choice, Quot.sound.

Unconditional finite identity:
- interior jet iota_N := sourceHorizontalWoldOrderedNormalizedMoment N 2.
- iota_N > 0 and iota_N + epsilon_N = 1, where epsilon_N is selected BV endpoint third jet.
- complete positive energy is exactly 8*normSq(c), so literal primitive budget is smaller at every clock for c != 0.

New arithmetic result:
- sum over primes 1/(p*(log p)^2) < 2.
- proof isolates 2,3,5, bounds ordered-prime tail by integer tail from 7 and integral 1/log 6.
- routePPrimitiveBaseCauchyCubicTraceBudget < 1.

Canonical Krein sign:
- signed split = 8*normSq(c)*(2*epsilon_N-1) -> (8/3)*normSq(c).
- source budget = (8/3)*normSq(c)*B_P with B_P<1, hence signed split overspends cofinally.

Cross-corpus Route-O pivot:
- exact matched Suzuki current retains all natural/prime-power labels below open nth-prime cutoff.
- existing absolute summability implies its partial current divided by (log p_N)^3 -> 0.
- any fixed source scaling k leaves signed limit 8/3*normSq(c), so budget still loses eventually.

Scoped retirement:
- complete-positive BV conservation, canonical Krein conservation, and fixed-scale Route-O matched-current compensation cannot supply requested primitive-budget law.
- surviving producer would require genuinely new cubic-order, non-summable but source-renormalized negative channel before Xi selection; clock-dependent amplification of a summable current is not source naturality.
- Not RH.

Docs:
- docs/drafts/pipeline/5-failed/source-horizontal-bv-complete-split-primitive-budget-firewall.md
- Route P section updated in docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md.

Verification:
- direct lake env lean passed.
- exact lake build GaloisForLFunctions.RHTower.SourceHorizontalWoldBVCompleteSplitPrimitiveBudgetFirewall passed.
- global lint failure only unrelated pre-existing unreachable modules; target has no sorry/admit/axiom/opaque/unsafe.
