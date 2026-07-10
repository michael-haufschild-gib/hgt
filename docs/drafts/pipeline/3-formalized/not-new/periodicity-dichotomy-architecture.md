# Periodicity dichotomy: proven regions and RH bridge

- **ID:** periodicity-dichotomy-architecture
- **Stage:** 3-formalized (theorem complex; headline conjecture stays SEARCH register)
- **Type:** THEOREM (Lean) supporting CONJECTURE C-PD
- **Statement:** `PeriodicityDichotomy f` = every open-strip zero is on `Re = 1/2` or on a full vertical progression. Proven: column forms and the degree-zero class satisfy it; it is stable under multiplication by column forms; the aperiodic core is subadditive; the finite-prime sector satisfies it with hypertranscendental columns allowed; and cell-wide dichotomy + no-off-line-progression for ζ is equivalent to RH and drives every rung of the ladder.
- **Lean:** `PeriodicityDichotomy.lean` (`columnForm_periodicityDichotomy`, `periodicityDichotomy_mul_columnForm`, `aperiodicZeroAt_mul`, `periodicityDichotomy_zeta_iff_riemannHypothesis`), `DichotomyInstances.lean` (`integralMultiplicativeFEClass_periodicityDichotomy`, `gammaFECell_dichotomy_implies_rh`, `gammaFECell_dichotomy_implies_ladder`, `zetaDzo_witness_zero_periodic`), `FinitePrimeSectorDichotomy.lean` (`finitePrime_zero_periodic`, `finitePrime_periodicityDichotomy`). All axiom-clean; no-AP input [VERIFIED-KNOWN] (Putnam/van Frankenhuijsen/LSSS; Martin–Ng for L(s,χ)).
- **Dual gate:** PASS. NOVEL — the dichotomy is documented [ABSENT] (checks-ostrowski-da-dirichlet.md Q3, seven searches); extends Grand RH for the Selberg class beyond temperedness with periodicity as the failure-mode invariant. SIGNIFICANT — C-PD ⟹ RH is a machine-checked composition; boundary clauses certified (Epstein non-multiplicativity Lean certificate; 2^ω drop-FE witness); implies no Landau–Siegel zeros.

## Log
- 2026-07-09 — architecture formalized; conjecture carded on `goldilocks-divisor-rigidity.md`.

## Verdict correction (2026-07-09, same day)
- **Dual gate: FAIL on decomposition.** On column/gear members the dichotomy is trivially true by
  factor structure; on ζ the periodic clause is empty (no vertical APs — verified literature), so
  the conjecture collapses to RH restated. C-PD ≡ (triviality on DA members) ∪ (GRH-type on
  primitives): significant-but-derivable packaging, a synonym. The clock/orbit framing is a flow
  picture — the object this field studies has no clock.
- **What stands:** the theorem complex is retained as a FLOW-SIDE NO-GO BANK — it closes the flow
  side exhaustively (finite clockwork, limits of clockwork, finite regroupings, global stabilizers
  can never carry the divisor content), so no future session digs there. The bridge theorems are
  dictionary, not knowledge.
