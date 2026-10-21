# AIP: shared strip surplus, allocated across nested prime strips without double counting

- **ID:** aip-shared-surplus-2026-10-21
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean): allocation survivors and the sharing obstruction; the signed global allocation stays CONJECTURE (B-RH)
- **Source:** frontier map, AIP open/hard obstacle "Allocate shared strip surplus without double
  counting"; review-2110 hard-obstacles AIP (b); AIP README mechanisms 28–35.
- **Statement:** For odd `F` on `[−r, r]` the strips `S_n = [log n − r, r]` of the entered prime powers
  are nested with common right end `r`. Allocate the one archimedean surplus
  `T(S) = ∫∫_{S×S} k(x, y)(F x − F y)²` among them so that every atom `2Λ(n)/√n ∫ F F(· + log n)` is
  paid and no pair is counted twice. Determine where this is possible and prove the obstruction
  outside.

## Result
The surplus can be shared exactly in the light cone, and not beyond it through the odd parts.

1. **Shell micro-fold** (`NestedStripShellMicroFold`, `sharpMicroFold_shell_ge`). For an inner
   strip `[p', r]` right of the centre of `[p, r]` (`c = p' − m > 0`) only the right–right pair of a
   quadruple meets the inner box, and only on the corner `u, v > c`; the corner weight is
   `≤ (2 + η/2)/c + 1`. Hence `T(S) − T(S') ≥ (λ₀ − (r − p')((2 + η/2)/c + 1)) ∫_S α²`.
2. **Allocation** (`SharedStripSurplusAllocation`). Union with weights `Σθ ≤ 1` over nested boxes
   (`sum_primeStripCharge_le_union`); telescoping chain over disjoint shells
   (`sum_primeStripCharge_le_chain`). The atoms of `23` and `25` share one strip for
   `½ log 25 < r ≤ ½ log 25 + 1/250` where no union allocation exists
   (`primeStripCharge_twentyThree_twentyFive_le`, `C¹` form `…_of_contDiff`).
3. **Light cone at every scale** (`PrimeLightConeAllocation`, `sum_primeShift_le_lightCone`, `C¹`
   form `…_of_contDiff`). For `r ≥ 2`, `δ ≤ e^{−r}/(16r)`: all atoms of `2r − 2δ ≤ log n < 2r` are
   paid by one copy of `T(r − 2δ, r)`; the band holds `≍ e^r/r` integers.
4. **Sharing obstruction** (`EdgeTentSharingObstruction`, `exists_edgeTent_oddPart_sharing_fails`).
   For all large `r` the odd edge tent of width `1/48` makes every atom of the thin band
   `2r − 1/6 ≤ log n ≤ 2r − 1/24` vanish and every odd part paid by its own strip, while the odd parts
   together exceed `T(0, r)`. The input is the PNT of `RHTower.Sieve` (`tendsto_sum_vonMangoldt_div`).
5. **Logarithmic capacity** (`EdgeTentLogarithmicCapacity`, `stripBoxEnergy_edgeTent_le_log`,
   `stripBoxEnergy_edgeTent_lt_sum_oddPart`). `T(0, r) ≤ (log(4/ε) + 42) ∫_0^r F²` for the edge tent,
   uniformly in `r`. No allocation of the surplus of the support pays the odd parts of strips wider
   than `ε` with total weight above `2 log(4/ε) + 84`.

## No-go closure
- **Exact killing theorem/mechanism:** the intermediate claim "the odd parts of all entered (even all
  thin) prime strips are paid by one copy of the archimedean surplus" is false for large `r`
  (`exists_edgeTent_oddPart_sharing_fails`). Mechanism: every strip contains the common edge `r`; an
  edge bump is charged `½∫F²` by each strip wider than it, but the surplus is a logarithmic energy
  of capacity `O(log 1/ε)` (`stripBoxEnergy_edgeTent_lt_sum_oddPart`), while the atom mass of the
  width layer `[η, 2η]` is `≍ ηe^r`.
- **Strongest positive survivor:** the light cone, all atoms of strip width `≤ e^{−r}/(16r)` paid
  simultaneously at every scale (`sum_primeShift_le_lightCone`). Also the shell and chain
  allocation, which make widely separated strips share nothing, and the `{23, 25}` instance.
- **New insight:** the per-strip Harnack inequalities (mechanisms 30, 35) do not globalize through
  odd parts. On the obstruction test the atoms themselves vanish: the even parts cancel the odd
  parts exactly. Any global allocation must be signed. The band's charge is a Hankel form whose
  symbol is `Σ_{band} Λ(n) n^{−1/2−iξ}`. Its mean (PNT) part is a gain; its fluctuation competes with
  the surplus symbol `log ξ`, heuristically of that order only when the nearby zeros are on the
  line. So the signed global allocation is the B-RH core, not an unconditional target.
- **Status:** all five items dependency-closed and formalized; axioms `propext, Classical.choice,
  Quot.sound`; modules wired in the AIP umbrella. Gap between the light cone (`e^{−r}/r`) and the
  obstruction (fixed width) is arithmetic: Brun–Titchmarsh widens the cone to `e^{−r}`; refuting at
  width `Ce^{−r}` needs lower bounds for prime powers in `(N − C√N, N)`.

## Conjecture loop (ledger)
- C1 shell micro-fold — PROVED (Lean).
- C2 telescoping chain allocation — PROVED (Lean).
- C3 union allocation — PROVED (Lean).
- C4 `{23, 25}` shared strip — PROVED (Lean); union provably insufficient there (`1.95 > λ₀`).
- C5 light cone at every scale — PROVED (Lean), width `e^{−r}/(16r)`.
- C6 global odd-part allocation of the thin band — FALSE (Lean), large `r`.
- C7 logarithmic capacity of the edge — PROVED (Lean), `2 log(4/ε) + 84`.
- C8 signed global allocation of the thin band — OPEN, B-RH heuristic (Hankel symbol vs `log ξ`).
- C9 wide strip `S₂` sharing with `S₃` past `½ log 3` — done by a sibling agent
  (`WideMicroFoldExactRates`, `OverlappingPrimeStripsJointHarnack`, README mechanism 40); not
  duplicated.

## Gates
- [x] 0 → 1 well-posed, corpus searched (`research "shared strip surplus allocation prime shifts"`:
  only per-strip theorems existed).
- [x] 1 → 2 paper proofs (this card, README mechanisms 36–39, 41)
- [x] 2 → 3 Lean: `NestedStripShellMicroFold`, `SharedStripSurplusAllocation`,
  `PrimeLightConeAllocation`, `EdgeTentSharingObstruction`, `EdgeTentLogarithmicCapacity`; each
  checked with `lake env lean`, oleans via `lake --old env lean -j 1 -o`, axiom audit clean.

## Log
- 2026-10-21 — created; C1–C7 formalized; C8 recorded open; moved to 3-formalized.
