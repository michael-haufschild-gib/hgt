# Event topological-debt conservation — Lean certificate

- **ID:** `event-topological-debt-conservation-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[LEAN-PROVEN] [REDISCOVERED] [BRIDGE]`
- **Paper proof:** `event-topological-debt-conservation.md`
- **Lean module:**
  `../../../../../formal/GaloisForLFunctions/HTGeometry/EventTopologicalDebt.lean`

## Certified statements

For an arbitrary type \(A\) with `[AddCommGroup A]`:

1. `eventDebt_eq_source_sub_target`
   proves
   \[
   s=k+i,\quad t=i+c
   \quad\Longrightarrow\quad
   k-c=s-t.
   \]
2. `kernel_eq_cokernel_iff_source_eq_target`
   proves, under the same decompositions,
   \[
   k=c\quad\Longleftrightarrow\quad s=t.
   \]
3. `sum_range_state_sub_succ`
   proves the generic finite telescope
   \[
   \sum_{j<n}(x_j-x_{j+1})=x_0-x_n.
   \]
4. `eventDebt_history_telescope`
   substitutes local event decompositions into that telescope.
5. `eventDebt_closed_history_eq_zero`
   proves zero total debt when \(x_n=x_0\).

No bundle, \(K\)-theory, spacetime, gravity, or physical-emergence claim occurs in the formal
theorems.

## Verification

Focused final audit:

```text
lake build GaloisForLFunctions.HTGeometry.EventTopologicalDebt
✔ [8475/8475] Built GaloisForLFunctions.HTGeometry.EventTopologicalDebt
Build completed successfully (8475 jobs).
```

A `/tmp` `#print axioms` audit reports:

```text
eventDebt_eq_source_sub_target:
  [propext]
kernel_eq_cokernel_iff_source_eq_target:
  [propext]
sum_range_state_sub_succ:
  [propext, Classical.choice, Quot.sound]
eventDebt_history_telescope:
  [propext, Classical.choice, Quot.sound]
eventDebt_closed_history_eq_zero:
  [propext, Classical.choice, Quot.sound]
```

These are standard mathlib foundations. There is no custom `axiom`, `sorry`, `admit`, `opaque`,
or `unsafe` declaration.

Repository-wide lint still reports unrelated pre-existing unreachable modules in `RHTower` and
three other `HTGeometry` modules. It does not report
`GaloisForLFunctions.HTGeometry.EventTopologicalDebt`; the new module is reachable from the
`HTGeometry` umbrella.

## Gates

- [x] paper theorem dependency-closed
- [x] exact arbitrary-group target formalized
- [x] focused module build green
- [x] axiom audit recorded
- [x] umbrella reachability checked
- [ ] vector-bundle \(K^0\) interpretation formalized when library support exists

## Log

- 2026-07-29 — formalized one-event conservation, same-parent rigidity, finite-history
  telescoping, and closed-history zero debt.
- 2026-07-29 — focused build and axiom audit passed; no stale Lean process remained.
- 2026-08-15 — re-audited with `lake env lean /tmp/event_topological_debt_audit.lean` and
  `lake build GaloisForLFunctions.HTGeometry.EventTopologicalDebt` (8,655 jobs); the source
  declaration scan remains free of `sorry`, `admit`, custom `axiom`, `opaque`, and `unsafe`.
