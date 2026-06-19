# A native invariant that survives Door-3 — FAILED (reduces to C5)

- **ID:** c3-native-invariant-door3
- **Stage:** 5-failed
- **Type:** CONJECTURE (native) — **goal not achievable as posed**
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/00-status.md rows #44, #23; ../../door/door-C5-irreducibility-and-door-2-retest.md;
  charter C3 + Door-3
- **Original goal:** exhibit an *independent* native invariant of multi-`q` modules — functorial,
  not a parent pullback — with a parent-identical witnessing pair, closing **C3** on its own (more
  tractably than the C5 theorem).

## Why it failed (verdict 2026-06-19)
The independent native invariant does **not** exist. Worked out in full
(`../2-fully-proven/c3-gluing-invariants-bridge.md`, theorem (a)–(c) + `logs/2026-06-19-c3-native-invariant.md`):

1. **The gluing phenomenon is real but cheap.** Two multi-`q` modules can be isomorphic on every single
   prime yet inequivalent jointly — explicit rank-2 two-prime witness, `tr(A_2A_3)=3 ≠ 5/2=tr(B_2B_3)`
   with per-prime conjugacy. So a joint invariant exists.
2. **Every such invariant is BRIDGE.** Curvature `[A_p,A_q]`, joint conjugacy, word-traces are
   coordinates on the GIT character variety of the underlying representation (Procesi/Artin); the `σ_p`
   are inert on the constant model and the frequencies `(log p)` never enter. **Fails Door-2 and Door-3**
   — the same way `corank(Λ)` fails Door-3 (#23).
3. **The arithmetic refinement = C5★.** The primes' arithmetic (`Λ`, Baker on `m·ℓ`) enters the
   classification only through the *quantitative* trivialization of cocycles (transfer-function
   regularity), which is exactly the combination-mode object of Conjecture C5★. So the only
   Door-3-surviving invariant is the arithmetic one, and **C3-native ⟺ C5★**.

**Conclusion:** C3 is **not an independent criterion** — it cannot be closed below C5. The hoped-for
"more tractable than C5" native invariant was a false hope; there is no cheap native invariant. C3 is
**reduced to / folded into C5**.

## Disposition of the work
- **Proven content → 2-fully-proven:** `../2-fully-proven/c3-gluing-invariants-bridge.md` (the gluing
  theorem + BRIDGE grade + the C3 ⟺ C5★ reduction).
- **Native closure → C5:** `../1-in-progress/combination-mode-baker-reducibility.md` (C5★). Closing C5★
  closes C3 automatically; no separate C3 work remains.
- **Criterion status:** C3 stays formally **PARTIAL** in the scorecard, now annotated "cheap invariants
  proven BRIDGE; native closure ⟺ C5★."

## What this rules out (so it is not retried)
Do **not** re-open C3 as a standalone target via: the curvature `F_{pq}`, the joint conjugacy / character
variety, word-traces, or the qualitative `Λ={0}` gluing class. All are character-variety / `ℤ^{(P)}`-
cohomology parents (BRIDGE). The only live route is the quantitative arithmetic layer = C5★.

## Log
- 2026-06-19 — created in 0-backlog (branchhood criterion C3).
- 2026-06-19 — worked to conclusion and **moved to 5-failed**. The independent native-invariant goal
  fails: gluing invariants exist but are all BRIDGE (Procesi character variety); the native invariant is
  the arithmetic layer = C5★. Proven yield split to `../2-fully-proven/c3-gluing-invariants-bridge.md`;
  native closure folded into C5 (`../1-in-progress/combination-mode-baker-reducibility.md`).
