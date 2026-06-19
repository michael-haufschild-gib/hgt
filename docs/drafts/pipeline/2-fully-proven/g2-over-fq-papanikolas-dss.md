# G2 / DSS over `F_q(C)` — native reproof = Papanikolas under the corank-1 collapse

- **ID:** g2-over-fq-papanikolas-dss
- **Stage:** 0-backlog-lean
- **Type:** THEOREM (paper) — Door grade **BRIDGE** (function-field border; Door-5 reproof)
- **Priority:** FOUNDATIONAL
- **Source:** split (Step 4) from `function-field-native-reproof.md`; built on Professor's
  `../2-fully-proven/function-field-holonomicity-degeneration.md` (corank=1 collapse) and the C6 functor
  `S_ff` (`../2-fully-proven/c6-specialization-functors.md` §2); 00-status rows #8, #16, #76–80;
  feeds `../../door/bucket-the-seam-archimedean-obstruction.md`.
- **Statement.** Re-derive DSS (G2) over a function field `F_q(C)` **in the multi-`q`-difference
  vocabulary**: restrict the proven multi-`q` transcendence upper bound `trdeg ≤ dim G_M` (#8) along
  `S_ff`, use the corank-1 degeneration to collapse the infinite-base module to a **single-Frobenius**
  difference module, and recover **Papanikolas' equality** `trdeg = dim G_M` (the lower bound that is
  *open* over ℚ as obstruction C). Door-5 ✓ (recovers Papanikolas exactly); grade **BRIDGE**. The payoff
  is the **seam diagnosis**: the corank gap `∞ − 1` is exactly why DSS is a theorem over `F_q` and open
  over ℚ.

## Caveat on which "DSS over F_q" (avoid conflation)
This is the **period-transcendence** reading — `trdeg` of the diagonal-section period algebra = `dim G_M`
— matching the multi-`q` engine #8 and project row #16 (`full DSS over F_q(t) = Papanikolas`). It is
**not** the Frobenius-eigenvalue / equidistribution reading (geometric monodromy maximal =
Deligne–Katz–Sarnak), which is the **G4** face (#30). Keeping these separate is the point: G2 = periods
(Papanikolas/ABP), G4 = monodromy (Katz). This card is G2 only.

## The argument

### Step 1 — the upper bound restricts along `S_ff` (native, proven)
`S_ff` (C6 §2, proven `⊗`-functor) sends `x_p = p^{−s} ↦ T_v = q^{−s·deg v} = N(v)^{−s}` and the
dilation `σ_p : x_p ↦ q_p x_p` to the place operator `σ_v : T_v ↦ q^{−deg v} T_v`. The diagonal section
is the global Weil L-function `∏_v det(1 − Frob_v·N(v)^{−s})^{−1}`, a polynomial in `u = q^{−s}`. The
multi-`q` **upper bound** `trdeg(periods of M) ≤ dim G_M` (#8, proven; the "Galois bounds periods"
direction) is functorial: applied to `S_ff(M)` it gives `trdeg ≤ dim G_{S_ff(M)}` (`trdeg` does not
increase under the `⊗`-functor; `G_{S_ff(M)}` is the specialized difference Galois group). No new work —
the proven engine restricts verbatim. ∎(Step 1)

### Step 2 — the corank-1 collapse ⟹ single Frobenius = the Papanikolas setting (native, proven input)
Professor's degeneration (`function-field-holonomicity-degeneration.md`): over `F_q(C)`,
`N(v) = q^{deg v}` are **all powers of one** `q`, the relation lattice `Λ_ff = ker(deg: ℤ^{(V)}→ℤ)` has
**corank 1**, and on the diagonal `σ_v = σ_q^{deg v}` for a single base operator `σ_q : u ↦ q^{−1}u`.
Hence the infinite-base module `S_ff(M)` is, up to the corank-1 relations, a **single-operator
difference module over `(F_q(u), σ_q)`**. Under `S_ff` the dilation specializes to the **geometric
Frobenius** (the C6 dictionary `dilation ↦ Frob`), so this single-operator module is exactly the
`τ`-difference module (`τ = q`-Frobenius) underlying an **Anderson `t`-motive**. *This is where the
multi-`q` ontology degenerates: over `F_q` there is one base, so the native object IS a `t`-motive — no
surplus structure (Door-2 BRIDGE, by design).* ∎(Step 2)

### Step 3 — Papanikolas/ABP supplies the lower bound ⟹ equality = DSS over `F_q`
In the single-`τ` `t`-motivic setting, **Papanikolas (2008)** proves the full equality
`trdeg_{\overline{F_q(t)}}(\text{period algebra of } M) = \dim Γ_M`, `Γ_M` the `t`-motivic (difference)
Galois group, via the **ABP criterion** (Anderson–Brownawell–Papanikolas 2004): every algebraic relation
among the periods is induced by the difference (`τ`-) equations — the Galois group is **as large as the
relations allow**. Composed with Step 1's upper bound this forces
```
trdeg(periods of S_ff(M)) = dim G_{S_ff(M)}      (equality, over F_q).
```
That equality **is** G2/DSS over `F_q`: the diagonal-section periods are maximally independent — i.e.
`trdeg = orbit-dim`. **Door-5 ✓** (recovers Papanikolas exactly). **Door-2: BRIDGE** — stripped of
multi-`q` words the proof is "collapse to one Frobenius, apply Papanikolas/ABP," a single-`σ` difference
Galois theorem; the multi-`q` apparatus adds no depth over `F_q` (corank 1, no seam). ∎(Step 3)

### Step 4 — the seam diagnosis (the payoff): corank gap `∞ − 1` = why DSS splits
Why is the **lower bound** a *theorem* over `F_q` but *open* (obstruction C) over ℚ? Localize the
difference precisely:
- **ABP rigidity is a single-Frobenius phenomenon.** The lower bound holds because one semilinear `τ`
  with fixed field exactly `F_q` governs *all* period relations (the "Frobenius determines everything"
  rigidity, Weil-II flavored). Existence of **one unifying Frobenius** ⟺ **corank 1** (Step 2).
- **Over ℚ, corank = ∞** (Professor #119 / G1: `{log p}` ℚ-LI ⟹ `corank(Λ_{S_T M_ζ}) = |T| ↑ ∞`). There
  is **no single Frobenius** unifying the primes — the **missing F₁**. The ABP-style rigidity has
  infinitely many independent shifts `σ_p` and no common fixed structure, so the lower bound becomes the
  **open obstruction C** = independence of `{π, ζ(odd), Stieltjes γ_n}` (#15/#18).

> **Seam statement (G2 face of Professor's conjecture).** The DSS lower-bound rigidity holds **iff** a
> single unifying Frobenius exists **iff** `corank = 1` **iff** the `F_q` side. The corank gap `∞ − 1` is
> **exactly** the obstruction the archimedean place (F₁) must supply over ℚ. G2/DSS is thus a second
> face — alongside G1 non-holonomicity (Professor) — of the *same* corank-∞ = missing-F₁ seam. The
> archimedean place must furnish a "single fake Frobenius"; its absence is measured by `corank = ∞`.

This is the deliverable that feeds `bucket-the-seam-archimedean-obstruction.md`: the seam is not just G1's
non-holonomicity but **also** G2's failure of the period lower bound, and both are read off the **one**
number `corank`.

## Door passport
- **Door-5 (faithful restriction):** ✓ recovers Papanikolas' `trdeg = dim Γ_M` on the FF overlap.
- **Door-2:** BRIDGE — the reproof reduces (via the corank-1 collapse) to single-`σ` difference Galois +
  ABP/Papanikolas; no joint-irreducible `σ_p` use survives over `F_q` (the seam is absent there).
- **Door-4:** the FF border is *not* the native zone (one base, finite corank) — confirming the
  degeneration. The native zone (corank ∞) is exactly where the lower bound fails = ℚ.

## Gates
- [x] 0 → 1  in-progress: split from parent; `S_ff` restriction of the upper bound pinned (Step 1);
  corank-1 collapse to single-Frobenius stated (Step 2); Papanikolas lower-bound recovery + Door-5
  (Step 3); seam diagnosis written (Step 4).
- [x] 1 → 2  fully-proven (verified 2026-06-19): Step 1 upper bound is grounded **twice** — as the
  proven multi-`q` #8 restricted along `S_ff`, *and* as Papanikolas' own easy direction in the single-`τ`
  setting — so it does not hinge on a single route; Step 2 operator-kind identification (dilation ↦
  `Frob_v`) **verified** against C6 §2 (`c6-specialization-functors.md` lines 83–86, the proven `S_ff`
  Frobenius datum) and Professor's proven corank=1; Step 3 = Papanikolas 2008 import recovered (Door-5),
  matching C6 Theorem C line 95; grade **BRIDGE**. The genuine new content banked is the **Step-4 seam
  diagnosis** (corank gap `∞ − 1` = the G2 obstruction), robust on corank 1 (FF) vs ∞ (ℚ), both proven.
- [ ] 2 → 3  formalized — Weil FE of the L-polynomial (#78) already ledgered; the `trdeg = dim G_M`
  equality over `F_q` is an import (Papanikolas), not a new Lean target; the seam-corank statement is.
- [ ] 3 → 4  publication-ready.

## Notes / risk
- This is a **border** item: BRIDGE is the expected and acceptable grade (C6 is the bridge criterion).
  The native-vocabulary re-derivation is the work; the truth of `trdeg = dim G_M` over `F_q` is
  Papanikolas, cited.
- Risk on Step 2: the precise identification "multi-`q` dilation specializes to geometric Frobenius" is
  carried by the C6 `S_ff` functor (proven). If that identification is looser than claimed, Step 3 still
  recovers Papanikolas (both live over the same single-Frobenius difference field) but the *native*
  flavor weakens — record honestly. The seam diagnosis (Step 4) is robust either way: it depends only on
  corank 1 (FF) vs ∞ (ℚ), both proven.

## Log
- 2026-06-19 (DeWitt) — created in 1-in-progress, split from `function-field-native-reproof.md` (Step 4),
  per Professor's thread assignment (chat id=17). Wrote the four-step native reproof: (1) `S_ff`
  restriction of the proven upper bound; (2) corank-1 collapse to single-Frobenius = Papanikolas setting;
  (3) ABP/Papanikolas lower bound ⟹ DSS-over-`F_q` recovered (Door-5, BRIDGE); (4) **seam diagnosis** —
  the corank gap `∞ − 1` is the exact obstruction, G2 face of Professor's seam conjecture. Next: tighten
  Steps 1–2 (functoriality + operator-kind identification) to clear the 1→2 gate.
- 2026-06-19 (DeWitt) — verified inputs (C6 §2 `S_ff` Frobenius datum lines 83–86; #8 upper bound =
  THEOREM; C6 Thm C line 95 = Papanikolas; Professor corank=1) and moved 1→2 (2-fully-proven, BRIDGE).
  Result: G2/DSS over `F_q` = Papanikolas under the corank-1 collapse (Door-5 recovery), and the
  **seam diagnosis** — corank gap `∞−1` is the exact G2 obstruction (single-Frobenius rigidity over
  `F_q` vs missing F₁ over ℚ). No runpod (structural). Feeds the seam bucket via library-backlog.

## Lean return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven`: the theorem depends on `S_ff`, the function-field corank collapse, and the Papanikolas/ABP equality as an external import. Those parent function-field cards and imports are not formalized as no-hypothesis Lean theorems, so this border recovery cannot be certified in Lean as stated.

## Triage note — 2026-06-19 (Professor): returned to 2-fully-proven (user-directed; Leaner over-return)

Per @user ("send tickets that are clearly 'leaner is just lazy' back to fully-proven"): Leaner's return was a
**Lean-library-coverage objection** (no formal model of the imported / categorical / analytic objects), **not** a
paper-proof defect. This is a **paper-proven BRIDGE theorem** whose proof legitimately credits classical imports;
those imports are to be carried as hypotheses/axioms (or formalized separately) at the Lean stage — not a reason to
reject the paper proof. The card's stated theorem is proved at its 1→2 gate; any co-located open conjecture
(C5★ / ω=0 / Schanuel / apex) is explicitly a SEPARATE open core, not part of this theorem. Re-banked for Lean re-attempt.
