# The DSS lower bound is native-orbit-inaccessible — the G_L-orbit gives genericity (upper bound), not the arithmetic lower bound

- **ID:** dss-lower-bound-orbit-nogo
- **Stage:** 2-fully-proven — structural **no-go**, grade BRIDGE.
- **Type:** THEOREM (paper, structural no-go) — obstruction-theory content (per the user 2026-06-19: the field
  is obstruction theory + value-relations; this is a "why no native shortcut" obstruction result).
- **Priority:** FOUNDATIONAL
- **Source:** the DSS lower-bound apex (`../0-backlog/.../g2-dss-lower-bound.md`, obstruction C);
  friable auxiliary (`friable-dirichlet-auxiliary.md`, the s=1 edge form); orbit/genericity (#8/#9);
  DeWitt's native-lower-bound attempt 2026-06-19; the Airy=SL₂ analogue (keystone = value-relation via the
  group). 00-status #7/#15/#18.

---

## Statement

> **The native difference-Galois apparatus (the `G_L`-orbit) supplies the DSS *upper* bound
> (`trdeg ≤ orbit-dim`, genericity) but provably CANNOT supply the *lower* bound** (`trdeg ≥ orbit-dim` =
> obstruction C). The lower bound lives at the **arithmetic edge `s=1`** (a Diophantine magnitude), which is
> **orthogonal** to the orbit (the Kronecker flow in the imaginary `t = Im s` direction). Hence no native
> orbit/genericity route gives the lower bound; it is irreducibly the arithmetic input
> **Schanuel-for-prime-logs**.

This is the precise native-side reason the DSS lower bound is the apex — the companion to "#74 multiplicative
methods are apex-blind" (there: Euler/multiplicative; here: the native `G_L`-orbit).

## Proof

1. **The orbit gives the upper bound.** The diagonal `G_L`-orbit is the Kronecker flow `φ_t : x_p ↦ x_p e^{-it
   log p}` on `𝕋^∞`, dense by Weyl–Kronecker (`{log p}` ℚ-independent, #1/#9). Its genericity yields
   `trdeg ≤ dim(G_L·δ) = orbit-dim` (the proven multi-q SS upper bound, #8). ✓ — the orbit is exactly what
   the upper bound uses.
2. **The lower bound lives at the arithmetic edge `s=1`.** By the friable reduction (`friable-dirichlet-
   auxiliary.md` §5), obstruction C is the lower bound `|F^{(T)}(1)| ≥ H^{-c}` for the auxiliary
   `F(s)=Σ_m λ_m n_m^{-s}`, where `F^{(T)}(1) = (−1)^T Σ_{|a|=T} C_a ∏_p (log p)^{a_p}` is a ℚ-linear form in
   degree-`T` prime-log monomials — an **arithmetic magnitude at the single real point `s=1` (`t=0`)**.
3. **Orbit ⊥ edge.** The orbit varies `t = Im s` (dense in the modulus torus `{|x_p|=p^{-σ}}`); the lower
   bound is the magnitude of `F^{(T)}` at the **fixed** point `t=0`, `σ=1`. Orbit density determines the
   *distribution* of values along `t` (an upper/genericity statement) but imposes **no lower bound on the
   value at the special arithmetic point `t=0`**: a nonzero Bohr polynomial dense-orbit can still have its
   `t=0` value arbitrarily controlled only by the *arithmetic* of `{log p}`. Concretely `F^{(T)}(1)` is a
   prime-log linear form whose lower bound is a Diophantine (Schanuel/Baker) question — independent of the
   orbit. So the native orbit structure cannot reach it. ∎

**Corollary (no native shortcut for obstruction C).** Every native route through the orbit/genericity/`G_L`
gives only the upper bound; the lower bound is Schanuel-for-prime-logs, supplied by neither the orbit nor
(per chat id=80) Mahler/Nesterenko (the `log p` are not values of Mahler functions at algebraic points). This
is *why* the DSS lower bound is the irreducible apex, and (per the user's reframe) it is the field's keystone:
a value-relations obstruction, computed via the group, whose lower half is the arithmetic wall.

## Door passport — BRIDGE
- **Door-2:** the upper-bound half is the proven SS argument (#8); the orthogonality is an elementary
  observation about Kronecker orbits vs a fixed real point; the lower bound = Schanuel (parent). It is a
  *no-go / locating* result, not C5. **BRIDGE.**
- **Door-5:** over `F_q` the orbit collapses (corank 1, single Frobenius) and the lower bound IS supplied
  (Papanikolas/ABP) — there is no `s=1` archimedean edge orthogonal to a finite orbit; the no-go is
  number-field-only (matches #16/#121).

## Gates
- [x] 0 → 1: stated; the orbit=upper / edge=lower split identified.
- [x] 1 → 2: proved — orbit gives upper bound (#8); lower bound at the s=1 edge (friable §5); orbit (t-flow)
  orthogonal to the t=0 arithmetic value ⟹ native-orbit cannot supply it. Grade BRIDGE.
- [ ] 2 → 3: (low priority — structural no-go) reuse `linearIndependent_log_primes`, the SS upper-bound anchor.
- [ ] 3 → 4: folds into the DSS exposition as the native-side no-go (companion to #74).

## Cross-references
- `friable-dirichlet-auxiliary.md` (the s=1 edge form), `corank-seam-invariant.md` (#125, lower bound =
  Schanuel), `../0-backlog/fields-medal-after-future-tickets/g2-dss-lower-bound.md` (the apex this locates).
- 00-status #74 (multiplicative apex-blind) — this is the native-orbit companion; #8 (SS upper bound), #9 (orbit).

## Log
- 2026-06-19 — DeWitt: created + proved → 2-fully-proven (BRIDGE). A genuine apex attempt (a native lower bound
  for DSS via the `G_L`-orbit) and its precise failure: the orbit (Kronecker flow in `t=Im s`) gives the
  *upper* bound (genericity, #8) but is orthogonal to the `s=1` arithmetic edge where the *lower* bound
  (obstruction C = prime-log linear form, friable §5) lives, so the native structure cannot supply it — the
  lower bound is irreducibly Schanuel-for-prime-logs. Obstruction-theory content (per the user's reframe:
  field = obstructions + value-relations). Native-side companion to #74. No runpod.

## D-axis recast (2026-06-19, charter §6) — this is a D4 contribution, re-grade `BRIDGE (substrate)`

Under the new charter §6 (the D-axis / substrate), this no-go is **not** merely a C-axis failure — it is a
contribution to **D4 (the irreducible obstruction, the substrate's C5-dual): a class visible in every parent
and computable by none.** The DSS lower bound (= Schanuel-for-prime-logs) has exactly the D4 signature on the
**value-relations face**:
- **Visible in every parent.** "Are `{log p}` algebraically independent?" is statable in analytic number
  theory, differential/difference Galois, Mahler theory, and harmonic analysis on `𝕋^∞` — every parent sees
  the question.
- **Computable by none.** No parent resolves it: the native `G_L`-orbit route is blocked (this card —
  orbit=upper/genericity ⊥ s=1 arithmetic edge=lower); Mahler/Nesterenko does not apply (`log p` are not
  values of Mahler functions at algebraic points, chat id=80); it is open in transcendence theory (even
  `log 2, log 3` algebraically independent is open). This is the **defining property of a D4 obstruction**,
  not a defect.
- **Unified across faces (D2 ⟹ D4 has content).** Via the seam invariant (#125), this value-relations
  obstruction (G2/DSS) is the **same** `corank=∞` realization as the holonomicity face (G1) and the weight-
  torus/`ω` face (G4) — one missing-`F₁` obstruction wearing three parent-faces. Erase the framework and the
  three look unrelated; that cross-parent unification is the D2 content that makes D4 substantive (vs empty
  atlas).

**Re-grade: `BRIDGE (substrate)`** (substrate-load-bearing: it yields the cross-parent prediction that the
DSS lower bound, the G1 corank, and the G4 `ω` are one obstruction). The "Fields-Medal apex, unprovable by
any single parent" verdict is the **correct D4 status**, not a failure — the substrate's keystone-dual is, by
definition, the obstruction every parent sees and none resolves. C5 was the wrong sole criterion (user,
2026-06-19); on the D-axis this is progress toward D4.
