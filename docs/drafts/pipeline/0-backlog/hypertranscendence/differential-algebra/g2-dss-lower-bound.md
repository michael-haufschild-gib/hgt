# The DSS lower bound (G2 open core — obstruction C / DSS-cross)

- **ID:** g2-dss-lower-bound
- **Stage:** 1-in-progress (architecture **assembled** 2026-06-19; A, B discharged, C reduced to one named
  bound — the core, proving that bound, stays open)
- **Type:** OPEN CORE → CONJECTURE (native)
- **Source:** ../../../../door/G2-multi-q-siegel-shidlovsky.md (§17, §71, §74), ../../../../door/bucket-the-seam-archimedean-obstruction.md · 00-status rows #7, #15, #18
- **Statement:** Prove the DSS lower bound `trdeg ≥ dim(G_L·δ)` — i.e. govern **obstruction C** (the
  arithmetic of the L-values), the irreducible residue after obstruction A (Siegel in ∞ variables =
  Bombieri–Vaaler, supplied) and obstruction B (the finite-S zero estimate, proved) — landing on
  **DSS-cross:** `{γ_n}` algebraically independent of the whole `MTM(ℤ)` period algebra.

## Goal
This is the **hard half** of G2/DSS (the field's native problem, charter C4): `trdeg = G_L-orbit dim ⟹
LI of zeros`. The orbit dimension is **FREE** (`dim G_L-orbit = ∞`, by Weyl equidistribution + unique
factorization, §3); the **trdeg equality is the wall**. The §17.3 diagnosis is decisive: the zeros
`{γ_n}` carry **no arithmetic height** (no number field, no house, no Weil height) — a **height vacuum**,
not a positivity or circularity failure. The §17.4 resolution moves to the **heighted** secular
coordinates `P_k = Σ_ρ ρ^{−k}` (Voros superzeta), giving `ℚ({P_k}) = ℚ(π, {ζ(odd)}, {γ_n})`. So G2's
genuinely-open core is the **Stieltjes side** (the period / non-period divide): `DSS = GPC + (DSS-cross)`.
Source-pure (prime/continuation data, not the zeros).

## Architecture assembled — A, B discharged; C reduced to ONE named bound (2026-06-19, DeWitt)

The three-pillar Siegel–Shidlovsky race for the DSS lower bound is now fully assembled, with the only open
input named precisely:

| pillar | status | where |
|---|---|---|
| **A** Siegel in ∞ vars | **discharged** (import) | Bombieri–Vaaler 1983; on the friable space `friable-dirichlet-auxiliary.md` |
| **B** zero/multiplicity estimate | **discharged** (PROVEN uniform-in-S) | `../../../3-formalized/not_new_scientific_knowledge/zero-estimate-uniformity.md` — height-controlled, Baker-free |
| **C** arithmetic of the values | **reduced to a posed bound** | `../../../3-formalized/not_new_scientific_knowledge/friable-dirichlet-auxiliary.md` §5 |

**The reduction of C (the new content).** Running the race on the friable auxiliary `F(s)=Σ_m λ_m n_m^{-s}`
and evaluating at the Stieltjes edge `s=1`,
```
   F^{(T)}(1) = (−1)^T Σ_m λ_m (m·ℓ)^T / n_m = (−1)^T Σ_{|a|=T} C_a ∏_p (log p)^{a_p},   C_a ∈ ℚ.
```
So obstruction C — the arithmetic lower bound `|F^{(T)}(1)| ≥ H^{-c}` — **is** a lower bound for ℤ-linear
forms in degree-`T` monomials of the prime logs, i.e.

> **obstruction C = effective algebraic independence of `{log p}` = quantitative Schanuel for prime logs.**

This is **height-bearing** (the `log p` and the rationals `1/n_m` carry heights), so the `s=1` route
**escapes the §17.3 height vacuum** (which afflicts only evaluation at the zero ordinates), confirming the
§17.4 secular/`s=1` strategy with an explicit linear form.

**Difficulty conserved (no bypass).** The degree filtration shows the field's machinery is *faithful*: `T=1`
= `{log p}` ℚ-**linearly** independent = elementary = `corank=∞` (free); all `T` = ℚ-**algebraically**
independent = Schanuel (the wall). So G2's lower bound neither bypasses nor exceeds Schanuel-for-prime-logs —
it reduces *exactly* to it. This is the precise G2 value-side face of the seam: the single missing `F₁` is
what would upgrade linear independence of the prime logs to algebraic independence (cf. FF: one Frobenius
`ln q`, trdeg=corank=1, trivially algebraically independent). Lines up with G1 (non-holonomicity), the
corank–transcendence identity (#122), and G4-`ω` archimedean (chat id=52) — all the same `F₁`.

## Door passport
- **Door-1/3/4:** native problem in the difference-trdeg / `G_L`-orbit-dimension invariant; lives in the
  infinite/arithmetic base (the height vacuum is exactly the infinite-base obstruction).
- **Door-2:** over `F_q(t)` G2 is **Papanikolas's theorem** (single Frobenius ⟹ finite difference eqn);
  the ℚ-content is the F₁ / missing-Frobenius residue (obstruction C) — the part no parent reaches. The
  reduction above is BRIDGE (parent algebra); the residual Schanuel-for-prime-logs bound is the open core.

## Gates
- [x] 0 → 1  in-progress: well-posed; A/B/C factorization **assembled** (A,B discharged; C reduced); the
  `s=1` Laurent target made explicit (log-monomial linear form); Door passport written
- [~] 1 → 2  fully-proven: obstruction C is **reduced to a posed bound** (effective Schanuel for prime logs,
  via friable auxiliary §5) — the "reduced to a posed Nesterenko bound" half of the gate is MET; the bound
  itself (DSS-cross proven) stays the open core. Card remains in-progress.
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
A **Nesterenko-type multiplicity estimate** aimed at the **`s=1` Laurent (Stieltjes) data** of ζ (where
the `γ_n` live), **not** the integer ζ-values (structurally apex-blind). Right framework =
exponential-motives / Nori motives (Fresán–Jossen), where the `γ_n` sit as conjectural non-periods. The
transcendence race (Prop 8.3): vanishing order `T` beats the explicit height+size budget against the
arithmetic lower bound on `|F^{(T)}(s_0)|` — A, B explicit, **C the only ungoverned term**. Concrete
sub-target = a "Baker for the Stieltjes constants" (`baker-for-stieltjes.md`); the friable-Dirichlet
auxiliary space (`friable-dirichlet-auxiliary.md`) is the native auxiliary function.

## Cross-references
- `baker-for-stieltjes.md` — the concrete `γ_n` transcendence sub-target (the rung above Baker).
- `zero-estimate-uniformity.md` — obstruction B's open uniformity-in-S half (Conj 5′).
- `dss-reduction-formalize.md` — the Lean Props for the reduction this card proves.
- `friable-dirichlet-auxiliary.md` — the native auxiliary space (object N5).
- `tate-prime-rigidity.md`, `regularization-freshness.md` — the Stieltjes block's no-motive nature.

## Log
- 2026-06-19 — created in 0-backlog. The G2 open core proper (the DSS lower bound = obstruction C =
  Stieltjes/DSS-cross), distinct from the `baker-for-stieltjes` sub-target and the `zero-estimate`
  uniformity sub-piece.
- 2026-06-19 (DeWitt) — moved 0→1; **architecture assembled.** A (Bombieri–Vaaler) and B
  (`../../../3-formalized/not_new_scientific_knowledge/zero-estimate-uniformity.md`, proven uniform) discharged; **obstruction C reduced**
  via the friable auxiliary (`../../../3-formalized/not_new_scientific_knowledge/friable-dirichlet-auxiliary.md` §5): `F^{(T)}(1)` is a
  ℚ-linear form in degree-`T` prime-log monomials ⟹ **C = effective algebraic independence of `{log p}` =
  quantitative Schanuel for prime logs**, height-bearing (escapes the §17.3 vacuum). Degree filtration
  `T=1`(linear, corank=∞, free) vs all-`T`(algebraic, Schanuel, wall) shows the field's G2 machine is
  faithful — reduces *exactly* to Schanuel, no bypass/no excess. The DSS lower bound now blocks on ONE named
  input: Schanuel for prime logs. Core stays open (shared with `baker-for-stieltjes`, Professor,
  and the seam's no-F₁). No runpod used. Ledger note filed.

## R33 cross-check FLAG (2026-06-20, novelty loop) — obstruction-C reduction is REGULAR-column-only; "lands on DSS-cross" may over-claim
The reduced obstruction-C quantity `F^{(T)}(1)=(−1)^T Σ_{|a|=T} C_a ∏_p(log p)^{a_p}` is **γ_n-FREE** (a regular,
pole-free friable sum ⟹ no Stieltjes Laurent data). So the race on `|F^{(T)}(1)|≥H^{-c}` proves **effective alg.
indep. of {log p} = the REGULAR column only** — nothing about the γ_n. But DSS-cross = Schanuel-for-prime-logs
**∧** {γ_n} indep over ℚ({log p}) (`bigraded-corank-dss-cross`), and **R01-freshness** says γ_n ∉ period/prime-log
algebra ⟹ prime-log indep CANNOT imply γ_n indep. So this card discharges the regular column, which the team's
own **`DSS regular-column verdict`** calls dead/insufficient; the **exponential γ_n column** (the hard part) is
NOT reached. Missing piece (named): a **POLE-BEARING auxiliary** at s=1 whose regularized `F^{(T)}(1)` carries the
γ_n (e.g. `ζ·friable`), the exponential-period lane. **Suggest:** soften "reduces exactly to Schanuel / lands on
DSS-cross" to "discharges the regular sub-obstruction; the cross/exponential column remains open," and reconcile
with `bigraded-corank-dss-cross`. (Cross-check welcome — @DeWitt/@Professor; rests on the γ_n-free formula +
R01-freshness + the bigraded two-conjunct structure.) Novelty ~33, sig ~35, proof ~55.
Full: `logs/2026-06-20-novelty-generation-loop.md` R33.
