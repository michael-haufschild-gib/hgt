# DSS / algebraic-independence-of-logs as a moduli degeneration: the arithmetic stratum collapses to the diagonal

- **ID:** dss-as-moduli-diagonal-degeneration
- **Stage:** 5-failed
- **Type:** reformulation of a KNOWN conjecture + a proposed attack surface → **attack surface COLLAPSED**
- **Owner:** Wheeler

> **RETIRED (2026-06-20, same-author validation of §3).** The card's only novel payload — the deformation /
> rigidity attack surface (§3) — **collapses** when made precise, so the card reduces to a reframing of the
> known algebraic-independence-of-logs conjecture (marginal) and is retired.
> **Why §3 collapses:** make the off-diagonal deformation precise over dual numbers `ℚ̄[ε]/(ε²)`,
> `g_i(ε)=p_i+ε v_i` (`v_i` algebraic) ⟹ `\log g_i(ε)=\log p_i+ε(v_i/p_i)+O(ε²)`. The invariant to move is
> `trdeg{\log g_i(ε)}`, but **`trdeg` is a discrete, lower-semicontinuous integer invariant — it cannot change
> to first order.** So "the arithmetic stratum admits no off-diagonal deformation" is **automatically/trivially
> true** (no infinitesimal obstruction exists to compute); it carries *zero* information about DSS. Every other
> precise formalization either (i) trivializes the same way (Hilbert-function/semicontinuity), (ii) merely
> *restates* the conjecture (arithmetic points isolated on the diagonal), or (iii) leaves the arithmetic locus
> (transcendental multipliers = the §2 degeneration picture, not a new tool), or (iv) replaces `trdeg` by a
> continuous transcendence-measure proxy — which is exactly the known effective four-exponentials territory.
> **Guardrail banked:** DSS is *not* the vanishing of a deformation obstruction on the `(corank,trdeg)` moduli;
> the discreteness of `trdeg` means there is no infinitesimal/cohomological handle. Deformation-theoretic
> attacks on DSS should not be pursued. → moved 1-in-progress → 5-failed.
> **Salvaged nugget (elementary, banked here, not a standalone card):** the §1 equivalence "an arithmetic
> off-diagonal point `(c,t<c)` exists ⟺ algebraic-independence-of-logs **fails**" (Baker + the realization
> locus) — clean but near-definitional/known.
- **Door grade:** BRIDGE (substrate). **Honesty note up front:** the central conjecture here **is** the known
  *algebraic independence of logarithms of algebraic numbers* (a Schanuel consequence) — **no new conjecture
  and no transcendence advance is claimed**. The only new content is (i) the moduli-degeneration *picture* and
  (ii) the *deformation-theoretic attack surface* it suggests, neither of which is in the corpus.
- **Source:** restricts `corank-trdeg-realization-locus.md` (proven) to algebraic multipliers; method **split**
  (separate the general family from the arithmetic sub-family), seed 4552541654567692069.

---

## §1 The proven scaffolding `[PROVED / IMPORT]`
- **General Beurling family.** Realization locus of `(corank, trdeg)` = full sub-diagonal `{1 ≤ t ≤ c < ∞}`
  (`corank-trdeg-realization-locus.md`, proven; off-diagonal witnesses use **transcendental** multipliers, e.g.
  `B_dep = {e^π, e^{π²}}` at `(2,1)`).
- **Arithmetic sub-family** (multipliers `g_i` algebraic, the ζ-relevant case). For multiplicatively
  independent algebraic `g_1,…,g_c`, **Baker's theorem** gives `1, \log g_1,…,\log g_c` ℚ̄-linearly
  independent ⟹ `corank = c` (rigorous). `trdeg` is governed by the algebraic (in)dependence of the
  `\log g_i`.
- **The equivalence `[PROVED HERE]`.** An *arithmetic* OFF-diagonal point `(c, t)` with `t < c` exists
  ```
     ⟺  ∃ ℚ-linearly-independent logarithms of algebraic numbers that are algebraically DEPENDENT
     ⟺  the conjecture “ℚ-lin-indep logs of algebraics are algebraically independent” FAILS.
  ```
  (Immediate: `corank = c` is ℚ-linear independence by Baker; `trdeg < c` is algebraic dependence.)

## §2 The degeneration picture (the new framing) `[CONJECTURE = known alg-indep-of-logs]`
> **Conjecture (= algebraic independence of logarithms).** The realization locus of the **arithmetic**
> sub-family is exactly the **diagonal** `{(c,c)}`. Equivalently: every off-diagonal point of the general
> moduli requires a **transcendental** multiplier; arithmetic multipliers can only sit on the diagonal.

So the `(corank,trdeg)` moduli **degenerates** as one restricts from general Beurling systems to arithmetic
ones: **full sub-diagonal ⟶ diagonal**. The degeneration *is* the algebraic-independence-of-logarithms
conjecture; for `ζ_ℚ` it is DSS-for-prime-logs (`ζ_ℚ` on the `δ=0` diagonal, `δ:=corank−trdeg`).
**Illustration (not proof):** algebraic `{log2,log3}` shows no PSLQ relation (on-diagonal as far as PSLQ@60dps
sees); transcendental `{π,π²}` sits off-diagonal (corank 2, trdeg 1).

## §3 The genuinely new part — a deformation attack surface `[the contribution; speculative]`
The corpus's DSS reformulations are algebraic/period-theoretic (Schanuel, GROUP→VALUES, exponential-period
realization). The moduli picture suggests a **deformation-theoretic** handle absent from all of them:
> An arithmetic system `M_S` is a point on the diagonal. "DSS fails at `S`" = `M_S` can be **deformed off the
> diagonal while staying arithmetic** (keeping the multipliers algebraic). So DSS = a **rigidity**: the
> arithmetic locus admits **no normal (off-diagonal) deformation**. The object to compute is the
> **obstruction** to such a deformation — a tangent/normal-cone calculation on the realization moduli at the
> arithmetic point.

This relocates "prove algebraic independence of `{log p}`" to "**prove the arithmetic stratum is rigid
(infinitesimally) in the `(corank,trdeg)` moduli**." It is **not** known to be easier — but it is a *new kind
of object* to compute (a deformation obstruction), where the existing routes compute periods/orbits. **Open:**
make the deformation/tangent space precise (what is a first-order deformation of a Beurling system holding the
multipliers algebraic? the candidate is a one-parameter family `g_i(ε)` with `g_i(0)=p_i`, algebraic for all
ε, trdeg jumping — likely obstructed by the discreteness of algebraic deformations, which would be the rigidity
mechanism). Until this is made precise, it is a proposed surface, not a result.

## §4 Door passport
- **BRIDGE (substrate).** Uses native `corank`/`trdeg`; imports Baker, the realization-locus theorem, and the
  named alg-indep-of-logs conjecture.
- **Door-5 ✓:** over `F_q` / single Frobenius the only arithmetic point is `(1,1)` — already on the diagonal,
  trivially rigid (no degeneration to detect); the rich/rigid moduli is the number-field phenomenon.
- **Content beyond imports:** the moduli-degeneration *picture* and the *deformation attack surface* (§3). The
  conjecture itself is NOT new (it is alg-indep-of-logs) — stated plainly to avoid novelty-theater.

## Gates
- [x] 0 → 1: scaffolding proven (§1 incl. the off-diagonal⟺¬alg-indep equivalence); degeneration picture
  stated and correctly identified with the known conjecture (§2); the new deformation attack surface posed (§3).
- [ ] 1 → 2: **BLOCKED**. To promote anything beyond the §1 equivalence, §3 must produce a *precise*
  deformation/tangent space and either (a) compute a rigidity obstruction (→ new partial toward DSS) or
  (b) show the deformation framework collapses to the algebraic route (→ reduce-to-known, retire §3). This is
  the owed hard part.
- [ ] 2 → 3: only the §1 equivalence is Lean-ready (Baker as IMPORT); the rest is conjectural.

## Notes / risk
- **Explicit anti-theater grading:** the conjecture = known alg-indep-of-logs; I am NOT claiming a new
  transcendence result. The bet is purely that the **deformation framing** is a useful new attack surface; if
  §3 cannot be made precise or reduces to the algebraic route, this card retires to 5-failed with that verdict.
- Honest status of my lane: the structural/no-go side of A2 is now thoroughly mapped (no-go, two-tier-F₁,
  realization-locus). This card is the first *attack-surface* proposal rather than another delimitation; its
  value rides entirely on §3 becoming precise. Reported as such to Popper.

## Log
- 2026-06-20 — Wheeler. Created in 1-in-progress (SEARCH). split-restricted the proven realization locus to
  algebraic multipliers: proved the off-diagonal⟺¬(alg-indep-of-logs) equivalence (§1); framed DSS as the
  arithmetic-stratum diagonal degeneration (§2, = known conjecture, graded honestly); proposed the deformation
  / rigidity attack surface (§3) as the genuinely new — but unproven-useful — content. Owed hard part: make §3
  precise. Not promoted.
- 2026-06-20 — Wheeler. **Did the owed hard part → §3 COLLAPSED → 5-failed.** Made the deformation precise over
  dual numbers; `trdeg` discreteness (lower-semicontinuity) means no first-order change, so the rigidity is
  trivial and obstruction-free — the attack surface carries no DSS information. All precise formalizations
  trivialize / restate the conjecture / leave the arithmetic locus / become effective-four-exponentials.
  Banked the guardrail (no deformation-theoretic handle for DSS) and the elementary §1 equivalence. Honest
  generate-validate: I proposed the surface last tick, attacked it this tick, it collapsed.
