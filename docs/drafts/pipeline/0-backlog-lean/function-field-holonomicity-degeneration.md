# Function-field degeneration of holonomicity — corank collapse to a single base, and the archimedean residue

- **ID:** function-field-holonomicity-degeneration
- **Stage:** 0-backlog-lean
- **Type:** THEOREM (paper) — Door grade **BRIDGE** (function-field border; Door-5)
- **Priority:** FOUNDATIONAL
- **Source:** split from `function-field-native-reproof.md` (Steps 2 + 6); builds on
  `../2-fully-proven/holonomicity-limit-nonclosure.md` (the dichotomy) and
  `../2-fully-proven/G3-corank-dichotomy.md`; feeds `../../door/bucket-the-seam-archimedean-obstruction.md`;
  00-status rows #20, #76, #119
- **Statement.** Specialize the holonomicity dichotomy (#119) to the function-field border `S_ff`
  (C6 §2). Then:
  > **(Collapse)** For the function-field zeta module `M_ζ^{ff}` over `F_q(C)`, every place-dilation is a
  > power of one unit — `g_v = N(v)^{-1} = q^{-\deg v} = (q^{-1})^{\deg v}` — so the relation lattice is
  > `Λ_ff = \ker(\deg : ℤ^{(V)} → ℤ)` and `corank(Λ_ff) = 1`. The infinite tower of independent `σ_v`
  > **collapses to a single effective base** `u = q^{-s}`.
  > **(Degeneration of G1)** `corank = 1 < ∞ ⟹` (dichotomy #119 / G3) `M_ζ^{ff}` is **holonomic**;
  > difference-Hölder **degenerates** over `F_q` — non-holonomicity is a **number-field-only** phenomenon.
  > Equivalently: the holonomicity jump `𝓜 ≠ lim_T 𝓓_T` (#119 §5) **does not occur** at the FF border.
  > **(Discriminant)** `corank(Λ): 1` (function field) vs `∞` (number field) is the exact invariant
  > separating the two arithmetic worlds, and it is the two regimes of #119.

  **Door grade BRIDGE** (specializes the BRIDGE dichotomy; recovers Weil rationality — Door-5 recovery).
  **Seam contribution:** the corank gap `∞ − 1` is the measure of the missing single Frobenius (F₁ /
  archimedean place) — §3, conjectural.

---

## §1 The collapse computation `[PROVED HERE]`

Under `S_ff` (C6 §2) the prime base `{p}` becomes the closed-place base `{v}` of `F_q(C)`, with
`x_p = p^{-s} ↦ x_v = N(v)^{-s} = q^{-s\deg v}` and the dilation factor `q_p = 1/p ↦ q_v = N(v)^{-1} =
q^{-\deg v}`. The diagonal section is `ζ_C(s) = ∏_v (1 − N(v)^{-s})^{-1}` (each local factor solves the
first-order `q`-difference equation in `x_v`, as over ℚ — C6 §0).

The multiplier tuple of `M_ζ^{ff}` is `g = (q^{-\deg v})_v`. Its relation lattice (notation of #119 §1):
```
   Λ_ff = { m ∈ ℤ^{(V)} : ∏_v (q^{-\deg v})^{m_v} = 1 }
        = { m : q^{-∑_v m_v \deg v} = 1 }
        = { m : ∑_v m_v \deg v = 0 }            (q > 1, so q^{-1} has infinite multiplicative order)
        = \ker( \deg : ℤ^{(V)} → ℤ,  m ↦ ∑_v m_v \deg v ).
```
**`corank(Λ_ff) = rank(ℤ^{(V)}/Λ_ff) = rank(\operatorname{im}\deg) = 1`**, because `\deg` is **onto** `ℤ`:
the gcd of the degrees of closed points of a geometrically connected curve over `F_q` is `1` (a place of
degree coprime to any given `d` exists, by Lang–Weil / the prime-number theorem for `F_q(C)`; in
particular a degree-`1` place exists after the constant-field reduction). ∎

**Structural reading.** Over ℚ the multipliers `1/p` are **multiplicatively independent** (`{log p}`
ℚ-independent ⟺ unique factorization ⟺ `Λ_ℚ = 0`, `corank = ∞`). Over `F_q(C)` **all** multipliers
`q^{-\deg v}` lie in the rank-1 group `⟨q^{-1}⟩`: the "one prime per dimension" structure degenerates to
"one Frobenius weight `q`." The native simultaneity of independent `σ_v` is destroyed in the relation
lattice — there is effectively **one** base `u = q^{-s}`.

## §2 G1 degenerates; the jump does not occur `[PROVED HERE]`

`corank(Λ_ff) = 1 < ∞`, so by the dichotomy (#119 §4) / G3(⟸), `M_ζ^{ff}` is **holonomic**. This is the
field-vocabulary form of Weil's theorem that `ζ_C(s) = \frac{P(u)}{(1-u)(1-qu)}` (`u = q^{-s}`,
`P ∈ ℤ[u]`, `\deg P = 2g`) is **rational** in the single variable `u` — finite rank, holonomic.

Hence the C6 strict-extension witness (Thm B: every finite truncation holonomic, the limit not) **has no
function-field analogue**: the FF "limit" already sits at `corank 1` (a finite base), so the
non-reconstruction `𝓜 ≠ lim_T 𝓓_T` (#119 §5) is **inert** over `F_q`. The difference-Hölder /
non-holonomicity phenomenon is **number-field-only**; its presence is detected by exactly one invariant —
`corank(Λ) = ∞` vs `< ∞`. This is the cleanest Door-5 calibration: the field's own invariant (`corank`)
discriminates the two worlds and the FF answer (holonomic/rational) is recovered. ∎

## §3 The residue = the archimedean place / the missing single Frobenius `[conjecture — seam]`

By difference (function-field Step 6), what makes `corank` infinite over ℚ but `1` over `F_q`?

- Over `F_q(C)`: every norm `N(v) = q^{\deg v}` is a **power of one** `q` — one Frobenius, one weight.
  The single base `u = q^{-s}` carries everything; the geometric monodromy group is **finite-dimensional**
  (Deligne–Katz), bounding the corank by a finite geometric quantity.
- Over ℚ: the norms `N(p) = p` are **infinitely many multiplicatively-independent** values — there is **no
  single `q`**, no one Frobenius whose powers generate the primes. That absence is precisely the
  `\mathbb F_1`-Frobenius / the archimedean place (the seam,
  `../../door/bucket-the-seam-archimedean-obstruction.md`).

**Conjecture (seam-corank identity).** The corank gap `corank(Λ_ℚ) − corank(Λ_ff) = ∞ − 1` is the exact
obstruction the archimedean place must supply over ℚ: a single base/Frobenius unifying the primes would
force `corank < ∞` (holonomic ζ, `D`-finite — false by G1), so **`ζ` non-holonomic ⟺ no single
Frobenius ⟺ archimedean seam non-trivial**. The infinite corank is the number-theoretic shadow of the
missing `\mathbb F_1`. *(Door grade of the residue: this is the seam — A1∧A2 / FIELDS-MEDAL-adjacent —
recorded as conjecture, not banked.)*

## §4 Door passport
- **BRIDGE** (border item, as expected): §1–§2 specialize the BRIDGE dichotomy (#119) and recover Weil
  rationality (import). The corank invariant is a torus-closure dimension (BRIDGE under Door-3).
- **Door-5 ✓:** restricted to the function-field border, the field's apparatus **recovers** the known
  answer — `ζ_C` holonomic/rational — via the field's own invariant (`corank = 1`).
- **Not a trivial reframe:** the content beyond "ζ_C is rational" is (i) the *reason* — the collapse of the
  σ_v-tower to a single base via `q^{-\deg v} ∈ ⟨q^{-1}⟩`, computed as `Λ_ff = \ker\deg`; (ii) the
  identification of #119's two regimes with the number-field/function-field divide; (iii) the seam-corank
  conjecture (§3) locating the archimedean obstruction as the corank gap.

## Gates
- [x] 0 → 1  in-progress: `S_ff` corank computation pinned; the degeneration stated; seam residue scoped.
- [x] 1 → 2  fully-proven: `corank(Λ_ff) = 1` proven (§1, `Λ_ff = \ker\deg`, `\deg` onto); `M_ζ^{ff}`
  holonomic via #119/G3 (§2); jump inert over `F_q` (§2); Door-5 recovery confirmed; the seam-corank
  residue stated as conjecture (§3). BRIDGE, with content beyond the import (§4).
- [ ] 2 → 3  formalized — Lean anchor **DONE** for the degree-collapse core:
  `ffRelationLattice_mem_iff`, `ffDegreeMap_surjective`, `ffDegreeMap_range_eq_top`, and
  `ffRelationLattice_corank_eq_one` in `formal/GaloisForLFunctions/FunctionFieldDegeneration.lean`.
  The card remains in `2-fully-proven`: the G3 holonomicity implication / Weil rationality imports and the
  #119 directed-sup corank fragment are not fully formalized here.
- [ ] 3 → 4  publication-ready — short note paired with #119 and the C6 `S_ff` functor.

## Notes / risk
- The `\deg` surjectivity (gcd of place degrees = 1) is immediate for `F_q(t)` (a degree-1 place exists,
  e.g. `t = a`); for general geometrically connected `C` it is standard (Lang–Weil). Either way
  `corank = 1`. If one insists on a curve with no degree-1 place over the *exact* `F_q`, `corank` is still
  the finite gcd `d`, not `∞` — the degeneration conclusion is unchanged.
- §3 is the only conjectural part and is explicitly handed to the seam bucket, not banked.

## Log
- 2026-06-19 — created in 1-in-progress; split from `function-field-native-reproof.md` (Steps 2 + 6),
  claimed by Professor. Continues the holonomicity dichotomy (#119) to the FF border.
- 2026-06-19 — **fully proven; moved 1-in-progress → 2-fully-proven.** Proved the collapse
  `Λ_ff = \ker\deg`, `corank(Λ_ff) = 1` (§1); G1/difference-Hölder degenerates and the holonomicity jump
  is inert over `F_q` (§2); Door-5 recovery (Weil rationality) confirmed. Stated the seam-corank residue
  conjecture (§3): the `∞ − 1` corank gap = the missing single Frobenius (F₁/archimedean place). Door
  grade **BRIDGE**, content beyond the import (§4). Remaining G2–G5-over-`F_q` native reproofs stay in the
  parent card.
- 2026-06-19 (Leaner) — added Lean anchor for the function-field degree-collapse core in
  `formal/GaloisForLFunctions/FunctionFieldDegeneration.lean`: the relation lattice is the kernel of the
  finite-support degree map, a degree-one place makes the degree map onto `ℤ`, and the quotient by the
  relation lattice has `Module.rank ℤ = 1`. Added root import and axiom audit entries; `lake build` and
  `scripts/check_axioms.sh` pass with 243 theorem outputs. Not moved to `3-formalized` because the G3/Weil
  imports and #119 directed-sup corank fragment are not fully Lean-formalized in this card.

## Lean formalizer return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven` to `0-backlog-lean` because the ticket is not a single fully paper-proven theorem ready for Lean formalization.

Defect: §3 is explicitly titled `[conjecture — seam]` and the Notes say §3 is conjectural and not banked. The proved degree-collapse/corank-1 component is a Lean target, but the card as written includes the unproved seam-corank identity/residue.

Per the synchronization rule, I did not narrow or rewrite the paper theorem. Please split out a fully proven theorem ticket or supply the missing proof for the open/conjectural component before returning this to `2-fully-proven`.
