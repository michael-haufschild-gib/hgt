# Corank as the unifying seam invariant — the `∞ − 1` identity (G1 ∧ G2 ∧ G4, one number)

- **ID:** corank-seam-invariant
- **Stage:** 0-backlog
- **Type:** CONJECTURE (native-invariant candidate — the seam read on the corank face)
- **Priority:** FIELDS MEDAL
- **Source:** the proven corank trilogy
  `../2-fully-proven/G3-corank-dichotomy.md`,
  `../2-fully-proven/holonomicity-limit-nonclosure.md` (#119),
  `../2-fully-proven/function-field-holonomicity-degeneration.md` (#121),
  `../2-fully-proven/g4-over-fq-deligne-katz.md` (#122),
  `../2-fully-proven/corank-transcendence-continuation-bridge.md`,
  `../2-fully-proven/g2-over-fq-papanikolas-dss.md`;
  ../../door/bucket-the-seam-archimedean-obstruction.md · 00-status rows #20, #76, #119, #121, #122
- **Statement (to shape).** Let `Λ_M ⊂ ℤ^{(P)}` be the relation lattice of an infinite-base multi-`q`
  module and `corank(Λ_M) = rank(ℤ^{(P)}/Λ_M) = dim⟨g⟩-closure` (G3). For the arithmetic module `M_ζ`:
  > **(Unification — one number, three faces)** `corank(Λ)` simultaneously controls
  > **(G1)** holonomicity (`< ∞ ⟺` holonomic, #119/G3),
  > **(G2)** continuation/period transcendence (`trdeg(T_{s_0}) ≤ corank`, the FF instance exact = 1,
  >   `corank-transcendence-continuation-bridge`), and
  > **(G4)** the weight/Tate torus (`dim W = corank`, `g4-over-fq-deligne-katz` §2).
  > **(Border collapse — proven)** Over every finite border and over `F_q(C)`, `corank` is **finite**
  > (`= 1` over `F_q`: all multipliers are powers of one `q`, `Λ_ff = \ker\deg`, #121); the three faces
  > all degenerate to their classical (Weil / Papanikolas / Deligne–Katz) answers.
  > **(Seam identity — conjecture)** Over ℚ, `corank(Λ_{M_ζ}) = ∞` (unique factorization, `{log p}`
  > ℚ-LI), and the gap `corank(Λ_ℚ) − corank(Λ_ff) = ∞ − 1` is **exactly** the structure the archimedean
  > place / `F₁`-Frobenius must supply: a single unifying Frobenius would force all three faces finite
  > (holonomic `ζ`, DSS-provable periods, rank-1 weight torus), contradicting G1. So
  > **`ζ` non-holonomic ⟺ no single Frobenius ⟺ `corank = ∞` ⟺ archimedean seam non-trivial**, with the
  > infinite corank *realized* as genuine transcendence on all three faces at once.

  **One sentence:** the corank of the difference-Galois lattice is the number-theoretic shadow of the
  missing single Frobenius — `1` where it exists (`F_q`), `∞` where it does not (ℚ) — and the `∞ − 1`
  gap is the archimedean seam itself, the same gap on the holonomy, transcendence, and weight faces.

## Goal
The proven layer computes `corank` and proves its **upper-bound / border** half on each face separately
(the three bridges above). What no card yet states as one object is that these are **one invariant with
three faces**, and that the *open* content is a **single lower-bound realization** over ℚ: that
`corank = ∞` is not merely an upper bound that goes vacuous but is **attained as actual transcendence /
non-holonomicity / weight-torus-rank** simultaneously. Banking this would discharge, in one stroke, the
number-field exclusivity of G1 (already proven, but as an *upper-bound* phenomenon), obstruction C of G2
(`baker-for-stieltjes`), and the ℚ weight-torus rank of G4. It gives the seam — currently only a **door
bucket** — a concrete pipeline home as a *corank* problem, which is the form in which it is actually
computable.

## Door passport
- **Door-3 (the live question):** as currently defined `corank` is a torus-closure dimension — a renamed
  classical algebraic-group invariant, graded **BRIDGE / fails Door-3** (G3 verdict). The conjecture is
  that corank becomes **NATIVE exactly at the seam**: the *realization* (lower bound) that `corank = ∞`
  is genuine independent transcendence is Door-3-surviving content, because no single-prime / single-
  Frobenius parent can pose "the corank is infinite **and attained**." So **corank-native ⟺ seam
  non-trivial** — the corank-face analogue of the proven `C3-native ⟺ C5★`.
- **Door-2:** the FF computation (`corank = 1`) and the per-face upper bounds are BRIDGE (Weil /
  Papanikolas / Deligne–Katz + unique factorization, all parents). The ℚ lower-bound realization is the
  candidate native residue.
- **Door-5 ✓:** restricted to the FF border the invariant **recovers** the known answers on all three
  faces (`corank = 1`: rational `ζ_C`, DSS=Papanikolas, rank-1 weight torus).
- **Relation to C5★ (keep distinct):** C5★ is the *branchhood* lock (combination-mode Baker
  reducibility, `../1-in-progress/combination-mode-baker-reducibility.md`); this seam-corank identity is
  the *archimedean* lock (the `∞−1` Frobenius gap). They are siblings, not the same theorem — flag any
  surfaced overlap rather than merging.

## Approach
1. **Write the unified statement.** Pin one definition of `corank(Λ_M)` and prove (assemble from #119/
   #121/#122) the single proposition "`corank` controls G1, G2, G4 faces" — the three-faces lemma that is
   currently implicit across three cards. This half is essentially **bookkeeping of proven results** and
   should clear 0 → 1 cleanly.
2. **State the lower-bound realization precisely** on each face over ℚ and identify their common core: is
   "`trdeg{γ_n} = ∞`" (G2, `baker-for-stieltjes`) **equivalent** to "weight torus has infinite corank"
   (G4) and to "`ζ` non-holonomic" (G1)? G1 is **proven** (non-holonomic), so use it as the **anchor**:
   does G1's `corank = ∞` already *force* the G2/G4 realizations, or are they strictly stronger? Settling
   this implication structure is the first real theorem and may itself be bankable (a BRIDGE reduction
   "G1 ⟹ partial G2/G4 realization").
3. **Localize the irreducible residue.** Whatever does **not** follow from G1 alone is the genuine seam
   content (obstruction C). Door-2 it: finite-border = parents (BRIDGE); infinite-base uniform attainment
   = the archimedean obstruction. Hand the irreducible core to the seam bucket / `baker-for-stieltjes`
   rather than duplicating their analytic work here.
4. **Pre-certify numerically** (mpmath, archive in `computations/`) before any Lean: the FF `corank = 1`
   collapse and the ℚ corank-growth `c_T = |T| ↑ ∞` on truncations, as the floor under the identity.

## Cross-references
- `../2-fully-proven/corank-transcendence-continuation-bridge.md` — the **G2 face** (proven upper bound +
  exact FF `trdeg = corank = 1`); this card is the **unified invariant**, that card the transcendence
  realization. Coordinate; do not duplicate the Stieltjes analysis.
- `../1-in-progress/baker-for-stieltjes.md` — the **analytic ℚ instance** of the G2 lower bound. This
  card supplies the *unifying corank framing*; that card does the Stieltjes transcendence.
- `../2-fully-proven/g4-over-fq-deligne-katz.md` (§2 weight/angle split), `#121` (FF collapse),
  `#119`/`G3` (the dichotomy) — the **G1/G4 faces**.
- `../../door/bucket-the-seam-archimedean-obstruction.md` — the seam home; this card is its pipeline
  realization on the corank face.

## Gates
- [ ] 0 → 1  in-progress: unified `corank` definition + the three-faces proposition assembled from
  #119/#121/#122; the ℚ lower-bound realization stated per face; Door-3 question sharpened; seam coupling
  pinned
- [ ] 1 → 2  fully-proven: the implication structure among the three ℚ realizations resolved (G1-anchored);
  the irreducible residue isolated and Door-2'd, or handed to the seam effort with a definite verdict
- [ ] 2 → 3  formalized: Lean targets — `corank(Λ_ff) = 1` (reuse #121, `\deg` onto) and the directed-sup
  corank growth `c_T = |T| ↑ ∞` for `M_ζ` (reuse `finitePrimeLogAnnihilator_eq_singleton`,
  `linearIndependent_log_primes`, both ledgered)
- [ ] 3 → 4  publication-ready: standalone note "corank = the missing single Frobenius," the one-number
  unification of the three FF-degeneration cards + the seam identity

## Log
- 2026-06-19 — created in 0-backlog. Promotes the seam-corank `∞ − 1` conjecture from a door bucket to a
  concrete pipeline ticket on the **corank** face: unifies the three proven corank bridges (G1
  non-holonomicity #119, G2 transcendence, G4 weight torus #122) as one invariant and isolates the open
  content as a **simultaneous lower-bound realization over ℚ**, G1-anchored. Door-3 question: corank-native
  ⟺ seam non-trivial (the corank analogue of the proven `C3-native ⟺ C5★`). Kept distinct from C5★
  (branchhood lock) — this is the archimedean lock. First step = assemble the three-faces proposition.
</content>
