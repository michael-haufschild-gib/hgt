# MWM Research Plan — concrete moves

Companion to `00-approach.md`. Every arc terminalizes: each card ends in `2-fully-proven` /
`3-formalized` or `5-failed` with the blocker named. Register: plan text is SEARCH; every
deliverable crosses the gate individually.

## Verified toolchain ground (probed 2026-07-03, `lake env lean` on this toolchain)

| Name | Status |
|---|---|
| `riemannZeta : ℂ → ℂ` | exists |
| `completedRiemannZeta : ℂ → ℂ` (poles at 0, 1) | exists |
| `completedRiemannZeta₀ : ℂ → ℂ` (entire variant; Λ = Λ₀ − 1/s − 1/(1−s)) | exists |
| `completedRiemannZeta_one_sub : Λ(1−s) = Λ(s)` | exists (the FE) |
| `RiemannHypothesis : Prop` | exists (unfold with `#print` before A2) |
| `riemannZeta_eulerProduct_tprod`, `_hasProd` (Re s > 1) | exist |
| `riemannZeta_ne_zero_of_one_lt_re` | exists |
| `riemannXi` | **does not exist** — Arc A defines ξ itself |

ξ in Lean: define `xi s := s * (s − 1) / 2 * completedRiemannZeta s` extended across the two
poles (the factor clears them; equivalently express via `completedRiemannZeta₀`:
s(s−1)Λ(s) = s(s−1)Λ₀(s) + (2s−1)·(pole bookkeeping) — do the algebra in Lean once, bank it).
On Ω = {Re s > 1/2} only the pole at 1 matters.

Reusable in-repo machinery (all axiom-clean, file:line pinned in `00-approach.md` §2.3):
`exists_analyticOnNhd_pow_eq`, `analyticOnNhd_of_continuousOn_exp_eq`,
`u0_coherent_kummer_tower` (pattern), `noRelation_pow_descent(_both)`, `meroField`,
`index_formula_split` + `IndexWiring*`.

---

## Arc A — Bank the language (Lean, pure execution, gate-exempt "just work")

**A1. `KummerObstruction.lean` — the general lemma set.** For Ω ⊆ ℂ open simply connected,
f analytic on Ω, Z := f⁻¹(0) discrete:
- (i) *root ⟺ divisibility*: (∃ g analytic on Ω, g^n = f) ↔ (∀ ρ ∈ Z, n ∣ ordₚ f ρ).
  Forward: order arithmetic. Backward: analytic log on Ω∖Z along paths; monodromy around ρ is
  2πi·ord; n ∣ ord makes exp(log f / n) single-valued; |g| = |f|^{1/n} → 0 gives removable
  singularity (mathlib: `Complex.analyticAt_of_...` / removable-singularity API — probe names
  first per discipline).
- (ii) *coherent tower where zero-free*: repackage the `u0_coherent_kummer_tower` construction
  generically (one log L on a zero-free simply-connected Ω; χ_k := exp(L/2^k)).
- (iii) *monodromy character*: the map H₁(Ω∖Z) → ℤ/2^k, loop ↦ winding-weighted multiplicity
  sum mod 2^k, as the obstruction object. Minimal version: per-zero local character (avoid
  full H₁ API; a circle around each ρ suffices for (i)).
- Numerical pre-cert: none needed (soft analysis). Terminalize: axiom-clean file + card.

**A2. `RiemannTower.lean` — the equivalences against mathlib's ζ.**
- Define `xi`; prove entirety, FE `xi_one_sub`, `xi(s̄) = conj(xi s)`, zeros of xi on Ω = zeros
  of riemannZeta on Ω (using `riemannZeta_ne_zero_of_one_lt_re` + Γ nonvanishing — probe
  `Complex.Gamma_ne_zero`), no zeros with Re s ≥ 1.
- `RH_ladder (k) : Prop := ∀ ρ, 1/2 < ρ.re → xi ρ = 0 → 2^k ∣ analyticOrderAt xi ρ`
  (probe the current order-of-vanishing API name: `analyticOrderAt` vs `AnalyticAt.order`).
- Theorems: `rh_iff_tower` (mathlib `RiemannHypothesis` ↔ coherent ℤ₂-tower of xi on Ω),
  `rh_ladder_root : RH_ladder k ↔ ∃ g, AnalyticOnNhd ℂ g Ω ∧ ∀ s ∈ Ω, g s ^ 2^k = xi s`,
  `rh_iff_forall_ladder : RiemannHypothesis ↔ ∀ k, RH_ladder k`.
- This gives hgt its first machine-checked statements ABOUT ζ. Terminalize as above.

**A3. Cocycle formalization (defer until C1 stabilizes the definition).** Box-winding
w_k(T) via mathlib's argument principle; only worth Lean once the paper-level Reduction (C1)
fixes the exact invariant.

First action: A1 (i). Estimated single session including name probes.

---

## Arc B — The parity target RH_2 (open mathematics; the gate-bearing arc)

**B1. Attack-as-false: engineer an FE + positive-log system with an odd off-seam zero.**
Banked status (audit F2, door bucket X5): positivity WITHOUT the FE is settled — DMV Beurling
systems are positive with generic off-line zeros, so the ONLY live cell is the conjunction
FE ∧ positivity, and Arc B is a parity-side probe of the bucket's realization problem #85
(positivity ∧ genericity ∧ FE ⟹ Euler-realized?). The intersection to probe: functional
equation (any Γ-factor completion, symmetry line L) × log with nonnegative "prime-type"
coefficients × a zero of odd multiplicity strictly right of L. Sub-moves:
- Shifted/derived combinations of ζ, L-functions: check each candidate's log-positivity by
  hand (recorded dead end: ζ(s)/ζ(2s) has mixed signs at p^{2j} — coefficient
  Λ(p^{2j})/log p^{2j} − Λ(p^j)/log p^j = 1/(2j) − 1/j < 0; shifted ζ(s−δ) keeps positivity
  but its zeros sit ON its own shifted symmetry line — the statement is FE-relative, so no
  kill).
- Beurling systems: positivity is free (any generalized-prime measure), the FE is the scarce
  resource. Start from the banked DMV constructions (off-line zeros generic in 𝓟 — door bucket
  X5) and ask whether an FE can be GRAFTED onto one; if the class "Beurling + FE" is provably
  thin (Hamburger-type rigidity — check #3), the emptiness proof IS a parity theorem for that
  class and direct progress on realization problem #85. Either exit terminalizes:
  counterexample → FE∧positivity insufficient, name the discriminating Euler feature;
  emptiness theorem → bank it.
- Dirichlet polynomials × Γ-completions: small explicit families, mpmath zero-search with
  PRE-REGISTERED prediction (guard: predict *before* running; if theory predicts the outcome,
  don't run).

**B2. Landau-mod-2 lemma hunt.** Candidate lemma shapes, weakest first:
- L1: f = exp(g) on Re s > 1, g Dirichlet series with coefficients ≥ 0, f continues
  meromorphically past 1 with FE about Re s = 1/2 and finite order ⟹ the divisor in
  1/2 < Re s < 1 has some divisibility/pairing structure. (Expect FALSE as stated — B1 hunts
  the counterexample; each failure refines the hypothesis. The FE clause is NOT optional:
  dropping it makes L1 banked-false via DMV, audit F2.)
- L2 (pair version): zeros right of the line come in pairs coupled by the FE + reality — NOT
  ρ ↔ ρ̄ (both already in Ω) but a genuinely new pairing, if one exists. The q62 lesson
  (`Rigidity`: pair the object with its symmetry-partner and let the relation die between
  them) suggests hunting a second involution. Wild-analogy slot: run `scripts/rng` collision
  when stuck here — this is where the leap belongs.
**B3. Real-structure equivariance (small Lean).** Conjugation-invariant cycles carry even
winding; the level-1 obstruction lives on classes separating ρ from ρ̄. Concrete lemma on
boxes: for T < 0 < T+H symmetric boxes, winding is even. Banks the "seam of the double tower"
picture (§3.4) formally.

First action: B1 Beurling+FE literature scoping (method exception: tooling/prior-work search,
not answer-search) + B2/L1 falsification attempt on paper.

---

## Arc C — The mechanism (defect recurrence; Bagchi coarsening; index transposition)

**C1. The Reduction, rigorous (paper first).** Theorem draft: *Fix σ₀ > 1/2, H > 0, k. If
w_k(T₀) ≠ 0 for some T₀ and the defect set {T : w_k(T) ≠ 0} is relatively dense, then
lim sup N(σ₀,T)/T > 0.* Combined with Ingham (N(σ₀,T) ≪ T^{3(1−σ₀)/(2−σ₀)} log^C T = o(T)):
defect-recurrence ⟹ w_k ≡ 0 ⟹ (box-shrinking) 2^k ∣ m(ρ) right of σ₀. Write with full
care about boundary zeros (define w_k by interior winding on a.e. box; the step function is
right-continuous with discrete jumps). Deliverable: pipeline card, paper proof; Lean later
with Ingham as an explicit hypothesis (Ingham is not in mathlib; NO axioms — state the
implication with the density bound as a named hypothesis).
**C2. Bagchi positioning (check #1 — do FIRST in this arc).** Fetch and read Bagchi's actual
statement/proof (thesis 1981; Math. Z. ~1982 paper). Questions to answer: (a) is his strong
recurrence sup-norm on compacts of the open strip? (b) does his proof pass through zero
counting (if so, the mod-2^k coarsening may be implicit — extract it and cite, don't
rediscover); (c) does ANY follow-up literature state a coarse/topological-invariant version?
Outcome routes: implicit-in-Bagchi → novelty item 2 downgrades to "formalization +
ladder-grading of known"; absent → item 2 stands.
**C3. Explicit formula as index formula.** (a) Express w_k as ∮ ξ′/ξ mod 2^k and connect to
S(T)-type quantities mod 2^k; (b) inventory which test-function families in the explicit
formula see parity of local counts (expect: none classically — that absence is the opening);
(c) transpose the `index_formula_split` + resonance-pinning pattern: what plays "resonance"
for a non-recurrent defect against the {j log p} frequency set? Candidate: transient vs
almost-periodic spectral content (Wiener-type decomposition of the defect indicator).
Deliverable: a precise statement of mechanism M1 as a conditional theorem
("if the defect term's Bohr spectrum is disjoint-in-weight from the prime side's, then
defect ⟹ recurrence"), then attack its hypothesis.
**C4. Coarse Bohr continuity (M2).** Make "the ℤ/2^k monodromy datum extends to T^∞"
precise: the datum as a function of the finite-truncation coordinates (p ≤ X) plus a tail;
the question is tail-insensitivity of a discrete invariant. Expect hard; card it, attack
as false first (construct a toy where a discrete invariant of an a.e.-convergent random
product is NOT tail-measurable — if impossible in the relevant class, that impossibility is
M2's engine).

First action: C2 (an hour of verified reading changes the whole arc's shape), then C1.

---

## Arc D — Family picture (orientation; lower priority)

**D1. D–H disconnected-member card.** Verify the known Davenport–Heilbronn off-line zero
numerics (check #6); record its log's failure of positivity explicitly; its off-line zeros
are the "escaping orbit" datum. Compute nothing that theory predicts (multiplicity-1 winding
is predictable — no compute).
**D2. Hamburger rigidity kernel (check #3).** Exact hypotheses; position as the
"connectedness-locus rigidity" of §7; identify the regularity gap between Hamburger-rigid
(Dirichlet series) and D–H-flexible (linear combinations) — the parity question lives in
that gap.
**D3. Partial-Euler / Deep-RH interface (check #4).** Their renormalized convergence vs our
coarse monodromy: is level-k defect-recurrence implied by (much weaker than) DRH? A
one-session map, then card or drop.

---

## Sequencing, entropy, guards

- **Default order:** C2 (verified reading) → A1/A2 (bank language while fresh) → C1 (paper
  Reduction) → B1/B2 (open math) → C3 → rest. At each session start `scripts/rng seed`, and
  when choosing among open arcs `scripts/rng pick A B C D` — the plateau guard: if two
  consecutive sessions produce only re-derivations, force a wild-analogy collision on B2/L2.
- **Checks discipline:** items #1–#7 of `00-approach.md` §8 are the ONLY sanctioned
  literature lookups (positioning/prior-work, the narrow exception); the problem itself is
  not to be searched.
- **Promotion gate:** nothing from this lane enters `2-fully-proven`/Lean without the full
  verification gate; every Lean name probed in /tmp first; `#print axioms` on every capstone.
- **No-go guards:** never argue independence ⟹ RH (ω = 0 ⇏ RH); no positivity kernel enters
  silently (attack-as-false #4 in `00-approach.md` §9); computations only where theory does
  not predict the outcome, predictions pre-registered.
- **Mailbox:** post the RH_{2^k} ladder + Reduction to the parent-lab mailbox once C1 is
  paper-proven (it is seam-relevant for the other agent's DSS work only via the explicit
  formula — flag, don't oversell).

## Success criteria (what "progress" means here, in order of strength)

1. Any unconditional defect-recurrence statement for a restricted box family (even σ₀ near 1,
   even k = 1) — the first nontrivial rung.
2. A proved parity lemma (L1-type, any nonempty hypothesis class) or a clean counterexample
   with the discriminating feature named.
3. C1 Reduction paper-proven + A1/A2 formalized: the language banked, the burden relocated
   onto one named a.p. statement.
4. The C3 conditional theorem (M1 made precise) with its hypothesis isolated as the new open
   core — the successor document to this one.
