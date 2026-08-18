# §G Factor — γ-Affine Structure of Generalized Stieltjes Constants

- **ID:** gamma-affine-stieltjes-log-independence
- **Stage:** 2-fully-proven (not new scientific knowledge; reopened from 5-failed/free-beurling-stieltjes-realization.md, closed 2026-07-12)
- **Type:** CANDIDATE THEOREM — structural fact + open independence question
- **Source:** Turing id=1879, id=1880; correction of Wheeler's 5-failed card (2026-06-24)
- **Parent cards:** bigraded-corank-dss-cross.md §G; corank-arithmeticity-not-cardinality.md

## Banked structural fact `[PROVED HERE — elementary mechanism]`

**Theorem (γ-affine structure of individual A_β):** Every generalized Stieltjes structure constant A_β (with finite-support multi-index β) is ℚ-linear in {γ, log p}:
  A_β ∈ ℚ·γ ⊕ ⊕_p ℚ·log p  (for each β with finite support).

**Proof:** A_β = reg-lim Σ_{k≤x} (∏_p v_p(k)^{β_p})/k. Expand v_p(k)^{β_p} using valuation-indicator sums [p^i|k]; each indicator sum regularizes to (density)·(γ + log x - Σ_i i_p log p) plus lower-order terms. The (log x) part is cancelled by the boundary subtraction. Finite part = D_β·γ - Σ_p (∂D_β/∂log p)·log p, where D_β = Σ_d a_d/d ∈ ℚ (Dirichlet density) and the log-coefficients are rational. ∎

**Verified closed forms (Turing id=1879,1883; numeric at x ≤ 8·10^6):**
- A_{1,p} = γ/(p-1) - (log p)·p/(p-1)^2   (general first-order formula) ✓
- A_{2,2} = 3γ - 10·log2 = −5.199825  (numeric −5.199814, err 1.1e-5) ✓
- A_{(1,1),(2,3)} = γ/2 - log2 - (3/4)·log3 = −1.228499  (numeric −1.228496, err 2.5e-6) ✓
- A_{3,2} = 13γ - 62·log2 = −35.4711  (numeric −35.4711) ✓
- A_{(2,1),(2,3)} = (3/2)γ - 5·log2 - (9/4)·log3 = −5.0718  (numeric −5.0717) ✓

## RETRACTED: the γ_n = B_n·γ + C_n finite factoring `[WRONG — Wheeler id=1887, Turing id=1886]`

The card previously claimed:
  γ_n = B_n · γ + C_n,   B_n, C_n ∈ ℚ-span{log-monomials}  (RETRACTED)

**Why it fails (numerical, comp83):**
γ_1 = Σ_p log(p) · A_{1,p} = γ · Σ_p log(p)/(p-1) - Σ_p (log p)^2·p/(p-1)^2

B_1 = Σ_p log(p)/(p-1) partial sums: 4.16 (p≤100), 6.37 (p≤1000), 8.65 (p≤10000), 10.93 (p≤99000).
DIVERGES like **log P** (= ln P): the partial sums track ln P − 0.577 (ln 99000 = 11.50, 11.50−0.57 = 10.93 ✓),
matching Mertens Σ_p (log p)/p ~ log x. (NOT log log P — that would be ~2.44 at P=99000; the earlier "log log P"
label confused Σ_p 1/p ~ log log x with Σ_p (log p)/p ~ log x.) C_1 = Σ_p (log p)²p/(p-1)² diverges faster,
~ (log P)²/2. Both B_n and C_n are infinite.

**Why the error occurred:** Each individual A_β ∈ ℚ·γ ⊕ ⊕_p ℚ·log p is a FINITE constant. But γ_n is an INFINITE convergent combination of A_β × log-monomials. The γ-coefficient and log-coefficient diverge individually — like a conditionally convergent series where the real and imaginary parts can't be separated. The regularization that makes γ_n finite is EXACTLY the entanglement of γ with the log structure: they can't be separated by finite B_n and C_n.

**What SURVIVES:** 
- A_β ∈ ℚ·γ ⊕ ⊕_p ℚ·log p for each INDIVIDUAL finite-support β. Verified through order 3.
- The correction of the 5-failed card's "wild tower" claim is still correct — {A_β} is NOT a separate tower from {log p}; each A_β is ℚ-linear in {γ, log p}.

## Reformulated open question: algebraic independence of the A_β catalog

Since B_n, C_n are infinite divergent prime sums, the "reduction to log-independence" fails. The correct open question becomes:

**Are the specific A_β values — viewed as elements of ℚ·γ ⊕ ⊕_p ℚ·log p — sufficient to determine trdeg{γ_n} = ∞?**

The Stieltjes constants are determined by {A_β : all β} via convergent infinite sums. The trdeg{γ_n} = ∞ question now reduces to: does the convergent assembly of A_β values produce infinitely many algebraically independent real numbers γ_n?

This is equivalent to: the transcendence question for {γ, log 2, log 3, log 5, ...} over ℚ (Schanuel-type). The γ-affine structure tells us what "basis" the γ_n live over, but doesn't simplify the independence question.

**Correct apex statement:** γ_n are built from A_β ∈ ℚ·γ + ℚ-logs, but the infinite assembly means the trdeg question is inherently about the joint algebraic independence of {γ, log p} — standard Schanuel territory, no shortcut found.

## Remaining novelty

**Banked (elementary, correct):** γ-affine structure of individual A_β with explicit Dirichlet-density mechanism. Closed forms verified through order 3 (5 explicit values). Corrects the "wild tower" claim in 5-failed card.

**Grade revision:** The §G apex has been reformulated twice: wild-tower (WRONG) → finite B_n/C_n (WRONG). Current statement: Schanuel territory. No shortcut survives; the card should transition to reference status.

## Novelty

**Banked part (γ-affine structure):** ELEMENTARY — the regularization calculation is standard; this is explicit change-of-basis at the level of the known bigraded §G factorization. No deep new mathematics. Grade: LOW novelty but CORRECTS a wrong framing.

**Open question (log-independence of {B_n, C_n}):** This IS the genuine §G open core. Whether it's source-new depends on how explicitly the {log p}-transcendence of the C_n/B_n has been studied. Schanuel's conjecture implies it (all values in the list are expected transcendental over ℚ with full independence) but is open. Baker covers linear independence.

## Gates

- [x] 0 → 1: A_β ℚ-linearity proved (elementary); closed forms verified through order 3
- [x] RETRACTED: B_n/C_n finite factoring (WRONG — divergent prime sums)
- [x] Open: does the A_β catalog give any new transcendence angle beyond Schanuel? — NO (verdict 2026-07-12): the pre-registered gate lemma holds but the class is prime-side-only; BRIDGE.
- [x] Card matured to reference: moved to 2-fully-proven/not_new_scientific_knowledge (2026-07-12)

## Log

- 2026-06-24 — Wheeler: card opened from correction of 5-failed/free-beurling-stieltjes-realization.md
  (Turing id=1879, id=1880). γ-affine structure banked; realization gap scoped to {log p}-independence.
- 2026-06-24 — Wheeler id=1887, Turing id=1886: independently found B_n/C_n finite factoring is WRONG
  (B_1 = Σ_p log(p)/(p-1) diverges like log P, comp83 — rate corrected from "log log P", Turing id=1905).
  γ_n does not split into finite B_n·γ + C_n.
  Apex back to Schanuel territory. Card demoted to reference status.

## 2026-07-09 Codex medalist pass — residue: renormalized γ/log non-splitting

Seed: `2744613319640932496`; forced method move: `extreme-cases`.

### Extreme cases

- `[SEARCH]` Finite-support `A_β` remains γ-affine: each lane lives in `ℚ·γ ⊕ ⊕_p ℚ·log p`.
- `[SEARCH]` The `n=0` Stieltjes rung is pure archimedean: `γ_0=γ`; no prime assembly is present, so there is no weld obstruction yet.
- `[BRIDGE]` Finite-prime/Euler-truncated Stieltjes data reduce to symmetric polynomials in finitely many `log p` values; this is the `f1-inversion-single-prime-stieltjes-collapse` / finite-corank theorem, not a native seam theorem.
- `[CONJECTURE]` The first genuinely seam-visible rung is `γ_1`: finite lanes are γ-affine, but the infinite prime assembly refuses to split into a finite γ-coefficient plus a finite log-only coefficient.

### Divergence floor of the failed split

`[PROVED HERE — BRIDGE]` The retracted `γ_1 = B_1·γ + C_1` finite split cannot be repaired by ordinary prime cutoff limits. From the per-prime first-order lane

`A_{1,p}=γ/(p-1)-p(log p)/(p-1)^2`,

the two visible cutoff coefficients satisfy

`B_1(P)=Σ_{p≤P} log p/(p-1) = log P + O(1)`,

`C_1(P)=Σ_{p≤P} p(log p)^2/(p-1)^2 = (1/2)(log P)^2 + O(log P)`.

Proof: replace `1/(p-1)` by `1/p+O(1/p^2)` and `p/(p-1)^2` by `1/p+O(1/p^2)`. The error sums converge. Partial summation plus the prime number theorem gives `Σ_{p≤P} log p/p = log P+O(1)` and `Σ_{p≤P} (log p)^2/p = (1/2)(log P)^2+O(log P)`. Thus neither coefficient has a finite ordinary limit; the finite Stieltjes value is created by the global regularization, not by separately finite γ/log pieces.

Door grade of this paragraph: `[BRIDGE]`. It is PNT/Mertens-level analytic number theory plus the per-prime lane formula; it is useful cleanup, not new native content.

### Candidate native residue

`[CONJECTURE]` The object worth naming is not a new independence claim, but a **renormalized γ/log non-splitting class**. Informally, `γ_n` is the finite part of a two-scale expression in which the archimedean constant `γ` and the prime-log lattice counterterms cancel only after the infinite prime assembly is taken. The class should measure the failure of the map

`finite γ-affine lanes  ->  infinite Stieltjes coefficient`

to commute with the direct-sum splitting `(γ-line) ⊕ (prime-log algebra)`.

`[OPEN CORE]` Make this class scheme-independent. A raw Hadamard finite part depends on cutoff and subtraction convention; to become mathematics in `𝓜⁺`, the class must be invariant under changing the prime exhaustion / equivalent counterterm and must vanish on the border cases above (`n=0`, finite support, finite prime base) while remaining nonzero at `γ_1`.

### Attack

- `[BRIDGE]` If the class is only "PNT divergence of `Σ log p/p`", Door-2 strips it to classical analytic number theory.
- `[BRIDGE]` If the class is only "Hadamard finite part of a divergent series", it is ordinary renormalization language, not native HGT.
- `[CONJECTURE]` It becomes substrate-load-bearing only if it is functorial for the completed `(σ_p, ∂_s)` object: finite prime restrictions kill it, Source-A alone kills it, Source-B alone kills it, and the infinite archimedean-prime weld carries it.

### Next gate

Prove or refute the following precise lemma before opening a new theorem card:

`[CONJECTURE]` There exists a quotient of two-scale cutoff germs `Q_weld` and a canonical element `ε_1 ∈ Q_weld` attached to `γ_1` such that:
1. `ε_1` is unchanged by cofinal prime exhaustion and by adding separable finite counterterms;
2. `ε_1=0` after restricting to any finite prime set or to the `n=0` archimedean rung;
3. `ε_1≠0` because the γ-coefficient pole has order `1` in `log P` while the log-only coefficient has order `2`.

If (1) fails, retire this residue as a useful BRIDGE cleanup. If (1) holds, the next object is a `renormalized seam-extension` card, not another Schanuel-independence card.

## 2026-07-12 Verdict on the pre-registered gate lemma — card closes as BRIDGE

The gate lemma is settled affirmatively, and the class then fails the card's own
substrate-load-bearing test. Both halves are certified.

### The lemma holds

`Q_weld` and `ε₁` exist with properties (1)-(3):

- **Formal core (already in tree):** `formal/GaloisForLFunctions/HTGeometry/SeamNonSplitting.lean` builds the
  quotient of cutoff germs by separable counterterms, the class `seamEpsilonOne`/
  `gammaOneVisibleClass`, its nonvanishing, the descending order-`n` detector hierarchy
  (`cutoffOrderClass_ne_zero`), and detector invariance under representative changes.
- **Analytic realization (new):**
  `formal/GaloisForLFunctions/RHTower/StieltjesLaneCutoffDivergence.lean`, axiom-clean:
  - `tendsto_stieltjesGammaLaneCutoff_atTop` — the γ-lane cutoff `B(x)=Σ_{p≤x} log p/(p−1)`
    diverges;
  - `tendsto_stieltjesLogLane_sub_affineGammaLane_atTop` — for every `r s : ℝ` the log-lane cutoff
    `C(x)=Σ_{p≤x} p(log p)²/(p−1)²` satisfies `C(x) − (r·B(x)+s) → ∞`: the log lane escapes every
    affine renormalization by the γ-lane, which is the machine-checked form of the order-1 versus
    order-2 pole separation in (3).
  - Property (1) follows because `Tendsto _ atTop atTop` is invariant under cofinal exhaustion and
    bounded (in particular convergent-counterterm) perturbations; property (2) because finite prime
    restrictions make both lanes eventually constant.

The affine-escape proof needs strictly less than PNT: prime-harmonic divergence plus the termwise
domination `log q · (log p/(p−1)) ≤ p(log p)²/(p−1)²` for `p > q`. It also certifies, en route,
the retraction of the finite `γ₁ = B₁·γ + C₁` split at machine-checked strength: no real pair
`(r,s)` reproduces the log lane from the γ-lane up to bounded error.

### The class is not native seam content

The card's attack list pre-registered the decisive test: the residue is substrate-load-bearing
only if the infinite archimedean-prime weld carries it and each source alone kills it. The
formalized nonvanishing shows the opposite: the order separation lives entirely on the prime side
(`log P` versus `(log P)²` masses of prime sums); the archimedean constant `γ` enters only as a
spectator coefficient, and no archimedean input appears anywhere in the proofs. Source-B alone
carries the class. Per the pre-registered criterion, the residue reduces to divergence-order
bookkeeping over classical prime sums — a useful BRIDGE cleanup, not native HGT content.

### Disposition

- Banked and correct: γ-affine structure of each finite-support `A_β` (elementary, paper, verified
  closed forms through order 3); the divergence floor of the retracted split (paper + Lean); the
  formal seam-class hierarchy (Lean); the analytic lane certificates (Lean).
- No renormalized seam-extension card is opened: the load-bearing test failed.
- The Schanuel-territory apex statement stands as the honest reformulation; no shortcut exists
  through the `A_β` catalog.

Card moves to `2-fully-proven/not_new_scientific_knowledge` as a reference: correction of the
5-failed wild-tower claim, two retracted apex reformulations with certificates, and the certified
non-splitting floor.

### What this opens

The two-scale mechanism itself — a finite value created only by joint cancellation of two
individually divergent lanes — is now certified on the simplest rung. The forward question is not
independence but *which constraint selects the pairing*: the completed Euler–Gamma constraint
pairs each `γ`-divergence with a specific prime-log counterweight. A native object would be a
pairing rule derived from the completed constraint that reproduces every `γ_n` assembly at once,
rather than rung-by-rung regularization.
