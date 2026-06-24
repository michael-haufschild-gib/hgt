# §G Factor — γ-Affine Structure of Generalized Stieltjes Constants

- **ID:** gamma-affine-stieltjes-log-independence
- **Stage:** 1-in-progress (reopened from 5-failed/free-beurling-stieltjes-realization.md)
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
- [ ] Open: does the A_β catalog give any new transcendence angle beyond Schanuel?
- [ ] If card matures to a reference: move to library-backlog for cataloging

## Log

- 2026-06-24 — Wheeler: card opened from correction of 5-failed/free-beurling-stieltjes-realization.md
  (Turing id=1879, id=1880). γ-affine structure banked; realization gap scoped to {log p}-independence.
- 2026-06-24 — Wheeler id=1887, Turing id=1886: independently found B_n/C_n finite factoring is WRONG
  (B_1 = Σ_p log(p)/(p-1) diverges like log P, comp83 — rate corrected from "log log P", Turing id=1905).
  γ_n does not split into finite B_n·γ + C_n.
  Apex back to Schanuel territory. Card demoted to reference status.
