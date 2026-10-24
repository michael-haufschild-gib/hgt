# Signed Successor Arithmetic (SSA)

- **ID:** signed-successor-arithmetic-2026-10-24
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) — research programme
- **Source:** `docs/reports/review-2410/fable.md` §3 (the field the walls ask for)
- **Statement:** Develop the quantitative theory of signed multiplicative data along the successor
  `n ↦ n+1`, in which cancellation is produced by counting and read at a single scale.

## Goal
Lean programme `formal/GaloisForLFunctions/SignedSuccessorArithmetic/` with umbrella
`SignedSuccessorArithmetic.lean` (wired into `MainTheorems.lean`), a foundational README, and
unconditional theorems on the research topics of fable.md §3.8.

## Plan (topics → modules)
- **A. Successor sign calculus.** CM signs `f : ℕ → ℤˣ`; successor sign `σ(n) = f(n)f(n+1)`;
  dilation cocycle `∏_{j<m} σ(mn+j) = σ(n)`; cocycle ⟺ complete multiplicativity (primes suffice);
  reconstruction `f(n) = ∏_{k<n} σ(k)`; cocycle is blind to the prime values.
- **B. The successor floor.** Binary recursion `a(2n)+a(2n+1) = 1 + σ(2n)a(n)`; exact two-scale
  identity `C[2,2N+1] + C[1,N] = −N + 4E_N` (`E_N` = doubled agreements ≥ 0); natural two-scale law
  `A(2N+1)+A(N) ≥ N`; log floor `Σ_{n≤N} a(n)/n ≥ (1/3)log N − C`.
- **C. Sharpness at conductor 3.** χ₃-twins: exact count `A(3J+2) = J + [f(J+1) = −ε]`, zero doubling
  defect, log density exactly 1/3 → the floor −1/3 is optimal.
- **D. Calibration over 𝔽_p.** Successor correlation of characters `S(χ,ψ) = χ(−1)J(χ,ψ)`;
  `S(χ,χ⁻¹) = −1`; `|S|² = p` (square-root cancellation is a count).
- **E. Conductor quantization.** Legendre twins mod odd prime p: successor bias −1/p.
- **F. Selectivity.** Alternating control, parity-twin control, lag-2 bracket; cocycle blindness.
- **G. Topic 3 (hypercube form).** Candidate no-go: partial Euler products diverge in 1/2<σ<1 by
  PNT coherence (pole), so the hypercube Dirichlet form is unbounded for 0<ε<1/2 unconditionally.
  Needs Mellin/spectral representation (`RHTower.MellinL2`, `physicalToSpectralUnitary`).
- **H. Further topics** (Witt structure as estimate, index exit model, scale matching) — after A–G.
- **I. README.**

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Status
- Fourteen-file programme: umbrella + 13 modules, all checked with `lake --old env lean`, wired into
  `SignedSuccessorArithmetic.lean` (wired into `MainTheorems.lean`). README v2 (§§3.1–3.11, pillars
  1–37). Axiom audit: main theorems use only propext, Classical.choice, Quot.sound.
- Resolved: review topic 3 / BVI §7.5 — the prime-supported hypercube form is unbounded for
  −1/2 ≤ ε < 1/2 (pole-driven); survivor: size-truncated form (spectral identity built).
- Open (README §7): λ beyond conductor 3, square-root scale over ℤ, borderline ε = 1/2 and
  size-truncated boundedness in 1/2 < σ ≤ 1, zero-defect classification, lag floors, complex floor
  constant in [−1/2, −1/3], μ calculus, index exit, Kloosterman to balanced Gram, Witt.

## Log
- 2026-10-24 — created. Corpus survey: BVI (incidence counts, least seed, hypercube form, prefix
  lattice), THIM (selectivity classes), AOT (frustration index), RHTower Liouville additive
  correlation (no successor-sign calculus exists in the corpus).
- 2026-10-24 — modules A–K compiled and audited; README v2; topic 3 settled negatively.
