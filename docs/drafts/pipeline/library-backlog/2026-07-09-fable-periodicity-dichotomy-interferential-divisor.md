# Ticket: door index — periodicity dichotomy (C-PD) + interferential divisor

Requested updates to `docs/drafts/door/00-index.md` / `00-status.md` (apply-agent to place):

1. **New native object:** the *interferential divisor* — the part of a factored carrier's strip
   divisor at which no Euler factor vanishes. Exists only in the analytic continuation; no
   approximation by bounded-period clockwork; unreachable by finite column regroupings (natural
   boundaries inherited); ζ's strip divisor is 100% interferential. Lean:
   `formal/GaloisForLFunctions/RHTower/{ColumnarInterferential,ClockEscape,NoCrossColumnHealing,DivisorStabilizer}.lean`.

2. **New headline conjecture [C-PD], SEARCH register:** off the critical line, the divisor of a
   multiplicative FE Dirichlet stream is vertically periodic; equivalently the constraint-only
   (interferential) divisor lies on the involution's fixed line. Novelty [ABSENT] documented.
   Machine-checked: C-PD + verified no-AP literature ⟹ RH and the full 2^k-ladder
   (`DichotomyInstances.lean`). Supersedes the four-way HT-fiber rigidity headline (refuted:
   degree-0 fiber empty by structure theorem; γ-cell by ζ·dzo convolution mobility).

3. **New gatekeeper theorem:** completion parity — FE-completability of a central normal form is
   the reflection fixed-point μ₂-bit; the root-ladder completability bits are the 2-adic digits
   of the central order (`CompletionParity.lean`, `CompletionParityTower.lean`). Welds the
   divisor-rigidity lane to the seam-sign/crease-ledger lane.

Cards: `pipeline/3-formalized/new/{degree-zero-structure-and-mobility, periodicity-dichotomy-architecture, completion-parity-tower, interferential-divisor-theory}.md`; research card `pipeline/1-in-progress/goldilocks-divisor-rigidity.md`.
