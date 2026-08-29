# PW finite-endpoint Gamma-recurrence kill

- **ID:** PW-FE-GAMMA-KILL
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `rh-current-frontier-map.md` · PW-B literal finite-energy first-winding Borel response
- **Statement:** At every finite physical endpoint, truncated first-winding Mellin moments obey the Gamma recurrence with a strictly positive endpoint boundary defect; hence the half-line `Gamma(s+2k)/(k!)^2` recurrence used by PW-B is not the literal finite-energy source recurrence.

## Goal
Kill PW-B chain at its source weld:

`literal finite-energy Parikh--Wilczek first-winding response`
`→ half-line Gamma Borel recurrence`
`→ fixed-grade FE-partner balance`
`→ Deninger reflect-gauge Ward cancellation`
`→ RH`.

Exact target at real Mellin grade `s = 1`: with
`I_m(X) = ∫_0^X x^m exp(-x) dx` and `X > 0`, prove

`I_{m+1}(X) = (m+1) I_m(X) - X^(m+1) exp(-X)`

and consequently, for `B_k(X) = I_{2k}(X)/(k!)^2`,

`B_{k+1}(X) = R_k(1) B_k(X)
  - exp(-X) (X^(2k+2) + (2k+2)X^(2k+1))/((k+1)!)^2`,

with strictly positive defect. Therefore the corpus half-line recurrence fails at every finite physical endpoint, already at `k=0`.

Non-circularity: statement concerns elementary finite endpoint moments for every `X>0`; it has no zeta-zero or RH premise.

## Gates
- [x] 0 → 1  in-progress: exact source seam, attack by FTC/integration by parts, route passport above
- [ ] 1 → 2  fully-proven: falsified by hostile asymptotic audit
- [ ] 2 → 3  formalized: Lean theorem, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
Build finite-endpoint Gamma-moment infrastructure directly with `intervalIntegral`. Prove one-step recurrence by differentiating `x^(m+1) exp(-x)`, iterate once, normalize by factorial squares, and prove boundary defect strictly positive for `X>0`. Compare with `schwarzschildParikhWilczekFirstWindingBorelCoefficient_succ` at `(s,k)=(1,0)`.

Hostile alternatives to audit: whether Borel coefficient is intentionally an asymptotic half-line object rather than literal finite-energy response; whether a finite-endpoint boundary-corrected successor still has the same fixed-grade FE partner law. Route is killed only if current architecture explicitly requires literal finite-energy source faithfulness.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** The proposed route kill fails. The finite-cutoff correction is proportional to `exp(-1/(2 epsilon))` times a polynomial in `1/epsilon`; extended at `epsilon = 0`, it is flat to every perturbative order. Therefore it does not change the formal Borel coefficients `Gamma(s+2k)/(k!)^2`.
- **Strongest positive survivor:** `NO POSITIVE SALVAGE FOUND`. The incomplete-Gamma recurrence is classical and distinguishes exact finite-`epsilon` response from its perturbative Borel sector, but does not lower the PW-B RH burden.
- **New insight:** Any valid PW-B kill must attack the Borel/FE-partner producer itself or prove that the exact nonperturbative completion creates off-wall balance; finite cutoff alone is insufficient.
- **Status:** Falsified before Lean. Corpus definitions plus Parikh's energy-conservation analysis show that the cutoff is physically required, but asymptotic flatness preserves every formal jet.

## Log
- 2026-08-29 — Created in 1-in-progress from corpus mismatch between physical endpoint `x=1/(2 epsilon)` and half-line Gamma recurrence.
- 2026-08-29 — Falsified: endpoint correction is beyond all perturbative orders and does not invalidate Borel coefficients.
