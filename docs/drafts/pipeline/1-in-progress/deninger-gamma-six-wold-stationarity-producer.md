# Deninger Gamma-six Wold-stationarity producer

- **ID:** deninger-gamma-six-wold-stationarity-producer
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `rh-current-frontier-map.md` Frankenstein seam: completed-exponent exceptional transport × Gamma-six projective edge × prime-depth Wold source clock
- **Statement:** Source functoriality forces the unique coefficient-faithful carrier between forward and reflected Gamma-six shell powers to be stationary under one Wold clock step.

## Goal
Prove, without RH or a hidden spectral premise, that for every Xi divisor `rho` and shell coordinate `n`,
`d_rho(W n) = d_rho(n)`, where `d_rho(n) = lambda_n^(2*(2*Re(rho)-1))` is the unique carrier transporting both retained orientations. Existing unconditional Lean theorem then forces every Xi divisor onto the critical line and proves RH.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `<producer>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
Heavy-conjecture loop:

1. **C0 — constant exceptional scalar transports all grades. FALSIFIED.** Exact classification: possible only at horizontal grade zero.
2. **C1 — allow grade-dependent carrier. PROVED.** Coefficient faithfulness uniquely forces `d_delta(n) = lambda_n^(2*delta)`.
3. **C2 — use covariance alone to make `d_delta` stationary. FALSIFIED.** Reflection involution exchanges grades and gives reciprocal drift; it does not identify a grade with its Wold successor.
4. **C3 — coupled source naturality makes the square commute. FALSIFIED.** Exact Beck--Chevalley law gives boundary defect `exp(a)-1`. Lean now proves source Wold stationarity, exceptional isometry, and fixed-character cyclic descent are the same pointwise obstruction. They are three presentations of one equation, not independent inputs.
5. **C4 — target-side anomaly absorption. OPEN.** Lift the complete shell-amplified class through the fixed resolved target square so the nonzero source Beck--Chevalley defect becomes an actual target boundary annihilated by the fixed reader. This must preserve the trace-class remainder, prime labels, divisor multiplicity, and both marked orientations; it cannot declare source reader cyclic.

Target square for C4:
`exceptional direction --reflection--> reflected exceptional direction`
with vertical maps induced by the literal Gamma-six Wold source coordinate and the already-fixed target differential. Source square alone has holonomy `exp(a)-1`; required strict lift must send that anomaly to a target boundary while retaining the physical coefficient.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** Covariance alone supplies an involution but no Wold stationarity. Unique carrier has nontrivial factor `(1/6)^(2*delta)` off line, while source boundary readout has exact defect `exp(a)-1`.
- **Strongest positive survivor:** `RiemannHypothesis` iff unique shell-reflection multiplier is Wold-stationary globally. Pointwise TFAE theorem identifies literal blow-up isometry, full shell transport, and cyclic physical descent exactly.
- **New insight:** Several frontier obstructions are shadows of one universal defect: reflected orientations are equivalent only by a cocycle whose multiplicative-clock holonomy is `(1/6)^(2*delta)`. Source involution gives covariance, and source boundary gives the same holonomy in exponential coordinates. Any real producer must absorb this anomaly after strict target transport; source-side flatness simply restates RH.
- **Status:** C0--C3 paper-closed and Lean-formalized in `DeningerExponentGammaSixShellTransportRigidity.lean`. Lean also proves both reflection transports are explicit coboundaries and identifies mixed curvature with `exp(-2a)`, where `a` is the existing physical cyclic-character parameter. C4 is sole open core and matches Route L's strict global ideal-preserving lift. Internal and external novelty audits found no pre-existing target lift supplying absorption.

## Log
- 2026-08-11 — frontier cross-audit isolated exceptional transport × Gamma-six shell seam.
- 2026-08-11 — C0 failed; exact unique diagonal carrier and Wold drift proved.
- 2026-08-11 — C2 failed; covariance distinguished from stationarity.
- 2026-08-11 — C3 failed against exact Beck--Chevalley defect; three-presentation TFAE formalized.
- 2026-08-11 — C4 opened: strict target-side anomaly absorption/global ideal-preserving lift.
- 2026-08-11 — Gauge attack: both reflection cocycles trivialized; mixed reflection--Wold curvature isolated as sole invariant and formally identified with physical Beck--Chevalley coordinate.
