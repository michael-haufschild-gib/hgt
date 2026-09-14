# One-sided FZZ common-compact pair classification

- **ID:** fzz-one-sided-common-compact-pair
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · FZZ-P
- **Statement:** One common complex compact response cancels reflected one-sided receivers at `±p` iff `p=0`.

## Goal

Kill conjugate-blind/source-fixed compact cancellation away from critical momentum in FZZ-P chain.

## Gates

- [x] 0 → 1: source-pure receiver and exact reflected-pair question
- [x] 1 → 2: reflection/sign/classification proof dependency-closed
- [x] 2 → 3: Lean modules below; direct checks and targeted leaf builds pass
- [ ] 3 → 4: publication novelty review and exposition

## Result

For `D(p)=deriv (fzzMarkedRadialReplicaResponse u v) p`:

- `D(-p)=-conj(D(p))`;
- `Re D(p)=0 ↔ p=0`;
- `∃ C, D(p)+C=0 ∧ D(-p)+C=0 ↔ p=0`;
- the vacuum anchor `C₀=-D(0)` gives the same iff classification.

Lean capstone: `fzzOneSidedRadialNonzeroCommonCompactPairRouteKilled` in
`FZZCigarOneSidedRadialCommonCompactPairNoGo.lean`.
Formal lint passed with build disabled; source scan contains no forbidden declaration.

## RH consequence

With FZZ radial momentum `p=Re ρ-1/2`, universal source-fixed pair cancellation forces every
parity-Mellin source mode onto `Re ρ=1/2`; corpus Mellin completeness then gives RH. Remaining
producer burden is literal all-depth compact response, not selector logic.

## Novelty audit

Corpus deep/lexical searches found no prior exact reflection or common-complex-response
classification. Literature searches through August 2026 found no matching theorem; Halder–Jafferis
supplies the one-sided prescription, not this pair classification.
