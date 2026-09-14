# FZZ-P one-sided common-compact pair kill (2026-09-14)

For `D(p)=deriv (fzzMarkedRadialReplicaResponse u v) p`:
- `D(-p)=-conj(D(p))`.
- `Re D(p)<0` for `p>0`; hence `Re D(p)=0 ↔ p=0`.
- `∃ C:ℂ, D(p)+C=0 ∧ D(-p)+C=0 ↔ p=0`.
- Separate cancelling responses satisfy `C₋=-conj(C₊)` (positive survivor).
- Vacuum anchor `C₀=-D(0)` cancels both iff `p=0`.

Route consequence: kills every nonzero-momentum FZZ-P branch using one source-fixed/conjugate-blind complex compact response. Surviving physical producer must retain orientation, obey conjugate-odd law, and match all-depth normalization/cross-charge weights. With `p=Re ρ-1/2`, selector lands at Mellin-completeness/RH; literal source realization remains open.

Lean modules:
- `FZZCigarOneSidedRadialReflectionLaw`
- `FZZCigarOneSidedRadialReflectionSelector`
- `FZZCigarOneSidedRadialCommonCompactPairNoGo`

Audit: each source checked directly; each exact leaf target built (largest total 8.7s); formal lint passed with build disabled; no `sorry/admit/axiom/opaque/unsafe`; umbrella imports wired. No umbrella/full build. Frontier map remained read-only.
