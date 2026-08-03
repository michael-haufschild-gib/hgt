# Publication card — countable observer weaving

- **Status:** hostile audit in progress
- **Primary claim:** countable coercivity–defect dichotomy for injective dense-range Hilbert observers
- **Novelty:** `[PROVED HERE; NOVELTY UNVERIFIED]`
- **Paper:** `main.tex`
- **Formal module:** `formal/GaloisForLFunctions/RHTower/PythagoreanObserverBlindness.lean`

## Result

For `T_i : G → H_i`, `i ∈ ℕ`, bounded injective and densely ranged:

- if some `T_i` is coercive, every closed common dense-image subspace is `G`;
- otherwise one closed common normal `D` avoids every `ran(T_i*)`, contains a countably indexed linearly independent family, and every closed `L≤D` yields the common dense-image defect `L⊥`.

The arbitrary-family observer–annihilator equivalence and finite-family specialization are included. The paper also gives the exact two-observer relation criterion, the inverse-adjoint graph classification for Hilbert pre-quasi pairs, and an explicit pre-quasi-not-quasi model.

## Stronger-than-prior-draft delta

- removed Banach theorem claim;
- removed Pythagorean stability assumption;
- removed spectral normalization and endpoint spectral weaving;
- strengthened two observers to countably many;
- replaced one witness/codimension hierarchy with hereditary closed-subspace law;
- added exact coercive rigidity branch;
- formalized entire retained mathematical surface in Lean.

## Claim discipline

`CLAIM_TRACE_AUDIT.md` is authoritative. No mathematical theorem, lemma, corollary, or model assertion may remain without a named unconditional Lean declaration.

Explicit exclusions:

- uncountable families;
- Banach-general theorem;
- PDE trace counterexample;
- independent priority certification;
- Annals/JAMS/Inventiones-level significance claim.

## Required gates

- [x] direct Lean elaboration of modified module
- [x] umbrella import present
- [x] manuscript rewritten to Lean-backed claims only
- [x] updated novelty audit
- [ ] global formal lint green after concurrent umbrella updates settle
- [ ] scratch `#print axioms` audit
- [ ] final targeted `lake build GaloisForLFunctions.RHTower.PythagoreanObserverBlindness`
- [ ] LaTeX build without overfull boxes
- [ ] PDF visual inspection
- [ ] hostile referee report with claim-ledger audit
- [ ] revision after hostile report

## Venue calibration

Potential level: strong general analysis/operator-theory journal; possible *Advances in Mathematics* only if external priority and significance review are positive. Current evidence does not justify flagship general-journal claims.

## Log

- 2026-08-03 — prior Hilbert pre-quasi counterexample and graph classification completed.
- 2026-08-03 — observer–annihilator law isolated.
- 2026-08-03 — direct finite-family weaving replaced stable spectral route.
- 2026-08-03 — countable family theorem formalized unconditionally.
- 2026-08-03 — manuscript and audits rewritten around countable universal law.
