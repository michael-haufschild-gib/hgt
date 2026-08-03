# Publication card — countable observer weaving

- **Status:** publication package complete; independent priority gate open
- **Primary claim:** arbitrary-family coverage–rigidity law plus countable coercivity–defect dichotomy
- **Novelty:** `[PROVED HERE; NOVELTY UNVERIFIED]`
- **Paper:** `main.tex`
- **Formal module:** `formal/GaloisForLFunctions/RHTower/PythagoreanObserverBlindness.lean`

## Result

For `T_i : G → H_i`, `i ∈ ℕ`, bounded injective and densely ranged:

- if some `T_i` is coercive, every closed common dense-image subspace is `G`;
- otherwise one closed common normal `D` avoids every `ran(T_i*)`, contains a countably indexed linearly independent family, and every closed `L≤D` yields the common dense-image defect `L⊥`.

For every arbitrary nonempty dense-range family, common dense-image rigidity is
equivalent exactly to pointwise coverage by the adjoint ranges.  The
observer–annihilator equivalence and finite-family specialization are
included. The paper also gives the exact two-observer relation criterion, the
inverse-adjoint graph classification for Hilbert pre-quasi pairs, and an
explicit pre-quasi-not-quasi model.

## Stronger-than-prior-draft delta

- removed Banach theorem claim;
- removed Pythagorean stability assumption;
- removed spectral normalization and endpoint spectral weaving;
- strengthened two observers to countably many;
- replaced one witness/codimension hierarchy with hereditary closed-subspace law;
- added exact coercive rigidity branch;
- added exact arbitrary-family coverage–rigidity law;
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
- [x] global formal lint green
- [x] scratch `#print axioms` audit: only `propext`, `Classical.choice`, `Quot.sound`
- [x] final targeted `lake build GaloisForLFunctions.RHTower.PythagoreanObserverBlindness`
- [x] LaTeX build without overfull boxes
- [x] PDF visual inspection
- [x] hostile referee report with claim-ledger audit
- [x] revision after hostile report

## Venue calibration

Hostile internal verdict: passes renowned broad-journal bar in the
*Mathematika* / *Mathematische Zeitschrift* / *Proceedings of the AMS* band,
conditional on independent priority confirmation. Possible *Advances in
Mathematics* submission remains high-risk. Current evidence does not justify
flagship general-journal claims.

## Log

- 2026-08-03 — prior Hilbert pre-quasi counterexample and graph classification completed.
- 2026-08-03 — observer–annihilator law isolated.
- 2026-08-03 — direct finite-family weaving replaced stable spectral route.
- 2026-08-03 — countable family theorem formalized unconditionally.
- 2026-08-03 — manuscript and audits rewritten around countable universal law.
- 2026-08-03 — arbitrary-family coverage–rigidity law formalized and added.
- 2026-08-03 — Baire noncoverage explicitly separated from new common closed avoidance theorem.
- 2026-08-03 — hostile review passed broad renowned-journal tier; external priority remains open.
