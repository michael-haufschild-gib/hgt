# Library update request — 2026-06-19 — dss-cross-equals-schanuel-prime-logs moved & ground

Informal ticket for the librarian to fold into `door/00-status.md` and `door/00-index.md`.
No edits by me to those files (race-avoidance rule).

## Pipeline move
`dss-cross-equals-schanuel-prime-logs.md`: **`0-backlog → 1-in-progress`** (the regular column of DSS-cross,
sibling to the exponential column `1-in-progress/relative-exponential-apex.md`). Apex unchanged: FIELDS
MEDAL, open, explicitly unfaked.

## What was added (a grinding session; all BRIDGE/EMBASSY — apex untouched)
1. **§A spectral reformulation `[PROVEN, Door-1 native]`.** `∂_s x_p = −(log p) x_p`, so `{log p}` is the
   eigenvalue spectrum of the archimedean generator `∂_s` on the Bohr prime modes. Hence
   **DSS-cross / Schanuel-for-prime-logs ⟺ the `∂_s`-spectrum `{log p}` is algebraically independent.** A2
   reading: prime frequencies, "many clocks, no master clock ⟺ frequencies algebraically independent."
2. **§B native freeness-agnosticism `[PROVEN no-go]`.** `∂_s^k` on composite modes realizes `{log p}` as the
   **free** polynomial generators of `ℚ[log p]` (expressively complete — a naive "degree-1 ceiling" is
   FALSE and was self-corrected), but the only relations the `(mult, ∂_s, σ_p, FE)` structure FORCES are
   ℤ-linear (unique factorization). So algebraic independence = realization faithfulness is **undecided by
   the native data**. Consequences: (i) the regular column is **purely a value-lift, unified with the
   exponential column** (`relative-exponential-apex` §10) and the `#165` GROUP→VALUES residue — group/symmetry
   side maximal, value-lift the sole content, triangulated three ways; (ii) the `σ_p` contribution must be
   **analytic** (lcm/PNT denominators), not algebraic, so a single flat construction is predicted insufficient
   (mirrors `relative-exponential-apex` §8) and the live crux is prime-weighted (multi-`q`) decoupling.
3. **§C two-Frobenii disambiguation `[clarification + FLAG]`.** `f1-inversion`'s lattice-collapse Frobenius
   `(a)` (corank→1, kills DSS) ≠ the value-lift/ABP Frobenius `(b)` (Papanikolas over `F_q`, proves the FF
   analog with high trdeg). The ℚ obstruction is the **absence of `(b)`**; corank ∞ is its enabler, not its
   barrier. **FLAG for the seam bucket:** the FF cards describe the `F_q` Frobenius once as collapse-to-rank-1
   (`corank-seam` §A/§B) and once as the Papanikolas value-engine (`g2-over-fq-papanikolas-dss`) — two
   different modules; recommend making "the missing `F₁`" unambiguously denote `(b)`. (Papanikolas attribution
   marked IMPORT/recalled — to re-verify against `2-fully-proven/g2-over-fq-papanikolas-dss.md`.)
4. **§D EMBASSY — KAM/Diophantine allegory.** Baker's effective linear-forms-in-logs bound = the prime
   frequency vector is Diophantine (no linear resonance); algebraic independence has no dynamical shadow —
   confirms §B and "constraint, not flow." Quarantined.
5. **§E experiment.** Degree-2 PSLQ floor (runpod, mpmath 1.4.1): **no integer relation** in any
   adequately-precise config for `{2,3,5,7}`/`{2,3,5,7,11}` homogeneous and mixed `≤2`; one dps=220 false
   positive checked & rejected (residual `1.5e-13`). Archived
   `computations/2026-06-19-schanuel-primelog-degree2-floor.txt`. Consistent with (not a proof of)
   `corank^{(2)}=∞`.

## Suggested status-row touch (librarian's discretion)
G2 / seam rows: note the regular column is now **in-progress with a method-level unification to the
exponential column** (both = value-lift `(b)` / `#165` GROUP→VALUES; group side maximal). Optionally record
the `(a)/(b)` Frobenius disambiguation as a sharpening of the seam/`F₁` language.

## Unaffected
Banked `corank-seam` §B/§C/§F and `f1-inversion` reductions are **built upon, not altered**. The apex remains
the open FIELDS-MEDAL conjunct.
