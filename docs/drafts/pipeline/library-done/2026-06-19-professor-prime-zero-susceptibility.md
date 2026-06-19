# Library backlog — door/00-index + door/00-status update (Professor, 2026-06-19)

**New 2-fully-proven card:** `docs/drafts/pipeline/2-fully-proven/prime-zero-susceptibility-transverse.md`
(Door grade **BRIDGE**).

## For door/00-status.md (new proven row)
- **Title:** Prime→zero susceptibility χ is transverse; FE-balance characterization of the line.
- **Grade:** BRIDGE (RH-axis reformulation + structural placement; does NOT prove RH).
- **Content (3 proved items):**
  1. Single-coefficient linear response: `dρ/dε = −n^{−ρ}/ζ'(ρ)` for a simple zero
     (`ζ_ε=ζ+ε n^{−s}`); susceptibility `χ_n(ρ)=n^{−Re ρ}/|ζ'(ρ)|`. Numerically pre-certified to
     rel err ≤4e−25 (`computations/2026-06-19-prime-zero-susceptibility.py`).
  2. **Equivalent characterization of RH:** mirror-pair ratio `χ_n(ρ)/χ_n(1−ρ)=n^{1−2β}/|χ_{FE}(ρ)|` is
     frequency-`n`-independent ⟺ `β=½`; so "every FE-mirror pair susceptibility-balanced ⟺ RH". Off-line
     imbalance exponent `2a`, `a=|½−β|` = the curvature-window half-width of `phase-cancellation-crux §3`.
  3. **Placement (headline):** χ's mode content is the pure frequency `n^{−(½+it)}` = all-orders transverse,
     so χ is NOT an affine `e^{a+bz}` mode → NOT demoted by `phase-cancellation-crux`'s affine-confinement. The
     prime→zero susceptibility equals the curvature hierarchy `P^{(k)}=Σ_ρ(½+it−ρ)^{−k}` order by order
     (`χ` of the murmuration card = `P^{(k)}` of the phase-cancellation card).

## For door/00-index.md
- Link the new card under the RH/positivity (A1) axis, cross-referenced to `phase-cancellation-crux`
  (the curvature hierarchy) and to the backlog moonshot `moonshot-zeros-as-critical-murmuration` (parent;
  the variational/optimality residue stays MOONSHOT).
- Net readout effect: +1 paper-proven BRIDGE card on the RH axis. (No Lean yet; 2→3 target noted in the card.)

Proven-count bookkeeping is the librarian's call; flagging the +1 paper BRIDGE card.
