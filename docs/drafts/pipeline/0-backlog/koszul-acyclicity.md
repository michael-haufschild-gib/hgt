# Koszul-acyclicity ⟺ Tannakian / RH (G15) — the homological reading of ω

- **ID:** koszul-acyclicity
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Priority:** FUTURE
- **Source:** ../../door/bucket-new-sibling-conjectures.md (#73 SEED-R, #79 SEED-T), ../../door/G4-multi-q-picard-vessiot-and-langlands-group.md · 00-status row #99
- **Statement:** Read the monoidality obstruction `ω ∈ H²(G_L)` as the **Koszul homology of the prime
  lattice in the `∏_p` limit**: **RH / Tannakian ⟺ no Koszul homology condenses in the renormalized
  `∏_{p≤P} → ∏_p` limit.** The finite shadow is the `e–h` duality `Σ_{i+j=k} (−1)^i e_i h_j = 0`
  (**ledger-proven**, `EHKoszulDuality`). SEED-T: the operations λ-ring and the cohomology grading are
  the **same Koszul complex** of the prime lattice.

## Goal
A homological **"fourth language"** for the renormalization wall (alongside ξ-outer condensation,
LP-survival, and the explicit-formula limit), and the **testable** sharpening of `compute-omega-h2-gl.md`:
`ω` has a finite, machine-checked acyclicity shadow, so the open question is concrete — does that
acyclicity **survive the limit**?

## Door passport
- **Door-3:** Koszul homology of the prime lattice is intrinsic to the simultaneity of the `σ_p` (the
  complex is built from the joint difference operators); not a renamed classical invariant.
- **Door-2:** the finite `e–h` acyclicity is ledgered (a parent-grade identity); the **limit** condensation
  is where the infinite base becomes load-bearing — the native-candidate content.

## Gates
- [ ] 0 → 1  in-progress: the prime-lattice Koszul complex pinned; `ω` identified as its `H²`; the finite
  `e–h` floor (`eh_koszul_duality`) stated as the testable shadow
- [ ] 1 → 2  fully-proven: the limit acyclicity decided (`ω=0`?) — couples to `compute-omega-h2-gl.md`
- [ ] 2 → 3  formalized — the finite `e–h` duality is already ledgered; the limit statement is the target
- [ ] 3 → 4  publication-ready

## Approach
Set up the Koszul complex of the prime lattice `ℤ^{(P)}` acting via the `σ_p`; identify its degree-2
homology with `ω`. Test whether the finite acyclicity `Σ_{i+j=k}(−1)^i e_i h_j = 0` (proved at every
finite truncation) survives `∏_{p≤P} → ∏_p` or condenses a class in the limit.

## Cross-references
- `compute-omega-h2-gl.md` — `ω ∈ H²(G_L)`, which this card computes homologically.
- `../../door/bucket-ledger-footholds.md` — `EHKoszulDuality` / `eh_koszul_duality`, the finite floor.

## Log
- 2026-06-19 — created in 0-backlog. Koszul-acyclicity (G15, SEED-R/SEED-T): the homological reading of
  `ω`; #5 on the bucket's promotion shortlist.
