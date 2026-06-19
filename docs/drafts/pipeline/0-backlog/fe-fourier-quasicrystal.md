# FE ⟺ the measure is a Fourier quasicrystal (G8 / crystalline self-duality)

- **ID:** fe-fourier-quasicrystal
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Priority:** FUTURE
- **Source:** ../../door/bucket-new-sibling-conjectures.md (#68 SEED-F) · 00-status row #97
- **Statement:** A difference system admits the **σ-base-symmetry functional equation** ⟺ its
  generalized-integer measure is a **Fourier quasicrystal**. (FE ⟺ theta-modularity ⟺ Poisson/Fourier
  self-duality of the generalized-integer measure ⟺ crystalline measure; Lev–Olevskii / Kurasov–Sarnak /
  Meyer.) This gives the FE an **intrinsic (non-analytic) characterization**.

## Goal
Characterizes the functional equation — currently an analytic input — as a **crystallinity / self-duality
property** of the prime measure, decoupling it from ζ's analytic continuation. Relevant to
`carrier-herglotz-rh.md` / `weil-positivity-operator.md`: the FE is the **polarization** in the G5
faces, and a crystalline characterization is exactly what the polarization needs. A sibling family that
isolates the FE axis the structural gatekeepers don't address.

## Door passport
- **Door-1:** the σ-base-symmetry is the native FE (the simultaneous inversion-and-scale
  `x_p ↦ p^{−1} x_p^{−1}`); a Fourier-quasicrystal characterization keeps it inside the difference world.
- **Door-2:** the test is whether identifying the σ-FE with quasicrystal self-duality needs the joint
  difference structure or reduces to classical Poisson summation (a parent) — likely BRIDGE for the
  single-place case, native for the simultaneous one.

## Gates
- [ ] 0 → 1  in-progress: the σ-base-symmetry FE and the Fourier-quasicrystal self-duality both pinned;
  the equivalence stated; Door passport sketched
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
Identify the σ-base-symmetry with Poisson/Fourier self-duality of the generalized-integer measure;
import the Lev–Olevskii / Kurasov–Sarnak / Meyer crystalline-measure theory. Check it against the Beurling
generalized-prime measures (so the characterization rejects the off-line fakes) — links to
`lee-yang-localization.md`.

## Cross-references
- `lee-yang-localization.md` — the crystalline / real-rootedness sibling (same Kurasov–Sarnak circle).
- `carrier-herglotz-rh.md`, `weil-positivity-operator.md` — FE = polarization in the G5 faces.

## Log
- 2026-06-19 — created in 0-backlog. FE = crystalline self-duality (G8, SEED-F): the FE as a Fourier
  quasicrystal property of the prime measure.
