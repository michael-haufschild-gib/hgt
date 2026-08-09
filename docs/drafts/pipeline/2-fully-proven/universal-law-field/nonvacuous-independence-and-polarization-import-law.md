# Non-vacuous independence and the polarization import law

- **ID:** ULF-INV-6
- **Stage:** 2-fully-proven
- **Type:** METATHEOREM (paper) / UPGRADE OF ULF-INV-5 THEOREMS B AND D
- **Source:** the vacuity caveat of ULF-INV-5 §3, attacked directly
- **Statement:** The independence of the polarization clause survives the vacuity caveat:
  noncompact finite-area hyperbolic surfaces with small first eigenvalue satisfy the Selberg-world
  analogues of N1–N6 **non-vacuously — including the cusp clause N5 and geometric truncation
  N2 —** while their Selberg-zeta RH fails with explicit off-critical real zeros. Hence even the
  full no-go specification with genuine infinite-dimensional cusped structure does not force the
  conclusion; only polarization does. Calibration upgrade: in every world where the
  RH-analogue is proved, the polarization is *imported* from the function-field world where it is
  native geometry (Castelnuovo/Deligne); the rationals sit at the top of the import chain with no
  upstream world, which derives the exact fork the two major programs occupy.
- **Status:** [PAPER-PROVED AT CITATION LEVEL] [VACUITY CAVEAT CLOSED] [IMPORT STRUCTURE
  OBSERVED, NOT CLAIMED AS THEOREM] [NOT RH] [NO LEAN]

## 1. Theorem B′ — the non-vacuous independence witness

Let \(S=\Gamma\backslash\mathbb H\) be a noncompact finite-area hyperbolic surface obtained by
pinching a separating geodesic of a finite-area surface with cusps (Buser-type construction;
classically, pinching drives \(\lambda_1\to0\), and the construction coexists with cusps —
Buser, *Geometry and Spectra*; Colin de Verdière). Choose the pinching so that
\(0<\lambda_1<\tfrac14\). Then:

1. **N5 non-vacuous:** \(S\) has cusps; the spectral decomposition has continuous (Eisenstein)
   spectrum; the heat/wave traces diverge naively and are rendered finite by the Maass–Selberg /
   truncation mechanism — which is *restriction to a compact core*, a geometrically positive
   operation (multiplication by an indicator), exactly the shape N2 demands and the moment
   category cannot express.
2. **N1, N3, N4, N6 non-vacuous:** the pairing is the Selberg trace formula (geometric, not a
   regularized moment limit of the length spectrum); upper bounds on eigenvalue counts come
   from `count ≤ trace` (Weyl law with the truncated trace); the length spectrum begins at the
   systole of \(S\); the identity/volume term plays the pole role and every spectral estimate
   spends it.
3. **The RH-analogue fails, exactly:** the Selberg zeta \(Z_S\) has zeros at
   \(s=\tfrac12\pm\sqrt{\tfrac14-\lambda}\) for each eigenvalue \(\lambda\); since
   \(\lambda_1<\tfrac14\), there are real zeros in \((0,1)\setminus\{\tfrac12\}\) — off the
   critical line.

Hence the specification N1–N6, satisfied with genuine infinite-dimensional content, a genuine
cusp, and a genuine geometric truncation, is consistent with failure of the conclusion. The
missing clause is precisely the spectral-gap/polarization statement \(\lambda_1\ge\tfrac14\),
which for congruence \(\Gamma\) is **Selberg's eigenvalue conjecture** — open since 1965. The
specification's N7, instantiated in the nearest continuous world, is a named 60-year-old open
problem; ULF-INV-5's vacuity caveat is closed and its Theorem D sharpens: the joint model
{N5, N2, N7} exists *conjecturally* (congruence quotients), with exactly N7 unproved there.

## 2. Theorem D′ — the polarization import structure

Where does N7 ever get proved? Reading the proofs:

| world | RH-analogue proved? | where the polarization comes from |
|---|---|---|
| curves over \(\mathbb F_q\) | yes (Weil) | **native**: Castelnuovo positivity — geometry of \(C\times C\) |
| varieties over \(\mathbb F_q\) | yes (Deligne) | native + amplification: purity via tensor-power monodromy |
| Ramanujan graphs (LPS) | yes, for the constructed families | **imported**: Ramanujan–Petersson via Eichler–Shimura from Deligne — function-field positivity transported to graphs |
| congruence \(\Gamma\backslash\mathbb H\), archimedean place | partial (\(\lambda_1\ge\) Kim–Sarnak bound) | **imported through functoriality**: poles of symmetric-power \(L\)-functions — bounded-degree purchase |
| \(\zeta\) over \(\mathbb Q\) | open | — no upstream world exists |

Observation (recorded as structure, not theorem): polarization has never been proved *in-world*
outside function-field geometry; every other instance is an import along a correspondence whose
source is the function-field world. The rationals are terminal in this import order. Therefore
any adequate theory must do one of exactly two things:

- **Fork (a) — make polarization native over \(\mathbb Q\):** construct the cusped polarized
  geometric-truncation object directly (the Deninger/Connes shape). The corpus's constraints on
  this fork are the axioms: the object's corner is noncompact (N5), its truncation is geometric
  (N2), its normalizers pay the systole floor (N4), its bounds spend the pole (N6), and none of
  it lives in the moment category (N1, N2).
- **Fork (b) — build a new upstream world:** a geometry in which \(\operatorname{Spec}\mathbb Z\)
  becomes a curve-like object with a genuine product \(\ \times\ \) and an intersection theory,
  from which positivity can be imported (the \(\mathbb F_1\)/global-field-analogy shape). The
  corpus constraint here is ULF-INV-1/N1: the import correspondence cannot factor through
  Mertens-normal moment data — it must transport more than asymptotics.

The two forks are precisely the two major live programs in the literature; what the inverse
theory adds is that the fork is *forced* (Theorem B′: nothing weaker suffices) and that each
fork inherits a specific, machine-checked constraint list.

## 3. Hostile scope

- Small-eigenvalue cusped surfaces: classical (Buser; Randol; Colin de Verdière); Selberg zeta
  zero dictionary: standard (Hejhal). Nothing new claimed in the witness itself — its role
  against the axiom list is the contribution.
- The import table is a reading of proofs, cited; the "terminal in the import order"
  observation is exactly that — an observation about existing proofs, not a nonexistence
  theorem about future correspondences. Fork (b) is not excluded by it; it is *specified* by it.
- This card does not advance either fork; it proves the fork is exhaustive relative to the
  specification and equips both sides with the corpus's constraint lists. The program's next
  falsifiable targets remain ULF-INV-4 (general-d barrier) and the fork-(a)/(b) constraint
  instantiations.

## Log

- 2026-08-09 — created: vacuity caveat of ULF-INV-5 closed with the cusped thin-neck witness;
  Selberg's conjecture identified as N7's instance in the continuous world; polarization import
  structure tabulated; the two-fork conclusion derived with per-fork constraint lists.
