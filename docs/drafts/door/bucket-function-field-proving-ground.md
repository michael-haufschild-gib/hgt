# Bucket X4 — Function-field proving ground (Door-5)

**Bucket grade:** organizational (SEARCH channel). Sorted from `docs/support-extraction-log.md`. These
are mostly **IMPORT** (Grothendieck/Deligne/Deligne–Katz, reframed) — but they are the charter's
**Door-5 faithful-restriction proving ground**: over `F_q(C)` *all* gatekeepers are THEOREMS.
**Scope (one line).** Over a function field `F_q(C)` the archimedean place is **absent**, the seam
vanishes, and G1–G5 are theorems — the validation that the architecture is buildable, and the model the
ℚ-case must mirror.
**Work package this seeds.** Prove the gatekeepers G1–G5 **first over `F_q(t)`** (where Weil II is
available); then the number-field obstruction = exactly the one missing archimedean place = the F₁
cohomology-with-Frobenius.

---

## All gatekeepers are theorems over F_q(C) (#88 — the headline)
- **§2 keystone `spec(H_L)=Spec(L)` = GROTHENDIECK** (cohomological L-function; `H_L = Frob_q` on
  `H^1_c`, finite-dim, eigenvalues = the zeros).
- **§3 RH = DELIGNE (Weil II); Ramanujan = PURITY.**
- **§4 G4 / Conjecture 4 (Langlands group = Tannakian `π_1`) = DELIGNE–KATZ** (monodromy group; `⊗` =
  tensor of sheaves; Sato–Tate = Katz–Sarnak equidistribution).
- **G2 over `F_q(t)` = PAPANIKOLAS 2008** (full `trdeg=dim G_M`, the field's exact mechanism) — see
  [[G2-multi-q-siegel-shidlovsky]].
- *Four planetary conjectures = four theorems — the architecture is SOUND. This is where G1–G5 should
  be proved FIRST (charter Door-5).* Ledger (axiom-clean): `functionField_esymm_FE` /
  `functionField_localFactor_FE` (the Weil FE of the L-polynomial, `e_k(S)=q^k e_k(S^{−1})`).

## What the function field LACKS = exactly the ℚ-frontier (#88 §5, #90 §5)
- #88 §5: the single missing brick over ℚ is an **arithmetic cohomology with a Frobenius at the
  archimedean place (= F₁)**. Over `F_q(C)` it is present (Frobenius); over ℚ it is the one absence.
  (→ [[bucket-the-seam-archimedean-obstruction]])
- #90 §5: over `F_q(C)` there is **no archimedean place ⟹ no derivation `D` ⟹ `ω=0` ⟹ RH=Weil/Deligne**
  (type II/finite, all Fredholm). **The wall = exactly the one archimedean derivation `D` (type III, no
  trace).** *The number field = function field + one operator `D`; RH = closing `D`'s trace defect via
  F₁-regularization.* The cleanest statement of the F₁ gap as a single operator.
- #78 §13, §15: function-field RH = "the finite Frobenius is unitary," provable from Poincaré duality +
  hard Lefschetz (Hodge–Riemann); number-field RH = "the infinite secular CMV operator is unitary," the
  **single missing ingredient = the self-dual pairing `Q_W`** (the archimedean-completed cup product).
  *Localizes [[G5-unitarity-gatekeeper]]'s gap to exactly "the duality pairing," present over `F_q`,
  sought over ℚ.* The Hodge–Riemann / Weil-rep picture (#78 §19–22) matches function-field hard
  Lefschetz generator-for-generator.

## The dynamics realization — CM/non-CM (#86 §5+§8, runpod-certified)
- CM/non-CM = the rotation / almost-Mathieu cocycle = the DMR solvable/non-solvable dichotomy.
  **CM curve:** supersingular density ½, δ-atom at θ=π/2 (rotation SO(2), `L=0`, abelian hull).
  **Non-CM:** Sato–Tate `(2/π)sin²θ`, SL₂-dense, irreducible. *The abstract Galois↔dynamics dichotomy
  is the oldest arithmetic dichotomy (complex multiplication) — a concrete proving ground.*
  Ledger: `SatakeInterval`, `SatakeSymPower` (`symPowerGL2_eq_chebyshevS`), `SatoTateMoment`
  (μ_ST moments + `U_k` orthonormality — the analytic core at the measure level; prime-average =
  imported BLGHT).

## The faithful-restriction proving ground for ALL gatekeepers (#67 SEED-C)
- Function field has **no archimedean place** ⟹ its RH = Ramanujan = Deligne (proved by geometry). The
  charter Door-5 proving ground: **G5 and G1–G4 should be proved first over `F_q(t)`** where the
  archimedean wing is absent and Weil II is available. Then the number-field obstruction = exactly the
  archimedean wing = the missing Frobenius / F₁.

---

## The bracket — the two solved corners vs the two open apexes (#93 §5)
- Two **SOLVED** corners (full structure): function-field zeros (Weil/Deligne, Frobenius) and edge
  values `s=1` (Baker, Kummer/Tate motive). Diagonally opposite two **OPEN** apexes (missing one
  structure): RH (ζ/L zeros, missing F₁-Frobenius) and central value `ζ(½)` (missing the motive). *The
  field's two theorems are the two full-structure corners; its two hardest problems are the two
  missing-structure corners.* (→ [[G2-multi-q-siegel-shidlovsky]] for the edge corner)

## Status
- Everything here is **IMPORT** under Door-2 (a parent — algebraic geometry — proves it). Its value is
  **Door-5 validation**: it shows the field's architecture *recovers known mathematics on the overlap*
  (charter C6) and pinpoints the ℚ-obstruction as the single archimedean place. It is the calibration,
  not the native content.

## Open core / the work package
**Prove G1–G5 over `F_q(t)` in the field's own vocabulary** (not merely cite Deligne) — a Door-5
exercise that would establish C6 (the faithful bridge) concretely and isolate, by difference, exactly
what the archimedean place must supply over ℚ.

## Cross-references
- [[bucket-the-seam-archimedean-obstruction]] — the ℚ-obstruction = exactly what `F_q` lacks.
- [[G5-unitarity-gatekeeper]] — over `F_q`, G5 = "Frobenius is unitary" (Deligne); the missing pairing
  `Q_W` is what ℚ needs.
- [[G2-multi-q-siegel-shidlovsky]] — over `F_q(t)`, G2 = Papanikolas; edge `s=1` over ℚ = Baker.
- [[G4-multi-q-picard-vessiot-and-langlands-group]] — over `F_q`, G4 = Deligne–Katz.
- [[door-C5-irreducibility-and-door-2-retest]] — Door-5 is the faithful-restriction test.
