# Bucket G4 — Multi-q Picard–Vessiot & the Langlands group

**Bucket grade:** organizational (SEARCH channel). Sorted from `docs/support-extraction-log.md`.
**Scope (one line).** The multi-q Picard–Vessiot correspondence that makes `G_L` a theorem-grade
object (charter autonomy / C7), and its endpoint: a candidate construction of the **Langlands group
as a difference-Galois group**.
**Work package this seeds.** Decide the **monoidality obstruction `ω ∈ H²(G_L)`** after the #191/#198
split: `ω_mot` controls the Tannakian/motive/value-lift/DSS axis, while `ω_pol` controls the separate
polarization/RH axis. The autonomy/C7 and realization gatekeeper live on the motivic face; G5 positivity
is not forced by that face alone.

---

## The conjecture

> **G4 — Multi-q Picard–Vessiot correspondence** (autonomy / C7): the multi-q difference system has a
> Picard–Vessiot extension whose Galois group `G_L` satisfies the Galois correspondence; conjecturally
> `G_L` (on the automorphic side) **is the Langlands group**.

---

## What belongs here

### The structural achievement (#68 — LARGELY DONE, modulo classical n=1 lemmas)
- §43.1: the **infinite-base Galois correspondence PROVED** (Tannakian for affine group schemes +
  finite-S import; the one new ingredient = finite-support-invariants-commute-with-limit, Lemma C).
- §47: the "several-operator" import **dissolved** to the classical `n=1` PV method + the co-extension
  identity 47.1 (`σ_i(A_j)A_i = σ_j(A_i)A_j`, ledger-formalized in `FlatConnection.lean`).
- §55: **inverse-Galois problem CLOSED** — `R_multi = {G : π₀(G) finite abelian}`. (#101 7d: finite ⟹
  abelian via the commuting-monodromy lemma; outer twists via induction-with-duality.)
- §16 integrability/curvature `F_{pq}=1` = flatness on the prime lattice; PV existence for
  non-decomposable modules PROVED via filtered limit (`FlatConnection.lean`).
- *Caveat (#68 grading / #101): inverse-Galois §55, λ-subring §56, the main structure theorem (7g,
  Tannakian) lean on classical imports (Etingof, classical IGP, Deligne) and likely **FAIL Door-2** —
  IMPORT-reframed, not NATIVE.* (→ [[door-C5-irreducibility-and-door-2-retest]])
- §67 §18/§19-D1: multi-q Picard–Vessiot named as the central open object; single-factor PV group
  `⊂ 𝔾_m` is the base case.

### The monoidality obstruction (#73 §4 — the one explicit class)
- §4: the de Branges `⊗↦⊕` (foundations §11) vs the cup product `∧` disagree by a 2-cocycle
  `ω ∈ H²(G_L)`. **Corrected by #191/#198:** the class splits into a motivic/value face
  (`ω_mot=0 ⟺ G_L` Tannakian / motive exists / DSS value-lift succeeds) and a polarization face
  (`ω_pol=0 ⟺ Weil/G5 positivity / RH`). This locates G4's autonomy gap in one explicit H² class
  without collapsing RH and DSS into one statement.
- SEED-R (#73 §6 [SPEC]): candidate `ω = the Koszul homology class of the prime lattice in the ∏_p
  limit`; `ω=0 ⟺ the ∞-prime Koszul complex stays acyclic`. Finite Euler shadow = the `e–h` duality
  `Σ_{i+j=k}(−1)^i e_i h_j = 0` (ledger-proven, `EHKoszulDuality.lean`). (→ [[bucket-new-sibling-conjectures]] G15 Koszul-acyclicity)

### The master spectral Langlands group in λ-ring form (#79)
- §4/§8: the moment λ-ring `𝓜 = ℚ[p_m(π)]` = the **free λ-ring on the Adams operations (prime power
  sums)**; conjecturally the **coordinate ring of the field's master spectral Langlands group
  `π₁(𝒮)`** (`G_L`-reps ↔ `𝓜`-comodules). §3: **functoriality = a λ-ring homomorphism** preserving the
  two faces (GRH and DSS are functorial invariants of the whole λ-ring). The field's terminal object.
- Extensively ledger-proven Satake-side half (axiom-clean): `adamsPowerSum_tensor`,
  `adamsPowerSum_isobaricSum`, `adamsPowerSum_comp` (Adams monoid), `chebyshevU_eval_plethysm`,
  `localFactor_coeff_esymm`, `eh_koszul_duality`. (the clean half; → [[bucket-ledger-footholds]])

### The Langlands-group construction (#86 §4, #88 §4)
- #86 §4 **Conjecture 4 (the deep weld, = #68's C2 / G4 autonomy):** the automorphic multi-q category
  is neutral Tannakian; its fundamental group `G_𝒜` is **conjecturally the Langlands group `L_ℚ`**,
  with functoriality = Tannakian morphisms (Sym/∧/induction/base change = native operations). **The
  field PROPOSES a concrete construction of the Langlands group AS a difference-Galois group** — a new
  candidate definition, gradable against known cases. The `⊗`=Rankin–Selberg half is a **THEOREM**
  (§3, exact at unramified places); the group-coincidence is the conjecture.
- #88 §4: over `F_q(C)`, **G4 / Conjecture 4 = DELIGNE–KATZ** (monodromy group; `⊗` = tensor of
  sheaves; Sato–Tate = Katz–Sarnak). The proving ground. (→ [[bucket-function-field-proving-ground]])

---

## Status ledger for this bucket

| Piece | Tier / grade | Source |
|---|---|---|
| infinite-base Galois correspondence | **`[PROVED HERE]`** (mod n=1 lemmas; likely IMPORT under Door-2) | #68 §43.1 |
| inverse-Galois `R_multi={G:π₀ finite abelian}` | **`[PROVED HERE]`** (likely IMPORT) | #68 §55 |
| Satake-side λ-ring algebra (⊗, ⊕, Adams, plethysm, e–h) | **ledger-proven** (axiom-clean) | #79 |
| `ω_mot=0` (Tannakian / motive exists / value realization) | **OPEN core** — wild-kernel freeness / H² face | #73 §4, #198 |
| `ω_pol=0` (polarization / Weil positivity / RH) | **OPEN G5 face** — separate from motive existence | #191/#198 |
| `G_𝒜 = L_ℚ` (Langlands group = difference-Galois group) | **conjecture** (RS-half is a theorem) | #86 §4 |
| over `F_q(C)`: G4 = Deligne–Katz | **THEOREM** | #88 §4 |

## Open core / the work package
**Compute (or bound) the split class `ω=ω_mot⊕ω_pol`.** The motivic face asks whether the wild
exponential kernel `K` is free pro-unipotent / whether the missing F₁ value-lift exists; the polarization
face is G5/Weil positivity. The SEED-R route reads the motivic face as Koszul homology of the prime
lattice in the `∏_p` limit — a homological "fourth language" for the renormalization wall. Test: does
the finite `e–h` acyclicity (ledgered) survive the limit in the wild kernel?

## Cross-references
- [[G5-unitarity-gatekeeper]] — the polarization face `ω_pol` is the G5/RH axis.
- [[bucket-realization-and-fake-family]] — `ω=0`/realization is the converse of the First Theorem.
- [[bucket-new-sibling-conjectures]] — G15 (Koszul-acyclicity) is the SEED-R sharpening of the motivic `ω` face.
- [[bucket-function-field-proving-ground]] — over `F_q(C)`, G4 is Deligne–Katz.
- [[bucket-ledger-footholds]] — the Satake-side λ-ring half is largely in Lean.
