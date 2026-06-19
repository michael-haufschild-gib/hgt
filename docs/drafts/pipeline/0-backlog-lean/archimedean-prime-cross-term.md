# The archimedean×prime cross-term — the FE-conspiracy cocycle is purely archimedean (BRIDGE); C5 relocates to G5-positivity

- **ID:** archimedean-prime-cross-term
- **Stage:** 0-backlog-lean
- **Type:** THEOREM (paper), **BRIDGE** (Door-2) — an object built, computed, and graded; the native-C5 hope for *this* object is settled negative
- **Priority:** FOUNDATIONAL (was FIELDS MEDAL as a C5 hope; the deliverable is the object + its grade)
- **Source:** the Hölder-recentering — C5 keystone = the weld (charter §5; `door-C5` "Second carrier dimension");
  SEED-G §64.3 (FE = base-swap `0↔∞`); §4 FlatConnection (FE=flatness); §3 σ-parity=FE-parity weld (row #49);
  `ω∈H²` (#27, "ω purely archimedean"); seam thesis #69/#71/#74 (#1142 "Γ-weight = the entire archimedean content")
- **Numerics:** `computations/2026-06-19-fe-conspiracy-cocycle.py(.out)` — all four claims below certified to ≥30 digits.

---

## Result (what is proven here)

On the completed module `M_Λ = M_∞ ⊗ M_ζ` (diagonal section `Λ(s)=Γ_ℝ(s)ζ(s)`, `Γ_ℝ(s)=π^{-s/2}Γ(s/2)`),
the **FE-conspiracy cocycle** — the obstruction to factoring the functional-equation involution
`ι : s ↦ 1−s` as a tensor product `ι_∞ ⊗ ι_ζ` of factor-automorphisms — is **well-defined, computable, and
concentrated entirely in the archimedean factor**. Explicitly:

> **The entire FE-asymmetry is the archimedean defect `χ(s) = Γ_ℝ(1−s)/Γ_ℝ(s)`; the prime lane
> contributes nothing to it.**

Hence the archimedean×prime cross-term, like the prime×prime carriers, comes back **BRIDGE** — and the
honest payload is *where this sends C5* (below).

### The cocycle, precisely
- `G = ℤ/2 = ⟨ι⟩`, `ι:s↦1−s`, acting on (germs of) meromorphic functions by `(ι·f)(s)=f(1−s)`.
- The two factors are individually **not** ι-symmetric. Their FE-defects (1-cochains):
  - archimedean: `ρ_∞(s) = Γ_ℝ(1−s)/Γ_ℝ(s) =: χ(s)`,
  - prime:       `ρ_ζ(s) = ζ(1−s)/ζ(s)`.
- The FE `Λ(s)=Λ(1−s)` is exactly the **cocycle product relation** `ρ_∞(s)·ρ_ζ(s) = 1`, i.e. `ρ_ζ = χ^{-1}`.
  *(Certified: `ρ_∞·ρ_ζ = 1.0` to 30 digits.)*
- `[∂_s, σ_p] = 0` on the base (`σ_p` scales `x_p` by the constant `p^{-1}`; `θ_p` is scale-invariant), so the
  weld is **not** an operator commutator — it lives in the completion (the tensor + the FE), exactly as the
  card anticipated.

### The computation — the obstruction is purely archimedean
1. **`χ` is purely archimedean.** In the completed (Arakelov) normalization,
   `χ(s) = π^{s−1/2}·Γ((1−s)/2)/Γ(s/2)` — built from `Γ` and `π` alone, **no integer prime** (the stray `2^s`
   of the bare FE factor is absorbed by `Γ_ℝ`'s duplication). *(Certified to 30 digits.)*
2. **`ι_ζ` exists structurally (the prime side is "free").** On `M_ζ`, `ι` acts by `x_p ↦ p^{-1}/x_p` =
   (inversion `x_p↦1/x_p`, i.e. `θ_p↦−θ_p` — the **§3 FE=`w↦1/w` parity**, row #49, Lean-proven) ∘ (the `σ_p`
   shift). This is a genuine `M_ζ`-internal symmetry: isometric, zero-blind, the free multiplicative wing
   (#1142). So the prime factor carries `ι` with **zero FE-defect of its own**.
3. **`ι_∞` does NOT exist as a module automorphism.** Realizing `ι` inside `M_∞` would need `χ` to be a
   `∂_s`-horizontal gauge. It is not: `∂_s log χ = logπ − ½ψ((1−s)/2) − ½ψ(s/2) ≠ 0`. *(Certified ≠ 0 at all
   test points.)* So the archimedean factor is genuinely **not** ι-stable; the FE-asymmetry is irreducibly
   carried by the transcendental `χ`.

**Conclusion:** the obstruction to `ι = ι_∞⊗ι_ζ` is `[χ]`, concentrated 100% in `M_∞`. The prime lane is
inverted+shifted with no defect. The cross-term cocycle uses the archimedean lane irreducibly but the prime
lane **only trivially**.

---

## Door-2 verdict — **BRIDGE** (not C5)

Strip the multi-`q` vocabulary: the cocycle's *value* is the identity `ζ(s)/ζ(1−s) = χ(s)` with `χ`
archimedean — i.e. **the functional equation** (Riemann 1859), which a parent (classical analytic number
theory, a Door-2 parent) proves with no multi-`q` apparatus. The obstruction `[χ]` is **Source A alone**
(Γ/π — the differential-Galois / Hölder border, charter §2). Because the prime lane contributes nothing to
the FE-defect, the cocycle does **not** use the two sources *jointly and irreducibly*. **⟹ BRIDGE.**

This is the negative the card flagged ("if the cocycle factors after all… that negative is itself
informative"). It factors **asymmetrically**: `ι_ζ` exists (BRIDGE, §3), `ι_∞` does not, and the gap is the
classical-FE archimedean factor `χ`.

### Why this is the right (and useful) verdict — the strategic payload
The FE is a **conspiracy** (a forced equality between an archimedean transcendental and a prime
inversion-defect) and it is **classical**. Refining the vision §3 ("RH = non-conspiracy of the two
sources"):
- the **FE-conspiracy** (the *forced* coupling) = classical, BRIDGE — captured by this cocycle;
- **RH** = the *absence of any further conspiracy* (the zeros do not additionally align off-line) = the
  **free, native frontier** = G5 positivity / unitary holonomy of the completed connection.

So **C5 is not in the FE/factorization structure**; it is in the **positivity/holonomy** of the completed
`(σ,∂)`-connection (G5). This complements DeWitt's prime×prime result (the large-values sup-bound is parent):
together, *both* cross-term cocycles are BRIDGE, and C5 is pinned specifically to **G5-positivity**, not to any
FE-symmetry structure. Also a clean independent re-derivation of the seam thesis (#71/#74, "the entire
archimedean content is one Γ-term"; #27, "ω is purely archimedean") — here at the elementary cocycle level.

### Bearing on row #49 (σ-parity=FE-parity weld, flagged "candidate NATIVE, re-test Door-2")
This analysis Door-2-tests its prime-lane content: `ι_ζ`'s inversion `θ_p↦−θ_p` is the **free/zero-blind**
multiplicative involution (BRIDGE); any native surplus would need the archimedean coupling, which is `χ`
(Source-A-alone, BRIDGE). So #49 reads as **BRIDGE** under the cross-term lens. *(Flagged for the librarian /
team — not unilaterally re-graded here.)*

---

## D-axis recast (2026-06-19, charter §6) — this is the substrate's D4 object; grade `BRIDGE (substrate)`
The card's original payload ("C5 relocates to G5-positivity") was on the **C-axis/localization** axis and is
**superseded**: the user's reframe + charter §6 place the keystone elsewhere. On the **D-axis** this cocycle is
the **D4 object** — *the obstruction to the FE-constraint factoring* (charter §6 D4: "a class visible in every
parent, computable by none"). The verdict splits into two layers:
- **Layer 1 — PROVEN here (the non-trivial obstruction).** The FE-factoring obstruction is `[χ] ≠ 1`,
  purely archimedean: `ι_ζ` exists (prime inversion, §3) but `ι_∞` does **not** (`χ` non-`∂_s`-horizontal), so
  `ι = s↦1−s` does **not** factor as `ι_∞⊗ι_ζ`. **The weld does not factor trivially — there is a genuine
  archimedean obstruction.** This is D4-positive *at the symmetry level*: the constraint (the FE) is genuinely
  obstructed, visible in every parent (χ = the classical FE-factor, every border sees it).
- **Layer 2 — OPEN (the decider).** Whether the *deeper* monoidality class `ω∈H²(G_L)` vanishes (`ω=0 ⟺`
  Tannakian/motive/realization, #27, **purely archimedean**) is "computable by none" — the open D4 decider
  (substrate-with-content ⟺ `ω≠0`). My layer-1 result shows the obstruction is non-trivial and archimedean;
  the realization layer (`ω=0⟺RH/realization`) is the open core.
**Grade: `BRIDGE (substrate)`** — C-axis BRIDGE (the value is the classical FE), D-axis substrate-load-bearing
(it constructs the D4 obstruction and proves Layer 1). The cocycle is *not* a failed C5; it is the substrate's
keystone-dual object, half-resolved.

---

## Weil-form shadow & `F_q` degeneration (Door-5)
- **Weil shadow.** The explicit formula `Σ_zeros = (prime term) + (archimedean Γ term)`. The cocycle `[χ]` is
  the algebraic/Galois source of the **archimedean term**; its non-triviality = there *is* an archimedean
  term = the seam. RH (`H_W = −Δ_prime + V_arch ⪰ 0`, #38) is the **positivity** of the coupling — not the
  existence of the cocycle. Consistent: cross-term builds the coupling; G5 asks if it is positive.
- **`F_q` (Door-5).** Over `F_q(C)` there is **no archimedean place** ⟹ no `M_∞` ⟹ `χ ≡ 1` ⟹ the cocycle is
  **trivial** and the FE is the bare L-polynomial symmetry (Weil). No conspiracy, no weld — matching
  `corank(Λ_ff)=1`, holonomic (#121). The cross-term is a **number-field-only** phenomenon.

---

## Gates
- [x] 0 → 1  in-progress: `[∂_s,σ_p]=0` confirmed; interaction located in the tensor + FE; FE-conspiracy
  cocycle defined; links to `ω`/`H_W`/§3/§64.3 stated; Door passport.
- [x] 1 → 2  fully-proven: cross-block/cocycle computed (`[χ]`, purely archimedean, prime lane null); Door-2
  grade decided (**BRIDGE**); Weil-form shadow checked; `F_q` degeneration confirmed; numerics archived.
- [ ] 2 → 3  formalized (optional, low priority — BRIDGE): Lean fragment — `ρ_∞·ρ_ζ=1` as FE-restatement and
  `χ` purely-archimedean; reuse the §3 `exteriorPower_map_neg_id` / `FunctionalEquationParity` anchors for the
  prime-side inversion. Likely not worth a Lean push given the BRIDGE grade.
- [ ] 3 → 4  publication-ready: folds into "the archimedean–prime weld" exposition as the *negative* that
  relocates C5 to G5-positivity.

## Cross-references
- `gamma-module-construction.md` (`M_∞`), `completed-connection-category.md` (`M_Λ`, FE=flatness) — the
  construction cards; this card uses their concrete analytic incarnations (`Γ_ℝ`, `Λ`). Module-category
  formalization of the cocycle is deferred to them — **coordinate, do not duplicate**.
- `weil-positivity-operator.md` (#38), `compute-omega-h2-gl.md` (#27, ω purely archimedean) — the
  positivity/obstruction shadows; **C5 now points here (G5-positivity), per this card's payload.**
- `../../door/door-C5-irreducibility-and-door-2-retest.md` — record: archimedean×prime cross-term = BRIDGE;
  with the prime×prime carriers also BRIDGE, C5 ⟺ G5-positivity.
- `../5-failed/c5-near-resonance-large-values.md` (DeWitt, prime×prime sup-bound = parent) — the complementary
  half of "both cross-terms BRIDGE."

## Log
- 2026-06-19 — created in 0-backlog as the C5 weld entry. **Worked to 2-fully-proven (Professor):** the
  FE-conspiracy cocycle is well-defined, equals the archimedean defect `[χ]` (purely `Γ,π`), and the prime
  lane contributes nothing to the FE-defect (its ι-action is the free §3 inversion ∘ `σ_p` shift, no defect);
  `χ` is non-`∂_s`-horizontal so `ι_∞` is not a module automorphism. Door-2 = **BRIDGE** (value = classical
  FE; obstruction Source-A-alone). **Payload:** C5 is not in the FE/factorization (the forced conspiracy is
  classical); it is in **G5-positivity** (the free non-conspiracy = unitary holonomy). Both cross-term
  cocycles (prime×prime via DeWitt, archimedean×prime here) are BRIDGE. Numerics: all 4 claims ≥30 digits
  (`computations/2026-06-19-fe-conspiracy-cocycle.*`). Bears on row #49 (reads BRIDGE under this lens; flagged
  to librarian, not re-graded here).
</content>

## Lean return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven`: the card's theorem is a completed FE-cocycle/germ/module statement involving `Λ`, `Γ_ℝ`, the FE involution, horizontal gauges, and the claim that the prime lane contributes no FE-defect. The project has no Lean model of that cocycle or its analytic non-horizontal proof; the computation/numeric checks and parity anchors are not a whole-ticket formal proof.
