# KMS / modular temperature — σ = β, the FE = a temperature duality, ∂_s = the modular (thermal) clock

- **ID:** kms-modular-temperature
- **Stage:** 0-backlog
- **Type:** CANDIDATE (EMBASSY → native target; the time/thermal face of the archimedean generator)
- **Priority:** FUTURE
- **Source:** ../../door/bucket-time-and-non-holonomic-time.md (M1 — the missing physics ingredient with a
  rigorous engine); builds on the archimedean generator `∂_s = D` (../../door/bucket-archimedean-generator.md,
  `completed-connection-category.md`); credits the corpus time/holography docs #94 (WDW), #96 §3
  (Hawking temp = Bost–Connes seam temp), #90 (`D` = Connes scaling flow); ../../door/bucket-the-no-margin.md
  (the `{0,1}` pump); 00-status row #27 (`ω`)
- **Statement (to shape).** Bost–Connes (1995) is a **rigorous** quantum-statistical system: a C\*-dynamical
  system whose `KMS_β` partition function is `ζ(β)`, with the primes (via `ℚ^{ab}`'s Galois group) acting
  as symmetries and a phase transition at `β = 1`. Identify its modular structure with the branch:
  `∂_s = D = −Σ_p(log p)θ_p` is the **Tomita–Takesaki modular flow** of the archimedean (type-III)
  algebra = the **emergent thermal time** (Connes–Rovelli). Then:
  > **(σ = inverse temperature)** the real part `σ = Re(s)` is the `KMS` inverse temperature `β`.
  > **(FE = temperature duality)** the functional equation `s ↔ 1−s` is a **duality of temperatures**
  > `β ↔ 1−β`, a Kramers–Wannier-type self-duality with fixed point `β = ½`.
  > **(RH = self-dual KMS criticality, conjecture)** RH = the emergent thermal time is consistent
  > (unitary modular flow / real spectrum) at the **self-dual** state `β = ½` — the critical temperature
  > of the prime-zero system.

  **One sentence:** the emergent time of the branch is the modular flow of a KMS state whose temperature
  is `σ`; the FE is a temperature self-duality; RH asks that the self-dual (`β=½`) state be unitary.

## Goal
This is the **one EMBASSY ingredient of the time bucket with a rigorous mathematical engine** behind it
(Bost–Connes), hence the best candidate to follow the **erosion threshold** from metaphor into native
math. Banking even the *framing* — `σ=β`, FE = temperature duality, `∂_s` = modular flow — gives the
archimedean generator a thermodynamic semantics and a concrete object (a KMS state) to test RH against,
rather than a "vague self-adjoint hope" (the corpus's own warning, #88 §5).

## The honest subtlety (state it, do not paper over)
- **Two special temperatures.** Bost–Connes condenses at `β = 1` (the pole of ζ / the `s=1` residue),
  **not** at `β = ½` (the FE self-dual point). So "`σ=½` = critical temperature" is **not** the
  Bost–Connes phase transition; the two live at different normalizations. The honest object is the
  **modular structure on the special temperatures `{0, ½, 1}`** — the no-margin pump `L_∞(1)·Res_{s=1}ζ =
  (π^{−½}Γ(½))·1 = 1` already pins `β=1` (Tamagawa, [[bucket-the-no-margin]]), and the FE pins the
  `0↔1` and `½`-fixed structure. Reconciling "condensation at 1" with "self-duality at ½" is the first
  real question, not a detail to hide.
- **Type III ⟹ no trace ⟹ the modular flow is the only intrinsic time** (Connes). This is *why* `∂_s`
  is forced (the seam / `ω≠0`), and it ties the card to corank ∞ (the trace defect = the arrow of time,
  the time bucket weld).

## Door passport
- **Door-1:** EMBASSY by default (a physics/thermodynamic framing). Promotion needs a **native object** —
  the KMS state realized inside `𝓜⁺`/`G_L⁺`, not borrowed.
- **Door-5:** over `F_q` there is a global Frobenius = a trace = type II/finite = an **ordinary**
  (non-modular) time; no KMS-emergence is needed — the function-field control showing the structure is a
  number-field-only phenomenon (matches corank 1 vs ∞).
- **Couples to** `completed-connection-category` (`∂_s` = the modular generator) and the time weld
  (emergent time = corank ∞).

## Approach
1. **Pin the dictionary** `σ=β`, `∂_s` = modular flow, FE = `β↔1−β`; state RH = self-dual KMS criticality
   precisely, with the `{0,½,1}` reconciliation (the §subtlety) as step 1's deliverable.
2. **Locate the native KMS object** in `𝓜⁺`: is there a state on the (type-III) archimedean algebra whose
   modular automorphism group is the `∂_s`-flow and whose partition function is the completed `Λ`? (Connes'
   `L²_0`/Sonine cut, #88 §7, is the candidate Hilbert space.)
3. **Door-1 test:** does any step use the joint `σ_p` + `∂_s` irreducibly (native), or is it Bost–Connes
   re-dressed (EMBASSY)? Grade honestly.
4. **`F_q` control** (Door-5): the trace exists ⟹ no modular emergence.

## Gates
- [ ] 0 → 1  in-progress: dictionary pinned; the `{0,½,1}` temperature reconciliation stated; the native
  KMS-object question posed; Door-1 grading criterion fixed
- [ ] 1 → 2  fully-proven / promoted: a native KMS object in `𝓜⁺` exhibited (promote off EMBASSY), or a
  definite verdict that the thermal reading is Bost–Connes re-dressed (stays EMBASSY, recorded)
- [ ] 2 → 3  formalized: only if a native finite floor appears (e.g. the `{0,½,1}` pump relation; reuse
  `MultiplierScaling`, `BoundaryModulus`)
- [ ] 3 → 4  publication-ready

## Notes / risk
- **No RH claim.** This is a framing/target card; the value is converting an EMBASSY metaphor into a
  statement about a specific (Bost–Connes / modular) object. The erosion threshold is the precedent that
  this conversion is possible.
- Heavy import surface (Bost–Connes, Connes–Rovelli thermal time, Tomita–Takesaki). Mark each honestly;
  the native content is only what uses the branch's own `(σ_p, ∂_s)` structure.

## Cross-references
- `../../door/bucket-time-and-non-holonomic-time.md` (M1) — parent; the emergent-time = corank-∞ weld.
- `../../door/bucket-archimedean-generator.md`, `completed-connection-category.md` — `∂_s` = the modular
  generator (dependency). **Coordinate; do not duplicate.**
- `../../door/bucket-the-no-margin.md` — the `{0,1}` pump / Tamagawa, the `β=1` end of the temperature line.
- `hp-not-too-algebraic.md`, `weil-positivity-operator.md` — the operator/positivity faces of the same clock.

## Log
- 2026-06-19 — created in 0-backlog from the WDW/holography sort (bucket-time M1). The one time-bucket
  EMBASSY ingredient with a rigorous engine (Bost–Connes `β=s`): `σ`=inverse temperature, FE = temperature
  duality, `∂_s` = the Tomita–Takesaki modular/thermal clock, RH = self-dual KMS criticality. Honest
  `{0,½,1}` subtlety recorded (condensation at 1 vs FE self-duality at ½). First step = pin the dictionary
  and the temperature reconciliation; locate the native KMS object in `𝓜⁺`.
</content>
