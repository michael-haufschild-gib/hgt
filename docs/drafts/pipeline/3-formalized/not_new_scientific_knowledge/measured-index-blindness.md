# The faithful–measured index dichotomy: the type-II₁ transverse index is RH-blind

- **ID:** t3-measured-index-blindness
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — a method-limitation no-go
- **Source:** T3 of `../../rh-monodromy-weight-mismatch/123-constraint-reframe-catalog.md`;
  parent `docs/rh/opus_faithful_vs_measured_trace_dichotomy_20260615.md`,
  `opus_transverse_current_c8_test_20260615.md`, `object_x.md` (transverse-current face);
  finite anchor `formal/GaloisForLFunctions/HTGeometry/KreinLangerInertia.lean` (`exact_neg_inertia`).
- **Statement:** The negative index `κ₋` of the FE-forced indefinite Weil/Krein form counts off-line
  zeros. The **faithful** (integer) count is point-resolving and `= 0 ⟺ RH`. The **measured**
  (normalized, type-II₁/III₁, flow-invariant) index is the ratio `Noff/N`, and it is **blind to RH**:
  configurations with `0`, `1`, and infinitely many off-line zeros all have measured index `0`.
  Moreover a scaling-covariant trace (`τ∘θ_s = e^{-s}τ`, type-III₁) that is also flow-invariant is
  forced to vanish. So no measured/flow-invariant trace can express RH; the faithful integer is the
  un-normalizable remainder.

## Goal

T3 named the object "RH ⟺ `κ₋ = τ(P₋) =` type-II₁ index of the scaling flow's transverse current
`= 0`." Rule-7 audit ("constraint not flow, no carrier construction") plus the corpus's
faithful-vs-measured analysis show this object is the **wrong** one: the type-II₁ *measured* index is
free/classical (the normalized zero-density) and structurally RH-blind. This card formalizes *why*,
turning the corpus's paper-level dichotomy into an axiom-clean method-limitation theorem, and locating
T3's residue precisely at the **faithful** referee (which is T2 / the HP-index, not a measured trace).

## The Lean certificate (axiom-clean)

`GaloisForLFunctions/RHTower/MeasuredIndexBlindness.lean`:

- `MeasuredIndexZero Noff N` — the measured index vanishes: `Noff(n)/N(n) → 0`.
- `measuredIndexZero_const` — a bounded (constant) off-line count normalizes to `0` (`c/n → 0`): a
  *fixed* finite set of off-line zeros is invisible to the measured index.
- `measuredIndexZero_dust` — an unbounded **density-zero dust** (`Noff = n`, `N = n²`, ratio `1/n → 0`):
  infinitely many off-line zeros, measured index still `0`.
- `faithful_measured_dichotomy` — the packaged no-go: three configs (`κ₋ = 0`, `1`, `∞`) share
  measured index `0`. The normalized index cannot distinguish RH from its failure, not even from a
  single off-line zero.
- `typeIII_scaling_forces_zero` — the **type-III scaling obstruction**: a functional both
  scaling-covariant (`τ(θ_s P) = e^{-s}τ(P)`) and flow-invariant (`τ(θ_s P) = τ(P)`) satisfies
  `e^{-1}τ(P) = τ(P)`, hence `τ(P) = 0` (since `e^{-1} ≠ 1`). No scaling-covariant trace can be a
  nonzero absolute count — it reads `0` on every configuration.

The **faithful** half is the tree's `exact_neg_inertia` (`κ₋ = #off-line pairs`, point-resolving,
`= 0 ⟺ RH`), already proven; this card is the measured half and the dichotomy.

## Approach

`κ₋` counted two ways. Faithful: the exact negative inertia of the finite conjugate-pair Krein
carrier is the off-line pair count (`exact_neg_inertia`), an integer; one off-line pair forces
`κ₋ ≥ 1`. Measured: the scaling flow's trace is type-III₁ (`τ∘θ_s = e^{-s}τ`), so only ratios are
flow-invariant, and the natural index is `Noff/N` against the total density `N`. Two independent
arguments show this is RH-blind: (i) density — a fixed or density-zero off-line set normalizes to `0`
(`c/n → 0`, `n/n² → 0`); (ii) covariance — a covariant + invariant functional is algebraically forced
to `0`. Both say: the normalization destroys the integer.

## Verdict — dual gate

**DELIVERED (formalized):** the method-limitation is proven and machine-checked, axiom-clean — the
measured/type-II₁/III₁ index cannot express RH, two ways.

**T3's operator-spectral face — KILLED as an independent RH route:**
- The **finite faithful** index `κ₋ = #pairs` is DONE (tree, `exact_neg_inertia`), but it needs the
  zeros — not a non-circular RH route by itself.
- The **measured/type-II₁/III₁** index is **RH-blind** (this card): free, classical (`= `normalized
  zero-density), and structurally incapable of resolving a density-zero off-line set. This is the
  constraint-side reason every trace/measured-positivity method stalls at the same wall.
- The **faithful infinite** index `κ₋(m_ξ) = 0 ⟺ RH` is (a) RH-equivalent and (b) requires
  *constructing the carrier* `m_ξ = -Ξ'/Ξ = Σ_ρ 1/(t_ρ-z)` from the zeros — a **flow in disguise**
  (rule 7), and circular. The abstract infinite Nevanlinna/Krein–Langer infrastructure it would need
  is reduce-to-known and serves only that flow-forbidden apex.

**Where it points (not a terminus):** the residue is the **faithful integer referee** that a measured
trace cannot be — either an integer F₁-Hodge index or a genuine discrete-spectrum Hilbert–Pólya
operator. Both are **T2 (the weld `ω` / complex structure `J`)** and the **HP-index** of doc 123 §4.
T3, taken to exhaustion, hands its open content to T2: the operator-spectral face has no non-flow,
non-RH-equivalent content of its own beyond the finite (done) and the no-go (built).

## Log
- 2026-07-07 — created in 3-formalized: measured-index blindness proven two ways
  (`MeasuredIndexBlindness.lean`, axiom-clean, lint green); T3 operator-spectral route killed as
  independent, residue handed to T2/HP. Finite faithful `κ₋` anchor pre-existing
  (`KreinLangerInertia.exact_neg_inertia`).
