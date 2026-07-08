# Clock selection for a seam object without a functional equation

- **ID:** seam-clock-selection
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]`, axiom-clean. Constructs the first consumer of the rate-lattice weld interface ([[weld-rate-lattice-interface]]): a concrete non-functional-equation seam object, run through both interface entry points, answering "does a coherent clock exist / is it unique" non-trivially.
- **Scope note:** constraint-side only. The "object" is its constraint *data* — a rate family plus a selecting constraint — never a carrier; no difference-equation solution is constructed (that would be a flow).

## What is proved (`formal/GaloisForLFunctions/RHTower/SeamClockSelection.lean`)

**The selecting constraint and the coherent-clock criterion.** A seam object's clock is pinned by a constraint acting on the clock parameter as an affine map `affineSelect a b s = a·s + b`; its fixed locus is the selected clock. The complete criterion:
- `affineSelect_existsUnique_iff : (∃! s, affineSelect a b s = s) ↔ a ≠ 1` — a coherent (unique) clock exists iff the constraint's linear part is not `1`.
- `affineSelect_no_fixed` — a pure translation `s ↦ s + b`, `b ≠ 0`, fixes nothing.

**The object and the two interface consumers.** `SeamObject ι` bundles a rate family `rate : ι → ℝ` with `LinearIndependent ℤ rate` and the selecting constants `selLin, selConst`. It consumes the interface:
- `SeamObject.weld_nontrivial` — the weld classes are ℤ-independent (via `weldClass_indep_of_linIndep`): every object has a nontrivial weld.
- `SeamObject.clock_covector_free` — the clock covector is free and unique-given-values (via `clock_covector_existsUnique`).
- `SeamObject.clock_coherent_iff` — a single selected clock locus exists iff `selLin ≠ 1`.

**Three concrete objects on one rate lattice.** All three carry the *same* prime-rate lattice `⟨log p⟩` — so the same nontrivial weld and the same free clock covector — differing only in the constraint:
- `feObject` (`selLin = −1`): the functional-equation reflection. `feObject_is_sigma` — its constraint *is* the tree's `sigma` (`s ↦ 1 − s`); `feObject_clock_at_half` — clock at `1/2`.
- `mahlerObject q` (`selLin = q ≠ 1`): a Mahler scaling, no functional equation. `mahlerObject_clock_at_zero` — clock exists, but at `0`.
- `shiftObject h` (`selLin = 1`): the native difference/prime-shift constraint. `shiftObject_no_clock` — **no clock**; `shiftObject_weld_nontrivial` — yet the weld is intact.

## The structural content
Weld and clock are independent. The weld is generic to the rate lattice — present for every independent rate family. The coherent clock is the constraint's alone, and exists iff the constraint's linear part is not `1`. The functional equation is the special *reflection* case (`a = −1`) that localizes the clock at `1/2`; a Mahler scaling localizes it elsewhere (`0`); the native shift localizes none. So for a seam object without a functional equation the question "does a coherent clock exist" is genuinely open until the constraint's linear part is named — nothing hands you `1/2`. The proofs are elementary; the content is the separation of weld from clock and the location of the functional equation's exact role.

## Constraint, not flow
Everything is constraint data (a rate family, an affine constant) and cohomological/lattice invariants. No carrier, no solution of the difference equation, no propagation.

## Lean
`RHTower.{affineSelect, affineSelect_fixed_iff, affineSelect_existsUnique, affineSelect_no_fixed, affineSelect_existsUnique_iff, SeamObject, SeamObject.weld_nontrivial, SeamObject.clock_covector_free, SeamObject.clock_selected, SeamObject.clock_coherent_iff, feObject, mahlerObject, shiftObject, feObject_is_sigma, feObject_clock_at_half, mahlerObject_clock_at_zero, shiftObject_no_clock, shiftObject_weld_nontrivial}` in `formal/GaloisForLFunctions/RHTower/SeamClockSelection.lean`, imported in the `RHTower` umbrella. `lake build` green, axiom-clean, lint pass.

## Open continuations
- **A genuinely non-arithmetic rate family**: all three objects reuse `⟨log p⟩` to isolate the constraint's role. A rate family not derived from the primes needs its own ℤ-independence proof (a transcendence input) — that is the real frontier for a fully non-arithmetic seam object.
- **The amplitude layer**: why `1/2` (not merely "a fixed point") is distinguished for the reflection is the self-duality of the prime phases (`norm_cpow_eq_critical_iff`); pairing that with `clock_coherent_iff` would say when a *selected* clock is also an amplitude-democratic locus.

## Log
- 2026-07-08 — created in 3-formalized. First consumer of the rate-lattice weld interface: FE / Mahler / shift seam objects on the prime-rate lattice, the weld intact for all, the coherent clock existing iff the constraint's linear part ≠ 1 (`clock_coherent_iff`), the native shift object clock-less. Axiom-clean.

## Completion: a genuinely non-arithmetic object (`TranscendentalRateObject.lean`)

The prime-lattice objects above share ζ's arithmetic; the first open continuation is now closed with a rate family that is not `log ∘ prime`. Rate family `{θ^n}` for `θ` the concrete Liouville number `∑ 2^{-k!}`:
- `transc_pow_indepZ` — **powers of a transcendental are ℤ-linearly independent**: `aeval θ` is injective (`transcendental_iff_injective`), carrying the monomial basis of `ℤ[X]` to an independent family. This is the transcendence-sourced independence input, replacing unique factorization; a reusable non-arithmetic bridge.
- `liouvilleConst`, `liouvilleConst_transcendental` (from `transcendental_liouvilleNumber`), `liouvilleConst_ne_one` (from irrationality).
- `liouvilleRateObject : SeamObject ℕ` — rates `{θ^n}`, selecting constraint the object's own frequency self-similarity `λ_{n+1} = θ·λ_n` (`liouvilleRate_recurrence`), implemented on the clock parameter as the **Mahler scaling `s ↦ θ·s`** — not a functional equation.
- `liouvilleObject_weld_nontrivial` — infinite-rank weld, sourced from transcendence not factorization.
- `liouvilleObject_clock_covector_free` — the clock covector is free.
- `liouvilleObject_has_clock` + `liouvilleObject_clock_at_zero` — the constraint has linear part `θ ≠ 1`, so it **selects a clock, at `0`** (the scaling's fixed point), with no functional equation anywhere: the answer to "does a coherent clock exist" is read off the object's self-similarity, not handed down by a reflection. (`0` is also the democratic-amplitude locus `Re s = 0` of `{e^{−θ^n s}}`, the analogue of ζ's `1/2`.)

Caveat: this is constraint data (rate family + self-similarity), not a proof that a specific analytic realization `∑ a_n e^{−θ^n s}` is hypertranscendental — the construction stays constraint-side, no carrier.
