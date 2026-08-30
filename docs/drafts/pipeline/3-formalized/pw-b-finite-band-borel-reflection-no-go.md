# PW-B finite-band Borel reflection no-go

- **ID:** PW-B-FINITE-BAND-REFLECTION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** read-only `rh-current-frontier-map.md`, route PW-B; source coefficient tower in `ThetaCuspHawkingParikhWilczekBorelPartnerEndpoint.lean`
- **Statement:** No finite, spectrally independent linear combination of forward PW first-winding Borel grades equals the functional-equation-reflected grade-zero coefficient throughout the open critical strip.

`[NEW] [CLASSIFICATION] [NO-GO] [PW-B] [PROVED HERE] [LEAN-PROVED]`

## Goal and discharged route burden

Targeted chain:

`PW first-winding Borel tower → source-derived FE partner transport → partner balance on Xi support → Deninger Ward identity → RH`.

The theorem kills the finite-band non-diagonal candidate for the first arrow.  It applies already
to the grade-zero boundary row, so later matrix rows may depend on grade and may mix in either
direction; no positivity, Toeplitz, translation-invariance, or energy hypothesis is used.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3  formalized: closed Lean theorem, targeted build green, axiom audit passed
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Exact theorem

For

`B_k(s) = Γ(s+2k)/(k!)²`

and fixed finite coefficients `a₀,…,a_N ∈ ℂ`, set

`T_a(s) = Σ_{j=0}^N a_j B_j(s)`.

Then

`¬ ∃ N a, ∀ s, 0 < Re(s) < 1 → T_a(s) = B_0(1-s)`.

Lean declaration:

`RHTower.no_schwarzschildParikhWilczekFiniteBandBorelReflection`.

## Paper proof

1. Gamma recurrence gives the positive classification

   `T_a(s) = Γ(s) P_a(s)`,

   where

   `P_a(s)=Σ_j a_j (s)_{2j}/(j!)²`

   is an even ascending-Pochhammer polynomial.
2. The proposed source law at `s` and at `1-s`, with Gamma nonzero in the strip, gives

   `P_a(s)P_a(1-s)=1`.
3. The difference polynomial vanishes on the infinite line `s=1/2+ni`, so the identity holds as
   a polynomial.  Hence `P_a` is a polynomial unit and is constant, say `c`.
4. At `s=1/2`, `c Γ(1/2)=Γ(1/2)` and Gamma is nonzero, so `c=1`.
5. The source law holds on a neighborhood of `1/2`; differentiating gives

   `Γ'(1/2)=-Γ'(1/2)`, hence `Γ'(1/2)=0`.
6. But `Γ'(1/2)=Γ(1/2)ψ(1/2)` and

   `ψ(1/2)=-γ-2 log 2 ≠ 0` (`γ>1/2`, `log 2>0`).  Contradiction.

## No-go closure

- **Exact killing theorem/mechanism:** finite Gamma shifts yield a polynomial multiplier; FE
  involution makes that multiplier a polynomial unit; Gamma's nonzero center derivative kills the
  unit.
- **Strongest positive survivor:** exact finite-row classification
  `T_a(s)=Γ(s)P_a(s)` with an even-Pochhammer polynomial `P_a`, formalized as
  `RHTower.schwarzschildParikhWilczekFiniteBandBorelTransform_eq_eval_mul_Gamma`.
- **New insight:** obstruction lies at the amplitude boundary row, before positivity, evaporation
  aggregation, matrix moments, or holonomy.  Finite grade bandwidth cannot manufacture the
  reflected archimedean Gamma leg.
- **Surviving route:** any exact PW-B FE producer must be infinite-range/non-polynomial
  (fractional or singular), channel-coupled, or explicitly spectral-feedback dependent.
- **Status:** survivor and killing theorem are dependency-closed and Lean-proved.

## Novelty audit (through 2026-08-30)

- **Internal corpus:** required `scripts/formal_tools.py research` searches covered PW-B
  finite-band/non-diagonal mixing, first-winding Borel reflection, Gamma/Pochhammer shift rigidity,
  diagonal calibration, finite polynomial histories, and signed matrix moment classifications.  No
  amplitude-level finite boundary-row exclusion was present.
- **Literature parent mechanisms:** Parikh--Wilczek derive the conservation-corrected nonthermal
  tunneling spectrum, not this Borel/FE source law
  (`https://arxiv.org/abs/hep-th/9907001`).  Vidūnas treats integer contiguous relations and their
  Pochhammer coefficients (`https://arxiv.org/abs/math/0109222`).  Koornwinder treats arbitrary
  parameter-changing transmutations by fractional integrals/generalized Stieltjes transforms
  (`https://arxiv.org/abs/1504.08144`).
- **Classification:** Pochhammer shift algebra is **[LITERATURE]**; its weld to the corpus-derived
  PW Borel tower is **[BRIDGE]**; the exact finite-band PW-B boundary-row no-go and route
  consequence are **[NEW]** relative to audited corpus and located literature.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekFiniteBandBorelReflectionNoGo`
- Source:
  `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekFiniteBandBorelReflectionNoGo.lean`
- Direct check:
  `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekFiniteBandBorelReflectionNoGo.lean` — PASS
- Targeted final build:
  `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekFiniteBandBorelReflectionNoGo` — PASS (`9034/9034`)
- Axiom audit: both new theorems use only `propext`, `Classical.choice`, `Quot.sound`; no added
  axioms, `sorry`, `admit`, `opaque`, or `unsafe` declaration.
- Umbrella: wired into `formal/GaloisForLFunctions/RHTower.lean`; no umbrella build run.
- Global lint: new module is wired and clean; lint remains red only for unrelated pre-existing or
  concurrent unwired modules listed by the tool.

## Log

- 2026-08-30 — conjecture frozen from corpus-derived PW coefficient tower and explicit RH chain.
- 2026-08-30 — paper proof closed; strengthened from translation-invariant mixing to an arbitrary
  finite grade-zero boundary row.
- 2026-08-30 — formalized, targeted-build audited, axiom-audited, and umbrella-wired.
