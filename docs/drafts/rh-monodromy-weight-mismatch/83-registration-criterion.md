# 83 — The Registration Criterion: the New Object, Built and Formalized

**Register: LEDGER for §2 (Lean, proven through); SEARCH for §§3–4.**
(The /goal object: the design gate minted by the Route C-direct refutation
(doc 82 §5), made into a formal instrument.)

## 1. The object

A carrier can anchor a creation-counting spine only if its own shallow
pair-zeros force detectable line values — if it REGISTERS its creation.
Behind both directions sits one exact law. For the FE∧real pair
factorization Φ(z) = (z − ρ)(z − ρ′)·H(z), ρ = ½+η+iγ, ρ′ = ½−η+iγ:

> **The pair-dip law:** ‖Φ(½+it)‖ ≥ η²·‖H(½+it)‖ for ALL t, with
> EQUALITY η²·‖H(foot)‖ at t = γ.

Registration is therefore EXACTLY an envelope question: upper envelope
bounds register (the foot dips to η²M); lower envelope bounds obstruct
(nothing in the window dips below η²M). No analysis beyond the
factorization — the law is carrier-agnostic and two-sided.

## 2. The Lean object [banked: Registration.lean, axiom-clean, lint green]

- `pair_dip_lower` / `pair_dip_foot` — the law, both sides (exact norm
  computation: ‖½+it − ρ‖ = √(η² + (t−γ)²)).
- `RegistersAt Φ γ w lam` — a sub-`lam` line value within the `w`-window.
- `RegistrationComplete Φ P h w lam` — every band pair (family `P`,
  offsets 0 < η ≤ h) registers.
- `registersAt_of_envelope_le`, `registrationComplete_of_peeled_envelope`
  — the POSITIVE clause: foot envelope ≤ M ⟹ registration at h²·M.
- `not_registersAt_of_envelope_lower`,
  `not_registrationComplete_of_gap_pair` — **the registration gap as a
  theorem**: ONE band pair over an envelope ≥ M on its window refutes
  completeness below η²·M. This is doc 82 §1's located unsound link,
  machine-checked in its general form.

Consumers: a registered pair is a selected dip — `RegistersAt` feeds the
parity counter (`ParityCounting.selected_sliver_budget`) and the dip
counters (`MollifiedDip`); the criterion is the missing interface between
"carrier has a pair" and "counter sees an event".

## 3. The carrier table [the criterion applied across the lane]

The operative form: a carrier registers its sliver band at threshold λ iff
its envelope scale M satisfies h²·M ≤ λ; via the dip-lemma route the same
sorting is by the local L² normalization κ² (doc 56 §3):

| carrier | normalization | verdict |
|---|---|---|
| mollified P = F_N·M_y | κ² = 1 + V = O(1) (doc 56 §3, Graham-grade) | **REGISTERS** (dip radius ∝ c; the doc 67 chain was sound for THIS carrier) |
| sharp g_N (doc 22) | κ² ~ 2 log N (un-mollified) | **FAILS** (doc 82: c ≤ e^{−A/2} forced; Route C-direct dead) |
| exponential-AFE Φ* (doc 32 §6 / 76 §5) | κ² ~ log T (E\|Z\|² classical) | **two-horn dichotomy, §4** |

## 4. The exp-AFE horn [CONJECTURE-grade, the next test]

By value-normalization, Φ* sits in the sharp class: typical envelopes are
√log T-grade and band pairs at η ≫ e^{−ωt} would NOT register — horn (a):
exp-AFE fails like g_N. BUT the family's defining property (displacement
e^{−ωt}; doc 76 §5 measured 1e−50 at t ≈ 221) suggests horn (b): its
ACTUAL pair population may be confined at η ~ e^{−ωt}, where registration
is vacuously easy (η²M ≤ any threshold). The criterion thus RE-TYPES the
exp-AFE question: not "does it register its band" but "is its pair
population confined below the band" — a zero-confinement census, not a
value-distribution estimate. Test: the doc 76 §5 instance machinery on
Φ*'s own off-line pairs across a height sweep (does any pair sit at
η ∈ (e^{−ωt}-scale, h]?). If confinement holds and is certifiable, the
exp-AFE family inherits Route C's collapse benefits with the gap closed
by vacuity — the one live heir, now with a precise entrance exam.

## 5. Ledger

Registration.lean: 6 endpoints, axiom-clean [propext, Classical.choice,
Quot.sound], lint green, module build 8575 jobs; umbrella import appended
(umbrella itself pending the parallel session's SpurLattice/SpurCPI clash
fix). The criterion object is BUILT and FORMALIZED; its remaining life is
consumption: the exp-AFE confinement census (§4) and the Route B
re-assembly with ParityCounting + RegistrationComplete as explicit
interfaces.
