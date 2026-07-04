# 66 — Ideation Card: the Quantum-Walk Collision (Kicked Rotor, Metaplectic π/8, Inverse Grover)

**Register: SEARCH — ideation (user-injected wild-analogy collision, 2026-07-04).
Everything labelled; two anchors are already PROVED lane objects.**

## 1. Honest negatives first
The value walk Z_n is NOT a quantum walk technically: the update is affine and
non-unitary, no coin/Szegedy structure. In the log-clock it is DIFFUSIVE (√θ),
not ballistic. The metaphor must land on the phase structure, not the process.

## 2. The dictionary, anchored
| QW object | Lane object | Status |
|---|---|---|
| kicked rotor, unitary orbit sums | cascade phase lattice e^{−i(4πpm+πm²)} = w^m | PROVED (doc 50 §1) |
| quantum resonances at rational rotation number | coherence blowup at p = ¼, ¾; survivor support {d(p) ≤ 0.194} at resonances, N-stable | PROVED denominator + MEASURED support (docs 50, 47 §5) |
| dynamical localization | Abel master bound a₀/|cos 2πp| | PROVED (doc 50 §3) |
| DFT self-duality / Gaussian fixed point | AFE with χ-kernel; matched length N = √(t/2π) = the self-dual point | KNOWN structure |
| finite reciprocity (Landsberg–Schaar) | Siegel's RS derivation; doc 50's collapse as degenerate instance | bridge to mine |
| Grover diffusion (reflect about mean) | m-dial: iterated Cesàro projection toward the mean; OU deviation damped ×~3/level | MEASURED (docs 62–64) |
| coherent interference beating √ | Harper better-than-√ cancellation | KNOWN — "the quantumness is the enemy's name" |

## 3. The hit worth a check: π/8 as the metaplectic phase of the 2-cover
Doc 50 P-L5 measured the birth stationary value πn₀ − 2πd² + π/8 and left π/8
as numerology. [CONJECTURE]: π/8 = ½·(π/4) — half the Fresnel/Maslov constant
— because the carrier is a SQUARE-ROOT-weight object (theta multiplier system:
8th roots of unity; the lane's whole architecture is the ℤ₂-Kummer tower).
The birth phase would be the metaplectic cocycle of the tower's 2-cover — the
seam constant derived structurally, not asymptotically.
CHECK (analytic, cheap, no compute): re-run P-L5's stationary phase keeping
the Fresnel phase symbolic; confirm the halving arises from the d²-completion
/ even-odd pairing. If confirmed: (T1) birth layer gets a structural
derivation; open follow-up = read the whole cascade's phase bookkeeping as a
metaplectic cocycle (constants as reciprocity phases, not estimates).

## 4. The wild end [labelled wild]
BBBV/hybrid-adversary lower bounds limit amplitude concentration at marked
points under unitary families using ONLY unitarity. An adversary-style proof
of (SEL-PS)-class anti-concentration (measure of t with |S| small) would be a
moment-free mechanism — no instance known in this setting; kept as a moonshot
card, not a plan.

## 5. Next moves opened
1. The π/8 symbolic check (§3) — one sitting, feeds (T1).
2. KR resonance-width asymptotics as first-principles derivation of the
   0.194/0.236 window constants (import candidate; verify against census).
3. Landsberg–Schaar upgrade of the cascade's blockwise bounds to exact finite
   reciprocity identities (doc 50 §8(4)'s Gabcke transplant, now with the
   right classical home named).

## 6. §3 verdict — π/8 check DONE: structural but reduces-to-known [PROVED arithmetic + novelty gate, 2026-07-04]

The §3 test executed (analytic, no compute). The halving is REAL and structural:

> **π/8 = 2π·(1/16) = the classical Riemann–Siegel remainder constant.**
> Rewriting P-L5's `Ψ(p) = cos(2π(p²−p−1/16))/cos 2πp = cos(2π(p²−p) − π/8)/cos 2πp`,
> the additive constant inside the cosine is exactly `−π/8`. And
> `π/8 = ½·(π/4)`, `e^{iπ/8} = √(e^{iπ/4})` = square root of the Fresnel/theta
> saddle factor = argument of a **16th root of unity** = the square root of the
> theta multiplier's **8th-root Weil index**. The ℤ₂-Kummer 2-cover (the
> square-root carrier) realizes precisely that square root. (All four identities
> machine-checked.)

So doc 50 P-L5's "π/8 numerology" is de-numerologized: the birth phase IS the RS
remainder constant, and its value is fixed by the 2-cover carrying the square root
of the theta multiplier. Conjecture §3 CONFIRMED at the constant level.

**But it FAILS the novelty gate.** This identifies a lane constant with Riemann's own
150-year-old remainder constant, read through textbook metaplectic/Weil-index
language. A competent search (RS formula + theta multiplier + 2-cover) reproduces it.
It is a re-description, not a bridge. The (T1) "structural derivation of the birth
layer" is genuine as a *consolidation* (kills the numerology), but it is not new
knowledge — do not re-file it as a moonshot. The follow-up "whole cascade as
reciprocity phases" (§5.3 here / doc 50 §8(4)) currently IMPORTS Gabcke's C₁,C₂,…
hierarchy — importing the classical hierarchy reduces-to-known by construction.

## 7. Where the object is actually non-classical — the survival window [next move]

The metaplectic reading explains the BIRTH phase (classical). It does NOT touch the
lane's genuinely non-classical constants: the survivor support `{2πd² ≤ 0.236 rad}`,
`d(p) ≤ 0.194` (docs 50 §6, 47 §5). Probe: `0.236/(π/8) = 0.601` — NOT a clean
multiple of the structural constant; the window is not forced by π/8. (The
birth-amplitude PEAK is at `d = ¼`, `2πd² = π/8`; the survival CUTOFF is elsewhere.)

Generative redirect: the survival window is the lane-native object worth deriving,
and importing KR resonance-width asymptotics (§4.2) would reduce it to physics. The
non-reducing move is to derive `0.236` as the fixed point of [birth amplitude
`B(p) = |cos(π/8 − 2πd²)|` vs drift-induced dephasing `dp_eff/dm ≈ m/N`, doc 50 §4] —
the survival floor of doc 51, closed WITHOUT import. If that derivation lands, the
metaplectic π/8 becomes a genuine *input* (the birth phase) to a novel window
constant, instead of a decorative re-labeling of a classical one. That is the bridge
candidate; the π/8 itself is not.
