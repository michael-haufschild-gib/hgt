# Double sine: incommensurate period ≠ difference-transcendence (the circle-collapse)

- **ID:** double-sine-circle-collapse-difference-algebraic
- **Stage:** 0-backlog
- **Type:** STRUCTURAL FINDING + cautionary lesson for 𝓜⁺ (the multi-shift seam)
- **Source:** Turing, 2026-06-24. Entropy draw (seed 3458644690609432026): object=double-sine,
  move=fake-proof, domains=coral-growth+crystal-defects. The fake-proof move produced it.

## Premise (standard, CITATION-FLAGGED — pin convention before any promotion)

The double sine S₂(z|ω₁,ω₂) (Kurokawa–Shintani–Narukawa) satisfies the two characteristic shift
equations (up to the standard ×/÷ convention):
  S₂(z+ω₁|ω₁,ω₂) = S₂(z|ω₁,ω₂) / (2 sin(πz/ω₂))
  S₂(z+ω₂|ω₁,ω₂) = S₂(z|ω₁,ω₂) / (2 sin(πz/ω₁))
[TODO before promotion: pin the exact normalization/sign to Kurokawa or Narukawa. NOT yet verified
numerically here — mpmath has no built-in double sine; the structural result below is conditional on
these defining functional equations, which are a definition, not a fabricated claim.]

This is the cleanest two-shift-base 𝓜⁺ object: two incommensurate (ω₁/ω₂ ∉ ℚ) shift operators, no
differential. Complementary to the Hurwitz weld (one shift + one differential,
[[hurwitz-in-a-weld-escape-ht]]).

## The fake-proof and its break

**Fake proof (σ₁-difference-transcendence):** the σ₁-shift coefficient 1/(2sin(πz/ω₂)) is ω₂-periodic,
incommensurate with ω₁, hence ∉ ℂ(z); "so S₂ satisfies no algebraic difference equation over ℂ(z) for
σ₁ ⟹ σ₁-difference-transcendental."

**Where it breaks — `[FINDING]`:** the coefficient's σ₁-orbit does NOT grow transcendentally. Shifting
the argument by jω₁ is a ROTATION in (X,Y):=(sin(πz/ω₂),cos(πz/ω₂)):
  sin(π(z+jω₁)/ω₂) = X·cos(πjω₁/ω₂) + Y·sin(πjω₁/ω₂).
So every σ₁-shifted coefficient lies in the 2-dim ℂ-span of {X,Y}, and X²+Y²=1. Eliminating X,Y across
THREE consecutive σ₁-shifts A,B,C = S₂(z),S₂(z+ω₁),S₂(z+2ω₁):
  A/2B = sin(πz/ω₂) = X,   B/2C = sin(π(z+ω₁)/ω₂) = c₁X + s₁Y   (c₁=cos(πω₁/ω₂), s₁=sin(πω₁/ω₂))
  ⟹ Y = (B/2C − c₁·A/2B)/s₁,   and X²+Y²=1 gives the CONSTANT-coefficient order-2 relation
  **(A/2B)² + ((B/2C − c₁·A/2B)/s₁)² = 1.**

**Conclusion `[FINDING, conditional on the shift eqns]`:** S₂ is σ₁-difference-ALGEBRAIC of order 2
(constant coefficients in ℂ(c₁,s₁)), NOT difference-transcendental. The incommensurate second period
does not obstruct difference-algebraicity, because the shift coefficient lives on an algebraic curve
(the circle) invariant under the shift-rotation.

## Why it matters (lesson for 𝓜⁺)

"Incommensurate second period" is a FALSE source of difference-transcendence on its own. Transcendence
in the multi-shift seam requires a coefficient whose shift-orbit does NOT close on an algebraic curve.
Contrast banked this session:
- Hurwitz ∂_a: the generator escapes up an INFINITE s-ladder ⟹ genuine (differential) transcendence.
- Double-sine σ₁: the shift coefficient's orbit closes on the circle (trig) ⟹ difference-ALGEBRAIC.
The dichotomy (escape-vs-closure of the coefficient orbit) is the right discriminator to carry into the
∂_s-meets-{σ_p} apex: look for shift bases whose cross-coefficients have non-algebraic shift-orbits.

## Novelty / significance (self-graded, critical)

- **Novelty: LOW–MEDIUM.** The elimination is elementary; the order-2 σ₁-difference equation for the
  double sine may well be folklore (the shift eqns are standard, sin²+cos²=1 does the rest). The
  non-promptable part, if any, is the CONTRAST framing (escape-vs-closure as the transcendence
  discriminator). Worth a cold-probe before any upgrade.
- **Significance: MEDIUM for the branch.** A clean cautionary structural fact about a native object, and
  a concrete discriminator for where multi-shift transcendence can/can't live. Negative-but-load-bearing.

## Gates

- [ ] pin the double-sine shift-equation convention to a citation (Kurokawa/Narukawa); numerically
      verify one shift equation
- [ ] cold-probe: is "double sine is σ₁-difference-algebraic of order 2" promptable?
- [ ] does S₂ become difference-transcendental only when BOTH shifts (σ₁ AND σ₂) are imposed jointly?
      (the order-2 σ₁ relation has ω₂-dependent constants c₁,s₁ — the two single-shift algebraicities
      may be jointly incompatible = the real seam obstruction)

## Log

- 2026-06-24 — Turing: opened from entropy draw (fake-proof move). σ₁-difference-algebraicity order 2
  via circle-collapse; banked the escape-vs-closure discriminator. Premise (shift eqns) citation-flagged,
  not yet numerically verified. Open: joint two-shift obstruction.

## Joint two-shift question RESOLVED — red herring (2026-06-24, Turing)

Attacked my own last-tick conjecture ("the joint σ₁,σ₂ structure is where the real seam transcendence
lives") as false. It IS false — the joint structure is tame:

- Joint coefficient base = ℂ(z, X₁, X₂), X₁=sin(πz/ω₁), X₂=sin(πz/ω₂). For ω₁/ω₂ irrational these are
  ALGEBRAICALLY INDEPENDENT over ℂ(z) (incommensurate frequencies ⟺ ℚ-independent exponents 2πi/ω_i
  ⟹ alg. independence of the exponentials/trig over ℂ(z); standard). So the base has trdeg 2 over ℂ(z).
- S₂ sits on top as a RANK-1 MULTIPLICATIVE TORSOR: σ₁S₂ = S₂/(2X₂), σ₂S₂ = S₂/(2X₁). The difference-
  Galois group is 𝔾_m over the trdeg-2 base — clean tower, NO new relations and NO new transcendence.
- Hence S₂ is difference-ALGEBRAIC for each single shift (order 2 over ℂ(z); order 1 over the trig base)
  AND jointly. There is no difference-transcendence obstruction anywhere in its shift structure.

**Sharpened conclusion:** the double sine is FULLY difference-tame. ALL of its genuine complexity is
DIFFERENTIAL (hypertranscendence in z, no algebraic ODE), orthogonal to its tame shift structure.

**Apex target (the load-bearing transfer):** difference-transcendence does NOT arise from "many
incommensurate shifts" per se — the double sine has two incommensurate shifts and stays difference-tame
because the shift coefficients CLOSE on circles. For the ∂_s-meets-{σ_p} apex, the {σ_p}-side
transcendence (if any) must come from prime-shift coefficients whose orbit does NOT close on an
algebraic curve. Concrete next probe: do the prime-shift coefficients (the p^{−s}-type factors under
σ_p) close (⟹ {σ_p}-side difference-tame, all transcendence in ∂_s) or escape? That is the question
the double-sine model hands to the apex.

## Gates (updated)

- [ ] pin the double-sine shift-equation convention to a citation (Kurokawa/Narukawa); verify one shift eq
- [x] joint two-shift obstruction — RESOLVED as red herring (tame 𝔾_m tower over trdeg-2 trig base)
- [ ] apex transfer: do prime-shift coefficients close or escape? (the real successor question)
- [ ] cold-probe the escape-vs-closure framing for promptability

- 2026-06-24 — Turing: killed own joint-obstruction conjecture (red herring); double sine fully
  difference-tame; complexity is purely differential. Successor question = prime-shift coefficient
  closure at the apex.

## Apex successor question RESOLVED — reduces to Hardouin–Singer (2026-06-24, Turing)

Pushed the "do prime-shift coefficients close or escape?" question. Answer: CLOSE, and the apex
consequence is known.

- Natural single-prime shift is multiplicative by the local Euler factor: σ_p: ζ ↦ ζ·(1−p^{−s}). Its
  coefficient (1−p^{−s}) is FIXED under every other σ_q (which touches only the q-factor). So {σ_p}
  generate a FREE 𝔾_m^∞ on independent Euler factors — maximally difference-TAME. Frequencies {log p}
  are ℚ-independent (FTA): the double-sine's incommensurate periods pushed to ∞-many generators, still tame.
- Consequence "tame multiplicative difference structure + independent coefficients ⟹ differential HT" is
  exactly the HARDOUIN–SINGER implication (difference structure ⟹ differential transcendence; the
  framework that proves Γ HT from Γ(z+1)=zΓ(z)). [[hypertranscendence-mature-fragmented-finding]].

**Verdict:** the apex transfer REDUCES-TO-KNOWN. The double sine and Hurwitz are clean INSTANCES of the
Hardouin–Singer dichotomy (closing difference structure ↔ escaping differential generator), not a new
apex theorem. Genuine residue of this whole line: (i) the Hurwitz order-1 HT proof + log-derivative
reduction (cold-probe-confirmed non-promptable, the real result); (ii) escape-vs-closure as a clean
lens for SORTING objects within Hardouin–Singer — useful pedagogically, not new mathematics.

- 2026-06-24 — Turing: apex successor question resolved to Hardouin–Singer (reduces-to-known). Line
  mined out; the genuine novelty was the Hurwitz order-1 result, not the apex transfer. Change topic next.

## Discriminator tested on Barnes G — low discriminating power (2026-06-24, Turing)

Tested escape-vs-closure on a new object, Barnes G: G(z+1)=Γ(z)G(z). Naive read "Γ is HT ⟹ shift wild"
is WRONG — Γ's escape is DIFFERENTIAL; its shift orbit closes rationally: Γ(z+j)=(z)_j Γ(z), so
Γ(z+1)=zΓ(z) is order-1 difference with rational coefficient. Hence G is difference-tame (tower
ℂ(z)→ℂ(z,Γ)→ℂ(z,Γ,G), each step order-1), HT only differentially — same as double sine and ζ.

**Verdict on the discriminator:** LOW discriminating power on the classical family. Γ, ζ, double sine,
Barnes G are ALL difference-tame; shift coefficients close (rationally or on the circle), escape is
ALWAYS differential. That is ~what "special function" means (tame shift relations by construction). The
escape-vs-closure lens does not separate the natural objects; a genuinely shift-escaping object would
have to be non-classical. Line closed (the lens is descriptive, not productive on this family).

- 2026-06-24 — Turing: discriminator has low power (all classical HT objects difference-tame); honest
  negative on own tool. Escape-vs-closure line closed.
