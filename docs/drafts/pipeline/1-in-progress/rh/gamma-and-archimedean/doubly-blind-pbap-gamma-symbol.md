# Doubly blind PBAP and the pure Gamma symbol θ′ + 2sin²θ

- **ID:** doubly-blind-pbap
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** producer loop rows 288–291 (`1-in-progress/producer-loop-opus-2026-10-12.md`)
- **Statement:** (C291) RH ⟺ ∫|𝓜u(½+it)|²(θ′(t) + 2sin²θ(t))dt ≥ 0 for every test u whose multiplicative
  autocorrelation g is blind on both sides: g(n) = ĝ(n) = 0 for all integers n ≥ 2.

## Goal
- PBAP for ζ needs the pole term, an evaluation off the critical line (CANNOT-539, MUST-1445, rows 283 and 289).
  Every real-line method stops there.
- Poisson summation removes it. For doubly blind tests the pole equals 2g(1) − 2ĝ(1) = (2/π)∫|𝓜u|²sin²θ, and the
  Weil energy becomes the integral of the purely archimedean real-line symbol Θ = θ′ + 2sin²θ against the spectral
  measure.
- If C291 holds, RH is a positivity statement for a Gamma-only symbol on a cone cut out by two arithmetic families of
  linear conditions (Dirichlet characters n^{−it} and twisted characters e^{−2iθ(t)}k^{it}).

## Gates
- [x] 0 → 1 in-progress: identities checked on paper (row 291), attack plan below
- [ ] 1 → 2 fully-proven
- [ ] 2 → 3 formalized
- [ ] 3 → 4 publication-ready

## Approach
1. **Identities [P].**
   - pole = ĝ(0); Poisson gives ĝ(0) = 2g(1) − 2ĝ(1) + 2Σ_{n≥2}g(n) − 2Σ_{k≥2}ĝ(k).
   - g(1) = (1/2π)∫|𝓜u|²; ĝ(1) = (1/2π)∫|𝓜u|²cos 2θ (Mellin–Parseval with 𝓜[2cos 2πy](½−it) = χ(½+it) = e^{−2iθ}).
   - Prime-blind tests: Q_arch = (1/π)∫|𝓜u|²(θ′ + 1 − Re ζ(½+it)).
   - Doubly blind tests: Q_arch = (1/π)∫|𝓜u|²Θ.
2. **Existence of doubly blind PD tests.** Window tests (log-support in [−log 2, log 2]) are prime-blind
   automatically. Fourier blindness on [½, 2] leaves an infinite-dimensional space, because the integer cosines are
   incomplete on an interval of length 1.5. Large-support examples are open. Stationary phase: twisted blindness at k
   localises near t = 2πk.
3. **Uniqueness.** The corpus proof (`eq_vonMangoldt_of_weilPositiveFull`) uses a prime-blind Ξ-divisible null family
   that is not known to be Fourier-blind. A doubly blind certificate has extra Fourier-side weights b_k (symbols
   k^{−½}cos(2θ − t log k)). Uniqueness needs a doubly blind Ξ-divisible null family. Its Fourier-side condition
   involves ζ(½+it)² (Voronoi / d(m)), linking to the (N1)/T₂ lane.
4. **Lean.** Poisson pole lemma (done: see Log), then the Mellin evaluation of ĝ(1) with χ, then the Θ identity.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** —
- **Strongest positive survivor:** —
- **New insight:** —
- **Status:** —

## Log
- 2026-10-14 — created in 1-in-progress (rows 288–291)
- 2026-10-14 — [L] Poisson pole lemmas `fourier_zero_eq_poisson`, `fourier_zero_eq_of_blind`,
  `fourier_zero_eq_of_doublyBlind` in `RHTower/BlindIntegerFareyMoebius`. C291 reduced to the Fourier-repair lemma
  R291: prime-blind Ξ²-divisible null tests realise every Fourier-value sequence (ĝ(k))_{k≥2}. This is a Voronoi
  interpolation problem (row 292).
- 2026-10-14 — [L] `RHTower/DoublyBlindCorePoleDistance`: for doubly blind compact cores the pole is
  Ψ_f(0) = ‖f − JCf‖² ≥ 0, and mean-zero doubly blind cores vanish (row 294). R291 recast as pointedness of the
  null Fourier image; C291 ⟸ non-pointed (row 293).
- 2026-10-14 — rows 295–297: JC = multiplier e^{−2iθ} (not an involution; earlier ± split withdrawn).
  Fourier blindness acts as virtual nodes log(215.3k) at low frequency (215.3 = e^{−A(0)}). By analogy with row 269
  (extra nodes fatten the dual cone) C291 is probably false. Deciding it needs a doubly blind Ξ²-divisible null
  family (true) or a finite twisted certificate (false; numerics).
- 2026-10-14 — row 300: the pole energy is the product ⟨h,e^{x/2}⟩⟨h,e^{−x/2}⟩ (signature (1,1)).
  - Prime-blind detection of an off-line zero needs exponentially negative pole energy.
  - Doubly blind tests have pole ‖f − JCf‖² ≥ 0, hence F ≥ −5.37‖u‖². C291 can only hold through bounded-strength
    ("mild") detection; this does not refute it.
- 2026-10-14 — cross-reference (rh-goal-loop row 1198, card `0-backlog/modular-null-face-single-ray.md`). Inside the twisted-arc family, ν ⊥ {twArcMoment_n} ⟺ the 1-periodized witness W_ν is a trigonometric polynomial of degree ≤ 1 (Basset + Poisson). If this annihilator is ℝν* (conjecture C1189b), the arc family supplies only one blind Ξ²-null ray. R291 would then need Ξ²-divisible blind tests from outside the arc family. Every arc test has pole ∝ ∫√(y/2)dν, which is > 0 on that ray.
- 2026-10-14 — row 307 [L] `RHTower/CosDilationBlindSesquiSupportVanishing`.
  - Nonzero doubly blind compact cores need support ratio ≥ 3/2.
  - Hann-window form of Fourier-integer blindness [P].
  - Open C307: no doubly blind cores below ratio 2. Existence of doubly blind cores at any ratio is still open;
    without it C291 is vacuous on compact tests.
- 2026-10-14 — row 309 [L] `RHTower/CosDilationBlindGoldenSupportVanishing`: nonzero doubly blind compact cores
  need support ratio ≥ (1+√5)/2. Proof: Farey transfer recursion plus analytic continuation.
- 2026-10-14 — row 310, corrected in row 311: the TMP witness h is Fourier-side blind (𝓕h(N) = 0 for N ≥ 2, PD log
  profile, inversion law). It is therefore a noncompact Ψ-blind kernel, but it is not known to vanish at the integers,
  so it is not known to be doubly blind.
  - The null kernel ξ²R it produces is integer-blind (A-side) and Ξ²-divisible. Its Fourier-side blindness is the
    Voronoi/ζ² condition R291.
  - The earlier claim "C291 is non-vacuous via (N1)" is withdrawn. Existence of doubly blind tests remains open.
  - Compact ones need ratio ≥ φ [L] and ≥ 5/3 [P].
- 2026-10-14 — cross-reference (rh-goal-loop-opus, after row 1203), Lean infrastructure note for C331 (R* = 2): Mathlib in this toolchain does have the Fredholm alternative for compact operators on Banach spaces. See `Mathlib/Analysis/Normed/Operator/Compact/FredholmAlternative.lean`, with `hasEigenvalue_or_mem_resolventSet`, `hasEigenvalue_iff_mem_spectrum` and `antilipschitz_of_not_hasEigenvalue`. Producer-loop row 327's "no Fredholm alternative" is out of date. Bessel `J₀` and the Hankel transform are still absent, so the ½-contraction route of row 327 would need them built.
