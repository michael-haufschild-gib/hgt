# A real-rooted Dirichlet series with the functional equation of ζ³ (C394, the negation of C329)

- **ID:** real-rooted-twin-existence-c394
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (with a proved reduction chain and one open lemma)
- **Source:** producer ledger `hf-positive-hodge-attack/krein-producer-loops.md`, L391–L398. Builds on Theorem A (`3-formalized/degree-three-fake-zeta-cubed-abundance.md`), MUST-670 (`RHTower.WeilBoundaryFractionalCountingTwin`), and the C329 card.
- **Statement:** There is `F = Σ f_n n^{−s}` with `f_1 = 1`, `Γ_ℝ(s)³F(s)` meromorphic with only poles at `0, 1` (order 3), `Γ_ℝ(s)³F(s) = Γ_ℝ(1−s)³F(1−s)`, `F ≠ ζ³`, and all zeros of `(s(s−1))³Γ_ℝ(s)³F(s)` on `Re s = ½`.

## Goal
- **Consequence.** `lam := Λ_F/3`, where `−F'/F = Σ Λ_F(n)n^{−s}`, is an integer-supported, full-cone, Weil-positive weight system for ζ's archimedean datum with the pole. It is a **producer of positivity that does not depend on RH**.
  - Hence `W ≠ ∅`, i.e. PBAP holds unconditionally.
  - `W ≠ {Λ}`. If RH holds, `W` has at least two extreme points.
- **Non-circularity.** Nothing about the zeros of ζ is assumed. `F` is a different function, and its real-rootedness is a statement about `F` alone.
- **Why this route.** Every certificate route of the form `ζ × (Möbius polynomial)` (GY, mollifier, sieve), the Gram-node route, and the prime-gap weights need near-RH input (L393, L396, L398). Twins need no certificate.

## Gates
- [x] 0 → 1  in-progress: well-posed; reduction chain R1–R3 proved on paper; open lemma R4 isolated; falsification test specified
- [ ] 1 → 2  fully-proven: R4 proved
- [ ] 2 → 3  formalized
- [ ] 3 → 4  (no stage 4 by directive)

## Reduction chain
- **R1 (twin ⇒ producer) [P, standard].** The explicit formula for `F` (Hadamard product of `ξ_F`, contour shift) gives `𝓕(μ_F/3) = T_∞ − ν_{Λ_F/3}`, where `μ_F` is the zero-counting measure. If `F` is real-rooted, `μ_F ≥ 0`, and the corpus converse explicit formula (MUST-642, `WeilFormConverseExplicitFormula`) gives full-cone Weil positivity of `Λ_F/3`.
  - Lean status: the explicit formula for a general `F ∈ V₃` is not in the corpus; `Zeta23`'s `EF_lit` is ζ-specific.
  - The converse direction (fractional counting ⇒ twin) is MUST-670. The corpus Herglotz bridge (`WeilFullConeHerglotzRightHalfPlane`) goes from positivity to Herglotz, not back.
- **R2 (staircase form) [P, L394].** Twins correspond exactly to real sequences `(b_m)_{m≥2}` for which `N(t) = 3θ(t)/π + 3 + Σ_m b_m sin(t log m)` is a non-decreasing integer step function, with `b_m = −Λ_F(m)/(π√m log m)`.
- **R3 (local-to-global compactness) [P].** Fix `n₀ ≥ 2`. Suppose for each `T` there is `F_T ∈ ζ³ + W` (`W` = the entire self-dual part, Theorem A) with:
  - (i) every zero of `ξ_{F_T}` with `|Im| ≤ T` on the line;
  - (ii) `|f^{(T)}_n| ≤ C n^A` uniformly in `T`;
  - (iii) `F_T − ζ³` with coefficient `1` at `n₀` (or bounded below in a fixed coefficient).

  Then a twin exists.
  - *Proof.* (ii) and the functional equation give uniform bounds for `Λ_{F_T}` in vertical strips (Phragmén–Lindelöf), so the family is normal. Coefficients converge, since `f_n` is given by Perron integrals on `σ = A + 2`.
  - The limit `F` lies in `V₃`, has `f_1 = 1`, and differs from `ζ³` by (iii).
  - A zero of `ξ_F` off the line at height `γ` would, by Hurwitz, be a limit of zeros of `ξ_{F_T}` off the line at heights `≈ γ < T`, contradicting (i). ∎
- **R4 (local twins with uniform bounds) [OPEN CORE].** Show that the `F_T` of R3 exist.

## Evidence for R4
- **Phase-space count (L394).** Zero positions in degree `k` cover the Nyquist band `|x| ≤ (k/2)log t`; `log ℕ` covers `|t| ≤ πe^{|x|}`. Unknowns minus constraints is `≈ ((k−2)/2π)T log T`.
  - Overdetermined for `k = 1` (Hamburger: only ζ, and only under RH).
  - Critical for `k = 2` (Kaczorowski–Perelli: only ζ²).
  - Underdetermined for `k = 3`. This is consistent with `dim W = ∞` (Theorem A).
- **Separate component.** No twin lies near `ζ³` (rosette and unfolding argument: a real-root-preserving deformation of a triple zero needs `E ∈ ζ·(entire part of V₂) = 0`). Twins therefore have simple zeros and lie far from `ζ³`.
- **Necessary structure.** By the Davenport–Heilbronn argument, `Σ|f_n − d₃(n)|/n = ∞`: `F − ζ³` is Euler-like in its large-prime tail. Pair correlation and Bohr–Jessen checks are compatible (L395).

## Approach to R4
1. **Finite-height linear-algebra form.**
   - Truncate the `W`-basis from Theorem A's KNS relations (lacunary node removal), giving `E_1, …, E_M`.
   - Impose Gram-sign constraints `(−1)^j Z_F(g^{(3)}_j) > 0` at the degree-3 Gram points up to `T`, plus a Turing-count bound on `S_F(T)`.
   - Feasibility of this linear system implies (i).
   - Minimize `max_n |f_n|/(d₃(n)n^A)` for (ii).
2. **Analytic route.** A KNS frame inequality for the pair (zero-like set of density `(3/2π)log t`, `log ℕ`) plus Newton. The precise obstruction is the Poincaré–Wirtinger weight mismatch, `log²t` against `t²` (L395). It needs wave-packet localization along `|x| = log(t/π)`. The Lean-proved `RHTower.LogLatticePoisson.norm_integral_le_of_vanish_logLattice` is the `log ℕ`-side local estimate.

## Falsification test (decisive)
- Approach 1 with `M ≤ 300`, i.e. height `T ≍ 2πM^{2/3}`.
  - A plateau of `max_n |f_n|/d₃(n)` as `M` grows supports C394.
  - Growth like `exp(cM^{2/3})` refutes it (then C329 holds and the twin door closes).
- This is a runpod job of minutes. Under the user's compute policy it needs explicit authorization, which has not been given.

## Log
- 2026-10-03 — created from L394–L398 as the single remaining non-RH producer route. R1–R3 hold; R4 is open.
- 2026-10-03 — L399. `dim W` per unit height is `((d−2)/2π)log t`, matching the zeros-first surplus. So the real-rooted locus is open in `ζ³ + W`, and C394 ⟺ existence of one simple-zero seed.
  - Rice/Wendel and the literature pattern (DH, Epstein, Hejhal's Hecke groups) argue against a seed; the zeros-first construction argues for one.
  - Verdict: undecided. R4 reduces to finding a single seed. The decisive finite test is unchanged.
- 2026-10-03 — L400 corrects L399. Openness needs twins with crystalline zero gaps, but twins with Montgomery-type statistics would be marginal (an `ε ≳ g²` splitting of close pairs). C394 is disfavoured.
  - Sharp sub-question: is a crystalline twin (normalized gaps bounded below) possible? A Rodgers–Tao-type crystallization contradiction for `F` would make twins isolated.
- 2026-10-03 — Falsification test (approach 1) run. No macroscopic local twins up to `T = 120` (d = 3), `70` (d = 4), `55` (d = 5); details in the C329 card log.
  - Visible W freedom per window equals ζ's zero count (critical).
  - R4 survives only in the fine-structure regime forced by certified pinning.
