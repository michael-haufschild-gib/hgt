# Real-rooted twins of ζ^k: is the moduli space a point? (C329)

- **ID:** real-rooted-twin-moduli-c329
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `hf-positive-hodge-attack/krein-producer-loops.md`, L329–L342 (session 2026-10-03). Builds on Theorem A (`degree-three-abundance-supercritical-pairs.md`), MUST-669/670, L256, L286, L290, L317.
- **Statement:** For every `k ≥ 1`, the only `F ∈ V_k` (Dirichlet series over ℕ with the `Γ_ℝ(s)^k` functional equation, conductor 1) with `f_1 = 1`, a pole of order `k` at `s = 1` and all zeros of the completion on `Re s = ½` is `ζ^k` (under RH), and there is none otherwise.

## Goal
This is the single open core behind the producer question beyond `Λ`.
- **Uniqueness.** By MUST-670, a phase-locked producer with `1/k`-integer counting is exactly such a real-rooted twin. C329 together with Ω (no continuous producers) and C323 (atomic extremes) would give `W = {Λ}`.
- **Slack (L74).** Twin differences are Gordan certificates on near-radical spaces (L338). C329 is the missing input for L74 alongside the L332 noise–dip dichotomy.
- **Detection.** Any producer, in particular a twin, is a certificate against prime-blind detection (L337). So `W ≠ ∅ ⇒ RH` needs C329 together with Ω.
- **Non-circularity.** C329 is a statement about Dirichlet series with ζ's datum. It does not assume RH for ζ: the "under RH" clause only fixes which object is the trivial one.

## Gates
- [x] 0 → 1  in-progress: well-posed; reductions L338–L340; known exclusions listed below.
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready (no stage 4 by directive)

## Known exclusions (all corpus or this session)
- `k = 1`: Hamburger, so `V_1 = ℂζ` (Lean). `k = 2`: Maass converse / Kaczorowski–Perelli degree 2, conductor 1, so `V_2 = ℂζ²` (paper).
- Rational twins `F/ζ^k = P₁/P₂` with Dirichlet polynomials: trivial (L286; Kaczorowski–Perelli degree-1 conductor integrality / Hecke non-discreteness).
- Perturbative twins `ζ^k + εE`: rosettes at `k`-fold zeros give off-line zeros unless `E` vanishes at every ζ-zero, which forces `E ∝ ζ^k` (L289, L301).
- Pólya (n=1-dominated) twins with unbalanced low coefficients: tail inflation, far-right zero combs (L290).
- Twins with log-square-summable deviation `Σ(lam_F/k − Λ)²/(1+log n)^K < ∞`: trivial (L163, Lean).
- ζ-light twins: trivial (L152/L155, Lean). Real twins are ζ-heavy, `A = ∞` (L342).

## Reduction (L339–L340)
- Under RH, PBAP holds, so the degree-`k` Gram-law inequalities together with Turing count control are feasible at every finite height (L317 correction: balanced edits do not inflate the tail; the Farkas certificate attaches to the count, not to the Gram values).
- Let `F_M ∈ ζ³ + W_3` have simple real zeros up to `T_M ≍ 2πM^{2/3}` obeying Gram's law.
  - If the coefficients stay uniformly bounded, a limit `F_∞` exists, is real-rooted, and differs from `ζ³` (Gram's law prevents triple-zero merging). That would refute C329.
  - So under RH, **bounded Gram twins refute C329**. (The converse fails: a real-rooted twin need not obey Gram's law. L343 corrects L339.)
- A limit `F_∞` would have `|S_F| ≤ 1`, hence log-coefficients with `Σb_n²/n < ∞`, spread over composites: an **anti-Selberg** real-rooted twin, a balanced Pólya twin.
- Bounded Gram twins would produce a real-rooted `F ∈ V_3` with bounded `S_F`. By L343 (Bohr's inequality on `σ > 1`), such `F` has `Σ_p|f_p|/p < ∞`, i.e. `E` cancels `ζ³` on the primes.

## Approach
1. **Decisive finite test (queued; needs user authorization for a runpod run).** Construct `F_M` for `M ≤ ≈300` by exact or rational linear algebra:
   - the balanced low-coefficient subspace (jet balance at `y = 1`);
   - plus Gram-sign constraints at degree-3 Gram points;
   - plus a Turing-count constraint.
   Record `max_n |f_n|/d_3(n)` as a function of `M`. Growth like `exp(cM^{2/3})` supports C329; a plateau refutes it.
2. **Analytic.** Find an obstruction to anti-Selberg real-rooted twins that is not a second-moment or ζ-mass argument (both are blind: L341, L342). Candidates:
   - the Hecke/KNS structure of `W_3` (coefficients as values of a self-dual kernel);
   - a Rodgers–Tao-type heat-flow argument (crystalline zeros mean de Bruijn–Newman constant `< 0`, which might be incompatible with the FE plus a pole);
   - a quasicrystal uniqueness theorem with log-growing density (L330).

## Log
- 2026-10-03 — created at stage 1 from ledger rows L329–L342. No exclusion of the anti-Selberg class yet. Decisive test queued.
- 2026-10-03 — L343: Bohr-inequality constraint on anti-Selberg objects; L339's ⟺ downgraded to ⇒.
- 2026-10-03 — L344: relaxed producers are quasi-RH ladders (no bypass). An anti-Selberg twin needs log|F| to be an infinite-degree heavy-tailed chaos on T^∞ (Bohr lift); degree ≤ 2 chaos killed (L345 correction: degree ≥ 3 is not).
- 2026-10-03 — L387/L389: this is the only producer route that does not pass through RH.
  - Perturbative twins: rechecked dead.
  - The degree-0 inner class (`G(s) = G(1−s)`, divisor on the line) has nonconstant finite-prime members, e.g. `((1−2^{½−s})/(1+2^{½−s}))²`. So rigidity must come from the prescribed `−3` multiplicity at ζ's zeros (density `T log T`), which forces infinitely many primes.
  - Spectral-gap and high-moment conditions are automatic for all of `V₃`.
  - The decisive test (approach 1) still needs user authorization for a runpod run.
- 2026-10-03 — L394 reverses the expected verdict.
  - Twins are exactly the integer staircases `kθ/π + k + Σ b_m sin(t log m)`.
  - The zeros-first phase-space count is overdetermined for `k=1`, critical for `k=2`, and underdetermined by `((k−2)/2π)T log T` for `k ≥ 3`. It predicts real-rooted twins for `k ≥ 3` (C394 = ¬C329), on a component separate from `ζ^k` (rigid: unfoldings need the entire part of `V₂`, which is `0`).
  - Open core: KNS frame for `(Γ, log ℕ)`, a small-residual seed, Newton.
  - The Gram-twin test (approach 1) is the discriminator; its prediction is now "feasible".
- 2026-10-03 — **Decisive Gram-twin test run** (runpod; `computations/2026-10-03-twin-gram-lp`, `-w3-window-density`).
  - Gram-law twins: LP-infeasible at `T = 30, 50, 80`, even with unbounded coefficients.
  - With coefficients ≤ 1000·d₃(n) over certified visible W directions, ζ³+E keeps only ζ's own sign changes (10/28, 21/62, 41/114 at `T = 50, 80, 120`). Degrees 4 and 5 are no better (20/66, 29/56).
  - Window-local `dim W₃` equals ζ's zero count `ϑ/π` (L399 exact), so perturbative twin conditions (one per ζ zero) are exactly critical.
  - Certified pinning (`certified-producer-pinning.md`): any twin has `Λ_F(n)/3` equal to `Λ(n)` to 1e-9..3e-5 for n ≤ 5, and |Λ_F(6)/3| ≤ 4.3e-3. So a twin is ζ³ at small n.
  - **Open:** fine-structure twins (tiny E vanishing at low zeros with the right derivative signs) are invisible at double precision. The perturbative-to-macroscopic transition decides C329.
- 2026-10-11 — Opus loop rows 2046–2061: the cubic ladder in Lean, and the obstruction beyond it.
  - [L] MUST-930 + addenda 1–3. A cubic datum `ZetaPowerDatum 3 g E` (`E(1) ≠ 0`, either sign) is `g(1)ζ³` or misses ξ's divisor at infinitely many points. Odd data are never `ζ³`. Degree `k`: `k−2` copies of ξ's divisor force `g(1)ζᵏ`. So every twin has infinitely many deficits, and perturbative twins (L289/L301) are excluded in Lean.
  - The extras side: finitely many extras ⇒ trivial (corpus ζ-mass rigidity). Mean-value receivers reach at best `o(T/(log T)^{4/3})` extras and are ζ-mass arguments, hence blind to real twins (L341/L342; row 2056).
  - The deficit side: the residues of `L(g)/ζ` at deficits are polynomially bounded given deficit–deficit separation (strip Blaschke product + Phragmén–Lindelöf; `1/ζ'` is not the obstruction). But they do not decay, so absolute-summability arguments fail in principle (row 2060). The infinite odd packet converges absolutely in the interior, but the three-term identity forces the boundary point 1. In Mellin form, rigidity ⟺ the packet's spectral zeta `Σ c_ρ(−iγ_ρ)^{s−1}` has no poles at `ρ + 1` (row 2061).
  - Row 2036's HKO pencil survivor is only a dichotomy (row 2058): either the pencil leaves LP for small `λ`, or the twin shares every simple critical zero.
