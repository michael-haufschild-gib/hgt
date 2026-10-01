# Finite evaluation blindness with a regular support tuple (Θ4, generic case)

- **ID:** critical-locus-regular-tuple-blindness
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** backlog `0-backlog/critical-locus-finite-evaluation-blindness.md` (Θ4); loop rows 126, 130.
- **Statement:** Let `F₁, …, F_k` be spectral tests that are holomorphic on a strip around the critical line and decay in the substrip. If the line-pair derivatives `u_i'` admit an invertible evaluation matrix at support ordinates, then every sufficiently distant off-line quadruple of displacement `t*` is compensated exactly by sliding those `k` support ordinates.

## Goal
Θ4 says that no finite family of spectral positivity tests implies RH. The single-test case is `singleTest_blindness`. This card proves every `k` whenever the configuration's support is not inside the common critical set of a combination of the tests.

## Gates
- [x] 0 → 1: zero-base slide blocks (row 126).
- [x] 1 → 2: inverse function theorem argument (paper, below).
- [x] 2 → 3: `regularTuple_blindness`, `supportIndependent_blindness`. `lake env lean` clean, `--old` build, standard axioms, 0 collisions, wired after `CriticalLocusSingleTestBlindness`.
- [ ] Degenerate case (support in a common critical set): open.

## Proof
1. Define the slide map `f(ε)_i = Σ_m (u_i(α_m + ε_m) − u_i(α_m))`. Then `f(0) = 0`, and `Df(0) = (u_i'(α_m))` is invertible.
2. By the inverse function theorem, `map f (𝓝 0) = 𝓝 0`, so `f '' univ ∈ 𝓝 0`.
3. The quadruple vector `(4 Re F_i(½ + t* + iγ))_i` tends to `0` as `γ → ∞`. Its negative eventually lies in `f '' univ`, and the preimage gives the slides.
4. A regular tuple exists under linear independence on the support. This uses the corpus's `exists_injective_evaluation_minor_of_linearIndependent` and the complex evaluation minor to obtain a real nonzero determinant.

## Remaining case
`W = {w : w·u'(α) = 0 for all support α} ≠ 0`. The support then lies in `Crit(Σ w_i u_i)`. Second-order slides give `w·u''(α) ε²`. Tiny moves (far insertions, far quadruples, far deletions, second-order slides) positively span by the minimum principle. The missing piece is an assembly lemma with uniform rounding, because far-deletion directions drift.

### One degenerate direction (`dim W = 1`), paper
Take `w` spanning `W` and `g = w·u`, and suppose `g` is positive-type (otherwise far insertions with `g < 0` already supply both signs).
1. Fix a far support point `α_f`. Delete it and re-insert at a free `β`. The `W`-value is `2(g(β) − g(α_f))`, and the `V`-value is `2P_V(u(β) − u(α_f))`, which is small for `β ≥ α_f` far.
2. A first-order slide block at support points spanning `V` solves the `V`-equation, with slides `ε(β)` depending continuously on `β` (inverse function theorem with parameter).
3. The `W`-equation becomes a continuous function of `β`. At `β = α_f` it is positive, `≈ 4 Re F_w(q₀)`. As `β → ∞` it is negative once `4 Re F_w(q₀) < 2g(α_f)`. The intermediate value theorem closes the argument.
4. For `dim W ≥ 2` this needs a `j`-dimensional intermediate value theorem (Poincaré–Miranda), which is not in mathlib.

## Log
- 2026-10-01: formalized (row 130). STATUS MUST-653.
