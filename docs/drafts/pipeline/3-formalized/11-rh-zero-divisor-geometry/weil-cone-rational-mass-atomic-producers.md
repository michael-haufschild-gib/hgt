# Rational-mass atomic producers are fake ζᵏ with RH; half-integer masses force Λ

- **ID:** weil-cone-rational-mass-atomic-producers
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** krein-producer-loops L150, L153, L168 (open item "mixed/irrational masses"), L222
- **Statement:**
  - (a) Let `k ≥ 1`. A real `lam` is a full-cone producer whose Weil measure has `kμ((a,b]) ∈ ℕ` for all `a < b` (an atomic, locally finite measure with masses in `(1/k)ℤ_{>0}`) **if and only if** `Σ|lam(n)|n^{−σ} < ∞` for `σ > 1` and `lam = (1/k)Λ_G`, where:
    - `G = Σ g(n)n^{−s}` converges absolutely on `Re s > 1` and `g(1) = 1`;
    - the completion `E(s) = (s(s−1)Γ_ℝ(s))^k G(s)` is entire of finite order with `E(1−s) = ±E(s)` (archimedean factor `Γ_ℝ(s)^k`, conductor 1);
    - `E(1) ≠ 0`, i.e. `G` has a pole of exact order `k` at `s = 1` and no other pole;
    - every zero of `E` lies on `Re s = ½`.

    For such `G` the Weil measure is `(1/k)Σ_ρ δ_{Im ρ}` over the zeros of `E` with multiplicity, and the sign of the functional equation is `(−1)^{kμ({0})}`.
  - (b) For `k = 2`: `G = ζ²`, so `lam = Λ` and RH holds. Atoms may lie anywhere, and the sign is forced to be `+1`.

## Goal
Close part of the atomic branch of the uniqueness problem beyond L153 (integer masses), and turn the rest into a precise converse-theorem question.

## Gates
- [x] 0 → 1
- [x] 1 → 2: paper proof, modulo classical inputs:
  - Maass's converse theorem for even forms at level 1 (one functional equation, via Cauchy data on the imaginary axis);
  - `λ₁(SL₂(ℤ)) > ¼` (Roelcke; the numerical value is `91.14`);
  - the Eisenstein constant-term analysis at `s = ½`.
- [x] 2 → 3: (a) and (b) formalized unconditionally. All classical inputs are proved in Lean (see Lean section).
- [ ] 3 → 4

## Lean
- **(a), the exact correspondence:** `RHTower.WeilZetaPower.weilPositiveFull_counting_iff_zetaPowerDatum` (module `RHTower/WeilZetaPowerForward`).
  - The datum is the structure `WeilZetaPower.ZetaPowerDatum k g E`.
  - `lam = (1/k)Λ_G` is stated as `G' = −k (Σ_{n≥2} lam(n)n^{−s}) G` on `Re s > 1`.
  - Forward: `exists_zetaPowerDatum_of_fractional_counting`. It also assumes only a.e. counting.
  - Converse: `weilPositiveFull_of_zetaPowerDatum`. Weil measure `= (1/k)Σ_ρ δ_{Im ρ}`: `boundaryMeasure_eq_zeroMeasure`. Counting: `exists_natCast_eq_mul_boundaryMeasure` (module `RHTower/WeilZetaPowerConverse`).
- **Bricks of (a):**
  - `WeilFunctionalLineIntegral`: the Weil functional is the line integral `(1/2π)∫(H(c+it)+H(1−c−it))Φ_lam(c+it)dt`; generic prime side; two-line simple-pole residue identity.
  - `WeilAtomicExplicitFormula`: the explicit formula for an atomic Weil function; positive atoms ⇒ `WeilPositiveFull`.
  - `WeilAtomicBoundaryMeasure`: the Weil measure of an atomic Weil function is the atomic measure (Bochner measures of translated autocorrelations, mollifier shells).
  - `CompletionLogDerivZeroPairs`: `E'/E = ½Σ_ρ(1/(s−ρ) + 1/(s−1+ρ))` via order-one Hadamard; the zero divisor is symmetric under `ρ ↦ 1−ρ`.
  - `CompletionOrderOneEnvelope`: finite order ⇒ order-one envelope, via Phragmén–Lindelöf on `−1 ≤ Re s ≤ 2`, `Γ ≤ 1` on `[1,2]` and `Γ(x) ≤ xˣ`.
- **(b), k = 2:** `RHTower.HalfIntegerMassRigidity.vonMangoldt_and_riemannHypothesis_of_half_integer_counting`.
  - Statement: Weil-positive with `2μ((a,b]) ∈ ℕ` a.e. ⇒ `lam = Λ`, RH. There is no gap hypothesis; atoms may lie anywhere.
  - Inputs: `G^k = K·P·Q` (`WeilRationalMassAtomicProduct.bigG_pow_eq_of_fractional_counting`); level-one Maass converse at λ = ¼ with sign (`MaassConverseLevelOne`); constant-term Wronskian (`MaassConstantTermWronskian`); no even level-one cusp form at λ = ¼ (`MaassLevelOneCuspVanishing`); converse theorem for ζ² and the odd case (`MaassZetaSquaredConverse`).
- **Audit:**
  - Standard axioms only (propext, Classical.choice, Quot.sound).
  - All modules are wired into `RHTower.lean`, `lake build --old` is green, and the collision sweep is clean.

## Proof sketch
1. **Setup.** The Herglotz function is `Φ = Σ m_j 2(s−½)/((s−½)²+t_j²)`, so `E = exp∫Φ = Π(1+(s−½)²/t_j²)^{m_j} = C·s(s−1)Γ_ℝ(s)F(s)`, with `F = exp(Σ lam(n)n^{−s}/log n)`.
2. **Degree-k functional equation.**
   - `E^k = K·P·Q` is single-valued and entire.
   - `P` is the polynomial of the finitely many atoms in `(−1,1)`; `Q` is the genus-one product over the others.
   - `P(1−s) = (−1)^{deg P}P(s)` and `Q(1−s) = Q(s)`.
   - So `G = F^k` has ζᵏ's functional equation with sign `(−1)^{kμ({0})}`. Its zeros are the atoms.
   - Finite order: `|P|` and `|Q|` increase in `σ ≥ ½`, so `E^k` is bounded on `−1 ≤ Re s ≤ 2`; Stirling handles the rest.
3. **Datum.** Only `Γ_ℝ(s)^k` with conductor 1 is allowed. The Weil functional carries ζ's archimedean datum, so this is built in.
4. **Converse.** For `lam = (1/k)Λ_G`:
   - Finite order upgrades to order one (Phragmén–Lindelöf).
   - Hadamard gives `kΦ_lam = E'/E = ½Σ_ρ g_ρ`.
   - The two-line residue identity evaluates `W_lam(f⋆f̃) = (1/2k)Σ_ρ(|f̂(γ)|²+|f̂(−γ)|²) ≥ 0`.
   - The same formula on translates identifies the Weil measure as `(1/k)Σ_{zeros} δ`.
5. **k = 2.**
   - Form `u(z) = c(y) + Σ g_n 4√y K₀(2πny)cos 2πnx`. It is even and a Δ-eigenfunction with `λ = ¼`.
   - The functional equation gives `u∘S = ±u` on `x = 0`; evenness and unique continuation give `u∘S ≡ ±u`.
   - The sign `−1` is impossible by `(ST)³ = 1` and `g₁ = 1`.
   - There are no `λ = ¼` cusp forms for `SL₂(ℤ)`. The constant-term Wronskian makes `u` proportional to the ζ² function, so `G = ζ²`, `F = ζ`, `lam = Λ`, and RH follows.

## Literature audit (L223)
Part (b) is a corollary of the Kaczorowski–Perelli classification of degree-2, conductor-1 functions in the extended Selberg class (Adv. Math. 2022; arXiv 2503.02492). The datum `Γ_ℝ²` is their case `χ_F = 0`, whose only member is ζ². So (b) is a BRIDGE. The new content is the correspondence (a) and the datum rigidity at `t = 0`. Degree 3 with conductor 1 has no classification in the literature.

## Open core (k ≥ 3)
- `V_k = ζᵏ·V₀^{ζ,k}`, where `V₀^{ζ,k}` is the set of Dirichlet series `B` with `B(s) = B(1−s)` whose only poles are at nontrivial zeta zeros (of order `≤ k·`multiplicity).
- For `k = 3`: `G/ζ` is a λ = ¼ Maass-type function whose `S`-defect is supported on the zeta spectrum.
- Automorphic fakes are excluded: a level-1 GL(3) cusp form with trivial parameters would have `λ = 1`, below Miller's bound.
- A non-automorphic `G ≠ ζ³` with RH would be a non-Λ producer.
- Open sub-question exposed by Lean: whether the sign `−1` (an odd central multiplicity `kμ({0})`) can occur for `k ≥ 3`.

## No-go closure
- **Killing theorem:** (b) for masses in `½ℤ`.
- **Strongest positive survivor:** the exact correspondence (a) between rational-mass atomic producers and fake ζᵏ with RH, now formal as an iff. It is a new producer source and a new link between Weil-cone uniqueness and twist-free converse theorems.
- **Status:** (a) and (b) formal; (k ≥ 3) open.

## Log
- 2026-09-30 — created at stage 2
- 2026-10-05 — (b) formalized: atoms anywhere, both functional-equation signs, no gap hypothesis.
- 2026-10-05 — (a) formalized in both directions, as an iff, together with the Weil-measure identity `μ = (1/k)Σ_ρ δ`. Correction exposed by Lean: the functional equation of `E` holds with sign `(−1)^{kμ({0})}`. The paper's "E^k even" overlooked an odd central atom. For `k = 2` the sign is `+1` by (b). Moved to stage 3.
