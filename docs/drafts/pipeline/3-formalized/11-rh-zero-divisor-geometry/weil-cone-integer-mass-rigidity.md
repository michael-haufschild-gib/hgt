# Integer spectral masses force Λ and the Riemann hypothesis (arbitrary ordinates)

- **ID:** weil-cone-integer-mass-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** krein-producer-loops L153 (paper, verdict BRIDGE), L228/L229 (Hamburger stability), L233 · STATUS MUST-608
- **Statement.** Let `Σ_n |lam(n)| n^{−σ} < ∞` for `σ > 1`. Suppose that on `Re s > 1`
  `Γ̃(s) + 1/(s−1) − Σ_{n≥2} lam(n)n^{−s} = 2(s−½) Σ_j m_j/((s−½)² + t_j²)`,
  with integers `m_j ≥ 0`, ordinates `t_j ≥ 1` and `Σ_j m_j/t_j² < ∞`. Then `lam(n) = Λ(n)` for every `n ≥ 2`, and the Riemann hypothesis holds.
  - The ordinates are **not** assumed to be zeta ordinates.
  - This is the formal form of: "an atomic Weil-positive weight system with integer masses is Λ".

## Goal
L150 (`crystalline_producer_rigidity`) needed the atoms at zeta ordinates. L153 removed that hypothesis on paper by exponentiating the Herglotz function. This card makes L153 formal and removes the ordinate hypothesis.

## Gates
- [x] 0 → 1
- [x] 1 → 2: L153 paper proof.
- [x] 2 → 3: `RHTower.IntegerMassRigidity.integer_mass_rigidity` (module `RHTower/WeilIntegerMassAtomicRigidity.lean`, 988 lines), with the Dirichlet exponential `GaloisForLFunctions.HTGeometry.LSeries_dirichletExp` (module `HTGeometry/DirichletConvolutionExponential.lean`, 258 lines).
  - `lake env lean` is clean.
  - `#print axioms` gives propext, Classical.choice, Quot.sound.
  - Both modules are wired into their umbrellas.
- [ ] 3 → 4

## Proof (as formalized)
1. **Dirichlet exponential.** `exp⋆f = Σ_k f^{⋆k}/k!` with `f = lam/log` (finite sums, since `f^{⋆k}` vanishes below `2^k`). It satisfies `L(exp⋆f, s) = exp L(f, s)` on `Re s > 1`, by an absolutely convergent double series (`LSeries_dirichletExp`).
2. **Atom product.** `P` is the corpus genus-one canonical product over `½ ± it_j` with multiplicity `m_j`. Its Mittag-Leffler form, grouped by pairs, is `P'/P = Φ + B` with `B = Σ m_j/(¼ + t_j²)` (`logDeriv_atomProduct`).
3. **Functional equation.** `Q = e^{−Bs}P` has `Q'/Q = Φ`, and `Φ` is odd under `s ↦ 1−s`. On the convex strip `|Im s| < 1`, which contains no atom, `Q(1−s)/Q(s)` has zero derivative and equals 1 at `s = ½`. The identity theorem gives `Q(1−s) = Q(s)` on ℂ (`atomQ_one_sub`).
4. **`G = KQ`.** `G(s) = s(s−1)Γ_ℝ(s)exp(Σ lam(n)n^{−s}/log n)` has `G'/G = Φ` on `Re s > 1` by the hypothesis (`bigG_eq_mul_atomQ`).
5. **Growth.** `Re Φ ≥ 0` on `Re s > ½` (each pair is `Re 1/(w−iτ) + Re 1/(w+iτ)`). So `σ ↦ |Ĝ(σ+iτ)|²` is monotone on `[½, 2]` (`norm_ghat_le_two`). Stirling at `σ = 2` gives `|Ĝ(2+iτ)| ≪ (|τ|+4)^N e^{−π|τ|/4}`.
6. **Hamburger.** `E = dslope(Ĝ − β·s(s−1)Γ_ℝ(s−1), 1)/s` with `β = Ĝ(1)/2` is holomorphic on `Re s > 0`, decays like `1/(1+t²)` on the strip, and has zero defect on the critical line. L228 with `g = 0` makes every coefficient of `exp⋆(lam/log)` equal to 1. So `exp(Σ lam(n)n^{−s}/log n) = ζ(s)`, and comparing logarithmic derivatives gives `lam = Λ` on `n ≥ 2`.
7. **RH.** `Ĝ = s(s−1)Λ(s)` (identity theorem from `Re s > 1`). A zero of ζ with `½ < Re ρ < 1` would make `Q(ρ) = 0`, but `Q` vanishes only at the atoms on the line.

## No-go closure
- **Killing mechanism:** exponentiating an integer-mass Herglotz function gives an entire function with Riemann's functional equation, and Hamburger's theorem applies.
- **Strongest positive survivor:** the theorem itself (formal, unconditional). Every atomic producer other than Λ needs a non-integer mass somewhere.
- **New insight:** the formal route needs only one-sided positivity (`Re Φ ≥ 0`, giving horizontal monotonicity) for the growth hypothesis of Hamburger's theorem. No a priori polynomial bound on the producer's zeta function is assumed.
- **Status:** Lean complete. Rational masses with denominator 2 (L222.1) need a Maass converse theorem. Denominators ≥ 3 are the open fake-ζᵏ door (L226/L231, problem P3T).

## Log
- 2026-10-01 — created at stage 3
