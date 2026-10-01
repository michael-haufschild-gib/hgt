# Zero-interpolating prime-blind majorant (ZIPM): the uniqueness scalar as an extremal problem

- **ID:** MC-188
- **Stage:** 1-in-progress (CONJECTURE; reduction proved on paper)
- **Type:** CONJECTURE
- **Source:** MC loop cycle 188. Follows MUST-619/621 (uniqueness of the nonnegative cone with vanishing local mass ⟺ `T ≥ 0`), MUST-622 (notch tests give only `T ≤ 0`) and MUST-624 (Weil LP duality).
- **Statement (ZIPM).** Let `P(t) = (1/2π)/(¼ + t²)` be the Poisson kernel of the critical line seen from `s = 1`. There is an admissible even test `F` (with convergent pole term) such that:
  - (i) `F̂ ≥ P` on `ℝ`;
  - (ii) `F(±log n) = 0` for every integer `n ≥ 2` (prime-blind);
  - (iii) `F̂ − P` vanishes at every zero of `Ξ`, real or not; for instance `F̂ − P = Ξ(t)² h(t)` with `h ≥ 0` on `ℝ`.

  Approximate ZIPM: for every `ε > 0` there is a prime-blind `F` with `F̂ ≥ P` and `Σ_ρ (F̂ − P)(γ_ρ) ≤ ε`.

## Reduction (paper)
Let `lam` be Weil-positive in Herglotz form, `Φ_lam = A + 1/(s−1) − Σ lam(n)n^{−s}`, with Poisson representation `Φ_lam(1) = ∫ P dμ_lam` and `μ_lam ≥ 0`.
1. `Φ_lam(1) ≤ ∫ F̂ dμ_lam`, by (i) and `μ_lam ≥ 0`.
2. `∫ F̂ dμ_lam = W_lam(F) = W_arch(F)`, because by (ii) every weight drops out.
3. `W_arch(F) = W_Λ(F) = Σ_ρ F̂(γ_ρ)`, by the explicit formula (unconditional, complex `γ` allowed). By (iii) this equals `Σ_ρ P(γ_ρ) = ξ'/ξ(1) = Φ_Λ(1)`.

Hence `T(lam) := Φ_Λ(1) − Φ_lam(1) ≥ 0` for **every** Weil-positive `lam`, of either sign. With MUST-619/621, every nonnegative `lam ∈ W` with vanishing local mass equals `Λ`. Approximate ZIPM gives the same conclusion, since `T ≥ −ε` for all `ε`.

## Why integrality enters exactly here
- Prime-blindness (ii) is a condition only at the integer logs.
- MUST-523's real-support producer `1_{(1,∞)}dx − e^{1/20000}δ_{e^{1/10000}}` has `T = γ − e^{−1/20000} ≈ −0.42 < 0`. The argument does not apply to it, because its support is not `{log n}`.
- So ZIPM is a precise form of "the RH content of uniqueness is integrality".

## Status of the conjecture
- **ZIPM ⟸ (W ⊆ {Λ}) + strong duality**, via MUST-624 extended to the harmonic functional. ZIPM is therefore not weaker than the uniqueness half; it is its archimedean dual.
- **Kill attempts.**
  - (a) An exact compactly supported `F` cannot interpolate `P` at all zeros, since an entire function of finite exponential type has zero density `≤ a/π` while the zeros have density `log t/2π`. So `F` must have unbounded support. The ansatz `F̂ = P + Ξ²h` has the right spectral structure.
  - (b) The finite-dimensional duality obstruction would be a nonnegative almost-periodic Dirichlet polynomial `Σ_{n≥2} μ_n cos(t log n)` without constant term. It must vanish, by mean value. So no finite obstruction exists to matching (ii) at finitely many `n`. The difficulty is matching all `n` while keeping (iii).
  - (c) The pole at `t = ±i/2` must cancel: `F̂ − P` needs residue `−res P` there. So `h` must have a pole with negative residue, `h = A − P` with `A ≥ P` entire. The construction is self-similar.
- **Verdict:** SURVIVES PRELIMINARY ATTACK, as an RH-uniqueness-strength extremal problem in harmonic analysis: majorants of the Poisson kernel interpolating on the zeta zeros, with Fourier transform vanishing on `{±log n}`.

## Lean
- The reduction needs the bridge `WeilPositiveFull lam ⇒` Herglotz form with Poisson representation. It is absent from the corpus: `HerglotzWeilPositive` is a hypothesis structure.
- The finite-level counterpart is MUST-624: `WeilDualBound` with `w(n) = −n^{−½}1_{n≤N}`.

## Log
- 2026-10-01: created (cycle 188).
- 2026-10-01 (cycles 189–190):
  - Corpus check. The Ξ-annihilated version of (iii) is the corpus' exposed-point machinery: `F̂ = Ξ²h` tests give `ℓ(lam − Λ) ≤ 0`, with equality only at `Λ`.
  - Duality. ZIPM is the harmonic-functional analogue of the exposed-ray criterion MUST-629: RH ⟺ the dual energy bound along the ray `ℝ₊·w`. ZIPM asks for the same along the Poisson ray `n ↦ n^{−1/2}`, restricted to the nonnegative, vanishing-local-mass cone.
  - Heuristic count. With t-band `H`, the prime-blind constraints at `log n` cap the useful x-support at `log(H/π)`. That leaves `(2H/π)(log(H/π) − ½)` degrees of freedom against `(2H/π)(log(H/2π) − 1)` double-interpolation conditions at the zeros: slack `(2H/π)(log 2 + ½)`. ZIPM is supercritical by a constant factor, not at critical density.
