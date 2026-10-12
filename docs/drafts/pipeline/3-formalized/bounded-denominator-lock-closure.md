# Bounded-denominator AP locks force RH

- **ID:** bounded-denominator-lock-closure
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Opus loop rows 2100–2105 (`rh-goal-loop-opus-2026-09-29.md`); STATUS MUST-1322, MUST-1327
- **Statement:** a Herglotz producer with lower-line lock `G(1−s) = N^{s−½}(Σ_k P(k)k^{−(s−½)})G(s)`, `Σ|P(k)| < ∞`, forces RH.

## Goal
This closes the bounded-denominator part of the open almost-periodic class in the uniqueness half (U) of the HF route. The class has a two-sided rational spectrum `log(k/N)` and was the open case left after MUST-1246/1247/1310/1315. Not an RH proof by itself: it removes one class of twins.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure; MUST-1322 done in Lean
- [x] 1 → 2  fully-proven: paper proof below
- [x] 2 → 3  formalized: `bounded_denominator_lock_riemannHypothesis`, `lake build` green per module, standard axioms, no heartbeat overrides
- [ ] 3 → 4  not pursued

## Proof
Notation: `a = exp⋆(lam/log)`, so `F(s) = Σ a(n)n^{−s} = exp(Σ ℓ(n)n^{−s})` with `ℓ = lam/log`, `Σ|ℓ(n)|n^{−σ} < ∞` for `σ > 1`.

1. **Periodicity [L, MUST-1322].** `a(n) = Ψ(n mod N)`, `Ψ : ℤ/N → ℂ`.
2. **Twist.** For a completely multiplicative `f` with `|f(n)| ≤ n^{−σ}`, `σ > 1`, twisting commutes with the Dirichlet exponential: `exp⋆(ℓf) = a·f`. Hence `Σ_n a(n)f(n) = exp(Σ_n ℓ(n)f(n)) ≠ 0`.
3. **Decomposition.** For `m` `N`-smooth put `α_χ(m) = φ(N)^{−1} Σ_{b unit} Ψ(mb) χ̄(b)`, and `α_χ = 0` off `N`-smooth numbers. Then `Ψ = Σ_χ α_χ ⋆ χ` on `n ≥ 1`. Indeed `n = mr` uniquely with `m` `N`-smooth and `(r, N) = 1`, and orthogonality gives `Σ_χ α_χ(m)χ(r) = Ψ(mr)`. So `Σ_n Ψ(n)f(n) = Σ_χ (Σ_m α_χ(m)f(m)) (Σ_r χ(r)f(r))`.
4. **Choice at `p | N`.** Fix a real `s₀ > 1` so large that each `A_χ := Σ_m α_χ(m)m^{−s₀}` is nonzero unless `α_χ ≡ 0`. A nonzero absolutely convergent Dirichlet series is nonzero for all large real `s`. Put `f(p) = p^{−s₀}` for `p | N`.
5. **Zero construction.** Suppose `χ₁ ≠ χ₂` with `A_{χ₁}, A_{χ₂} ≠ 0`. With `⟨χ, u⟩ = Σ_a χ(a)u_a` and the dual vectors `v^χ_a = χ̄(a)/φ(N)` (`⟨ψ, v^χ⟩ = δ_{ψχ}`), take `u⁰ = Σ_χ β_χ v^χ` with:
   - `β_{χ₁} = 0`;
   - `β_{χ₂} = log(−A_{χ₁}/A_{χ₂})`;
   - `β_χ = −R'` otherwise.

   Then `Θ(u⁰ + λ v^{χ₂}) = A_{χ₁}(1 − e^λ) + O(e^{−R'})`, where `Θ(u) = Σ_χ A_χ e^{⟨χ,u⟩}`. Dirichlet divergence `Σ_{p≡a} 1/p = ∞` gives finite sets `S_a` of primes `≡ a` and `σ > 1` with `R_a = Σ_{S_a} p^{−σ}` as large as needed. Put `z_p(λ) = (u⁰_a + λ v_a) p^{−σ}/R_a` for `p ∈ S_a`. Then `log Π_{p∈S}(1 − χ(p)z_p)^{−1} = ⟨χ, u⁰ + λv⟩ + O(K²/min R_a)`. Rouché on `|λ| = ½` gives `λ*` with `Σ_χ A_χ Π_{p∈S}(1 − χ(p)z_p(λ*))^{−1} = 0` and `|z_p| ≤ p^{−σ}`. This contradicts step 2, applied to `f(p) = z_p(λ*)` on `S`, `p^{−s₀}` on `p | N`, `0` elsewhere.
6. **Single character.** So exactly one `χ₁` has `α_{χ₁} ≢ 0` (`Ψ(1) = 1` excludes none). `L(s,Ψ) = A(s)L(s,χ₁)` with `A = Σ_m α_{χ₁}(m)m^{−s}` holomorphic on `Re s > 0`.
7. **Principal.** `G` is zero-free on `Re s > ½`, so `G(1) ≠ 0`, so `F` has a pole at `1`, so `χ₁ = χ₀`.
8. **RH.** On `Re s > ½`, `s ≠ 1`: `G(s) = s(s−1)Γ_ℝ(s)A(s)Π_{p|N}(1 − p^{−s})ζ(s)`, by the identity theorem from `σ > 1`. A zero of `ζ` with `½ < Re ρ < 1` would be a zero of `G`. So `ζ` has no zero right of `½`, and RH follows by the functional equation.

The mean-motion law (MUST-1315) is needed only for the stronger `lam = Λ`, which is not required for RH.

## Lean
| Step | Module | Declaration |
|---|---|---|
| 1 | `RHTower/WeilBoundedDenominatorLockConvolution`, `RHTower/WeilBoundedDenominatorLockPeriodicity` | `sqrtConv_periodic`, `bounded_denominator_lock_periodic` (MUST-1322) |
| 2 | `HTGeometry/DirichletExpMultiplicativeTwist` | `dirichletExp_mul_twist`, `tsum_dirichletExp_twist_ne_zero` |
| 3 | `HTGeometry/PeriodicCharacterDecomposition` | `exists_smooth_coprime_split`, `sum_charSection_mul`, `periodic_twist_eq_sum_convolution` |
| 5 | `HTGeometry/PrimeProgressionReciprocalDivergence`, `RHTower/CharacterProductZeroPlanting` | `not_summable_primeRecipClass`, `exists_charProduct_zero` |
| 4, 6 | `RHTower/PeriodicExpProducerSingleCharacter` | `periodic_exp_single_character` |
| 7, 8 | `RHTower/WeilBoundedDenominatorLockRH` | `bounded_denominator_lock_riemannHypothesis` (MUST-1327) |

## Log
- 2026-10-12 — created; MUST-1322 (step 1) in Lean.
- 2026-10-12 — steps 2–8 formalized (MUST-1327); moved to 3-formalized.
