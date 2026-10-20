# The size law (`S(T)` unbounded) and the Mehler–Fock / Bochner–Godement dictionary

- **ID:** size-law-mehler-fock-2026-10-20
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) ×2
- **Source:** walls ledger, Wall 14 (paper item CANNOT-549) and Wall 13 (producer loop row 241)
- **Statement:** (A) `S(T) = N(T) − M(T)` is unbounded. (B) A continuous compactly supported
  point-pair kernel `k(u(z,w))` on `ℍ` is positive definite iff its Mehler–Fock (Selberg) transform
  is nonnegative on the critical line iff its Abel transform lies in the Bochner cone.

## Goal
Remove the two paper-only items of the walls ledger. (A) excludes finite-rank prime modifications of
the archimedean reference (bounded spectral shift); the corpus has only non-integrability. (B) is the
dictionary behind the cone-mismatch wall: the Bochner cone `{Ĝ ≥ 0}` on `ℝ` is identified, through
the Abel transform, with positive-definite zonal kernels on `ℍ`.

## Gates
- [x] 0 → 1  in-progress: both statements well-posed, unconditional, proof architectures below
- [ ] 1 → 2  fully-proven: paper proofs complete (below)
- [ ] 2 → 3  formalized: Lean theorems, `lake env lean` clean, axioms standard, umbrellas wired
- [ ] 3 → 4  not pursued (no stage 4)

## (A) Paper proof: `S(T)` is unbounded

Notation. `Φ(u) = bump(u)` (smooth, even, `0 ≤ Φ ≤ 1`, support `[−1,1]`), `Φ_ℓ(u) = Φ(u/ℓ)`
(`cb ℓ 0`), `K = Φ_ℓ ⋆ Φ_ℓ` (`EF.weilTest`), `ψ(y) = |Φ̂_ℓ(y)|² = K̂(y)` (`psi ℓ 0`),
`X = e^{2ℓ}`, `N = ⌊X⌋`. For a height `T` put `ξ = −T/2π`, so `S_ξ Φ_ℓ` is the window at `T`.

1. **Explicit formula** (SRT `zetaZeroConfig_W_heightShift_eq_sub`, Zeta23 EF, unconditional):
   `Σ_ρ m_ρ K̂(γ_ρ − T) = A(T) − Π(T)` with `A(T) = pole(T) + ∫ ψ(τ − T) μ(τ) dτ` and
   `Π(T) = primePolynomial Φ_ℓ N ξ`.
2. **Off-line correction.** For `ρ = ½ + δ + it`: `Re K̂(t − T − iδ) − ψ(t − T) = Re ĝ_δ(t − T)`
   with `g_δ = K·(cosh(δ·) − 1)` (the `sinh` part is odd, its transform imaginary). Hence
   `|·| ≤ C_ℓ δ² (1 + |t − T|)^{−2}` (`norm_paperFT_le_decay`).
3. **Zero sums.** Local count `N(t, t+1) ≤ A₀ log(|t|+3)` gives
   `Σ_ρ m (1+|Im ρ − T|)^{−2} ≤ C log(T+3)` and the far part `≤ C log(T+3)/W`.
4. **Good heights.** Threshold `v = (log U)^{−2/3}`, radius `W = (log U)²`. Zeros of depth `≥ v`
   in `(U/4, U/2)` number `o(U/W)` (`exists_windowZeros_count_le`), so heights within `W` of one
   have measure `o(U)`. At a good height `T ∈ [U/4, U/2]`:
   `|Corr(T)| ≤ C_ℓ(v² log U + log U/W) → 0`.
5. **Abel summation.** `Σ_{Im ρ > 1} m ψ(Im ρ − T) = −∫_1^∞ ψ'(t − T)(N(t) − N(1)) dt`; integrate
   `M` by parts; Stirling `|μ(t) − log(t/2π)/2π| ≤ C/t²` and `M'(t) = log(t/2π)/2π`. Hence
   `Re Π(T) = ∫_1^∞ ψ'(t − T) S(t) dt − Corr(T) + o(1)` along good heights.
6. **Bounded `S` caps `Π`.** If `|S| ≤ B` on `[t₀, ∞)` then `Re Π(T) ≤ B‖ψ'‖₁ + o(1)` along good
   heights, with `‖ψ'‖₁ ≤ C ℓ²`.
7. **Kronecker.** `{phases : Re Π > G}` is open and nonempty for `G < primeOnlyEnvelope −
   primePowerTailEnvelope` (SRT); the prime flow visits it with positive lower density
   (`exists_pos_density_preimage_primeFlow`), hence with positive measure in `[U/4, U/2]` for
   arbitrarily large `U`, which beats the `o(U)` bad set.
8. **Growth.** `primeOnlyEnvelope ≥ c ℓ Σ_{p ≤ e^{ℓ/2}} log p/√p ≫ ℓ e^{ℓ/4}`, tail `≤ C ℓ²`, so
   `G(ℓ) > B ‖ψ'‖₁` for large `ℓ`: contradiction.

## (B) Paper proof: the Mehler–Fock / Bochner–Godement dictionary

Objects: continuous profile `k` with `KernelSupport k R`; kernel `k(u(z,w))`; Selberg transform
`h_k(s) = ∫_ℍ k(u(i,w)) (Im w)^s dμ(w)` (corpus `selbergTransform`); Abel transform
`𝒜k(v) = ∫_ℝ k(η²/4 + sinh²(v/2)) dη` (even, continuous, compact support).

1. **Horocyclic slice.** `∫_ℝ k(u(x+iy, x'+iy')) dx = √(yy') 𝒜k(log y − log y')`
   (substitute `x − x' = √(yy') η`).
2. **Mehler–Fock = Fourier ∘ Abel.** `h_k(½ + iτ) = ∫ 𝒜k(v) e^{iτv} dv` (slice at `w = i`).
3. **Necessity.** PD on `ℍ` ⟹ test with `g(z) = χ_X(x) b(log y) √y`, `X → ∞`: the slice gives
   `∫∫ 𝒜k(a − b) b(a) b̄(b) ≥ 0` (Bochner cone) ⟹ Fejér ⟹ `h_k(½ + iτ) ≥ 0`.
4. **Convolution algebra.** `(κ₁ ⋆ κ₂)` profile via SL(2,ℝ)-invariance; the slice identity gives
   `𝒜(κ₁ ⋆ κ₂) = 𝒜κ₁ ∗ 𝒜κ₂` (Fubini only); `κ ⋆ κ` is PD for real `κ`.
5. **Inverse Abel.** `κ(w) = −(1/2π)∫_w^∞ q'(c)(c − w)^{−1/2} dc` inverts `𝒜` on `C²_c` even
   profiles (Beta integral); `𝒜` is injective on continuous compactly supported profiles.
6. **Sufficiency.** Regularize `k_ε = ρ_ε ⋆ k ⋆ ρ_ε` (`𝒜k_ε = P ∗ Q ∗ P ∈ C²_c`, transform
   `≥ 0`). Fourier inversion `Q_ε = (1/2π)∫ Q̂_ε cos`. With `f_{τ,T} = cos(τ·) ψ(·/T)`:
   `(1/2πN_T)∫ Q̂_ε(τ) f_{τ,T} ∗ f_{τ,T} dτ = (1/2N_T)∫ψ_Tψ_T[Q_ε(v) + Q_ε(v+2a)]da → Q_ε/2`
   in `C²`, each `f ∗ f = 𝒜(κ ⋆ κ)` PD; pass to the limit through the inverse Abel bound; then
   `ε → 0`.

## Log
- 2026-10-20 — created; corpus survey done (Zeta23 EF/RvM/Stirling, SRT localized form and
  Kronecker realization, prime-flow density, zero-density window count; ℍ point-pair invariant,
  SL(2,ℝ)-invariant measure, Selberg's theorem). Building (A) first.
