# CHMD loop step 5 (2026-10-16): small-scale positivity of all first-order Toeplitz packets (MUST-1533)

Module `formal/GaloisForLFunctions/RHTower/CHMDSmallScalePacketPositivityFirstOrder.lean`
(namespace `RHTower.CHMDSmallScale`, imports the energy module, wired in `RHTower.lean` after
`CHMDKleinGordonEnergyPositivityAndOriginMaximum`, standard axioms, `lake build --old` green).

Statement (`exists_scaledForm_nonneg`): for every finite packet `(t, c) : Fin N → ℝ` with
`Σ cᵢ ≠ 0` or `Σ cᵢ tᵢ ≠ 0` there is `λ₀ > 0` with
`scaledForm t c λ := Σ_{i,j} cᵢ cⱼ φ_Λ(λ(tⱼ − tᵢ)) ≥ 0` for all `0 ≤ λ ≤ λ₀`, where
`φ_Λ = chmdWave = cosineShiftFn Λ sechHalf`.

Mechanism:
- `re_mul_one_sub_cos_expansion`: `|Re(w(1 − cos x)) − Re(w x²)/2| ≤ 4‖w‖‖x‖⁴` for `|Im x| ≤ ¼`
  (Taylor regime `‖x‖ ≤ 1` via `Complex.cos_bound`; crude regime via `‖cos x‖ ≤ e^{1/4} ≤ 2`).
- `sum_sum_mul_sq_sub`: `Σ cᵢcⱼ(tⱼ−tᵢ)² = 2(Σ cᵢ)(Σ cᵢtᵢ²) − 2(Σ cᵢtᵢ)²`.
- `packetMode_ge` / `scaledForm_ge_of_sum_eq_zero`: for `Σ cᵢ = 0`, `λ·2T ≤ ½` (`T = Σ|tᵢ|`):
  `scaledForm ≥ λ²(Σ cᵢtᵢ)² M₁ − 4λ⁴ D Q`, `M₁ = kgEnergyMoment > 0`, `Q = kgQuarticMass`,
  `D = packetQuartic = Σ|cᵢ||cⱼ|(tⱼ−tᵢ)⁴`.
- `Σ cᵢ ≠ 0`: continuity at `0` with `scaledForm t c 0 = (Σ cᵢ)² φ_Λ(0)`, `φ_Λ(0) > 0`.
- Radius: `λ₀ = min(1/(4T+4), √((Σ cᵢtᵢ)² M₁ / (4(D+1)(Q+1))))`.

Law learned: the `k`-th zero moment `M_k = Σ m_ρ Re(ρ_ρ^{2k} w_ρ)` governs the packets degenerate
to order `k` (`Σ cᵢ tᵢ^j = 0` for `j < k`). `M₁ > 0` is strip-sector positivity of
`(z²+2)sech²(z/2)`. Next target: `M₂ > 0` ⟸ `Re((z²+2)² sech²(z/2)) > 0` on `|Im z| < ½`
(open). The sector mechanism must stop at finite `k` since `arg((z²+2)^k)` leaves `(−π/2, π/2)`
on the strip; the exact stopping order is the next question. Large scales remain Wall 1.

Lean notes: `Summable.tsum_finsetSum` is the name for `∑' b, ∑ i ∈ s, f i b = ∑ i ∈ s, ∑' b, f i b`
(`tsum_sum`, `tsum_finsetSum` do not exist); `summable_sum` needs the expected type written out;
`continuous_finsetSum`; `rw [mul_sub]` matched `lam * (t j − t i)` first — name the factor
(`mul_sub w`); after `set k := kgFreq ρ with hk`, new facts about `kgFreq ρ` must be restated for
`k` (`rw [hk]`); `field_simp` alone closed the `S*M/(4(D+1)(Q+1))` rearrangement (`ring` after it
errors with "no goals").

## Loop step 6 (killed, 2026-10-16): all moments M_k > 0
Sector works only for k ≤ 4; for large k the moment is dominated by zeros at height ≈ 2k whose angle
2k·b/a ≈ b < π/2 is automatically positive, with negative zeros (height < 2k/π) suppressed by
(π/e)^{−2k}; so every moment is blind (TH heat-Hankel detection-horizon analogue). Do not build M₂.
Positive survivor (blind): exact leading law at degeneracy order d:
scaledForm(λ) = M_d λ^{2d} (Σ cᵢtᵢ^d)²/(d!)² + O(λ^{2d+2}); all-orders small-scale Bochner ⟺ M_d ≥ 0 ∀d
⟺ v ↦ φ_Λ(iv) absolutely monotone on [0,1). Route law: zero-side unconditional positivity = sector or
density domination = blind; non-blind sign enters only from the prime side (Wall 1).
Next structural candidates (identities, not wall passes): Cramér-type continuation of Φ(z)=Σ m w cos(zρ)
with poles at z = ±log n ± i; light-cone/Bessel decomposition of the prime kernel K_y.
