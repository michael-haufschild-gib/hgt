# Band–far cross of the complete Weil matrix below the eighth root

- **ID:** band-far-cross-below-one-eighth
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** T2 of `off-pole-nonratio-cross-and-one-eighth-weil-positivity.md`
- **Statement:** For `α < 1/8`, eventually, uniformly in `1 ≤ c ≤ (log N)^α`, for a band
  `u = Σ_{m≤R} a_m v_m ∈ V_R ∩ V_Q^⊥` (`R = ⌊N^{θ₁}⌋`, `Q = ⌊(log N)^q⌋`, `q > 2α`) and
  `w ∈ V_R^⊥`:
  `2|⟨W u, w⟩| ≤ (1/32) E_mass(a) + (1/4)‖u‖² + (k/32) P_w + (b k/(32 c⁷)) S_w`.

## Decomposition of the nonprime channels
`W = (ℓ+κ)I − fullPrime + C_α − Sep + PoleErr + Overlap − (Up + Down)`, `C_α = (α/N)(Π − ω)`,
`Overlap = K₁ + K₂ₐ + log j·K₂ᵦ` on near pairs with `K₁ = (α/N)ω|_near`, and
`Down u = K₂ᵦ(log j·u) − K₂ᵦ v_jet + Ext` (`Σ_{k|n} Λ(k)c_m(n/k) = log n·c_m(n) − jet_m(n)`). Hence
`C_α u + Overlap u − Down u = (α/N)Π u − (α/N)ω_far u + K₂ₐ u + K₂ᵦ v_jet − Ext`, and
`⟨(α/N)Π u, w⟩ = 0` for `u, w ⊥ v_1`.

Write `v_jet = Σ_k J_k v_k`, `J_k = Σ_m a_m w(m,k) √(φ(k)/φ(m))`,
`w(m,k) = [k=m] log m + Λ(m/k)`, and `u = Σ_{m>Q} a_m v_m + Σ_{k≤Q} a_k v_k`.

1. **Coherent pole pair.** Write `u = a_1 v_1 + ũ` (`ũ` has conductors `≥ 2`). Since `u ⊥ v_1`,
   `Π u = 0`, so `Π ũ = −a_1 Π v_1` and, with `Σ_{n≤N} c_m(n)/n = −Λ(m) + O(σ(m)/N)`,
   `(α/N)Π ũ = −J_1 (α n/N) v_1 + (α/N)(1/√n)⟨√j, ũ⟩ + O(Σ|a_m| σ(m)/(N√ℓ))`.
   The jet gives `K₂ᵦ(J_1 v_1) = J_1 m(n) v_1`, `m(n) = Σ_{h≠0} A(hN/(nc))` (row mass of the near
   Gram kernel), `m(n) = αn/N − 1 + O((nc/N)^{−p})` for `nc/N ≥ 1` and `0` below. Hence the
   coherent sum is `J_1 (m(n) − αn/N) v_1`: `−J_1 v_1` on the top rows (orthogonal to `w`) and a
   deep-row remainder of norm² `O(J_1² log c/ℓ)` paid by the prefix reserve `≍ log R`.
   `a_1 W v_1 = a_1 E_1 v_1 + a_1 r_1` with `‖r_1‖² ≲ c² ℓ^ε/ℓ` (corpus residual) costs
   `c⁹ θ² ℓ^ε/ℓ²` against the top reserve.
2. **Jet, conductors `k ≥ 2`.** `Γ = I + K₂ᵦ` is the atomic Gram matrix (PSD, `‖Γ‖ ≤ 1+2ec`), so
   `‖K₂ᵦ x‖² ≤ (‖Γ‖ − 2)⟨Γx, x⟩ + ‖x‖²` and it suffices that `⟨K₂ᵦ x, x⟩ ≤ δ‖x_top‖²` with
   `δ = c^{o(1)}`. Per conductor `k` the diagonal part is `Σ_h (c_k(h)/φ(k)) W(h)`, with `W` the
   linearized near weight (mass `O(1 + log c)` per shift): for `k ≤ 2c`, Möbius over the progressions
   `t | h` gives `O(σ(k)/φ(k))`; for `k > 2c`, `|c_k(h)|/φ(k) ≤ 1/φ(k/(k,h))` gives
   `O((c/k) τ(k) log log k)`. Cross terms `k ≠ l` are shifted-mode oscillations with partial sums
   `≤ 4R³` (`shifted_mode_osc_Ico_le`), total `O(c³R⁴/N)`. Cost `c^{8+o(1)}(1+log R)(1+log c)G/ℓ²`.
3. **Center far collar, high conductors.** Near multiplier
   `M_D(ξ) = Σ_{h≤D} cos(2πhξ)/h`, `|M_D(r/m)| ≤ 3 + log(m/(2 min(r, m−r)))`;
   `Σ_{n<M}(κ∗c_m)(n)² = M Σ_{(r,m)=1} M_D(r/m)² ≤ C M m`; distinct conductors orthogonal over
   `lcm` periods. Cost `α² (m/φ(m))/ℓ` per unit mass, i.e. `c⁹ log log R/ℓ²`.
4. **Low conductors `2 ≤ k ≤ Q`:** coefficients `a_k = O(J_k/ℓ)`, collar multiplier `≤ 3 + log k`.
5. **`K₂ₐ`, `Ext`, `Sep`:** corpus bounds (`c⁴/ℓ`, `c³R²ℓ/N`, `c⁴/ℓ`) suffice below `1/8`.
6. **Upward:** prefix rows pay with `k P_w`; top rows read only `u|_S`.

## Lean modules
- `CompletedArithmeticForms.TheNearCollarCostsTheMeanLogarithmicMultiplier` — step 3 core:
  `|M_D(θ)| ≤ 3 + log(1/|sin(θ/2)|)`, collar weight `≤ 130 k/φ(k)` (`k ≥ 2`), smoothed packets
  over a range, `sum_collarRowNear_sq_le_sharp`. The collar decomposition in
  `ConductorBandPrimeAndCenterBounds` (`collarRow_eq_sum_three`, `SumHalf`/`Far` bounds) is public.
- `CriticalArithmeticCorrelationTheory.TheNearGramFormOfAPacketCostsItsDivisorMean` — step 2 core:
  `sum_nearGram_sq_le_gram` (`‖K₂ᵦ y‖² ≤ (2ec − 1)⟨Γy, y⟩ + ‖y‖²`), the Möbius/Abel mean
  `abs_sum_ramanujanLagCoefficient_mul_le`, `exists_nearGram_packet_form_le` (packets with `a 1 = 0`).
  The mid-band machinery in `SharpenedMidBandAndCrossBounds` (`midBand*`, `shifted_mode_osc_Ico_le`,
  `sum_nearBand_sq_le_of_mem_conductorSubspace`) is public.
- `SharpenedMidBandAndCrossBounds.exists_overlap_sub_downward_sub_jet_sq_le` —
  `‖(Overlap − Down)u − K₂ᵦ v_jet‖² ≤ C(c⁴(1 + log c)/log N + c³R²log N/N)‖u‖²`.
- `CriticalArithmeticCorrelationTheory.TheReducedDivisorJetCostsItsDivisorMean` — step 2:
  `reducedDivisorJet` (`v_jet` without `k = 1`), `v_jet = v_jet' + J₁v₁`;
  `exists_nearGram_reducedDivisorJet_sq_le_weighted`:
  `‖K₂ᵦ v_jet'‖² ≤ C c((1 + log c)Sg/log N + c⁵/N + c³R⁴/(N log N))(1 + log R)Σ(1 + log m)a_m²`,
  `Sg ≥ σ(m)/φ(m)` on `[2, R]`.
- `CriticalArithmeticCorrelationTheory.TheJetPoleComponentCancelsThePole` — step 1:
  `exists_coherentPolePair_sq_le`: `(P⟨Πũ, w⟩ + J₁⟨K₂ᵦ v₁, w⟩)² ≤
  C((1 + log R)(1 + log c)/log N · G + c²R⁵/(N² log N) · A)‖w‖²` (`P` exact pole coefficient,
  `ũ` the band without `v₁`, `w ⊥ V_R`). Uses the exact pole `P = a₋a₊/G` (center pole part plus
  pole error), so no `α/N` approximation enters.
- `CriticalArithmeticCorrelationTheory.TheBandFarCrossBelowTheEighthRoot` — assembly:
  `band_far_cross_eq` (channel identity for `u = a₁v₁ + ũ`); `collar_reducedBand_sq_le`
  (`‖C ũ‖² ≤ (24 + 780 Sg₁ + 72R^{15}/N)/log N · ‖u‖²`, `Sg₁ ≥ m/φ(m)`);
  `exists_div_totient_le_loglog` (`m/φ(m) ≤ K(1 + log(1 + log m))`), `sigma_div_totient_le_sq`;
  `exists_upwardPrimeVector_top_sq_le` (rows `n > M`: `O(c²(N/M)(1 + log c)/log N)‖u‖²`);
  `exists_band_far_cross_le_channels` (every channel paid by free parameters `s₁, t₁, s₂, t₂, γ`;
  six non-prime channels share `bandFarChannelBudget`, pole mode through `ρ ≥ ‖r₁‖²`).
  `#print axioms`: `propext, Classical.choice, Quot.sound`.

- `CriticalArithmeticCorrelationTheory.TheEighthRootComplementKeepsItsBlockReserves` — the statement
  above: `exists_band_far_cross_le_reserve_shape` (`s = k/128`, `t = bk/(128c⁷)`, `γ = bk/(32c⁷)`),
  scalar budgets `budgetE_le`, `budgetU_le` from `c⁸(1 + log c)Sg²/L ≤ σ` (`8α + 4ν ≤ 1`),
  `exists_band_far_cross_le_at_cutoff` at `R ∈ {R₀, R₁}`, `k = θ₁L/(2D)`, `ρ` from
  `exists_tiltedUnitSpline_quadratic_conductor_residual_variable_rate` at `m = 1`.

## Status
Steps 1–6 and the specialization to the statement are in Lean.

