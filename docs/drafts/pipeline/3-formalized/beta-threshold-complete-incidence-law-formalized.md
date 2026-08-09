# Beta-threshold complete-incidence law — formalized closure

- **ID:** `beta-threshold-complete-incidence-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./beta-threshold-complete-incidence-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [BRIDGE]`

## Lean modules

- `GaloisForLFunctions.HTGeometry.BinomialTailBetaThreshold` (new) — the polynomial layer:
  Hoeffding's lemma for a two-point variable, the binomial head/tail Chernoff bounds, the
  threshold sandwich, the derivative telescoping and the beta-density normalization.
- `GaloisForLFunctions.HTGeometry.BetaThresholdIncidenceLaw` (new) — the measure layer: the
  incidence action, the sandwich `(6)`–`(7)`, return excision `(16)`–`(18)`, the exact coarea
  identities `(12)` and `(17)`, the trace-distance corollary `(24)` and the monomial separation
  `(25)`–`(26)`.
- `GaloisForLFunctions.HTGeometry.BoundedReplicaThresholdProjector` (new) — the operator layer:
  the literal replica outcome projections `(19)`, their algebra `(20)`, the expectation identity
  `(21)` and the occupied-target maximum `(22)`.

All three are imported by the umbrella `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

### Layer 1 — binomial tail polynomial, monotonicity, Hoeffding sandwich

1. `one_sub_add_mul_exp_le_exp` — Hoeffding's lemma for a Bernoulli variable in uncentred form,
   `1 - x + x e^t ≤ exp(t x + t²/8)` for `x ∈ [0,1]` and every real `t`.  Obtained from mathlib's
   `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` applied to the two-point measure
   `Ber(1-x, -x, x)` on `ℝ`; the sub-Gaussian constant `((b-a)/2)² = 1/4` gives the `t²/8`.
2. `binomialTerm`, `binomialHead`, `binomialTail` — definition `(3)` and its complement; the
   defining decomposition is `binomialHead_add_binomialTail`, the full sum
   `sum_binomialTerm_range` is the binomial theorem.
3. `sum_binomialTerm_mul_exp` / `sum_binomialTerm_mul_exp_le` — the exponential moment of the
   binomial weights is `(x e^c + 1 - x)^r`, hence at most `exp(r (c x + c²/8))`.
4. `binomialTail_le_exp_shift`, `binomialHead_le_exp_shift` — the two Chernoff shifts.
5. `binomialTail_le_exp` — the upper tail bound: `k ≥ r x + r s ⟹ B_{r,k}(x) ≤ exp(-2 r s²)`,
   with the optimal shift `λ = 4(k - r x)/r`.
6. `binomialHead_le_exp` — the lower tail bound: `k - 1 + r s ≤ r x ⟹ head ≤ exp(-2 r s²)`.
7. `replicaThreshold r a b = ⌈r (a+b)/2⌉` — the count `k` of `(2)`.
8. `binomialTail_replicaThreshold_le` — inequality `(10)` after integration of the threshold:
   `x ≤ b ⟹ B_{r,k}(x) ≤ exp(-r δ²/2)`.
9. `one_sub_le_binomialTail_replicaThreshold` — inequality `(9)`:
   `x ≥ a ⟹ B_{r,k}(x) ≥ 1 - exp(-r δ²/2)`.  The ceiling strictness `⌈y⌉ < y + 1` is exactly what
   turns the head condition `k - 1 ≤ r x - r δ/2` into a consequence of `x ≥ a`.
10. `measure_le_two_mul_binomialTail` — the pointwise form of `(7)`, for `r ≥ 2 log 2 / δ²`.

### Layer 2 — derivative telescoping and beta-density normalization

11. `cast_choose_absorb_left`, `cast_choose_absorb_right` — the two identities `(13)`,
    `j C(r,j) = r C(r-1,j-1)` and `(r-j) C(r,j) = r C(r-1,j)`, the second from Pascal.
12. `betaKernel r k u = r C(r-1,k-1) u^(k-1) (1-u)^(r-k)` — the `Beta(k, r-k+1)` density.
13. `hasDerivAt_binomialTail` — **equation `(11)`**: `B'_{r,k} = betaKernel r k` for `1 ≤ k ≤ r`.
    Each term differentiates to `r (g j - g (j+1))` with
    `g j = C(r-1,j-1) x^(j-1) (1-x)^(r-j)`; the sum telescopes over `Icc k r` and the boundary term
    `g (r+1)` vanishes because `C(r-1, r) = 0`.
14. `binomialTail_eq_intervalIntegral` — equation `(14)`, by the fundamental theorem of calculus
    together with `binomialTail_zero_eq_zero`.
15. `intervalIntegral_betaKernel_eq_one` — the beta density has unit mass, from
    `binomialTail_one_eq_one`.
16. `binomialTail_monotoneOn` — monotonicity of `B_{r,k}` on `[0,1]`, from the nonnegativity of
    the density (with the two degenerate cases `k = 0` and `k > r` handled separately).

### Layer 3 — the incidence action, its sandwich and the coarea law

17. `incidenceAction μ r k Y = ∫ B_{r,k}(Y ω) dμ` — definition `(4)`;
    `restrictedIncidenceAction μ r k Y R = ∫_{Ω∖R} B_{r,k}(Y ω) dμ` — definition `(15)`.
18. `integrable_binomialTail_comp` — the integrand is bounded in `[0,1]`, hence integrable on any
    finite measure.
19. `incidenceAction_le` — the right half of `(16)` for an arbitrary finite measure:
    `𝔍 ≤ μ{Y ≥ b} + η μ(Ω)`.
20. `le_incidenceAction` — the left half of `(16)`: `(1-η) μ{Y ≥ a} ≤ 𝔍`.
21. `incidenceAction_sandwich` — **equation `(6)`**, the probability-measure specialization; and
    `measure_le_two_mul_incidenceAction` — **equation `(7)`**.
22. `measure_le_return_add_restrictedIncidenceAction` — **equation `(18)`**: return mass is paid
    once, with coefficient one; the restricted statement is literally the general one applied to
    `μ.restrict Rᶜ`, so no mixed `R × Rᶜ` term can appear.
23. `incidenceAction_eq_betaCoarea` — **equation `(12)`**, the exact beta-threshold coarea law
    `𝔍 = ∫₀¹ betaKernel r k u · μ{Y ≥ u} du`.  The inner identity rewrites `B_{r,k}(Y ω)` as the
    integral of the density against the indicator of `{u ≤ Y ω}`; the interchange is Fubini for a
    globally bounded jointly measurable integrand on `μ ⊗ (volume ↾ Ioc 0 1)`.
24. `restrictedIncidenceAction_eq_betaCoarea` — **equation `(17)`**: return excision commutes
    exactly with the beta decomposition.
25. `incidenceAction_traceDistance_sandwich` — **equation `(24)`**, the pure-state trace-distance
    parametrization `a = 1 - ε₋²`, `b = 1 - ε₊²`, `δ = ε₊² - ε₋²`.
26. `incidenceAction_indicator` — **equation `(25)`**: for a two-valued observable the action is
    exactly the source probability, for every admissible `k`.
27. `monomial_reporter_indicator`, `monomial_reporter_eq_pow_mul_incidenceAction` —
    **equation `(26)`** and the exact separation factor: the monomial Markov reporter is
    `a^{-r}` times the bounded action on the same observable.

### Layer 4 — the literal bounded replica projector

28. `quadForm M w = star w ⬝ᵥ M *ᵥ w`, with `quadForm_eq_sum`, `quadForm_add`, `quadForm_sum` and
    the Gram identity `quadForm_conjTranspose_mul`, which realizes `⟨w, Mᴴ M w⟩` as a sum of
    squared moduli and is the source of every positivity statement below.
29. `replicaVector r v` and `replicaOp r A` — the `r`-fold tensor power of a vector and of a
    family of operators, written in the product basis indexed by `Fin r → n`.
    `replicaOp_mul` and `replicaOp_conjTranspose` show the tensor product multiplies and
    transposes slotwise; `replicaOp_eq_zero_of_factor` kills a product with a zero slot.
30. `quadForm_replicaOp` — the product factorization
    `⟨v^{⊗r}, (⊗ A_i) v^{⊗r}⟩ = ∏_i ⟨v, A_i v⟩`, by two applications of `Finset.prod_univ_sum`.
31. `rankOne z` — `P_z`; `rankOne_conjTranspose`, `rankOne_mul_rankOne` (for unit `z`),
    `quadForm_rankOne` (`⟨v, P_z v⟩ = |⟨z,v⟩|²`) and `quadForm_one` (`⟨v, v⟩`).
32. `outcomeProjector z r S` — one summand of `(19)`.  `outcomeProjector_conjTranspose`,
    `outcomeProjector_mul_self` and `outcomeProjector_mul_of_ne` are the mutual orthogonality of
    distinct outcome strings.
33. `boundedReplicaProjector z r k` — the operator `Q_{z;r,k}` of `(19)`.
    `boundedReplicaProjector_conjTranspose` and `boundedReplicaProjector_mul_self` are
    **`Q² = Q = Q*`** of `(20)`.
34. `quadForm_boundedReplicaProjector_eq_normSq` and
    `quadForm_one_sub_boundedReplicaProjector_eq_normSq` — **`0 ≤ Q ≤ I`** of `(20)`, in the form
    that both `⟨w, Q w⟩` and `⟨w, (I-Q) w⟩` are sums of squared moduli.
35. `quadForm_outcomeProjector` and `quadForm_boundedReplicaProjector` — **equation `(21)`**:
    `⟨v^{⊗r}, Q_{z;r,k} v^{⊗r}⟩ = B_{r,k}(|⟨z,v⟩|²)` for every unit `v`.  The regrouping of
    outcome strings by success count uses `Finset.sum_fiberwise_of_maps_to` together with
    `Finset.card_powersetCard`.
36. `normSq_hermInner_le_one` — Cauchy–Schwarz in the product basis, obtained from the positivity
    of `I - P_z` rather than assumed.
37. `sup'_replicaTest` — **equation `(22)`**: maximizing over the occupied target set commutes
    with the bounded test, because `B_{r,k}` is monotone on `[0,1]`.

## Verification

- `lake env lean` clean, no warnings, on all three modules.
- `lake build GaloisForLFunctions.HTGeometry.BinomialTailBetaThreshold`,
  `...BetaThresholdIncidenceLaw`, `...BoundedReplicaThresholdProjector` — green.
- `#print axioms` on statements 1, 8, 9, 13, 15, 16, 21–27, 33–35, 37:
  `propext`, `Classical.choice`, `Quot.sound` only.
- Umbrella imports present in `GaloisForLFunctions/HTGeometry.lean`.

## What is *not* claimed

The card's positive survivor `(27)`–`(28)` — that the quenched incidence action is `o_n(1)` for
ordinary static local Hamiltonians — is a dynamical anti-concentration statement about a specific
ensemble.  It is a research target on the parent cards, not formalization debt: Theorems A, B, B',
C and the separation example are exactly what this closure certifies, and they are the whole
mathematical content of the reduction.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready
