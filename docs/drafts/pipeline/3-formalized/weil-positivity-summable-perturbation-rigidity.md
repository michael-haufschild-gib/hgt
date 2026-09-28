# Weil positivity is rigid under summable perturbations of the prime weights

**Status:** formalized (Lean, unconditional, standard axioms).
**Module:** `formal/GaloisForLFunctions/RHTower/WeilPositivitySummablePerturbationRigidity.lean`

## Statement
With the archimedean term of `ζ` fixed, the weights `Λ(n) + w(n)` are not Weil-positive whenever `Σ_{n≥2}|w(n)|n^{−½} < ∞` and `w ≢ 0` on `n ≥ 2`.

Corollaries:
- `eq_vonMangoldt_of_weilPositive_of_summable_sub`: a Weil-positive `lam` with `lam − Λ` summable equals `Λ`.
- `vonMangoldt_update_not_weilPositive`: no single weight can be changed.

## Proof
1. **Energy decomposition.** `∫|h|²S_{Λ+w} ≤ 2π‖W(f)‖ − ∫|h|²P_w + ε_N‖h‖²`, via the explicit formula for `Λ` and the full-symbol truncation bound for `w`.
2. **Coefficient extraction.** `∫|h_F|²P_w = Σ 2π w(n)n^{−½}φ_F(log n)`, using a tsum/integral interchange. For `F = g(x − log 1) ± g(x − log n₀)` (L57 resonator with coefficients `1_{m=1} ± 1_{m=n₀}`), `φ_F(log n) = ±2‖g‖²[n = n₀]`. So `P_w ≤ 0 ⇒ w(n₀) = 0`.
3. **Concentration.** At a point where `P_w > 0`, the spread radical tests `twistTest 0 τ₀ (log S) S` give energy `≤ 2πK S^{10}e^{−S} − (3/2)cS + cS/4 < 0`.

## Novelty and significance
- No literature studies which prime weights are compatible with Weil positivity.
- This gives the "exact primes" gate as a theorem: positivity pins every individual prime weight.
- New relative to the corpus. It extends the twist/scaling/constant isolation results to the whole ℓ¹ neighbourhood of `Λ`.
