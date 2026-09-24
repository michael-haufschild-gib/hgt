# Weil's bound for Kloosterman sums in Lean

- **ID:** WEIL-KLOOSTERMAN
- **Stage:** 3-formalized
- **Type:** THEOREM (paper, classical) — Lean build
- **Source:** Selberg programme (card `selberg-maass-symmetric-power-attempt`, section 7). Absent from mathlib
  and the corpus (searched 2026-09-24).
- **Statement:** For a prime p, a ∈ 𝔽_p^×, and the standard additive character ψ,
  |Σ_{x ∈ 𝔽_p^×} ψ(x + a/x)| ≤ 2√p.

## Why
Needed for every Kloosterman/Kuznetsov estimate (Selberg's 3/16, sums of Kloosterman sums over moduli,
the d = 2 case of the moduli-cancellation hypothesis H_η), and the d = 2 model for Deligne's bound.

## Proof route chosen for Lean (no étale cohomology)
1. **L-function over monic polynomials.** For monic f ∈ 𝔽_q[T] with f(0) ≠ 0 put
   λ(f) = ψ(−nextCoeff f − a·f'(0)/f(0)). Multiplicative: nextCoeff and f'(0)/f(0) are additive under
   products. Degree sums: s₀ = 1, s₁ = K, s₂ = q, s_m = 0 (m ≥ 3; the T^{m−1}-coefficient is free).
2. **Newton identity.** With c_n = Σ_{P monic irreducible, deg P | n} deg P·λ(P)^{n/deg P}:
   m·s_m = Σ_{k=1}^m c_k s_{m−k} (von Mangoldt identity deg f = Σ_{P^k | f} deg P, and f = P^k h).
   Hence c₁ = K, c₂ = 2q − K², c_m = −K c_{m−1} − q c_{m−2}; so c_n = −(αⁿ + βⁿ) with α + β = −K, αβ = q.
3. **Roots.** c_n = K_n := Σ_{x ∈ 𝔽_{q^n}^×} ψ(Tr(x + a/x)) (group x by minimal polynomial).
4. **Stepanov.** For the Artin–Schreier curve y^p − y = x + a/x over 𝔽_{q^n}: N_n ≤ q^n + C q^{n/2} for large
   even n (auxiliary polynomial vanishing to high order, Hasse derivatives, dimension count).
5. **Conclusion.** N_n = q^n − 1 + Σ_{j ∈ 𝔽_p^×} K_n(ja), so Re Σ_j (α_jⁿ + β_jⁿ) ≥ −C q^{n/2}. A Pringsheim-type
   lemma gives |α_j| ≤ √q; with αβ = q, |α| = |β| = √q and |K| ≤ 2√q.

## Log
- 2026-09-24 — card opened; step 1 started.
- 2026-09-24 — Steps 1–3 closed in Lean (build green, axioms propext/choice/Quot.sound, wired into RHTower.lean):
  `WeilKloostermanDegreeSums` (monic parametrization, multiplicative weight, s₀ = 1, s₁ = K, s₂ = q, s_m = 0),
  `WeilKloostermanLFunction` (general Newton identity m·s_m = Σ c_j s_{m−j} for multiplicative weights on monic
  polynomials; c_n = −(αⁿ+βⁿ), αβ = q), `WeilKloostermanHasseDavenport` (fibres of the minimal-polynomial map,
  minpoly of x⁻¹ = normalized reverse, trace formula, `hasseDavenport`: K_E(a) = −(α^{[E:F]} + β^{[E:F]}) for every
  finite extension E/F). Remaining: step 4 (Stepanov upper bound for the Artin–Schreier curve), step 5
  (additive Hilbert 90 point count N = Q − 1 + Σ_j K_E(j²a), Pringsheim-type lemma, |K| ≤ 2√q).

## Revised steps 4–5 (paper, 2026-09-24): hyperelliptic Stepanov route
- **Reduction.** For p odd, E ⊇ 𝔽_p, |E| = Q: #{x ≠ 0 : x + a/x = u} = 1 + χ(u² − 4a) (χ quadratic character of E),
  and u ∈ ker Tr_{E/𝔽_p} ⇔ u = v^p − v with exactly p preimages v (additive Hilbert 90). Hence
  Σ_{j∈𝔽_p} K_E(ψ_j; a) = p·#{x ≠ 0 : Tr(x + a/x) = 0} = Q + Σ_{v∈E} χ(h(v)), h(v) = (v^p − v)² − 4a, and
  K_E(ψ_j; a) = K_E(ψ; j²a) = −(α_jⁿ + β_jⁿ). So |Σ_{j≠0}(α_jⁿ + β_jⁿ)| ≤ 1 + |Σ_v χ(h(v))|.
- **h is squarefree:** h = (A − c)(A + c), A = v^p − v, c² = 4a; A ± c are separable (A′ = −1) and coprime.
- **Stepanov (hyperelliptic).** For squarefree h of degree D and ε = ±1, T_ε = {x : h(x) ≠ 0, h(x)^{(Q−1)/2} = ε}:
  auxiliary R = Σ_{j<J} (r_j + s_j h^{(Q−1)/2}) X^{Qj}, deg r_j, s_j < K. Hasse derivatives: D^{(k)}X^{Qj} = 0 (0<k<Q),
  D^{(k)}h^N = h^{N−k}P_k with deg P_k ≤ k(D−1). Vanishing of the polynomials Φ_k (k < ℓ) is a linear system with
  Σ_k (K + kD + J) equations and 2KJ unknowns; independence (R ≠ 0) from h(X)Â(X,Y)² = B̂(X,Y)²h(Y) forcing h(X)h(Y)
  to be a square unless Â = B̂ = 0 (needs 2K + D ≤ Q). Then ℓ|T_ε| ≤ deg R, giving |T_ε| ≤ Q/2 + C_D√Q for large
  even n, hence |Σ_v χ(h(v))| ≤ 2C_D√Q + D.
- **Vandermonde lemma.** If |Σ_i ω_iⁿ| ≤ C·Rⁿ for all large n then max|ω_i| ≤ R (invert the Vandermonde system of
  distinct values). Applied with R² = p on even n: |α_j|, |β_j| ≤ √p, αβ = p ⇒ |K(a)| = |α + β| ≤ 2√p.
Components: (A) Hasse derivatives of X^{Qj}, root multiplicity via Hasse derivatives; (B) D^{(k)}h^N = h^{N−k}P_k;
(C) nonzero kernel of an underdetermined linear map; (D) independence lemma; (E) root counting; (F) parameters;
(G) Euler criterion link; (H) squarefreeness of h; (I) additive Hilbert 90 count; (J) Vandermonde; (K) assembly.
- 2026-09-24 — Stepanov closed in Lean (build green, axioms propext/choice/Quot.sound):
  `StepanovHyperelliptic` (Hasse-derivative lemmas, D^{(k)}h^N = h^{N−k}P_k, substitution injectivity, squarefree
  descent, `stepanov_independence`), `StepanovCount` (`stepanov_count`: ℓ·#T_ε ≤ (K−1) + N·D + Q(J−1)),
  `StepanovCharacterSum` (`stepanov_bound`: 2#T_ε ≤ s² + 2(D+1)s for Q = s², s ≥ D + 5;
  `abs_sum_quadraticChar_le`: |Σ_x χ(h(x))| ≤ 2(D+1)s + D). Elementary Weil bound for hyperelliptic character
  sums over even-degree extensions. Remaining for Kloosterman: squarefreeness of (v^p−v)²−4a, the
  Artin–Schreier/trace counting identity Σ_{j≠0} K_E(j²a) = 1 + Σ_v χ(h(v)), and the Vandermonde lemma.
- 2026-09-24 — **Closed in Lean** (build green with `--old`, wired into RHTower.lean, axioms
  propext/Classical.choice/Quot.sound). `WeilKloostermanArtinSchreier`: `asMap` (v ↦ v^p − v) has kernel of
  size p and image = trace kernel (`image_asMap`, `sum_asMap`), `card_fiber_quadratic`
  (#{x≠0 : x + b/x = u} = 1 + χ(u² − 4b)), `sum_twist_char`, `twist_eq_extKloosterman`,
  `sum_extKloosterman_twists`: Σ_{j∈𝔽_p^×} K_E(j²a) = 1 + Σ_v χ((v^p−v)² − 4a).
  `WeilKloostermanBound`: `asDisc_squarefree`, `norm_le_of_power_sums_bound` (power sums O(ρ^m) ⇒ all |z_i| ≤ ρ),
  `power_sums_bound` (over GaloisField p (2m), m ≥ 3), and
  `kloosterman_weil_bound : p ≠ 2 → ψ primitive → a ≠ 0 → ‖kloosterman ψ a‖ ≤ 2√p`.
  Classical theorem (Weil 1948); first formal proof in this corpus and, as far as checked, absent from mathlib.
