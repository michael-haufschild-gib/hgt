# Weil's bound for Kloosterman sums in Lean

- **ID:** WEIL-KLOOSTERMAN
- **Stage:** 1-in-progress
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
