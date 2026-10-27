# The Landau–Wronskian principle and strong multiplicity one for powers of ζ

- **ID:** bgg-c9
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:**
  1. (Principle) Entire `Λ, Λ₀` with finite orders, nonzero on a real ray where
     `Λ₀'/Λ₀ − Λ'/Λ = 𝓛ν + E` (`ν ≥ 0`, `E` holomorphic on `Re s > σ_E`): for some `c ≥ 0` the divisors
     agree on `Re w > max(c, σ_E)`, and `c > max(0, σ_E)` forces `Λ₀(c) = 0`, `ord_c Λ < ord_c Λ₀`.
  2. (ζ^d rigidity) `(F, Λ) ∈ CompletedPositiveSystem κ d`, `κ ≤ d`, `−F'/F + dζ'/ζ = 𝓛ν + E` with
     `σ_E < 1/2` ⇒ `κ = d` and `F = K ζ^d`, `K ∈ ℝ^×`. No hypothesis on the zeros of `ξ`.
  3. (Strong multiplicity one) Same class, `−F'/F = Σ b(n)n^{−s}`, `b ≥ 0`, deficit `Σ (dΛ(n) − b(n))⁺ n^{−s}`
     of abscissa `< 1/2` ⇒ `κ = d`, `b = dΛ` on `n ≥ 1`, `F = K ζ^d`.

## Paper proof
1. Thicken `ν` by Lebesgue measure (finite abscissa `c ≥ 0`); the Wronskian
   `Λ₀'Λ − Λ'Λ₀ − (𝓛(ν + Leb) − 1/s + E)ΛΛ₀` vanishes on the ray, hence on `Re s > max(c, σ_E)`; residues
   give equal orders. At `c > max(0,σ_E)` Landau forbids equal orders and positivity of the transform
   on the ray fixes the sign.
2. Compare `Λ(s(s−1))^{d−κ}` with `(s(s−1))^{κ−d}(2ξ)^d` (same archimedean factor on `Re s > 1`). The
   base has no positive real zero when `κ ≤ d` (ξ has no real zeros), so `max(c, σ_E) < 1/2`. At `s = 1`,
   `κ < d` would give a zero of the left side but not of `(2ξ)^d`: so `κ = d`. Orders agree right of
   `1/2` and, by `s ↦ 1 − s`, everywhere. Divisor rigidity (zero-free order-one quotient `Q e^{Bs}`,
   symmetry ⇒ `B = 0`, reality ⇒ `Q ∈ ℝ`) and cancellation of `(s(s−1))^dΓ_ℝ^d`.
3. Split `−F'/F + dζ'/ζ` into the surplus lattice measure plus `b(1) − D` (deficit series), apply 2, and
   compare Dirichlet coefficients.

## Lean
`TheLandauWronskianDeformationPrinciple.lean`: `landauWronskian_orders_and_anchor` (+ moved helpers).
`StrongMultiplicityOneForPowersOfZeta.lean`: `logDeriv_sub_eq_of_common_factor`,
`zetaPowDeformation_orders_and_anchor`, `orderOneEnvelope_two_xi_pow`, `zetaPowDeformation_trivial`,
`latticeMember_eq_zetaPow`. Generic `eq_real_const_mul_of_orders_eq` (C6 module), general split
`relMember_primeMass_split` (C4 module). Axioms: propext, Classical.choice, Quot.sound.

## Log
- 2026-10-27 — formalized.
