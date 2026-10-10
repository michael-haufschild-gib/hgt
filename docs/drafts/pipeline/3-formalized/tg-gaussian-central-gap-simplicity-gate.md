# TG — Gaussian simplicity gate (multiplicity excess of the Cramér mean square)

- **ID:** TG-SIMP-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean; RH-conditional identity + unconditional characterization)
- **Statement:** c_q = ½Γ((ρ_q−½)/2) over multiplicity copies q. Excess E := Σ_{q≠q', ρ_q=ρ_q'} |c_q|² (= Σ_ρ(m_ρ²−m_ρ)|c_ρ|²).
  (a) E ≥ 0; E = 0 ⟺ q ↦ ρ_q injective (all zeros simple) — unconditional.
  (b) Under RH: T⁻¹∫₀^T G(u)²du → |A(½)|² + Σ_q|c_q|² + E.

  (c) Unconditional at the zero abscissa Θ: normalized mean square of e^{-(Θ−½)u/2}G → [Θ=½]|A|² + Σ_{Re ρ_q=Θ}|c_q|² + E_Θ,
      E_Θ = Σ_{Re ρ=Θ}(m²−m)|c|² ≥ 0, E_Θ = 0 ⟺ every zero on Re s = Θ is simple.

## Proof
Parseval pair kernel (cycle 24) under RH: equal half-ordinates ⟺ same zero (Re = ½), and c depends only on ρ, so the
pair term is |c_q|² on same-zero pairs. Split into diagonal (Σ_q|c_q|² via the diagonal embedding) and off-diagonal (E).
E > 0 iff some pair of distinct copies shares a zero (positivity of tsum, c_q ≠ 0).

## Lean
`RHTower/GaussianCentralGapSimplicityGate.lean`, wired after GaussianCentralGapFiniteHeightTransfer.
`gaussianMultiplicityExcess`, `multiplicityExcess_eq_zero_iff_injective`,
`tendsto_centralGap_meanSquare_eq_diagonal_add_multiplicityExcess`, `extremalMultiplicityExcess`,
`extremalMultiplicityExcess_eq_zero_iff`, `tendsto_extremalGap_meanSquare_eq_diagonal_add_excess`. Axioms [propext, Classical.choice, Quot.sound].

## Reading
TG-style integer residual for simplicity: beyond the Weil-type (linear) diagonal Σ_ρ m_ρ|c_ρ|², the prime-side
mean square carries exactly the quantized multiplicity defect Σ(m²−m)|c|² (each double zero costs 2|c_ρ|²).
A simplicity "producer" = computing the Gaussian mean square to precision below 2|c_ρ|² near height γ — a prime pair
correlation (Montgomery-type) problem; Γ-damping makes only low zeros visible.
