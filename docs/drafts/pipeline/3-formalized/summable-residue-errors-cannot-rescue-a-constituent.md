# Summable residue errors cannot rescue a constituent

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Γ215; B153, arithmetic constituents of ξ.
- **Statement:** Let `F` be a nonzero real-scale Wiener expansion on the closed strip of half-width `0 < ω ≤ 1/2` about `Re s = 1/2`. A zero in its interior forces either an off-line zero there or nonsummability of `mρ ‖ζ(ρ)/ρ‖` over its critical-line zeros, with `mρ` the analytic multiplicity.

## Mathematical connection

CTZ's finite-exception exclusion and summable-pole jump law meet through normal convergence and local zero factorization. The survivor is a divergent weighted residue mass, stronger than merely infinitely many unmatched zeros. B153 in the bounded class remains open.

## Proof [PROVED HERE]

Assume all strip zeros lie on the line and their residue norms have finite sum `R`. Put `K(s) = −ζ(s)/s` on a smaller strip and `rρ = mρ K(ρ)`.

1. Finite analytic order isolates every zero. Away from the divisor, `Σ rρ/(s−ρ)` converges normally, bounded by `R/d` at distance at least `d` from all zeros. Near a zero, remove its one term; the remaining series is analytic. Local factorization gives `KF'/F = rρ/(s−ρ) + Hρ` with `Hρ` analytic. Thus their difference extends holomorphically across every zero.
2. Wiener inversion expands `F'/F` on either side of the line. These expansions bound the remainder on two vertical boundary lines. Strip almost periodicity supplies relatively dense horizontal lines with `|F| ≥ μ > 0`. A uniform derivative bound `M` puts every zero at distance at least `μ/(M+1)` from these lines. The same Cauchy-sum estimate bounds the remainder there. The maximum principle on the resulting rectangles bounds it throughout the smaller strip.
3. Apply the summable-pole jump law: the polar series is continuous, so both logarithmic-derivative expansions have identical coefficients. Their common expansion is holomorphic across the line. Analytic continuation gives `F' = HF`; a nonzero analytic solution of this equation has no zeros. This contradicts the assumed zero.

## Lean

- Module `HTGeometry.SummableLogarithmicPrincipalParts`: `GaloisForLFunctions.HTGeometry.exists_holomorphic_sub_residueCauchySum`.
- Module `ConstituentTheoryOfTheZeros.SummableResidueErrorsDoNotPermitZeros`: `GaloisForLFunctions.ConstituentTheoryOfTheZeros.expansion_zero_forces_offLine_or_nonsummable_residues`.
- Both modules compiled; both programme umbrellas import them. Final capstone check: `lake --old env lean GaloisForLFunctions/ConstituentTheoryOfTheZeros/SummableResidueErrorsDoNotPermitZeros.lean`.
