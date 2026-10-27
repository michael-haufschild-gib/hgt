# The half-defect is the optimal Frobenius Hodge repair

Status: formalized in Lean 4.

Module: `formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheHalfDefectIsTheOptimalHodgeRepair.lean`.
Namespace: `GaloisForLFunctions.ArithmeticLorentzianGeometry`.

## Mathematical result

For every `CurveDatum D`, let `r(z)=1/conj(z)` and `E_x(z)=Σ_{k<n} x_k z^k`.
Let `O_n` and `A_n` be the odd and even reflected evaluation matrices, with rows
`(β_j^k-r(β_j)^k)/2` and `(β_j^k+r(β_j)^k)/2`. Define `C_n=O_nᴴ O_n`.

The actual normalized Frobenius span Gram satisfies `G_n+C_n=A_nᴴ A_n`.
Thus `C_n` and `G_n+C_n` are positive semidefinite, and
`C_n[x]=Σ_j |E_x(β_j)-E_x(rβ_j)|²/4`. On real graph classes this is exactly half
ACS's existing `frobReflectionDefect`. In raw graph coordinates, for every signed real `d`,

`spanDefect(range n,d) + frobReflectionDefect(range n, k ↦ d_k sqrt(q)^k)/2 ≥ 0`.

The correction commutes with restriction to an initial window. Its entire row and column at
exponent zero vanish, preserving the diagonal graph's pairings.

Let `κ` be the number of distinct normalized eigenvalues outside the unit circle. For every
window `n≥D.spectrum.card`:

1. `rank C_n=κ`. Every matrix `R` with `G_n+R` positive semidefinite has rank at least `κ`;
   the competing correction need not itself be positive.
2. `G_n+t C_n` is positive semidefinite exactly when all eigenvalues have norm one or `t≥1`.
3. For every pole row `B`, completing the defect by
   `Q_B(G)=[[J,B],[Bᴴ,BᴴJB-G]]` turns this into a Hodge repair. Subtracting `C_n` only from
   the graph block preserves the pole plane and both pole couplings and gives one positive
   square. The same exact scalar threshold holds, independently of `B`.

The combined theorem `optimal_frobenius_hodge_repair` uses the window `n=D.spectrum.card`,
so its statement needs no window-size premise. No purity, Hodge-index, point-count positivity,
or unproved analytic input is assumed for the datum.

## Dependency-closed proof

Reflection permutes the eigenvalue list, including multiplicity. Consequently the two cross
sums obtained by expanding the even and odd Gram matrices agree. Their difference is the
existing reflected-evaluation expression for `D.spanGram`, proving `G+C=AᴴA`.

The odd evaluation matrix factors as `outerReflectionCoordinates * outerFrobeniusOdd`.
For an outer eigenvalue its row is its own outer row; for an inner eigenvalue it is the negative
of its reflected outer row; for a unit-circle eigenvalue it is zero. The factorization uses
`pairValue` to select the appropriate distinct outer coordinate. Matrix rank inequalities give
`rank C≤κ` on every window. At a spectrum-complete window, ACS's exact Pontryagin law gives
`hermNegIndex G=κ`. The existing finite-rank perturbation inequality forces every positivity
repair to have rank at least `κ`, so our explicit correction attains the bound.

For each outer point, Lagrange interpolation realizes the function taking values `1` at that
point, `-1` at its reflection, and zero at the rest of the spectrum. Its even evaluation is zero
and its odd energy is strictly positive. On this vector `G+tC=(t-1)C`, forcing `t≥1`.
Conversely, `G+tC=AᴴA+(t-1)C` is positive for `t≥1`; in the unitary case `C=0`.

Haynsworth additivity for the invertible hyperbolic pole plane gives
`hermPosIndex Q_B(G)=1+hermNegIndex G`. ALG's Hermitian hyperbolicity criterion therefore
transfers the positivity and threshold laws to the completed intersection form. The exact
block subtraction identity proves pole preservation.

## Lean declarations

- `spanGram_add_halfDefectRepair`
- `halfDefectRepair_posSemidef`, `spanGram_halfDefectRepair_posSemidef`
- `halfDefectRepair_submatrix`, `halfDefectRepair_zero_row`, `halfDefectRepair_zero_column`
- `halfDefectRepair_energy`, `halfDefectRepair_eq_half_frobReflectionDefect`
- `frobeniusOdd_factor`, `rank_halfDefectRepair_le`, `rank_halfDefectRepair`
- `outerSpectrum_card_le_rank_repair`, `exists_positive_repair_iff`
- `spanGram_scaled_halfDefectRepair_posSemidef_iff`
- `hodgeCompletion_add`, `posIndex_hodgeCompletion`, `hodgeCompletion_isHyperbolicHerm_iff`
- `halfDefectRepair_hodgeIndex`, `halfDefectRepair_hodgeIndex_iff`
- `optimal_frobenius_hodge_repair`
- `spanDefect_add_half_reflectionDefect_nonneg`

## Novelty and exact boundary

Reused: ArithmeticPolarization's reflected-pairing mechanism; ACS's actual reflected evaluation
Gram, reflection defect, interpolation and exact negative-index count; HTGeometry's general
rank perturbation and Haynsworth laws; ALG's Hermitian Hodge criterion. The restricted-Weil
programme already has abstract optimal negative-part repairs.

The contribution is the explicit half-defect repair, its coherence and diagonal preservation,
its attaining the exact rank budget on complete windows, the sharp coefficient law, and its
pole-preserving Hodge transfer. Generic minimum-rank repair alone is not claimed as new.

The correction is rank-minimal on complete windows and coefficient-minimal along its specified
ray. No least correction in the positive-semidefinite order is claimed. Short-window rank
minimality is not claimed. Positivity and restriction coherence hold on all windows.

The corrected pairing is different from the original pairing. This result neither proves RH
nor supplies an arithmetic sign producer. It identifies the exact reflection-odd sector that
an arithmetic construction must eliminate while retaining the original pairing. Extending the
coherent finite-spectrum construction to an infinite spectrum requires additional analytic
control and is open.

## Validation

Targeted final audit from `formal/`:

`lake --old env lean GaloisForLFunctions/ArithmeticLorentzianGeometry/TheHalfDefectIsTheOptimalHodgeRepair.lean`

Seven principal axiom audits cover the decomposition, restriction, identification with the
existing defect, optimal rank, scalar threshold, combined Hodge theorem and raw graph-coordinate
inequality. Dependencies: only `propext`, `Classical.choice`, `Quot.sound`.

The module is wired into the ALG umbrella; no umbrella or whole-project build was run.
