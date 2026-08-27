# PW-B signed matrix three-moment classification

- **ID:** PW-SM3
- **Stage:** 3-formalized
- **Type:** SIGNED MATRIX CLASSIFICATION / EXACT DARK SECTOR
- **Parent:** PW-B
- **Lean module:** `GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekSignedMatrixThreeMomentClassification`
- **Frontier-map policy:** read only

## Result

Set

`C(s)=Re(s)(1-Re(s))+Im(s)^2+1`, `u(k)=4k(k+1)`.

Every Borel-grade residual satisfies the exact affine-rank-two law

`Residual(s,k)=C(s)+u(k)`.

For arbitrary finite real matrix `M`, define

`m₀=ΣᵢⱼMᵢⱼ`,
`m₁=ΣᵢⱼMᵢⱼ(uᵢ+uⱼ)`,
`m₂=ΣᵢⱼMᵢⱼuᵢuⱼ`.

Then

`ResidualEnergy(M,s)=m₀C(s)^2+m₁C(s)+m₂`,

and

`CrossGradeEnergy(M,s)=Wall(s)^2(m₀C(s)^2+m₁C(s)+m₂)`.

On actual Xi support this gives the complete pointwise classification

`CrossGradeEnergy(M,ρ)=0 ↔ Re(ρ)=1/2 ∨ P_M(C(ρ))=0`.

Moreover, `P_M` and the full energy vanish identically exactly when all three
moments vanish.

## Exact dark sector

The first three recoil grades obey, for every complex `s`,

`2 phase₀(s)-3 phase₁(s)+phase₂(s)=0`.

Let `w=(2,-3,1)` and `M=w wᵀ`.  Lean proves:

- `M` is symmetric and nonzero;
- `M₀₁=-6`, so it is genuinely signed;
- its quadratic form is a square and hence nonnegative for every vector;
- its recoil reporter and full cross-grade energy vanish for every `s`.

Thus a nonzero symmetric positive-semidefinite finite coupling can be
identically dark.  Entrywise nonnegativity in PW-PM is essential; positive
semidefiniteness alone is insufficient.

## Paper proof

Expanding the existing residual gives

`(2k+x+1/2)(2k+3/2-x)+y²+1/4`
`=4k(k+1)+x(1-x)+y²+1`.

Substitution into the finite double sum and expansion yields the three moments.
The existing common-wall theorem supplies the full energy factorization.  On Xi
support, nonzero imaginary part makes `Wall(s)=0` equivalent to `Re(s)=1/2`,
giving the union classification.

For the kernel theorem, an identically zero quadratic is evaluated at spectral
coordinates `1,2,5`; the resulting nonsingular three-equation system forces
`m₀=m₁=m₂=0`.  Conversely those equalities erase the polynomial.  For full
energy use non-wall test points with coordinates `2,5,10`.

Finally `u(0)=0`, `u(1)=8`, `u(2)=24`, and both
`2-3+1=0` and `2u(0)-3u(1)+u(2)=0`; hence `w` annihilates both generators of
the residual affine span.  Its outer product is PSD because every quadratic
form equals `(Σᵢvᵢwᵢ)^2`.

Dependency-closed; no analytic or asymptotic premise remains.

## Lean theorems

- `schwarzschildParikhWilczekBorelGradeResidual_eq_coordinate_add_shift`
- `schwarzschildParikhWilczekMatrixResidualEnergy_three_moment`
- `schwarzschildParikhWilczekMatrixCrossGradeEnergy_three_moment`
- `schwarzschildParikhWilczekMatrixCrossGradeEnergy_eq_zero_iff_wall_or_residual`
- `schwarzschildParikhWilczekSignedMatrixResidualPolynomial_eq_zero_forall_iff`
- `schwarzschildParikhWilczekMatrixCrossGradeEnergy_eq_zero_forall_iff_moments`
- `schwarzschildParikhWilczekBorelRecoilHolonomy_im_three_grade_dark`
- `schwarzschildParikhWilczekThreeGradeDarkMatrix_symmetric`
- `schwarzschildParikhWilczekThreeGradeDarkMatrix_ne_zero`
- `schwarzschildParikhWilczekThreeGradeDarkMatrix_has_negative_entry`
- `finite_rankOneQuadraticForm_eq_sq`
- `schwarzschildParikhWilczekThreeGradeDarkMatrix_quadraticForm_nonneg`
- `schwarzschildParikhWilczekThreeGradeDarkReporter_zero`
- `schwarzschildParikhWilczekThreeGradeDarkMatrix_energy_zero`

## No-go and positive survivor

**No-go.** Finite signed matrix cross-grade flatness is not an RH producer: it
can be caused by a residual-quadratic root or by the exact three-moment dark
kernel.  Even symmetric PSD coupling does not exclude this counterfeit.

**Positive survivor.** Every finite signed interaction has an exact quotient by
the three moments `(m₀,m₁,m₂)`.  Outside their common kernel, its only possible
counterfeit zeros are roots of one explicit degree-two polynomial in `C(s)`.
This is a complete finite signed-matrix invariant and reduces source design to a
sharp root-exclusion obligation.

Remaining viable PW-B producer must derive coupling moments whose quadratic is
strictly nonzero on all Xi spectral coordinates, or introduce genuinely
non-affine cross-shell/orbit dynamics beyond finite Borel-grade mixing.

## Novelty audit (through 2026-08-27)

Mandatory corpus searches for PW Borel signed matrices, rank collapse, moment
classification, and annihilators found no such theorem.  Primary-source search
covered Parikh--Wilczek's original nonthermal tunneling law
([arXiv:hep-th/9907001](https://arxiv.org/abs/hep-th/9907001)), work on
correlation claims and their limitations
([arXiv:1406.3635](https://arxiv.org/abs/1406.3635)), and semiclassical
successive-emission correlation analysis
([arXiv:1703.10760](https://arxiv.org/abs/1703.10760)).  Searches for Borel
recoil grades, signed matrix moments, or the three-grade relation found no
matching primary result.

Novelty priority remains provisional pending expert/database review; theorem
itself is unconditional and formally checked.

## Verification

- Direct `lake env lean` check: passed.
- Targeted module build: passed.
- Axiom audit: all fourteen exported theorems use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Umbrella import: wired; full umbrella build intentionally not run.
