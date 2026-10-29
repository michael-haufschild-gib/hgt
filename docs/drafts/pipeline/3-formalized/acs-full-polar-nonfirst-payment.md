# The actual full pole term in the joint non-first-prime payment

- **ID:** acs-full-polar-nonfirst-payment
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Replace the detail pole in the proved joint source by the
  actual complete-profile pole, retaining coarse Gamma and positive detail
  reserves at the cost of one scalar negative direction.

## Exact source

For original averages g, details h and F=g+h, write
`P(f)=2 coshHalfMoment(f)²−2 sinhHalfMoment(f)²` and
`κ=fullDetailPrimeGap`. The source to estimate is

`R=ΓF+2 gammaHardyPhaseRate(0)∫h²−haarPrimeEnergy(d,X)
    −squarePrimeMixedSource(q,d,X)−oddHigherPrimePowerMixedSource(d,q,X)+P(F)`.

The full P(F), including coarse and mixed moments, must remain literal.
The estimate, beyond a fixed detail head, is

`(1−ε)Γg+(κ/8)D+∫h²+2 coshHalfMoment(F)²
 ≤ R+2 sinhHalfMoment(F)²`.

It gives a uniform negative-dimension bound A+1 through the A detail
head coefficients and the single original sinh moment. This pays the full
polar block in this source, not the remaining coarse signed prime and
archimedean block or the first-prime mixed source.

## Proof

Write p± for the two exponential moments of h and M=∫h². Existing estimates
give `(p+)²≤M` and `(p−)²≤M`. Since P(h)=2p+p− and
`(p+−p−)²≥0`, this implies P(h)≤2M.

The proved joint source Q retains `(1−ε)Γg+(κ/4)D+M` beyond a fixed
head A₀. Choose A₁>exp(16/κ). For details vanishing below A₁,
`cellGammaWeight(A₁) M≤D`, while `cellGammaWeight(A₁)≥log A₁>16/κ`.
Thus `(κ/8)D≥2M`. The maximum of A₀,A₁ works uniformly in q,d,X.

The exact source identity is `R=Q−P(h)+P(F)`. Consequently
`R−P(F)≥Q−2M≥(1−ε)Γg+(κ/8)D+M`, which is precisely the asserted
estimate with both full-profile polar squares retained. Applying it to
the actual tail coefficients removes the head-vanishing condition.

For an arbitrary finite family, read the first A detail coefficients and
the single sinh moment of the complete linear combination into ℝ^(A+1).
That moment is linear by finite sum integration on compact BV profiles.
At ε=1/2 the source is nonnegative on the readout kernel. A strictly
negative subspace meets this kernel only at zero, so the readout is
injective on that subspace and its dimension is at most A+1.

No polar correction is added to the source. Its original full pole is
retained, with its sole adverse square represented by its actual moment.

## Inputs and status

- `EveryMixedExponentAboveOneLeavesACoarseReserve.lean`: inspected; direct
  check passed in the previous goal turn.
- `HaarCellPoleBound.lean`: both exponential moments have square at most
  the exact detail square mass.
- Lean implementation, including the upper pole estimate, full-profile
  moment linearity and the finite readout:
  `ArithmeticIndexDescent/TheFullPolarNonfirstSourceHasUniformFiniteIndex.lean`.
  Direct check passed without diagnostics:

  `lake --old env lean GaloisForLFunctions/ArithmeticIndexDescent/TheFullPolarNonfirstSourceHasUniformFiniteIndex.lean`

- `haarSectionProfile_pole_le_mass`: upper bound for the removed detail pole.
- `exists_fullPolarNonfirst_coarse_reserve`: joint coercive estimate with the
  complete original polar term.
- `exists_fullPolarNonfirst_uniform_tail`: the same bound on literal tails.
- `sinhHalfMoment_completePairProfile_linearCombination`: the adverse moment
  is the original linear readout on every finite family.
- `exists_uniform_fullPolarNonfirst_negative_dimension`: one horizon-independent
  bound A+1 on strictly negative subspaces.
- Imported by the AID umbrella; umbrella not compiled.

## Remaining source problem

First-prime mixing and the coarse signed prime/archimedean block remain.
The positive cosh square is retained for their joint comparison. A finite
detail head and the sinh coordinate still cost negative directions; no
complete-Weil index bound or index-zero statement follows from this subform.
The existing ordered Chebyshev identity keeps prime–pole cancellation before
absolute values. It supplies an exact discrepancy, not its missing sign.

No web search, novelty checks, numerical computations or axiom checks.
