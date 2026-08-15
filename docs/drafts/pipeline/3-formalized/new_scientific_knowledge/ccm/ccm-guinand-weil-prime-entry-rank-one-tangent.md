# CCM Guinand--Weil prime-entry rank-one tangent

- **Status:** LEAN-FORMALIZED
- **Lane:** CCM-FU / aperture-event orientation
- **Novelty scope:** corpus-new whole-matrix event tangent, rank-one factorization, and source-derived
  negative-semidefinite orientation
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/CCMGuinandWeilPrimeEntryRankOneTangent.lean`

## Divided-difference collapse

C62 proves that the odd tangent of one entering atom is mode times a common rate while every
diagonal tangent is that common rate:

```text
r_k=-4 criticalMellinAtomWeight(k)/log(k),
b'_(k,n)=n r_k,
d'_(k,n)=r_k.                                                   (1)
```

The underlying first-clock odd slope has prior corpus provenance in
`CCMFirstClockPrimeEntrySlopeTomography`; the all-mode diagonal relation and whole-matrix collapse
below are the new step.

On centered clock `c_i`, differentiate the whole divided-difference packet. Diagonal entries give
`r_k`; for `i != j`,

```text
(b'_(k,c_i)-b'_(k,c_j))/(c_i-c_j)=r_k.                          (2)
```

Lean proves `(2)` entrywise for every packet size. Therefore the whole event tangent is

```text
T_(k,N)=r_k vecMulVec(e,e),                                     (3)
```

where `e` is the constant CCM boundary vector.

## Orientation

For a genuine prime power, the von-Mangoldt weight is strictly positive and `log(k)>0`, so Lean
proves `r_k<0`. The exact quadratic form is

```text
v^T T_(k,N) v = r_k (sum_i v_i)^2 <= 0.                         (4)
```

It also proves `rank(T_(k,N))<=1`. Hence every prime-entry event is a negative-semidefinite
rank-one boundary contraction; it annihilates the zero-sum hyperplane and acts only on the
constant-boundary direction.

## CCM-FU consequence

Finite divided differences do not scramble atomic aperture incidence. They collapse each prime
event to the same canonical boundary line and preserve its negative orientation. This is stronger
than source-vector normalization: it is a whole-matrix, pre-ground-state orientation theorem.
Remaining work is to factor the full atomic BV measure through `(3)` and combine it with the
continuous pole/Gamma connection without losing sign.

## Lean declarations

- `ccmGuinandWeilPrimeEntryMatrixRate`
- `ccmGuinandWeilPrimeEntryCenteredSource`
- `ccmGuinandWeilPrimeEntryCenteredDiagonal`
- `ccmGuinandWeilPrimeEntryCenteredMatrix`
- `ccmGuinandWeilPrimeEntryRankOneTangent`
- `hasDerivAt_ccmGuinandWeilPrimeEntryCenteredSource_entry`
- `hasDerivAt_ccmGuinandWeilPrimeEntryCenteredMatrix_apply_entry`
- `ccmGuinandWeilPrimeEntryCenteredMatrix_deriv_eq_rankOne`
- `ccmGuinandWeilPrimeEntryMatrixRate_neg`
- `ccmGuinandWeilPrimeEntryRankOneTangent_quadratic`
- `ccmGuinandWeilPrimeEntryRankOneTangent_quadratic_nonpos`
- `ccmGuinandWeilPrimeEntryRankOneTangent_rank_le_one`

Targeted direct Lean check and `lake build
GaloisForLFunctions.RHTower.CCMGuinandWeilPrimeEntryRankOneTangent` pass. Principal
`#print axioms` reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
