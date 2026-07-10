# Finite prime Sonin Gram matrices inject into the Calkin quotient

- **ID:** finite-prime-sonin-gram-matrix-injectivity
- **Stage:** 3-formalized
- **Type:** THEOREM / QUADRATIC OBSTRUCTION (Lean)
- **Date:** 2026-07-10
- **Status banner:** `[NOVELTY UNVERIFIED]` Full matrix-level compactness rigidity is formalized on
  the actual even Sonin carrier and on the literal Hardy--Titchmarsh source. Scientific priority
  remains subject to an independent Sonin/prolate and operator-algebra audit.
- **Paper source:**
  `../../2-fully-proven/new_scientific_knowledge/sonin-prime-quadratic-calkin-matrix-injectivity.md`
- **Lean endpoint:**
  `formal/GaloisForLFunctions/RHTower/SoninEulerFiniteGramLower.lean`

## Formal theorem

Let `a>0`, let `p : Fin n -> Nat` be an injective prime family, and write

`L_i=(1-Q_a)(U_(p_i)+U_(p_i)^(-1))Q_a`

on the exact even physical-and-Fourier Sonin carrier. For every complex matrix `A`, define

`G_A=sum_(i,j) A_(ij)L_i^*L_j`.

Lean proves

`IsCompactOperator G_A  iff  A=0`.                         (1)

This includes arbitrary trace-zero, skew-adjoint, indefinite, and nonsymmetric matrices. It is
strictly stronger than entrywise noncompactness of `L_i^*L_j`.

## Quantitative readers

For every compact operator `K`, Lean proves:

`||A_(lk)|| <= ||G_A-K||` whenever `k!=l`;                 (2)

`||sum_(i:p_k<=p_i) A_(ii)|| <= ||G_A-K||`.                (3)

The off-diagonal readers recover every off-diagonal matrix entry. The diagonal readers are tail
sums in prime order. If a diagonal matrix is nonzero, choose a maximal prime carrying a nonzero
diagonal coefficient; its tail is that coefficient alone. Thus the readers separate all matrices.

## Constraint mechanism

Lean constructs one interior shell `0<c<d<a` which simultaneously:

- sends every inverse-prime preimage outside the physical cutoff;
- sends every decreasing prime ratio outside the cutoff;
- makes every distinct nondecreasing prime-ratio image disjoint.

For shell cells `v_m`, the corrected inputs

`f_(k,m)=Q_a U_(1/p_k)v_m`

are contractive and weakly null. The exact limit table is

`L_j f_(k,m) -> 0` for `p_j<p_k`,

`L_j f_(k,m) -> U_(p_j/p_k)v_m` for `p_k<=p_j`.            (4)

Consequently the limiting Gram compression is controlled by equal prime ratios. The equation

`p_i/p_l=p_j/p_k`

reduces to `p_i p_k=p_j p_l`; unique factorization leaves only the direct off-diagonal match, while
equal input indices leave the diagonal tail transform. This discharges the arithmetic interface
inside Lean.

## Positive Euler and source forms

The positive Euler corner is the nonzero scalar multiple

`C_i=-p_i^(-1/2)L_i`.

Entrywise multiplication of `A` by the nonzero Gram scalars preserves `A!=0`. Lean therefore proves
that every nonzero finite matrix combination of `C_i^*C_j` is noncompact. It then transports the
whole matrix combination through the archimedean dual Hardy--Titchmarsh unitary, giving the same
theorem for the literal source operators

`archimedeanPrimeEulerQuadraticCorner a p_i p_j`.

## Lean surface

The key declarations are:

- `exists_finiteScale_gramSeparatingInteriorShell`;
- `evenCentralSoninDilationCorner_finitePairedInput_tendsto`;
- `inner_finiteSoninRatioOutput_active`;
- `primePairProduct_eq_cases` and `primeRatio_eq_cases`;
- `finiteGramShellCoefficient_prime_offDiagonal_eq`;
- `finiteGramShellCoefficient_prime_diagonal_eq`;
- `norm_matrixEntry_le_norm_finitePrimeEvenDilationGram_sub_compact`;
- `norm_finitePrimeDiagonalTail_le_norm_finitePrimeEvenDilationGram_sub_compact`;
- `finitePrimeEvenDilationGram_isCompactOperator_iff`;
- `finitePrimeEvenPositiveEulerGram_not_isCompactOperator_of_ne_zero`;
- `finitePrimeArchimedeanEulerGram_not_isCompactOperator_of_ne_zero`.

## Scientific boundary

- `[PROVED]` Every finite signed quadratic cancellation is excluded.
- `[PROVED]` The conclusion is matrix-level, not a collection of pairwise statements.
- `[PROVED]` Primality supplies the collision rigidity; arbitrary real scales can have repeated
  ratios and need not satisfy this theorem.
- `[OPEN]` Infinite matrices, conditionally renormalized all-prime products, nonlinear phase-ratio
  compensation, and changed polarizations are not covered.
- `[NOVELTY UNVERIFIED]` Preliminary searches found quasi-inner Sonin constructions and general
  Toeplitz/Hankel product theory, but not this actual-Sonin prime-ratio matrix theorem. Absence from
  a targeted search is not a priority proof.

## Gates

- [x] 0 -> 1: matrix-level open core isolated
- [x] 1 -> 2: complete shell and prime-ratio proof
- [x] 2 -> 3: dilation, Euler, and concrete source forms formalized
- [ ] 3 -> 4: independent primary-literature and expert audit
