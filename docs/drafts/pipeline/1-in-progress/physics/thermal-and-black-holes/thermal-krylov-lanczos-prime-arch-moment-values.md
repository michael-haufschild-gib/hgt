# Thermal Krylov--Lanczos value relations for the prime--archimedean moment tower

- **ID:** `thermal-krylov-lanczos-prime-arch-moment-values`
- **Stage:** 1-in-progress
- **Type:** PHYSICS VALUE BRIDGE / LEAN
- **Physics sources:** finite-temperature Wightman correlations, Liouvillian Krylov dynamics,
  and Lanczos moment reconstruction
- **Lean consumers:**
  `PrimeArchSourceTraceHankelIntNonnegative`,
  `PrimeArchSourceMomentHankelDeterminantsPositive`, and
  `RiemannHypothesis`

Primary physics references used for the value identities are Sasaki,
[`Towards Verifications of Krylov Complexity`](https://arxiv.org/abs/2403.06391), for the
Liouvillian/Wightman moment and corrected Hankel--Lanczos scaling laws, and the finite-temperature
Wightman/Krylov construction in [`Krylov complexity at finite
temperature`](https://arxiv.org/abs/2401.10499).

## Physics relation

For a Hamiltonian with energy levels `E_a`, a Hermitian observable with transition amplitudes
`O_ab`, and a nonnegative symmetric Wightman weight `w_ab`, the Liouvillian spectral moments are

```text
mu_k = sum_(a,b) w_ab |O_ab|^2 (E_a-E_b)^k.              (1)
```

Symmetry under `(a,b) <-> (b,a)` makes every odd moment vanish.  The even moments

```text
nu_n = mu_(2n)
     = sum_(a,b) w_ab |O_ab|^2 ((E_a-E_b)^2)^n           (2)
```

are moments of a positive spectral-gap-square distribution.  Therefore every ordinary and shifted
Hankel form of `nu` is nonnegative.  Equivalently, the finite vectors

```text
v_n(a,b) = sqrt(w_ab) O_ab (E_a-E_b)^(2n)                (3)
```

satisfy `inner(v_i,v_j)=nu_(i+j)`.

The determinant has the exact Krylov residual factorization

```text
det(nu_(i+j))_(0<=i,j<N)
  = product_(k=0)^(N-1) ||GS(v)_k||^2.                  (4)
```

This is the correct Lanczos scaling law.  If `b_k` denotes the normalized Lanczos off-diagonal
coefficient, then `(4)` becomes

```text
D_N = nu_0^N product_(j=1)^(N-1) b_j^(2(N-j)),          (5)
```

not the sometimes quoted product with every `b_j` appearing only once.  Non-termination of the
thermal Krylov chain is exactly strict positivity of all leading moment determinants.

## Corpus value

The weak value relation

```text
normalizedPrimeArchMoment n = nu_n for every n           (6)
```

immediately discharges the source trace-Hankel hypothesis and proves RH through the existing Lean
consumer.  A finite thermal system cannot supply an infinite strictly positive determinant tower;
the useful source target is therefore either an infinite thermal spectrum or compatible finite
thermal approximants whose moment blocks converge to the canonical source blocks.

The strict version replaces the current opaque finite linear-independence premise with the physical
condition that every Lanczos coefficient is nonzero.  Formula `(4)` records the determinant values,
not merely their signs.

The finite-size statement is now formalized rather than left as prose.  If the state space has
cardinality `d`, the transition space has dimension `d²`, so

```text
det(nu_(i+j))_(0<=i,j<N) = 0 whenever d² < N.            (7)
```

Applying `(7)` back to the existing source consumer proves that no one fixed finite thermal or
finite KMS/Wightman system can satisfy `(6)` in every degree.  The exact finite-model capstones are
therefore logically valid but have an impossible premise; the growing finite-section limit is the
only live thermal interface in this corpus.

## Formalized corpus applications

- `HTGeometry.ThermalKrylovMoments` proves the odd-moment cancellation, the exact squared-gap
  moment-functional value, ordinary Hankel positivity, and shifted Stieltjes-Hankel positivity.
- `HTGeometry.FiniteKMSWightman` defines the canonical Gibbs partition and Wightman half-density,
  proves normalization, positivity, symmetry, and the exact geometric-mean value
  `w_ab² = p_a p_b`, and consequently removes the free weight-positivity and symmetry assumptions.
- `HTGeometry.ThermalKrylovDeterminant` constructs the finite Krylov vectors, proves their exact
  Gram values, proves the determinant/residual product, proves residual nontermination equivalent
  to finite linear independence, proves the corrected normalized Lanczos exponent law `(5)`, and
  proves the finite-rank determinant termination law `(7)`.
- `RHTower.PrimeArchThermalKrylovRH` applies the result to the general trace-Hankel sequence cone,
  to pointwise limits of growing finite thermal systems, to the prime--archimedean source
  hypothesis, and to the existing RH consumer.  Its canonical KMS specialization now leaves only
  thermodynamic convergence as a live route: `not_primeArchExactFiniteThermalEvenGapMoments` and
  `not_primeArchExactFiniteKMSWightmanMoments` formally rule out equality with one fixed finite
  system in every degree.  The packaged witness forms are also closed by
  `not_finiteThermalKrylovMomentSequence_normalizedPrimeArchMoment` and
  `not_finiteKMSWightmanMomentSequence_normalizedPrimeArchMoment`.
- `RHTower.PrimeArchThermalKrylovEquivalence` constructs the multiplicity-exact reciprocal-square
  Xi thermal truncations, proves their KMS realizability and convergence to their complete
  positive thermodynamic moment tower unconditionally, and reduces identification of that tower
  with the prime--Gamma source to the single second-moment inequality
  `xiThermalSecondMoment <= normalizedPrimeArchMoment 1`.  The opposite inequality is proved
  unconditionally, and equality is equivalent to RH.  Its scalar gap is exactly a strictly
  positively weighted version of the existing global reflection-defect energy.
- `RHTower.PrimeArchKrylovResidualRH` adds the previously missing strict complex producer, records
  exact determinant values for both the source and Xi central moment matrices, and rewrites both
  towers in the normalized Lanczos coefficients with exponent `2(N-j)`.

## Verification boundary

- The finite spectral identities `(1)--(4)` are unconditional finite-dimensional algebra.
- For arbitrary weights, Wightman symmetry remains explicit.  For the canonical Gibbs
  half-density it is proved from the exact formula, and Hermiticity of the observable is the only
  remaining input to odd-moment cancellation.
- Equation `(6)` is the source-comparison target and is not assumed to follow from generic thermal
  positivity.
- Numerical pre-certification on random finite Hamiltonian spectra confirmed odd-moment
  cancellation, positive squared-gap Hankel spectra, and determinant equality with the
  Gram--Schmidt residual product.

## Gates

- [x] physics value relation isolated
- [x] wrong Lanczos determinant scaling excluded
- [x] numerical pre-certification completed
- [x] finite Wightman spectral moments formalized in Lean
- [x] exact Krylov residual determinant factorization formalized in Lean
- [x] source-Hankel and RH consumers connected in Lean
- [x] canonical KMS/Wightman positivity and symmetry hypotheses discharged in Lean
- [x] fixed finite-system exact realization ruled out by source-level Lean declarations
- [ ] source-defined thermal spectral comparison constructed
- [ ] RH

## Current verification status

The finite-rank termination theorem and its two RHTower no-go consumers were added source-first on
2026-07-15.  They have not been checked by Lean: no Lean command, build, linter, numerical script,
or other computation was run under the active research constraint.  A later authorized check
should target only `ThermalKrylovDeterminant.lean` and `PrimeArchThermalKrylovRH.lean`.
