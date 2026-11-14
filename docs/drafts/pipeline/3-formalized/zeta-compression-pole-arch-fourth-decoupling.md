# Pole and archimedean terms in the fourth compressed source moment

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `Zeta23/PrimeSideA/Defs.lean`, `PrimeSideA/Basic.lean`, `RHTower/ZetaWeightedGramIntegral.lean`.
- **Statement:** At bandwidth one, the literal full-line pole compression tends to zero in operator norm, changes the normalized prime fourth trace by `O(L⁻²)`, and the archimedean compression tends to the identity in normalized Schatten fourth norm. The prime fourth-moment bound remains open.

## Exact source

Write `L=log(T/(2π))`, `X=exp L`, `d=floor(LT/(2π))`,
`V c(τ)=Σ_{k<d} c_k φ̂(τ−τ_k)` and
`C_T(f)=(aL²)⁻¹ V* M_f V`. The actual normalized Gram matrix is
`C_T(μ)+C_T(Π_X)+C_T(P_X)`.

The existing taper estimates give `||V||²≤2πL`,
`∫r²φ̂(r)²dr≤M=8+2(cϱ/w)²`, and `|Π_X(τ)|≤3√X/(1+|τ|)`.
The first bound follows from Plancherel, `0≤φ≤1`, its support of length `L`,
and orthogonality of the grid exponentials.

## Full-line pole estimate

Split the integral at `J=[T/2,3T]`. On `J`, `|Π_X|≤6√X/T`.
Since every sampling center belongs to `[T,2T]`,

```
∫_{Jᶜ} Σ_{k<d} φ̂(τ−τ_k)² dτ ≤ 4dM/T².
```

Cauchy–Schwarz for the finite sum and `|Π_X|≤3√X` give

```
||C_T(Π_X)|| ≤ 12π√X/(aLT)
              +12dM√X/(aL²T²).
```

Thus the full-line pole norm is `O(√X/(LT))`, including the neighborhood of
zero where the uncompressed pole density is large.

For Hermitian matrices `P,Q`, put `p=||P||`, `q=||Q||`,
`v=tr(P²)/d`. Cyclic expansion and Schatten Cauchy–Schwarz give

```
|tr((P+Q)⁴−P⁴)|/d ≤ 4pqv+6q²v+4q³√v+q⁴.
```

The existing prime supremum and second-moment bounds give
`p=O(√X/L)`, `v=O(1)`. Consequently the literal pole contribution to the
normalized fourth trace is `O(L⁻²)` for `X≤T`; no prime fourth bound is used.

## Archimedean term

Put `B₀=(2πaL)⁻¹V*V`. The sampling bound and diagonal Plancherel identity give
`0≤B₀≤a⁻¹I` and `tr B₀=d`. Hence, for `a≥1/2`,

```
tr(B₀−I)⁴/d ≤ tr(B₀−I)²/d ≤ a⁻¹−1 = O(w/L).
```

The sharper pointwise decay also gives the tail bound
`3d cϱ²/(w²T³)`, but the existing second spectral moment already suffices.

On `[T/2,3T]`, the existing digamma estimate gives
`μ(τ)=L/(2π)+O(1)`. Outside this interval the same taper tail estimate,
with the existing linear growth bound for `μ`, gives a vanishing operator error:
on the complement, `|τ−τ_k|≥T/2`, so both `T` and `|τ−τ_k|`
are bounded by fixed multiples of `(τ−τ_k)²/T`.
Therefore `C_T(μ)−B₀=O(1/L)` in operator norm and
`C_T(μ)−I` tends to zero in normalized Schatten fourth norm.

The quartic inertia polynomial has the exact centered form
`q⋆(H)=(64/49)[(3/4)I+(1/4)(H−I)²−(H−I)⁴]`.
Separate cubic asymptotics are unnecessary when the centered fourth source
moment is controlled directly. The archimedean error itself tends to zero
unconditionally in normalized Schatten fourth norm. Minkowski then transfers
bounded fourth moments between the centered full source and the pure prime
source, with the same limits whenever those moments are bounded. No
unconditional boundedness of either fourth moment is asserted.

## Gates

- [x] Full-line paper estimates; no fourth-moment assumption.
- [x] Narrow corpus search: existing source identities and diagonal estimates; no matching operator-tail or fourth-decoupling theorem found.
- [x] Concrete Lean sampling estimate, full-line pole bound, and uniform vanishing: `ZetaSamplingPoleCompression.lean`; transitive axioms are `propext`, `Classical.choice`, `Quot.sound`.
- [x] Full-line archimedean density error `O(1/L)` and uniform vanishing: `ZetaSamplingArchimedeanCompression.lean`; standard axioms only.
- [x] Actual matrix pole-norm vanishing and archimedean normalized-fourth approximation: `ZetaSamplingCompressionMatrix.lean`; standard axioms only.
- [x] Actual prime second-moment bound and pole fourth-trace error: `ZetaSamplingPrimePoleFourth.lean`; standard axioms only.
- [x] Direct source checks and transitive axiom audits of all displayed estimates.

## Formalized matrix estimates

`ArithmeticCastelnuovoSeveri/FourthTracePerturbation.lean` proves the displayed
second-moment perturbation inequality (`norm_trace_fourth_perturbation_normalized`).
It also proves the fourth-moment perturbation bound
`|tr((P+Q)⁴−P⁴)| ≤ D(4a³b+6a²b²+4ab³+b⁴)` when the two Hermitian
fourth energies are at most `Da⁴` and `Db⁴`
(`norm_trace_fourth_perturbation_le_fourth`). This supplies the matrix estimate
for bounded-fourth-moment transfer. The exact centered polynomial identity and
finite positive-spectrum edge-defect estimate are formalized in the same module.
Its three main perturbation theorems pass Lean with only
`propext`, `Classical.choice`, `Quot.sound`.

`zetaSamplingCompression_archimedean_centered_fourth_small` in
`ZetaSamplingCompressionMatrix.lean` proves the actual archimedean approximation.
Its entries are the literal full-line
density integrals; the baseline trace is exactly the sampling dimension.
`zetaSamplingCompression_pole_uniformly_small` proves actual pole operator-norm
vanishing. `exists_zetaSamplingCompression_prime_second_bound` derives the pure
prime second moment from the established full-source trace theorem.
`zetaSamplingCompression_pole_fourth_error_le_inverse_bandwidth_sq` proves the
actual prime/pole fourth-trace estimate. Both declarations are in
`ZetaSamplingPrimePoleFourth.lean`; their transitive axioms are exactly
`propext`, `Classical.choice`, and `Quot.sound`.

The pure prime centered fourth upper bound remains unproved; none of these
results asserts it.
