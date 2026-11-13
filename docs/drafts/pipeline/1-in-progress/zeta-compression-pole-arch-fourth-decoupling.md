# Pole and archimedean terms in the fourth compressed source moment

- **Stage:** 1-in-progress
- **Type:** THEOREM (paper); Lean formalization in progress
- **Source:** `Zeta23/PrimeSideA/Defs.lean`, `PrimeSideA/Basic.lean`, `RHTower/ZetaWeightedGramIntegral.lean`.
- **Statement:** At bandwidth one, the literal full-line pole compression tends to zero in operator norm, and the archimedean compression tends to the identity in normalized Schatten fourth norm. The prime fourth-moment bound remains open.

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
- [ ] Concrete Lean sampling estimate and full-line pole bound: estimates pass; final vanishing corollary has one corrected algebraic step awaiting its source check.
- [ ] Concrete Lean archimedean normalized-fourth approximation.
- [ ] Direct source checks and transitive axiom audit.
- [ ] Prime centered fourth upper bound; remains unproved.

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

The actual archimedean matrix approximation and the prime/pole asymptotic
application remain unformalized; the matrix estimates alone do not assert them.
