# Growing quadratic tests ignore finite relocation

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `fable.md`, §12.3, short mean values as single-zero detectors.
- **Lean:** `ArithmeticPositiveDuality/GrowingQuadraticTestsIgnoreFiniteRelocation.lean`.
- **Validation:** Direct `lake --old env lean` check passed; umbrella import added.

## Statements

Let `R` move two symmetric critical-line pairs to the quartet of `ρ`, and set
`Z(s)=ζ(s)R(s)`. For `P_T(t)=Σ_{k<N(T)} a(T,k) exp(iω(T,k)t)`, write
`E(T)=Σ|a(T,k)|²`.

1. On each fixed line `σ>1/2`, `σ≠1`, every nonnegative continuous weight
   bounded by `B(T)=o(T²)` preserves the quadratic mean on `[T,2T]`.
   In particular, normalized tests `E(T)≤1` with `N(T)=o(T²)` do so.
2. On arbitrary moving lines `3/8≤σ(T)≤5/8`, every test with
   `N(T)E(T)=o(T)` satisfies
   `T⁻¹∫_T^(2T) (|Z(σ(T)+it)|²−|ζ(σ(T)+it)|²)|P_T(t)|² dt → 0`.
3. Two actual critical-line donor pairs admit such a relocation with
   `Re ρ=3/4`, `Im ρ>0`, `R(0)=R(1)=1`, `Z(ρ)=0`, and the completed
   functional equation. Thus the class in statement 2 cannot detect this
   off-line zero even with pole normalization preserved.

## Proof

Put `w=s−1/2`, `d=ρ−1/2`. The numerator is
`(w²−d²)(w²−conj(d)²)` and denominator is
`(w²+γ₁²)(w²+γ₂²)`. Their difference is `Aw²+B`, with
`A=2((Im ρ)²−(Re ρ−1/2)²)−γ₁²−γ₂²`.
For `t≥2(|γ₁|+|γ₂|+1)`, every denominator factor has modulus at least
`t/2`. On `3/8≤σ≤5/8`, `|w|≤2t`; consequently `t²|R−1|≤D` uniformly.
It follows that `t²||R|²−1|≤(D+2)D` there.

On a fixed line, Carlson's theorem bounds the window mean of `|ζ|²`.
The tested difference is therefore `O(B(T)/T²)`. On the moving strip,
convexity at `η=3/8` gives `|ζ(σ+it)|²≤Ct`. Hence
`t ||Z|²−|ζ|²|≤C'` uniformly. Cauchy–Schwarz gives
`|P_T|²≤N(T)E(T)`, so the tested difference is `O(N(T)E(T)/T)`.
These estimates prove statements 1 and 2 without an assumed zeta bound.

For statement 3, use the existing actual donor ordinates and normalized
relocation target. Its target has real part `3/4`, positive height, and
`R(0)=R(1)=1`. The symmetric multiplier preserves the completed functional
equation and vanishes at its target. Statement 2 applies to this multiplier.

## Positive survivor and scope

The uniform estimate
`t ||Z(σ+it)|²−|ζ(σ+it)|²|≤C'` is the positive stability theorem behind the
obstruction, with explicit test-energy dependence. Lean declarations:
`exists_uniform_relocatedZeta_normSq_error_bound`,
`relocation_preserves_growing_trigonometric_tests`,
`relocation_preserves_short_tests_on_moving_lines`, and
`exists_normalized_relocation_invisible_to_short_tests`.

Relocation destroys ordinary Dirichlet-series structure. The theorem concerns
these tested quadratic means, not indistinguishability by arithmetic data or
all possible statistics. It does not assert a new global entireness theorem
for the pointwise rational formula at its removable donor singularities.
