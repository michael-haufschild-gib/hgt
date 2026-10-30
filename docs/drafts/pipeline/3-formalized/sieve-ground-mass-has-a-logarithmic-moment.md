# Sieve ground mass has a logarithmic moment

- **ID:** sieve-ground-logarithmic-moment
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** Put `μ_Q(n)=sieveDensity(Q)/n` on positive integers supported on `Q`, and `L_Q=Σ_(p∈Q) log p/(p-1)`. Then `Σ log(n) μ_Q(n)≤L_Q`; consequently `Σ_(n>T) μ_Q(n)≤L_Q/log T` for `T>1`.

## Proof

For a finite divisor-closed set `S` of supported integers, take the class vector with coefficients `b_n=1/sqrt(n)` on `S`. Splitting the symmetric prime kernel into its two directed halves gives

`Σ_(m,n∈S) b_m b_n K(m,n)=2Σ_(n∈S) log(n)/n`.

Indeed, each downward row includes every divisor of `n`, and `Σ_(d|n) Λ(d)=log n`. Positivity of the actual sieve operator above its Euler ground therefore gives

`Σ_(n∈S) log(n)/n ≤ L_Q Σ_(n∈S) 1/n`.

The class densities have total mass one by the proved ground-vector normalization. Multiply the last inequality by `sieveDensity(Q)>0`: its right side is at most `L_Q`. Every finite set of supported integers lies in a finite divisor-closed set of supported integers. Nonnegativity thus bounds all finite partial logarithmic moments by `L_Q`, proving summability and the stated infinite-sum bound. On `n>T`, use `log n≥log T>0` to obtain the tail estimate.

## Scope

`TheSieveGroundMassHasALogarithmicMoment.lean` proves the exact divisor-closed prime form in `primeForm_divisorClosed_sievePole`, summability in `summable_log_mul_sieveClassDensity`, the moment bound in `tsum_log_mul_sieveClassDensity_le`, and the tail bound in `tsum_sieveClassDensity_above_le`. Direct Lean check passed; transitive axioms: `propext`, `Classical.choice`, `Quot.sound`. Imported by the theory umbrella.

The tail estimate supplies the geometric cutoff needed for uniform harmonic-measure comparison. Finite-horizon conductor confinement remains unproved.
