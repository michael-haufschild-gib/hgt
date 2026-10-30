# Harmonic sieve mass is controlled by its Euler correction

- **ID:** harmonic-sieve-euler-comparison
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** For every finite prime sieve `Q`, write `δ=sieveDensity(Q)`, `L=sieveEuler(Q)-γ`, and `H_Q(N)=Σ_(n≤N,(n,primorial(Q))=1) 1/n`. Then `δ H_N≤H_Q(N)≤2δ(log(N+1)+2L+4)`. Consequently the harmonic class mass at a supported integer `a` satisfies
  `μ_Q(a)(log(N+1)-log a) ≤ H_Q(⌊N/a⌋)/a ≤ 2μ_Q(a)(log(N+1)+2L+4)`.

## Proof

Unique supported/coprime factorization gives the positive identity

`δ H_N = Σ_(a≤N, supported) μ_Q(a) H_Q(⌊N/a⌋)`.

Since `H_Q` is increasing and `Σ μ_Q=1`, this is at most `H_Q(N)`.

Choose `T=ceil(exp(2L+2))`. Then `log T≥2L+2`, `log T≤2L+3`, and the proved logarithmic-moment tail leaves at least half of `μ_Q` on `a≤T`. For `N≥1`, retain those factors in the same identity at horizon `TN`: each quotient horizon is at least `N`. Hence `H_Q(N)/2≤δ H_(TN)`. The elementary bound `H_(TN)≤1+log(TN)` proves the upper estimate. At `N=0` the claim is immediate.

For the class bounds, divide by `a`. The upper estimate uses `⌊N/a⌋≤N`. For the lower estimate use `H_k≥log(k+1)` and `(⌊N/a⌋+1)a≥N+1`, so `log(⌊N/a⌋+1)≥log(N+1)-log a`.

Thus, when `a²≤N+1` and `log(N+1)≥2L+4`, the class weight lies between `½ log(N+1) μ_Q(a)` and `4 log(N+1) μ_Q(a)`. Both sides retain the same sieve-density factor.

## Lean

`TheHarmonicSieveMassIsControlledByItsEulerCorrection.lean` proves `harmonicSum_eq_sum_sieveClassMass`, `sieveDensity_mul_harmonicSum_le`, `sievedHarmonic_le_density_log_euler`, `sieveClassDensity_mul_log_sub_le_mass`, `sieveClassMass_le_density_log_euler`, and `sieveClassMass_comparable_to_density_log`. Direct file check passed; transitive axioms: `propext`, `Classical.choice`, `Quot.sound`.

This compares the actual finite-horizon harmonic weights with the geometric norm used by the spectral-tail theorem. Exponential Ramanujan approximation and the signed complete-Weil reserve remain separate obligations.
