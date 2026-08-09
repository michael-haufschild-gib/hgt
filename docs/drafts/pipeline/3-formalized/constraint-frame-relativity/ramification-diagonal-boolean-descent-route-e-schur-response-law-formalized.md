# Ramification-diagonal Boolean descent and Route-E Schur response — formalized

- **ID:** `cfr-ramification-boolean-route-e-response-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `ramification-diagonal-boolean-descent-route-e-schur-response-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellRamificationPower` | shared with the power-event card |
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.RamificationBooleanSupport` | new |
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.BernoulliBooleanGibbs` | new, reusable |
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.SchurCapacity` | new, reusable |
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.FiniteTiltResponse` | new, reusable |
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.BooleanGibbsCapacityResponse` | new |

All wired into `GaloisForLFunctions.HTGeometry`.

## New infrastructure

`BernoulliBooleanGibbs` builds the product Bernoulli law on `Finset ι` from one identity,
`bernoulliExp_prod` (`Finset.prod_add` read backwards), and derives the subset-occupation law
`E[1_{A ⊆ S}] = ∏_{p ∈ A} q_p`, the pair correlations, and

`bernoulliCov_linearStat : Cov(∑_{p∈S} a_p, ∑_{p∈S} b_p) = ∑_p a_p b_p q_p (1-q_p)`.

A corpus search for existing Bernoulli/Gibbs material found the *Gaussian-conditioned* Route-E
block (`RHTower/RouteEPhysicalShellParityEnergyRegression`) and the multiplicative Gibbs gas
(`RHTower/GibbsParityEnergyCovariance`), neither of which contains the finite Boolean product law
or its diagonal covariance.

`SchurCapacity` is the reusable two-row Gram layer: `capA/capB/capC`, `schurCapacity`, the
variational `IsLeast` characterisation, both forms of two-row Cauchy--Binet, and positivity.

`FiniteTiltResponse` is the reusable exact-response layer for a tilted finite law.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintFrameRelativity`.

Theorem 1.1 — exact squarefree pullback, card `(RB.2)`:

1. `unitalShellIndicator` — the unitalised stream `ã_m`.
2. `unitalShellIndicator_pow_self` — the boxed identity `ã_m(k^m) = μ(k)²` for `k ≠ 0`, `m ≠ 0`.
3. `unitalShellIndicator_pow_self_eq_one_iff` — the pulled-back support is exactly the squarefree
   integers, i.e. the Boolean divisor lattice.
4. `unitalShellIndicator_pow_self_eq_zero` — hard-core exclusion: `p² ∣ k` kills the value, which
   is card `(RB.4)`: occupying `p` twice produces exponent `2m`.
5. `logCoeffOperator`, `logCoeffOperator_shell_clock` — card `(RB.6)`: the logarithmic coefficient
   operator returns `E(k) = log k` on the active slice.

Card `(RB.5)`: the `ℤ/2` grading `μ(k) = (-1)^{Ω(k)}` on the squarefree slice is
`ArithmeticFunction.moebius_apply_of_squarefree`, used inside item 2; the card states explicitly
that the ordered Boolean boundary `(RB.5a)` needs an extra ordering datum and is *not* recovered,
so nothing is claimed for it.

Theorem 2.1 — exact Schur capacity and Plücker formula, card `(RB.7)`–`(RB.13)`:

6. `bernoulliWeight_occProb` — card `(RB.7)`/`(RB.8)`: the divisor Gibbs law `Z⁻¹ ∏_{p∈S} x_p` is
   exactly the product Bernoulli law of `q_p = x_p/(1+x_p)`.
7. `sum_bernoulliWeight` — total mass one.
8. `bernoulliCov_one_one`, `bernoulliCov_one_lam`, `bernoulliCov_lam_lam` — card `(RB.9)`:
   `Var N = A`, `Cov(N,E) = B`, `Var E = C` with `w_p = q_p(1-q_p)`.
9. `quadratic_expand`, `schurCapacity_le_quadratic`, `quadratic_eq_schurCapacity`,
   `isLeast_schurCapacity` — card `(RB.10)`: `D_F` is the least value of `Var(πN - tE)`, attained
   at `t = πB/C`.
10. `capA_mul_capC_sub_capB_sq`, `capA_mul_capC_sub_capB_sq_lt` — card `(RB.12)`/`(RB.13)`: the
    two-row Cauchy--Binet identity `det G = ∑_{p<q} w_p w_q (λ_p-λ_q)²`.
11. `schurCapacity_eq_ordered_ratio` — the boxed formula `(RB.11)`.
12. `capA_mul_capC_sub_capB_sq_pos`, `schurCapacity_pos` — strict positivity `(RB.11)`, from
    positive weights and distinct clocks.

Theorem 3.1 and Corollary 3.2 — exact intervention response, card `(RB.14)`–`(RB.21)`:

13. `tiltExp`, `tiltCov`, `hasDerivAt_tiltExp` — card `(RB.16)`: `d/dε|₀ E_ε f = Cov(r, f)`.
14. `hasDerivAt_tiltCov` — card `(RB.19)`: `d/dε|₀ Cov_ε(X,Y) = Cov(r,(X-EX)(Y-EY))`.
15. `hasDerivAt_capacityOfMoments` — the Schur combination `A - B²/C` differentiates to
    `A' - 2βB' + β²C'`.
16. `hasDerivAt_tiltSchurCapacity`, `hasDerivAt_booleanTiltCapacity` — the boxed response
    `(RB.18)`: `D_F'[h] = π² Cov(r_h, R²)` with `R = (N - EN) - β(E - EE)`.
17. `fugacityProb`, `fugacityVar`, `hasDerivAt_fugacityProb`, `hasDerivAt_fugacityVar` — the
    factorwise fugacity derivatives `q_p' = w_p s_p`, `w_p' = w_p(1-2q_p)s_p`.
18. `hasDerivAt_fugacitySchurCapacity` — the boxed response `(RB.21)`:
    `D_F'[s] = π² ∑_p w_p(1-2q_p)s_p(1-βλ_p)²`.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/BernoulliBooleanGibbs.lean       # clean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/SchurCapacity.lean               # clean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/FiniteTiltResponse.lean          # clean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/RamificationBooleanSupport.lean  # clean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/BooleanGibbsCapacityResponse.lean # clean
#print axioms  ⇒  propext, Classical.choice, Quot.sound
```
