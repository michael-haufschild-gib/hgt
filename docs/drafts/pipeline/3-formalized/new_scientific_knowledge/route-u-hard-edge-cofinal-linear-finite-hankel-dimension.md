# Route-U hard-edge cofinal linear finite-Hankel dimension

- **Stage:** 3-formalized
- **Route:** U
- **Status:** `[EXACT PAPER PROOF CLOSED] [LEAN FORMALIZED] [MODULE BUILD PASSED]`
- **Depends on:** `mass-shifted-hard-edge-paley-wiener-compactification`,
  `XiShiftedHardEdgePolynomialGaussianFiniteHankelCriterion.lean`,
  `XiShiftedParabolicDegreeHorizon.lean`

## Claim

Let `a_k=k+1`, `h_k=2/a_k`, and let the expanding cutoff index be `n`.  Put

```text
N(n,k) = (n+1)(k+1)+1.
```

If RH is false, one polynomial--Gaussian carrier and one cutoff index `n` have the following
cofinal property: for every sufficiently large `k`, the explicit finite Chebyshev packet truncated
at `N(n,k)` produces a negative shifted-Xi reciprocal-Hankel quadratic.  If `S(n,k)` is the exact
coefficient-vector size after reciprocal pullback, then

```text
a_k^2 < routeUParabolicDegreeHorizon * S(n,k)^2,
S(n,k) <= (n+1)(k+1)+2.
```

Thus false RH forces a cofinal negative family whose exact finite Hankel dimension is trapped on
the hard-edge scale `Theta(a_k)=Theta(sqrt(y_k))`.  This is the quantitative Lean closure missing
from the existing exact finite-witness criterion.

## Exact proof

1. `scaledUnitCutoff n` is supported where `|t| <= 2(n+1)`.  For
   `j >= N(n,k)`, one has `h_k(j+1)>2(n+1)`, so the sampled compact approximation is exactly zero.
   Hence `N(n,k)` is a valid finite-lattice cutoff, not an existential support radius.
2. Every term in the corresponding Chebyshev sum has degree `j+1 <= N(n,k)`.  Finite-sum degree
   subadditivity gives packet degree at most `N(n,k)`.  Reciprocal affine pullback does not raise
   degree, hence its coefficient-vector size is at most `N(n,k)+1`.
3. Failure of RH gives a negative polynomial--Gaussian Xi heat trace.  Expanding cutoff transfer
   preserves negativity for one fixed cutoff index `n`.  Complex hard-edge divisor convergence
   then makes the exact lattice divisor sum negative for every sufficiently large integer `k`.
4. Step 1 lets the exact finite Chebyshev/Hankel identity use the explicit `N(n,k)`.  Since
   `a_k^2>0`, negativity of the divisor sum is exactly negativity of the finite Hankel quadratic.
5. If `a_k^2 >= routeUParabolicDegreeHorizon*S(n,k)^2`, the parabolic degree-horizon theorem makes
   that same nonzero coefficient vector strictly positive, contradiction.  This proves the lower
   dimension bound.

No numerical evaluation, zero-location data, RH premise, or extra analytic assumption enters the
closed equivalence/disjunction capstone.  Conditional implications above are proof components;
the public capstone quantifies the false-RH alternative inside a closed proposition.

## Conjecture loop

1. **Arbitrary finite witness automatically gives `O(sqrt y)` dimension.** Failed: compact support
   was only existential in the existing witness theorem, so no dimension bound followed.
2. **Use exact cutoff support before Fourier sampling.** Proved: canonical support radius is
   `2(n+1)` and yields explicit `N(n,k)`.
3. **Dimension might still grow under reciprocal pullback.** Falsified: existing affine-pullback
   degree theorem is nonexpansive.
4. **Quantitative cofinal two-sided dimension law.** Proved in Lean by
   `XiShiftedHardEdgeCofinalLinearFiniteHankelDimension.lean`.

## Lean audit

- Direct `lake env lean` passed.
- Named `lake build GaloisForLFunctions.RHTower.XiShiftedHardEdgeCofinalLinearFiniteHankelDimension`
  passed `11977/11977`.
- Module is imported by `GaloisForLFunctions.RHTower`.
- Forbidden declaration/computation scan is clean: no `sorry`, `admit`, `axiom`, `opaque`,
  `unsafe`, `native_decide`, `#eval`, or `#reduce`.
- Every public theorem uses only `[propext, Classical.choice, Quot.sound]`.
- Repository lint was run and failed only on unrelated pre-existing/untracked modules not reachable
  from `GaloisForLFunctions.RHTower`; this module was not among the failures.
