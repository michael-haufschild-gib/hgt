# Degree-zero Selberg classification

- **ID:** selberg-degree-zero-classification
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Γ15
- **Statement:** A full Selberg function of presentation degree zero has coefficients equal to the Dirichlet unit; its conductor parameter and root number are both one. For the extended class, degree zero forces finite coefficient support.

## Proof

Since every Gamma scale is positive, degree zero means the Gamma product is empty. Write `γ(s)=Qˢ`. Away from zero and one, the functional equation becomes

`F(s)=r(s) conjugate(F(1−conjugate(s)))`, where `r(s)=ωQ^(1−2s)`.

The reflected expression is analytic near one because `F` is analytic near zero. Filling the value `F(1)=ωQ⁻¹ conjugate(F(0))` therefore gives an entire function `E`. Outside `|s|<2`, division of the original entire regularization by `(s−1)^m` increases no norm; compactness fills the omitted disk. Thus `E` has finite order.

Put `B=Σ|a(n)|n⁻²`. Absolute convergence gives `|E(s)|≤B` for `Re s≥2`, and reflection gives

`|E(s)|≤B exp(log(Q)(1−2 Re s))` for `Re s≤−1`.

The vertical edges of `−1≤Re s≤2` are bounded by `max(B,BQ³)`. Every finite-order bound is below the strip Phragmén–Lindelöf threshold: on a fixed strip, its exponent is polynomial in `|Im s|`, hence bounded by `D exp(c|Im s|)` for any `c>0`. Phragmén–Lindelöf therefore bounds the whole strip by a constant `C`.

Let `L=max(log Q,0)`. On each left flank `−M≤Re s≤−1`, the displayed reflection bound is at most `B exp(L) exp(2L)^M`. Choose the heights `T_k=k+1`; the central-strip bound satisfies `C/T_k²→0`. The existing variable-knot Perron support theorem now applies with every hypothesis derived, and gives

`a(n)≠0 ⇒ n≤exp(2L)=max(1,Q²)`.

Thus the extended-class degree-zero function has finite Dirichlet support, without a small-abscissa or quiet-sequence premise.

For the full class, differentiation of the Euler identity on `Re s>2`, followed by Dirichlet-series uniqueness, gives

`log(n)a(n) = Σ_{ij=n} a(i)log(j)b(j)`.

Take a prime `p` above the finite support and `n=p^k`, `k>0`. Every divisor `i>1` is a positive power of `p`, so `a(i)=0`; only `i=1` survives. Since also `a(p^k)=0`, the identity forces `b(p^k)=0`. Hence all Euler discrepancies from the Dirichlet unit are supported on finitely many primes. The arbitrary-Gamma finite-prime rigidity theorem, using the full class's strict Euler growth bound, gives `a=1`.

The entire function `E` agrees with one on the Euler half-plane, so the identity theorem gives `E=1` everywhere. Its filled value at one gives `1=ω/Q`; since `Q>0` and `|ω|=1`, both `Q` and `ω` equal one.

## Formalization

Namespace `GaloisForLFunctions.SelbergClass`:

- `DegreeZeroContinuation.lean`: `degreeZeroValue_analyticOnNhd`, `degreeZeroEntire`.
- `DegreeZeroSupport.lean`: `degreeZeroValue_bounded_strip`, `degreeZero_coefficient_index_le`, `degreeZero_finite_support`.
- `FiniteSupportRigidity.lean`: `coeff_eq_one_of_support_bound`.
- `DegreeZeroClassification.lean`: `rank_eq_zero_of_degree_eq_zero`, `coeff_eq_one_of_degree_zero`, `degreeZero_classification`.

The coefficient convolution is `RHTower.SelbergClass.logMul_coeff_apply` in `RHTower/SelbergClass/FullEulerLogPrime.lean`.

All five affected modules pass `lake --old env lean`; seven transitive axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`. New modules are wired into the Selberg-class umbrella.

The classification concerns the coefficients and canonical entire continuation. It does not prescribe a nonminimal pole regularization or its stored value at one. Γ15 remains partially solved in positive degree.
