# Overlap, polynomial length, height, and the complete Weil form

- **ID:** overlap-length-height-dictionary
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-2910/fable2.md`, §1.3; walls, route-obstacles, and route-unification ledgers.
- **Statement:** Identify atomic overlap with length divided by spectral height, with exact normalization, and transport the corpus's actual threshold and completeness theorems through this dictionary.

## Goal

Formalize the dictionary and its consequences without importing any unproved positivity,
prime-correlation estimate, or completeness assumption. Audit each inference against the current
Lean source. Retain the full prime, Gamma, and polar terms. Continue the conjecture loop from
each success or obstruction.

## Gates

- [x] 0 → 1: well-posed source comparison; existing transform factorization located.
- [ ] 1 → 2: dependency-closed paper arguments for each proposed extension.
- [ ] 2 → 3: individual `lake --old env lean` audits, transitive `#print axioms`, umbrella imports.

## Current evidence

`SpacingScaleHarmonicAnalysis/TheAtomicFamilyIsADirichletPolynomial.lean` already proves
`paperFT_atomicTest` and the complete zero-side summand factorization. Its convention is
`h_f(z) = ∫ f(u) exp(i z u) du`, `D_x(z) = Σ x_n exp(i z log n)`.

The literal formula in §1.3 omits the dilation Jacobian for unnormalized bumps. Calling the
Fourier window a cutoff must mean a scale of decay, not compact frequency support. A conventional
Dirichlet polynomial needs a coefficient reweighting and a sign change in the frequency.
The identity `N = T c_N` is exact; replacing the argument `N` in `c_N` by `T` needs an asymptotic
proof. Equal scale coordinates do not identify distinct quadratic forms or their quantifiers.

## Results and proof obligations

| Mathematical statement | Lean status / module |
|---|---|
| Exact overlap and bandwidth identities; fixed overlap has limiting bandwidth one | Checked: `OverlapCoordinates` |
| Raw transform has factor `w`; conventional polynomial has weights `√n x_n` at `1/2-iz`; no hard cutoff | Checked, axiom-audited, umbrella wired: `TheNormalizedAtomicTransform` |
| Paired-lattice density `log T/(2π)` gives sharp cutoff `X²=T`, with negative-test converse | Checked, axiom-audited, umbrella wired: `DensityMatchedLengthHeightBoundary` |
| Every nonpolar reference energy is `E_m(1)-log c`; exact crossings; actual diagonal error `O(c/N)` for `0<c≤N` | Audit pending: `OverlapForcesNewRamanujanTerms` |
| Census cutoff `(T/(2π))^λ`, physical overlap `(T/(2π))^(λ-1)/(2π)` | Checked, axiom-audited, umbrella wired: `CensusLengthHeightCoordinates` |
| Actual complete matrix at height `N/c`; fixed-`c` positivity for `0<c<1+δ_*` | Checked, axiom-audited, umbrella wired: `CompleteWeilLengthHeight` |
| Super-Gevrey overlap diverges, bandwidth tends to one, and `N~T_N rβ(T_N)` | Audit pending: `SuperGevreyLengthHeight`; dependency `SuperGevreyCriticalGrowth` fails compilation |
| Exact asymmetric shell radii and onset `N log((N+1)/N)<1`; eventual absence at each fixed `c<1` | Kernel checked, axiom-audited; final direct check pending: `ExactSuccessorShellWindows` |
| Actual successor divisor fiber divided by `log(N+1)` tends to a positive coefficient for every fixed `c>1` | Checked, axiom-audited, umbrella wired: `FixedOverlapHasLogarithmicDivisorRows` |
| Actual support aperture includes profile width: cutoff `N exp((b-a)w)` | Audit pending: `TheAtomicApertureRetainsTheProfileWidth` |
| Paid coordinate prefix at overlap `cM/N≤1`; exact Schur reduction retaining every mixed entry | Audit pending: `APositivePrefixGivesTheExactSchurReduction` |
| Gap `k` first becomes geometrically eligible at `N log(1+k/N)`, tending to `k` | Audit pending: `ExactHigherShellThresholds` |

Here `δ_*=1/107520002048050000`; the existing certified floor is
`1/25-2000δ(1+1024000(2100000+1/25))`. This is the range of the certified estimates,
not a classification of the actual matrix sign. The revised report already states this range
and the exact Steklov overlap schedule.

The Steklov receiver is not yet dependency-closed: direct compilation of
`SuperGevreyCriticalGrowth` fails in its moving-average construction and synthesis estimates.
Its printed receiver audit therefore contains `sorryAx` from elaboration errors. The proposed
length-height transport cannot be certified until this dependency is repaired and re-audited.

Remaining mathematical obligations: complete divisor-shell row decomposition; the self-energy loss along
growing overlap; whether the full matrix admits the proposed additive/shell Schur decomposition.
Entrywise signs and disjoint edge supports alone do not supply such a block decomposition.

**Aperture qualification.** A profile supported in `[a,b]` gives total atomic support
`[aw,log N+bw]`; centered aperture is `(log N+(b-a)w)/2`, with outer prime cutoff
`N exp((b-a)w)`. Plateau profiles use `[0,1]`, whereas `VanishesOff` in the completeness
theorems uses `[-1,1]`. The scale coordinate `c=Nw` must retain that profile convention.
Moreover SRT quantifies over all tests in an aperture, while atomic positivity quantifies over
one fixed-profile finite-dimensional family. A support inclusion does not place SRT's negative
witness inside that atomic family.

**Proved row law.** At every fixed `c>1`, the normalized downward divisor fiber from
row `N` to product `N+1`, for the explicit plateau profile, is asymptotic to
`(bumpCorr φ (1/c)/∫φ²) log(N+1)`, with strictly positive coefficient. This is the corpus's
weighted Schur row, with weights `n^(-1/2)`, not an assertion about an unweighted operator norm.

## Paper arguments

For `X,c>0`, `T=X/c`, so `log T=log X-log c` and
`λ=log X/log T=1+log c/log T`. At fixed `c`, division by the diverging `log T` makes
the excess vanish. At fixed `λ>1`, overlap instead equals `T^(λ-1)`.

The positive Fourier convention gives `h_(φ(·/w))(z)=w h_φ(wz)` by change of variables.
Translation supplies `exp(iz log n)`. Absorb `exp(log n/2)=√n` into coefficients to write
the usual Dirichlet polynomial at `1/2-iz`. A nonzero-mass compact profile has an entire
transform nonzero at zero; vanishing on any real tail would force it identically zero.

At matched paired-lattice density the existing exact agreement criterion becomes
`log X/2 ≤ log T/4`, equivalent to `X²≤T`. Above this boundary the existing negative
two-bump witness applies. At atomic touching `X=T>1`, this model is already beyond its
boundary. Thus the two thresholds cannot be identified under one density and cutoff convention.

In the existing separated reference formula, the common scalar is
`log(1/(2πc))+β(φ)/∫φ²`, while only conductor one receives the pole term. For `m≠1`
subtracting its value at `c=1` gives `-log c`. Exponentiation gives the exact crossing.
For a finite set `S`, choose `c=exp(1+Σ_(m∈S)|E_m(1)|)` to make every nonpolar energy negative.

For `rβ(X)=loglog X (logloglog X)^β`, `β>2`, set `T_N=N/rβ(N)`.
Existing little-o estimates give eventually `1≤rβ(N)≤(log N)^2`; hence
`0≤log rβ(N)/log N≤2loglog N/log N→0`. Thus `log T_N/log N→1`.
Two further logarithms, powers, and products give `rβ(T_N)/rβ(N)→1`.
The exact identity is `N=T_N rβ(N)`; height substitution gives asymptotic equivalence.

The exact upper and lower additive radii of a logarithmic window are
`a(exp w-1)` and `a(1-exp(-w))`. At overlap at most one, the existing boundary-star theorem
forces the only eligible unequal pair to be `(N,N+1)`. Its onset is
`N log((N+1)/N)`, between `1-1/N` and `1`. This yields the exact finite-horizon existence
criterion and the eventual absence theorem for each fixed `c<1`.

For a downward divisor fiber with product `ℓ`, the Schur weight cancels `√k`:
`(Λ(k)/√k)√(m/(ℓ/k)) = Λ(k)√(m/ℓ)`. Every divisor has the same logarithmic lag,
so the fiber equals `√(m/ℓ) logℓ · bumpCorr g(logℓ-logm)` by `Σ_(k|ℓ)Λ(k)=logℓ`.
For `m=N`, `ℓ=N+1`, `g=φ(·/(c/N))`, dividing by atom mass leaves
`√(N/(N+1)) log(N+1) · bumpCorr φ(firstExteriorOverlap N/c)/∫φ²`.
The first factor tends to one and the lag tends to `1/c`; continuity gives the conjectured
coefficient. The explicit plateau is positive throughout `(0,1)`, so its autocorrelation
is positive at every lag in `(0,1)`.

**Successor conjecture after the fiber law.** At fixed overlap, the full downward weighted
row should collapse to a local sum over products `ℓ`, with coefficient
`√(m/ℓ) logℓ · bumpCorr g(logℓ-logm)`. Once the support forces `ℓ≤2N`, every divisor
`k≥2` has quotient `ℓ/k≤N`, so horizon truncation removes no nonzero Mangoldt term.
This would identify the leading logarithmic row exactly, rather than bound it by Chebyshev.
Its relation to the positive archimedean overlap row is a further question about quadratic forms.

**Paid-prefix conjecture.** For the explicit plateau, the actual principal block on
`1≤n≤M` of the length-`N`, overlap-`c` complete matrix is the length-`M` matrix at
overlap `cM/N`. The corpus's uniform positivity through touching should therefore pay
this block whenever `M` is sufficiently large and `cM≤N`. This supplies a genuine Schur
reduction to the remaining coordinates, with every mixed prime, Gamma, and polar entry
retained. It does not identify additive edges with a vertex block or prove the residual sign.

**Higher-shell conjecture.** Among integer pairs `1≤a≤N`, `b≥a+k`, the minimum
logarithmic separation is `log(N+k)-log N`, attained at `(N,N+k)`. Thus gap at least
`k` enters exactly at `c=N log(1+k/N)`, which tends to `k`. This would classify
finite-horizon shell boundaries at every overlap, beyond the first-shell calculation.

## No-go closure

The literal common-threshold inference is rejected by the calibrated model calculation above.
Its positive survivor is the exact cutoff classification `X²≤T`, including both position and
depth and the negative-witness converse. The survivor is checked and axiom-audited in Lean.
The unchanged separated reference is also unsuitable as an all-overlap positive reference;
its positive survivor is the exact per-conductor crossing law and finite negative-family theorem.

