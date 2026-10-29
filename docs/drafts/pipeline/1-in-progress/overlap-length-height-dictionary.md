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

## Conjecture loop

1. **Scale algebra checked.** `OverlapCoordinates.lean` checked successfully and its olean was
   generated for the new dependent modules. It proves the exact bandwidth excess, fixed-overlap
   bandwidth limit, aperture cutoff, four-thirds overlap, and `-log c` diagonal loss.
2. **Transform normalization drafted.** `TheNormalizedAtomicTransform.lean`: raw versus unit-mass
   dilation; critical-line coefficient reweighting; no hard Fourier cutoff. Awaiting Lean check.
3. **Common-threshold conjecture fails at the SRT density calibration.** The actual source
   `PositionAndDepthShareOneNyquistAperture.lean` explicitly assigns density `L/π` to its paired
   lattice and threshold `a=L/2`. Matching `log T/(2π)` therefore gives `L=log T/2`,
   `a=log T/4`, cutoff `X=exp(2a)` with `X²=T`. The sharp agreement and negative-witness
   theorems in `DensityMatchedLengthHeightBoundary.lean` now pass Lean. All three main
   declarations have only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms.
4. **Separated-reference continuation classified on paper and drafted.** For every conductor
   `m≠1`, `completeWeilAdjunctionEnergy φ c m = E_m(1)-log c`; sign changes exactly at
   `c=exp(E_m(1))`. Any finite family of these modes is negative at one sufficiently large `c`.
   `OverlapForcesNewRamanujanTerms.lean` awaits checking. This concerns the reference formula,
   not the actual overlapping matrix. New interaction terms must change its spectrum.
5. **Still open work:** exact successor-shell geometry and divisor row laws; actual full-form
   positivity transport; super-Gevrey height reparameterization; census parameter comparison;
   completed documentation, umbrella integration, and transitive axiom audits.
6. **Census normalization:** `Zeta23.Params.X T = exp (λ log(T/(2π)))`, exactly
   `(T/(2π))^λ`, not `T^λ`. Therefore its physical overlap is
   `(T/(2π))^(λ-1)/(2π)`, and at `λ=4/3` equals
   `(T/(2π))^(1/3)/(2π)`. The normalized-height overlap is `(T/(2π))^(λ-1)`.
7. **Sharper certified plateau range already exists:** `OptimizedTransMetzlerFloor.lean`
   proves positivity for `c=1+δ`, `0≤δ<1/107520002048050000`, and the exact certified
   mass floor `1/25-2000δ(1+1024000(2100000+1/25))`. The report's `10^-18`
   range is a strict subset. This is a bound from existing estimates, not the actual sign boundary.
8. **Height reparameterization proof:** write `rβ(X)=loglog X (logloglog X)^β` and
   `T_N=N/rβ(N)`. Existing little-o estimates give eventually `1≤rβ(N)≤(log N)^2`.
   Hence `0≤log rβ(N)/log N≤2loglog N/log N→0`. It follows that
   `log T_N/log N→1`; two further logarithms preserve asymptotic equivalence.
   Positive real powers and products then give `rβ(T_N)/rβ(N)→1`.
   Thus `N~T_N rβ(T_N)`, while exact equality remains `N=T_N rβ(N)`.
9. **Revised §1.3 reread at user's request.** The revision now uses the certified `δ_*`
   and exact Steklov overlap schedule. Those are no longer omissions. It adds explicit shell
   descriptions at `c=1,3/2,2` and a Schur-complement interpretation. Still to audit:
   finite-horizon versus eventual shell statements, asymmetric logarithmic endpoints,
   the actual block decomposition and invertibility needed by the Schur complement.
   The Fourier Jacobian, SRT density calibration, census `2π`, and `-log c` issues remain.
   In particular `N log(1+1/N)<1` means the first exterior successor already enters at
   a finite-horizon overlap below one. The positive survivor should be an exact finite-horizon
   shell classification; fixed-`c` eventual absence is a different statement.

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

## No-go closure

The literal common-threshold inference is rejected by the calibrated model calculation above.
Its positive survivor is the exact cutoff classification `X²≤T`, including both position and
depth and the negative-witness converse. The survivor is checked and axiom-audited in Lean.
The unchanged separated reference is also unsuitable as an all-overlap positive reference;
its positive survivor is the exact per-conductor crossing law and finite negative-family theorem.

## Log

- 2026-10-29 — Read requested report and supporting ledgers; first corpus searches located existing
  transform factorization and dilation law. Existing unrelated working-tree changes preserved.
