# Route-P irregular-RH trace-class relocation no-go

- **ID:** IRH-P-TRACE-RELOCATION-NOGO
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Source:** source-native Route-P prime-harmonic `det₂` carrier; Bertola–Bothner Fredholm/RH transport
- **Statement:** Canonically prime-marked depth-zero Route-P Stokes spectrum cannot be relocated to smooth Riemann--von Mangoldt spectrum, or to ordered Xi reciprocal spectrum, by an `ℓ¹` diagonal correction.

## Goal

Test first spectrum-moving escape from static Route-P divisor no-go. Irregular Riemann--Hilbert
tau functions are Fredholm determinants of trace-class integrable operators, and Hankel-composition
determinants admit matrix Riemann--Hilbert representations. Determine whether such a trace-class
correction can move the explicit Route-P genus-one spectrum to Xi without inserting Xi data.

## Gates

- [x] 0 → 1 in-progress: exact source and target sequences fixed; no fitted coefficient
- [x] 1 → 2 fully-proven: complete paper proof below; `[PROVED HERE]`; no open dependency
- [x] 2 → 3 formalized: Lean theorem, direct check, targeted build, and axiom audit pass
- [ ] 3 → 4 publication-ready: standalone note and external novelty review pending

## Audit

- `[CORPUS]` `routePPrimitive_GammaJulia_logPrimeHarmonicGenusOne` gives balanced source
  eigenvalues `±8w(p,e)`, where `w(p,0)=1/(4p)`; positive depth-zero eigenvalue is `2/p`.
- `[CORPUS]` `not_summable_routeKPrimeRVMReciprocal` and
  `routeKRVMQuantile_le_linear` give non-`ℓ¹` smooth RVM reciprocal spectrum and `T_n=O(n)`.
- `[CORPUS]` `tendsto_natCast_div_nthPrime` gives `n/p_n → 0`.
- `[CORPUS]` `summable_abs_xiOrderedPrimeReciprocal_sub_routeKPrimeRVMReciprocal` gives
  ordered Xi-to-RVM `ℓ¹` relocation.
- `[CORPUS]` Searches for `RouteP logPrime harmonic trace class perturbation eigenvalue
  relocation no go`, `Stokes genus one determinant trace class correction Xi`, and related
  spectral-density formulations found no theorem comparing this Route-P spectrum with RVM/Xi.
- `[LITERATURE]` Bertola, *The Malgrange Form and Fredholm Determinants*, SIGMA 13 (2017),
  proves analytic matrix-RH tau functions are IIKS Fredholm determinants; it supplies the
  trace-class deformation class, not an arithmetic Xi identification.
- `[LITERATURE]` Bothner, *A Riemann-Hilbert approach to Fredholm determinants of Hankel
  composition operators: scalar-valued kernels* (2022), supplies Riemann--Hilbert representations
  for Hankel-composition determinants and rank-one perturbations; no Route-P/Xi spectral weld is
  given.
- `[LITERATURE]` Suzuki, *Integral operators arising from the Riemann zeta function* (2020),
  constructs zeta Hankel/Fredholm operators from shifted Xi ratios and `exp(-2θ ξ'/ξ)`; it does
  not derive ordered Xi reciprocal spectrum by trace-class relocation of prime-harmonic Stokes
  atoms.
- `[NOVELTY STATUS]` No exact statement found in corpus or audited primary literature. This is an
  internal novelty result, not a claim of exhaustive external priority.

## Exact claim

Let `p_n` be the `n`-th prime, `T_n` the smooth Riemann--von Mangoldt quantile, and

```text
a_n = 1/T_n,
b_n = 8 w(p_n,0) = 2/p_n.
```

Then

```text
b_n / a_n -> 0,
sum_n |a_n-b_n| = infinity.
```

If `x_n` is ordered positive Xi reciprocal spectrum from the corpus, then

```text
sum_n |x_n-a_n| < infinity,
sum_n |x_n-b_n| = infinity.
```

The same statements hold after transport along canonical prime-index equivalence.

## Complete paper proof `[PROVED HERE]`

Write `C=2*routeKRVMBase*exp(1)>0`. Corpus bound gives

```text
T_n <= C(n+1).
```

For `n>=1`, `n+1<=2n`; hence

```text
0 <= b_n/a_n = 2T_n/p_n <= 4C n/p_n.
```

Prime number theorem consequence `n/p_n -> 0` and squeeze imply `b_n/a_n -> 0`.
Therefore for some `N`, every `n>=N` satisfies `b_n<=a_n/2`. On this tail,

```text
|a_n-b_n| = a_n-b_n >= a_n/2.
```

If `sum |a_n-b_n|` converged, comparison on tail would make `sum a_n/2`, hence `sum a_n`,
converge. This contradicts non-summability of smooth RVM reciprocals. Thus
`sum |a_n-b_n|` diverges.

Now let `x_n` be ordered Xi reciprocal spectrum. Corpus proves `sum |x_n-a_n|<infinity`.
If `sum |x_n-b_n|<infinity`, triangle inequality would give

```text
|a_n-b_n| <= |a_n-x_n| + |x_n-b_n|,
```

forcing `sum |a_n-b_n|<infinity`, contradiction. Prime-index transport preserves summability.
No RH assumption enters.

## Hostile audit

- Reordering escape: theorem intentionally fixes canonical prime marking used by both Route-P and
  ordered-RVM corpus operators. Arbitrary spectral permutation is not ruled out.
- Non-diagonal escape: theorem rules out diagonal trace-class relocation. A genuinely non-diagonal
  IIKS coupling can survive; operator-level eigenvalue matching would require a separate
  perturbation theorem.
- Genus escape: source and target are both Hilbert--Schmidt/non-trace-class. Obstruction is sharper
  than genus mismatch: their leading spectral densities differ beyond `ℓ¹`.
- Circularity: ordered Xi appears only in final transfer through already-proved Xi/RVM `ℓ¹`
  comparison; source/RVM obstruction is Xi-free.

## No-go closure

- **Exact killing theorem/mechanism:** Depth-zero Stokes eigenvalues are asymptotically negligible
  relative to smooth RVM reciprocal eigenvalues, leaving a non-summable RVM tail after subtraction.
- **Strongest positive survivor:** `[BRIDGE] [PROVED HERE]` Any viable irregular-RH transport from
  this Route-P carrier must contribute at genus-one scale in canonical prime marking, or mix prime
  sectors genuinely non-diagonally. A trace-class diagonal IIKS/Fredholm correction cannot carry
  missing arithmetic density.
- **New insight:** Arithmetic cannot live solely in a trace-class tau correction over explicit
  prime-harmonic Stokes background. Leading RVM density must be built into base wild operator or
  a non-diagonal interaction.
- **Status:** `[LEAN-PROVED]` in
  `RoutePPrimitiveGammaJuliaLogPrimeHarmonicTraceRelocationNoGo.lean`; capstone
  `routePPrimitive_GammaJulia_logPrimeHarmonic_traceClassRelocationNoGo`.

## References

- Marco Bertola, SIGMA 13 (2017), 046, https://doi.org/10.3842/SIGMA.2017.046
- Thomas Bothner, arXiv:2205.15007, https://arxiv.org/abs/2205.15007
- Masatoshi Suzuki, arXiv:1907.07302, https://arxiv.org/abs/1907.07302

## Log

- 2026-08-24 — corpus/literature audit, exact conjecture, hostile audit, complete proof; moved to
  `2-fully-proven`.
- 2026-08-24 — formalized exact RVM and Xi non-`ℓ¹` displacement theorem; direct Lean check and
  targeted module build pass; new declarations use only `propext`, `Classical.choice`, and
  `Quot.sound`; moved to `3-formalized`.
