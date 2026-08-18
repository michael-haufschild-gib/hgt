# Xi-sampling card: §5 closed, §4 reduced (2026-08-18)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/prime-modulated-weyl-idealizer-collapse-on-xi-sampling.md`
Programme card: `docs/drafts/pipeline/1-in-progress/selberg-superlinear-xi-density-programme.md`

## §5 (27)–(31) CLOSED unconditionally

New: `formal/GaloisForLFunctions/RHTower/TwoDilationSpectralRepresentation.lean`.

**Do not rebuild Bochner–Schwartz.** The tree already owned it:
- `HTGeometry/SchwartzPositiveMeasureRepresentation.lean` — `existsUnique_temperateSpectralRepresentation`
  (nonneg + `MomentumSymmetric` ⟹ unique positive temperate spectral measure).
- `HTGeometry/SchwartzSesquilinear.lean` — `ContinuousSchwartzSesquilinearForm`, `IsNonnegative`,
  `MomentumSymmetric`, `momentumSymmetric_iff_derivativeSkew`, `hasDerivAt_translate_pair`,
  `translate_pair_invariant`.
- `RHTower/HedenmalmUniversalPositiveFormClassification.lean` — theta-null ⟹ support ⊆ `xiRealZeroSet`,
  atomicity, left radical, closability.
- `RHTower/TwoDilationDivisorMetric.lean` — `irrational_log_div_log`, `dense_closure_pair_of_irrational`,
  `eq_of_two_dilation_invariance`, `measure_compl_xiRealDivisor_eq_zero`.
- `RHTower/XiCSchwartzRestriction.lean` — `xiThetaSchwartzSource : 𝓢(ℝ,ℂ)` with
  `fourier_xiThetaSchwartzSource : 𝓕 xiThetaSchwartzSource t = XiC t`, and `continuous_XiC_ofReal`.

The ONLY missing step was `momentumSymmetric_of_two_dilation_invariance`: two multiplicatively
independent integer dilations ⟹ `MomentumSymmetric`. Proof pattern worth reusing: the orbit
`t ↦ Q (translateCLM ℂ t u) (translateCLM ℂ t v)` is differentiable everywhere by
`hasDerivAt_translate_pair`, hence continuous; `translateCLM_add` makes `log r`, `log s` periods;
`eq_of_two_dilation_invariance` forces constancy; `deriv = 0` at `0` is exactly `DerivativeSkew`.

## §4 (22) = `SuperlinearSamples xiRealDivisor` — NOT closed, but reduced

New: `HTGeometry/GridCancellationZeroCount.lean`, `RHTower/XiSuperlinearFromCancellation.lean`.
`GridCancellationSurplus f → SuperlinearSamples xiRealDivisor` for any continuous `f` whose zeros
are `Xi`-zeros; `clampAt δ` variant makes the per-cell bound automatic;
`xiSamplingIdealizer_collapse_of_grid_cancellation` restates `(23)`.

`SuperlinearSamples S := ∀ c, ∃ T ≥ 1, c*T < samplingCount S T` — a **limsup**, superlinear-only,
no-proportion target. Three relaxations vs Selberg, but still strictly beyond Hardy–Littlewood.

### Ruled out (do not re-attempt)
- Hardy theta-source blow-up: caps at `N₀(T) ≫ T^{3/4−ε}` (sublinear).
- Bochner positivity of `Ξ = 𝓕Φ`, `Φ > 0`: Gaussian/Fejér counterexamples, no zero density.
- Littlewood+Jensen on ζ: only `|β−1/2| ≥ δ` zeros; nothing on the line.
- Levinson with trivial mollifier: `(1/R) log L ≈ 2 > 1`, vacuous (CIS Appendix A, Corollary A).
- Gram-point route: parity-locked, needs a proportion **> 1/2** at Gram points, so it gains nothing
  from the superlinear-only slack. Grid device has no threshold — that is why it was chosen.

### The single crux (next brick)
`∫_T^{2T}|ζ(1/2+it)M(1/2+it)|² dt ≪ T` with `M = ∑_{m≤X} μ(m)m^{-s}P(log(X/m)/log X)`, `X = T^θ`,
`θ < 1/2` — the **asymptotic** product main term (Conrey's computation), not just a bound.
Assets: `Sieve/DirichletMVT.lean` (`dirichlet_meanValue_complex`, error `O(N log N)`; MV sharp `O(N)`
NOT owned), `Sieve/InghamMollifierSecondMoment.lean` (mollifier alone), `SmoothAFEZetaExact.lean`
(+`SmoothAFEZetaDirichletExpansion`), `HardyZ.lean`/`HardyZPhaseAsymptotic.lean` (polar
decomposition), `HTGeometry/NonstationaryPhaseLowerBound.lean` (**continuous first-derivative test /
van der Corput k=1, global and interval-local — already owned, use it**),
`EntireWeightedLittlewoodRectangle.lean` + `MeanValueBridge.lean` (Levinson contour + Jensen steps).
