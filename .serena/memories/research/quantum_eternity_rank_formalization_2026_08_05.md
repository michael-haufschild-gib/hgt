# Dense arithmetic instability of quantum eternity — formal status (2026-08-05)

Card `2-fully-proven/dense-arithmetic-instability-of-quantum-eternity.md`.
Formal status stays `[OPEN]`; only obligation 8 is left.

## Already in the corpus (do not rebuild)

- `rationalCoordinateRank`, `exists_linearIndependent_close`, `dense_exactRationalRank`,
  `rationalCoordinateRank_nowhereContinuous` — `ArithmeticTemporalRankInstability`.
- `exists_injective_exactRank_close`, `exists_simpleSpectrum_close_gapRank` —
  `SimpleSpectrumRankBridge` (already gives simple spectra: injective, nonzero gaps, exact rank).
- `exists_isHermitian_commuting_close_gapRank` — `SimpleSpectrumMatrixPerturbation`
  (Theorem B, operator form, L2 operator norm, same eigenvectors, commuting).
- `exp_skewAdjoint_sub_exp_skewAdjoint_norm_le`, `selfAdjoint_unitaryEvolution_norm_sub_le`,
  `selfAdjoint_heisenbergEvolution_norm_sub_le` — `FiniteHorizonCStarPerturbationLaw`
  (Theorem C in a general C*-algebra, no commutativity needed).
- `exists_hasBoxDim_closure_range_observedOrbit` — `SpectralObservedOrbitDimension`
  (completed observed orbit has box dimension = ℚ-rank of the visible gap set).
- `finiteTorusHaarProbabilityMeasure_anchoredProjectiveReturnTarget` —
  `AnchoredProjectiveReturnDensityLaw` (exact `(2 arcsin(ε/2)/π)^d` at maximal rank).

## Built this session

- `RationalRankStratumTopology` — Theorem A topology: rational hyperplanes are proper, closed,
  nowhere dense and Haar-null; `R_{n,k}` meagre + null for `k ≠ n`; `R_{n,n}` residual + conull but
  with empty interior once `n ≥ 2`; capstone `rationalRank_stratum_dichotomy`.
- `RationalRankHyperplaneAvoidance` — `exists_exactRationalRank_close_avoiding`: exact rank `k`
  arbitrarily close **and** off any finite family of proper affine rational hyperplanes.
- `ProjectiveExactReturnRankOne` — `hasPositiveProjectiveReturn_iff_gapRank_le_one` (an iff), plus
  dense periodic/aperiodic separation at spectrum and Hermitian-matrix level.

## The avoidance mechanism (reusable)

Perturb `y i ↦ y i + s * t^i * y i₁` with `s, t ∈ ℚ` and `y i₁ ≠ 0`.
- Span is unchanged when `1 + s * t^{i₁} ≠ 0` — lemma `span_add_rat_smul_eq`; the entry at `i₁` is
  rescaled by that factor, which recovers `y i₁` and then every `y i`.
- Each rational functional moves affinely in `s` with slope `P_c(t) * y i₁`, where `P_c` is the
  polynomial carrying the functional's coefficients (`ratPacketPoly`).  Choose `t` off the finitely
  many roots of the finitely many `P_c`; then each hyperplane is hit for at most one `s`.
- Pick `s` in a small `Set.Ioo` (infinite, since ℚ is densely ordered) minus that finite bad set.

- `TorusReturnExponentLaw` — obligation 8's measure/limit core:
  `finiteTorusHaar_return_sandwich` gives `(2a)^dim ε^dim ≤ m (S ε) ≤ (2b)^dim ε^dim` from a ball
  sandwich, and `tendsto_log_finiteTorusHaar_return_div_log` gives `log m / log ε → dim`.  The pure
  real-analysis step is isolated as `tendsto_log_div_log_of_power_sandwich`.

- `IntegerTorusReturnVolume` — closes obligation 8 completely.  Key move: **no bi-Lipschitz chart
  is needed**.  A nonsingular integer matrix `N` has trivial left kernel, so the Fourier
  coefficients of `orbitClosureHaar N` are those of Haar (`orbitClosureHaar_eq_haar`, via
  `probabilityMeasure_ext_of_mFourier_integral_eq`), hence preimages along `torusIntegerHom N`
  have unchanged Haar measure (`measure_preimage_torusIntegerHom`).  That gives the upper bound
  `m ≤ 4^τ ε^τ` globally and exactly; the lower bound `(2/rowBound)^τ ε^τ ≤ m` is just Lipschitzness
  of each character.  `exists_selectedSquare_det_ne_zero` supplies the nonsingular square selection
  from a spanning character family, so the capstone
  `tendsto_log_integerReturnPreimage_div_log_of_span` needs only minimality of the presentation.

## Open

Nothing formal.  All ten formalization obligations of the card are discharged unconditionally.
The card stays at Stage 2 for non-formal reasons: the positive finite-scale replacement law, the
collision-complete external novelty audit, the feasible protocol, and the Nature hostile review.

## Mathlib names worth remembering

`Submodule.finrank_mono` needs only `Module.Finite R t` (not a finite-dimensional ambient);
`Submodule.eq_of_le_of_finrank_le`; `finrank_span_singleton`; `Measure.addHaar_submodule`;
`Submodule.eq_top_of_nonempty_interior'`; `IsMeagre.mono`; `isMeagre_iUnion`;
`interior_eq_empty_iff_dense_compl`; `Rat.mul_den_eq_num`; `Set.Ioo_infinite`;
`Set.Infinite.sdiff` (not `.diff`); `Polynomial.finsetSum_coeff`, `Polynomial.eval_finsetSum`.
