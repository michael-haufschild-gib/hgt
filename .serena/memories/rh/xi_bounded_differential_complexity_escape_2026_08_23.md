# Xi bounded differential-complexity escape (2026-08-23)

Module:
- `formal/GaloisForLFunctions/RHTower/XiBoundedDifferentialComplexityEscape.lean`

Theorem:
`differentiallyAlgebraic_of_tendstoLocallyUniformly_of_uniformFiniteMonomialRelation`.
If entire `F_k` converge compact-open to `f`, and each `F_k` satisfies a normalized nonzero polynomial differential relation inside one fixed finite injectively enumerated monomial window (fixed derivative-order / exponent bounds), then `f` is differentially algebraic. Proof extracts a convergent coefficient subsequence from a finite-dimensional compact ball, preserves nonzero limit by ℓ1 normalization, transfers all required jets using local-uniform derivative convergence, and passes the relation to the limit.

Xi corollary:
`not_tendstoLocallyUniformly_unitCentralXiC_of_uniformFiniteMonomialRelation`.
Since `unitCentralXiC` is hypertranscendental, any compact-open approximating model family must escape every fixed differential-complexity window.

Literature audit: finite algebraic state -> DA was already stronger in `HTGeometry/FiniteAlgebraicStateBoundary.lean`, so that conjecture was retired. Universal polynomial ODE results (Rubel/Duffin; Bournez-Pouly) concern weak/piecewise or real-axis C0 universality and do not supply compact-open holomorphic bounded-complexity approximation. Novelty status remains unverified, not claimed.

Isolated compile and olean build passed. Axiom audit only `propext`, `Classical.choice`, `Quot.sound`. Umbrella import added.