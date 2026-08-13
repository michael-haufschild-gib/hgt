# universal-first-order-entire-cascade-unit-cost — Lean frontier (reconstructed 2026-08-13)

Card target: transcendental entire f_1..f_n, each P_k(z,f_k,f_k')=0 (nonzero polynomial) ⇒
ord_DA(f_n∘…∘f_1) = n. Upper bound + independence + sharpness + consequences all Lean-closed.

## Assembly point
`CascadeExactOrderUnconditional.exactDifferentialOrder_entireCascade_of_elimination_pos`:
only remaining input is `helim`: DA of order m<n for the cascade ⇒ nonzero polynomial state relation
(statePoly cascadeFamily P ≡ 0). Everything else unconditional.

## helim instances already closed (peel machinery)
- exponential tower: ExponentialTowerObservability (exactDifferentialOrder_expTower)
- polynomial-coefficient: ExpPolyAllHeights (exactDifferentialOrder_expPolyCascade_all)
- linear first-order: LinearCascadeInstances (exactDifferentialOrder_linearCascade)
- rational-coefficient linear: RatCascadeOrder.exactDifferentialOrder_ratCascade (2026-08-09), via
  RatCascadeLaw + RatCascadeInstance (ratExample). Peel interfaces: PeelStep/PeelInvariant/
  PeelLimitVector/PeelInduction (+ Affine, Pair variants), TerminalPowerCascadeInduction,
  ColumnPencilDeterminant.

## General (algebraic P(z,f,f')=0) case — what exists (all wired, built, post-card-log)
- Item 1 place: AlgebraicCascadePlace.exists_heightOneSpectrum_over_topInt (Q above degree-at-∞
  of topInt m; AlgCascadeField p = AdjoinRoot p over CascadeField).
- Item 2' different order: KummerDedekindDifferentOrder.not_mem_pow_aeval_derivative
  (aeval x (minpoly)' ∉ Q^e; 2026-08-09 15:50, newer than card log) + DVRDifferentRamificationBound
  + DifferentExponentTame (reused from stable-coframe campaign) + monogenicity chain
  (DedekindOrderMonogenic/QuotientPowerMonogenic/ProductMonogenic/DedekindLocalUniformizer/
  IdealQuotientTransport/SeparableFactorDerivativeOrder).
- Item 2 derivation bound: AlgebraicCascadeDerivationBound.valuation_uDeriv_le_of_mem_adjoin —
  v(p'(α)·δf) ≤ 1 for f in adjoin(topInt, root p), p monic integral coeffs; i.e. δ lowers order by
  ≤ ord(p'(α)). Uses AdjoinRootDerivationIntegral, TopDegreeSharpDrop.
- Reduction I analytic: Wiman–Valiron layer (2026-08-04): WimanValironSelection/SmallDefect/Radius/
  WindowEstimate/CleanBound, CentralIndex*, MaximumTerm*, TopSymbolReduction,
  TopSymbolWimanPlace.exists_radius_norm_topSymbol_le, WimanPlaceRoot.exists_radius_wiman_place,
  DiscreteJensenExp, MeanIndexComparison, BorelGrowthLemma, TranscendentalEntireOrderOne,
  EliminationOrderDescent, DifferentialJetPivotCore.

## What remains (item 3, the actual work)
Restate the peel/elimination over the extended datum: general first-order state satisfies an
algebraic (not polynomial-solved) law W: p(z, h, h')=0, so the cascade's jet field lives on
AlgCascadeField of the tower; the Bell/terminal-linear induction (TerminalPowerCascadeInduction,
card Reduction III) must run with the derivation extended to the algebraic extension, using the
derivation bound + different order to control degree drop (`v(∂_{X_m} f) ≥ v(f) + e` shape), and
Reduction I selects the place (which branch the cascade follows) via Wiman radii.
Template: RatCascadeOrder/RatCascadeLaw (rational case) — read these first, then extend.
Fact (Irreducible p) instances; synthInstance.maxHeartbeats trap noted in AlgebraicCascadePlace.

When general helim lands: assemble exactDifferentialOrder_entireCascade (no elimination hypothesis),
wire, build, axiom-audit, update card (many stale notes: gate line ~465, 'Lean status' superseded
block), promote to stage 3.
