# Route P facts (root)

- Literal matched-centroid excess atom is
  `w_n (centroid_n - 2 sqrt(n))`, with `w_n = Λ(n)/sqrt(n)`.
  From `centroid_n² = 4n + w_n²/4`, it is nonnegative and at most
  `w_n³/(16 sqrt(n)) ≤ log(n)³/(16 n²)` for `n>0`.
- The atom sequence is summable. The existing finite Route P
  `ccmActualHeadMatchedCentroidChebyshevExcess K` equals its prefix through
  `K+2`, is bounded by its total sum, and converges to that finite sum.
  Lean: `SPEQuantileRieszRoutePTerminalCentroidExcessSummability.lean`.
- Whole-route implication: at physical ratio one the nonnegative geometric
  correction is a finite constant, not a growing reservoir. The exact barrier
  remains `4 chebyshevError(x) + (mass-2 sqrt(x))² + 4 mass + O(1)`;
  its sign and the ordered-history graph intertwiner are still open.
- For normalized centroid variance, summable excess is amplified by
  barycentric recentering. Let `m_K` be critical mass, `p_K = ψ(K+2)`,
  `e_K` matched centroid excess, `q_K = Σ_{n≤K+2} w_n³/4`, and
  `c₀(n)=2 sqrt(n)`. Exact finite identity:
  `Var_K(matched) - Var_K(c₀) = q_K - (4 p_K e_K + e_K²)/m_K`.
  Lean: `SPEQuantileRieszRoutePIdealCentroidVarianceCorrection.lean`.
- `w_n→0` by `Λ(n)≤log n`, so Cesàro gives `m_K/(K+1)→0`.
  Unconditional PNT gives `p_K/(K+1)→1`; hence `p_K/m_K→∞`.
  Existing corpus cube summability bounds `q_K`, and the atom at `n=2`
  gives `e_K≥e₂>0`. Therefore
  `Var_K(matched) - Var_K(c₀)→-∞`, proved in
  `SPEQuantileRieszRoutePIdealCentroidVarianceEscape.lean`.
- Whole-route implication: finite local geometry is not negligible after
  global centering. Any cofinal nonnegative matched-minus-quantile variance
  must gain an unbounded compensating contribution from the ideal-minus-quantile
  term. This does not decide that term's sign or construct the ordered-history
  graph intertwiner; those remain the hard route obstacles.
- Equal-mass quantile cells tile one interval. Their normalized centroid
  variance is exactly `mass³/12 - widthCubePrefix/3`. Consequently the literal
  normalized prime-power history is `4 sqrtChebyshevMoment + 4 widthCubePrefix/3
  - (2 psi + centroidExcess)²/mass - mass³/12`.
  Lean: `SPEQuantileRieszRoutePArithmeticVarianceNull.lean`.
- Put `x=K+2`, `r=√x`, `μ=mass-2r`, `ε=psi(x)-x`, `e=centroidExcess`,
  `q=widthCubePrefix`, and `C=sqrtChebyshevMoment-(2/3)xr-rε`. Exact null law:
  `history/mass = 4C - 2re - (2ε+e-rμ)²/mass - (4r+mass)μ²/12 + 4q/3`.
  Thus linear endpoint mass error cancels; all remaining geometry except cubic
  width is negative. Lean: `SPEQuantileRieszRoutePWeightedChebyshevCredit.lean`.
- Finite Abel summation cancels terminal `psi(x)r` inside `C`:
  `C = x r/3 - Σ_{j<K} psi(j+2)(√(j+3)-√(j+2))`, equivalently deterministic
  lattice baseline minus the same Abel sum of `psi(j+2)-(j+2)`.
  Lean: `SPEQuantileRieszRoutePChebyshevAbelLattice.lean`.
- The geometric remainder `history/mass - 4C` tends to `-∞` unconditionally.
  Prime-two centroid excess gives a fixed positive lower floor, multiplied by
  `2√x`; cubic width is bounded and both square debts are nonnegative.
  Lean: `SPEQuantileRieszRoutePWeightedCreditEscape.lean`.
  Whole-route consequence: a nonnegative cofinal history must acquire growing
  signed Abel-integrated Chebyshev credit. Bounded-credit/geometry-only repairs
  cannot work. This does not establish the credit's sign or the independent
  ordered-history terminal graph intertwiner.
- Exact cross-route identification at `x=K+2`:
  `C = x sqrt(x)/3 - (x/2)·unitRieszVonMangoldtRenewal(x,x)` and
  `C = -(x/2)·criticalMellinChebyshevResolventSource(log x)`.
  Lean: `SPEQuantileRieszRoutePUnitRieszRenewalBridge.lean`. Corpus already
  proves the source has a zeta-log-derivative Laplace weld and RH-equivalent
  boundedness; the new equality identifies P's only signed credit with that
  source, not with a free graph correction.
- SP-E's existing literal completed quantile transport equals `x` times the
  same resolvent source, so `C = -transport(x)/2` exactly. Therefore
  `history/mass + 2·transport(x) -> -∞` unconditionally.
  Lean: `SPEQuantileRieszRoutePTransportHistoryEscape.lean`.
  Whole-route consequence: scalar P history and SP-E completed transport are
  linked but have an unbounded negative geometric mismatch. A cofinal ordered
  graph action must carry that mismatch plus the independent terminal
  connection; this result does not construct it or settle RH.
- The literal source transform on `Re z>1/2` equals
  `F(z)=(-(logDeriv zetaResidueUnit (z+1/2)+1)/(z+1/2)-2/3)/(z+1)`.
  This follows algebraically from the corpus's already-proved complex defect
  weld, without a new analytic premise. Hardy's theorem supplies a positive
  critical-line ordinate where `F` is not even continuous, by transferring the
  nonzero boost-current residue through the exact factorization.
  Lean: `SPEQuantileRieszRoutePSourceSpectralPole.lean`; axiom audit only
  `[propext, Classical.choice, Quot.sound]`.
- Whole-route implication: P's signed credit and SP-E's completed transport
  share a genuine imaginary-axis spectral singularity. Their scalar source
  cannot be replaced by a globally holomorphic positive proxy. Still open:
  a Landau proof that this forces cofinal signs of the literal source, transfer
  to integer apertures, physical diagonal sign, ordered terminal graph.
- Landau attack insight (not yet Lean-proved): existing low-height theorem
  `zetaResidueUnit_ne_zero_of_re_pos_abs_im_le_four` makes `F` holomorphic on
  the closed disk `|z-1|≤5/4`, reaching `Re z=-1/4`. If one source sign is
  eventual, tilt its nonnegative tail at `Re z=1` and apply the corpus's
  complex-MGF Landau transfer at radius `5/4` to force integrability at a
  negative real Laplace parameter. That would contradict the just-proved
  Hardy-axis pole. The compact initial correction and weighted-holomorphy
  transfer remain proof obligations.
- The required low-height analytic disk is now Lean-proved, not conjectural:
  `F` is analytic at every `z` with `Re z > -1/2` and `|Im z|≤4`, hence on
  `closedBall 1 (5/4)`. Lean:
  `SPEQuantileRieszRoutePLandauDisk.lean`. The disk reaches `Re z=-1/4`
  while staying clear of the `z+1`, `z+1/2` denominators and all zeta zeros.
  This supplies exact Landau continuation radius. Positive-measure MGF
  identification, compact initial correction, and Hardy-pole contradiction
  are still open.
