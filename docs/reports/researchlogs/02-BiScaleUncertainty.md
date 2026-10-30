# BSU working log (mathematical facts)

Source: cat/02.txt (152786 lines, 668 files).
## KreinIncrementAndChordCascade
- h = autocorr f (real, compact continuous f). |h(x)| ≤ h(0); ∫(f(u+x) − f(u+y))² = 2(h(0) − h(x−y)).
- Chord √(h(0) − h(·)) subadditive (Peter–Paul with optimal t). Doubling h(0) − h(2x) ≤ 4(h(0) − h(x)); h(0) − h(mx) ≤ m²(h(0) − h(x)); dyadic 4^k.
- Zero node h(x₀) ≤ 0 ⇒ h(0)/m² ≤ h(0) − h(x₀/m); dyadic h(0)/4^k.
- Krein increment: (h(x) − h(y))² ≤ 2h(0)(h(0) − h(x−y)) (discriminant of ∫(D − tf)²). Zero node: h(x)² ≤ 2h(0)(h(0) − h(x − x₀)).
## MultiplicativeChainBesselAndOriginLeverage
- Orthogonal shifts (h(t_i − t_j) = 0) ⇒ Bessel Σ h(y − t_i)² ≤ h(0)². Adjoining origin (h(t_i) = 0): h(y)² + Σh(t_i ∓ y)² ≤ h(0)².
- Divisibility a|b ⇒ log b − log a ∈ log grid; dyadic coset {m2^k} is an orthogonal chain if h blind on log grid.
- Single zero node: (2 − √2)h(0) ≤ (h(0) − h(y)) + (h(0) − h(t₁ − y)).
- Origin leverage: sphere u₀² + Σu_i² ≤ R² ⇒ W₀(R − u₀) + Σw_i(R − u_i) ≥ (W₀ + Σw − √(W₀² + Σw²))R ≥ (Σw − Σw²/(2W₀))R. With W₀ = ω(y) ~ 1/y → ∞, full collar weight Σw transfers to increment energy.
## OptimalOriginAllocation
- Splitting origin weight W among blocks with sizes q_i: min Σ√(a_i² + q_i²) subject to Σa_i = W equals √(W² + (Σ|q_i|)²), attained by proportional shares a_i = W|q_i|/Σ|q|.
## OverlapSafeCollarMeasureTransport / LogarithmicCollarCoverage
- Collar substitution ∫_{(0,δ)}F(t∓y) = ∫ over one-sided collar (ℝ≥0∞, no integrability). Multiplicity-normalized shares partition unity on union of overlapping collars ⇒ exact transport of arch increment density (h(0) − h(x))e^{x/2}/sinh x onto collars.
- Adjacent log gaps log((n+3)/(n+2)) < log 2 ⇒ half-log-2 collars around log 2..log N cover (log2/2, log N) ⇒ exact decomposition: arch energy on (0, log N) = origin half-collar (0, log2/2) + normalized collars at each log k.
## SignedDyadicCollarPartition / IntegratedOriginCollarLeverage
- Nodes k+2 = 2^d·odd; nodes in one odd fibre comparable by divisibility ⇒ for a grid-blind source (h(log n) = 0, 2 ≤ n ≤ N) each odd coset is an orthogonal chain ⇒ origin sphere law per signed coset (left/right collars).
- autocorr of C_c source is continuous (convolution).
- Integrated leverage: kernel K_n(y) = ω(y) + collarMass − √(ω(y)² + blockNorm²) (shared origin across signed odd cosets, optimal proportional allocation), 0 < K ≤ collarMass, finite integral on (0, log2/2) despite ω ~ 1/y (rationalize). THEOREM: for every grid-blind C_c source, c_N h(0) ≤ ∫_{(0, log N)} (h(0) − h(x))ω(x) dx with explicit c_N = ∫K_N > 0 (bi-scale uncertainty: blindness on log grid costs archimedean energy). No regularity beyond C_c, infinite energy allowed.
## CollarAllocationDuality
- Shared-origin cost √(W² + A²) (A = Σ block Euclidean norms). Explicit marginal prices (dual slopes) radius·direction support the cost; remainder = radial curvature W²(B−A)²/(S(ST + W² + AB)) + Σ block-direction discrepancies ≥ 0; zero remainder ⇒ equal aggregate block norms. Adding capacity strictly improves the allocation kernel with loss ≤ final radial price; prices in [0,1), measurable, integrable at the singular origin.
## PhysicalCollarPartition
- General admissible partitions (measurable nonnegative shares supported on collars, summing to 1 on (log2/2, log N)); equal multiplicity is one. Each gives kernel ω + mass − √(ω² + blockNorm²) ∈ [0, mass], integrable; bounded by (n+1)·2·e^{log N/2}/sinh(log2/2).
- Every partition transports the same total collar mass = ∫_{(log2/2, log N)} ω.
## PhysicalCollarDualPrices / DualCertificate
- Dual prices pulled back to physical points; price floor = min over active collars. Exact dual gap: coeff(ρ) + gap(ρ) − coeff(η) = slack(ρ,η) + ∫remainder ≥ 0 for all admissible η. gap = 0 ⇔ complementary allocation (shares only on minimal-price collars) ⇒ optimal. optimalCoefficient(N) = sup over partitions, finite (≤ total mass), positive; ρ within gap(ρ) of optimum; zero-gap optimum rigid in aggregate block norm. N = 2 (one collar): every partition optimal, optimum = equal-multiplicity constant. Existence of optimizer for general N not asserted.
## PhysicalCollarHilbertAllocation (start)
- Shares as L²(interval; ℝ^{n+1}) with pointwise closed convex fibres (simplex on active collars, ‖v‖ ≤ 1); feasible set closed convex bounded.
- No relaxation gap: every feasible L² class repairs (on exceptional set, using equal multiplicity) to a pointwise partition with that class.
## PhysicalCollarHilbertPrices / HilbertAttainment
- Bounded measurable prices have L² representatives; inner product = physical cost integral. Dual prices give affine upper supports of the coefficient (exact at base); coefficient sublevels closed convex ⇒ weak compactness (HTGeometry closed convex attainment) ⇒ THE OPTIMAL COLLAR PARTITION EXISTS for every N (sup attained).
## SelectedCollarHilbertAttainment
- Same for an arbitrary finite subset s of nodes (selected weights, variable-mass objective, marginal price 1 − dual slope).
## PrimePowerGridCollarAttainment
- Any finite set P of prime powers at literal nodes log m: optimal selected partition exists (mass exactly on selected collar union, zero in gaps).
## PhysicalCollarSourceEnergy
- Every partition coefficient c(ρ) and the optimum: c·h(0) ≤ ∫_{(0, log N)} (h(0) − h)ω for every grid-blind C_c source (extended energy, no regularity). Monotone certificate max over smaller grids.
- c_N ≤ ∫_{x > log2/2} ω (N-independent); C² normalized: c_N ≤ Lévy(f)/h(0).
## PhysicalCollarCutoffMonotonicity / CutoffStability
- Optimal coefficient monotone in N (extend partitions; zero-padding preserves coset support function); limit c_∞ = sup exists, positive, ≤ tail mass. Retraction of larger partitions loses ≤ tail mass beyond log N − log2/2 ⇒ quantitative saturation 0 ≤ c_∞ − c_N ≤ 4e^{log2/4}/(√(N)(1 − 2/N²)) (O(N^{−1/2}), from ω ≤ (2/(1−e^{−2a}))e^{−x/2}). Any trial partition certifies c_∞ within gap + tail.
## PairedCosetSphereDuality / SignedCosetProductCoupling / ProductCoupledCollarHierarchy
- If source is blind through N ≥ K² then h(log a + log b) = 0 for a,b ≤ K ⇒ positive-offset coset ⟂ negative-offset coset ⇒ paired sphere (both signs share origin): support scale √(W² + A₊² + A₋²) instead of √(W² + (A₊+A₋)²); gain = 2A₊A₋/(sum of roots); attained by parallel blocks (finite relaxation sharp, realizability not claimed).
- Paired coefficient ≥ independent coefficient; product-coupled monotone certificate max(c_N, paired c_K for K² ≤ N), bounded by collar tail mass, converges.
## PairedCollarCapacity (start)
- Block Euclidean size monotone with increments ≤ added mass; three-coordinate radial √(W² + C² + D²) increments ≤ (C−A) + (D−B).
## PairedCollarCutoffStability
- Paired optimum monotone, same tail stability; limit = sup of paired optima. Largest admissible paired grid K = ⌊√N⌋ − 2 ⇒ fourth-root saturation: c_∞^{paired} − c_N^{prod} ≤ 16e^{log2/4}/N^{1/4}. ⇒ For C² grid-blind sources: Lévy(f)/h(0) ≥ c_∞^{paired} − 16e^{log2/4}/N^{1/4}.
## CappedBlockSupport / CappedCosetSphereDuality
- Capped disk support sup{Lx + Hz: x ≤ t, x² + z² ≤ 1} = √(L²+H²) if L ≤ t√(L²+H²) else Lt + H√(1−t²) (division-free, continuous, attained).
- Paired low-node constraints (opposite-sign low blocks only) reduce to two caps (t, √(1−t²)) on quarter circle; whole-block spheres retained; support attained in finite model; ≤ independent support.
## FullGridCappedCollarEnergy / CappedSupportComparison / CappedCollarArrayComparison / CappedCollarCutoffComparison
- Full-grid capped kernel: whole cosets through N keep their spheres; only low subblocks (nodes ≤ K, K² ≤ N) paired across signs. capped ≥ independent coefficient, ≤ paired (all-low endpoint = paired). Applies to actual grid-blind sources (C² ⇒ ≤ Lévy/h(0)).
- Capped support: l1-capacity increments; at fixed whole-block norm moving weight into capped low part decreases support (constraint growth vs capacity growth separated); monotone in low cutoff; zero-padding invariance.
## FullGridCappedCollarHierarchy
- Capped optimum c(N, K) monotone in both endpoint and low cutoff; paired(K) ≤ capped(N,K) ≤ paired(N); full-grid hierarchy with K = ⌊√(N+2)⌋ − 2 dominates product-coupled one, same limit c_∞^{paired}, same N^{−1/4} error; certifies Lévy(f)/h(0) for grid-blind C² sources.
## CappedSupportActivation / PhysicalCappedActivation
- Capped support = independent support ⇔ (max low fraction on + side)² + (max on − side)² ≤ 1 (activation index); binding cap gives quadratic deficit. Physical gain over independent kernel is integrable, zero ⇔ activation index ≤ 1 a.e.
## TwoColumnSchurGeometry (start)
- Two collar columns u,v with energies ≤ R² and pairing² ≤ (R² − E_u)(R² − E_v) (zero-lag Schur domain) invariant under rotations (Gram determinant and energy sum invariant).
## TwoColumnSchurSupport / DyadicSchurSupport / DyadicSchurCollarEnergy / SchurCappedCollarHierarchy
- Two-column Schur domain support = sum of singular values √(E_a + E_b + 2√det); polynomial IVT gives orthogonalizing rotation; = independent ⇔ columns orthogonal.
- Dyadic frame {0, log2, 2log2} with targets y, y+log2 (zero lag log 2): actual source zeros at log2, log4 give full residual determinant (not just spheres); optimized four-coordinate split support strictly beats sphere relaxation (example (1,1,1,0): < √3). Schur-capped kernel = max(capped, dyadic Schur) ⇒ monotone certificates dominating all previous, bounded by tail mass; limit ≥ paired limit (not identified with sharp infimum).
## SignedPhysicalGramEnergy (start)
- Full signed Gram (all node correlations incl. cross-coset entries) with origin anchor: kernel = h(0)(W + Σa) − √(h(0)·Gram) ∈ [0, 2h(0)Σa] (singular origin cancels); applies to ARBITRARY C_c sources (no grid blindness).
## SignedGramCapacity / CutoffComparison / CutoffHierarchy / DualSupport / PhysicalPrices
- Anchored Gram kernel = h(0)(W+Σa) − √h(0)·‖packet‖, packet = W·τ₀f + Σ aᵢ τ_{tᵢ}f in L²; triangle inequality ⇒ adding weights b ≥ 0 raises kernel by ∈ [0, 2h(0)Σb] (no sign/grid/origin condition); monotone in weights; zero extension invariant; kernel ≤ Σ aᵢ(h(0) − h(tᵢ)) (node deficits).
- Signed-Gram optimum over physical partitions is monotone in N; retraction loss ≤ 2h(0)·tailMass(N); normalized saturation error ≤ 8e^{R/2}/(√N(1−2/N²)) (inverse sqrt, source-dependent, ANY C_c source); limit ≤ Lévy(f).
- Supporting prices: slope = covariance/‖packet‖ ∈ [−1,1] (zero by total division at zero packet), price = (1+slope)/2 ∈ [0,1]; supporting-hyperplane remainder ≥ 0; dual remainder identity cancels singular anchor; prices pull back to both signed collar branches, transport exactly to physical location.
## SignedGramTrialCertificate
- Price floor = min of masked physical prices over active collars; exact dual gap identity: c(ρ) + gap(ρ) − c(η) = 2h(0)·slack(ρ,η) + ∫ remainder ≥ 0 ⇒ any trial ρ certifies optimum within gap(ρ) = 2h(0)·slack(ρ,ρ); gap = 0 ⇔ h(0)=0 or prices equal floor a.e. on active shares (complementary slackness). Limit error ≤ gap + 2h(0)·tail(N).
## DyadicDifferenceSource / DyadicAnchoredProducer / DyadicTriangularOptimality
- Concrete source: narrow smooth bump φ (support ⊂ (−log2/4, log2/4)), atoms = log2-translates orthonormal; source g = φ − φ(·+log2): h_g(0) = 2h_φ(0), h_g(log 2) = −h_φ(0) (negative adjacent correlation), edges e_j = atom_j − atom_{j+1}.
- Anchored packet edge0 + Σ (a_k e_{−k−1} + b_k e_{k+1}): ‖·‖² = h_g(0)/(m+1) + ‖packet − producer‖² for ALL signed coefficients; sharp minimum h_g(0)/(m+1), attained uniquely by producer = average of symmetric chains = triangular weights (m−k)/(m+1) ∈ (0,1]. Origin-anchored Gram minimum decays like 1/m: anchor cancellation possible for signed sources.
- Equality ⇔ coefficients exactly triangular on both arms (test vectors = partial atom sums).
## DyadicGramConditioning
- Concrete source realizes nearest-neighbour lattice kernel h(z log2) = h_φ(0)(2δ₀ − δ₁ − δ₋₁) (discrete Laplacian). Normalized anchored Gram minimum on dyadic nodes 2..2^m = 1/(m+1) = log2/(log 2^m + log2): LOGARITHMIC degeneration in cutoff N = 2^m. No uniform positive anchored bound even with nonnegative coefficients. (Anchored packet coefficients, not physical partitions.)
## SignedGramMinimumResponse / ResponseOptimality / ResponseLadder
- Pure response: least-index min-price active collar, measurable cells partition physical interval, shares ∈ {0,1}; attains linear minimum; gap(ρ) = max over η of linearized gain (attained); response exact gain = gap − ∫ remainder; improves ⇔ remainder < gap.
- Ladder: extend + accept-if-improves; monotone, produced limit ≤ optimized limit; error at n+1 ≤ min(gap, curvature remainder) + 2h(0) tail(n+1).
## RegularizedGramGeometry (start)
- Regularized scale √(packetScale² + (ε h(0))²) adds orthogonal coordinate; kernel differs by ≤ εh(0); quadratic remainder bound even at zero packet.
- Regularized remainder identity 2S_a·Rem = h(0)‖P_a − P_b‖² − (S_b − S_a)² ⇒ Rem ≤ ‖P_a − P_b‖²/(2ε) (augmented Cauchy–Schwarz; no packet positivity).
## PhysicalCollarMixture / PhysicalPriceResponse / RegularizedPhysicalGram / RegularizedGramDescent
- Convex mixtures of physical partitions are physical; packet displacement under mixture = τ·(P_ρ − P_η) (anchor cancels); ‖P_ρ − P_η‖ ≤ √h(0)(mass_ρ + mass_η).
- General CollarPrice (bounded measurable): floor = min over active collars; equal sharing among minimizers gives physical response attaining linear minimum; fibre cost transports to physical linear cost.
- Regularized coefficient within ε·R·h(0) of signed-Gram coefficient (R = collar radius); integrated curvature of mixture step ≤ (2h(0)·fibreMassBound·transportedMass/ε)·τ² ⇒ damped Frank–Wolfe ascent with quadratic error, no Gram coercivity.
## RegularizedGramIteration / QuantitativeGramProducer
- Frank–Wolfe with step 2/(t+2): competitor error ≤ 4·curv/(t+3); with ε = 1/(k+1) and explicit iteration count ⌈8·fibreMass·transportedMass·(k+1)²⌉, original signed-Gram error ≤ h(0)(R+1)/(k+1). Monotone ladder (max of extension, fresh producer) reaches limitingSignedGramCoefficient; normalized error ≤ (R+1)/(n+1) + 8e^{R/2}/(√N(1−2/N²)). Fully produced (constructive) certificate, any C_c source.
## RightNodeCollarPartition / CollarRadialPenalty / CollarMeshBounds
- Right-node allocation: above log 4 assign x to node ⌈e^x⌉; nonzero high fibres are left-sided (σ = false), y ≤ e^{−x}, (k+1)y ≤ 1 (mesh).
- Radial penalty √(W²+A²) − W ∈ [0, A], increment ≤ (2AG + G²)/(2W) (quadratic relative to origin weight); coefficient = transported mass − ∫ penalty (singular origin cancels inside difference). Block norm grows ≤ added mass.
- Mesh: ω(node_k ± y) ≤ 8/√(k+2); fibre mass ≤ 32√N; 1 ≤ 2yω(y) near origin; with mesh, array mass ≤ 64/√y (cutoff-uniform).
## ConcentratedCollarExtension / Retraction / LogarithmicArrayRadialComparison / ConcentratedCollarPenalty
- Splice partitions along measurable region; concentrated extension: keep old shares, fill added interval by right nodes ⇒ added signed density only at offsets y ≤ 1/N (left side). Concentrated retraction: keep old shares, fill missing fraction by right node ⇒ repair at y ≤ 2/N.
- Using 1 ≤ 2yω(y) (origin absorbs singularity) and √y-scaled masses: radial penalty increase ≤ 8192·1[y ≤ 1/N] (extension), ≤ 6144·1[y ≤ 2/N] (retraction) ⇒ integrated loss O(1/N).
## CollarEndpointTailMass
- ω(x) = 2e^{−x/2} + r(x), 0 ≤ r ≤ 4e^{−5x/2} for x ≥ R. Endpoint tail ∫_{log N}^∞ ω = 4/√N + O(1/N) (error ≤ 1/N). Transported mass = collarTailMass − endpointTail.
## SharpCollarCutoffComparison (start)
- Extension/retraction lose only inverse-cutoff radial budget ⇒ optimum difference = leading tail 4/√N + O(1/N).
- For N ≥ 8: tail(N) − tail(M) − 8192/N ≤ c(M) − c(N) ≤ tail(N) − tail(M) + 12288/N.
## SharpCollarAsymptotics
- |c_∞ − c_N − 4/√N| ≤ 12289/N; √N(c_∞ − c_N) → 4 exactly (independent signed-coset sphere relaxation). Grid-blind source bound: Lévy/h(0) ≥ c_∞ − 4/√N − 12289/N.
## ForcedFirstCollar / UniformPairedCollarGain / StrictPairedCollarLimit
- Below the node-3 collar edge, partition forces all share on node 2 ⇒ on fixed offset interval (I/3, 2I/3], I = log3 − log2 − R, both sign weights ≥ 1 for EVERY partition, cutoff ≥ 3.
- Paired radial gain ≥ 1/(W₀+2) when both sign norms ≥ 1 ⇒ explicit uniform gap g > 0: c(ρ) + g ≤ c^{paired}(ρ) for all ρ.
- STRICT: c_∞^{indep} + g ≤ c_∞^{paired} (coupling opposite signs strictly helps); product-coupled hierarchy eventually equals paired branch; eventually every grid-blind source has Lévy/h(0) > c_∞^{indep} + g/2.
## PairedArrayRadialGeometry / ConcentratedPairedCollarPenalty
- Paired norm √(S₊² + S₋²) ≤ block norm ≤ mass; unit capacity in added mass; paired radial penalty integrable; same 8192/6144 concentrated cutoff bounds for paired kernel.
## SharpPairedCollarComparison / SharpPairedCollarAsymptotics / FourthRootCutoffNormalization / SharpProductCoupledAsymptotics
- Paired optimum: |c_∞^{pair} − c_N^{pair} − 4/√N| ≤ 12289/N; √N(gap) → 4. Coupling gain (paired − independent) stabilizes at rate 24578/N (common leading tail cancels).
- Product-coupled hierarchy (source cutoff N, admitted ⌊√N⌋): eventually |c_∞^{pair} − c_N^{prod} − 4/N^{1/4}| ≤ 24586/√N; N^{1/4}·gap → 4 exactly. Grid-blind sources: Lévy/h(0) ≥ c_∞^{pair} − 4/N^{1/4} − 24586/√N eventually.
## MultiChainToeplitzGramCoupling
- Packet partition loss (Σ‖p_i‖)² − ‖Σp_i‖² = Σ pairwise Cauchy–Schwarz defects ≥ 0, = 0 ⇔ all positively aligned. Anchored remainder: (e^a/2)‖d‖² − ⟨d,p⟩ ≥ −‖p‖²/(2e^a) with exact square remainder.
- Gram origin leverage for ANY C_c f (no grid zeros): h(0)Σw − Σw h(t_i) − Gram/(2e^a) ≤ e^a(h(0) − h(y)) + Σ w_i(h(0) − h(t_i − y)); exact remainder ∫(e^a(f(·+y) − f) − P)²/(2e^a). Odd-dyadic node coords log(2m+1) + j log 2; Gram entries depend on dyadic exponent difference.
## TriangularGramSineBound
- chainSineFactor(n) = cos(π/(n+2)) < 1 (=1/2 at n=1). Split cross Gram M into strict upper triangular (nilpotent, index n+1) + lower-diagonal error F: |⟨Mx,x⟩| ≤ (cos(π/(n+2))‖M‖ + (1+cos)‖F‖)‖x‖² (sharp nilpotent numerical radius from RHTower.CCM). Synchronized frames: ‖Ac + Bc‖² ≤ (‖A‖² + ‖B‖² + 2cos‖A‖‖B‖ + 2(1+cos)‖F‖)‖c‖²; synthesis ‖·‖² ≤ ‖v₀‖² + Gram defect.
## SynchronizedCosetSineLeverage
- translationFeature f t ∈ L², ⟨τ_x f, τ_y f⟩ = h(y − x). Dyadic chain (base + i log 2); within-chain Gram/defect entries = h(log 2^{|i−j|}); cross-chain forbidden (lower) entries = h(log((2q+3)2^{i−j})) — exact integer-log samples (odd × dyadic). Second chain lies in coset of product (2m+3)(2q+3).
- Synchronized energy ≤ 2(1+cos)(h(0) + ‖within defect‖ + ‖triangular error‖)Σc²; gain over independent 4h(0)Σc²: 2((1−cos)h(0) − (1+cos)(defects))Σc². Sine-improved origin leverage with explicit grid-defect errors, any C_c f.
## ProfileStableCosetLeverage
- Separation margin m = (1−cos)h(0) − (1+cos)(‖D‖ + ‖F‖): ‖A x − B x‖² ≥ 2m‖x‖² (arithmetic nilpotence separates the two synthesis maps); lower frame bound (h(0) − ‖D‖)‖x‖²; stability under coefficient mismatch: ≥ √(2m)‖x‖ − √K‖x − y‖.
- Profile gain ‖x‖‖y‖(max(0, √(2m) − √K‖x̂ − ŷ‖))² ≥ 0; pair energy ≤ K(‖x‖+‖y‖)² − gain; gain > 0 ⇔ x,y ≠ 0 and √K‖x̂ − ŷ‖ < √(2m). Weighted identity ‖au + bv‖² = (a+b)(a‖u‖² + b‖v‖²) − ab‖u − v‖².
- True partition loss (‖Ax‖+‖By‖)² − ‖Ax+By‖² ≥ profile gain − 2‖D‖‖x‖‖y‖ ⇒ profile-improved origin leverage.
## AbstractBiScaleSystemAndSchurKreinCoupling
- Orthogonal family e_i with ‖e_i‖² = R: scaled residual Rx − Σ⟨e_i,x⟩e_i, ⟨res x, res y⟩ = R(R⟨x,y⟩ − Σ⟨e_i,x⟩⟨e_i,y⟩); Bessel; Schur–Krein: (R⟨x,y⟩ − Σ)² ≤ (R‖x‖² − Σ_x)(R‖y‖² − Σ_y).
- Autocorrelation version: residual waves h(0)f(·+y) − Σ h(y − t_i)f(·+t_i) for difference-orthogonal clique ⇒ (h(0)h(z−y) − Σh(y−t_i)h(z−t_i))² ≤ (h(0)² − Σh(y−t_i)²)(h(0)² − Σh(z−t_i)²); zero lag ⇒ collar inner product ≤ product of Bessel slacks.
## CosecantSecantDualDecomposition
- ω(x) = e^{x/2}/sinh x = 1/(2 sinh(x/2)) + 1/(2cosh(x/2)); dual ω*(x) = e^{−x/2}/sinh x = csch/2 − sech/2; ω = sech(x/2) + ω* (forward = smooth secant + functional-equation dual). Lévy energy = secant energy + dual Lévy energy, both ≥ 0.
- Secant intertwining: h_f(x)·sech(x/2) = (h_{cosh(·/2)f}(x) − h_{sinh(·/2)f}(x))/cosh²(x/2).
## HyperbolicMultiplierGramTransfer
- Packet correlation Σw h(t_i − y) ≤ √(h(0)·Gram) (any C_c). cosh/sinh multiplier Gram difference = Σ w_iw_j cosh(α(t_j−t_i)) h_f(t_j−t_i). Source zeros do NOT make sinh-multiplier off-diagonal entries vanish (parity breaks orthogonality inheritance) — measured clique defect.
- Compensated secant collar (with cosine-increment companion) ≥ h_cosh(0)Σv − √(h_sinh(0)·Gram_sinh); secant increment = h(0)(sech − sech²) + (cosh-increment − sinh-increment)/cosh² — sinh increment enters with minus sign (cannot discard companion).
## HyperbolicJumpEnergyTransfer
- Exact identity ∫ sinh(αu)sinh(α(u+x))(f(u) − f(u+x))² = 2(cosh(αx)h_s(0) − h_s(x)), s = sinh(α·)f. Support radius B: sinh-product ≤ envelope sinh(B/2)sinh((B+|x|)/2) ⇒ cosh(x/2)h_s(0) − h_s(x) ≤ env(x)(h(0) − h(x)) (uncompensated transfer).
- secant collar ≥ sinh-multiplier Gram bound (no parity/zero/clique hypothesis); secant kernel ≤ 2e^{−x/2}; secant energy integrable for C_c (no C²); disjoint periodic collars with step δ (δ = log 2 dyadic) ⇒ ∫_0^δ Gram bound ≤ biScaleSecantEnergy.
## PlasticCrossoverGramReceiver (start)
- Hyperbolic moment energy 2((∫f cosh(u/2))² − (∫f sinh(u/2))²).
- Plastic crossover (RHTower.WeilLevyCoshPlasticCrossover, threshold screwSignThreshold): P(f) = 2·jumpEnergy + hyperbolic moment; 2·plasticKernel − sech = remainder weight > 0 everywhere (core 4cosh(x/2) − sech, tail = dual Lévy ω*) ⇒ P(f) = secant energy + remainder (≥0) + moment ⇒ P(f) ≥ ∫ sinh-Gram bound + moment. Odd sources: cosh moment = 0, moment = −2(∫f sinh(u/2))² (negative), sinh multiplier even.
## OddMultiplierLeakageFamily
- Smooth odd six-packet family f_T (coeffs (−1,1,1,1,−1,−1), nodes ±(|T| + k log2)): h_f(0) = 6·packetMass fixed, h_f(log 2) = 0 exactly, but h_{sinh(·/2)f}(log 2) = 2 sinh(|T| + 2log2) sinh(log2/2)·∫cosh·packet² > 0, growing exponentially in T. ⇒ for any A, odd smooth source with zero at log 2 and sinh-correlation > A·h(0). Multiplier leakage unbounded relative to source energy (one node, not full grid).
## CenteredHyperbolicGramControl (start)
- Odd f: ∫cosh(2αu)f(u)f(u+x) = 2cosh(αx)h_{sinh f}(x) + cosh²(αx)h_f(x); centered source (cosh(2αu) − c)f gives exact cross identity; mixed packet |Σw∫q f(·+t_i)| ≤ √(h_q(0)·Gram_f).
- Odd sinh-clique defect = source correction (Σ over pair differences of weight·(c − cosh²)·h_f(diff)) + mixed packet of centered source vs difference packet ⇒ |defect − correction| ≤ √(h_centered(0)·Gram_f(difference packet)). Centered energy quadratic in c, minimized at source mean c* = ∫cosh(2αu)f²/h(0) (variance ≥ 0 by Cauchy–Schwarz). Centered jump bound ⇒ secant energy and odd plastic crossover receivers with only source data.
## ProjectedHyperbolicGramControl
- Mean-centered source is orthogonal to f; project difference packet off f ⇒ Schur residual Gram − cov²/h(0) replaces Gram; projected envelope ≤ every scalar-centered envelope (exact optimization lemma). On an exact source clique (all difference lags are zeros), corrections vanish and projection = mean-centering (no gain) — boundary.
## ArithmeticMultiplierCollisionControl (start)
- Chain nodes iδ: equal pair differences coalesce into lag amplitudes (aperiodic correlation Σ w_i w_{i+k}/(2cosh(αkδ))); center lag amplitude 0.
- Difference-packet Gram = h(0)·collisionEnergy (Σ lag amplitudes²) + crossLagError (h at integer lags (r−r')δ). Zeros at mδ for m ≤ 2N (doubled range) kill cross-lag error and source correction ⇒ |odd sinh-clique defect| ≤ √(variance·collisionEnergy); full log-grid blindness supplies doubled dyadic range (2^m). Variance = h(0)·h_centered(0).
## DyadicMultiplierFrameBound
- Lag amplitudes symmetric; at α=1/2, δ=log2: lag k amplitude² ≤ W²/2^k (cosh decay), collision energy ≤ 2W² independent of chain length N (W = Σw²).
- frameRadius = √(2·variance_{1/2}): grid-blind odd source ⇒ |defect| ≤ frameRadius·W ⇒ sinh-multiplier chain Gram ≤ (h_s(0) + frameRadius)·W (uniform Bessel/frame bound, NO multiplier zeros assumed). Unconditional version adds explicit source-error term. Frame jump bound ⇒ secant energy & odd plastic receivers.
## DyadicHyperbolicMomentControl (start)
- Coherent chain packet Σ g(u + i log2): integral = (N+1)∫g; support length ≤ 2(B+1) + N log2; Cauchy–Schwarz ⇒ (N+1)²(∫g)² ≤ span·Gram (moment controlled by Gram of long packets).
- Odd moment (∫f sinh(u/2))² ≤ momentBudget(N) (from frame bound + chain packet); with full log-grid blindness and uniform frame, (∫g)² ≤ log2·C (let N → ∞): odd moment² ≤ log2·(h_s(0) + frameRadius) — support radius disappears.
## FourthMomentJumpReceiver
- Fourth energy T = ∫sinh⁴(αu)f²; identity 4h(0)T = variance + 4h_s(0)² (cosh moments = h + 2h_s, h + 4h_s + 4T). Fourth envelope T cosh²(αx) + (T + h_s(0))sinh²(αx) bounds ∫(sinh·sinh)²(Δf)² ≤ 4·env (no support radius).
- Signed variational: for any a, 2a(cosh(αx)h_s(0) − h_s(x)) − 2a²·env ≤ h(0) − h(x). Fourth-Gram bound with control costs; radius-free odd secant/plastic receivers.
## OptimizedHyperbolicRayReceiver
- Ray along hyperbolic profile cosh((i log2 − y)/2): gain A = h_s(0)·Σprofile² − √(h_s(0)·frameUpper), cost D = Σ env·profile³/2; optimal scale A₊/(2D), certificate A₊²/(4D) ≥ 0 continuous; positive ⇔ h_s(0)·frameUpper < (h_s(0)·Σprofile²)²; on doubled zero range ⇔ frameRadius < h_s(0)(Σprofile² − 1). Feeds secant energy & odd plastic crossover with no free controls.
## SourceLatticeMultiplierFrame
- Compact sources have finitely many nonzero dyadic lattice samples h(k log 2). Row budgets: correlationMass Γ = Σ|h(k log2)|, correctionMass = Σ|correction samples|. Uniform multiplier frame for ANY odd C_c source (no blindness): Gram_sinh(chain) ≤ latticeFrame·W, latticeFrame = h_s(0) + correctionMass + √(2·h_centered(0)·Γ). Odd moment² ≤ log2·latticeFrame. Under dyadic zeros reduces to h_s(0) + frameRadius.
## SignedCoherentMomentReceiver
- Equal-weight packets keep signed cancellation: correction sum eventually affine (N+1)·signedMass − firstMoment (finite support). Coherent budget (signed instead of absolute correction) ⇒ odd moment² ≤ log2·coherentBudget; latticeFrame − coherentBudget = 2·negativeCorrectionMass ≥ 0; strict gain whenever one correction sample is negative; plastic receiver gains 4log2·negMass.
## RealizedCoherentCancellation (start)
- Outward six-packet source: energy 6·packetMass, h(log2) = 0, h(2log2) = −2·packetMass (negative second lag).
- Outward family: source mean grows ≥ c|T| (sinh leakage forces cosh moment up); correction sample at lag 2 becomes very negative ⇒ latticeFrame − coherentBudget ≥ gainSlope·|T| − const → ∞ at FIXED energy with zero at log 2. Realized arbitrarily large plastic certificate gain.
## CoherentSourceProjection
- Covariance of uniform difference packet with f eventually affine: (N+1)·covMass − firstMoment, covMass = Σ_k h((k+1)log2)/cosh((k+1)log2/2). Coherent producer = differencePacket/(N+1) − (covMass/h(0))·f; energy ≤ projectedEnergy + boundary/(N+1), projectedEnergy = 2Γ − covMass²/h(0) ≥ 0 (forced by producers).
- projectedBudget = h_s(0) + signedCorrection + √(h_centered(0)·projectedEnergy); odd moment² ≤ log2·projectedBudget; projectedBudget ≤ coherentBudget, gap·(sum of roots) = h_centered(0)·covMass²/h(0).
## LocalCoherentFilter (start)
- sourceCutoff L with 2B < L log2: all correlations of f and sinh f vanish beyond; centered pairing zero outside window (exact finite truncation). Symmetric filter Σ_{k<L}(f(u+(k+1)log2) + f(u−(k+1)log2))/(2cosh((k+1)log2/2)); filterCovariance = covMass exactly; filter energy = Σ_{k,l}(h((l−k)log2) + h((l+k+2)log2))/(2cosh·cosh) (difference & reflected-sum lags).
- Orthogonal filter (filter − cov/h(0)·f) has energy = filter Schur energy ≥ 0, orthogonal to f. Finite filter reproduces coherent multiplier slope EXACTLY: signedCorrection + ⟨centered, filter⟩ = 2Σ_{k<L} h_s((k+1)log2). Coherent sinh-chain Gram is EXACTLY affine beyond cutoff: (N+1)(h_s(0) + slope) − boundary. localBudget = h_s(0) + signedCorrection + √(h_centered(0)·filterEnergy) ⇒ odd moment² ≤ log2·localBudget.
## LocalFilterLatticeGain
- Filter coefficient energy 2Σ 1/(4cosh²((k+1)log2/2)) ≤ 13/9 (first coefficient² = 2/9 exactly, rest geometric) ⇒ filter energy ≤ (13/9)Γ < 2Γ ⇒ projectedEnergy − filterEnergy ≥ (5/9)Γ; explicit latticeGain = (5/9)h_centered(0)Γ/denominator ≤ projectedBudget − localBudget.
## HyperbolicVarianceRigidity
- h(0) = 0 ⇔ f = 0; centered source zero ⇔ f = 0 or (α = 0, c = 1) (no nonzero continuous f on a nontrivial cosh level set); variance > 0 ⇔ f ≠ 0 and α ≠ 0; Γ ≥ h(0); latticeGain > 0 ⇔ f ≠ 0; for odd part: strict plastic improvement ⇔ input not even.
## FiniteFilterSchurResidual
- Support escape: extreme translate of nonzero compact f lands outside supp f ⇒ filter nonzero outside source support ⇒ Schur residual after removing f and centered-source directions has positive energy ⇔ f ≠ 0; strict Cauchy–Schwarz ⟨centered,filter⟩² < h_centered(0)·filterEnergy; residualGain = √(...) − pairing > 0 ⇔ f ≠ 0 (odd part nonzero ⇔ input not even).
## FoldedHyperbolicCellDefect
- Fold s(log2·x) = sinh(·/2)f rescaled over Z: continuous 1-periodic; ∫_0^1 fold = moment/log2; ∫_0^1 fold² = Σ_k h(k)(lattice autocorrelation sum) = (localBudget − residualGain)/log2.
- EXACT: log2²·cellVariance = log2(localBudget − residualGain) − moment² ⇒ coherent moment bound equality ⇔ folded multiplier constant on the cell. Plastic receiver recovers both residuals.
## CoherentMomentAttainment (start)
- Two symmetric tents at ±2log2 (vanish near 0, fold to constant 1): attainingSource a = a·profile/sinh(u/2) is compact continuous odd with sinh-multiplier a·profile ⇒ attains coherent price; log 2 is the best universal coefficient.
- attainingSource a: fold ≡ a, moment = a log2, exact coherent price = log2·a²; universal coefficient c works ⇔ c ≥ log 2 (sharp constant).
## AnnularCoherentRetraction
- Canonical odd representative R(f) = attainingSource1·fold(f)(u/log2), supported in annulus log2 < |u| < 3log2, idempotent, preserves fold (hence moment, coherent price, cell defect) exactly; R(f) = R(g) ⇔ folds equal.
## CoherentKernelSplitting
- odd f = R(f) + K(f) uniquely, K(f) = zero-fold part (linear, idempotent, K∘R = 0); K(f) has zero moment and zero coherent price ⇒ P(K f) = secant + remainder ≥ 0 (plastic-positive). Explicit nonzero invisible family: energy a²·const while coherent price 0 ⇒ NO scalar c with h(0) ≤ c·coherentPrice (coherent price cannot control energy).
## PlasticCoherentLineMinimizer (start)
- jumpEnergy = 0 ⇔ f = 0; P(K g) = 2·jump > 0 for K g ≠ 0 (no plastic-null kernel direction). P(f + t g) exact quadratic: (1−t)P(f) + (t²−t)P(g) + tP(f+g). Fold linear.
- Coherent ray odd f + t·K(g) keeps fold/moment/price; P(ray t) = P(f) + 2t·pair + t²P(Kg); exact minimizer step −pair/P(Kg), gain pair²/P(Kg); square-defect global minimum on the line; strict iff pair ≠ 0.
## OutwardCoherentEscape
- Translate R(f)'s sinh multiplier by (n+4)log2, divide by sinh(u/2), take odd part: escapingSource(f,n) odd, support in annulus ((n+1)log2,(n+7)log2), SAME full fold (moment, price), energy ≤ 2·escapeEnergy/((n+1)log2)² → 0.
## CoherentFiberPlasticInfimum
- Coherent fiber = odd g with fold(g) = fold(odd f). On fiber: P(g) = 2·jump(g) − 2M², M = fixed moment; jump ≤ 2·(∫plastic kernel)·h(0). Escaping sources: 0 ≤ P + 2M² ≤ C/(n+1)² ⇒ inf over fiber = −2M² EXACTLY (IsGLB); attained ⇔ fold = 0 (zero source); fiber contains negative plastic values ⇔ M ≠ 0.
- KEY: the plastic crossover is not bounded below by 0 on odd sources; it is bounded below by −2·(odd sinh moment)², approached only by sources escaping to infinity with vanishing energy.
## ConfinedCoherentPlasticGap (start)
- Window radius (N+1)log2/2; tail = archLevyAntideriv(2R + threshold) > 0; confinementCost = (2N+1)sinh²(R/2). coherentPrice ≥ 0, = 0 ⇔ fold ≡ 0.
- Confinement (support in |u| < (N+1)log2/2): coherentPrice ≤ (2N+1)sinh²(R/2)·h(0); plastic tail coercive: tail(N)·h(0) ≤ jump ⇒ confinementGap = 2·tail·price/cost ≤ P(g) + 2M² for all confined fiber members; gap > 0 ⇔ fold ≠ 0 ⇒ every near-minimizer below the gap must leave the window (escape forced).
## AnnularCoherentEnergyBounds
- Tent partition reproduces folded energy: ∫profile(u)·fold(u/log2)² = coherentPrice. Representative energy ∈ [price/cost(5), annularFactor·price], annularFactor = 1/sinh²(log2/2); R linear; Lipschitz in folded L² distance. P(R f) + 2M² ∈ [gap, 2·potential·annularFactor·price]; P(odd f) + 2M² ≤ 4·potential·annularFactor·price + 2P(K f).
## DisjointCollarCliqueDivergenceAndTuransProblem (start)
- Periodic collar tiling ∫_{t0}^{t0+Kδ}F = ∫_0^δ Σ_k F(t0 + kδ + y). Zeros at mδ (1 ≤ m ≤ M) ⇒ arithmetic progression is difference-orthogonal clique. Weighted clique window bound; Beurling–Turán window: δ((M+1) − √(M+1))h(0) ≤ ∫_0^{(M+1)δ}(h(0) − h) ⇒ square-root cancellation ∫_0^{(M+1)δ} h ≤ δ√(M+1)h(0).
- Dyadic clique Lévy constant: zeros at m log 2 (m ≤ M) ⇒ dyadicCliqueLevyConstant(M)·h(0) ≤ Lévy(f).
## LogarithmicTuranWindowLaw
- Spectral form h(y) = ∫ρ(ξ)cos(2πξy), ρ = |f̂|² (via RHTower.WeilWorkPBAP). Zeros at mδ (1 ≤ m ≤ M) ⇒ FLAT Dirichlet energy: ∫ρ(ξ)D_{M+1}(θ − 2πδξ)dξ = (M+1)h(0) for every phase θ (only diagonal survives). D_K ≥ K²/4 within 1/K of 2πZ caps spectral mass of each arc. Cosine window ≤ T/max(1, 2πT|ξ|); covering by O(K) arcs with weights K/max(1,n) ⇒ harmonic sum.
- LOGARITHMIC window law: |∫_0^{(M+1)δ} h| ≤ 12δ(4 + log(M+1))h(0) (clique √(M+1) bound not sharp).
## LogarithmicTuranWindowSharpness (start)
- Quarter-shifted atoms ω_k = 2π(k+1/4)/A, A = (M+1)δ: mixture C(x) = (M+1)⁻¹Σcos(ω_k x) vanishes at mδ (telescoping); every atom contributes same sign to window ⇒ harmonic sum; wide envelope realizes it ⇒ ∫_0^{(M+1)δ} h ≥ (δ/4π)log(M+2)h(0). log is the TRUE order.
- Two-sided: best constant c_M in ∫_0^{(M+1)δ}h ≤ c_M δ h(0) lies in [log(M+2)/(4π), 12(4 + log(M+1))].
## FiniteSpectralEnvelopeRealization
- archFrequencyCost(ω) = ∫(1 − cos ωx)ω_arch(x) = gammaBracket(ω) − gammaBracket(0) EXACTLY (centered archimedean symbol). cos/sin modulation realizes h_f(x)cos(ωx); Lévy(cos) + Lévy(sin) = h(0)·cost(ω) + envelopeError, |error| ≤ Lévy(f) uniformly in ω.
- Finite nonnegative cosine mixtures realized by scalar compact sources with exact local correlations h_f·C on |x| ≤ A, energy ≤ h(0)·Σw·cost + Lévy(f)·Σw; polar version (∫h cosh(x/2) = 0) with ε tolerance; logarithmic-grid zeros transfer from cosine mixture zeros at log n.
## BroadSpectralCostRealization
- First moment ∫x·ω < ∞; compact C² ⇒ h(0) − h(x) ≤ M|x|; dilation f(δu) ⇒ normalized Lévy energy ≤ δK → 0 (broad sources have arbitrarily small normalized energy).
- ⇒ every finite spectral probability with cosine zeros at log n (2 ≤ n ≤ N) is approached FROM ABOVE by smooth compact polar grid sources: normalized energy < spectral cost + ε. Any valid polar finite-grid lower bound C ≤ every feasible spectral cost (realization direction of sharp spectral variational problem).
## HyperbolicPolarBalanceAndLevySinhFunctional (start)
- Under polar constraint ∫h cosh(x/2) = 0: weilArchRe = Ω(0)h(0) + Lévy; ≥ 0 ⇔ |Ω(0)|h(0) ≤ Lévy, |Ω(0)| = γ + π/2 + log 8π (bi-scale uncertainty inequality). Lobe decomposition h = h⁺ − h⁻, polar ⇒ hyperbolic lobe mass conservation.
- Lévy energy (biScaleLevyEnergy) = ∫_0^∞ (h(0) − h(x))·e^{x/2}/sinh x, finite for C²_c (via lintegral_levy_ne_top). weilArchRe = gammaBracket(0)h(0) + Lévy on polar hyperplane (pole eliminated). Polar–Lévy deformation identity with Lagrange multiplier μ: floor μh(0)cosh(x/2) where μcosh ≤ w.
## FoldedCollarIntegralAndObstructionResolution
- Explains RHTower even-sector single-point obstruction: zero at t₁ gives sphere h(x)² + h(t₁−x)² ≤ h(0)²; asymmetric points can have h(x) → h(0) only by forcing h(t₁−x) → 0. Weighted reflected pair: w_L(h0−h(x)) + w_R(h0−h(t₁−x)) ≥ (w_L + w_R − √(w_L²+w_R²))h(0) ≥ (2−√2)min·h(0).
- Folding [a, t₁−a] about t₁/2 ⇒ archFoldedCollarConstant(a,t₁)·h(0) ≤ Lévy(f), constant > 0 for 0 < a < t₁/2; ⇒ log-2-blind smooth even polar tests: weilArchRe ≥ (gammaBracket(0) + C_fold)h(0).
## SharedOriginMultiCosetLeverage
- Multiple orthogonal chains share the origin coordinate: support (√(W² + (Σ block norms)²))·R (sum of norms squared, origin charged once); attained by the sphere relaxation; rationalized form Σw − Q²/(2W); simultaneous dyadic-coset leverage under literal log-grid zeros (nodes m·2^k ≤ N).
## DistantCopyPolarEnforcement (start)
- Subtracting an exponentially attenuated distant translate cancels the cosh moment exactly; local normalized correlations unchanged; normalized energy changes by O(e^{−T}) ⇒ polar and nonpolar finite-grid classes have the SAME lower bounds.
- subtractCopy f − a·f(·−T): autocorr (1+a²)h(x) − a(h(x−T) + h(x+T)); exp moment multiplier (1 − a e^{sT}); a = e^{−T/2} kills ∫f e^{u/2} ⇒ cosh-polar. Energy change exact: (1+a²)Lévy + a·∫h(x−T)ω; normalized change ≤ C·e^{−T}. ⇒ polar_log_grid_lower_bound_iff: polar and full finite-grid classes have identical best constants (C^r, r ≥ 2).
## InfiniteGridTailRigidity
- Node ⌈e^T⌉ is within e^{−T} of T in log coords. Distant copy samples h near 0 at that node: e^{T/2}·h_{polarCopy}(log⌈e^T⌉) → −h(0) (universal negative tail). Dichotomy: h(0) = 0, or all distant polar copies have negative grid sample < −e^{−T/2}h(0)/2. Preserving the sample forces translation-square defect = 2h(0) at displacement ≤ e^{−T}.
## LogarithmicIncrementEnergy
- ω_arch antitone; translation chord ⇒ (h(0) − h(δ))·∫_δ^b ω ≤ 4·Lévy; ω(x) ≥ e^{−1/2}/x on (0,1] ⇒ e^{−1/2}(h(0) − h(δ))(−log δ) ≤ 4·Lévy (log modulus from Lévy energy). Grid lag ⇒ e^{−1/2}T(h(0) − h(lag_T)) ≤ 4·Lévy; distant copy preserving its first far grid sample pays Lévy ≥ (e^{−1/2}/4)·T·h(0) (linear in separation).
## LogarithmicCompressionEnergy
- ∫_a^∞ ω = log((1+e^{−a/2})/(1−e^{−a/2})) + 2arctan(e^{−a/2}) ≤ log(6/a) + π. Compression f(Lu): normalized energy ≤ A + 2 log L (radius-free), ≤ A + log L with support radius (coefficient 1).
## InfiniteGridPolarRecovery
- Compressed seed (support ≤ 1/(8(N+1))) + polar copy at logarithmic midpoint between log N and log(N+1): ALL infinite-grid samples h(log n) = 0 (n ≥ 2), exact polar balance, smooth compact; normalized energy ∈ [(e^{−1/2}/4)T, C + T], T = midpoint. ⇒ infinite-grid tail rigidity is nonvacuous and LINEAR-order sharp (polar sources blind on the whole log grid exist, cost ≍ log N).
## LogarithmicGridDistance / InfiniteGridDistanceClassification
- Nearest-node distance d(T) via floor(e^T); attained; d(T) ≤ e^{−T}; d > 0 ⇔ T off grid.
- Separated two-copy source blind on the whole grid ⇒ h_f(d(T)) = 0 (zero at the grid distance) ⇒ center must be OFF-GRID; energy ≥ (e^{−1/2}/4)(−log d(T)) for seed and copy. Converse: at every off-grid center a compressed smooth seed realizes all grid zeros + polar balance with energy ≤ C − log d(T). Exact classification: cost ≍ −log(distance to grid).
- Exact iff: separated smooth polar two-copy source blind on whole log grid exists ⇔ center T off-grid.
## FiniteTranslationTrains / FiniteCopyTailRigidity / FiniteTrainActiveLags / FiniteTrainGridClassification
- Finite translate source Σc_i f(u − t_i): autocorr = ΣΣ c_ic_j h(x + t_i − t_j). Copy train (spacing S > D+1): local short correlations = (Σc²)h(x); near full span mS only endpoint pair c_0c_m survives ⇒ grid zero near span forces seed zero at grid distance ⇒ energy ≥ (e^{−1/2}/4)(−log d(mS)) for seed & train; linear cost Lévy ≥ (e^{−1/2}/4)·mS·h(0).
- Lag coefficients A_k = Σ_{j−i=k} c_ic_j (aperiodic autocorrelation of coefficient vector); near kS: h_train = A_k·h(x − kS) (whole packet survives, individual pairs may cancel). Exp symbol B(β) = Σc_i e^{βiS}; B(1/2) = 0 ⇒ polar balance.
- EXACT classification: smooth compact seed + train blind on infinite log grid exists ⇔ every ACTIVE positive lag (A_k ≠ 0) has kS off-grid. Each active lag imposes its own −log(distance) energy cost.
## LocalCorrelationEnergyStability (start)
- If normalized correlations agree on [0, a], |normEnergy(g) − normEnergy(f)| ≤ 2∫_a^∞ ω (singular part cancels; independent of support/coefficients).
- Copy trains change normalized energy by ≤ 2∫_1^∞ω regardless of packet count; fixed bump realizes correlation radius ρ at cost ≤ C − log ρ.
## FiniteTrainUniformEnergy
- One constant C for ALL compatible finite coefficient patterns (S ≥ 2): normalized energy ∈ [(e^{−1/2}/4)(−log d_min), C − log d_min], d_min = smallest active-lag grid distance; polar if symbol vanishes.
## InfiniteGridUniformTail
- Krein increment (h(x) − h(y))² ≤ 2h(0)(h(0) − h(x−y)) + log modulus ⇒ e^{−1/2}(−log|x−y|)(h(x) − h(y))² ≤ 8h(0)·Lévy; uniform continuity radius for bounded normalized energy.
- Full infinite-grid blindness ⇒ e^{−1/2}|T|h(T)² ≤ 8h(0)Lévy (inverse-sqrt tail in T); uniform tail radius; dyadic window ∫_{log N}^{log 2N} h² ≤ 8log2·h(0)Lévy·e^{1/2}/log N.
## LinearKreinSmoothingAndInverseLinearGridTail (start)
- Two-point combos f(·+x) ± c f ⇒ (1+c²)(h(0)−h(z)) + c(2h(x) − h(z−x) − h(z+x)) ≥ 0. Progression smoothing S h(x) = m⁻²ΣΣh(x + (i−j)λ): |h(x) − Sh(x)| ≤ h(0) − Sh(0) (LINEAR, no square root; h − Sh positive-definite profile); one lag step moves Sh by ≤ 2h(0)/m; origin defect ≤ max progression increment ≤ 4e^{1/2}Lévy/(−log(mλ)).
- Claimed endpoint: T|h(T) − h(log⌈e^T⌉)| ≤ 32√e·Lévy + 2h(0) (inverse-LINEAR interpolation law), log modulus log(1/d)|h(x) − h(x+d)| ≤ 32√e Lévy + 2h(0); grid-blind ⇒ 1/|T| tail, ∫_T^∞ h² ≤ (32√e Lévy + 2h(0))²/T.
- PROVEN: linear log modulus log(1/|x−y|)·|h(x) − h(y)| ≤ 32√e·Lévy + 2h(0) for 0 < |x−y| < 1 (via progression smoothing with m = ⌈L⌉, L = −log d). Inverse-linear interpolation T|h(T) − h(log⌈e^T⌉)| ≤ same. Integer-log-blind cone: |T||h(T)| ≤ 32√e Lévy + 2h(0) for ALL T; ∫_T^∞ h² ≤ C²/T.
## LinearLogarithmicModulusSharpness
- archFrequencyCost(ω) ≤ log ω + 33/8 + π − 2θ'(0) (Stirling, RHTower.gammaHardyPhaseRate). cos/sin modulation of a nonnegative-correlation bump at ω = π/d: increments at d sum ≥ h_φ(0); energies sum ≤ h(0)(log ω + K) + Lévy(φ) ⇒ ∃ source with Lévy + h(0) ≤ 8 log(1/d)(h(0) − h(d)) at arbitrarily small d. Rate 1/log(1/d) and linear energy dependence jointly SHARP.
## PrimeBlindInverseLinearTail
- Window transfer: node n ∈ (e^T, e^T + e^{θT}] with h(log n) = 0 ⇒ (1−θ)T|h(T)| ≤ 32√e Lévy + 2h(0). Corpus Hoheisel θ = 71/100 (RHTower.Sieve...HoheiselEveryBase) ⇒ prime-blind sources: (29/100)T|h(T)| ≤ C beyond absolute T₀, ∫_T^∞ h² ≤ (100/29)²C²/T. (Prime-power blind = von Mangoldt term vanishes.)
## PoleInvisibilityOnGappedBlindGrids (start)
- RH ⇔ ZeroPoleBlindPositiveOn{n ≥ 2} (blind at every log n + zero pole mass ⇒ archimedean energy ≥ 0) — corpus theorem riemannHypothesis_iff_zeroPoleBlindPositive. GappedNodeSet: arbitrarily far T at log-distance ≥ 1/5 from all nodes. Distant pair b(u) − σb(u−T) blind on gapped set; pole term 2(1 − σe^{T/2})(1 − σe^{−T/2})m₊m₋ (≍ e^{T/2}, either sign); arch-without-pole bounded uniformly.
- On gapped node sets: (1) pole mass is free — every pole mass p carried by nonneg 𝒩-blind combination with |arch-without-pole| ≤ ε; (2) pole invisibility — every 𝒩-blind combination ε-close to one with zero pole mass; (3) NO-GO: ZeroPoleBlindPositiveOn 𝒩 fails for every gapped 𝒩 (uses RHTower.exists_blind_arch_add_mul_pole_neg: all-integer-blind combination with negative arch-only part); powers of one integer q ≥ 2 are gapped ⇒ single-integer blindness never suffices. Full integer grid has no gaps (e^{−T}-dense) and there positivity ⇔ RH.
## SquareRootDensityPoleInvisibility
- Sub-square-root window density: windows X ≤ log n ≤ X+1 with K nodes, M(K+1)(1+log(K+1)) ≤ e^{X/2} for every M. Pigeonhole free point at distance 1/(2(K+1)); compressed bump (L = K+1) distant pair: blind, pole ≍ e^{T/2}/L² either sign, arch part O((1 + log L)/L) ⇒ unit pole mass cost O(L(1+log L)e^{−X/2}) → 0 ⇒ zero-pole positivity FAILS. S-smooth integers (finite prime set S) have polynomially many nodes per window ⇒ sub-sqrt density ⇒ blindness at S-smooth integers never suffices; integers have ≍ e^X nodes per window, beyond threshold e^{X/2}: the pole weight e^{x/2} makes SQUARE-ROOT NODE DENSITY CRITICAL.
## CombinationSpectralDensity
- For nonneg combination c: G_c(r) = Σc_f|f̂(r)|²: ∫G = 2π·mass; ∫G·γ = 2π·archOnly(c); ∫G cos(r log n) = π√n·nodeValue(n). Blind at all powers of q ⇒ phase r log q mod 2π UNIFORM for even continuous observables (uses RHTower.BlindPrimePowerSlack / PrimeCirclePeriodization). Spectral coordinates turn blind symbol slack into a moment problem.
## ExactSingleIntegerBlindSymbolSlack (start)
- m_q = (log q/π)∫_0^{π/log q} γ (period mean of archimedean symbol γ = gammaBracket). Bathtub lower bound: blind at powers of q ⇒ archOnly ≥ m_q·mass (γ dominates its fold). Attainment via midpoint atoms ω_k = (k+1/2)π/(N log q): Σcos(ω_k j log q) = 0 for 1 ≤ j < 2N; midpoint γ sum ≤ N m_q + γ(π/ℓ) − γ(0); stretched envelope O(1/N) ⇒ m_q attained at rate O(1/N). Pole invisible on powers ⇒ zero-pole blind symbol slack on powers of q = −m_q EXACTLY, same as without pole. q = 2 gives the smallest gap.
- Pair combination of cos/sin modulations at frequencies ω_k: mass N·h(0), node value 2h(log n)/√n·Σcos(ω_k log n), archOnly ≤ h(0)Σγ(ω_k) + N·Lévy. Proven: BlindSymbolSlackOn(powers q) M ⇔ ZeroPole version ⇔ M ≥ −m_q. Pole constraint does NOT improve single-integer bathtub. m_q ≤ m₂ (mean of γ over [0,a] increasing in a); corpus dyadic constant twoPeriodMean = m₂.
## IncidenceGainOfTheSingleIntegerBathtub (start)
- Adding blindness at one extra n: if n power of q, nothing changes; if multiplicatively independent, explicit strict gain A(c) ≥ (m_q + |s|/C)mass, s = sin(π log n/ℓ)/(π log n/ℓ) ≠ 0.
- Mechanism: folded radius ρ(r) = ‖rℓ mod 2π‖/ℓ; powers-blind ⇒ ∫G cos(tρ) = s∫G; n-blind ⇒ ∫G cos(rt) = 0 ⇒ |s|∫G ≤ ∫G|cos(rt) − cos(tρ)|; pointwise |cos(rt) − cos(tρ)| ≤ C(γ(r) − γ(ρ(r))) via crossing slope κ(ℓ) = (π/8ℓ)/(1/16 + π²/ℓ²)² from first Gauss term of γ. Gain depends on arithmetic incidence (multiplicative independence), not spacing. Example 2^k & 3: slack −m₂ − η₂₃ strictly below dyadic. On gapped sets zero-pole slack = slack.
- Incidence gain η(q,n) = |s|/C > 0 iff n ∉ powers of q. blindSymbolSlack_two_three: full-grid BlindSymbolSlack(−m₂ − η(2,3)) — full integer grid strictly beats dyadic bathtub. Gapped sets: ZeroPole slack ⇔ slack (pole invisible).
## PowerNodeRemovalLaw
- Folded symbol F(z) = γ(‖z‖/ℓ) on R/2πZ, cosine coefficients φ_d. EXACT: blind slack on {q^j : j ≠ d} is −(m_q − |φ_d|) — node q^d is worth exactly |φ_d|; same with zero pole.
- Lower bound: blind off q^d leaves one free cosine moment c; phase measure = (∫G + 2c cos(dz))dz/2π (Fourier uniqueness on circle, via HTGeometry.addCircle_measure_eq_of_fourier_integral_eq); positivity ⇒ 2|c| ≤ ∫G. Upper bound: translated pairs f ± f(· − dℓ) multiply spectral density by 2 ± 2cos(dℓr). Far nodes cheap: |φ_d| ≤ (γ(π/ℓ) − γ(0))/d.
- Removal law upper bound: translated pair combination doubles mass, kills q^j (j ≠ d) via cos-addition with (j±d) moments; symbol moves by s·φ_d up to the bathtub defect |X − 2π mass φ| ≤ 2π(archOnly − mass·m_q). Removal law also for zero-pole (gapped subset). φ_d = (ℓ/π)∫_0^{π/ℓ} γ(v)cos(dℓv)dv.
## PowerOrbitLaw
- F_d(z) = (1/d)Σ_{k<d} F(z + 2πk/d) orbit average of folded symbol. EXACT: blind slack on {q^j : d ∤ j} is −min_z F_d(z) (also zero-pole).
- Lower bound: blindness off multiples of d kills Fourier coefficients off dZ ⇒ phase measure rotation-invariant by 2π/d (Fourier uniqueness) ⇒ folded symbol integrates to orbit average ≥ min. Attainment EXACT design (no discretization error): atoms at folded radii of orbit θ*+2πk/d of minimizer; Σ_k cos(α + 2πjk/d) = 0 for d ∤ j; wide envelope with normalized energy < ε. Powers of q^d are worth exactly m_q − min F_d.
- min F_d ≤ m_q (powers of q^d have nonnegative value).
## CircleCosineDesigns
- Design = finite weighted angles; moments Σw cos(jθ). Quadrature: uniDesign (N equal points) has zero moments 1 ≤ j < N; dirDesign weights (1 ± cos(jθ_k))/N gives moment ±1/2 at j, 0 at other j' ≤ K when 2K < N. Approximation: finitely many moments + value of probability measure lie in closed convex hull of the curve ⇒ design matches to η. Exactification: mix λ of quadrature designs to kill residual moments exactly, cost O(λ).
## PowerGridMomentTheorem
- V_q(J) = inf{∫F dν : ν prob. on circle, ∫cos(jz)dν = 0 for j ∈ J}. EXACT: blind slack on {q^j : j ∈ J} is −V_q(J) (also zero-pole). Blind slack on any set of powers of ONE integer = moment problem for folded symbol on circle. Lower: normalized phase measure admissible, γ ≥ fold. Upper: exact design up to K + compressed envelope whose correlation vanishes beyond (K+1)ℓ; envelope energy O(1/K). Recovers V(N) = m_q, V(N∖{d}) = m_q − |φ_d|, V({d∤j}) = min F_d.
## SignedPowerBathtub
- NO blindness: every nonneg combination A(c) = m_q·mass + Σ_{j≥1} φ_j √(q^j) v_c(q^j) + fold defect, fold defect = (1/2π)∫G(γ − F∘phase) ≥ 0; equality iff spectral density supported in fundamental period [−π/ℓ, π/ℓ]. Mechanism: phase measure of compact combination has finitely many nonzero Fourier coeffs ν̂(j) = π√(q^j)v_c(q^j) (compact support ⇒ node values vanish beyond J₀) ⇒ trig-polynomial density. Each power node priced by a Fourier coefficient of folded symbol.
## PrimePowerZeroPoleNodeCriticality (start)
- CLASSIFICATION: ZeroPoleBlindPositiveOn 𝒩 ⇔ RH ∧ (all prime powers ∈ 𝒩). Dividing line is INCIDENCE (Λ support), not density. Primes alone (above √ density) never suffice (4 missing). Deleting one prime power falsifies unconditionally; deleting non-prime-power (e.g. 6) changes nothing. ZeroPole ⇔ PrimeBlindPositiveOn (pole invisible to node criticality).
- Mechanism: two-sided Farkas duality (HTGeometry.exists_of_nonneg_on_null_cone) on node values in 𝒩 + pole coordinate, generators = pole-corrected pair tests, blind adjTestFn(±1) two-bump tests ⇒ weight supported on 𝒩 Weil-positive at pole weight 1−λ_none; pole-weight rigidity (eq_one_of_weilPositiveAt) ⇒ λ_none = 0; Weil-cone uniqueness (eq_vonMangoldt_of_weilPositiveFull) ⇒ weights = Λ. Node indispensable iff Λ charges it.
- RH ⇔ ZeroPoleBlindPositiveOn{prime powers}. log 4 indispensable, log 6 redundant.
## PrimePowerNodeDeletionPrice
- A(c) = W(c) + Σ_n Λ(n)L_n(c) (explicit formula, prime side); weilEnergy W = full Weil functional with Λ weights, pole weight 1. On prime-power blind cone A = W (composite nodes free).
- Deletion law: blind at all prime powers except m ⇒ A − W = Λ(m)L_m; TOWER FEJÉR bound |L_m| ≤ ‖c‖²/√m (powers m^k, k≥2, blind ⇒ one free Fourier coeff ⇒ ≤ half mass; without tower the cap is 2‖c‖²/√m). EXACT range of (A−W)/‖c‖² = [−Λ(m)/√m, Λ(m)/√m], both ends attained by narrow pair tests h(u) ± h(u − log m). Price of log 4 = log2/2, log 3 = log3/√3, composite = 0.
- Criterion: RH ⇔ ∀ prime powers m, ZeroPoleBlindSymbolSlackOn(primePowers∖{m}, Λ(m)/√m). (⇐: prices of 4^k = log2/2^k → 0.)
## PrimePowerDeletionPriceAdditivity (start)
- Coprime m₁, m₂ deleted together: exact range ±(Λ(m₁)/√m₁ + Λ(m₂)/√m₂) — prices ADD. Attained by double pair b*(δ₀+σ₁δ_{log m₁})*(δ₀+σ₂δ_{log m₂}) with narrow bump of index m₁m₂; cross lag log(m₁m₂) carries σ₁σ₂‖·‖²/(2√(m₁m₂)) — free because Λ(m₁m₂) = 0. Additivity across towers = redundancy of composite nodes; full integer-grid cone (blind at m₁m₂ too) does not admit double pair. Gap lemma: |log a − log b| ≥ 1/(max+1) via WeilExcess.inv_succ_le_abs_log_sub.
- Two-node identity A = W + Λ(m₁)L_{m₁} + Λ(m₂)L_{m₂}; {2,3}: price log2/√2 + log3/√3 (cross node log 6 charged but Λ(6)=0).
## PrimePowerTowerDeletionInteraction
- Inside one tower prices do NOT add. Delete m and m², s = √(1+8m): exact range of (A−W)/‖c‖² = [−Λ(m)(s−1)/(2m), Λ(m)(s+1)/(2m)]. m=2: loss (√17−1)/4·log2 strictly between log2/√2 (single) and log2/√2 + log2/2 (sum): loss side sub-additive, gain side super-additive; marginal price of log 4 after log 2 positive.
- Mechanism: finite-band phase positivity (trigPoly_nonneg_of_cos_finite): moments vanish beyond J₀ ⇒ ∫G + 2Σc_n cos(nz) ≥ 0 pointwise. Tower inequality ‖c‖² + √m L_m cosθ + m L_{m²} cos2θ ≥ 0; evaluate at cosθ = −2√m/(s+1), 2√m/(s−1). Attained by narrow triples h + βh(·−log m) + h(·−2log m), β = (±s−1)/(2√m) (degree-2 Fejér–Riesz eigenvector). Square of a node = second harmonic in the tower's phase: the two prices share one circle.
## PrimeWindowCeilings
- Tests supported in interval of length L see only nodes log n < L. Prime side = weighted adjacency operator of graph u ~ u ± log n on window, atoms w_n = Λ(n)/√n.
- log3 < L < log4: exact ceiling of (A−W)/‖c‖² = λ₂₃ = (w₃ + √(w₃² + 4w₂²))/2 (Perron root λ² = w₃λ + w₂² of path w₂,w₃,w₂); floor −λ₂₃. Window graph = disjoint 4-vertex paths u+log2 — u — u+log3 — u+log3−log2, single w₂ edges, isolated points (the square u,u+log2,u+log3,u+log6 needs L > log 6).
- Mechanism: weighted Schur bound 2|Re k(s)| ≤ ∫|f|²(φ(t−s)+φ(t+s))/φ(t) with neighbours restricted to window; two-valued supersolution φ = λ₂₃ on [0,L−log3) ∪ [log3,L), w₂ elsewhere. Attained by narrow Perron test (weights λ₂₃, σw₂, σλ₂₃, w₂ on path).
- λ₂₃ < w₂ + w₃: joint price of 2,3 on this window strictly sub-additive; additive value needs cross lag log 6 inside window although Λ(6)=0.
## PrimePowerDeletionPriceEulerAdditivity
- Delete m_p = p^{e(p)} for p in finite prime set P: exact range ±Σ_p Λ(m_p)/√m_p — prices ADD over primes (Euler product multiplicativity read by positivity). Deleting all primes ≤ x (keeping higher powers): exact price Σ_{p≤x} log p/√p.
- Attainment: iterated pair b * Π_p(δ₀ + σ_p δ_{log m_p}) = train over subsets A ⊆ P at positions log m_A. Lag log(m_A/m_B) = log of a prime power n iff n m_B = m_A; unique factorization ⇒ n = m_r, A = B ∪ {r}. Other lags composite/non-integer ⇒ cone asks nothing. Train coefficient at m_r = σ_r·2^{|P|−1}; mass 2^{|P|}∫h². Lag selection lemma for narrow-bump trains (weilTest_train_select).
- Finite deletion identity A = W + Σ_{n∈D} Λ(n)L_n.
## PrimeTowerDeletionLocalEulerFactor (start)
- Delete whole towers of primes in P: (A−W)/‖c‖² ∈ OPEN interval (−Σ 2log p/(√p+1), Σ 2log p/(√p−1)), both ends approached, neither attained. Ends = extremes of local factor t ↦ 2Re(−ζ_p'/ζ_p)(1/2+it), ζ_p = (1−p^{−s})^{−1}.
- Spectral identity of a tower: π Σ_{k≥1} L_{q^k}(c) = ∫G_c(r) S_x(r log q)dr, x = q^{−1/2}, Poisson symbol S_x(θ) = Σx^k cos kθ = (x cosθ − x²)/(1 − 2x cosθ + x²); log q·2S_x(t log q) = 2Re(−ζ_q'/ζ_q)(1/2+it) for prime q: tower reads LOCAL EULER FACTOR on critical line.
- Tower bounds with NO blindness: −2/(√q+1)‖c‖² ≤ Σ_k L_{q^k} ≤ 2/(√q−1)‖c‖², both strict for positive mass (spectral density cannot concentrate on the countable extremal phase set).
- Sharpness: divisor train Σ_{d|M} σ^{Ω(d)} b(u − log d), M = box modulus Π_p p^n; L_n = 2σ^{Ω(n)}τ(M/n)∫h²/√n; Fejér weight (n+1)τ(M/p^{k+1}) = (n−k)τ(M); deviation Σ_p log p Σ_{k<n} 2(σ/√p)^{k+1}(n−k)/(n+1) → Σ 2σ log p/(√p − σ). Summed over all primes both ends diverge (ζ'/ζ unbounded on critical line).
- Whole tower costs strictly more than first node from below: log p/√p < 2log p/(√p+1). Towers {2,3}: exact inf −(2log2/(√2+1) + 2log3/(√3+1)).
## PrimeWindowCeilingPolarAsymptotics (start)
- Window ceiling c(L) = sup (A−W)/‖c‖² over tests in intervals of length L: c(L)/e^{L/2} → 1. On windows of length log X prime side reaches √X(1+o(1)) = top of polar kernel e^{|s−t|/2} (semi-separable; top eigenfunction φ(t) = e^{−t/2} + e^{−(L−t)/2}, polar cosh centred at midpoint). Atoms on average = polar density (PNT: Σ w_n δ_{log n} ≈ e^{y/2}dy).
- Upper: ψ(x) ≤ Kx + B ⇒ |A−W| ≤ (K e^{L/2} + B + (1+L)²)‖c‖²; Chebyshev K = log4 + 4 for all L; PNT K = 1+ε. Mechanism: Schur with polar weight; neighbour sum = e^{−τ/2}ψ(e^τ) + e^{−(L−τ)/2}ψ(e^{L−τ}) + Σ Λ(n)/n terms; e^{−τ/2}e^τ = e^{L/2}e^{−(L−τ)/2}: prime mass at distance log n pays polar weight at the FAR end. Σ_{n<e^τ}Λ(n)/n ≤ (1+τ)².
- Lower: polar test (e^{−t/2} + e^{−(L−t)/2})χ(t), mass ≤ 2 + 2Le^{−L/2}, ends correlate k(y) ≥ e^{−(L−y)/2}(L−y−2δ) ⇒ prime side ≥ 2e^{−L/2}Σ_{n≤Y}Λ(n)log(Y/n), Y = e^{L−2δ}; Riesz mean ≥ (1−η)Y via Riemann sum of PNT.
- Consequence: an archimedean bound paying a uniform prime ceiling must supply margin of order e^{L/2} on windows of length L. Deviation of c(L) from e^{L/2} carried by Chebyshev error ψ(x) − x near x = e^L.
- Riesz mean Σ_{n≤Y}Λ(n)log(Y/n) ≥ (1−η)Y via δΣψ(e^{−jδ}Y) Riemann sum. Ceiling theorem c(L)/e^{L/2} → 1 proven (tendsto_windowCeiling_div_exp); Chebyshev bound gives BddAbove for all L.
## PrimeWindowFloorPolarAsymptotics (start)
- Polar kernel on [0,L] ≈ e^{L/2}(u⊗v + v⊗u), u = e^{−t/2}, v = e^{−(L−t)/2}: spectrum pair ±e^{L/2}. Floor(L)/e^{L/2} → −1. With ceiling: on windows of length log X prime side ranges over [−√X, √X](1+o(1)).
- Antisymmetric polar test (e^{−t/2} − e^{−(L−t)/2})χ: k(y) ≤ 2Le^{−y/2} − e^{−(L−y)/2}(L−y−2δ); prime side ≤ 4L(2+L)² − 2e^{−L/2}Σ_{n≤Y}Λ(n)log(Y/n). Self-correlations O(L³). L_n ≤ 4L/n.
- tendsto_windowFloor_div_exp proven: floor(L)/e^{L/2} → −1.
## PrimeWindowCeilingRHCriterion
- If eventually every window deviation ≤ e^{L/2} + B(1+L), then RH (also c(L) ≤ e^{L/2} + O(L) ⇒ RH). Prime side must match pole to ABSOLUTE precision O(log X) at scale √X.
- Mechanism: polar test with cutoff width δ = e^{−L/2}; Riesz mean = e^T − 1 − D(T), D(T) = ∫_0^T(e^t − ψ(e^t))dt (RHTower.sum_vonMangoldt_mul_logGap_eq_integral); ceiling ⇒ D(L) ≥ −C(1+L)e^{L/2}; Landau one-sided ⇒ RH (RHTower.riemannHypothesis_of_logChebyshevDeficitPrimitive_ge_mul). |D(L) − D(T)| ≤ C e^L (L−T).
## DeficitPrimitiveOneSidedWidth (start)
- Quantitative width version: 0 ≤ α < 1/2, −B(1+T)e^{(1/2+α)T} ≤ D(T) ∀T ≥ 0 ⇒ all ξ zeros Re ρ ≤ 1/2 + α (also reverse bound). Landau at width α: g(T) = B(1+T) ± e^{−(1/2+α)T}D(T) nonneg density; Laplace transform analytic at real z > 0; continues regularized critical-Mellin defect to Re u > α − 1/2; rotate into Xi coordinates (xiZeroHalfPlaneBound_of_upper_logDeriv_extensionAbove).
- Width criterion proof: width measure (B(1+T) + εe^{−(1/2+α)T}D(T))dT + Lebesgue; continuation (B+1)/z + B/z² + ε(ζ_u'/ζ_u(z+1/2+α)+1)/(z+1/2+α)²; Landau ⇒ abscissa 0; extension of regularized critical-Mellin defect agrees on real axis ⇒ identity theorem.
## PrimeWindowCeilingWidthLaw
- 0 ≤ θ,β < 1/2. c(L) ≤ e^{L/2} + B(1+L)e^{θL} ⇒ zeros Re ρ ≤ 1/2 + θ. Zeros Re ρ ≤ 1/2 + β ⇒ c(L) ≤ e^{L/2} + Ce^{(1/4+β/2+ε)L}. Excess exponent θ* = limsup log(c(L) − e^{L/2})/L satisfies width ≤ θ* ≤ width/2 + 1/4. Zero width read (with loss) from finite prime quantity (n ≤ X). Under RH excess O(X^{1/4+ε}); excess O(X^ε) ∀ε ⇒ RH.
- Lower: deficit_ge_of_windowDeviations_le: ceiling e^{L/2}+G ⇒ D(L) ≥ −(L + 2G + 3 + 2C)e^{L/2}, C = log4+5. Upper: polar Schur with generalized von Koch ψ(x) ≤ x + Kx^γ + 1, γ = 1/2+β+ε; power error at distance log n costs Ke^{γL/2}; loss from window midpoint where weight ≍ e^{−L/4}. exp_half_mul_exp_le: e^{−s/2}e^{γs} ≤ e^{γL/2}(e^{−s/2}+e^{−(L−s)/2}).
- Zero-width ⇒ ceiling uses RHTower.Sieve.exists_chebyshevPsiReal_error_power_bound_of_xiZeroHalfPlaneBound (generalized von Koch); constant 66 + 2K from (1+L)² ≤ 66e^{L/4}.
## PrimeTwoThreeDecouplingLength
- log 6 = decoupling length of 2,3. Cone blind at all prime powers except 2,3, tests in intervals of length L: L ≤ log 6 ⇒ |(A−W)/‖c‖²| ≤ 111/100; L > log 6 ⇒ exact range ±(w₂+w₃) ≈ ±1.1244. Price JUMPS at L = log 6: composite node never charged but prices add only on windows long enough to contain its lag.
- Below log 6 lag graph (shifts log2, log3) has degree ≤ 2; alternating w₂w₃w₂w₃ pattern breaks at double w₂-vertex (neighbour sum 2w₂ < w₂+w₃). Five-step Schur weight 1,r,q,r,1 on [0,log(3/2)),[log(3/2),log2),[log2,log3),[log3,log4),[log4,L), q = 89/100, r = 207/200, κ = 111/100.
- Euler trains with narrow bumps of index N attain Euler price on every window longer than log m_P (isGreatest_eulerWindowDeviations).
## PrimeWindowLiouvilleMirror (start)
- Modulating test by e^{iξu} keeps mass/window, multiplies correlation at ±log n by n^{±iξ}. Kronecker (log p ℚ-independent; HTGeometry.KroneckerWeylDensity) ⇒ ξ with p^{iξ} ≈ −1 ∀ p < N ⇒ n^{iξ} ≈ Liouville sign (−1)^{Ω(n)} on prime powers. Mirror: ∀ window deviation x, δ>0, ∃ x' same length with |x + x'| ≤ 2T(N) + δ, T(N) = Σ_{n<N,Ω even}2Λ(n)/√n = 2Σ_{m²<N}Λ(m)/m ≤ 2log N + O(1).
- Consequences: |c(L) + floor(L)| ≤ 2T(N) ≤ 4L + C (window spectrum symmetric to O(log X)); floor(L) ≥ −e^{L/2} − O(L) ⇒ RH; floor ≥ −e^{L/2} − O(Le^{θL}) ⇒ width θ. Window extremes see prime atoms only through their sizes: cannot separate Λ(n)/√n from Liouville twist Λ(n)λ(n)/√n coarser than O(log X).
- Mirror proof: |P(e^{iξ·}f) + P(f) − 2P_even(f)| ≤ εK(N)‖f‖², K(N) = Σ2nΛ(n); ‖n^{iξ} − (−1)^k‖ ≤ kε on p^k. T(N) ≤ 2(log N + log4 + 4) via Mertens Σ Λ(m)/m. With N = ⌈e^L⌉: 2T ≤ 4L + 4(log 8 + 4). Floor bounds ceiling: deviations ≥ −F ⇒ ≤ F + 4L + 4(log8+4).
## PrimePowerDeletionStaircaseTrains (start)
- Cone blind at EVERY integer n ≥ 2 except m₁ = p^e, m₂ = q^f (p ≠ q): sup = w(m₁)+w(m₂), inf = −(…), same price as prime-power cone, NOT attained (double pair charges log(m₁m₂): not_gridBlind_doublePair). Blindness at composites free; at prime powers (e.g. log 4) not.
- Staircase train: bumps at k log(m₂/m₁) and k log(m₂/m₁) + log m₁, 0 ≤ k ≤ M, signs τ^k, στ^k. In exponent lattice positions lie on slabs of coordinate sum 0 and 1; integer lag log n needs nonneg exponents summing to 1 ⇒ only log m₁ (M+1 rungs) and log m₂ (M steps) (staircase_lag_cases via p-,q-adic valuations). Deviation σw(m₁) + στw(m₂)M/(M+1). Gives up attainment, keeps price.
## PrimeTowerDeletionCompositeCharge (start)
- WHOLE towers DO read composite nodes. Cone blind at every integer n ≥ 2 not a power of a prime of P (so blind at pq): sup ≤ Σ 2log r/(√r−1) − c₀, c₀ ≤ log r·x_r/(1−x_r²) (r = p,q); inf ≥ −Σ2log r/(√r+1) + c₀, c₀ ≤ log r·x_r(1−x_r)/(1+x_r)³. {2,3}: sup drops ≥ 9/10 — blindness at log 6 free for single nodes {2,3}, costs ≥ 9/10 for whole towers.
- Mechanism: tower spectral identity π(A−W) = ∫G_c Σ_r log r S_{x_r}(t log r); blindness at pq adds free term −(c₀/2)∫G cos(t log pq). Dual certificate bounded by its value at joint phase t log p ≡ t log q ≡ 0: Poisson symbol falls quadratically S_x(θ) ≤ x/(1−x) − x(1−cosθ)/(1−x²) faster than composite cosine rises 1 − cos(a+b) ≤ 2(1−cos a) + 2(1−cos b). Divisor trains approaching tower sup concentrate at joint phase where composites p^i q^j are charged most.
## PrimePowerDeletionSlabTrains (start)
- Integer-grid cone, delete m_p = p^{e(p)} for p ∈ P: sup/inf = ±Σ w(m_p) (Euler additivity survives full grid); deleting all primes ≤ x costs Σ_{p≤x} log p/√p (isGLB_gridEulerDeviations_primes_le). Composites never change a single-node deletion price.
- Slab train: fix p₀, Q = P∖{p₀}; bumps at Σ_i k_i log(m_i/m₀) + ε log m₀, k ∈ {0..M}^Q, ε ∈ {0,1}, signs σ^ε (τ_i optional); positions on slab of coordinate sum 0,1 ⇒ integer lags only deleted nodes (slab_lag_cases via p-adic valuations). m₀ charged by (M+1)^{|Q|} rungs, each m_r by M(M+1)^{|Q|−1} steps; deviation σ(w(m₀) + (M/(M+1))Σ_r w(m_r)).
## PrimeWindowTwistInvariance
- Unimodular completely multiplicative twist χ (Liouville, n^{iτ} vertical shifts, Dirichlet characters extended by 1 at p|q): twisted window ceiling = c(L), twisted floor = floor(L) (twistedWindowCeiling_eq/Floor_eq). Window extremes of every twisted L-function's prime measure equal those of ζ: twisted ceiling e^{L/2}(1+o(1)) though twisted measure has NO polar main term; excess reads ζ's zero width, never twisted L's. Window extremes see prime atoms only through sizes.
- Kronecker with prescribed targets ⇒ one modulation realizes χ on every prime power < N within εn; prime side continuous in phases |P_a − P_b| ≤ Σ2Λ(n)‖a(n)−b(n)‖‖f‖².
## PrimePowerDeletionPeriodizationDefect (start)
- EXACT time-domain identity: c blind at m^d (d≥2), tests in (a_f, a_f+L), L < (K+1)ℓ, ℓ = log m, σ = ±1: ‖c‖² + σ√m L_m(c) = Σ_f c_f ∫_{a_f}^{a_f+ℓ}|Σ_{j=0}^K σ^j f(u+jℓ)|²du. Deletion defect = energy of σ-periodization along log m over one period. Extremals: periodization vanishes ⇔ f = g ± g(·−log m) with g supported in interval shorter by log m (pair_structure_of_stepSum_eq_zero) — narrow pairs are the ONLY extremals.
- Mechanism: unfold period, shift i-th term, symmetric periodization Σ_{|d|≤K}σ^{|d|}f(v+dℓ), tile support ⇒ Σ_d σ^{|d|}k_f(−dℓ); blindness kills |d| ≥ 2.
- lagMass(c,y) = Σ c_f Re k_f(y); lagMass(log n) = √n L_n/2. Backward periodization telescopes B(u) − σB(u−ℓ) = f(u) − σ^{K+1}f(u−(K+1)ℓ); price ±w(m) attained only by pairs/antipairs.
## PrimePowerDeletionPairThreshold
- Two prime powers m₁ = p^e, m₂ = q^f (p ≠ q): Euler price ±(w₁+w₂) is a window deviation of length L iff L > log(m₁m₂) (eulerPrice_mem_eulerWindowDeviations_iff). Attainment needs room for both shifts.
- Mechanism: at price both nodes extreme ⇒ tests are pairs g + g(·−log m₁) whose alternating log m₂-periodization vanishes; φ = log m₂-periodization of g satisfies φ(u) = σφ(u−log m₁), antiperiodic along log m₂; |φ| invariant under dense group log m₁Z + log m₂Z (log m₁/log m₂ irrational, unique factorization; dense_addSubgroupClosure_pair_iff); g shorter than log m₂ ⇒ φ vanishes at left end ⇒ everywhere ⇒ g = 0.
## PrimePowerDeletionEulerThreshold
- Any finite prime set P, exponents ≥ 1: Euler price is a window deviation of length L iff L > log Π_p p^{e(p)}. Every extremal = iterated pair g * Π_p(δ₀ + δ_{log m_p}) — needs room for every deleted node at once; its lags contain every composite m_A, |A| ≥ 2.
- Mechanism: all_nodes_extreme (Σ w_p(M − √m_p N_p) = 0 with nonneg terms). Peel one prime: f = g + g(·−ℓ₁); ψ = periodization of g along other ℓ is antiperiodic under ℓ and ℓ₁ ⇒ invariant under dense index-2 subgroup ⟨ℓ₁−ℓ, 2ℓ₁⟩ ⇒ constant ⇒ 0 (eq_zero_of_two_antiperiods). Induction on P (eq_zero_of_periodizations): test shorter than Σ log m_p with vanishing (−1)-periodizations along all ℓ_p vanishes.
## PrimePowerTowerPairWindowSpectrum (start)
- Delete m and m², windows length L, ℓ = log m: L ≤ ℓ ⇒ deviations {0}; ℓ < L ≤ 2ℓ ⇒ exactly [−w(m), w(m)] both attained (square blind for free since lag 2ℓ ≥ L); L > 2ℓ ⇒ exact joint range [−Λ(m)(s−1)/(2m), Λ(m)(s+1)/(2m)], s = √(1+8m), both attained by indexed narrow triple. m=2: spectrum jumps at log 4.
- log 4 vs log 6: tower pair {2,4} threshold = lag of deleted node 4 itself; coprime pair {2,3} threshold = log 6 = lag of a never-deleted never-charged node. On (log 4, log 6] joint price of {2,4} attained, {2,3} not. Square closes its tower on its own lag; independent primes interact only through composite lag.
## TwoTowerBlindSlackEnclosure (start)
- Blind at all powers of q₁ and q₂: spectral law uniform on both circles r ↦ rℓᵢ mod 2π; joint phase winds densely on torus (mult. independent); γ(r) is a function on the LINE, not the torus.
- Line duality: line certificate = continuous even P₁, P₂ with P₁(rℓ₁) + P₂(rℓ₂) ≤ γ(r) ∀r ⇒ A ≥ (⟨P₁⟩+⟨P₂⟩)‖c‖². Folded symbol of one tower is a certificate (value m_q); incidence gain η is a certificate correction.
- Product designs: frequencies ω_a ± ω'_b (2N² of them); Σcos((ω_a ± ω'_b)t) = 2Σcos(ω_a t)Σcos(ω'_b t) vanishes at iℓ₁, jℓ₂ (i,j < 2N); symbol = 2D midpoint sum of pair symbol (γ(x+y)+γ(x−y))/2 → product mean T(q₁,q₂) = mean of γ under convolution of the two uniform period laws.
- ENCLOSURE: exact blind slack on powers of q₁,q₂ ∈ [−T(q₁,q₂), −m_{q₁} − η(q₁,q₂)]; every line certificate value ≤ T; m_{qᵢ} ≤ T; 2,3: m₂ + η₂₃ ≤ T(2,3). T is NOT expected exact: admissible law = any probability law on the line with uniform projections on both circles; box convolution only the smallest-support one. (OPEN: exact two-tower slack.)
## InfiniteGridCorrelationCompactness
- InfiniteGridEnergySource K: C_c C² source, positive mass, normalized energy ≤ K, autocorr zero at every log n (n ≥ 2). Normalized correlations relatively compact in GLOBAL sup norm (HTGeometry.isCompact_closure_bcf_of_uniform_tails: bound + equicontinuity from uniform continuity radius + uniform tails). Uniform limits keep H(0)=1, even, |H| ≤ 1, full log grid zeros, vanishing at ∞. No source asserted for the limit.
## InfiniteGridLimitEnergy
- Fatou: extended energy ∫⁻ (1−H)·archLevySinhWeight is lsc under pointwise convergence ⇒ limit has integrable Lévy density ≤ K. Finite real Gram positivity Σc_ic_jH(t_i−t_j) ≥ 0 survives. Compact relaxation: continuous, PD, full grid, uniform tails, integrable singular energy ≤ K.
## CorrelationOriginEnergy
- Energy split at a > 0 into origin ∫_{(0,a]} and tail ∫_{(a,∞)}; origin energy → 0 as a → 0 for integrable kernel; finite families share a cutoff. Tail energy continuous under pointwise convergence (dominated by 2·weight beyond a).
## InfiniteGridOriginConcentration (start)
- Energy convergence ⇔ uniformly small origin energy (eventual ⇔ uniform). Every limiting energy defect D = L − ∫(1−H)w ≥ 0 is concentrated at the ORIGIN: origin energies on any (0,a] → D + originEnergy(H,a). Every bounded-energy sequence has a subsequence with fully localized defect.
## SmallSourceCorrelationStability
- Young: 2|∫f q(·+x)| ≤ t h_f(0) + h_q(0)/t. Adding small-mass q changes autocorr by ≤ h_q(0) + t h_f(0) + h_q(0)/t. Disjoint perturbation with mass ≤ t² ⇒ normalized correlation moves ≤ t(h_f(0)+3)/h_f(0) globally. Energy parallelogram ⇒ a sign s with J(f)+J(q) ≤ J(f+sq) ≤ 2(J(f)+J(q)).
## UnitEnergySmallSources
- In any interval, smooth sources with raw Lévy energy exactly 1 and arbitrarily small mass exist (compress bump by L; logarithmic increment bound forces energy ≳ c·log scale; normalize amplitude).
## ShortSupportEnergyInjection
- Translate unit-energy small-mass bump off seed f, choose sign: support within 5b, normalized energy gain ≥ 1/(2h_f(0)), L² distance ≤ t², normalized correlation error ≤ t(h_f(0)+3)/h_f(0).
## InfiniteGridStrictEnergyLoss
- NO-GO for energy continuity: sources in one interval shorter than log 2/2 (hence blind on full integer grid), correlations converge uniformly (and sources in L²) to actual smooth source, energies retain fixed positive excess d. Subsequence realizes strictly positive origin-concentrated defect. General signed sources need origin-energy control; blindness is sharpness, not a coercivity premise.
## SignedGridEnergySources
- LevyEnergySource K (no grid constraints): signed sampling error at nearest log node: e^{−1/2}T(H(T) − H(log⌈e^T⌉))² ≤ 8K; one radius A uniform over bounded-energy class.
## SignedGridTailEquivalence (start)
- Uniform decay of signed log-samples ⇔ uniform decay of full normalized correlations (energy supplies sampling modulus; no blindness either way).
## SignedGridTraceCompactness
- Exact compactness criterion: family of normalized correlations at energy ceiling K has compact closure in global sup norm ⇔ signed log-traces vanish uniformly at ∞ ⇔ uniform continuum tails (finite nets use actual compact-source centers). No zero-grid or polar premise.
## DistantCopyCorrelationTopology
- Copy f − a f(·−T) separated (T > D): exact normalized error = −κ(a)(H(x−T) + H(x+T)), mixing coefficient κ(a) = a/(1+a²), |κ| ≤ 1/2; global error ≤ |κ(a)|, attained at copy center T. Uniform convergence ⇔ κ(a_n) → 0 (centers may vary).
## DistantCopyEnergyTopology
- Normalized energy error ≤ copyTailFactor(D,T)·∫|h|/(2h(0)) for EVERY amplitude (κ ≤ 1/2), exponentially small e^{−(T−D)/2}; escaping centers ⇒ energy convergence for any amplitudes; single energy ceiling contains seed and all separated copies.
## DistantCopyPolarTopology
- Normalized polar moment P(f) = ∫_0^∞ h cosh(x/2)/h(0); 2∫_0^∞ h cosh(x/2) = (∫f e^{u/2})(∫f e^{−u/2}). Copy: P(copy) = (1 − 2κ(a)cosh(T/2))P(f) — polar weight MAGNIFIES mixing by cosh(T/2). Polar continuity ⇔ κ(a_n)cosh(T_n/2) → 0. polarCopy has P = 0. Nonneg bump has P > 0.
- Topology split: correlation/energy converge when κ → 0 or T → ∞, but polar moment needs κ cosh(T/2) → 0 — the polar functional is not continuous in correlation/energy topology.
## SchurSquareCorrelation
- Squared correlation h² realized by simultaneous translation of product source on plane (tensorWave); finite Gram forms of h² are integrals of squares (PD). Increment decomposition (h(0)²−h(x)²) + (h(0)−h(x))² = 2h(0)(h(0)−h(x)); Lévy energy of h² + quartic defect = 2h(0)·Lévy(h) (in ℝ≥0∞, no finiteness premise).
## SeparatedCopySquareClassification
- Gap = 2·radius+1: three correlation packets disjoint ⇒ h_copy² = (1+a²)²h² + a²(h(·−T)² + h(·+T)²). Squared normalized profiles equal ⇔ κ(a)² = κ(b)² (or zero mass); signed profiles ⇔ κ(a) = κ(b); one signed sample at T recovers full signed profile.
## SchurSquarePolarAmbiguity
- NO-GO: smooth f, g with same mass, identical squared correlations h², same zero sets, but polar moment 0 vs positive (attenuated copy a = e^{−T/2}: 2κ(a)cosh(T/2) = 1 cancels polar moment; reversing sign doubles it). Polar moment does not factor through squared profile; nor through zero set.
## SeparatedCopyCycleCharge
- Gap_m = (m+2)radius+1. Copy sign flip multiplies each lag product by (−1)^{packet charge}. Nonzero products: |Σlags − charge·gap| ≤ length·radius. Closed products (Σ lags = 0) of length ≤ m have charge 0 ⇒ invariant under copy-sign reversal.
## SeparatedCopyCyclePolarAmbiguity
- Every permutation term of an n×n Gram determinant is a closed lag product ⇒ all Gram determinants up to order m invariant. NO-GO for every finite m: smooth f, g with identical closed products and Gram minors through order m but different polar balance (polarMoment_not_factor_through_finite_data).
## ClosedCorrelationCycleRecovery
- POSITIVE: ALL closed products (all orders) ⇔ signed autocorrelation (two-edge products give |h|; positivity near 0 fixes sign; closed cycle −x + n·(x/n) recovers h(x)). Polar balance recoverable from the full hierarchy; no uniform order.
## EnergyControlledClosedCycleRecovery (start)
- Quantitative: energy bound gives explicit origin collar + modulus; two closed products recover each signed value with explicit noise; finite mesh covers bounded window; signed log samples control tail. Mesh size, max cycle order, amplification explicit and source-independent for fixed K, accuracy. Finite-accuracy, not exact uniform order.
- EnergyCycle details: spoke cycle (−x, n+1 copies of x/(n+1)); value(spoke) = H(x)H(x/(n+1))^{n+1}; continuity radius e^{−(1 + 8K/(e^{−1/2}ε²))} from log-modulus; collar |x| < r_K ⇒ H > 1/2; recovery |H_f(x) − H_g(x)| ≤ 2^{n+1}(|spoke diff| + (n+1)|pair diff|); depth = ⌈|L|/collar⌉; mesh over [−R,R], R = sampling radius; amplification 2^{n+1}(n+2). global_recovery: |H_f − H_g| < max(amp·observationError, traceError) + ε. On fixed signed-grid fibre with zero observation error ⇒ uniform ε-recovery (fixed_integer_grid_recovery).
## FiniteGridNullCorrector
- Rank–nullity + L² translate independence (HTGeometry.linearIndependent_L2_translates): for smooth f and any finite z_k, a smooth corrector v supported in 2r with cross(f,v)(z_k) = 0 ∀k but cross ≢ 0. Separated source pair f + a g(·−T): exact three-packet correlation h_f + a²h_g + a cross(x−T) + a cross(−x−T); energy parallelogram J(+a) + J(−a) = 2(J(f) + a²J(g)).
## FullGridEnergyCycleAmbiguity
- NO-GO: ∃K > 0 s.t. ∀ order m, actual smooth sources p, q at energy ceiling K, BOTH blind at every log n (n ≥ 2), equal normalized closed products through order m, different signed correlations. Construction: seed u in radius log2/8; full-grid cross-null corrector v (finite constraints + support beyond e^{T+3r}); u ± a v(·−T), a = 1/(1+J(v)), T = (m+2)D+1; three-packet parity (ThreePacketParity.closed_products_eq: closed products with length·D < T have charge 0). Energy kept by parallelogram.
## ClosedCycleAmbiguityDecay
- Matching cycles through order n+2 ⇒ equality on |x| ≤ n·collar (linear window). On fixed signed grid fibre: e^{−1/2}|x|(H_f − H_g)² ≤ 32K globally ⇒ order-n ambiguity diameter O(n^{−1/2}) (no optimality claim).
## UnitCorrelationBump
- Literal seed bump radius 1/2: autocorr > 0 exactly on |x| < 1 (open), zero at |x| ≥ 1; positive polar moment.
## StrictCopyCycleCharge
- Seed with copy at T > 2: opposite copies differ only by packet parity; any closed product distinguishing signs has length strictly > T (strict support ⇒ strict error bound).
## SharpCycleDetectionOrder
- Seed + copy at T > 2: closed product of length n distinguishes ±a iff a ≠ 0 ∧ n > T (sharp). Detector: one outer edge T − T/(k+1) and k inner edges −T/(k+1). First detecting order ⌊T⌋+1. Attenuated pair (a = e^{−T/2}): polar 0 vs 2P(seed) with exactly this threshold (sharp_polar_pair).
## EndpointCycleDeterminant
- Symmetric tridiagonal path closed by endpoint edge z: det(cycle(−z)) − det(cycle(z)) = −4z(−1)^{k+2}c^{k+2} (two-row multilinearity; endpoint cofactor is upper-triangular minor c^{k+2}).
## SharpCycleGramRealization
- Equally spaced samples (step T/(⌊T⌋+1) ∈ (1/2,1)) of separated source give a chordless cycle Gram matrix at first detecting order; closing edge carries copy sign; determinant difference 4a h(step)(−1)^{k+2}((1+a²)h(step))^{k+2} ≠ 0 iff a ≠ 0.
## SharpGramDetectionOrder
- Gram determinant of size n distinguishes ±a iff a ≠ 0 ∧ n > T (padding by distant sample multiplies by mass). Polar-distinct equal-mass smooth pair with exact Gram detection threshold T (sharp_gram_polar_pair).
## DistantCopyCompactness (start)
- Global sup-norm distance of copy correlation to seed = |κ(a)| exactly. Compact closure ⇔ uniform signed-grid tail ⇔ κ(a_n) → 0.
- Escaping copies: every fixed bounded window eventually exactly unchanged regardless of amplitude.
## DistantCopySharpness
- Separating witnesses: (1) unit-amplitude escaping copies: each fixed log node eventually zero, energy converges, NO compact closure (κ(1) = 1/2). (2) polar-attenuated copies a = e^{−T/2}: compact closure, uniform signed-grid tails, uniform correlation + energy convergence, each member polar-balanced (P = 0) but limit has P > 0 — polar balance not closed under correlation+energy convergence.
## FiniteIntegerTrainPackets
- IntegerPacketTrain: coefficients on distinct integer sites, spacing S > 2D: correlation = Σ_k lagCoefficient(k) h(x − kS) (grouped signed interference); near lag kS only one packet active; mass = Σc².
## FiniteIntegerTrainPeak
- peak = max_{k≠0}|lagCoeff(k)|/mass; global normalized correlation error ≤ peak, attained at packet center. Correlation unchanged on |x| ≤ S/2.
## FiniteIntegerTrainEnergy
- |E(train) − E(seed)| ≤ 2∫_{S/2}^∞ archLevySinhWeight (count/coefficient independent); escaping spacing ⇒ energy convergence; one ceiling E(seed) + 2∫_1^∞ w for all trains with S ≥ 2D+2.
## FiniteIntegerTrainCompactness (start)
- dist(train correlation, seed) = peak exactly; uniform convergence ⇔ peak → 0; compactness ⇔ peak decay (arbitrary growing data).
## FiniteIntegerTrainPolar
- Polar multiplier of train = expSymbol(S,1/2)·expSymbol(S,−1/2)/mass, expSymbol(S,β) = Σc_i e^{β·site_i·S}; P(train) = multiplier·P(seed); polar continuity ⇔ multiplier → 1.
## TernaryPacketTrain / TernaryPacketPolarGrowth
- Sites 3^i, unit weights: all nonzero differences distinct ⇒ every nonzero lag coefficient 1, mass n+2, peak 1/(n+2). Symbol product ≥ e^S (first two packets); with S ≥ n+2: polar multiplier ≥ (n+2)/4.
## FiniteIntegerTrainProducers
- consecutive sites = copyTrain. DIFFUSE POLAR ESCAPE: smooth ternary trains with dist to seed = 1/(n+2), uniform correlation convergence, energy convergence, one ceiling, compact closure, uniform signed-grid tails, BUT normalized polar moment ≥ (n+2)/4·P(seed) → ∞. No dominant packet. Polar functional unbounded on compact correlation/energy families.
## FiniteMomentEnergyInvariance
- Separated copy energy error ≤ C e^{−T/2} uniformly in amplitude (|a|/(1+a²) ≤ 1). Cancel any real exponential moment ∫f e^{βu} with a = e^{−βT} copy; finite lists cancelled simultaneously preserving earlier zeros, local correlation on [−A,A] exactly, energy within ε. Hence: finite exponential moment constraints (any rates incl. 0, negative) do NOT change the valid log-grid energy lower bounds (finite_moment_log_grid_lower_bound_iff).
## FiniteSourceEnergyScalarization (start)
- sourceTranslate preserves autocorr & energy.
- Scalarization: correlation & energy parallelograms h(f+g)+h(f−g) = 2(h_f+h_g), J likewise. Two compact sources: separate supports so cross vanishes on [−A,A]; one sign gives scalar k with local h_k = h_f + h_g and J(k) ≤ J(f)+J(g). Local source-energy epigraph (unit mass, local data on [−A,A], energy allowance) is CONVEX for actual real scalar sources (no closure). Finite vector sources ⇒ scalar source with same local total correlation, no greater energy. Finite vector rank doesn't change log-grid energy lower bounds; polar scalar problem = unconstrained finite-vector problem (polar_finite_source_log_grid_lower_bound_iff, via polar_log_grid_lower_bound_iff).
## CliqueSphereDualityAndExtremalTheory
- Difference-orthogonal clique {t_i} (h(t_i − t_j) = 0, i≠j): multi-node Bessel Σh(y−t_i)² ≤ h(0)². Exact quadratic sphere defect identity 2W₂R(Σw_i(R−u_i) − (Σw−W₂)R) = W₂²(R² − Σu²) + Σ(W₂u_i − w_iR)². Duality factor Σw − √Σw² exact min, extremal ray u* = (w/W₂)R. Clique-rank amplification: (M − √M)h(0) ≤ Σ_i (h(0) − h(y−t_i)) ∀y; per-node defect fraction 1 − 1/√M → 1. Integrated collar bound.
## HyperbolicShiftCommutatorAndParityIntertwining (start)
- C_α f = cosh(αu)f, S_α f = sinh(αu)f. Parity: odd f ⇒ S_α f even (lifts odd prime-blind states into even sector). cosh(αu)cosh(α(u+x)) − sinh·sinh = cosh(αx). h_{C_αf}(x) − h_{S_αf}(x) = cosh(αx)h_f(x). At zero nodes h_f(x₀) = 0: h_C(x₀) = h_S(x₀); hence h_f(0) ≤ h_C(0) − h_C(x₀), and h_f(0)/m² ≤ h_C(0) − h_C(x₀/m).
- Hyperbolic increment decomposition: (C-incr) − (S-incr) = (h(0)−h(x)) − 2sinh²(αx/2)h(x); h(x₀) ≤ 0 ⇒ h_f(0) ≤ C-increment at x₀ (sinh increment nonneg by C-S).
## CoprimeShearAndMultiplicativeGraphUncertainty (discrete)
- mulShift v(kn), addShift v(n+1), addDiff. Telescoping: v(k(n+1)) − v(kn) = Σ_{j<k} addDiff v(kn+j); commutator telescopes across k−1 steps; mulJump telescopes over (k−1)n steps. Lagrange identity ⇒ finite C-S. Σ_n (v(k(n+1))−v(kn))² ≤ k Σ_{m<kN} addDiff². Coprime successor: v supported on multiples of d ≥ 2 pays full energy 2v(n)² at both neighbours. Beurling–Deny nodal decomposition (v(kn)−v(n))² = (|v(kn)|−|v(n)|)² + 4(v⁺(kn)v⁻(n) + v⁻(kn)v⁺(n)); cross term ≤ ((k−1)n)·Σ addDiff² over [n,kn).
## ContinuumShearDirichlet
- shear b x = log(e^x + b) (additive translation in log coords); semigroup, dilation relation shear(e^s b)(x+s) = shear b x + s; log(n+2) = shear 1 (log(n+1)). Physical Dirichlet energy ∫q² = log-weighted ∫e^{−x}(deriv)². Exact interval trace defect ∫((b−a)q − Δ)² = (b−a)²E − (b−a)Δ². Shear increment² ≤ b·log-energy (resistance = physical step, position independent). Dilated-cell sum inequality with exact defect; constants attain. Logarithmic version without origin extension.
- Affine commutator: |P(shear b x + s) − P(shear b (x+s))|² ≤ (e^s − 1)b·logEnergy (commutator interval physical length (e^s−1)b).
## ContinuumMultiplicativeEdgeControl
- Continuum edge x → x + log(n+1) has physical resistance n e^x: jump² ≤ n e^x·edgeEnergy; Beurling–Deny nodal identity on continuum edge; opposite-sign pairing 4·pair ≤ n e^x·edgeEnergy; finite weighted families inherit (infinite graph admission separate).
## SobolevTraceEnergy
- L² velocity q ⇒ locally absolutely continuous primitive, derivative = q a.e.; trace defect identity and increment² ≤ r·energy for rough states; unit-cell trace + interpolation remainder decomposition.
## CoprimeSobolevInterpolation
- Step velocity from prescribed slopes: primitive interpolates nodal differences, energy = discrete Dirichlet energy exactly. divisorTrace (multiples of d+2 masked, endpoints zero): successive values product 0 ⇒ discrete energy = 2Σ trace²; continuum velocity with energy exactly 2Σ trace² (sharp coprime successor coercivity attained); every amplitude realized at first active node.
## SobolevLogarithmicTransport
- Jacobian formula transports L² physical velocity to locally integrable log velocity e^x q(e^x) (no pointwise chain rule); absolutely continuous; weighted log energy = physical Dirichlet energy.
## CoprimeLogSobolevCoercivity (start)
- Log divisor state: ∫_0^{log(N+1)} e^{−x}(deriv)² = 2Σ trace² exactly (sharp coefficient 2 attained). Energy decomposition for competitors with prescribed slopes (trace error + interpolation defect explicit).
- Coprime trace energy decomposition for ANY competitor velocity: E = 2Σtrace² + 2Σ slope·(trace error) + interpolation defect ≥ 0; log version on [0, log(N+1)]; rough-state shear bound.
## LogarithmicPathKernel
- Edge (h,u) joins u to u+h; resistance = e^{upper} − e^{lower} (physical endpoint distance). pathKernel = resistance·1_{(lower,upper]}; budget(edge) = resistance·physical interval energy (finite for each edge); jump² ≤ budget; slack = budget − jump (ℝ≥0∞, no subtraction of infinities).
## MixedEdgePathCongestion
- EdgeMixture = diffuse weighted Lebesgue edges + countably many weighted lag lines (s-finite). Tonelli: congestion energy ∫ congestion(y)·density = jumpEnergy + slackEnergy exactly (extended, no finiteness premise); = derivative-weighted energy. Nodal opposite-sign energy ≤ jump energy ≤ congestion-weighted log Dirichlet energy.
## CompactSourceResistanceMass
- Compact source ψ: diffuse weight archLevySinhWeight(h)·ψ(u)²ψ(u+h)², lines at log(n+2) with arbitrary nonneg atom weights. ARCHIMEDEAN SINGULARITY CANCELS against path resistance: resistance(h,u)·archLevySinhWeight(h) = 2e^{u+h/2}/(1+e^{−h}) (smooth through h=0). Large lags killed by compact support (atomCutoff) ⇒ resistance mass finite, no summability of atom coefficients needed.
## CompactSourceGraphAdmission (start)
- Congestion supported in [−R,R] and ≤ resistanceMass ⇒ congestion energy ≤ resistanceMass·local Dirichlet mass < ∞ for EVERY physical L² velocity; jump, slack, nodal, derivative energies finite. Source mass ∫ψ²(c + logPrimitive)² finite.
## CompactSourcePairVariance
- Source moments m_k = ∫ψ²f^k; weighted variance V = m₀m₂ − m₁²; ∫∫ψ(u)²ψ(v)²(f(v)−f(u))² = 2V; positive-lag pair integral = V exactly (each unordered pair once). V = 0 ⇔ f constant on whole nonzero source (no connected-support premise).
## CompactSourceGraphCoercivity
- coercivityScale = sinh(2R) (R source radius): on contributing pairs archLevySinhWeight(h)·sinh(2R) ≥ 1 ⇒ V(c + logPrimitive) ≤ sinh(2R)·jumpEnergy (diffuse part alone suffices, arithmetic lines preserve). V ≤ sinh(2R)·resistanceMass·local Dirichlet mass. Jump energy = 0 ⇔ state constant on entire nonzero source (diffuse jumps join disconnected components).
## RoughSobolevModulus
- Fermat at zero level ⇒ velocity vanishes a.e. on {state = 0}; |state| absolutely continuous with derivative sign(state)·q a.e.; modulus velocity is an actual L² velocity with same local Dirichlet energy and primitive |c| + P = |c + P|.
## RoughModulusGraphDecomposition
- Modulus keeps every path budget; exact Beurling–Deny: jump(q) = jump(|·|) + nodalCost; lost nodal jump becomes extra slack; whole mixed-measure identities hold at infinite energy; congestion energy unchanged; source mass unchanged; compact-source finite real nodal difference; form energy (source mass + jump) decomposes exactly with nodal defect.
## CompactSourceNodalVariance (start)
- Lobe masses M± = ∫ψ² max(±f,0); V(f) − V(|f|) = 4M₊M₋ exactly; M₊ = 0 ⇔ f ≤ 0 on source. m₁ = M₊ − M₋, m₁(|f|) = M₊ + M₋.
- Positive-lag nodal gap integral = 4M₊M₋ exactly.
## CompactNodalMassCoercivity
- 4M₊M₋ ≤ sinh(2R)·nodalEnergy ≤ sinh(2R)·(jump(q) − jump(|q|)): modulus loses ≥ 4M₊M₋/sinh(2R). Nodal energy = 0 ⇔ sourcewise one-sign; equality of jump energies under modulus ⇔ one-sign; STRICT contraction ⇔ both signs occur at nonzero source points (disconnected support, arbitrary atom weights, zero source covered).
## RoughSobolevClamp
- Unit clamp = (|a| − |a−1| + 1)/2 built from two modulus velocities inside L²; firm nonexpansive: (Δclamp)² + (Δresidual)² ≤ (Δ)². Clamp velocity = q on open band {0 < state < 1}, 0 else; residual orthogonal pointwise a.e.; exact local energy splitting, log transport.
## RoughClampGraphControl
- Path budgets split exactly; jump energies firm: J(clamp) + J(residual) ≤ J(q); congestion splits (infinite allowed); source mass firm. Residual variance ≤ sinh(2R)(J(q) − J(clamp)). Equality J(clamp) = J(q) ⇔ residual jump 0 ⇔ state constant on source OR state ∈ [0,1] on source.
## CoprimeTentHilbertFrame (start)
- ℓ² trace data; unitCell indicators on (k,k+1] orthonormal in L²; ⟨prefixCell n, q⟩ = primitive q n; ⟨unitCell k, q⟩ = increment.
- Tent frame: centers (d+2)(j+1); tent velocity = unit cell before center − cell after; ⟨tent_i, tent_j⟩ = 2δ_ij; normalized tents orthonormal ⇒ synthesis isometry ℓ² → L², closed range; adjoint reads centered second differences traceCurvature = 2P(c) − P(c−1) − P(c+1).
## InfiniteCoprimeTraceProjection
- Every ℓ² sequence has L² tent extension with all integer traces exact (active = v_j, every other integer trace 0) and energy 2Σv². Projection P_d = synthesis∘analysis: idempotent, active trace = curvature/2; INFINITE coprime energy decomposition ∫q² = (1/2)Σ curvature² + ∫(q − P_d q)²; best approximation with error 2Σ(coeff − v)²; equality ⇔ q in tent range.
## CoprimeProjectionCrossGram
- ⟨tent^d_i, tent^e_j⟩ = 2 (same center), −1 (adjacent centers), 0 else. Common divisor g ≥ 2 of spacings ⇒ no adjacency ⇒ projection acts as coefficient restriction.
## CoprimeProjectionLattice
- Divisibility ⇒ nested projections; gcd ≥ 2 ⇒ P_d P_e = P_{lcm}; commute; simultaneous fixed points = lcm tent space; range intersections = lcm range (always).
## CoprimeProjectionCommutator
- Bézout gives adjacent active centers for coprime spacings; forbidden trace of commutator equals exactly 1/2. COMPLETE CLASSIFICATION: P_d, P_e commute ⇔ gcd(d+2, e+2) ≥ 2 (coprime spacings never commute, including spacing 2).
## CoprimeProjectionNeighbors (start)
- Nonzero cross coefficients only from adjacent centers; spacing ≥ 3 ⇒ unique neighbour; spacing 2 ⇒ two-arm star.
- Neighbor actions: no neighbor ⇒ P_d(tent^e_j) = 0; unique neighbor i (spacing ≥ 3) ⇒ P_d(tent^e_j) = −½ tent^d_i; spacing 2 with odd center ⇒ two even neighbors ⇒ −½(tent_i + tent_k) (star).
## CoprimeProjectionAnglePolynomial
- Reduced product T = P_dP_e − P_lcm satisfies T² = c·T with c = coprimeAngleSquare = 0 (gcd ≥ 2), 1/2 (coprime and a spacing equals 2), 1/4 (coprime, both ≥ 3). T* = T(e,d). Single nonzero arithmetic angle per spacing pair: cos²θ ∈ {0, 1/4, 1/2}.
## CoprimeProjectionAngleNorm
- TUT = TT; via C*-identity ‖T‖² = c (sharp), commutator K = P_dP_e − P_eP_d: K³ = −c(1−c)K, ‖K‖² = c(1−c) ∈ {0, 3/16, 1/4}; both norms attained by explicit nonzero velocities.
## CoprimeAlternatingProjectionRate
- (P_dP_e)^{k+1} − P_lcm = c^k·T exactly; ‖(P_dP_e)^{k+1} − P_lcm‖² = c^{2k+1}: geometric alternating projection rate with ratio 1/4 or 1/2 (no slow convergence; arithmetic Friedrichs angle).
## TwoGridTraceData (start)
- Two-grid data space: (a,b) ∈ ℓ²×ℓ² with b vanishing on common (lcm) nodes (closed kernel, complete); erase-common canonical map; extension = sum of two tent series; union nodal mass ‖a‖² + ‖b‖² counts common nodes once; second-grid extension vanishes at first-grid centers; all integer traces explicit.
- Two-grid exact energy: ‖ext(a,b)‖² = 2(‖a‖² + ‖b‖²) − 2Σ_j a_j·(b-values at the two neighbouring nodes c_j ± 1) — signed adjacent-node interaction is the only cross term; traces at second-grid centers read a (common) or b.
## TwoGridTraceStability
- |cross| ≤ √c·mass ⇒ Riesz bounds (2 − 2√c)·mass ≤ ‖ext‖² ≤ (2 + 2√c)·mass; √c ≤ 3/4 ⇒ uniform lower bound mass/2 for ALL spacing pairs; extension antilipschitz (2), injective, closed range; algebraic sum of two infinite tent ranges is closed (no closure needed). 2√c ∈ {0, 1, √2}.
## TwoGridTraceSharpness
- Both Riesz constants 2 ∓ 2√c attained by nonzero ℓ² joint data (eigenvectors of T*T).
## TwoGridTraceMinimality
- Competitor energy identity with explicit curvature pairings; matching all integer traces ⇒ ‖q‖² = ‖ext‖² + ‖q − ext‖²; extension is the unique minimum-energy velocity with those traces.
## FiniteGridRunLength
- Finite divisor family {d+2} ∪ {e+2: e∈D}: activity periodic with period lcm; every period window has an inactive node (multiple of lcm); longest active run finite, positive, < lcm, attained inside first period.
## SuccessorSequenceHilbert (start)
- Unilateral right shift on real/complex ℓ² as orthonormal synthesis; adjoint = successor (left) shift, ‖·‖ ≤ 1; coordinate masks contractions.
## IntegerAffineShear
- Integer dilation n ↦ (d+2)n as ℓ² isometry; adjoint = multiplicative pullback (mulShift). Shear = S∘D − D∘S (successor/dilation commutator), ‖·‖ ≤ 2; shear e (δ_n) = δ_{(e+2)n+1} − δ_{(e+2)(n+1)}. For n ≥ d+2 the coordinates (d+2)n+1 and (d+2)(n+1) read 1/−1 for scale d and 0 for EVERY other scale (incl. larger).
## SummableIntegerAffineShear
- ℓ¹ coefficients a ⇒ norm-convergent series Σ a_d·shear_d, ‖·‖ ≤ 2‖a‖₁; cofinal coordinates recover ±a_d exactly, no truncation.
## IntegerAffineShearCompactness
- Compact operators vanish on moving unit vectors; (series a − K) still reads ±a_d asymptotically; series a compact ⇔ a = 0; series a − series b compact ⇔ a = b (compact quotient retains full signed coefficient sequence); 2Σ_{d∈F} a_d² ≤ ‖series a − K‖² for every finite F and compact K (essential norm lower bound).
## IntegerHatTraceExtension
- integerHat k = cell k − cell k+1; extension of ℓ² trace data via unit-cell synthesis of discrete gradient: primitive at n+1 = v_n; energy 2‖v‖² − 2Σ v_k v_{k+1}; competitor identity with integer curvature; minimum-energy uniqueness under matched traces.
## FiniteGridTraceData
- Union data = mask fixed space (each node once), closed, complete; masking arbitrary ℓ² data gives union data; extension inherits all integer-hat identities; zeros off union.
## FiniteGridTraceStability (start)
- Masked successor on complex ℓ²: contraction, nilpotent of order = longest active run length L; via nilpotent-contraction sine bound |Σ v_k v_{k+1}| ≤ cos(π/(L+1))‖v‖² ⇒ Riesz bounds (2 ∓ 2cos(π/(L+1)))‖v‖²; antilipschitz with constant (2 − 2cos(π/(L+1)))^{-1/2}.
- Finite-grid extension injective, closed range.
## FinitePathSinePackets
- Interval trace data (finite ℓ² vectors) with exact adjacent pairing; sine path values w_j = sin((j+1)π/(n+1)) satisfy Σ w_j w_{j+1} = cos(π/(n+1)) Σ w_j²; alternating signs reverse pairing, preserve mass.
## FiniteGridTraceSharpness
- Sine packet on a longest active run (lower) and its alternating version (upper) are union data attaining both constants 2 ∓ 2cos(π/(L+1)) exactly ⇒ finite-grid Riesz constants SHARP, determined solely by longest active run L.
## FiniteGridTwoSpacingRuns
- Two spacings: L = 1 if gcd ≥ 2; L = 3 if coprime and one spacing is 2; L = 2 if coprime both ≥ 3. Hence cos(π/(L+1)) ∈ {0, √2/2, 1/2} = √(coprimeAngleSquare): longest-run sine factor recovers the projection-angle constants (two independent proofs of same sharp constants: operator angle vs. combinatorial run).
## DivisorGridTraceData
- Same union-data / integer-hat extension machinery for arbitrary (possibly infinite) divisor families D ⊂ ℕ; extension always injective.
## DivisorGridRunGeometry
- Bounded runs ⇒ least exclusion length = attained maximum run; unbounded ⇒ every finite run length realized; D = univ (all spacings ≥ 2) unbounded.
## DivisorGridTraceStability (start)
- Masked successor contraction, nilpotent at run length when runs bounded.
- Bounded runs ⇒ Riesz bounds 2 ∓ 2cos(π/(L+1)), antilipschitz, closed range.
## DivisorGridSinePackets
- Sine packets on any active run of length n: unit energy exactly 2 − 2cos(π/(n+1)) (→ 0 as n → ∞); alternating packet 2 + 2cos; sharp constants attained for bounded runs; unbounded runs give normalized near-null sequence.
## DivisorGridClosedRange
- EXACT CLASSIFICATION for arbitrary divisor families: positive coercivity ⇔ closed range ⇔ bounded active runs. Bottom unit energy (GLB) = 2 − 2cos(π/(L+1)) (attained) if bounded, 0 (unattained, energies strictly positive by injectivity) if unbounded. All spacings (D = univ) ⇒ range not closed.
## CellPrefixHilbert
- Cell currents w ∈ ℓ²; prefix functional Σ_{j<n} w_j continuous; trace gradient (I − right shift) with prefix(k+1)(∇v) = v_k; primitive of unit-cell synthesis at n = prefix n; ℓ² current cannot have nonzero constant tail.
## DivisorCellConstraints
- Cell space: zero cumulative current at inactive nodes (closed, complete) ⇔ zero total current on every finite active-edge component; univ family: only constraint w₀ = 0. Admissible current constant along all active edges ⇒ zero (finite components by conservation, infinite tail by ℓ²).
## DivisorGradientClosure (start)
- Orthogonal complement of gradient range = currents constant across active edges; closure of gradient range ⊆ cell space.
- Closure of gradient range = cell (prefix-conservation) space EXACTLY, for every family incl. unbounded runs (no spectral gap premise); orthocomplement = currents constant on active edges (constant on finite components, zero on infinite active tails).
## DivisorEnergyCompletion
- Completed energy domain = cell space; synthesis isometric, energy = Σw²; completed trace k = prefix(k+1); closure of old interpolant range = completed range. Completed state is old interpolant ⇔ its cumulative trace is ℓ². All completed states recoverable ⇔ bounded runs; unbounded ⇒ an escaping state exists.
## FullDivisorEnergyEscape
- D = univ: unit cell 1 has trace 0,1,1,1,… (not ℓ²) yet lies in closure; linear ramps of length n+1 approximate with exact squared error 1/(n+1).
## DivisorCellEndpoints
- Canonical endpoint map (first inactive node after a cell) partitions cells into finite components (fibres = Ico(start, j+1)); infinite tails use identity convention; univ: only cell 0 has an end.
## DivisorComponentAverages
- Orthogonal residual of cell projection = finite-component mean of the current (zero on infinite tails); centered current w − mean = projection onto cell space, ‖·‖ ≤ ‖w‖.
## DivisorComponentCharge
- Component charge (Σ_component w)²/length; summable; ‖centered‖² + Σ charges = ‖w‖² (exact Pythagorean split, convergence proved from ℓ²).
## PhysicalCellAveraging (start)
- Unit-cell analysis (adjoint): k-th entry = ∫_{(k,k+1]} q = primitive increment; analysis∘synthesis = id; prefix of analysis = primitive; cellular projection residual orthogonal to cellular velocities; ‖analysis q‖² + ‖q − Pq‖² = ‖q‖².
- Negative half-line velocity is invisible to cells; ‖q − Pq‖² = ∫_{t≤0} q² + ‖remaining noncellular‖².
## DivisorPhysicalProjection
- Physical divisor projection = synthesis ∘ (cell-space projection) ∘ cell analysis: cell value minus finite-component mean; first cell always 0 (first trace 0); idempotent; range = closure of old interpolants; unique nearest completed state with exact defect ‖q − ext v‖² = ‖q − Pq‖² + ‖data − v‖². Exact THREE-PART ERROR: ∫_{t≤0} q² + noncellular variation + Σ physical component charges (primitive increment over component)²/length. D = univ: projection = cellular projection minus first cell; error = noncellular + (∫₀¹ q)².
## PhysicalDilation
- (D_a q)(t) = a·q(at) bounded on L² for all real a (incl. 0), ‖D_a q‖² = |a|‖q‖², semigroup D_a D_b = D_{ab}, primitive(D_a q)(t) = primitive q(at); integer dilation by n+1 = log-translation by log(n+1).
## IntegerBlockAggregation
- Block sum B_m = cell analysis ∘ D_m ∘ synthesis: (B_m w)_j = Σ_{k∈[mj, m(j+1))} w_k; prefix(n)(B_m w) = prefix(mn)(w); semigroup B_m B_n = B_{mn}; intertwining analysis(D_m q) = B_m(analysis q); ‖B_m‖ ≤ √m; B_m δ_k = δ_{⌊k/m⌋}.
## IntegerBlockCoisometry
- Adjoint = block replication (z_{⌊k/m⌋}); B_m R_m = m·I; ‖R_m z‖² = m‖z‖²; B_{n+1} surjective; ‖B_m‖ = √m exactly; block mean (1/m)R_mB_m idempotent; m‖w − mean‖² = m‖w‖² − ‖B_m w‖².
## IntegerBlockVariance (start)
- Finite block variance Σ_{s<r<m}(u_r − u_s)² = mΣu² − (Σu)²; zero ⇔ constant block; block squares regroup ‖w‖².
- Σ_j blockVariance = m‖w‖² − ‖B_m w‖² = m‖w − mean‖² (convergent); ‖B_m w‖² = m‖w‖² ⇔ w constant on every block.
## IntegerDilationTraceDefect
- B_m intertwines right shift by m with right shift by one: B_m S^m = S B_m. Physical dilation trace defect: m‖q‖² − ‖analysis(D_m q)‖² = m·‖noncellular part‖² + Σ block variances; equality ⇔ q cellular AND block-constant. Block packet attains coefficient m (energy m, trace energy m²). Divisor completion NOT dilation-invariant: D_2(cell 1) lies outside every completed divisor range (first trace would be 1, but projections force first trace 0).
## PhysicalTranslation
- Translation isometry group on L² (comp, comm, inverse, surjective); primitive injective; primitive(T_b q)(t) = P(t+b) − P(b) (anchor correction); log form.
## PhysicalIntervalRestriction
- Interval/positive-half restrictions contractions; positive part has same logarithmic primitive (log-picture sees only t > 0); interval truncations integrable with explicit primitive (0 left, ∫_a^b right).
## PhysicalAffineAction
- T_b D_a = D_a T_{ab}; anchored states (c, q) carry exact affine action with value c + P(t) transforming by t+b, at; affine commutator [D_a, T_b] = D_a(T_b − T_{ab}); ‖[D_a,T_b]q‖² = |a|·‖T_{b(a−1)}q − q‖²; defect 4|a|‖q‖² − ‖·‖² = |a|‖T_{b(a−1)}q + q‖²; ‖[D_a, T_b]‖ ≤ 2√|a|.
## PhysicalAntiperiodicRigidity
- Translation by 1 acts as left shift on cell coefficients; ℓ² ⇒ no nonzero antiperiodic sequence ⇒ T_c q = −q ⇔ q = 0 (every c, via dilation rescaling). Hence ‖T_c q − q‖² = 4‖q‖² ⇔ q = 0, and affine commutator bound 4|a|‖q‖² attained only trivially (sharp but never attained on nonzero states).
## AlternatingPhysicalPackets
- T_{−1} cell k = cell k+1; alternating cell packet Σ_{j<N}(−1)^j cell_j: energy N, ⟨T_{−1}p, p⟩ = −(N−1), ‖T_{±1}p − p‖² = 4N − 2 (boundary deficit exactly 2 at every length).
## PhysicalAffineProducers
- Dilated alternating packets realize every gap c = b(a−1); normalized ⇒ ‖[D_a,T_b]p_n‖² = |a|(4 − 2/(n+1)); defect 2|a|/(n+1).
## PhysicalAffineSharpNorm
- ‖[D_a, T_b]‖ = 2√|a| if b(a−1) ≠ 0, else 0; commutator = 0 ⇔ a = 0 ∨ a = 1 ∨ b = 0; norm NEVER attained on nonzero vectors (antiperiodic rigidity); defect of producers → 0.
## PhysicalTranslationContinuity
- Translation orbit strongly continuous; orbit primitive (Bochner) differentiable with derivative T_t q; primitive evaluation = bounded functional ⟨1_{(0,t]} − 1_{(t,0]}, ·⟩; commutes with Bochner integrals.
## PhysicalBoxAverage
- Box average A_s q = e^{−s}∫_0^{e^s} T_u q du: contraction, translation-covariant; shift difference formula; box derivative (T_{e^s} − I)/e^s with norm ≤ 2e^{−s}.
## PhysicalBoxProfile
- A_s q has continuous representative e^{−s}∫_t^{t+e^s} q (moving window), absolutely continuous, derivative = box derivative (L²) a.e.; primitive of A_s via second primitive.
## PhysicalBoxVariance
- Energy loss ‖q‖² − ‖A_s q‖² = centered orbit variance / e^s = pair variance /(2e^{2s}) (exact, all cross-shift Gram terms retained).
## PhysicalBoxAffineRegularity (start)
- Translation orbit of A_s q differentiable (derivative T_c(box derivative)); ‖T_c A_s q − A_s q‖ ≤ 2 min(1, |c|e^{−s})‖q‖.
- ‖[D_a,T_b]A_s‖ ≤ 2√|a|·min(1, |b(a−1)|e^{−s}) (gap-to-width regularization); A_s q → q strongly as s → −∞; energy loss → 0.
## PhysicalBoxGraphControl
- Source Dirichlet mass ≤ ‖q‖²; compact-source jump energy ≤ resistanceMass·‖q‖²; affine commutator of box producer has jump energy ≤ resistance·4|a|min(1,|b(a−1)|e^{−s})²‖q‖² (finite); box approximations converge in graph jump energy.
## MultiCosetGramPackingAndNyquistDensity (Pillar XI)
- Abstract Hilbert: Gram residual identity; Gram–Cauchy–Schwarz (Σ⟨e_i,x⟩²)² ≤ ‖x‖²·Σ_ij ⟨e_i,x⟩⟨e_j,x⟩⟨e_i,e_j⟩; Schur/Geršgorin row-sum ⇒ Selberg–Bombieri Bessel Σ⟨e_i,x⟩² ≤ M_row‖x‖².
- Autocorrelation version: rows Σ_j|h(t_i − t_j)| ≤ (1+Δ)h(0) ⇒ Σ_i h(y − t_i)² ≤ (1+Δ)h(0)² for every y ⇒ collar sum Σ_i (h(0) − h(y − t_i)) ≥ (M − √(M(1+Δ)))h(0): effective rank ~ M/(1+Δ).
- Nyquist: 0 < log(n+1) − log n ≤ 1/n, antitone; on collar (0, log(n+1) − log n], sinh y < 1/n ⇒ archLevySinhWeight(y) ≥ n (origin singularity absorbs multiplicity). Log-grid partition of [log N, log 2N] into N Nyquist cells; with zeros h(log(N+k)) = 0 for k < N, ∫_{log N}^{log 2N} h² ≤ 2h(0)Σ_k ∫_0^{δ_k}(h(0) − h(y)) dy (Krein increment at each zero).
- N-fold Nyquist multiplicity absorbed by archLevySinhWeight ≥ N on first collar: with dyadic zeros, ∫_{log N}^{log 2N} h² ≤ 2h(0)∫_{(0, log(1+1/N)]}(h(0) − h)·w ≤ 2h(0)·biScaleLevyEnergy(f).
## ProducerConsumerDualityAndNymanBeurlingBridge (Pillar XII)
- Producer–consumer defect: ⟨f, p − Σc_i g_i⟩ = ⟨f,p⟩ − Σc_i⟨f,g_i⟩; grid-blind consumer (⟨f,g_i⟩ = 0) ⇒ ⟨f,p⟩² ≤ ‖f‖²‖p − Σc_i g_i‖² (any producer approximation of the polar target bounds polar pairing of every blind consumer — Nyman–Beurling duality). Orthogonal clique with ⟨e_i,e_i⟩ = R: R‖p − Σc_i e_i‖² = (R‖p‖² − Σ⟨e_i,p⟩²) + Σ(Rc_i − ⟨e_i,p⟩)² (min producer error = consumer Bessel slack).
- Correlation form: ∫h·P + ∫(h(0) − h)W − (∫W)h(0) = ∫h(P − W); squared ≤ ∫h²·∫(P − W)². Dyadic window with zeros: discrepancy² ≤ 2h(0)·biScaleLevyEnergy·∫(cosh(x/2) − W)².
## AsymptoticTailCoercivityAndNyquistTrap5Closure (Pillar XIII)
- Quadratic collar h(0) − h(y) ≤ Ky² on [0,1/N] + N dyadic zeros ⇒ ∫_{log N}^{log 2N} h² ≤ (2K/N²)h(0). ∫cosh²(x/2) over window ≤ 2N log 2. ⇒ (∫|h|cosh(x/2))² ≤ (4 log 2/N)K h(0); same for negative polar lobe. Kinetic coercivity: polar lobe mass μ in window ⇒ Nμ² ≤ 4 log 2·K·h(0) (distant-copy trap costs K ≳ N = e^T when the dyadic grid zeros are imposed).
