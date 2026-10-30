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
- Derivative-free: (∫_{window}|h|cosh)² ≤ 4N log 2·h(0)·∫_{(0, log(1+1/N)]}(h(0) − h)·w (no K).
## SignedKreinCollarAndPrimeDeficitTransfer (Pillar XIV)
- Drops grid-blindness. Signed collar identity (h(0) − h(t±y)) + h(t) = h(0) − (h(t±y) − h(t)); Krein increment |h(t+y) − h(t)| ≤ √(2h(0)(h(0) − h(y))) ⇒ h(0) − √(2h(0)D(y)) ≤ collar + h(t). Young: w√(2RD) ≤ W₀D + w²R/(2W₀) ⇒ single-node leverage (w − w²/(2W₀))h(0) ≤ W₀D(y) + w(h(0) − h(t±y)) + w h(t).
- Abstract Hilbert identity (‖x‖² = ‖x_y‖² = R): W₀(R − ⟨x,x_y⟩) + Σw_i(R − ⟨e_i,x_y⟩) + Σw_i⟨e_i,x⟩ = (Σw_i)R − (1/2W₀)Σw_iw_j⟨e_i,e_j⟩ + (1/2W₀)‖Σw_ie_i − W₀(x_y − x)‖². Orthogonal clique: ≥ (Σw − Σw²/2W₀)R; almost-orthogonal: ≥ (Σw − (1+Δ)Σw²/2W₀)R.
- Signed Nyquist sum over [log N, log 2N] without zeros: Σ∫((h(0) − h(x)) + h(log(N+k))) ≥ Σ∫((1 − 1/2W₀)h(0) − W₀D(y)).
- archLevySinhWeight(log n) = 2n^{3/2}/(n² − 1) = 2/√n + 2/(√n(n² − 1)) ≥ 2/√n; remainder ≤ 8/(3√n n²): arch weight at log n matches Weil prime weight exponent n^{−1/2}.
## KreinKantorovichMeasureTransportAndPrimePolarPairing (Pillar XV, start)
- 1/archLevySinhWeight(y) = e^{−y/2}sinh y = ½e^{y/2}(1 − e^{−2y}) ≤ y e^{y/2} (vanishes linearly at 0); on (0, r₂]: archLevySinhWeight(y) ≥ e^{−r₂/2}/y.
- Krein–Kantorovich pointwise: ρ|h(t) − h(t+y)| ≤ D(y)·w(y) + (h(0)/2)ρ²e^{−y/2}sinh y ≤ D·w + (h(0)/2)ρ²y e^{y/2}; integrated: |(∫ρ)h(t) − ∫h(t+y)ρ(y)| ≤ ∫D·w + (h(0)/2)∫ρ²e^{−y/2}sinh y (signed, no blindness).
- Width rigidity: h ≤ 0 on [r₁, r₂] ⇒ e^{−r₂/2}log(r₂/r₁)h(0) ≤ ∫_{r₁}^{r₂} D·w; bounded energy ≤ K h(0) ⇒ log(r₂/r₁) ≤ e^{r₂/2}K (midpoint-compression trap requires log-divergent energy).
## AnnularCorrelationTransport
- Annular average A(t) = (1/d)∫_{t+a}^{t+a+d} h differentiable with continuous slope (h(t+a+d) − h(t+a))/d for any continuous h. correlationAverage with a = e^α, d = e^β; |A(t) − h(t)| ≤ (1/d)∫_a^{a+d}√(2h(0)D(y)) = transport cost (uniform in t, signed). Cost ≤ e^c∫D·w + h(0)/(2e^c d²)·∫e^{−y/2}sinh y (Young, adjustable budget).
## SignedPrimePolarCoupling
- Finite window cutoff log(N+2); step function = ψ(e^x) on window; logError = ψ(e^x) − e^x. Abel/Stieltjes: Σ g(log n)Λ(n) − ∫g e^x = g(0) + g(L)·logError(L) − ∫ g'·logError. Pairing = Σ_{n≤N+2} Λ(n)/√n·H(log n) − ∫_0^L 2cosh(x/2)H; for differentiable H: pairing = H(0) + e^{−L/2}H(L)logError(L) − ∫e^{−x/2}(H' − H/2)logError − ∫e^{−x/2}H (Chebyshev work, both endpoints, polar shadow).
- |pairing H − pairing K| ≤ mass·sup|H − K| (mass = Σ Λ/√n + ∫2cosh). For every compact continuous f: |pairing(h_f) − chebyshevWork(annular average)| ≤ mass·transportCost ≤ mass·(e^c∫D·w + …). Pairing equals the literal truncated prime-minus-polar measure.
## SignedPrimePolarPacket
- Signed packet S_f = Σ Λ(n)/√n·f(·+log n) − ∫_0^L 2cosh(t/2)f(·+t)dt (compact continuous source); ∫ q·S_f = pairing of q⋆f correlation (Fubini justified by supports). ⟨f, S_f⟩ = pairing(h_f) ⇒ pairing(h_f)² ≤ h_f(0)·‖S_f‖² (packet energy). Increment control: pairing(h(·+y) − h)² ≤ 2‖S_f‖²(h(0) − h(y)). Packet energy = iterated pairing pairing_t pairing_s h(s − t) (full Gram incl. mixed terms); ‖S_f‖² ≤ mass²·h(0) (signed budget never exceeds unsigned).
## SignedPrimePolarGramTransport
- pairing commutes with annular averaging (Fubini on compact windows): pairing(A) − pairing(h) = (1/d)∫ pairing(h(·+y) − h) dy. Packet transport cost (1/d)∫√(2‖S_f‖²D(y)) ≤ mass·(unsigned cost). |pairing(h_f) − chebyshevWork| ≤ packet cost ≤ e^c∫D·w + ‖S_f‖²/(2e^c d²)∫e^{−y/2}sinh y (cancellation-sensitive).
## SignedPrimePolarHalfLineDomain
- Source cutoff N_f = ⌈e^{supp radius}⌉: h_f and every right-annular average/slope vanish beyond log(N_f + 2). Full pairing (infinite prime sum − half-line polar integral) admissible: finite atom support, absolutely summable, integrable polar term; stabilizes = finite-window pairing for every N ≥ N_f.
## SignedPrimePolarHalfLineTransport (start)
- Abel kernel e^{−x/2}(A' − A/2) and shadow kernel e^{−x/2}A vanish beyond source cutoff; Abel kernel × logError integrable on half-line (local boundedness of ψ-error suffices; no arithmetic asymptotic).
- Full Chebyshev work = A(0) − ∫_{x≥0} abelKernel·logError − ∫ shadowKernel (upper boundary term vanishes beyond source cutoff); fullPairing(A) = fullChebyshevWork exactly; |fullPairing(h_f) − fullWork| ≤ packet cost at any cutoff ≥ N_f.
## AnnularCorrelationSource
- Collar source C = (1/d)∫_a^{a+d} f(· − y)dy (compact continuous); ⟨C, f(·+t)⟩ = annular correlation average A(t) (mixed pairing, not assumed autocorr); collar energy ‖C‖² = (1/d)∫A(−y) = (1/d²)∫∫h(z − y) (full double Gram); A ≤ h(0), ‖C‖² ≤ h(0); ⟨C, S_f⟩ = Chebyshev work exactly.
## SignedPrimePolarCoherentSchur
- Removing f-parallel parts: Schur: (work − A(0)·pairing/h(0))² ≤ (‖C‖² − A(0)²/h(0))·(‖S_f‖² − pairing²/h(0)); ⇒ packet energy ≥ pairing²/h(0) + (work − …)²/collarSchur. Coherent chord ‖f − C‖² = h(0) + ‖C‖² − 2A(0) ≤ 2(h(0) − A(0)); (pairing − work)² ≤ ‖S_f‖²·‖f − C‖². All transferred to literal half-line scalars.
## AnnularSourceRegularity
- Collar source is C¹ with derivative (f(u − e^a) − f(u − e^a − e^b))/e^b (no derivative of f used); compact support; gauge source C' − C/2 compact continuous with finite L¹ norm; remainder f − C has energy = coherent chord energy exactly.
## SignedPrimePolarRoughGauge
- S_{f−g} = S_f − S_g; weighted split ‖S_f‖² ≤ (1+e^c)‖S_g‖² + (1+e^{−c})‖S_{f−g}‖². With g = collar: ‖S_C‖² ≤ 3(10 + E(L)²)‖C‖² + 3‖gauge‖₁²∫E² (E = normalized ψ error; smooth-source Chebyshev mean-square from HyperbolicGaugeChebyshevEnergyRepresentation); remainder ≤ mass²·chord. ⇒ packet energy of every compact continuous source bounded by collar energy + gauge L¹·∫E² + mass²·chord.
- roughGaugeBound = 6(10 + E(L)²)‖C‖² + 6‖gauge‖₁²∫E² + 2mass²·chord ≥ packet energy; smoothing collar and transport collar chosen independently.
## AnnularGaugeEnergy
- ∫(C')² = 2(h(0) − h(e^b))/e^{2b} (single-width chord); ⟨C', C⟩ = 0 (compact C¹); gauge energy ‖C' − C/2‖² = 2(h(0) − h(e^b))/e^{2b} + ‖C‖²/4 — position-invariant (depends only on width).
## SignedPrimePolarCorrelationBudget
- Gauge supported in interval of length 2R + e^b ⇒ ‖gauge‖₁² ≤ (2R + e^b)·gauge energy (Cauchy–Schwarz); packet energy ≤ correlationGaugeBound (only source correlations, source radius, Chebyshev error E).
## SignedPrimePolarScaledCollar
- S_{tf} = tS_f, ‖S_{tf}‖² = t²‖S_f‖²; ‖f − tC‖² = h(0) − 2tA(0) + t²‖C‖²; A(0)² ≤ ‖C‖²h(0); collar packet ≤ collarPacketBound ≥ 30‖C‖². Trial family: ‖S_f‖² ≤ (1+e^c)t²·collarPacketBound + (1+e^{−c})mass²·‖f − tC‖² for every real t.
## SignedPrimePolarOptimalCollar
- Optimal signed coefficient t* = covariance/quadMass (degenerate case handled via Gram inequality); trial − optimum = quadMass·(t − t*)² (exact); optimizedPacketBound = min(mass²h(0), optimum) ≤ correlationGaugeBound (t = 1, c = 0) with exact gain; strict improvement over mass bound ⇔ mass²h(0)/e^c < cov²/quadMass.
## SignedPrimePolarHarmonicCorrection
- harmonicCorrection(N) = 4N(H_{4N} − 2H_{2N} + H_N) = 4NΣ_{k<N}[1/(2(N+k)+1) − 1/(2(N+k)+2)] ∈ [0, 1] (bounded real-ratio polar correction of factorial bi-null stencil).
## SignedPrimePolarFactorialLift
- Polar rectangle 1_{[0,L]}e^{x/2}: 2cosh(x/2)·e^{x/2} = e^x + 1, polar integral = e^L − 1 + L. Factorial lift F_K(x) = Σ_{j≤K} rect_{log(K/j)} (REAL ratios, never floored); F_K(log n) = √n·⌊K/n⌋; prime side Σ Λ(n)/√n·F_K(log n) = Σ_{n≤K}Λ(n)⌊K/n⌋ = Σ_{j≤K}ψ(K/j) = log K! (floorSummatory ψ); polar side Σ_j (K/j − 1 + log(K/j)).
## SignedPrimePolarFactorialProducer
- fullPairing(F_K) = 2·floorSummatory ψ(K) − K log K − K·H_K + K. Bi-null combination B_N = (F_{4N} − 4F_{2N} + 4F_N)/√N: B_N(0) = 0, B_N(log 4N) = 2 (nontrivial, not an autocorrelation); admissible; fullPairing(B_N) = (2·chebyshevBiNullProducer(N) − harmonicCorrection(N))/√N; |fullPairing(B_N)| ≤ (10 log(4N+1) + 3)/√N — UNCONDITIONAL explicit producer driving the signed prime–polar functional to 0 at rate log N/√N (both factorial poles cancel).
## AntitoneDyadicStencil
- For antitone f with values in [0,1]: Σ_{j≤4N}f(j) − 4Σ_{j≤2N}f(2j) + 4Σ_{j≤N}f(4j) ∈ [−2, 1] uniformly in N (paired drops).
## ClampedExponentialRamp
- clampedRamp_ε(t) = min(1, max(0, (1+ε−t)/ε)), continuous antitone; ∫_{x≥0}(e^x + 1)ramp(e^x/a) = a − 1 + log a + εa/2 + ((1+ε)log(1+ε) − ε)/ε.
## SignedPrimePolarContinuousFactorialLift (start)
- Continuous lift e^{x/2}Σ_j ramp_ε(j e^x/K): equals e^{x/2}K for x ≤ 0, 0 for e^x ≥ K(1+ε), e^{x/2} on [K(1+ε)/2, K]; with εK ≤ 1 agrees with discrete factorial lift at every log n (collar crosses no extra integer product).
- Smoothing adds polar εK·H_K/2 + K·rampLogCorrection(ε).
## SignedPrimePolarContinuousFactorialProducer
- Collar ε = 1/(4N); smooth bi-null stencil agrees with discrete at every log n, vanishes for x ≤ 0 and x ≥ log(4N+1): compact continuous test (C_c). fullPairing = (2·chebyshevBiNullProducer − (1 + 1/(8N))·harmonicCorrection)/√N; |·| ≤ (10 log(4N+1) + 3 + 1/(8N))/√N. Value 0 at origin, 2 at log 4N ⇒ not an autocorrelation.
## SignedPrimePolarContinuousFactorialEnergy
- Pointwise (B_N)² ≤ 4e^x/N via antitone dyadic stencil ∈ [−2,1]; ∫B_N² ≤ 16 uniformly; on top band [log(2N+1), log 4N] B_N = e^{x/2}/√N ⇒ ∫B_N² ≥ 1. CERTIFICATE: compact continuous producer with unit-order L² norm (∈ [1,16]) and signed prime–polar pairing O(log N/√N), unconditional — small pairing is NOT from vanishing norm.
## ExponentialTentMoments
- Causal tent on [0,2δ]; ∫_0^{2δ} e^{ax}tent = ((e^{aδ} − 1)/a)²; exponential tent density e^x·tent/(e^δ − 1)² is a probability density; ∫e^x·density = ((e^δ + 1)/2)²; source e^{x/2}·density compact continuous.
## ExponentialTentSourceEnergy
- 1/(2δ) ≤ ‖source‖² ≤ e^{4δ}/δ (reciprocal-width cost, matching up to constant).
## SignedPrimePolarSourceParameters (start)
- Width δ_N = log(1 + 1/(4N))/3 ∈ [1/(15N), 1/(12N)], e^{3δ_N} = 1 + 1/(4N), e^{4δ_N} ≤ 2; costs 6N ≤ 1/(2δ_N), 2/δ_N ≤ 30N.
- Collar (1 + ε_N)e^t ≤ 1 + 1/(4N) for t ≤ 2δ_N; coefficient ((1 + e^{δ_N})/2)³ ∈ [1, 1 + 1/(4N)].
## ClampedExponentialBranchMoments
- ∫_{x≥0} e^x·ramp(e^x/a) = a − 1 + εa/2; ∫ ramp(e^x/a) = log a + rampLogCorrection(ε).
## SignedPrimePolarRampCore
- rampBiNull_ε(N) general collar: zero for x ≤ 0, zero beyond e^x ≥ 4N(1+ε); compact support under ε·4N ≤ 1; equals e^{x/2}/√N on top band [2N(1+ε), 4N]; |·| ≤ 2e^{x/2}/√N, ∫² ≤ 16. Integer separation: e^{t/2}·L_K(log n − t) = factorial lift at log n whenever K(1+ε)e^t ≤ K+1 (small dilation collar preserves all grid values).
## SignedPrimePolarRampMoments
- ∫e^{x/2}L_K = (1 + ε/2)K·H_K − K; ∫e^{−x/2}L_K = K log K − Σ_{d≤K}ψ(⌊K/d⌋) + K·rampLogCorr. Stencil: ∫e^{x/2}·rampBiNull = (1 + ε/2)·harmonicCorrection/√N; ∫e^{−x/2}·rampBiNull = −chebyshevBiNullProducer/√N (ramp correction cancels in (1,−4,4)); prime side Σ Λ(n)n^{−1/2}·B_N(log n) = chebyshevBiNullProducer/√N. (Polar two-branch split: growing branch ↔ harmonic correction, decaying branch ↔ Chebyshev producer.)
## SignedPrimePolarCausalSource (start)
- Causal source = average over shifts t ∈ [0, 2δ_N] of e^{t/2}·ramp(x − t) against exponential tent density; continuous, support [0, log(4N+1)], equals discrete bi-null at every log n (shift budget K(1+ε_N)e^t ≤ K+1), equals e^{x/2}/√N on top band.
- Causal source agrees with B_N at every log n (tent density mass 1), equals e^{x/2}/√N on top band.
## SignedPrimePolarCausalMoments
- Moment factorization (Fubini + translation): ∫e^{sx}C_N = (∫tent·e^{(s+1/2)t})·∫e^{sx}R_N; s = 1/2: coefficient((1+e^δ)/2)³·harmonicCorrection/√N; s = −1/2: −chebyshevBiNullProducer/√N (tent mass 1).
## SignedPrimePolarCausalEnergy
- |C_N| ≤ 2e^{x/2}/√N; 1 ≤ ∫C_N² ≤ 16.
## SignedPrimePolarSourceFactorization
- C_N is a genuine mixed correlation: C_N(x) = ∫ L(u)·R(u+x) with L(u) = ramp(−u) (reflected), R = exponential tent source; L and R have disjoint supports (L·R ≡ 0). With scale s = N^{1/4}: P = sL + R/s, M = sL − R/s; contrast (h_P − h_M)/2 = C_N(x) + C_N(−x), = C_N for x ≥ 0. So the producer is a DIFFERENCE of two autocorrelations of compact continuous sources.
## SignedPrimePolarSourceEnergy
- ‖P‖² = ‖M‖² = √N·‖L‖² + ‖R‖²/√N (disjointness kills cross term); ‖L‖² ≤ 16, 6N ≤ ‖R‖² ≤ 30N ⇒ 6√N ≤ ‖P‖² ≤ 46√N (balanced at square-root growth).
## SignedPrimePolarCausalPairing
- fullPairing(C_N) = (2·chebyshevBiNullProducer − coefficient·harmonicCorrection)/√N; |·| ≤ (10 log(4N+1) + 3 + 1/(4N))/√N (unconditional, no PNT error assumed).
## SignedPrimePolarSourceCertificate (start)
- Contrast producer compact continuous, equals B_{n+1} at every log m, same full pairing as C_N; ∫contrast² = 2∫C_N².
- factorialSourceProducer CERTIFICATE: (h_P − h_M)/2 with ‖P‖² = ‖M‖² ∈ [6√N, 46√N], equals B_N on the integer grid, fullPairing = (2·chebBiNull − coeff·harmCorr)/√N, |·| ≤ (10 log(4N+1) + 3 + 1/(4N))/√N, admissible, contrast L² norm² ∈ [2, 32].
## CompactProfileLipschitz
- Clamp-to-interval Lipschitz extension lemma; ramp_ε Lipschitz 1/ε; causal tent 1-Lipschitz; |e^x − e^y| ≤ e^L|x − y| below L.
## CompactLipschitzLevyEnergy
- K-Lipschitz compact source ⇒ h(0) − h(x) ≤ K‖f‖₁|x| ⇒ Lévy integrand integrable; energy ≤ 3Ma + K_tail(log(6/a) + π) (near/far split at a ≤ 1); parallelogram law for Lévy energy given four admissions.
## SignedPrimePolarTentRegularity
- Narrow tent source Lipschitz ≤ 2000N², L¹ ≤ 2; δ_N ≤ 1, 1/collar ≤ 15N.
## SignedPrimePolarRampRegularity
- Factorial ramp Lipschitz ≤ 10000N⁴, |ramp| ≤ 5, ‖ramp‖₁ ≤ 20N.
## SignedPrimePolarSourceJumpDomain (start)
- Left/right/plus/minus sources Lipschitz ⇒ all Lévy (jump) energies admitted; parallelogram: E(P) + E(M) = 2(√N·E(L) + E(R)/√N); E(P) − E(M) = −2∫_{x>0} C_N·archLevySinhWeight (signed jump integrand = −2C_N·w).
## SignedPrimePolarSourceJumpUpper
- Jump scale Q_N = 10⁶N⁵; left increment ≤ Q|x|, right increment ≤ 4000N²|x|; E(L) ≤ 3 + 32(log 6Q + π), E(R) ≤ N(3 + 60(log 24000N + π)); E(P), E(M) ≤ 2√N·(…log N…) = O(√N log N).
## SignedPrimePolarTentJumpLower
- Narrow tent autocorr vanishes beyond 2δ_N ≤ 1/N ⇒ E(R) ≥ 6e^{−1/2}·N·log N (narrow source forces logarithmic Lévy cost).
## SignedPrimePolarCausalJumpBounds
- |C_N(x)| ≤ 20000N⁴x near 0 (Lipschitz from zero at origin); |C_N·w| ≤ (4 + 2/x)/√N; ⇒ |∫_{x>0}C_N·w| ≤ (6 log(4N+1) + 7 + 2 log Q)/√N = O(log N/√N); |E(P) − E(M)| ≤ 2·that.
## SignedPrimePolarSourceArchimedeanCertificate
- E(P), E(M) ≥ 6e^{−1/2}√N log N − O(log N/√N); normalized E/‖·‖² ≥ (3/23)e^{−1/2}log N − const (normalized Lévy energy of both balanced sources grows like log N). Full certificate: admitted jump domains, two-sided bounds O(√N log N), signed difference = −2∫C_N w with O(log N/√N) bound.
- READING: the factorial producer drives the signed prime–polar pairing to 0 at rate log N/√N, but its balanced source pair pays normalized archimedean energy ≳ log N → ∞ (energy blowup is the price of small pairing).
## SignedPrimePolarRealFactorialStencil
- log ⌊·⌋! monotone; short cutoff change ≤ length·log(X+1); integer dilation creates < a floor carries; real-scale stencil log⌊4v⌋! − 4log⌊2v⌋! + 4log⌊v⌋! has |·| ≤ 9 log(4v+1) + 1 for all real v ≥ 0 (equals chebyshevBiNullProducer at integers).
## SignedPrimePolarClampedPrimeSum (start)
- ⌊w⌋ ≤ Σ_{j≤K} ramp(j/w) ≤ ⌊(1+ε)w⌋ (cap K ≥ ⌊w⌋); log B! = Σ_{m≤M}Λ(m)⌊B/m⌋ for B ≤ M; clamped prime factorial sum sandwiched between log⌊v⌋! and log⌊(1+ε)v⌋!.
- With εv ≤ 2: clamped sum − log⌊v⌋! ∈ [0, 2 log((1+ε)v + 1)] (at most two carries).
## SignedPrimePolarFactorialAtomicPacket
- Atomic packet of the factorial ramp at shift u = e^{u/2}/√N × (clamped stencil at scale N e^{−u}); collar bounds on u ≥ −3δ_N; |atomic packet(u)| ≤ 19e^{u/2}/√N·(1 + log 13N − u) on [−3δ_N, log(4N+1)] — explicit, no discrepancy assumption (arithmetic enters only through log v! identities).
## SignedPrimePolarFactorialPacketEnvelope
- Envelope e^{u/2}/√N·(1 + log 13N − u); ∫_{window}envelope² ≤ 130 (fixed budget though window grows logarithmically).
## SignedPrimePolarFactorialPolarPacket
- Ramp support [0, log(4N+1)]; full moments: |∫e^{x/2}ramp| ≤ 2/√N, |∫e^{−x/2}ramp| ≤ (5 log(4N+1) + 1)/√N; polar packet splits into two branches with partial moments; |polar packet(u)| ≤ 5e^{u/2}/√N·(1 + log 13N − u) (full harmonic cancellation used before head estimate).
## SignedPrimePolarReflectedTentPacket (start)
- Reflected narrow tent supported in [−2δ, 0]; no prime translates in local window (atomic packet = 0 for u ≥ −3δ, since log m ≥ log 2 > −u); |signed packet| ≤ 6 there.
- Reflected tent signed packet: zero for u ≥ 0, |·| ≤ 6 on [−3δ, 0] ⇒ ∫_{window} packet² ≤ 9/N.
## SignedPrimePolarLocalizedPacket
- Right support bound L ⇒ packet vanishes beyond L and stabilizes in cutoff (A ≤ K, L ≤ u + cutoff A); local Cauchy: pairing(q⋆f)² ≤ ‖q‖²·∫_{[a,b]} packet² when q·packet vanishes off [a,b].
## SignedPrimePolarFactorialLocalEnergy
- Window [−3δ_N, log(4N+1)]; |ramp packet| ≤ 24·envelope ⇒ ∫ ramp packet² ≤ 10⁵. Reflected balanced sources (b = ±): s·ramp ∓ s^{−1}·reflected tent, autocorr same as P/M; local packet energy ≤ 2s²·10⁵ + 2s^{−2}·9/N ≤ 3·10⁵√N; ratio local packet energy/‖source‖² ≤ 50000 (UNIFORM in N).
## SignedPrimePolarFactorialLocalCertificate
- Sources supported in window ⇒ packet stable for all cutoffs ≥ 10(n+1); pairing² ≤ 50000·h(0)² (uniform normalized prime–polar pairing bound); increment pairing² ≤ 6·10⁵√N·(h(0) − h(y)) for |y| ≤ δ_N.
## FactorialCompleteFormCoercivity
- Complete real-space energy = γ(0)·h(0) + LévyEnergy − 2·fullPairing. Normalized: ≥ γ(0) + normalizedJumpLower(n) − 448 → +∞ (|fullPairing| ≤ 224·h(0), normalized Lévy energy ≳ (3/23)e^{−1/2}log N). Eventually strictly positive for both signs. (Statement about the literal real-space expression; spectral identification separate.)
- READING: this factorial family is NOT a counterexample to Weil positivity — the archimedean log N growth dominates the bounded normalized prime–polar term; the arithmetic producer is defeated by its own archimedean cost.
## CompactFiniteJumpWeilFormula (start)
- Compact continuous source with finite physical jump energy ⇒ spectral archimedean symbol × |f̂|² integrable (no derivative needed): physical Lévy jump lintegral = spectral excess lintegral.
- re(weilFullFunctional(Λ, weilTest(f,f))) = γ(0)·h(0) + LévyEnergy(f) − 2·fullPairing(h_f) for every compact continuous f with finite jump energy (exact spectral Weil identity, all prime atoms and both polar branches, no derivatives).
## FactorialWeilCoercivity
- Both reflected factorial source families: literal spectral Weil functional = complete real-space energy; normalized Weil value ≥ γ(0) + (3/23)e^{−1/2}log N − const → +∞; eventually strictly positive. UNCONDITIONAL.
## FactorialWeilGram
- Weil form on span{c·L + d·R} (ramp L, tent R): exact quadratic W(c,d) = c²W(1,0) + d²W(0,1) + cd·mixed, mixed = −∫C_N·w − 2·fullPairing(C_N) (contrast gives all cross terms; contrast(0) = 0).
## FactorialWeilMixedDecay
- |mixed| ≤ (36 log N + const)/√N → 0; Gram error mixed²/(2N) → 0.
## FactorialTentWeilCoercivity
- Pure narrow tent has NO prime atoms (support < log 2) and nonpositive full pairing (pure polar); W(0,1)/N ≥ 6e^{−1/2}log N − 30|γ(0)| → ∞; eventually W(0,1) ≥ N.
## FactorialWeilGramDecoupling
- Eventually: W(c,d) ≥ c²(W(1,0) − GramError) + (W(0,1)/2)d²; exact completion of square W(c,d) = W(0,1)(d + c·mixed/(2W(0,1)))² + c²·minRamp; minRamp ≤ W(1,d) ∀d; 0 ≤ W(1,0) − minRamp ≤ GramError → 0. Tent direction decouples; sign of pure ramp diagonal NOT asserted (open).
## ClampedPrimeLogResummation (start)
- Divisor resummation: Σ_k log k·w(k) = Σ_m Λ(m)Σ_{j≤K/m}w(jm); with collar cutoff, clamped prime factorial sum = Σ_{k≤K} log k·ramp(k/v) exactly; atomic packet of factorial ramp on u ≥ 0 = explicit log-weighted lift field (no arithmetic premise; collar kills products beyond cutoff).
## CompactAutocorrelationPolarMoment
- ∫_{x≥0} 2cosh(x/2)·h_f = (∫e^{u/2}f)(∫e^{−u/2}f) for every compact continuous f (polar term = product of the two exponential source moments; via paperFT at ±i/2).
## FactorialBiNullPolarSign
- chebyshevBiNullProducer(N) = log C(4N,2N) − 2 log C(2N,N) ≥ 0 (Vandermonde: C(2N,N)² ≤ Σ_j C(2N,j)² = C(4N,2N)). Ramp polar term = −(1 + ε/2)·harmonicCorrection·chebBiNull/N ≤ 0: the POLE LOWERS the ramp diagonal (not a positive bonus); |·| ≤ 2(5 log(4N+1) + 1)/N.
## FactorialRampDiagonalIdentity
- Literal prime sum of ramp autocorrelation = ∫ ramp·logField (all von Mangoldt atoms eliminated via divisor resummation); pure ramp Weil diagonal W(1,0) = γ(0)h(0) + Lévy − 2∫ramp·logField − 2(1+ε/2)H·(log C(4N,2N) − 2 log C(2N,N))/N — prime-free explicit archimedean/logarithmic expression; sign not asserted.
## CentralBinomialRatioGrowth
- Ratio C(4N,2N)/C(2N,N)² has exact recurrence; N + 1 ≤ ratio² and ratio²(N+1) ≤ (9/4)(N+1) ⇒ log(N+1)/2 ≤ log ratio ≤ log(N+1)/2 + log(9/4)/2.
## FactorialPolarLossLowerBound
- chebBiNull(N) ∈ [log(N+1)/2, log N/2 + log(9/4)/2]; harmonicCorrection ∈ [N/(2N+1), 1/2] (≥ 1/4); polar loss ≥ log(n+2)/(8(n+1)) > 0; N·loss ≥ log 2/8; ramp polar integral strictly negative.
## FactorialPolarLossAsymptotic
- harmonicCorrection → 1/2; chebBiNull/log N → 1/2; collar → 0 ⇒ N·polarLoss/log N → 1/4 (exact asymptotic coefficient of the literal pole of the compact ramp).
- Signed pole term in ramp Weil diagonal: N·2∫polar·h/log N → −1/2.
## FactorialPolarGramScaleSeparation
- N·GramError → 0 while N·polarLoss ≥ log 2/8 ⇒ GramError/polarLoss → 0; eventually GramError < polarLoss; NOT eventually polarLoss ≤ GramError — closes "polar-absorption shortcut" (the pole cannot be absorbed into the mixed-Gram error budget).
## FactorialMuntzSeed
- Seed on t > 0: ramp(t/4N) − 4ramp(t/2N) + 4ramp(t/N) (as positiveRamp − left step representation); measurable, |·| ≤ 9, support (0, 4N(1+ε)], ∫ = 0 exactly (dilation scaling with coefficients 4 − 8 + 4 = 0), total variation ≤ 10.
## FactorialMuntzCompletion
- Arithmetic (Müntz) sum Σ_j seed(jt) bounded by 10; its Mellin transform VANISHES at every zeta zero with Re ρ > 0 (all premises of CCM BV–Müntz theorem discharged). Completion e^{x/2}·Σ(e^x)/√N agrees EXACTLY with the compact ramp for x ≥ 0; |completion| ≤ 10e^{x/2}/√N.
## FactorialMuntzTail
- Completion − ramp = tail on x ≤ 0; ∫tail² ≤ 100/N → 0 (ramp approximates a zeta-annihilated completion in L²).
## FactorialMuntzReadout (start)
- Readout ∫e^{(s−1/2)x}·completion = Mellin(Σ)(s)/√N (integrable for Re s > 0); at every zeta zero with Re ρ > 0: ramp readout = −tail readout, ‖·‖ ≤ 10/(√N·Re ρ); reflected left source same bound; fixed zero readouts → 0 as N → ∞ regardless of the zero's position relative to the critical line.
## ClampedRampLatticeSum
- Lattice remainder r(y) = {y}(1 − {y})/2 ∈ [0, 1/8]; Σ_{k≥1} max(y − k, 0) = (y² − y)/2 + r(y); clamp = difference of positive parts / ε; exact lattice sum Σ_k ramp((k+1)t/a) = a(1+ε/2)/t − 1/2 + (t/(aε))(r(a(1+ε)/t) − r(a/t)); error ≤ t/(8aε).
## FactorialMuntzBoundaryPole
- Müntz sum = stencil of clamped lattice sums; |Σ(t) + 1/2| ≤ 25t/(32Nε) (zero mean cancels reciprocal sampling scale, endpoint half survives); e^{−x/2}·completion → −1/(2√N) as x → −∞ (nonzero negative-end polar coefficient).
## FactorialMuntzBoundaryRepair
- Corrected completion + c·e^{x/2}1_{x≤0}: negative polar moment integrable ⇔ c = 1/(2√N) (unique); original completion NOT polar-admissible (despite small tail mass and zero readouts). Correction changes readout by exactly c/s for Re s > 0; at every zeta zero the canonical corrected readout = c/ρ ≠ 0 (not a null-source certificate); positive polar moment always integrable.
## FactorialMuntzUniformTail
- N·ε_N ≥ 1/15 ⇒ boundary error ≤ 12/√N uniformly; |Σ(t) + 1/2| ≤ 12t; corrected tail |·| ≤ 12e^{3x/2}/√N on x ≤ 0; readouts integrable on Re s > −1 with ‖·‖ ≤ 12/(√N(Re s + 1)); at zeta zeros |ramp readout| ≤ 1/(2√N|ρ|) + 12/(√N(Re ρ + 1)) (no singularity as Re ρ → 0).
## FactorialMuntzAnalyticRepair (start)
- Regularized sum Σ + (1/2)1_{(0,1]}.
- Regularized sum bounded by 21/2, ≤ 12t near 0, compactly supported ⇒ Mellin holomorphic on Re s > −1; corrected readout = regularized Mellin/√N, analytic on Re s > −1 (proved for source integral itself); uncorrected readout + c/s → corrected value at 0; residue of uncorrected readout at s = 0 is −c_N = −1/(2√N). Tail readouts → 0 UNIFORMLY on closed half-planes Re s ≥ −1 + δ; |ramp zeta readout| ≤ 13/√N uniformly over ALL nontrivial zeros (|ρ| ≥ 4); uniform convergence to 0 on the zero set (does not by itself justify exchanging the infinite Weil zero sum).
## ExponentialDecayCompactConvolution
- Compact kernel convolution preserves e^{−|x|} envelope (weighted kernel mass ∫|κ|e^{|y|}), also for derivative (moved to kernel); C²; exponential tilt commutes with convolution: transform of κ⋆f = product of tilted transforms (Fubini).
## FactorialMuntzWeilSmoothing
- Corrected Müntz source integrable with global e^{−|x|} envelope; mollified versions are ExpDecayTests (C², decay incl. derivative); unit mass; → source a.e.; readout = kernel readout × source readout on Re s > −1; at zeta zeros smoothed readout = kernel·c/ρ, eventually ≠ 0. Decay-class Weil identity holds: archPoleEnergy = re W(zero side) + Abel prime pairing.
## FactorialMuntzZeroReadout (start)
- Kernel readout bounded by e on 0 ≤ Re s ≤ 1 uniformly; paperFT at γ(ρ) = c/ρ; zero-side summand W_ρ = mult·c²/(ρ(1 − ρ)) at EVERY nontrivial zero (incl. hypothetical off-line); smoothed summand = kernel factors × summand → summand; |W_ρ| ≤ 2c²·mult/(1 + |γ|²) (summable genus-one majorant via |Im ρ| ≥ 4).
- re W_ρ = mult·c²·Re(1/(ρ(1−ρ))) > 0 for every nontrivial zero (Re(ρ(1−ρ)) = σ(1−σ) + t² > 0 in open strip).
## FactorialMuntzZeroSideLimit
- Majorant 2c²·mult/(1+|γ|²) summable (zero_sum_inv_sq); uniform for all smoothings (kernel ≤ e); dominated convergence: W(smoothed) → W(corrected); W(corrected) = c_N²·Σ_ρ mult/(ρ(1−ρ)) (universal reciprocal-zero mass × c_N²); Re W(corrected) > 0 WITHOUT RH (uses existence of a zero in strip); smoothed complete Weil difference archPoleEnergy − Abel prime pairing → Re W(corrected) > 0 ⇒ eventually positive; one smoothing threshold works for all n (exact c_N² scaling).
- READING: an explicit arithmetic source family whose Weil zero-side is EXACTLY c²·Σ1/(ρ(1−ρ)) — positive unconditionally because each summand has positive real part regardless of zero location; positivity here is not evidence for RH (works off-line too).
## FactorialMuntzTailSmoothing
- Corrected tail has rate 3/2: |tail| ≤ 12e^{−3|x|/2}/√N; smoothed tail preserves it (×e^{3/2}); ExpDecayTest; paperFT at γ(s) bounded by e·12/(√N(Re s+1)) for 0 ≤ Re s ≤ 1; tail polar term |·| ≤ 144e²/N.
## FactorialMuntzTailPrimePolarBudget
- Tail cross-correlation |·| ≤ (C/N)e^{−5|y|/4}; prime atoms ≤ (2C/N)(1 + log j)j^{−5/4} ⇒ ordinary prime series absolutely convergent = Abel pairing; |prime pairing| ≤ budget/N; prime + polar costs ≤ ε log N/N eventually, uniformly in smoothing; |W(tail) − arch integral(tail)| ≤ (budget + 144e²)/N (tail's non-archimedean cost negligible).
## FactorialMuntzTailPhaseCells (start)
- N·ε_N ≤ 1/12 (cubic collar relation); clamped lattice sum = m exactly on cells avoiding new integers; Müntz sum = 0 exactly on phase intervals N/t ∈ [j, j + 1/16] (j < 2N); phase cells log(N/(j+1/16)) ≤ x ≤ log(N/j) lie in x ≤ 0 for j ≥ N.
- On phase cells (j ∈ [N, 2N)): corrected tail = e^{x/2}/(2√N) exactly (Müntz sum vanishes, only correction left).
## FactorialMuntzTailMass
- N disjoint phase cells in [−log 2, 0], each with ∫tail² ≥ 1/(256N²) ⇒ ∫tail² ≥ 1/(256N) (tail mass NOT smaller than 1/N, cf. upper 100/N); smoothed tails → in L² mass; eventually ≥ 1/(512N); prime + polar error ≤ const × actual tail mass (relative budget independent of N).
## ClampedLatticePrimitive
- Lattice remainder = −periodic Bernoulli B̃₂; centered Bernoulli primitive differentiable through integer joins; collar difference r(a(1+ε)y) − r(ay) = derivative of bounded primitive (|·| ≤ 2/a; constant means cancel).
## FactorialMuntzTailPrimitive
- Müntz sum + 1/2 = t/(Nε)·R(N/t) (exact remainder stencil); remainder has bounded lattice primitive (|·| ≤ 12); corrected tail = −scale·e^{5x/2}·(primitive)' on x ≤ 0 with scale ≤ 15/(N√N).
## FactorialMuntzTailReadoutDecay
- Integration by parts (improper endpoints discharged): tail readout = scale·((s+2)∫e^{(s+2)x}P − P(0)); ‖·‖ ≤ 180/(N√N)·(1 + |s+2|/(Re s+2)); on Re s ≥ 0: ≤ 360(1 + |Im s|)/(N√N); paperFT of tail and smoothed tail ≤ 360e(1 + |τ|)/(N√N) (N^{−3/2} gain over trivial).
## FactorialMuntzTailPrimitiveEnergy (start)
- (1+|τ|)²/(τ² + 1/4)² ≤ 32/(1 + τ²); primitive energy budget 32(360e)²π.
- ∫|paperFT(smoothed tail)|²/(τ² + 1/4)² ≤ budget/N³ uniformly in smoothing; relative to actual tail mass ≤ (512·budget/N²)·mass (primitive energy decays by two powers).
## ExpDecayFourierMass
- ExpDecayTest ⇒ integrable, |paperFT| ≤ M/(1+|r|) (incl. truncations), |paperFT|² integrable, Parseval ∫|paperFT|² = 2π∫F² (noncompact), |paperFT|²·γ(r) integrable (|γ(r)| ≤ K + 2√(1+|r|)).
## FactorialMuntzTailArchimedeanGrowth
- Scalar quarter estimate on actual noncompact source: (b − C + 1/4)·mass ≤ archEnergy + e^{4b}/(8π)·primitive energy; with b = log N/2 and primitive energy O(N^{−3}): archEnergy ≥ (log N/2 − archLoss)·mass eventually in smoothing.
## FactorialMuntzTailWeilGrowth
- Re W(smoothed tail) ≥ (log N/2 − WeilLoss)·mass; for every B, eventually (n, then k) Re W ≥ B·mass (normalized Weil energy of tails → ∞); Re W ≥ log N/(2048N) > 0 eventually.
- READING: lattice cancellation (tail Fourier transform ≈ N^{−3/2}·(1+|τ|), primitive energy N^{−3}) forces the tail's spectral mass to high frequency, where the archimedean symbol log|τ| dominates — the Müntz/Nyman–Beurling-type correction tail is archimedean-coercive with log N growth.
## ThetaInnerLargeActionCurrent (namespace RHTower.ThetaCuspDefect, filed under BSU)
- Inner chamber 0 < t ≤ min(2,u): curvature e(u,s) ≤ c(u)e^{2s}; primitive E ≤ c(u)·t·e⁴; clock mass 30kE ≤ θZ when 4050e⁴ ≤ θ²Z; clock elasticity < θZ + 18; enriched clock current > 0 whenever clock elasticity < 1 + 12Z/5; unconditional positivity for action Z ≥ 710e⁴ (method reaches Z > (5625/8)e⁴); bounded-action remainder open.
## SquarefreeCancellationTransfer (namespace RHTower.SquarefreeDiscrepancy, filed under BSU; start)
- Möbius Abel summation with both boundary terms; weighted telescoping; |Σ_{D<n≤R} μ(n)w(n)| ≤ δ(2Dw(D) + Σw) given |M(n)| ≤ δn beyond D and w ≥ 0 decreasing.
- |Σ_{n≤D}μ(n)/n² − 6/π²| ≤ 3δ/D; squarefree count: |Q(N) − (6/π²)N| ≤ D + 6δN/D for any cutoff D with Mertens bound δ beyond D (free truncation, not necessarily √N).
## SquarefreeCriticalLogEnvelope (RHTower.SquarefreeDiscrepancy)
- Using unconditional |M(n)| ≤ Bn/log²n and D ≈ e^{t/2}/t: |E(e^t)|·e^{−t/2} ≤ C/t eventually (squarefree discrepancy critical source has reciprocal-log envelope, unconditional).
## SquarefreeUnweightedHilbertSource (RHTower.SquarefreeDiscrepancy)
- Unweighted critical source 1_{t>0}E(e^t)e^{−t/2} ≤ C/(1+|t|) ⇒ in L² (no auxiliary (1+t)^{−1} weight); ∫_{x>1}E(x)²/x² finite = ∫|source|²; ⟨source, evaluation_s⟩ = Mellin moment(s) for Re s > 1/2. Removes source-admission obstacle; inverse-overlap Sonin comparison remains open.
## MertensValuationBudget (namespace RHTower)
- primeRecipSum = mertensS; two Meissel–Mertens constant definitions agree; higher-prime-power defect has favorable sign; log N·e^{−c√log N} → 0 ⇒ eventually (∏(1−1/p))^{−1} ≤ e^γ log N·e^{a/log N} for every a > 0 (unconditional).
## RobinMovingValuationDefect (namespace RHTower; start)
- Valuation defect Σ_{p≤N} p^{−(v_p(n)+1)} at cutoff N = ⌊log n⌋.
- σ(n)/n ≤ e^γ log log n·exp((1+ε)/log log n − valuation defect at cutoff ⌊log n⌋) eventually (unconditional, defect retained); Robin counterexamples have defect ≤ (1+ε)/log log n; ⇒ every prime power (and every integer m) ≤ η log log n divides every sufficiently large Robin counterexample, for each η < 1 (growing lcm core).
## HyperbolicMultiplierIncrementAndOddSignCoercivity (Pillar XVI)
- Exact: (h_{C_αf}(0) − h_{C_αf}(x)) + 2sinh²(αx/2)h_f(0) = cosh(αx)(h_f(0) − h_f(x)) + (h_{S_αf}(0) − h_{S_αf}(x)) (both RHS terms ≥ 0) ⇒ sinh- and cosh-weighted source increments dominated by cosh-multiplier increment + 2sinh²h(0). Signed collar leverage applies to S_αf and C_αf with no multiplier blindness; at source zeros h_f(t) = 0, h_{C_αf}(t) = h_{S_αf}(t) ⇒ leaked multiplier value + C-collar defect ≥ (w − w²/2W₀)(h_f(0) + h_{S_αf}(0)) (+ hyperbolic shift bonus) — resolves odd multiplier leakage trap.
## EulerMaclaurinLevyQuadratureAndSFreeCellBounds (Pillar XVII, start)
- Exact cell quadrature identity (∫ρ)h(t) − ∫ρh = ∫_0^δ ρ(t+y)(h(t) − h(t+y)); pointwise ρ|h(t) − h(t+y)| ≤ W₀D(y) + ρ²h(0)/(2W₀) ⇒ S(f)-free (derivative-free) cell bound; Nyquist cell origin integral ≤ (1/n)∫D·w; W₀ = ηn ⇒ cell error ≤ η∫D·w + h(0)/(2ηn)∫ρ²; dyadic window: all N cells charge Lévy collar once.
- Global dyadic quadrature: |Σ_k(∫ρ)h(log(N+k)) − ∫_{log N}^{log 2N}ρh| ≤ η·LévyEnergy + h(0)/(2η)∫ρ². Polar cell weight ∫e^{x/2} = 2(√(n+1) − √n), ∫e^x = 1; polar cell quadrature: |2(√(n+1) − √n)h(log n) − ∫e^{x/2}h| ≤ η∫D·w + h(0)/(2ηn). On RealEvenPolarTestFn (unconditional): polar cell discrepancy ≤ weilArchRe + (|Ω(0)| + 1/(2(n+1)))·h(0).
## MultiShellOriginBudgetAndGlobalPrimeCollarSynthesis (Pillar XVIII)
- archLevySinhWeight(x) = 2/(e^{x/2} − e^{−3x/2}), strictly antitone on (0,∞); ≥ 2/√(n+1) on (0, log(n+1)]; shifted collar ×2/√(n+1) ≤ Lévy integral over cell. Origin interval (0, log(1+1/N)] ⊂ (0, log N] disjoint from dyadic window (log N, log 2N] ⇒ origin + window Lévy ≤ one LévyEnergy. Adaptive cell coercivity with w = 2/√(n+1), W₀ = n/N (coefficient ≥ 2/√(n+1) − 2/(n+1) > 0). GLOBAL DYADIC NYQUIST SIGNED COERCIVITY (unconditional, no blindness): (Σ_k δ_k(2/√(N+k+1) − 2/(N+k+1)))·h(0) ≤ LévyEnergy + Σ_k δ_k·(2/√(N+k+1))·h(log(N+k)).
## SignedWeilFunctionalCoercivityAndRHBridge (Pillar XIX, start)
- C_Nyq(N) := Σ_k δ_k(2/√(N+k+1) − 2/(N+k+1)) > 0 for N ≥ 2.
- weilArchRe(weilTest g g) = Ω(0)h(0) + LévyEnergy(source) on RealEvenPolarTestFn; unconditional dyadic signed Weil lower bound (Ω(0) + C_Nyq(N))h(0) ≤ weilArchRe + Σ_k δ_k(2/√(N+k+1))h(log(N+k)); single-node version; smooth specialization; cosh-multiplier version controls h_g(0) + h_{S_αg}(0); sinh-multiplier version.
- NOTE: these lower bounds have the signed grid sum on the RIGHT with positive coefficients — they bound h(0) by arch energy PLUS a positively weighted grid sum; they do not by themselves give Weil positivity (the explicit-formula prime sum has the opposite sign/weights Λ(n)/√n).
## AllScaleCriticalLineOriginConvergenceAndSynthesis (Pillar XX)
- Canonical weight ϖ_n = √2·n(1/√n − 1/√(n+1)) ≤ 2/√(n+1) ≤ archLevySinhWeight on (0, log(n+1)]; self-matched w = W₀ = ϖ gives coefficient ϖ/2; origin shares ϖ_n/n = √2(1/√n − 1/√(n+1)) telescope: Σ_{n=2}^{N+1} = 1 − √2/√(N+2) ≤ 1; every Nyquist step ≤ log 2 ⇒ first-prime origin window (0, log 2] + tail [log 2, log(N+2)] ≤ one LévyEnergy. ALL-SCALE signed coercivity: C_all(N)h(0) ≤ LévyEnergy + Σ_{n=2}^{N+1}δ_nϖ_n h(log n), C_all(N) = Σδ_nϖ_n/2 > 0, monotone in N; Weil version (Ω(0) + C_all(N))h(0) ≤ weilArchRe + Σδ_nϖ_n h(log n); multiplier versions.
## VonMangoldtWeilExplicitFormulaAndChebyshevBridge (Pillar XXI)
- θ_Λ(n) = Λ(n)/log n ∈ [0,1] (=1 at primes, 0 off prime powers); w_Λ = θ_Λϖ_n; with W₀ = ϖ_n: w − w²/(2ϖ) ≥ w/2 (θ(1−θ)/2 ≥ 0). Von Mangoldt all-scale signed coercivity: C_{Λ,all}(N)h(0) ≤ LévyEnergy + Σ δ_n w_Λ(n) h(log n) (C_{Λ,all} > 0, monotone) and Weil version; cosh-multiplier version.
- RealEvenPolarTestFn: polar integral ∫_{x>0}h(x)cosh(x/2) = 0 UNCONDITIONALLY (from exact Weil arch form identity) ⇒ positive and negative polar lobes have equal cosh-mass; weilArchRe ≥ 0 ⇔ |Ω(0)|h(0) ≤ LévyEnergy; truncated prime sum Σ_{n≤N+2}Λ(n)/√n·h(log n) = pairing_N(h) − polar tail beyond log(N+2).
## ChebyshevWeilExplicitFormulaAndUnconditionalSynthesis (Pillar XXII, start)
- RealEvenPolarTestFn embeds into C_c; annular Lévy integral ≤ LévyEnergy = weilArchRe + |Ω(0)|h(0); prime sum + polar tail = pairing_N; |prime sum + polar tail − chebyshevWork| ≤ e^c(weilArchRe + |Ω(0)|h(0)) + packetEnergy/(2e^c e^{2b})·∫e^{−y/2}sinh y.
- Chebyshev–mass–Weil: |prime sum + polar tail − chebyshevWork| ≤ mass(N)(e^c(weilArchRe + |Ω(0)|h(0)) + h(0)/(2e^c e^{2b})∫e^{−y/2}sinh y). Joint synthesis = conjunction of all-scale Λ coercivity, lobe conservation, Chebyshev–packet bound.
## WeilFullFunctionalAndPrimitiveHyperplaneBridge (Pillar XXIII)
- On RealEvenPolarTestFn: logValue(g,n) = 2h(log n)/√n; poleWeightArchRe(β) = weilArchRe for every β (pole term re = 0 on even polar class); weilPoleWeightFunctional re = weilFullFunctional re.
- supportScale(g) = ⌈e^{supportRadius}⌉: beyond it polar tail = 0 and prime sum = pairing_N exactly; Λ-linear combination of logVector = 2·pairing_N.
- EXACT FULL WEIL IDENTITY (unconditional): Re W_Λ(g*g̃) = Ω(0)h(0) + LévyEnergy(g) − 2·pairing_{supportScale}(h). So Weil positivity on this class ⇔ 2·pairing ≤ Ω(0)h(0) + LévyEnergy (Ω(0) < 0).
- |Re W_Λ − (weilArchRe − 2chebyshevWork)| ≤ 2e^c(weilArchRe + |Ω(0)|h(0)) + packetEnergy/(e^c e^{2b})∫e^{−y/2}sinh y; lower bound form; all-scale lower bound (Ω(0) + C_{Λ,all}(N))h(0) ≤ Re W_Λ + 2pairing + Σδ w_Λ h(log n) (tautological rearrangement — pairing appears on the right).
## MultiNodeSignedCliqueWeilCoercivity (Pillar XXIV)
- Gram identity: ∫(Σw_i f(u+t_i))² = ΣΣ w_iw_j h(t_i − t_j) ≥ 0 = (Σw_i²)h(0) + off-diagonal. Multi-node signed collar (no blindness): (Σw − Σw²/(2W₀))h(0) ≤ W₀(h(0) − h(y)) + Σw_i(h(0) − h(t_i+y)) + Σw_ih(t_i) + (1/2W₀)·offDiag (Cauchy–Schwarz of P = Σw f(·+t_i) against D = f(·−y) − f + Young).
- Dyadic coset nodes log((m+1)2^{k+1}): differences (i−j)log 2 independent of m ⇒ off-diagonal Gram entries are prime-2-power correlations h(log 2^{|i−j|}).
## HyperbolicGaugeChebyshevEnergyRepresentation (ChebyshevGauge namespace)
- Ẽ(t) = e^{−t/2}(ψ(e^t) − e^t); gauge derivative f' − f/2 = e^{u/2}(e^{−u/2}f)'.
- Stieltjes against ψ: ΣΛ(n)G(log n) − ∫_0^L G e^x = G(0) + G(L)(ψ(e^L) − e^L) − ∫_0^L G'(ψ(e^x) − e^x).
- POINTWISE PACKET IDENTITY: signed packet P(u) = Σ_{n≤N+2}Λ(n)n^{−1/2}f(u+log n) − ∫_0^L 2cosh(t/2)f(u+t) = [f(u) − ∫_0^L e^{−t/2}f(u+t)] + Ẽ(L)f(u+L) − ∫_0^L Ẽ(t)(f' − f/2)(u+t)dt. Origin value f(u) comes from ψ(1) − 1 = −1 boundary; e^{−t/2} half of cosh gives forward residual.
- packetEnergy = ∫(R + Ẽ(L)f(·+L) − Df)²; ∫(Df)² = ∫∫Ẽ(s)Ẽ(t)·autocorr(f' − f/2)(t − s) (positive-definite kernel); Young: ∫(Df)² ≤ ‖f' − f/2‖₁²∫_0^LẼ²; packetEnergy ≤ 3(10 + Ẽ(L)²)h(0) + 3‖f' − f/2‖₁²∫Ẽ²; converse ∫(Df)² ≤ 3packetEnergy + 3(10 + Ẽ(L)²)h(0). ∫_0^LẼ² = ∫_1^{e^L}(ψ(x) − x)²/x² dx.
- ⇒ uniform packet-energy stabilization over all C¹ sources ⇔ (up to source constants) ∫_1^X(ψ − x)²/x² = O(log X) — an RH-equivalent mean-square Chebyshev statement (RH ⇒ this; this ⇒ RH via standard Landau-type arguments). So the packet-energy route is exactly the mean-square PNT error.
- Proof details: D = line convolution of (f' − f/2) with reflected window Ẽ·1_{[0,L]}; forward residual energy ∫R² ≤ 10h(0) (window mass ∫_0^Le^{−t/2} ≤ 2, weighted Cauchy–Schwarz, ∫(windowed f²) = mass·h(0)); ∫B² = Ẽ(L)²h(0); (a+b−c)² ≤ 3(a²+b²+c²).
## ChebyshevGaugeNyquistCellQuadrature
- On cell [log n, log(n+1)) ψ(e^t) = ψ(n); ∫_cell e^{−t}(c − e^t)² = c²/(n(n+1)) − 2c·log((n+1)/n) + 1. Cell energy ∫_cell Ẽ² = (ψ(n) − m_n)²/(n(n+1)) + c_n, m_n = n(n+1)log(1+1/n) ∈ [n, n+1], c_n = 1 − n(n+1)log²(1+1/n) ∈ [0, 2/(n(n+1))].
- Σ_{n<M}(ψ(n) − m_n)²/(n(n+1)) ≤ ∫_0^{log M}Ẽ² ≤ same + 2: mean-square Chebyshev error = discrete critical-line-weighted mean square of centred ψ(n) up to universal constant.
- c_n = ∫_cell e^{−t}(m_n − e^t)² ≤ 2/(n(n+1)) (integrand ≤ 1/n, cell length ≤ 1/n), Σc_n ≤ 2 (telescoping). Dyadic window law: ∫_{log N}^{log 2N}Ẽ² = Σ_k[(ψ(N+k) − m_{N+k})²/((N+k)(N+k+1)) + c_{N+k}]. Comparison with classical E(n) = ψ(n) − n: ½ΣE²/(n(n+1)) − 1 ≤ ∫_0^{log M}Ẽ² ≤ 2ΣE²/(n(n+1)) + 4 (|m_n − n| ≤ 1).
## CausalExponentialResponseAndLaplaceEnergy
- Signed prime–polar measure ν_N = ΣΛ(n)n^{−1/2}δ_{log n} − 2cosh(t/2)1_{[0,L]}dt. Causal kernel K(x) = e^{−x/2}1_{x≥0}; autocorr K = Laplace kernel e^{−|x|/2}.
- Response K⋆ν_N on [0,L] = Ẽ(t) + (1 − t)e^{−t/2} (universal transient from polar ∫_0^t(e^s + 1)); 0 for t < 0; beyond L decays e^{−(t−L)/2}·value(L); |K⋆ν_N| ≤ mass·e^{L/2}·K.
- ∫(K⋆ν_N)² = laplaceEnergy N = ∬e^{−|s−t|/2}dν_N dν_N (Fubini exchange of pairing with dominated line integral).
- laplaceEnergy ≥ 0; = ∫_0^L(Ẽ + (1−t)e^{−t/2})² + (Ẽ(L) + (1−L)e^{−L/2})² (tail ∫_{>L} = value(L)²); transient energy ∫_0^L(1−t)²e^{−t} = 1 − (L²+1)e^{−L} ≤ 1; ∫Ẽ² ≤ 2·laplaceEnergy + 2; laplaceEnergy ≤ 2∫Ẽ² + 2 + boundary². Mean-square PNT error = Laplace Gram energy of ν_N (positive-definite kernel).
## CausalCorrelationPacketRepresentation
- Causal reconstruction f(u) = −∫K(t)(f' − f/2)(u+t)dt (K inverts the gauge derivative). Packet P_f(u) = −∫R_N(t)g(u+t)dt, g = f' − f/2, R_N = K⋆ν_N.
- packetEnergy = ∬R_N(t)R_N(s)autocorr_g(s − t) = ⟨autocorr g, autocorr R_N⟩_{L²}; Young: packetEnergy ≤ ‖g‖₁²·laplaceEnergy N. Green: autocorr f = autocorr g ⋆ e^{−|·|/2}. packetEnergy = ∬(autocorr g ⋆ Laplace)(s − t)dν_N dν_N.
- ⇒ all arithmetic content of every compact packet is in the single response R_N; every compact Gram energy = Laplace Gram energy filtered by positive-definite kernel.
## SpectralLaplaceEnergyCriticalLine (start)
- 𝓕R_N(ξ) = ν̂_N(ξ)/s(ξ), s = ½ + 2πiξ; laplaceEnergy = ∫|ν̂_N|²/(¼ + 4π²ξ²)dξ; ν̂_N(ξ) = Σ_{n≤N+2}Λ(n)n^{−s} − (e^{(1−s)L} − 1)/(1 − s) − (1 − e^{−sL})/s (pole-subtracted truncated −ζ'/ζ on critical line). Complex pairing pairingC, ‖pairingC h‖ ≤ mass·sup|h|, Fubini exchange.
- 𝓕K(ξ) = 1/s(ξ); |ν̂_N| ≤ mass N; ∫Ẽ² ≤ 2∫|ν̂_N|²/|s|² + 2. Atoms: Λ(n)n^{−1/2}e^{−2πiξ log n} = Λ(n)n^{−s(ξ)}; polar 2cosh(x/2)χ_ξ = e^{(1−s)x} + e^{−sx}.
## PrimeShellMellinMassBudget
- Square shell (m², 2m²]: half-mass Σp^{−1/2} ≤ m (≤ m² primes, each ≤ 1/m). Quadratically damped shell sum ‖Σ_{shell}p^{−s}/(s+1)²‖ ≤ halfMass·‖1/(s(1−s))‖ in strip (|s(1−s)| ≤ |s+1|²). Loud-mode count: #{i: |damped(s_i)| ≥ L}·L ≤ m·Σ‖1/(s_i(1−s_i))‖ (no separation). Above |Im s| ≥ 1: Re(1/(s(1−s))) ≥ ‖1/(s(1−s))‖/2 (uniform acute cone).
## CompensatedHausdorffPhase
- Budget B = |nτ − rσ| + (n|τ|³ + r|σ|³)/3 bounds |n arctan τ − r arctan σ|; Re((1+iτ)^n(1−iσ)^r) = |·|cos(phase) ≥ (1 − B²/2)|·|; B ≤ 1 ⇒ Re ≥ |·|/2. Opposite rotations cancel linearly; only cubic remainders paid absolutely.
## HausdorffSaddleScale
- For u ∈ [T, T+H], slope a ∈ [1/u², 1/(u²−1)], r = nT²: 0 ≤ a ≤ 1, ra ≤ 2n, |n − ra| ≤ 4nH/T; with |τ| ≤ 2/T and T² ≥ 32nH: B(n, r, τ, aτ) ≤ 5/16. Quadratic scale T² ≳ nH controls a whole band.
## HighFrequencyLaplaceEnergyMeanValue
- Spectral density S_N(ξ) = |ν̂_N|²/(¼ + 4π²ξ²) ≤ mass²/(2πξ)²; ν̂ = A_N − P_N; |P_N| ≤ (e^{L/2} + 3)/|s|; A_N = Dirichlet polynomial with coefficients Λ(n)/√n at t = −2πξ.
- Montgomery–Vaughan (sharp, corpus): ∫_{−u}^u|A_N|² ≤ 2uD₁ + 208D₂, D₁ = ΣΛ²/n, D₂ = ΣΛ². IBP against 1/u²: ∫_{T₀}^{T₁}(|A(u)|² + |A(−u)|²)/u² ≤ 4D₁/T₀ + 208D₂/T₀².
- Window law ∫_{ξ₀}^{ξ₁}(S(ξ) + S(−ξ)) ≤ 2D₁/(π²ξ₀) + 52D₂/(π³ξ₀²) + 4(e^{L/2}+3)²/(3(2π)⁴ξ₀³), tail same; laplaceEnergy = band(|ξ| ≤ ξ₀) + tail. D₂ ≤ Lψ(N+2), D₁ ≤ LΣΛ/n.
## BandLimitedLaplaceEnergy (start)
- Mertens ΣΛ(n)/n ≤ L + log 4 + 4; ψ(x) ≤ (log 4 + 4)x. Band frequency ξ₀ = √(N+2) = e^{L/2}; L ≤ 4√ξ₀.
- BAND THEOREM (unconditional): laplaceEnergy ≤ ∫_{|ξ|≤√(N+2)}S_N + (52(log 4 + 4)/π³)L + O(1). ⇒ Σ(ψ(n) − n)²/(n(n+1)) = O(log x) ⇔ band energy ∫_{|ξ|≤√x}|ν̂_x|²/|s|² = O(log x). Square-root barrier = bounded average energy of pole-subtracted truncated −ζ'/ζ on critical-line band |t| ≤ 2π√x (bi-scale: position √x × frequency √x).
- Remainder ≤ (52(log 4+4)/π³)L + (32 + 8(log 4+4))/π² + 4/(3π⁴) (b² = N+2 cancels exactly in D₂ term). band ≤ laplaceEnergy. Wall-1: ∫Ẽ² ≤ 2·band + O(L); band ≤ 2∫Ẽ² + 2 + boundary².
## BandSpectrumZeroWidthLaw
- Three rates (mean-square band ∫_0^LẼ² ≤ Ce^{2βL}, Laplace energy ≤ C(N+2)^{2β}, spectral band ≤ C(N+2)^{2β}); for 0 ≤ α < ½: XiZeroHalfPlaneBound α (all zeros Re ≤ ½+α) ⇔ every β > α rate holds, for each of the three.
- Band ⇒ width: resolvent Q(t) = e^{−t}(∫_0^te^hẼ − 2/3) ≤ (C+1)e^{βt} via 2|ab| ≤ μa² + b²/μ at μ = e^{(β−1)t}; exponentially bounded resolvent continues critical-Mellin defect (corpus RHTower CCM). Width ⇒ band: generalized von Koch |Ẽ| ≤ Ce^{βt}.
- Spectral band rate ⇔ Laplace rate for β > 0 (linear remainder absorbed).
- ENDPOINT: RH ⇒ ∫_0^LẼ² ≤ C(1+L) (Cramér dyadic mean square, corpus); RH ⇔ linear band ⇔ every subexponential band (for all three). SELF-IMPROVEMENT: e^{o(L)} band ⇒ O(L) band; no growth strictly between linear and exponential.
## BandSlopeZeroEnergyLaw (start)
- Claim: linear band ∫Ẽ² ≤ C(1+L) + K ⇒ Σ_k n_k²/|ρ_k|² ≤ C over critical zeros (orders of (s−1)ζ); multiplicity ≤ √C|ρ|. Mechanism: Laplace transform L(z) = ∫e^{−zt}Ẽ holomorphic on Re z > β = −((ζ_u'/ζ_u)(z+½) + 1)/(z+½); Abel coefficient σL(β+σ+iγ) → −n/ρ; IBP converts band bound into Abel energy σ∫e^{−σt}Ẽ²; Abel-orthonormal characters ⇒ Bessel inequality.
- Laplace transform = continuation on Re z > β (identity theorem); Abel coefficient σL(β+σ+iγ) → −n/ρ (log-derivative residue). IBP: ∫_0^TF² ≤ g(T) ⇒ ∫e^{−at}F² ≤ M. Linear band ⇒ Abel energy σ∫e^{−σt}F² ≤ C(1+σ) + Kσ. ∫_0^∞e^{−σt}e^{−iΔt} = 1/(σ+iΔ) ⇒ Abel-orthonormal characters. ABEL–BESSEL: Abel energy limit A, Abel coefficients c_k at distinct γ_k ⇒ Σ|c_k|² ≤ A (2|ab| ≤ a² + |b|² against φ = Σ conj(c_k)χ_k).
- BAND SLOPE ⇒ ZERO ENERGY: ∫Ẽ² ≤ C(1+L) + K ⇒ Σ n_k²/(¼ + γ_k²) ≤ C; n² ≤ C(¼ + γ²). Linear band forces C ≥ 0.
## BandExtremalLineLaw
- Exponential band ∫Ẽ² ≤ Ce^{2βL} + K (0 < β < ½) ⇒ Σ_k n_k²/((½+β)² + γ_k²) ≤ 2βC over zeros on Re = ½ + β (tilted error e^{−βt}Ẽ, Abel energy ≤ C(2β+σ) + Kσ).
- Zeros of (s−1)ζ have positive integer order; Hardy's theorem (corpus) gives a critical zero. UNCONDITIONAL: square-root barrier never sublinear — no ∫_0^LẼ² ≤ c(1+L) + K for all c > 0. Linear floor at each critical zero: slope ≥ n²/|ρ|². Off-line floor: zero at Re = ½+β with 2βC < n²/|ρ|² makes ∫Ẽ² − Ce^{2βL} unbounded.
## ProbeResolutionLaw
- Stationary gauge convolution Φ_f(τ) = ∫_0^∞Ẽ(t)g(t − τ)dt (g = f' − f/2). Gauge factor ĝ(iγ) = −ρf̂(γ), ρ = ½ + iγ (IBP): gauge derivative cancels the 1/|ρ| height damping exactly.
- Laplace factorization ∫e^{−zτ}Φ_f = ĝ(z)L(z) (convolution of integrable F₁, G₁). Under RH: Abel coefficient σ∫e^{−σt}Φ_f e^{−iγt} → n f̂(γ).
- PROBE RESOLUTION (conditional on RH as hypothesis): ∫_0^LΦ_f² ≤ C(1+L) + K ⇒ Σ n_k²|f̂(γ_k)|² ≤ C. Bare band weighs zero by n²/|ρ|²; a probe by n²|f̂(γ)|² — no height loss.
## ProbeParsevalLaw (start)
- characterMean (1/L)∫_0^Le^{iΔτ} → 0 for Δ ≠ 0 (≤ 2/(|Δ|L)); Parseval for absolutely convergent almost periodic series: (1/L)∫_0^L|Σa_ie^{iγ_iτ}|² → Σ|a_i|² (distinct real γ_i).
- Packet explicit formula (unconditional, from Zeta23 EF_lit_zetaZeroConfig for translate f(· − τ)): for compact C² f supported in [−w,w] and τ > w, Σ_ρ m_ρe^{iγ_ρτ}f̂(γ_ρ) = A_f(τ) − P_f(τ), P_f(τ) = ΣΛ(n)n^{−1/2}f(log n − τ) − ∫_0^∞2cosh(x/2)f(x − τ), A_f = (1/2π)∫e^{irτ}f̂(r)Ω(r)dr. Negative logs drop out beyond support; two pole terms = polar density.
- f̂Ω integrable (|f̂|(1+r²) ≤ M, |Ω(r)| ≲ √(1+|r|)); A_f → 0 (Riemann–Lebesgue), continuous. Cesàro means of functions → 0 vanish.
- PROBE PARSEVAL (under RH hypothesis): (1/L)∫_w^LP_f² → Σ_ρ m_ρ²|f̂(γ_ρ)|² (packet = Bohr almost periodic with coefficients −m_ρf̂(γ_ρ) + vanishing tail). Probe band slope attained exactly.
## PacketBoundednessCriterion (start)
- Beyond support: P_f(τ) = A_f(τ) − Σ_ρc_ρe^{λ_ρτ}, λ_ρ = ρ − ½, c_ρ = m_ρf̂(γ_ρ). Zero resolvent R(z) = Σc_ρe^{(λ_ρ−z)b}/(z − λ_ρ) holomorphic off locally finite {λ_ρ} (countable carrier), residue c_ρ at λ_ρ; termwise Laplace ∫_b^∞e^{−zτ}G = R(z) for Re z > ½.
- Half-plane minus countable set preconnected ⇒ if R agrees with holomorphic L on Re z > σ, then c_ρ = 0 for depth Re λ_ρ > σ. Growth |G| ≤ Ke^{στ} ⇒ Laplace of e^{−στ}G holomorphic on Re z > σ ⇒ c_ρ = 0 at depth > σ.
- For any complex ξ a small normed bump has f̂(ξ) ≠ 0. PACKET GROWTH LAW (unconditional): P_f = O(e^{στ}) ⇔ f̂(γ_ρ) = 0 at every zero of depth Re ρ − ½ > σ. Packet bounded ⇔ f blind to all zeros right of line. RH ⇔ every compact C² packet eventually bounded. Zero width β ⇔ every packet O(e^{βτ}).
## PacketOneSidedGrowthLaw
- One-sided bound suffices: P_f ≤ Ke^{στ} eventually (or ≥ −Ke^{στ}) ⇔ blind to zeros deeper than σ. Mechanism: εe^{σu} − ηP_f1_{u>b} is a nonnegative measure density; Laplace = ε/(z−σ) − η(L_A − R); analytic at every real t > σ because ζ has no real zero in the critical strip (no shifted zero is positive real); Landau ⇒ abscissa σ ⇒ R continues to Re > σ ⇒ residues vanish.
- RH ⇔ every compact packet eventually bounded above ⇔ every one bounded below. Zero width = universal one-sided packet exponent. Ω± oscillation: a source seeing a zero of depth > σ has packet > Ke^{στ} and < −Ke^{στ} at arbitrarily large τ.
## PacketWeilEnergyLaw (start)
- Packet energy weights critical zero by m²|f̂|², Weil functional by m|f̂|². If P_f bounded above (unconditional): (1/L)∫P_f² → E(f) = Σ_{critical}m²|f̂(γ)|²; W(f) = Σ_{critical}m|f̂(γ)|²; 0 ≤ W ≤ E; W = E ⇔ all seen critical zeros simple. Field form: 0 ≤ Ω(0)h(0) + LévyEnergy − 2⟨h,ν⟩ ≤ lim(1/L)∫P_f². Grid-blind polar source (pairing 0) ⇒ bi-scale uncertainty |Ω(0)|h(0) ≤ LévyEnergy from a one-sided bound on one linear packet. Under RH: all zeros simple ⇔ packet energy = Weil energy for every source.
- Off-critical zero series → 0 when blind right of line (left terms decay).
- Blind packet = B − criticalSeries, B → 0; unconditional packet Parseval for blind sources → E(f). conj γ_ρ = γ_{1−ρ̄}; ĥ_f(γ) = f̂(γ)·conj f̂(conj γ); Weil functional of blind source = critical Weil energy W(f). W ≤ E with equality iff seen critical zeros simple (m ≤ m²).
- Field form: Ω(0)h(0) + LévyEnergy − 2pairing = W(f) ∈ [0, E(f)] when packet bounded above. pairing = 0 + packet bounded above ⇒ 0 ≤ Ω(0)h(0) + LévyEnergy ≤ E(f). Under RH: all zeros simple ⇔ packet energy = Weil energy for every source.
## PacketPersistenceLaw
- Every nonzero compact source sees a critical zero (corpus: transform entire of exponential type cannot vanish on superlinearly dense simple critical ordinates) ⇒ E(f) > 0, W(f) > 0. STRICT bi-scale uncertainty |Ω(0)|h(0) < LévyEnergy for nonzero real Weil test with pairing 0 and packet bounded above.
- ζ(½) ≠ 0 ⇒ critical ordinates nonzero ⇒ Bohr mean 0. Sign from mean & energy: mean 0, mean square E > 0, |p| ≤ M ⇒ p > E/(2(M+1)) infinitely often ((p+M)(p−c) ≤ 0 averaging).
- PACKET PERSISTENCE (unconditional): every nonzero compact C² source has c > 0 with P_f > c and P_f < −c at arbitrarily large τ; no nonzero packet converges.
## ProbeAmplitudeLaw (start)
- |P_f| ≤ A eventually ⇒ E(f) ≤ A². Dilate f_t(u) = f(u/t): if ∫f ≠ 0, E(f_t) ≥ c·t log(1/t) for small t (f̂_t(ξ) = tf̂(tξ), |f̂| ≥ |∫f|/2 near 0, ≥ (72π)^{−1}(ξ₀/t)log(ξ₀/t) simple critical zeros, corpus). Probe amplitude law: |P_{f_t}| > √(ct log(1/t)) infinitely often; energy per unit source energy ~ log(1/t) = zero density.
- limsup|P_f| ≥ √E(f) unconditionally. Proof constants: |f̂| ≥ a/2 on |ξ| ≤ ξ₀, each simple critical zero of height ≤ ξ₀/t contributes t²a²/4; c = a²ξ₀/(576π). PROBE AMPLITUDE LAW (unconditional): ∫f ≠ 0 ⇒ |P_{f_t}| > √(c·t·log(1/t)) at arbitrarily large τ for small t.
## MultiplicitySpectroscopyLaw
- Tuned probe f_R(u) = φ(u/R)cos(γ₀u): f̂_R(ξ) = (R/2)(φ̂(R(ξ−γ₀)) + φ̂(R(ξ+γ₀))). Weighted scaled energy Σv_ρ|φ̂(R(γ−γ₀)) + φ̂(R(γ+γ₀))|² → 2v_{ρ₀}|φ̂(0)|² (dominated by m/(1+γ²), summable; 1+γ² ≤ 2(1+γ₀²)(1+(γ−γ₀)²)).
- UNCONDITIONAL: E(f_R)/W(f_R) → m_{ρ₀}. Under RH: E = packet mean square, W = Weil functional ⇒ multiplicities are prime-side observables.
## UniversalProbeLaw (start)
- Boost e^{tu}φ(u): transform translates f̂(z − it). For each zero t ↦ φ̂(γ_ρ − it) is nonzero entire (φ̂ not identically 0 on ℝ) ⇒ countably many bad t; countably many zeros ⇒ all but countably many boosts of any nonzero φ ∈ C²_c are UNIVERSAL probes (see every zero).
- For universal U: RH ⇔ single packet P_U bounded above; zero width β ⇔ P_U ≤ Ke^{βτ}; deeper zero ⇒ P_U oscillates beyond ±Ke^{στ}.
- Universal U: RH ⇔ P_U bounded ⇔ bounded above. Every nonzero φ ∈ C²_c has a boost t whose single packet decides RH and has zero width as one-sided growth exponent.
## SimpleZeroPacketCriterion
- For universal U: W(U) = E(U) ⇔ all critical zeros simple. RH ∧ all zeros simple ⇔ P_U bounded above ∧ lim(1/L)∫P_U² = Weil functional of h_U = Ω(0)h(0) + LévyEnergy − 2⟨h,ν⟩. Both sides prime–polar data of ONE compact source (linear packet energy vs quadratic bi-scale energy).
## PacketSignGapLaw
- Window means of absolutely convergent a.p. series uniform in window position: |mean over [x,x+L]| ≤ Σ|a_i||χ_L(γ_i)| (→ 0, nonzero freqs), window mean square ≥ Σ|a_i|² − Σ_{i≠j}|a_i||a_j||χ_L(γ_i − γ_j)| (→ 0, distinct freqs). Window energy inequality from (q+M)(q−c) ≤ 0.
- SIGN GAP LAW: nonzero source with packet bounded above ⇒ c, ℓ > 0 with P_f > c and P_f < −c in EVERY window [x, x+ℓ] (c = E/(4(M+1))). Under RH for every nonzero compact source: smoothed prime–polar discrepancy changes sign in every multiplicative interval [X, e^ℓX].
## PacketBandLaw (start)
- ∫_T^LP_f² = O((1+L)e^{2σL}) ⇔ f blind to zeros of depth > σ. Universal U: RH ⇔ ∫_T^LP_U² = O(1+L) (slope E(U)); zero width = half the exponential band rate of P_U. Mechanism: smoothing zero series by bump k gives coefficients c_ρk̂(γ_ρ); 2|k||G| ≤ e^{στ}k² + e^{−στ}|G|² turns window energy into pointwise O((1+τ)e^{στ}); residue law.
- Stationary packet of compact continuous source is continuous (locally finite grid + bounded polar range). Smoothing zero series by bump k multiplies coefficients by k̂(γ_ρ). Band O((1+L)e^{2σL}) ⇒ smoothed zero series O(e^{σ'τ}) ⇒ coefficient kills. PACKET BAND LAW proved both directions. Universal U: RH ⇔ linear band of P_U; zero width = half band rate.
## PairingRecurrenceLaw
- Packet of H at shift τ = full prime–polar pairing of H(· − τ). Recurrence: absolutely convergent a.p. series returns within ε of value at 0 at arbitrarily large times (finite simultaneous Kronecker/Bohr recurrence on mass-carrying finite set). autocorr f = weilTest f f; ĥ_f(z) = f̂(z)·conj f̂(conj z).
- PAIRING RECURRENCE LAW: packet of f bounded above ⇒ limsup_{τ→∞} −⟨h_f(· − τ), ν⟩ = W(f) = Ω(0)h(0) + LévyEnergy − 2⟨h_f,ν⟩ (critical series of h_f has nonnegative coefficients m|f̂|², |Γ(τ)| ≤ Γ(0) = W). Lévy energy fixed by prime–polar pairings alone (origin pairing + recurrent max of translated pairings). Under RH for every source.
## CubicSplineUniversalProbe
- Real-rooted boost law: if φ̂ vanishes only on ℝ, every boost |t| ≥ ½ is universal (zeros have |Im γ_ρ| < ½). Box smoothing gains one derivative ((U_w⋆g) = difference of primitives), U_w^{⋆(k+2)} ∈ C^k. Cubic spline B = U_1^{⋆4} ∈ C², supp [−4,4], B̂ = (sin z/z)⁴ real-rooted.
- EXPLICIT universal probe U(u) = e^uB(u). RH ⇔ Σ_nΛ(n)√n·B(log n − τ) ≤ ∫_0^∞2cosh(x/2)e^xB(x − τ)dx + Ke^τ for large τ (one spline-weighted prime sum vs polar prediction); zero width β ⇔ same with Ke^{(1+β)τ}. Band and simple-zero criteria for P_U.
## MultiplicityCeilingLaw
- E(f) ≤ K·W(f) ∀ compact C² f ⇔ every critical multiplicity ≤ K (tuned cubic splines read each multiplicity). Bounded multiplicities ⇔ uniform E ≤ KW. Under RH: multiplicity ≤ K ⇔ lim(1/L)∫P_f² ≤ K·Weil(h_f) ∀f.
## PacketZeroAmplitudeLaw
- Bohr mean of a.p. series = sum of zero-frequency coefficients; character twist shifts frequencies; twisted packet mean of P_f e^{−iητ} = −coefficient at ordinate η.
- PER-ZERO AMPLITUDE LAW (unconditional): limsup P_f ≥ m_ρ|f̂(γ_ρ)|, liminf P_f ≤ −m_ρ|f̂(γ_ρ)| for every critical ρ (weight 1 + cos(γ₀τ + θ) ≥ 0, mean 1; choose θ = arg(∓c₀)).
- Tuned spline B(u/R)cos(γ_ρu): |f̂_R(γ_ρ)| ≥ 15R/32 once R|γ_ρ| ≥ 1 ⇒ packet oscillates beyond ±15m_ρR/32 — linear resonance in R vs √(t log(1/t)) for dilates. |B̂(x)| ≤ x^{−4}.
## TranslatedPairingEnvelopeLaw
- Blindness of ĥ_f right of line ⇒ blind left too (ĥ_f(γ_ρ) = f̂(γ_ρ)conj f̂(γ_{1−ρ̄})) ⇒ Weil functional of h_f = critical sum W(f).
- WEIL BOUND BY ONE PACKET (unconditional): W(h_f) ≤ limsup_{τ→∞} −⟨h_f(· − τ), ν⟩ (if pairings unbounded below on −side, trivial; else envelope law).
- ENVELOPE LAW: translated pairings of h_f bounded on one side ⇒ W(h_f) ≥ 0 (Weil positivity for f), |⟨h_f(· − τ),ν⟩| ≤ W + ε eventually, −⟨…⟩ ≥ W − ε infinitely often. One-sided bound on single packet of h_f gives Weil positivity for f.
## CramerLiminfLaw (start)
- Gauge bridge: beyond support, below cutoff, P_f(τ) = R_N(−τ) − D_N(−τ) (forward residual − Chebyshev gauge convolution). Windowed energy: ∫_w^LP_f² ≤ (1+η)‖f' − f/2‖₁²∫_0^{L+w+3}Ẽ² + (1+1/η)·10h(0). Under RH: (1/M)∫_0^MẼ² ≥ E(f)/‖g‖₁² − ε eventually for every probe.
- Gauge-delta probe f(u) = e^{u/2}∫_u^{u+T}k_r: gauge derivative e^{u/2}(k(u+T) − k(u)); ‖g‖₁ ≤ e^{r/2} + e^{(r−T)/2}; |ĝ(γ)| ≥ 1 − 2|ρ|r − e^{(r−T)/2}. Ratio E/‖g‖₁² → zero energy of S. CRAMÉR LIMINF LAW (under RH): (1/M)∫_0^MẼ² ≥ Σ_{ρ∈S}m²/|ρ|² − ε for all large M; liminf ≥ full zero energy.
- Under RH zero energy Σm²/|ρ|² converges (finite parts ≤ 2C + 1); liminf (1/M)∫_0^MẼ² ≥ full zero energy.
## DiscrepancyTransformLaw
- Stieltjes form of pairing for any C¹ f: pairing_N f = f(0) + Ẽ(L)f(L) − ∫_0^LẼ(f' − f/2) − ∫_0^Le^{−t/2}f. Gauge derivative of χ_ξ = −s(ξ)χ_ξ.
- ν̂_N(ξ) = s(ξ)∫_0^LẼχ_ξ + Ẽ(L)χ_ξ(L) + 1 − (1 − e^{−sL})/s. 𝓕R_N = 𝓕(Ẽ·1_{[0,L]}) + B_N with |B_N| ≤ (|Ẽ(L)| + 5)/|s|. Boundary = Fourier shadow of endpoint jump Ẽ(L); high-frequency energy ≍ Ẽ(L)²/ξ₀ ⇒ Laplace energy (causal continuation) is the band-limited object, not the windowed Chebyshev energy. |s(ξ)| ≥ ½.
## DyadicRenewalChain (start)
- Renewal (Markov) law: R_N(t) = e^{−(t−a)/2}R_N(a) + e^{−t/2}[(ψ(e^t) − ψ(e^a)) − (e^t − e^a) − (t − a)]. R_N(0) = 0. Chain x_{k+1} = qx_k + r_k, q = e^{−h/2}, x_k = Σ_{j<k}q^{k−1−j}r_j. Dyadic h = log 2: r_k = 2^{−(k+1)/2}(ψ(2^{k+1}) − ψ(2^k) − 2^k − log 2).
- (he^{−h}/2)Σx_k² − Σc_k ≤ ∫_0^{Kh}R_N² ≤ 2hΣx_k² + 2Σc_k; Σx_k² ≤ (1−q)^{−2}Σr_k² (Schur); Σr_k² ≤ 4Σx_k². Laplace energy ≍ squared block discrepancies + fine intra-block energies (coarse/fine separated).
- Converse block bound (he^{−h}/8)Σr_k² ≤ ∫_0^{(K+1)h}R_N² + Σc_k. Dyadic coarse-fine law ∫_0^{K log 2}R_N² ≤ 2log2(1 − 1/√2)^{−2}Σr_k² + 2Σc_k.
## PacketEnergyPlancherel
- ν̂_N(−ξ) = conj ν̂_N(ξ) (real measure); S_N even. 𝓕(signedSource f N)(ξ) = 𝓕f(ξ)·ν̂_N(−ξ). packetEnergy = ∫|𝓕f|²|ν̂_N|² = ∫|𝓕f|²(¼ + 4π²ξ²)S_N. Every compact Gram energy = spectral energy of ν_N through window |𝓕f|²; probing band |ξ| ≤ √x needs sources of width ≲ 1/√x (bi-scale uncertainty of probes).
## ExponentialRectangleAndDivisorAverageLaw
- Pairing linear (finset sum, difference). RECTANGLE LAW: pairing_N(e^{t/2}1_{[0,a]}) = (ψ(e^a) − e^a) + 1 − a for 0 ≤ a ≤ L. Rectangle difference = e^{b/2}·blockResponse(a,b); chain input r_k = normalized rectangle-difference reading.
- Factorial lift Σ_{j≤K}polarRectangle(log(K/j)) pairs to Σ_j(ψ(K/j) − K/j + 1 − log(K/j)). DIVISOR-AVERAGED CHEBYSHEV LAW: Σ_{j≤K}(ψ(K/j) − K/j) = log K! − K·H_K; ⇔ Σ√(K/j)Ẽ(log(K/j)) = log K! − KH_K. Closed form pairing = 2log K! − K log K − KH_K + K. Factorial producers = signed sums of rectangle readings; their O(log K/√K) cancellation = Λ∗1 = log.
## GaugeDualNormAndDivisorSampledResponse (start)
- pairing_N h = −∫R_N(h' − h/2) for compact C¹ h ⇒ (pairing h)² ≤ laplaceEnergy·‖h' − h/2‖₂² (Laplace energy dominates squared gauge-Sobolev dual norm of ν_N). Rectangle tests are point readings e^{a/2}R_N(a), NOT L²-controlled. Divisor-sampled: Σ_{j≤K}√(K/j)R_N(log(K/j)) = 2log K! − K log K − KH_K + K.
- Every smooth producer: pairing²/‖h' − h/2‖₂² ≤ laplaceEnergy. Rectangle reading = e^{a/2}R_N(a); chain input r_k = R_N((k+1)h) − qR_N(kh).
## DyadicBlockEnergyDiscreteDeviation
- blockResponse(a,t) = e^{−t/2}(logError t − logError a − (t−a)). On cell of n ∈ [X,2X): explicit in integer errors E(n) = ψ(n) − n. Cell law: (E(n) − E(X))²/(16X²) − 3/(2X²) ≤ ∫_cell blockResponse² ≤ 4(E(n) − E(X))²/X² + 10/X².
- Dyadic fine energy: D_X/(16X²) − 2 ≤ c_k ≤ 4D_X/X² + 10, D_X = Σ_{n∈[X,2X)}(E(n) − E(X))², X = 2^k. Chain input r_k = 2^{−(k+1)/2}(E(2^{k+1}) − E(2^k) − log 2). Window Laplace energy bounded by purely discrete dyadic statistics of E(n): coarse jumps + fine in-block deviations.
## FermiNymanBrickDictionary
- t = e^{−u}: L²((0,1],dt) = gauge space ∫‖e^{−u/2}F(e^{−u})‖²du. Fermi–Nyman generator φ_a(t) = {1/(at)} − 2{1/(2at)}: φ_a(e^{−u}) = −1_{[log a, log 2a)}(u) on bulk u < log 2a.
- Gauge-lifted brick pairing: pairing_N(e^{t/2}1_{(a,b]}) = logError b − logError a − (b − a); dyadic brick reads ψ(2a) − ψ(a) − a − log 2 = √(2X)·r_k. Nyman–Beurling approximation = approximation of gauge brick by dyadic bricks + origin tails; generators pair to coarse dyadic block discrepancies.
## IntegerBlockVarianceBridge
- u_j = E(X+j): X·D_X = finiteBlockVariance X u + (Σu_j − Xu_0)² (Σ_{r<s}(u_r − u_s)² = XΣu² − (Σu)²). c_k ≍ Var_X(E)/X³ + (Ē_X − E(X))²/X. Var/(16X³) − 2 ≤ c_k.
- c_k ≤ 4Var/X³ + 4(Σu_j − Xu_0)²/X³ + 10.
## WindowEnergyArithmeticQuadrature
- On cell: R_N(t) = e^{−t/2}(ψ(n) + 1 − t − e^t). Closed cell energy ∫_cell e^{−t}(c+1−t−e^t)² = F_c(log(n+1)) − F_c(log n), F_c(t) = −e^{−t}((c+1−t)² − 2(c+1−t) + 2) − 2(c+1)t + t² + e^t. Window Laplace energy = finite explicit quadratic form in ψ(n) (coefficient 1/(n(n+1)) on ψ(n)²); laplaceEnergy = sum + R_N(L)².
## PoleRegionNetSignedMass
- ν̂_N(0) = pairing_N 1 = ΣΛ(n)/√n − 4sinh(L/2) = ½∫_0^LẼ + Ẽ(L) − 1 + 2e^{−L/2} (classical Σ_{n≤x}Λ(n)/√n = √x + ψ(x)/√x − 1 + ½∫(ψ−u)u^{−3/2}). S_N(0) = 4(pairing 1)². ∫_0^L2cosh(t/2) = 4sinh(L/2).
## OddSectorAndPrimitiveHyperplaneBiScaleSynthesis (Pillar XXV)
- For EVERY real f ∈ C²_c: Re pole term = 2((∫f cosh(u/2))² − (∫f sinh(u/2))²); weilArchRe = pole + Ω(0)h(0) + LévyEnergy. poleWeightArchRe(β) = Ω(0)h(0) + LévyEnergy + 2β((∫f cosh)² − (∫f sinh)²); β = 0 ⇒ pole cancels on all real tests.
- RealWeilTestFn (real, no parity), RealOddTestFn: odd ⇒ ∫f cosh(u/2) = 0 ⇒ pole re = −2(∫f sinh)² ≤ 0. SINH-CAPACITY WEIL IDENTITY (odd): weilArchRe + 2(∫f sinh(u/2))² = Ω(0)h(0) + LévyEnergy. All Layer-V coercivity bounds lift to odd and full real sectors at β = 0 (and β = 1 with sinh capacity).
- RealHyperplaneGenerator = RealOddTestFn ⊕ RealEvenPolarTestFn ↔ EvenSector.hyperplaneTest; poleWeightArchRe(0) = Ω(0)h(0) + LévyEnergy on all generators; all-scale Λ lower bound there.
## IntegratedMultiNodeDyadicCosetWeilCoercivity (Pillar XXVI)
- Integrating the multi-node collar over y ∈ [0, δ]: all K nodes SHARE one origin collar W₀∫_0^δ(h(0) − h(y)) (no division by K); price = off-diagonal Gram δ/(2W₀)ΣΣw_iw_jh(t_i − t_j) (prime-2-power correlations for dyadic cosets). Origin collar ×archLevySinhWeight(e^d) ≤ LévyEnergy; shifted collar ×archLevySinhWeight(t + e^d) ≤ LévyEnergy. Lifted to all sectors.
## AllParityWeilPoleWeightFunctionalAndChebyshevSynthesis (Pillar XXVII, start)
- For every real C²_c f: 4∫_{x>0}h_f(x)cosh(x/2) = Re weilPoleTerm = 2∫_{x>0}polarDensity·h_f. Support scale on RealWeilTestFn; polar tail vanishes beyond.
- UNIVERSAL POLE ABSORPTION (β = 1, any parity): 2(prime sum + polar tail) = 2pairing_N + Re pole; Λ-linear combination of logVector = 2pairing_N + Re pole. ⇒ Re W_Λ(f) = Ω(0)h(0) + LévyEnergy − 2pairing_{supportScale}(h_f) = poleWeightArchRe(0) − 2pairing for EVERY real test (pole term of ζ is exactly the continuum polar part of ν).
- Full Weil identity on every RealWeilTestFn and RealOddTestFn; |Re W_Λ − (poleWeightArchRe(0) − 2chebyshevWork)| ≤ 2e^cLévyEnergy + packetEnergy/(e^ce^{2b})∫e^{−y/2}sinh y; lower bound (1 − 2e^c)LévyEnergy + Ω(0)h(0) − 2chebyshevWork − packet term ≤ Re W_Λ.
## HyperbolicGaugeMeanSquareChebyshevWeilSynthesis (Pillar XXVIII)
- Cutoff-level dictionary ∫_0^LẼ² = ∫_1^{N+2}(ψ − x)²/x²; = discreteChebyshevCellSum + Σc_n; two-sided cell bound. smoothGaugeBound = 3(10 + Ẽ(L)²)h(0) + 3‖g‖₁²∫Ẽ² ≤ discreteCellGaugeBound. packetEnergy ≤ each.
- Chain of unconditional lower bounds for Re W_Λ(f) on all real sectors: (1 − 2e^c)LévyEnergy + Ω(0)h(0) − 2chebyshevWork − [packetEnergy | smoothGauge | discreteCell | roughGauge | correlationGauge]/(e^ce^{2b})·∫e^{−y/2}sinh y. All circular w.r.t. RH: the mean-square Chebyshev term is the RH-equivalent quantity.
- ∫f'f = 0 for compact C¹ ⇒ ∫(f' − f/2)² = ∫f'² + h(0)/4 (gauge L² energy identity).
## ExplicitNyquistPolarAndChebyshevFactorialProducer (Pillar XXIX)
- nyquistPolarConstant(n) = cosh(log n/2) = (√n + 1/√n)/2; √(n+1) − √n ≤ 1/(2√n); on cell 0 ≤ cosh(x/2) − const ≤ 1/(4√n); cell L² error ≤ 1/(16n²); dyadic window total ≤ 1/(16N). Instantiates Pillar XII producer W explicitly.
- Stirling residual T(k) − (k log k − k) ∈ [1, log(k+1) + 1], T(k) = Σ_{d≤k}ψ(⌊k/d⌋) = log k!.
- Alternating producer T(2N) − 2T(N): |· − (2log 2)N| ≤ 2log(2N+1) + 1 (no O(√N) divisor noise — avoids subtracting j before floor-summing). T(K) = Σ_dΛ(d)⌊K/d⌋. 0 ≤ ⌊2N/d⌋ − 2⌊N/d⌋ ≤ 1 ⇒ ψ(2N) − ψ(N) ≤ T(2N) − 2T(N) ≤ ψ(2N) ⇒ Chebyshev bounds: ψ(2N) − ψ(N) ≤ (2log2)N + O(log N), ψ(2N) ≥ (2log2)N − O(log N).
- Bi-null producer T(4N) − 4T(2N) + 4T(N) = alt(2N) − 2alt(N) ((1 − 2·2^{−s})² kills double and simple pole).
- Bi-null = second dyadic difference of Stirling residual; |T(4N) − 4T(2N) + 4T(N)| ≤ 5log(4N+1) + 1 (vs 24√N for floorSummatory psiDefect with divisor contamination).
## NyquistResidualMass / NyquistResidualPartition / NyquistResidualKernel / NyquistResidualOperator
- Residual density cosh(x/2) − cosh(log(k+1)/2) on cell k ∈ [0, 1/(4√(k+1))]; cell mass ≤ 1/(4(k+1)√(k+1)) ≤ 1/√(k+1) − 1/√(k+2) (telescoping); tail mass from N ≤ 1/√(N+1) → 0.
- Half-open cells partition (log(N+1), ∞); residual kernel K_N ≥ 0, integrable, ∫K_N = tail mass. Positive operator H ↦ ∫H·K_N on bounded continuous functions; EXACT operator norm = tail mass ≤ 1/√(N+1) (attained at H = 1); continuous under uniform convergence; = Σ cell residuals.
## NyquistPolarDecomposition
- ∫_cell H cosh(x/2) = cosh(log(k+1)/2)∫_cell H + cell residual. For compact H: polar tail ∫_{>log(N+1)}H cosh(x/2) = cell-average producer + residual operator; |tail − producer| ≤ ‖H‖/√(N+1). Under uniform convergence: tail convergence ⇔ producer convergence (residual always stable).
## NyquistPolarSourceEscape (start)
- LevyEnergySource correlation as bounded continuous ‖·‖ ≤ 1, compact support. Normalized polar moment = producer(0) + residual, |polar − producer| ≤ 1. Smooth diffuse train g_n → f (uniform correlation convergence, arch energy converges, compact closure, uniform signed grid tail) with producer(g_n) ≥ ((n+2)/4)·polar(f) − 1 → ∞ while residual converges: polar escape lives entirely in the cell-average producer.
## NyquistWeightJets / NyquistWeightTaylorRemainder / NyquistWeightCells / NyquistWeightCellAsymptotic
- Weight cosh(βx); j-th derivative (β^j/2)(e^{βx} + (−1)^je^{−βx}) ≥ 0 on x ≥ 0, ≤ β^je^{βx}, monotone. Taylor residual of order m at left endpoint a ≥ 0: jet_{m+1}(a)(x−a)^{m+1}/(m+1)! ≤ residual ≤ jet_{m+1}(b)(x−a)^{m+1}/(m+1)!; mass bounds with (b−a)^{m+2}/(m+2)!.
- Log cell widths 1/(k+2) ≤ w_k ≤ 1/(k+1), (k+1)w_k → 1. Cell mass ≤ 2^ββ^{m+1}/(m+2)!·(k+1)^{β−m−2}. β = 0 ⇒ residual ≡ 0.
- ASYMPTOTIC: cell mass ~ β^{m+1}/(2(m+2)!)·(k+1)^{β−m−2}. SHARP SUMMABILITY THRESHOLD: Σ_k cellMass(β, m, k) < ∞ ⇔ β < m + 1. (For polar β = ½, order-0 Taylor producer already summable; residual tail.)
## NyquistPowerTails / NyquistPositiveTailComparison / NyquistPositivePrefixComparison
- Σ_{k≥0}(N+k+1)^p for p < −1 between (N+1)^{p+1}/(−p−1) and (N+1)^p + (N+1)^{p+1}/(−p−1); normalized → 1/(−p−1). Pointwise ratio a_n/b_n → c (b > 0) transfers to tails (summable) and to divergent prefixes (Stolz–Cesàro type).
## NyquistPrefixScales / NyquistWeightPrefixMass
- Power increments (k+2)^r − (k+1)^r ~ r(k+1)^{r−1}; cell widths sum to log ratio, normalized → 1. CRITICAL β = m+1: prefix residual mass ~ C·log M (C = β^{m+1}/(2(m+2)!)); SUPERCRITICAL β > m+1: prefix mass ~ C/(β−m−1)·M^{β−m−1}.
## NyquistWeightKernel / NyquistWeightTailMass / NyquistWeightOperator
- Weight-β order-m Taylor residual kernel ≥ 0, ≤ cosh(βx), locally integrable; compact inputs always integrable against it. Kernel integrable ⇔ β < m+1 (sharp); at/above threshold lintegral = ∞.
- Subcritical tail mass ≤ 2^ββ^{m+1}/(m+2)!·(1 + 1/(m+1−β))(N+1)^{β−m−1} → 0; normalized tail → C/(m+1−β). Bounded positive operator with exact norm = tail mass.
## NyquistWeightProducer (start)
- Cell moments ∫_cell H(x)(x − node)^j; produced cell = Σ_{j≤m}jet_j(node)/j!·moment_j; exact: ∫_cell H·Taylor = produced cell; polar tail = producer + residual operator.
- Weighted polar tail = Taylor producer + residual (for compact H always, operator if β < m+1); |tail − producer| ≤ tailBound·‖H‖; convergence equivalence.
## NyquistWeightCalibrations
- Kernel integrable ⇔ ⌊β⌋ ≤ m: minimum producer order = ⌊β⌋. Polar β = ½, m = 0 recovers cell-average producer. SHARP: residual tail mass / (1/√(N+1)) → 1/4. Critical β = 1, m = 0: prefix mass/log M → ¼; β = 1, m = 1: tail·(N+1) → 1/12.
## NyquistWideSourceEnergy / NyquistWideResidualLimit / NyquistWideResidualEscape
- Stretched sources f(δx): normalized arch energy ≤ δK (linear). Fixed wide bump family f_j = bump rescaled by 1/(j+1): energy ≤ K/(j+1) → 0, correlation → 1 pointwise, plateau ≥ ½ on [0, r(j+1)].
- Subcritical: wide residual → tail mass ⇒ best constant under ANY energy ceiling = tail mass (attained). Supercritical (β ≥ m+1): wide residual → ∞ under arbitrarily small energy ⇒ no bound under energy ceiling. Low archimedean energy cannot control the order-m residual at/above threshold.
## ChebyshevCellAndArchimedeanWeilProducer (Pillar XXX, start)
- General dilation stencil Σc_aT(aN) = (Σc_aa)(N log N − N) + (Σc_a a log a)N + Σc_a·Stirling(aN); bi-null stencils O(log N). Coprime (2,3) producer T(6N) − 2T(3N) − 3T(2N) + 6T(N) (= (1 − 2·2^{−s})(1 − 3·3^{−s})): |·| ≤ 12log(6N+1) + 2.
- Slope ψ(x) ≤ (log 4 + 3)x ⇒ |Ẽ(t)| ≤ (log 4+3)e^{t/2}, Ẽ(L)² ≤ (log4+3)²(N+2); cell sum ≤ (log4+3)²(N+1); ∫_0^LẼ² ≤ (log4+3)²(N+1) + 2 (trivial exponential-size bound). Prime-free archimedean packet producer bound eliminates ψ via pairing² ≤ h(0)·packetEnergy.
- archimedeanPacketProducerBound(f,N) = 3(10 + slope²(N+2))h(0) + 3‖g‖₁²(slope²(N+1) + 2) ≥ packetEnergy (prime-free but O(N) — trivial Chebyshev). Young: 2|pairing| ≤ e^ch(0) + e^{−c}packetEnergy. ⇒ |Re W_Λ − poleWeightArchRe(0)| ≤ e^ch(0) + e^{−c}·archProducerBound(f, supportScale) for all real sectors. NOTE: grows like N ~ e^{supportRadius}: not a positivity proof; it is the trivial bound.
## LaplaceEnergyAndRoughCollarWeilProducer (Pillar XXXI, start)
- Dyadic telescoping ψ(2^K) = Σ_k(ψ(2^{k+1}) − ψ(2^k)) ≤ Σ alternating producers ≤ (2log2)(2^K − 1) + K(2log(2^K+1) + 1) — elementary Chebyshev upper bound ψ(x) ≤ (2 log 2)x + O(log²x) at x = 2^K.
- laplaceEnergy ≤ producer bound 2slope²(2N+3) + 6 + 2(transient)² (O(N), trivial). Ẽ(L)² ≤ 2laplaceEnergy + 2T²; packetEnergy ≤ 3(10 + 2laplaceEnergy + 2T²)h(0) + 3‖g‖₁²(2laplaceEnergy + 2) (all packets controlled by the single scalar laplaceEnergy).
- mass(N) ≤ (log4+4)(N+2) + 4sinh(L/2); derivative-free correlation-only collar producers.
- Atomic mass ≤ ψ(N+2) (Λ/√n ≤ Λ). Collar/correlation/trial producer bounds with slope and mass producer: all derivative-free, prime-free, but O(N) — trivial Chebyshev size.
## CoprimeFactorialLiftAndSpectralLaplaceProducer (Pillar XXXII, start)
- H_{2n} − H_n = Σ_{k<n}(1/(2k+1) − 1/(2k+2)); coprime harmonic correction 6N(H_{6N} − H_{3N} − H_{2N} + H_N) ∈ [0, 3].
- Coprime factorial lift [FL(6N) − 2FL(3N) − 3FL(2N) + 6FL(N)]/√N: vanishes at 0, equals √6 at log(6N) (so NOT an autocorrelation: autocorr with h(0) = 0 vanishes identically), admissible; fullPairing = (2·coprimeProducer − harmonicCorrection)/√N; |·| ≤ (24log(6N+1) + 7)/√N.
- Boundary-free: spectral critical-line mean square ≤ laplaceProducerBound; packetEnergy ≤ ‖g‖₁²·laplaceProducerBound; collar packet ≤ gaugeBudget·laplaceProducerBound.
- |ν̂_N(ξ)| ≤ massProducer. Boundary-free full Weil bound: |Re W_Λ − poleWeightArchRe(0)| ≤ e^ch(0) + e^{−c}‖g‖₁²·laplaceProducerBound(supportScale).
## ChebyshevHeadAndShearCellProducer (Pillar XXXIII, start)
- Chebyshev.psi(m) = RHTower.chebyshevPsi(m) for m ∈ ℕ. dyadicDiff(2m) = 2ψ(m) − ψ(2m) ∈ [ψ(m) − (2log2)m − O(log m), 2ψ(m) − (2log2)m + O(log m)]; at 2·2^K bounded by pure Stirling producers.
- Integer-centered cell sum Σ(ψ(n) − n)²/(n(n+1)) ≤ slope²(N+1) (trivial); harmonic bilinear von Mangoldt shear sum Σ(Λ(k+2)−1)(2E(k+1) + Λ(k+2) − 1)/(k+2) ≤ 2slope²(N+1) − 1 (Abel identity from companion module).
- Wall-1 Chebyshev head ∫_{1/(N+1)}^1(2ψ(1/(2t)) − ψ(1/t))² ≤ (log4+4)²N (|2ψ(x/2) − ψ(x)| ≤ (log4+4)x; ∫(1/t)² = 1/a − 1); log-Möbius Fermi error energy ≤ tail + (log4+4)²N/(log N)² — trivial size, not Nyman–Beurling convergence.
- Continuous coprime (2,3) factorial producer with collar 1/(6N): continuous, agrees with step producer at log n, vanishes for x ≤ 0 (stencil sum 6N − 6N − 6N + 6N = 0).
- Continuous coprime producer supported in [0, log(6N+1)] (C_c); linear collar log correction cancels (stencil Σc_aa = 0); fullPairing = (2·coprimeProducer − (1 + 1/(12N))harmonicCorr)/√N, |·| ≤ (24log(6N+1) + 7 + 1/(4N))/√N; never an autocorrelation (0 at 0, √6 at log 6N).
## FoldFreeKernelGramAndFranelGcdCancellation (second "Pillar XXIX")
- Canonical self-similar profile s₀ = selfSimilarExtension(1/u): ‖s₀‖² = 2 on (0,1], dyadic fold Ps₀ = 2/u, log-mean 1; Haar target ⊥ s₀. ⟨φ_{a+1}, s₀⟩ = −1/(a+1). Fold-free generator φ̃_{a+1} = φ_{a+1} + s₀/(2(a+1)) ∈ ker P (top-octave dyadic fold vanishes a.e.), ⊥ s₀.
- EXACT PYTHAGORAS on L²(0,1] = ker P ⊕ ℂs₀: ‖Haar − Σc_jφ_{a_j+1}‖² = ‖Haar − Σc_jφ̃_{a_j+1}‖² + |Σc_j/(a_j+1)|²/2; same for generator energy; ⟨φ̃_a, φ̃_b⟩ = ⟨φ_a, φ_b⟩ − 1/(2(a+1)(b+1)). Nyman–Beurling approximation splits into fold-free residual + harmonic shadow.
- Franel: ∫_0^1ψ((a+1)x)ψ((b+1)x) = gcd(a+1,b+1)²/(12(a+1)(b+1)).
- Franel diagonal 1/12; consecutive scales 1/(12(m+1)(m+2)); exact GCD quadratic form for sawtooth combinations. Alternating sawtooth ψ(mx) − 2ψ(2mx): Gram = (5gcd(m,m')² − gcd(m,2m')² − gcd(2m,m')²)/(12mm'), diagonal ¼, EXACT orthogonality to its dyadic double (scale 2m), odd–odd gcd²/(4(2k+1)(2l+1)).
## CoprimeShearArithmeticWeightsAndChebyshevCellIncrement (second "Pillar XXX")
- ⌊(n+1)/d⌋ − ⌊n/d⌋ = 1_{d|n+1} (idempotent); coprime neighbors ⇒ consecutive jumps of ⌊·/(d+2)⌋ have disjoint support. Weighted floor sum step = Σ_{d≤N, d|n+1}c(d); Möbius floor sum step = truncated Möbius divisor sum (vanishes below cutoff).
- ψ step = Λ(n+1); E(n) = ψ(n) − n step = Λ(n+1) − 1; log-Möbius floor sum = ψ below cutoff. Dyadic difference D(n) = 2ψ(n/2) − ψ(n): odd step −Λ(2m+1), even step 2Λ(m+1) − Λ(2m+2), two-step 2Λ(m+1) − Λ(2m+1) − Λ(2m+2).
- (E²) step = (Λ−1)(2E + Λ − 1). Abel on Nyquist weights 1/((k+1)(k+2)): Σ_{k≤N}A(k)/((k+1)(k+2)) = A(0) − A(N)/(N+2) + Σ_{k<N}ΔA(k)/(k+2). ⇒ Σ_{k≤N}E(k+1)²/((k+1)(k+2)) = 1 − E(N+1)²/(N+2) + Σ_{k<N}(Λ(k+2)−1)(2E(k+1) + Λ(k+2) − 1)/(k+2). discreteCellSum ≤ 2·integerCenteredSum + 2.
- Full Weil lower bound with integer-centered gauge (cell sum expanded into von Mangoldt shear increments) — same rearrangement shape; remainder = Chebyshev mean square.
## WitnessGermOriginMassAndJointTailHeadSynthesis (second "Pillar XXXI")
- L2FermiWitness bundle (w ⊥ every φ_{a+1}; zero witness inhabits). ⟨φ̃_{a+1}, w⟩ = ⟨s₀, w⟩/(2(a+1)): witnesses see fold-free kernel only through s₀. Scale-balanced difference Δ_{a,b} = (a+1)φ_{a+1} − (b+1)φ_{b+1} ∈ ker P ∩ s₀^⊥ ∩ W^⊥ (fold shadow −1/u is scale-normalized away).
- witnessMass(w,1) = witnessMass(w,2^{−K}) + Σ_{j<K} shell energies (rescaled top-octave form 2^{−j}∫_{1/2}^1|w(2^{−j}u)|²).
- |⟨Haar, w⟩|² ≤ 2·witnessMass(w,1/(N+1))·tailEnergy + 2·headMass·headEnergy for any generator combination Φ (Haar pairing invariant under Φ-subtraction; Cauchy–Schwarz per piece).
- logMobiusFermiErrorEnergy(N+2) = tail(0,1/(N+3)] + (log(N+2))^{−2}∫_{1/(N+3)}^1(2ψ(1/2t) − ψ(1/t))²; 2ψ(x/2) − ψ(x) = 2(ψ(x/2) − x/2) − (ψ(x) − x) (linear PNT drift cancels); head² ≤ 8E(x/2)² + 2E(x)². Wall 1 head = centered Chebyshev mean square (RH-equivalent size question).
## SelbergSieveTailQuadraticFormAndTruncatedDivisorGram (second "Pillar XXXII")
- General finite Nyman error 1_{(0,1]} + Σ_{d≤N}c_d{1/(dt)} = 1_{(0,1]} + H_c(N)/t − Φ_c(N,1/t), H_c = Σc_d/d, Φ_c(N,x) = Σc_d⌊x/d⌋.
- Φ_c(N,m+1) − Φ_c(N,m) = sieved divisor sum s_{N,c}(m+1) = Σ_{d|m+1, d≤N}c_d; equals full divisor sum on head k ≤ N; Φ_c(N,N+K) = head (full divisor sums) + tail (sieved sums, k ∈ (N, N+K]). Origin tail t < 1/(N+1) ⇔ m = ⌊1/t⌋ > N ⇔ Selberg Λ²-sieve regime.
- Σ_{k≤N+K}s_{N,c}(k)² = Σ_{d₁,d₂≤N}c_{d₁}c_{d₂}⌊(N+K)/lcm⌋. Smooth part: Σc_{d₁}c_{d₂}/lcm(d₁,d₂) = Σ_{e≤N}φ(e)(Σ_{d≤N, e|d}c_d/d)² ≥ 0 (Selberg totient diagonalization). Mean square ≤ (N+K)·diag + (Σ|c_d|)²; tail mean square ≤ that − head energy.
## CoprimeResidueAntiCorrelationAndSawtoothPhase (second "Pillar XXXIII")
- Δ{n/(d+1)} = 1/(d+1) − 1_{(d+1)|n+1}. At predecessor n = q(d+1)+d of a multiple: {n/(d+1)} = 1 − 1/(d+1), centered sawtooth ½ − 1/(d+1). Identity: 1_{d|n+1}·{n/d} = 1_{d|n+1}(1 − 1/d) ("coprime residue anti-correlation" — deterministic phase on jumps).
- Weighted floor sum = n·Σw(d)/d − Σw(d){n/d}. With w_Λ = −μ log: Σ_{d≤n+1}w_Λ(d)Δfloor(n){n/d} = Λ(n+1) − Σ_{d|n+1}w_Λ(d)/d; ψ(n) − n = n(Σ_{d≤n}w_Λ(d)/d − 1) − Σ_{d≤n}w_Λ(d){n/d}. Cross-term (Λ(n+1)−1)(ψ(n)−n) = harmonic drift part − sawtooth phase correlation. (Σ_{d≤n}−μ(d)log d/d → 1 is PNT-equivalent; drift term is where all info sits.)
## LocalToGlobalTailStabilityAndWitnessIndicatorPairing (second "Pillar XXXIV")
- φ_{a+1} = 2⌊1/(2(a+1)t)⌋ − ⌊1/((a+1)t)⌋ is a pure step function; = 0 for t > 1/(a+1), = −1 on (1/(2(a+1)), 1/(a+1)]; on (1/(2(a+1)), ∞) equals −1 of that brick. |φ| ≤ 3 ⇒ |Φ_{c,a}| ≤ 3Σ|c_j|.
- Tail energies: ∫_0^{1/(N+1)}|Φ|² ≤ 9(Σ|c|)²/(N+1); Haar tail ≤ 2(1 + 9(Σ|c|)²)/(N+1); |⟨Haar,w⟩|² ≤ 4·witnessMass(w,1/(N+1))(1 + 9(Σ|c|)²)/(N+1) + 2·headMass·headError. ℓ¹ coefficient growth vs origin mass is the trade-off.
## SawtoothPhaseCancellationAndBandSpectralProducer (second "Pillar XXXIV")
- H_{μlog}(N) = Σ_{d≤N}−μ(d)log d/d. Common cutoff N ≥ n: ψ(n) = n·H(N) − Φ_fract(N,n), Φ_fract(N,n) = Σ_{d≤N}(−μ log)(d){n/d}. Λ(n+1) = H(N) − ΔΦ_fract(N)(n). Dyadic: 2ψ(m) − ψ(2m) = Φ_fract(N,2m) − 2Φ_fract(N,m) for N ≥ 2m (drift cancels EXACTLY).
- |Φ_fract(N,n)| ≤ log N! ≤ N log N − N + log(N+1) + 1; dyadic phase difference ≤ (log4+4)2m (log factor cancels) + Stirling sandwich; Σ_{n≤N}Φ_fract(N,n) = (Σn)H(N) − Σψ(n); Σ_nΦ_fract(N,⌊N/n⌋) = (Σ⌊N/n⌋)H(N) − log N!.
- bandRemainderProducer(N) = 52(log4+4)cutoff(N)/π³ + (32 + 8(log4+4))/π² + 4/(3π⁴) = O(log N). Band integral ∫_{|ξ|≤ξ₀}S_N ≤ laplaceEnergyProducer. packetEnergy ≤ ‖g‖₁²(band integral at √(N+2) + bandRemainder); collar version derivative-free. Full Weil |Re W_Λ − poleWeightArchRe(0)| ≤ e^c h(0) + e^{−c}‖g‖₁²(band + remainder), across even-polar, odd, hyperplane-generator test spaces. Weil positivity reduces to critical-line band integral of S_N being small relative to arch energy.
## DyadicRenewalStirlingAndLogMobiusTotalEnergyProducer (second "Pillar XXXV")
- log-smoothed Möbius coefficients |μ(d)log(N/d)/log N| ≤ 1 ⇒ |logMobiusFermiApprox(N,t)| ≤ 3N; tail ∫_0^{1/(N+1)} ≤ (1+3N)²/(N+1); TOTAL logMobiusFermiErrorEnergy(N) ≤ (1+3N)²/(N+1) + (log4+4)²N/(log N)² — grows linearly in N (trivial; no Nyman–Beurling convergence). Witnesses ⊥ logMobiusFermiApprox.
- |⟨Haar,w⟩|² ≤ witnessMass(w,1)·logMobiusFermiErrorEnergy(N) ≤ witnessMass·logMobiusTotalEnergyProducer(N+2) (linear growth — no witness exclusion).
- Dyadic renewal at h = log 2: 0 ≤ ψ(2^{k+1}) − ψ(2^k) ≤ chebyshevAlternatingProducer(2^k) ≤ (2log2)2^k + 2log(2^{k+1}+1) + 1; chainInput sandwich (√2)^{−(k+1)}·[−(2^k + log2), altProducer − 2^k − log2]; prime-free envelope ~ (√2)^{k}(2log2 − 1) (grows!); Schur bounds Σ chainState² ≤ (1 − 1/√2)^{−2}Σ envelope²; causal response energy ≤ 2log2·that + 2Σ blockEnergy. boundaryTransform ≤ ((log4+3)e^{L/2} + 5)/|s(ξ)|.
- Selberg sieve tail specializations: μ weights ℓ¹ ≤ N; −μlog weights ℓ¹ ≤ log N!; Σ_{d|k}(−μ log)(d) = Λ(k), so head energy = Σ_{k≤N}Λ(k)².
## FoldFreeLogMobiusAndPlancherelCausalProducer (second "Pillar XXXVI")
- logMobiusHarmonicShadow(N) = Σμ(d)log(N/d)/(d log N) = Σ_{d≤N}μ(d)/d + H_{μlog}(N)/log N = ⟨logMobiusApprox, s₀⟩. Fold-free approximant (subtract shadow/2·s₀) ⊥ s₀; logMobiusErrorEnergy = foldFreeError + shadow²/2; shadow² ≤ 2·totalProducer.
- Tent-convolved causal factorial producer sourceFactorialCausal(N) (C_c, agrees with factorialBiNull at log n): polar integral = (coef·harmonicCorr − chebyshevBiNullProducer)/√N; fullPairing = (2·chebyshevBiNullProducer − coef·harmonicCorr)/√N, |·| ≤ (10log(4N+1) + 3 + 1/(4N))/√N.
- Plancherel: packetEnergy = ∫|f̂(ξ)|²(¼ + 4π²ξ²)S_N(ξ)dξ ≤ prime-free Laplace producer combination. Franel entry = gcd/(12 lcm) ≥ 1/(12 lcm) (Selberg smooth kernel), equality iff coprime.
## DivisorAverageChebyshevAndDyadicBlockVarianceProducer (second "Pillar XXXVII")
- log(K+1) ≤ H_K ≤ 1 + log K. Σ_{j≤K}(ψ(K/j) − K/j) = log K! − KH_K ∈ [−2K, −K + log(K+1) + 1] (K log K cancels; divisor-averaged Chebyshev error is NEGATIVE linear, i.e. −(γ+…)K: Euler constant channel). pairing_N(factorialLift K) = 2log K! − K log K − KH_K + K ∈ [−2K, −K + 2log(K+1) + 2] (needs log K ≤ cutoff N).
- Quantitative Gram coefficient on factorial source pair: allocation error ≤ 46√(m+1)(r₀+1)/(n+1); limiting error adds 92√(m+1)·collarTailMass(n). Package: mass ≤ massProducer, collar packet ≤ archimedean collar producer.
- Haar block variance m=2: Σ(w(2j+1) − w(2j))² + ‖blockSum₂ w‖² = 2‖w‖²; equality iff pairwise constant.
- Critical β=½ Nyquist cell masses: m=0 ≤ √2/4·(k+1)^{−3/2}; m=1 ≤ √2/24·(k+1)^{−5/2} ≤ √2/(24(k+1)²); cumulative ≤ √2/24·Σ1/(k+1)².
## FactorialSourceWeilContrastAndDivisorResponseProducer (second "Pillar XXXVIII")
- divisorSampledCausalResponse(N,K) = Σ_{j≤K}√(K/j)R_N(log(K/j)) = 2log K! − K log K − KH_K + K for 1 ≤ K ≤ N+2 — cutoff-independent, = pairing(factorialLift K) = fullPairing; in linear channel [−2K, −K + 2log(K+1) + 2]. Bi-null (1,−4,4) stencil over (K,2K,4K): = 2·chebyshevBiNullProducer(K) − harmonicCorr(K), |·| ≤ 10log(4K+1) + 3 (linear drift and γ cancel).
- (1,−4,4)/√K stencil of divisor-sampled response = fullPairing(factorialBiNull K). pairing_N(f)² ≤ laplaceEnergyProducer(N)·∫(gauge f)² (prime-free Sobolev dual norm; producer O(N)-size).
- Cutoff-free half-line Weil identity for every RealWeilTestFn: Re W_Λ(f*f̃) = Ω(0)h(0) + LévyEnergy − 2·fullPairing(autocorr f). Equal-origin contrast (same h(0)): Ω(0)h(0) cancels; W(f₊) − W(f₋) = ΔLévy − 2ΔfullPairing.
- Factorial source pair: (fullPairing(autocorr f₊) − fullPairing(autocorr f₋))/2 = fullPairing(factorialSourceProducer n); normalized contrast |·|/h(0) ≤ (10log(4(n+1)+1) + 3 + ...)/(6(n+1)) — prime–polar contrast decays relative to origin mass (only contrast, not the absolute pairing).
## OddProfileCollarDominanceAndUnimodalPrimeWindowProducer (second "Pillar XXXIX") — CHMD support
- CHMD Chebyshev discrepancy Δ(s) = chebyshevStep(s) − 2e^{s/2} ∈ [−2e^{s/2}, (2log4+14)e^{s/2}] on s ≥ 0 (trivial Chebyshev size); kernelDeriv·Δ integrable on (0,∞); window+tail split.
- Odd-profile test f = m_a w (w even): primeCrossing(oddPolarWeight a w, d) ≥ 0 and m_a-Doob collar difference ≥ 0, each ≤ the ground-state collar mixed integral (their sum equals it). Shift jump + collar mixed = 2·half-line shift jump + primeCrossing ≥ 0 (positive completion).
- Unimodal one-signed odd v ∈ C²_c with Doob profile Θ|v| antitone on [c, L/2]: weilLevyForm + 4crossSignBonus − Σ_{n<N}sameSideCross ≤ sourceEnergy (drops opposite-side bonuses ≥ 0).
## NodalLobeEnergyAndDyadicDilationDefectProducer (second "Pillar XL") — CHMD
- For resolvent eigenvector resolvent w = μw (μ ≠ 0), q = rieszLift w, lobes u± = pos/neg graph parts: five-term lobe jump (stationaryEnergy(Θu₊) − ⟨E(q₊),E(q₋)⟩ + ⟨L_prime u₊,u₊⟩ + ⟨T_prime u₊,u₋⟩ + (2μ−1)/μ‖u₊‖²) ≤ (1 + thetaGroundPotentialBound)‖u₊‖²; sum over lobes ≤ (1+bound)‖q‖².
- 2⟨T_prime u₊,u₋⟩ ∈ [0, ⟨L_prime u₊,u₊⟩ + ⟨L_prime u₋,u₋⟩]; for p ≠ 0, −2⟨E(p₊),E(p₋)⟩ < stationaryEnergy(Θu₊) + stationaryEnergy(Θu₋) (no zero mode); hence −2·sourcePair(pos,neg) < sum of lobe stationary + prime Dirichlet energies (strict nodal-lobe cross dominance).
- Dyadic dilation trace defect on Velocity: 2‖q‖² − ‖cellAnalysis(dilation₂ q)‖² = 2‖q − cellProj q‖² + Σ blockVariance₂; equality iff cellular and pairwise constant. Right-node collar partition: coefficient = Lévy mass on (r₀, endpoint) − radial penalty; active fibres above log 4 are left-sided with (k+1)y ≤ 1.
## CenteredRamanujanVarianceAndAbelCofactorCancellation (Route PM support)
- Centered discrete Bernoulli sawtooth B̃₁(d,n) = {n/d} − (d−1)/(2d) = ((n mod d) − (d−1)/2)/d: zero at d=1, zero period sum, |·| ≤ (d−1)/(2d) < ½; at d|n: −(d−1)/(2d); at predecessor: +(d−1)/(2d); sign flip B̃(n) + B̃(n+1) = 0 across d|n+1, jump 1 − 1/d.
- Power-damped Ramanujan cumulative prefix (cofactor weights W_{ε,Q+1}(d), |W| ≤ d^{−ε}) = periodMean + centered sawtooth prefix (d=1 mode vanishes; |·| ≤ ½Σ_{d=2}^{Q+1}d^{−ε}). Dyadic difference P(2N) − 2P(N) = Fermi prefix at t = 1/(2N) = transfer convolution of damped Möbius Fermi prefixes.
- Cesàro-centered vs energy-centered Ramanujan primitive differ by Δ(q) = φ(q)/2 − Λ(q); Gram matrices differ by rank-one Δ(p)Δ(q); meanCenteredQuadratic = energyVariance + (Σ w_q Δ(q))².
- Variational: Σ_N((P(N) − c)²/(N(N+1))) = energyVariance + (c − energyMean)² for every c; so energyVariance ≤ reciprocal-weighted energy of the centered sawtooth prefix (c = periodMean).
## MultiOctaveStepBrickPartitionAndWitnessDyadicPositivity (Route PW-B)
- φ_a = 0 on (1/2,1] for a ≥ 2. On reciprocal cell I_n = (1/(n+1), 1/n], ⌊1/t⌋ = n and φ_d(t) = fermiCellMatrix(d,n) = 2⌊n/(2d)⌋ − ⌊n/d⌋ ∈ {−1,0}: upper triangular (0 for n < d), diagonal −1, −1 on band d ≤ n < 2d.
- Σ_{m≤N/k}μ(m)⌊n/(km)⌋ = 1_{k≤n} (n ≤ N). Dilated Möbius combinator B_{k,N} = −Σμ(m)φ_{km} equals 1_{k≤n} − 2·1_{2k≤n} on I_n; dyadic resolvent Σ_{j≤N}2^jB_{2^jk,N} = 1_{k≤n}; difference gives EXACT single-cell indicator δ_{n,k} on bulk cells 1 ≤ n ≤ N (in span{φ_a : a ≤ N}, coefficients grow like 2^N).
- Re dyadicForm(v,v) = ½(∫_0^{1/2}|v|² − ∫_{1/2}^1|v|²). RH ⇔ every Fermi–Nyman witness has top-octave energy ≤ lower-half energy (under RH they are equal: half-mass law); domination ⇒ witnessNegIndex = 0 = rightStripMultiplicityCount ⇒ RH.
## RoutePMVarianceToWitnessSynthesisAndCriticalStripBridge
- Power-damped Fermi source ∈ L²(0,∞) with Mellin analytic on Re s > ½ unconditionally for ε ≥ ½; for 0 < ε < ½ conditional on uniform-in-Q bound of centered sawtooth variance / mean-centered quadratic / any shifted budget (criterion, open). All ε > 0: Σ‖w_ε(q)‖ = 1, log-square moment summable, energy mean uniformly bounded. Master packages ε=½ admission, variance ≤ sawtooth energy, Selberg diagonalization, witnessNegIndex = rightStripMultiplicityCount, RH ⇔ top-octave domination.
## VasyuninReciprocityAndExactTailGramProducer
- |I_n| = 1/(n(n+1)); bulk (1/(N+1),1] integral = Σ_{n≤N} cell integrals.
- Fermi Gram: global = tail(0,1/(N+1)] + head; head = Σ_{n≤N}cellMatrix(d₁+1,n)cellMatrix(d₂+1,n)/(n(n+1)) EXACTLY (no ℓ¹ truncation artifact); tail = global − cellular head.
- Single-cell combinator Δ_{k+1,N}: head energy = 1/((k+1)(k+2)) if k+1 ≤ N else 0; tail energy = global − cell (top octave: global − ½).
- Báez–Duarte: bdDistDiscrete(N)² ≤ 1 + 2Σc_iθ_i log θ_i + Σc_ic_j bdGram(θ_i,θ_j), θ_i = 1/(i+1); reciprocal Gram certificates below (1/(k+1))² for all k ⇒ RH (criterion).
## SawtoothCharacterExpansionAndCriticalStripPoleBridge
- B̃₁(d, d−1−r) = −B̃₁(d,r); B̃₁(d,d−r) + B̃₁(d,r) = 1/d (1 ≤ r < d). Σ_{r<d}B̃₁(d,r)² = (d²−1)/(12d) < d/12 (per-residue mean square (d²−1)/(12d²) < 1/12).
- Divisor-remainder hyperbola split: period bias + centered sawtooth head + large-divisor block + density tail. For 0 < ε < ½: unconditional (log N)^4 saving ‖R_ε(N)‖ ≤ 1 + CN^{1−ε}/(log N)^4; large-prime sector: head energy = o(sector energy), mixed energy ~ −sector, complement energy ~ +sector (complementary cancellation — signed mixed term cancels the diagonal asymptotically).
- Admission ⇔ centered-source admission ⇔ ∫|R_ε(x)|²/x² < ∞. Given uniform sawtooth budget at ε ≤ ½: cleared Mellin s·ζResUnit(s+ε)·M[F_ε](s) = (s+ε−1)(1−2^{1−s})ζ(s) on ½ < Re s < 1, and zero translation ζ(ρ)=0, Re ρ > ½+ε ⇒ ζ(ρ−ε)=0 (iterating pushes off-line zeros left ⇒ contradiction). Cofinal (ε → 0) sawtooth or mean-centered budgets ⇒ RH (criteria; budgets for ε < ½ are open = RH-strength).
## WitnessCellTransferAndTopOctaveTailInequality
- Witnesses ⊥ dilated Möbius combinators, dyadic resolvents, single-cell combinators. Head pairing of Δ_{k,N} with w = ∫_{I_k}w̄ (k ≤ N).
- Witness cell transfer: ∫_{I_k}w̄ = −∫_0^{1/(N+1)}Δ_{k,N}w̄ (k ≤ N) — bulk cell integrals transfer exactly into the origin tail; top octave ∫_{1/2}^1 w̄ = −∫_0^{1/(N+2)}Δ_{1,N+1}w̄ for every N.
- |∫_{I_k}w̄|² ≤ witnessMass(w,1/(N+1))·(‖Δ_{k,N}‖² − 1/(k(k+1))); |∫_{1/2}^1 w̄|² ≤ (∫_0^{1/2}|w|²)(‖Δ_{1,N+1}‖² − ½). (Δ energy grows ~4^N; origin mass shrinks — product controls nothing without rates.)
## SignedLcmFractionalDefectAndCompleteFibreCollapse
- Selberg coordinate Y_{N,c}(e) = Σ_{d≤N,e|d}c_d/d; Q_Sel = Σφ(e)Y(e)² ≥ 0. Signed lcm defect R(N,M,c) = Σc_{d₁}c_{d₂}{M/lcm}. LOSSLESS: Σ_{k≤M}s_{N,c}(k)² = M·Q_Sel − R(N,M,c) for all N, M (no ℓ¹ loss). Successor reciprocity: R(M+1) − R(M) = Q_Sel − s_{N,c}(M+1)². R = 0 at common multiples of [1,N] ⇒ Σ_{k≤M}s² = M·Q_Sel exactly there (clock period). Interval and origin-tail versions exact.
- LCM fibres F_{N,c}(L) = Σ_{lcm(d₁,d₂)=L}c c: R = ΣF(L){M/L}; Σ_{q|L}F(q) = s_{N,c}(L)²; F(L) = Σ_{d|L}μ(L/d)s(d)². Möbius weights: s_{N,μ}(k) = 1_{k=1} for k ≤ N; complete-fibre collapse F_{N,μ}(L) = μ(L) for 1 ≤ L ≤ N (3^{ω(L)} terms cancel); for L > N excess = Σ_{d|L,d>N}μ(L/d)s(d)².
## BarbanVehovLogarithmicDiagonalAndKerPCauchyPinch
- Y_{N,c}(1) = H_c(N) (harmonic shadow = ker P centering coordinate). Σ_{e≤N}μ(e)Y(e) = c(1). Q_Sel ≥ c(1)²/Σ_{e≤N}sqfreeTotientInv(e); on ker P (H_c = 0) sharpened to denominator Σ_{e=2}^N.
- Jordan J₂ = μ*id², Σ_{e|n}J₂(e) = n². Franel gcd form Σc c gcd²/(d₁d₂) = Σ_e J₂(e)Y(e)² — SAME Selberg coordinates as Q_Sel = Σφ(e)Y(e)²; difference Σ_{e≥2}(J₂ − φ)Y² (e=1 harmonic shadow cancels for every c).
- Barban–Vehov weight b_X (supported [1,X], X ≤ N): s_{N,b_X}(1) = log X, s(k) = Λ(k) for 2 ≤ k ≤ X, s = barbanVehovCoeff for all k (incl. tail). Pinch (log X)²/Σ_{e≤X}sqfreeTotientInv ≤ Q_Sel(b_X) ≤ 4A²(1 + log X); normalized w_X = b_X/log X: 1/Σ sqfreeTotientInv ≤ Q_Sel ≤ 4A²(1+log X)/(log X)² = O(1/log X). Mean square: (log X)² + Σ_{2≤k≤X}Λ² + Σ_{X<k≤M}b_X(k)² = M·Q_Sel − R(N,M,b_X).
## KerPCenteredSieveAndFirstSecondMomentReciprocity
- First moment: sievedFractSum F(m) = Σc_d{m/d}; F(m+1) − F(m) = Y(1) − s(m+1); Σ_{k≤m}s(k) = m·Y(1) − F(m). On ker P (H_c = Y(1) = 0): |Σ_{k≤m}s(k)| ≤ Σ|c_d| for all m (no drift).
- kerPEndpointWeight: subtract N·H_c(N) at d = N ⇒ H = 0, preserves c(d) for d < N and s(k) for k < N (keeps Λ recovery for Barban–Vehov with X < N); ker-P Selberg lower bound c(1)²/Σ_{e=2}^N sqfreeTotientInv. (Endpoint coefficient N·H_c can be large — ℓ¹ cost moved to one coefficient.)
## TwoLagArithmeticCone (namespace TwoLagSieve)
- lag-2 eigenvalue λ₂(n) = μ(n) + 2·1_{2|n}μ(n/2); Σ_{e|n}λ₂(e) = n·1_{n|2} (inverts gcd kernel for lag 2). Odd n ≥ 2 with μ(n) = 1 ⇒ φ(n) ≥ 8. MomentCone(V,x,y): five facets 2V+3x+y, V+x+y, V−x+y, V−4x−2y, V−x−2y ≥ 0.
- Every n ≥ 2 has (φ(n), μ(n), λ₂(n)) ∈ MomentCone (case split by 2-adic valuation: n odd/2r/4r/8r). MomentCone ⇔ nonnegative masses A..E on generating modes 2,3,4,6,12 (V = ΣA..E, x = −A − B/2 + D/2, y = A − B/2 − C − D/2 + E/2). Dual: a linear inequality αV + βx + γy ≥ 0 holds on the cone ⇔ α−β+γ, 2α−β−γ, α−γ, 2α+β−γ, 2α+γ ≥ 0 (five rays).
## TwoLagSievePeriod
- Joint count on complete period P (lcm(a,b) | P): #{k ≤ P : a|k, b|k+h} = P/lcm if gcd(a,b)|h else 0 (CRT, no coprimality); density gcd/(ab)·1_{gcd|h}.
## TwoLagMomentCone
- periodCovariance(N,c,h) = centered lag-h covariance of sieveSeq over 1..N!: = Σ_{e=2}^N w_h(e)Y(e)² with Σ_{e|g}w_h(e) = g·1_{g|h}: lag 0 → φ (Selberg variance), lag 1 → μ (Bézout covariance − H²), lag 2 → λ₂. Every finite sieve's (lag0, lag1, lag2) ∈ MomentCone; conversely, at N+12, every cone point with arbitrary mean H is attained by an explicit weight (Ramanujan-inverse of a profile on modes 1,2,3,4,6,12). Complete classification of universal linear inequalities in the three lag moments (= five facets). Lag 2 separates weights with equal mean, variance, lag-1 covariance.
## AffineFourierCorrelation (namespace AffineSieve)
- On ZMod P: correlation C_a(b) = P^{−1}Σ_kf(k)f(ak+b); DFT in b: Ĉ_a(r) = P^{−1}f̂(r)f̂(−ar) (holds for non-invertible a).
- Divisor indicator on ZMod P (d|P): DFT = (P/d)·1_{addOrder(r)|d} (Fourier support = frequencies of order dividing d).
## DivisorSieveAffineSpectrum
- On ZMod N!: DFT of residue signal Σc_d1_{d|k} at r = N!·Y(addOrder r) — Fourier coefficients ARE Selberg coordinates. Affine correlation DFT = N!·Y(q)Y(q/gcd(q,a)), q = order(r).
- Equality of ALL affine data (a,b) ⇔ equality on slopes 1..N and one period ⇔ equality of comparable products Y(q)Y(d) for d|q ≤ N ⇔ Y_e = ±Y_c with sign constant on components of the nonzero divisibility graph. Explicit weight with modes 3 and 5 only: flipping the 5-sign invisible to every affine quadratic observation.
## AffineSievePhaseRecovery
- Real version for actual sieveSeq: affineMoment(N,c,a,b) = complete-period correlation; DFT = N!Y(q)Y(q/gcd(q,a)); affine data ⇔ comparable products ⇔ componentwise signs. Same affine data, sieveSeq(0) = 6 vs |sieveSeq| ≤ 5 everywhere: NO functional of affine (quadratic) data recovers |origin response| (no absolute-origin decoder).
## SieveTripleFourier (namespace SieveMoments)
- Triple correlation T(h,k) = P^{−1}Σf(n)f(n+h)f(n+k); double DFT = P^{−1}f̂(r)f̂(s)f̂(−(r+s)) (closed triangle); for divisor sieve = (N!)²Y(ord r)Y(ord s)Y(ord(r+s)); triple data equal ⇔ triangle products equal.
- Odd-order mode q: diagonal double DFT at (N!/q, N!/q) = (N!)²Y(q)³. Anti-periodic f (f(n+t) = −f(n)) ⇒ every odd-length translated moment vanishes.
## ParityLiftedSieveMoments
- Explicit weight with Selberg coordinates exactly at 6 (value 1) and 10 (value t); response = (−1)^{k odd}·(−(1+t) + 3·1_{3|k} + 5t·1_{5|k}); anti-period 15; flipping t sign preserves all affine data; all odd translated moments vanish for every t.
## CubicSievePhaseRecovery
- Real triple moments: double DFT = (N!)²Y(ord r)Y(ord s)Y(ord(r+s)); triple data ⇔ triangle products; triple data determine every signed ODD-order Selberg coordinate (cube readout, odd 3rd power injective). Parity obstruction: real parity weights have equal affine data and equal (zero) odd translated moments, but origin 6 vs |·| ≤ 5 ⇒ no decoder of |origin response| from affine + all odd moments.
## EvenPrimePairMomentCalculus
- Centered residue row r_p(x) = p−1 at 0 else −1: Σ r_p^j = (p−1)^j + (p−1)(−1)^j; shift-mean zero. CRT: factorial average of F(n mod 3, n mod 5) = (1/15)Σ_{x,y}F. Sixth moment of a·r₃ + b·r₅: 22a⁶ + 360a⁴b² + 480a³b³ + 1560a²b⁴ + 820b⁶ (contains odd cross a³b³). All 2-lag and 4-lag translated products invariant under b → −b (cross terms are products of zero-mean rows).
## SixthSievePhaseRecovery
- Two-parameter weights evenPairReal(a,b) with coordinates a at 6, b at 10.
- evenPair response = (−1)^{k odd}(a·r₃(k) + b·r₅(k)); affine data ⇔ a² = c², b² = d²; odd moments 0; even moments = parity sign × CRT row averages; all moments of degree ≤ 5 invariant under b → −b; zero-lag sixth moment difference = 960a³b³. Affine + one sixth moment ⇔ (c,d) = ±(a,b). Degree six is SHARP for phase recovery in this sector.
## SieveMomentFourier
- Full m-lag DFT of translated product moment = 1_{Σr_i = 0}·Π f̂(r_i) (zero-sum resonances); for divisor sieve = (N!)^m Π Y(ord r_i) on resonances.
## ValuationTripleResonance
- Triple (r, r, (p−2)r) with r of order 2^k p (p odd; p=1: (r,r,−r)), all of exact order 2^k p, sums to N!/2^k (depends only on k). Pairing one triple with negative of another gives zero-sum six-resonance with product (v(2^kp)v(2^kq))³.
## SixthValuationPhaseRecovery
- sixthPairReadout = (N!)^6(Y(2^kp)Y(2^kq))³; equality ⇔ equal signed pair product. Rank-one rigidity: a_ia_j = b_ib_j on a set ⇔ a = b or a = −b there (incl. zeros). Sixth translated moments alone recover all relative signs within each 2-adic valuation block (one global sign per block).
## MixedValuationQuintic (namespace SieveMoments.MixedValuation)
- Lower order 2^k(2p+1), upper 2^{k+s+1}(2q+1); upper pair (r, (2^{s+1}(2q+1)−1)r) sums into the lower class center; 5-resonance (lower triple − upper pair); fifthReadout = (N!)^5Y(lower)³Y(upper)²; with upper magnitude known, orients lower coordinate unless Y(upper) = 0.
## SieveHalfPeriodTranslation (namespace SieveMoments.HalfPeriod)
- Reflection weights 2·gcdProjection(h) − c: coordinates kept where q|h, negated otherwise. A shifted divisor sieve k ↦ s(k+h) is again a divisor sieve ⇔ 2h is a period ⇔ every active raw divisor d|2h; then the translate equals the reflection (uses evenness of residue signal: DFT real/even). Reflection preserves ALL translated moments; preserves affine data ⇔ every comparable product crossing the resonant set (q∤h, d|h) vanishes.
## SieveValuationPhaseRecovery (namespace SieveMoments.ValuationPhase)
- activeDepth = max 2-adic valuation of active Selberg modes. Sixth moments ⇒ squares of all coordinates; fifth diagonal (r,r,−2r,r,−r) ⇒ odd coordinates exactly (fifth power injective); quintic receiver orients every lower valuation class against an active top mode. ⇒ fifth + sixth translated data determine all coordinates up to flipping the single highest active valuation class (if depth > 0).
## SieveCanonicalTranslation
- dyadicPeriod(N,k) = 2^k·(odd part of N!); q | it ⇔ v₂(q) ≤ k. canonicalShift = dyadicPeriod(depth − 1); 2·shift is a true period; companion = reflection by it: flips exactly the top active valuation class, is a literal translate of the response, involution, preserves active support/depth and EVERY translated moment; differs from c iff depth > 0. Fifth+sixth data ⇒ e = c or e = companion(c) on [1,N].
## SieveAffineTranslationAnchoring
- HasAnchor: active divisor edge q → d with v₂(q) = depth > v₂(d). Affine data distinguish companion ⇔ HasAnchor.
- Fifth+sixth translated moments ⇔ e ∈ {c, companion(c)}; ALL translated moments are determined by orders 5 and 6. Full observation fibre (affine + all translated): {c} ∪ {companion(c) if no anchor}. Absolute recovery ⇔ activeDepth = 0 ∨ HasAnchor; a distinct indistinguishable real sieve exists ⇔ depth > 0 ∧ no anchor (witness = companion = literal half-period translate).
## CoprimeOverlapQuarticReadout
- p,q,r odd pairwise coprime: frequencies (d+a+b, d−a+c, d+b+c, d−2b−2c) (d order 2) sum to 0 with orders 2pq, 2pr, 2qr, 2qr; fourthReadout = (N!)⁴Y(2pq)Y(2pr)Y(2qr)² (relative sign of two modes via third).
## IncomparableSieveQuartic
- momentDFT injective (full lag arrays recovered from all zero-sum products). In zero-sum tuple, an order occurring once divides product/lcm of others. Two incomparable orders A ∤ B, B ∤ A with only these modes active: equal squares ⇒ identical quartic arrays (no odd multiplicity possible). Squares of all coordinates ⇔ all quadratic lag moments.
## SieveMomentSpectralEquivalence
- Translated m-arrays equal ⇔ products over every zero-sum m-tuple equal. Quadratic arrays ⇔ all Y(q)²; fourth arrays already give all Y(q)² via (r,−r,r,−r).
## ArithmeticEdgeResonance
- In a zero-sum tuple each order divides product of the others; a nontrivial block coprime to all other orders cannot occur in only one entry. Blocks (pairwise coprime odd values >1 per vertex): edge order 2·v(u)v(w); edge orders incomparable unless same edge; in any resonance every vertex repeats. Edge frequency d + N!/p − N!/q has order 2pq; 4-cycle frequencies sum to 0.
- Fourth moments read 4-cycle products Y(2pq)Y(2qr)Y(2rs)Y(2sp) and triangle products Y(2pq)Y(2pr)Y(2qr)².
## FourEdgeQuarticRelations
- Combinatorics: a 4-edge multiset with no singleton vertex is (paired edges | triangle + doubled edge | 4-cycle); square + triangle + cycle equations (QuarticRelations) determine every such product (complete).
## ArithmeticEdgeQuartic
- For edge-supported sieves (coords only at 2·v(u)v(w)): full fourth lag array ⇔ competitor edge-supported ∧ QuarticRelations(squares, triangles, 4-cycles).
## ArithmeticEdgeSieveFamily
- Ramanujan inversion realizes any real profile on edge orders as actual weights (cutoff = 2 + Σ orders + n). Affine data ⇔ edge magnitudes (squares); affine data force any competitor into the realized edge family; fourth arrays between family members ⇔ QuarticRelations of edge amplitudes.
## ArithmeticEdgeTranslation
- Represented translate preserves all translated arrays. Edge-sieve negation: weights(−a) = −weights(a). halfPeriod = Π vertex blocks (odd); every edge order | 2·halfPeriod.
- Edge sieves have explicit odd ANTIPERIOD halfPeriod: s(k + Πv) = −s(k) (reflection = negation); all odd translated moments vanish; moment(−a) = moment(a). Sixth moments ⇔ CommonSign (one global sign); translation equivalence ⇔ CommonSign (shift 0 or halfPeriod).
## ArithmeticEdgePhaseCode (namespace ArithmeticEdges, BinaryPhase)
- Binary sign code over ZMod 2: columns = active edge orders, rows = active-triangle comparisons x_uv + x_uw = 0 and active 4-cycle parities x_uv + x_vw + x_wz + x_zu = 0. Twist by x ∈ ker ⇔ equal fourth-lag arrays; constants in kernel; |ker| = 2^{#active − rank} (rank–nullity).
## ArithmeticEdgePhaseFibre
- Signal equality ⇒ coordinate equality (Fourier readout). Fourth-data fibre of distinct actual cutoff signals (arbitrary competitors) ≃ ker of phase code; card = 2^{#active − rank}.
## ArithmeticEdgePhaseOrbits
- All-ones code vector = literal halfPeriod translation; commonCode = span{1}.
- Phase orbits (code mod constants) ⇔ literal translation classes; #orbits = 2^{#active − rank − 1}; every code vector constant ⇔ rank = #active − 1; rank deficiency ⇒ explicit fourth-data-indistinguishable non-translate.
## ArithmeticEdgeObservationHierarchy
- On edge support: affine data ⇔ quadratic translated arrays; squares ⇒ moments through degree 3 (odd vanish); fourth arrays ⇒ all moments through 5 and affine data. Order-two Ramanujan atom matches degree ≤ 1 data of any edge sieve but is never a translate (edge profiles vanish at orders 1, 2).
## ArithmeticEdgeObservationOrder
- SHARP recovery degree (up to translation, vs arbitrary real competitors, with affine data): ≤1 active order → 0 extra; else degree 4 suffices iff phase-code rank = #active − 1, otherwise degree 6 needed and suffices. Without affine data: need ≥ 2 plus same (degrees 2, 4, 6). Two active orders always admit a non-translate matching affine + degree ≤ 3.
## SieveThresholdRounding (namespace Threshold)
- Noise rounding: keep coords with |a| > δ, use competitor sign; for m ∈ {5,6}, magnitudes within δ and product error ≤ δ^6 (δ ≤ 1) ⇒ rounded products exactly equal (sign of product stable).
## SieveRawMomentPerturbation
- Raw lag error ε on m-arrays ⇒ resonant product error ≤ ε (factorial normalization exact, no loss). Sixth-array error ⇒ |Y^6 − Y'^6| ≤ ε; with ε = δ^6: ||Y| − |Y'|| ≤ δ (stability).
## SieveResonantVisibility (namespace LinearVisibility)
- Prime-factor count of order is subadditive under sums; pairwise coprime orders multiply. Visible(q): q appears linearly in a 5/6-resonance with other orders in admitted set S. Visibility with prime-power companions ⇒ ω(q) ≤ 5.
- Prime-power orders (with 1) keep the full lcm of [1,N]; divisibility by all prime-power orders ⇒ by all orders. Short family (≤5) with prescribed sum order ⇒ sixth-moment visibility word.
## SieveVisibilitySpikeEstimate
- Spike perturbation ±t at one coordinate: if every changed nonzero product has spike multiplicity odd ≥ 3, product error ≤ 2M^6t³ (cubic).
## SieveCoordinateSupNorm
- Ramanujan expansion sieveSeq(n) = Σ_{q≤N}Y(q)·c_q(n) (lag coefficient, |c_q(n)| ≤ φ(q)); pointwise signal error ≤ Σφ(q)|ΔY(q)| ≤ (Σ_{q≤N}φ(q))·η.
## SievePhysicalTranslationStability
- Noisy recovery: if fifth and sixth arrays differ by ≤ δ^6 (δ ≤ 1), ∃ ONE shift t with |s_e(n) − s_c(n+t)| ≤ 3(Σφ(q))δ for all n; raw ε ⇒ 3(Σφ)ε^{1/6} (Hölder-1/6 stability; threshold rounding to exact case).
## SievePhysicalTranslationSharpness
- One-mode family evenPairReal(δ/2,0): signal ≤ δ, moment differences ≤ δ^6 vs zero, but distance from zero ≥ δ/2 after every shift ⇒ no uniform exponent α > 1/6 (even near zero). Exponent 1/6 sharp.
## SieveHighestDyadicCoordinate (namespace TopAnchor)
- topOrder = 2^{⌊log₂N⌋} is the unique admitted mode at max depth; nonzero top coordinate fixes activeDepth; companion then flips only Y(top). Raw fifth-array noise ε bounds |Y(d)³Y(u)² − Y'(d)³Y'(u)²| ≤ ε for v₂(d) < v₂(u).
## SieveArithmeticSourceAnchors
- Squarefree-supported weights have Y(q) = 0 at non-squarefree q; so for N ≥ 4 the top dyadic coordinate vanishes for Möbius rows and their tapers (top-anchor classification inapplicable to arithmetic sources).
- Terminal-prime anchors: Möbius taper coordinate at a tail prime p = −w(p)/p (single multiple); Barban–Vehov anchor nonzero ⇔ p < X.
## SieveCubicAnchorEstimate / SieveHighestModeStability (TopAnchor)
- Scalar lemmas: large magnitudes (≥1) make sixth-power errors Lipschitz; |x−y|³ ≤ 4|x³−y³|; with |X|,|Y| ≥ 1 and errors δ³ on X⁶, x⁶, x³X²: |x−y| ≤ 2δ. Top-mode stratum (|Y(top)| ≥ 1 for both): fifth+sixth raw errors ≤ ε ⇒ one shift with signal error ≤ 2(Σφ)ε^{1/3} (cube-root stability, lower coords arbitrary).
## SieveHighestModeSharpWitness / SieveHighestModeSharpness (TopAnchor.Sharp)
- N=3 family weights(t): signal = parity(n) + t·r₃(n), Y(2) = 1; near parity (≤2|t|); every shift leaves discrepancy ≥ 2t between ±t; sixth arrays identical for ±t (moment(−t) = (−1)^m moment(t)); fifth arrays differ ≤ 224t³ (linear term averages out over ZMod 3). ⇒ no exponent > 1/3 on top-mode stratum, even near pure parity source. Cube-root sharp.
## SieveParityAnchorEstimate (namespace ParityNeighborhood)
- Positive anchors A,B ≥ 1: |A−B|, |A⁴−B⁴| ≤ |A⁶−B⁶|. Mixed sixth products a²A⁴ recover |a| within 4δ; mixed linear products aA⁴ recover a within 4ε (constant coordinate has linear readout near parity).
- Noisy readouts: Y(q)²Y(u)⁴ via (r,−r,s,−s,s,−s); Y(1)Y(u)⁴ via (0,s,−s,s,−s); same-depth (Y(d)Y(u))³ via valuation six; Y(4)Y(8)²Y(2)² (fifth) and Y(12)³Y(4)Y(2)² (sixth) — the only higher-depth interactions below 12 / 20.
- Rounding lemmas: retained products with relative error < 1 become exact after thresholding; anchored monomial with unit anchor converts noisy degree-d product into exact identity when perturbation degree ≤ d; retained square fixes sign of odd-power factor; cubic-linear readout fixes same-depth relative sign.
## SieveParityCutoffRecovery (ParityNeighborhood)
- Parity anchor Y(2) ≥ 1 (both): all magnitudes within 4δ when sixth error ≤ δ^d (d ≥ 2, competitor coords ≤ 3); odd and parity-depth modes oriented at degree 3; any retained higher mode orients lower modes at degree 5; below 12 only the 4–8 relation, below 20 only 4–12 pair repeat above parity depth. Phase relations ⇒ e = c or companion (coordinate recovery); coordinate rounding ⇒ one physical translation with error 3(Σφ)τ. Cutoffs N < 12: degree-3 rounded recovery; N < 20: degree 5.
- Parity-neighbourhood physical stability: with Y(2) ≥ 1 for both and competitor coords ≤ 3: N < 12 with fifth/sixth errors δ³ ⇒ one translation, error 12(Σφ)δ; N < 20 with δ⁵ same.
## SieveParityFourierBounds
- Multivariate DFT sup bound: coefficient sup ≤ C ⇒ array sup ≤ C. Resonant product error η ⇒ raw moment error ≤ (N!)^m η (inverse direction has factorial loss). Translated signal sup-error D ⇒ |Y_e(q) − phase·Y_c(q)| ≤ D for every Fourier coordinate. Phase incompatibility: z^p = w^q, q odd, |z|,|w| ≤ 1 ⇒ p|1−z| + q|1+w| ≥ 2.
## SieveParityResonanceCounts
- In zero-sum tuples: a prime confined to one order forbids that order appearing exactly once; annihilator version; under a common half-period h (all orders | 2h), the number of modes with order ∤ h is even. Multiplicity lower bounds: orders {2,3}, odd count of 3 ⇒ ≥3 non-parity entries; {2,8,12} with odd #12 ⇒ ≥5; {2,12,20} with odd #20 ⇒ ≥6.
## SieveParitySharpWitnesses
- Families sharpProfile(A,B,t) (Y(2)=2, Y(A)=Y(B)=t) vs flipped at B: raw moment differences of all degrees ≤ 6 bounded by 128(N!)^6 t^d with d = 3 (A=B=3), 5 (8,12), 6 (12,20). translationPhase(N,q,h): unit modulus, q-th power 1, phase relations from frequency relations.
- Separation: any translate of the flipped witness differs from the original by D with 2t ≤ kD (k = 3, 5, 8) via phase incompatibility (phase relations (8,12): z² = w³; (12,20): z³ = w⁵).
## SieveParityNeighborhoodStability
- parityWeights(N) has Y(2) = 2 only. Physical unit ball around it ⇒ Y(2) ≥ 1, |Y(q)| ≤ 3. LocalPairwiseHolder(N,b,α): local Hölder-α recovery modulo one translation from fifth+sixth raw arrays. Attained: α = 1 (N = 2, Lipschitz), 1/3 (N < 12), 1/5 (N < 20), 1/6 (all N).
## SieveParityNeighborhoodSharpness
- Generic obstruction: polynomial raw cancellation L·t^d + linear orbit separation ⇒ no α > 1/d. Hence α ≤ 1/3 (N ≥ 3), ≤ 1/5 (N ≥ 12), ≤ 1/6 (N ≥ 20), ≤ 1 (N = 2).
## SieveParityAmplitudeScaling / SieveParityNeighborhoodClassification
- Moments scale by scl^m; local exponent invariant under nonzero amplitude rescaling. SHARP CLASSIFICATION: optimal local exponent at any nonzero parity source = 1/d with d = 1 (N=2), 3 (N<12), 5 (12≤N<20), 6 (N≥20).
## SieveLinearVisibility
- Signed sixth root stable near |A| ≥ 2; bounded product perturbation ≤ 6M⁶ε; linear resonant factor stable when co-factors ≥ 1: |Δa| ≤ (1 + 6M⁷)ε. Visible coordinates (linear in a 5/6-resonance with anchored co-factors in S) are recovered Lipschitz.
- Physical unit ball bounds every coordinate by 1 + Σ|Y_b|. Visibility of every missing mode (from active set) ⇒ local Lipschitz (α = 1) recovery (normalized and general, by rescaling).
## SievePrimePowerVisibility
- Visible(q) w.r.t. prime-power support ⇔ ω(q) ≤ 5 (primary frequencies sum to order q).
## SieveVisibilityPerturbations / SieveVisibilityPhaseSeparation / SieveVisibilityRadialEstimates
- Spike at a missing mode moves signal ≤ φ(q)|t|; invisible ⇒ fifth/sixth raw arrays change ≤ 2(N!)^6 M^6 t³ between ±t. Lower-depth mode has odd-power phase relation with top dyadic mode ⇒ any translate separates ±t spikes by 2t ≤ (p+u)D given retained top coordinate. Radial scaling (1+t)b: raw arrays change linearly, translation separation 2t ≤ D (|Y| ≥ 2).
## SieveLocalVisibilityClassification
- On the nonzero highest-dyadic stratum: local cube-root recovery always; never better than Lipschitz (radial obstruction); Lipschitz ⇔ every missing mode visible; else exactly 1/3 (invisible spike obstruction). Complete sharp classification α ∈ {1, 1/3}.
## SievePrimePowerLocalRegularity
- primePowerWeights (Y = 2 on prime powers & 1) vs fullWeights (Y = 2 everywhere); top order is a prime power; all missing modes visible ⇔ every q ≤ N has ω(q) ≤ 5.
- Prime-power source local exponent: 1 if every q ≤ N has ω(q) ≤ 5, else 1/3 (sharp); full source always 1. Periodicity ⇔ every active order divides the period; sources containing all primary orders have least period = horizon modulus lcm(1..N). ∃ N (ω(N) = 6) where prime-power and full sources share least period AND dyadic depth but have different sharp exponents (1/3 vs 1) — period/depth do not determine local regularity.
## CoprimeOverlapSieveFamily (CoprimeOverlap.Triangle)
- Three overlapping orders 2pq, 2pr, 2qr (p,q,r odd pairwise coprime >1): antichain; Ramanujan-inverse weights realize any coordinates; halfPeriod = pqr is an exact antiperiod (negation = translation); odd moments vanish; affine data ⇔ squares; affine data force any partner into the family.
## CoprimeOverlapObservationOrder
- ≤1 active coordinate: squares suffice. Signs invisible through degree 3 always; with a missing coordinate invisible through degree 5 (two incomparable orders); all three active: affine + fourth moments ⇒ common sign (three readouts a₁a₂a₀² etc.); sixth ⇔ common sign.
- Triangle recovery degree (vs arbitrary real competitors, affine data supplied, modulo translation): ≤1 active ⇒ 0; all three active ⇒ 4; some missing (≥2 active) ⇒ 6. Sharp. Translation equivalence ⇔ common sign (shift 0 or pqr).
## OddPrimeSieveFamilies
- Atom at odd prime p: weights 1@1, −2@2, −p@p, 2p@2p has single Selberg coordinate 1 at 2p; response = parity(n)·r_p(n) (centered residue row). Family Σa_p·atom_p: coordinates a_p at 2p; response = parity(n)·Σa_p r_p(n mod p).
## FiniteCoprimeMomentCalculus
- CRT averaging over any multiple of Πp_i (pairwise coprime): period average = product-residue average. A factor at a single independent coordinate has zero mean. Independent centered rows: quadratic and quartic translated observations depend only on coefficient squares.
## PrimeFamilyTranslatedMoments
- Prime-family period Πp (odd, divides N!) is an exact antiperiod ⇒ odd moments vanish; even moments = parity signs × CRT product averages; quadratic and quartic moments depend only on a_p² (independent signs invisible through degree 5).
## PrimeFamilyPhaseRecovery
- Sixth readout for prime family = (N!)^6(a_p a_q)³; full sixth data ⇔ coefficients up to one common sign (incl. zeros/empty); affine ⇔ squares; every independent sign flip preserves affine + all degree ≤ 5 data; affine adds nothing beyond sixth. Zero extension embeds any finite odd-prime support.
## SixthReadoutStability (namespace CubedGram)
- Cubed coefficients make the readout matrix a rank-one Gram matrix; for one global sign: error6² ≤ 512·readoutError, mass6·error6 ≤ 32·readoutError, mass6·weightedError ≤ 8·readoutError (no support assumptions). One-mode: error t^6 vs readout t^12 (⇒ sixth-root exponent); two-mode vanishing: error 64t^6 vs readout 8t^6 with mass ≥ 2.
## PrimeReadoutSharpness (namespace PrimeSharpness)
- Embedded in actual prime family at primes 3, 5: power barriers sharp — at zero, distance⁶ ≤ C·noise^α iff α ≤ ½ (norm exponent 1/6); nonzero-mass stratum iff α ≤ 1 (norm exponent 1/3).
## PrimeRawMomentContrasts (namespace PrimeRaw)
- Finite-difference cube in lags: Σ_b sign(b)·moment(cubeLag) = average of Π(s(n) − s(n+t_i)); 2^m observations; error amplification ≤ sum over cube.
- CRT selective lag: even lag ≡ 1 mod p, 0 mod other family primes; s(n) − s(n + j·lag) = parity(n)·a_p·(r_p(n) − r_p(n+j)) isolates one prime coefficient (no support assumption).
## PrimeRawMomentRecovery
- (r_p(x) − r_p(x+1))²(r_p(x) − r_p(x+2)) = p³·1_{x=0}. Factorial averages factor into prime-coordinate means; joint zero-residue density Π1/p. Six lags (λ_p,λ_p,2λ_p,λ_q,λ_q,2λ_q) ⇒ 64-vertex contrast = pairScale·(a_pa_q)³ (pairScale = p²q² or p⁵, ≥ 81). Protocol with 64M² literal sixth moments recovers coefficients up to common sign; raw noise controls cubed-Gram stability (6561·noise ≤ 64·rawNoise).
## PrimeMeasurementComplexity
- Invariance of domain ⇒ any fixed protocol with fewer than M literal observations (any degree, affine included) has two distinct positive coefficient vectors with identical data (M = #modes). Explicit decoder: least prime with nonzero diagonal contrast as anchor, inverse cube, divide by √ — recovers up to common sign.
## PrimeAdaptiveMomentRecovery
- Adaptive: diagonals first, then anchor row: ≤ 128M − 64 raw observations; exact common-sign recovery including zero support.
- Adaptive observation equality ⇔ common sign; zero-filled unobserved slots give same decoder output.
## ClassicalFoundationBoundaries (namespace ClassicalBoundaries)
- Hyperbolic boosted correlations: autocorr(cosh_α f) − autocorr(sinh_α f) = cosh(αx)·autocorr f (exact); squared version fails by cross term 2cosh(αx)·autocorr f·autocorr(sinh_α f); holds iff one correlation vanishes; strict violation on an actual smooth bump at lag 0. Finite bi-scale joint energy has the same zero set (finite-window constants) as the additive step energy alone — the multiplicative term adds no new zero states.
## AllocationBoundaryClassification
- Equality W·a + A·q = √(W²+A²)√(a²+q²) ⇔ A·a = W·q ∧ W·a + A·q ≥ 0. Finite allocation Σ√(a_i²+q_i²) = √((Σa)²+(Σq)²) ⇔ (if both totals 0: all zero; else all vectors positively parallel to total).
## ThreePrimeMomentCollision / ThreePrimeScalarPhaseCollision
- Rows at 3,5,7 with u³ = 5, v³ = 2: zero-lag sixth moment of r₃ + u r₅ − v r₇ equals that of r₃ − u r₅ + v r₇ (cubic contributions cancel). Actual weights (N ≥ 14) with equal affine data, equal all degree ≤ 5 moments AND equal zero-lag sixth moment, yet not common-sign related; a selected sixth Fourier readout differs by 10(N!)^6, so some literal sixth lag separates. (Scalar/zero-lag sixth moment insufficient; lagged sixth required.)
## PrimeGraphClockOffDiagonalSynthesisAndStationaryEnergyProducer (CHMD SourceGraph)
- ‖p‖² = ‖fst‖² + ‖snd‖²; sourcePair(p,q) = ⟨snd,snd⟩ − ⟨fst,fst⟩ symmetric, bilinear, |sourcePair| ≤ ‖p‖‖q‖ (Lagrange identity).
- |sourceEnergy p| ≤ ‖p‖²; quadratic continuity |E(P) − E(q)| ≤ ‖P−q‖² + 2‖P−q‖‖q‖; same for bounded-operator forms (×‖T‖). 0 ≤ stationaryEnergy(Θp) ≤ (1 + ‖groundPerturbation‖)‖p‖².
- Finite packets: sourceEnergy(Σa) = Σ diag + offDiag; offDiag = offDiagStationary − offDiag(arch) − offDiag(primeShift) = offDiagStationary + offDiag(primeGenerator) + offDiag(groundPotential − id); diagonal terms bounded by Σ‖a_i‖².
- Terminal-prime clock realization: any q ∈ SourceGraph is approximated by Σ_{p∈S} prime clock atoms (primes p > √N, log(N/p) > T₀) with total diagonal cost < ε ⇒ sourceEnergy(q) and every bounded operator form concentrate in DISTINCT-PRIME off-diagonal sums up to O(ε(1+‖q‖)).
- Prime-clock product = (N/(pp'))·cutoff²·profile(t + log(p'/p))·profile(t) (N cancels; scale-free prime-ratio lag). Resolvent eigenvector with μ > ½ ⇒ sourceEnergy(rieszLift w) = ((1−2μ)/μ)‖fst‖² < 0 ⇒ off-diagonal prime-clock pairing strictly negative eventually; conversely nonnegativity of off-diagonal prime-clock pairings along arbitrarily precise realizations ⇒ sourceEnergy ≥ 0 and μ ≤ ½ (criterion; the sign is the open RH-type input).
## PrimeGraphClockCorrelationKernels
- primeClockProfile(k,t,x) = cutoff_k(x)·criticalAbelLogProfile(t − x); mass/edge kernels at center t = log(N/q), lag log(q/p); mass and edge pairings of clock atoms = N/(pq)·kernels exactly; difference = signed source pairing. (No lag-only reduction, no closed form, no sign.)
