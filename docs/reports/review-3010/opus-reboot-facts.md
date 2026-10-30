# Opus reboot: mathematical facts read from the Lean corpus

Facts only, each with its Lean anchor. [L] = Lean declaration or module docstring read. (obs) = an
observation about the shape of a proof or statement, read off the source.

## F1. Archimedean subsidy (APT)

- Every positivity theorem of APT on explicit families is paid by an archimedean gain log M;
  removing that subsidy is the gap (README central finding) [L].
- Reflection identity on any configuration: Z − Re W = R, Z = Σ m|F(ρ)|², R = ½Σ m|F(ρ) − F(1−ρ̄)|²
  (`configurationReflectionDefect`) [L].
- Envelope table: at β = ½ the absolute prime majorant diverges but the oscillatory majorant
  Λ(r)/(r^{β+1/2}(r−1)) converges for β > −½. "The critical line is a failure of the absolute
  bound, not of the prime channel" [L].
- Divisor charge A(m) = χ(m)Σ_{d|m} dΛ(d)χ(m/d): A(2) = −2 log 2 is the unique negative value [L].
- Critical prime kernel negative definite on linear windows [N,(1+δ)N], positive on dyadic pairs:
  the unique negative harmonic is cancelled exactly at ratio 2:1 by +(log2/π⁴)J₂ [L].
- Period difference detector f − f(·−L) multiplies the summand at ½+δ+2πik/L by −2(cosh δL − 1) [L].
- Collar arithmetic: |aλ_N − bλ_M| < 1/15 ⇔ a(12N+1) = b(12M+1) [L].

## F2. Where the critical exponent ½ appears as a soft threshold

- BSU: ½ is exactly the exponent making cell budgets n^{-1/2}·n^{-1} summable (Nyquist absorption) [L].
- THIM: horizon-limit commutation for receivers holds exactly from damping ½
  (`horizonLimit_commutes_with_receiver_iff`); sign-blind data decide payment iff ε > ½
  (`parity_barrier`) [L].
- ACCE: pronic contraction j^{-1/2} makes the scale sum finite exactly above ½; absolute dilation
  estimates stop at ½ [L].
- BVI: receiver known for ε ≥ ½; for ε ≥ ½ the actual limit Gram is PSD of rank two; at ε = ½ moving
  limits form a ray indexed by harmonic mass [L].
- APT: at β = ½ only the absolute majorant fails, the oscillatory majorant converges [L].

## F3. Additive structure is required (Beurling-blindness)

- BVI: Beurling systems satisfy every multiplicative identity yet may have off-line zeros: "a
  mechanism that sees RH must use Bézout structure" gcd(n,n+1) = 1 [L].
- THIM selectivity classes: I Beurling-universal; II sign-blind ((Z/2)^N-invariant); III
  Bézout-selective (gcd(n,n+1)=1, pa − qb = 1). Only III can carry new information
  (`selectivity_class_III_bezout_successor_selective_laws`) [L].
- BVI: 2μ(e) ≤ φ(e), equality only at e = 6; μ separates 4 from 6 where φ does not; the successor
  covariance in Selberg coordinates is μ(e) [L].
- BVI: dyadic windows reduce consecutive divisor edges to the single pair (2,3) ("Bézout seed") [L].
- AIP: from r = 23/40 smooth odd tests separate ζ from the Liouville twin; the Catalan pair (8,9)
  carries opposite signs [L].
- BSU node criticality: zero-pole positivity on a node set N ⇔ RH ∧ N ⊇ prime powers; any
  certificate has w = Λ; deletion prices are local Euler factors (`zeroPoleBlindPositiveOn_iff`) [L].

## F4. Where failure lives

- ACT: archimedean part is Z-type (D_arch ≤ 2S_arch, monotone Lévy density); every failure of RH lives
  on prime anti-diagonals x + y = log n (`riemannHypothesis_iff_forall_prime_le_antisymmetric_weilJumpDensity`) [L].
- ACT: harmonic identity W_pf Θ = cosh(x/2) for Riemann's kernel Θ (Θ̂ = Ξ); the harmonic theta span
  is the radical of the zero form (`poleFreeWeilOperator_riemannKernelReal`) [L].
- ACT two-moment law: no positive folded supersolution in the positive decaying class; the odd form
  is not Z-type [L].
- AIP: negative conductance only on crossing pairs; on the lattice {±log a}: same-side atom iff b/a a
  prime power (ratio pair), crossing atom iff ab a prime power (product pair) [L].
- ACCE short/long split: at D = √n the short-modulus head has bounded pronic energy for every
  ε ∈ (0,1); "the whole obligation is the long-modulus quadrature" (hyperbola incidences)
  (`pmPowerDampedCenteredDivisorPrefix_eq_short_add_quadrature`) [L].
- ACCE: E_T(ε) → Σ1/(n(n+1)) ≤ 1 as ε ↓ 0; RH ⇔ no interior bump; the bump lives at n ≳ 2^{1/ε} [L].
- ArithmeticIndexDescent (via ACS README): prime squares, odd higher powers and the full pole pay
  their blocks with uniform finite negative dimension (≤ A+1, A+2); open: coarse first-prime and
  first-prime mixing sources [L].

## F5. Z versus F_q, concretely

- ACT-comp: curve comb (lattice N·log q, geometric weights) is uniformly coercive,
  J_q ≥ ((1 − q^{-1/2})²/12)∫F²; the integer comb is defeated by concentrated tests
  (J(F_λ) = O(1/λ)) [L].
- ACT-comp: over curves, cofinal admission of the receiver ⇔ Weil bound (`weil_iff_cofinal_curveReceiverEnergy`) [L].
- ACCE: over F_q[T] the centred divisor prefix is exactly constant [L].
- ACS: Kronecker rank of the zero frequencies is 1 for curves, ∞ for ζ; finite-rank configurations
  have defect 0 or ∞ [L].
- ACS: a curve's towers are its base changes; its defect is finite exactly at scales ℓ ∈ Q_{>0}·log q [L].
- ACS: the golden fake datum (q = 5, β = φ, φ^{-1}) has integral counts, rational zeta, FE, Witt
  integrality, Beurling structure, Adams operations, and Hodge defect exactly 1 [L].
- ACS: span identities (i)–(iv) of Weil's proof are exact over Z (pole plane, prime comb =
  Lefschetz, archimedean term = adjunction); RR/effectivity is what is missing [L].
- ACS: classical zero-free region = Fejér barrier a₁ < 2a₀ for nonnegative cosine polynomials [L].
- ACS: "short cycles carry all of RH": Hodge index = local positivity (theorem for η ≤ 3/10) + a
  one-prime Lefschetz bound on short cycles [L].
- ACS: maximal blind ideal: sources whose Mellin transform vanishes at every off-line Ξ zero form the
  unique maximal sharp-stable convolution ideal with nonnegative trace [L].
- SRT: the pole is a depth-½ pair at height 0 (the whole infinite prime tail); Hodge index on lag
  lattices is blind exactly to s = 0, 1 [L].

## F6. Lattice versus continuum

- AOT: lattice samples (logs of integers) of the odd Weil ledger are balanced at every aperture;
  frustration is a continuum phenomenon between lattice points (`isBalanced_lattice`); the prime
  triangle (sums log 2, log 3, log 5) has frustration index exactly 2 [L].
- AOT: horizon-uniform lattice payment beyond a finite head: odd prime side + archimedean diagonal
  ≥ (1/16)Σ_{n≥256} n q(n)² − 106 Σ_{n≤255} q(n)², nonnegative on profiles supported in [25, X]
  (`sum_towerOddPrimeSide_add_archDiag_ge_tail_sub_head_255`) [L].
- AOT: continuum towers, all primes at once: ≥ −12 e^A ∫_0^A F² (prime-set uniform, exponential in
  aperture) [L].
- AOT: rank-one law per tower: tower product part = log p (S_p(q)² − q(1)²) [L].
- SAEI: odd folding is the source of frustration; anti-aligned odd overlaps need e^{p_x+p_y} a prime
  power (`frustrated_walk_has_primeSum`) [L].
- AOT section cones: over Z the graded Chebyshev cone has RR at every aperture; Bézout at all
  apertures ⇔ RH (`riemannHypothesis_iff_all_aperture_gradedChebyshev_bezout`). Over F_q Rosati cones
  have Bézout + ample always, RR iff zero reflection defect; the golden datum fails RR [L].
- AOT: even flip read at 2: M(c♭) − M(c) = 2 log 2 · W_c(2); every amplitude reading is blind to it [L].
- AOT critical Wiener algebra W_σ: Banach algebra with spectrum the Bohr polydisk; unpaid ⇔ nonempty
  obstruction hull; translated off-line zeros ρ − ε are obstructions (`isUnit_iff_forall_bohrEval_ne_zero`,
  `not_receiverBounded_iff_exists_obstruction`) [L].
- TTPC: the 3/4 budget is met by Hardy–Littlewood/GUE (−1/144), fails for Poisson without repulsion
  (+1/16), unsigned additive sieves need Υ ≤ 8/9 (impossible): "the budget uses arithmetic
  repulsion" (`calibration_five_models_four_thirds`) [L].
- TTPC: Ramanujan lag coefficients cancel the 1/θ pole across d | q (`trapezoidal_ramanujan_cos_eq`);
  the parity-locked singular series transfers to the negative Ward–Mertens repulsion
  −Ω̂(0)Σ_{q odd} μ²(q)/φ(q) [L].

## F7. Square-root cancellation over F_q is a count

- SSA: over F_q the successor correlation of characters is a count: S(χ,χ⁻¹) = −1,
  |Σχ(x)ψ(x+1)|² = q (`norm_sq_charSuccCorr`); Kloosterman second moment Σ_a|K(a,b)|² = q(q−1) by
  orthogonality, not Weil (`sum_normSq_kloosterman`) [L]. README: "square-root cancellation is the
  shadow of an integer".
- SSA: dilation cocycle Π_{j<m} σ_f(mn+j) = σ_f(n) for σ_f(n) = f(n)f(n+1) characterizes complete
  multiplicativity (`exists_cmSign_iff_primeCocycle`); prime values cancel out of it [L].
- SSA one-third floor: every completely multiplicative ±1 sign keeps its sign on ≥ 1/3 of steps in
  log density (`one_third_log_floor`), attained at conductor 3; two-scale deficit D_N = 4E_N is
  quantized (`twoScaleDeficit_eq`); every zero-defect sign has f(2) = −1 [L].
- SSA: the complex floor −½ configuration dies at Catalan's 9 = 8 + 1 (`no_cubeRoot_successor_coloring`) [L].
- SSA hypercube phase diagram: prime-divisor hypercube Dirichlet form unbounded for −½ ≤ ε < ½
  (pole-driven, shared with the +1 twin); at ε = ½ bounded over all squarefree P for μ, while the
  +1 twin diverges like c·log X (`hypercubeDilationDirichletForm_half_bounded`,
  `not_bddAbove_hypercubeTwinDilationDirichletForm_half`) [L].
- SSA sieve functional equation: G_ε is r-periodic and Σ_m m^{−1−ε} G_ε(mx) = C_r(⌊x⌋); μ is the
  unique bounded weight satisfying it (`eq_moebiusReal_of_sieve_functional_equation`); at ε = 0, r = 2
  the folded profile is (4/π) sin(πx) sin²(πx/2) [L].
- AOG: theta h⁰ of Spec Z: h⁰(d) = log Σ e^{−πn²e^{−2d}}, h⁰(d) − h⁰(−d) = d by Poisson
  (`arithH0_riemannRoch`); Λ(s) is its Mellin generating function; this RR gives the FE, not the
  Hodge index [L].
- AOG: eventual orbit bounds with any constant upgrade to the sharp bound (tensor-power trick;
  `hasseWeilAt_of_eventually_bounded`, `riemannHypothesis_iff_eventually_bounded_of_generic`) [L].
- AOG: Hecke graphs satisfy pullback, adjunction and TT' = e^s (`heckeGraph_rosati`); Rosati
  positivity at x = orbit Hodge index (`rosatiPositive_iff_orbitHodgeIndex`) [L].
- AOG: heat-collision index: collision mass = 2(D + E) for small dBN times, D distinct right zeros,
  D even (`TheIndexExit`) [L].
- ALDG: counting alone gives a finite-head Ki–Kim–Lee at large height
  (`exists_radiusHead_heat_coeffNonneg`); scale gap: counting gives heat ≍ R/log t, detector needs
  ≍ δ²/log t [L].

## F8. Positive definiteness plus integrality = rigidity (the one forcing mechanism)

- MPG: the boundary divisor D(u) = (pole order) − (zero order) at 1 + iu is an even positive-definite
  function on (R,+) whenever Λ ≥ 0 (`IsBoundaryDivisor.isEvenPosDef`) [L].
- MPG: integer-valued PD with D(0) = 1 ⇒ D ∈ {−1,0,1}, nonvanishing set a subgroup, D a ±1 character;
  a boundary zero at u forces a pole at 2u (`boundary_zero_forces_double_pole`, `boundary_trichotomy`) [L].
- MPG boundary forcing law: (N) nonnegative weights, (Z) integer divisor, (S) simple pole, (I) pole
  isolation force D = δ₀; dropping any one admits a realized boundary zero (`boundary_forcing_law`,
  `isolation_necessary`, `simplicity_necessary`, `integrality_necessary`, `nonnegativity_necessary`) [L].
- MPG interior invisibility: ζ(s)Φ(s+κ) satisfies all four invariants and vanishes in the strip
  (`interior_zero_invisible`) [L].
- MPG: exact Fejér barrier a₁ ≤ 2cos(π/(K+2))a₀; any finite multi-frequency certificate has
  a(γ) ≤ 2a(0) (`multiFrequency_purchase_le_two`); exclusion ⇔ √A + √(Gη) < √B; dlVP is the instance
  (3,4,(5/2)log γ + C) [L].
- MPG Bochner realization: a locally finite D is a boundary divisor iff even PD; realized by one
  Dirichlet series and by an integral Euler product Π_p(1−p^{−s})^{−m(p)} (`arithmetic_bochner`,
  `integral_bochner`) [L].
- MPG: Rankin–Selberg forcing: simple poles of f and f⊗f force D_f = δ₀ (`rankinSelberg_forcing`) [L].
- MPG: positivity margin: weights ≥ −εΛ; a simple pole forces δ₀ iff ε < 1 (`simple_pole_margin_threshold`) [L].
- MPG open problem: without the FE the interior answer is no (over-regular Beurling systems;
  ζ(s)/ζ(s+1−β) keeps all four invariants); with Riemann's theta relation and integral masses only ζ
  remains (README) [L].

## F9. Dilation operators and ×2, ×3

- ADR: on power rows (I + D̃)n^s = ζ(s+ε)n^s modulo admitted rows; on log^k n·n^s rows I + D̃ is the
  Leibniz matrix of ζ^{(i)}(s+ε); eigenspace dimension = ord_{s+ε} ζ
  (`powerRow_renormalizedInversion_bounded_iff`, `powerLogRows_global_renormalizedInversion_iff_order`) [L].
- ADR: H_ε = (I − 2^{1−ε}D₂)S kills the pole exactly, symbol (1 − 2^{1−ε−s})ζ(s+ε); "Euler laws at 2 and
  3 together ⇔ the renormalized inversion law"; rows obeying two dilation laws with O(1) errors and the
  inversion law exist exactly at zeros [L].
- ADR: common cofactor Gram limits carry a cyclic Hilbert realization with ‖V_p‖ ≤ p^{−1/2}, a
  contractive W_{1/2}-representation; admitted modules are faithful, infinite-dimensional, full Bohr
  hull; a finite-dimensional actual module forces escape (`receiver_escapes_of_finiteDimensional`) [L].
- BG: on HorizonSpace N the common commutant of successor U and dilation D₂ is scalar; invariant
  subspaces are the N+2 tails (`horizon_joint_commutant`); D_aU = U^aD_a [L].
- BG: E(log N) = (N − 1) − log #(Z/Q_N), Q_N = lcm(1..N)/N: degree minus log torsion; E(log 3/2) ∈ (0,1)
  so E is no N-valued index (`boxDefect_eq_degree_sub_log_torsion`, `no_dimension_model_for_boxDefect`) [L].
- BG: pronic dilation representation ‖D_j f‖ = ‖f‖/√j, D_jD_k = D_{jk}: a unital W_{1/2}-representation [L].
- BG: the logarithmic chirp orbit closure is a compact group of completely multiplicative phases;
  finite chirp Cauchy matrices are positive definite (`chirpCauchyKernel_posDef`) [L].

## F10. Rigidity theorems that force Z or ζ (positivity + self-duality + integer)

- APD theta rigidity: a positive measure on [1,∞) with Riemann's theta law is c·Σδ_k; a degree-one
  Beurling system with the completed FE is ζ (`measure_eq_of_measureTheta_relation`,
  `beurlingSystem_rigidity_of_completed_functional_equation`) [L].
- APD Poisson rigidity: a positive self-dual measure with unit gap is a multiple of the Dirac comb;
  the unit gap is sharp; one-sided gap gives only density (`tentSelfDual_iff_eq_smul_diracComb`,
  `exists_tentSelfDual_not_comb`) [L].
- APD: integer-valued PD with φ(0) = 1 ⇔ sign character of a subgroup, on every abelian group
  (`intValued_posDef_iff_signCharacter`) [L].
- APD: Weil over F_q = PD on Z of the trace sequence with integer mass 2g; the golden datum fails on
  every group (`curve_rh_tfae`, `not_exists_posDef_golden`) [L].
- APD: "no budget below the first quantum at Re s = ½, parity included" (`fejer_quantumBudget_half`) [L].
- APD inserted vs intrinsic charge: pole order pays inserted (deformation) charge exactly (index–pole
  conservation, `indexIncrement_eq`); intrinsic charge (ζ's own zeros) is reached by no pole count [L].
- APD affine laws: positivity on Aff(Q) is induced from dilations; the integer successor forces the
  Hecke weight (nd)^{−1/2}; extremals are twisted Haar states; threshold s ≥ ½ is the critical line;
  Bost–Connes temperature β forces (nd)^{−β/2} (`integer_successor_hecke_weight`,
  `isPosDefOnGroup_heckeState_iff`, `bc_successor_hecke_exponent`, `heckeExtremal_iff`) [L].
- APD: archimedean PD functions live on the Kronecker line, arithmetic successors force Kronecker-null
  spectra; Weil's correlation admits only blind successors, its extensions indexed by the zeros
  (`integer_successor_kronecker_null`, `weil_successor_blind`, `weil_extension_classification`) [L].
- APD: "amplification is depth-homogeneous over Z": harmonic twists, Følner coupling, family averages
  and tensor powers gain on depth exactly as fast as they pay in arithmetic length (README) [L].
- APD: two-prime orbit = Bochner problem on T² (`riemannHypothesis_iff_exists_torusMeasure`) [L].
- APD: blind ideal is closed in the Fréchet topology, dense in the critical-jet topology, closed
  there iff RH (`isClosed_criticalJet_iff`) [L].
- SBWF: completed positive systems: half-pole interior forcing κ < 2Σm_ℓ; collar sparsity
  2Σord ≤ κ in a 1/(d log T) collar, sharp; pole-order-one class is R^×·ζ (`completedPositiveSystem_one_iff`);
  pole-order-one refund rigidity −E'/E + ξ'/ξ = Laplace of ν ≥ 0 ⇒ E = cξ; 5d < 9κ
  (`five_mul_degree_lt_nine_mul_poleOrder`); at κ = 2 off-critical systems exist [L].
- SBWF complete monotonicity: PD sections of Re(−F'/F) with ≤ C√x growth make F completely monotone,
  Bernstein–Widder gives a positive Dirichlet measure, then theta rigidity identifies ζ [L].

## F11. The gauge torus and the trivial point

- ACG: gauge torus G = (R/Z)^primes acts by completely multiplicative twists; multiplicative data
  determine a source exactly up to its gauge orbit (`agreeMultiplicatively_iff_exists_twist`);
  successor correlations are pure gauge charge (`integral_normSq_succCorr_twisted`) [L].
- ACG: square-root laws hold Haar-a.e., fail at the Liouville twin, are RH at 0; the exceptional set
  is comeager and null (`moebius_gauge_trichotomy`, `moebius_exceptional_residual_and_null`,
  `zero_mem_closure_exceptional`) [L].
- ACG: windowed Gram = ‖η‖²·gauge moment + near-incidence: the square-root threshold is the resolution
  of one line in G (`windowed_pow_eq_gauge_add_nearIncidence`) [L].
- ACG: boundary of a dilation is the archimedean place: escaped mass at weight n^{−σ} → log a exactly at
  σ = ½ (0 above, ∞ below); charged boundaries are critical at ¼ (`exists_pos_tendsto_escapedMass_iff`) [L].
- ACG: Möbius boundary separates gauge twins μ and μ² (→ 0 vs ≥ 1/100) (`moebius_boundary_separates_twin`) [L].
- ACG: prime source is typical except for its pole; RH ⇔ typicality modulo the pole
  (`riemannHypothesis_iff_twistedPsi_zero_sub`) [L].
- ACG: escape states are spectral measures on G; RH ⇔ every escape state has positive gauge mass;
  power-type energy growth has zero gauge mass (`riemannHypothesis_iff_forall_gaugeMass_pos`,
  `gaugeMass_eq_zero_of_powerGrowth`) [L].
- ACG: ζ is the gauge fixed point; relative tensor powers do not amplify ζ (traps) [L].

## F12. Local types of symmetries at an off-line pair

- ACP: at an off-line pair the local form 2Re(u v̄) has signature (1,1). Hyperbolic (boost
  diag(β, β̄^{−1}), |β| ≠ 1): Hecke operators, archimedean flow, all gauge twists, exactly off the line;
  elliptic (rotation/swap): Hecke on the line, FE; unipotent: the additive successor
  (`mul_conj_eq_zero_of_cyclic_nonneg`, `eq_zero_of_two_prime_symCyclic_nonneg`, `separating_isometry_is_boost`,
  `norm_twisted_heckeSymbol`) [L].
- ACP: boost lemma: positivity of 2Re(u v̄) on a cyclic span under a boost forces u v̄ = 0; two primes force
  blindness; a non-real point resonates (γ log p ∈ πZ) at ≤ 1 prime [L].
- ACP: Weil layers L1 identities, L2 graphs (theorem of the square), L3 budget δ(x,x) fixed along every
  Hecke orbit all exist over Z and hold for the golden datum; sufficiency (positivity of normalized graphs
  of 1 ± T on every span {x,Tx}) is missing (`budget_sufficient_iff_unitary`, `complexFake_budget_insufficient`) [L].
- ACP: kernel counts (eigenvalue paired with its conjugate) vs Rosati trace (paired with its reflection)
  coincide in genus 1 and separate from genus 2; the complex fake (q = 16, roots ±8i, ±2i) has
  nonnegative point and kernel counts and violates Hasse–Weil; kernel counts are blind to complex
  quartets (`detDeg_nonneg_of_im_ne_zero`, `counts_do_not_force_purity`) [L].
- ACP: affine correspondences of Z have genus zero (`fixedPoints_iter_subsingleton`,
  `affine_graphs_meet_at_most_once`) [L].
- ACP: Cramér's constant Σm_ρ²/|ρ|² ≥ 2 + γ − log 4π unconditionally; RH ∧ simple zeros ⇔ Abel slope of the
  prime-error profile → 2 + γ − log 4π (`riemannHypothesis_and_simple_iff_tendsto_abelSlope`); over F_q a
  Mertens budget is purity with simple spectrum, slope = repulsion energy (`curveMertens_budget_iff`) [L].
- ACP: source field at every Ξ zero: the simple Laurent coefficient of (ζ'/ζ)² is the transverse field of
  the other zeros + archimedean term (`EveryXiZeroHasASourceField`) [L].
- ACP: escape-state cofactor Gram is a translation Gram of one log profile with Laplace symbol
  G(s) = ζ(s)(1/ζ(s+ε) − Re(1/ζ(1+ε)))/s; escape rank = number of dominant zeros [L].
- APol: Re W = D − Δ, D = Σm|f̂(ρ)|² collided form (positive, ≍ log-Sobolev norm at every aperture), Δ
  off-line defect; RH ⇔ W = D ⇔ D Hecke-invariant; W has ≤ 2AT₀K/π negative orthonormal directions per
  aperture (`re_W_eq_collided_sub_defect`, `collidedForm_equiv_logSobolev`, `card_negative_orthonormal_le`) [L].
- APol: the only affine maps commuting with s ↦ 1 − s̄ that send an off-line point into its pair are the
  identity and the point reflections σ_γ(s) = 1 + 2iγ − s (FE conjugated by the archimedean flow)
  (`affine_mem_pair_iff`); odd-sector positivity of the σ_γ-twisted form forces an off-line companion at
  aperture ≍ (1/2δ)log log γ; the even sector never forces (`odd_sector_nonneg_forces_offLine_companion`) [L].
- APol: global collision has no analytic carrier (`zeta_global_collision_not_analytic`); couplings
  collide evenly (`couple_detDeg_eq_normSq`) [L].
- APol: lattice zeta of the square: rank-one sublattices see ζ(s₁+s₂), Z² sees ζ(s₁)ζ(s₂); on the
  reflection plane a modulus square |ξ|² (`xi_mul_xi_reflection_plane`) [L].
- APol: the Liouville twin is ζ at height π/log 2 up to archimedean/polar terms on the first-prime window
  (`weilFullFunctional_liouville_eq_twist`) [L].
- AKT depth–length conservation: a k-linear receiver sees depth only through total length
  (`norm_productResponse_le`); the free region ends at the square-root threshold for every product order;
  Künneth positivity is point-count positivity and the golden datum is Künneth-positive
  (`kunneth_positivity_tfae`, `goldenDatum_kunneth_positive_not_pure`) [L].

## F13. Integers over Z are log-torsions; the prime kernel is a torsion energy

- AET: Λ(n) = Σ_{ζ∈O_n} log|1 − ζ| (O_n primitive n-th roots of unity); orbit energies
  J(a,b) = gcd(a,b)·log lcm(a,b); an orbit meets its Hecke translate of degree t in Λ(t) per point; Weil's
  prime kernel is a renormalized positive gcd-twisted torsion energy, the sign lost in the
  renormalization (log 1/(1−r) self-energy) (`orbitIntersection_hecke`, `weilPrimeKernel_renormalized_torsion_energy`) [L].
- AET: RH ⇔ log|Z/lcm(1..N)| = χ(√N·A) + O(√N log²N) (`riemannHypothesis_iff_logTorsion_sub_eulerChar`) [L].
- AET: Tate's limit: approximate doubling → unique homogeneous limit; Rosati positivity at a cycle ⇔
  existence of a naive height there (`orbitHodgeIndex_iff_exists_naiveHeight`); on curve data a naive
  height on Z[F] exists iff unitary; kernel counts never supply one (complex fake) [L].
- AET: theta surface h⁰(a,d) − h^{0∨}(a,−d) = d by Poisson; completing the square gives a nonnegative naive
  height πJ²/t identical on every translate: the polarization is soft; the characteristic-0 fibre is Λ(s)
  (`thetaH0_riemannRoch`, `tateLimit_log_thetaChar`) [L].
- AET: |τ(χ,ψ)|² = |F| by orthogonality: square-root cancellation is a count at every finite level [L].
- AET: odd-degree hyperelliptic curves of every genus over every finite field of odd characteristic are
  unitary by counting (Stepanov + Gauss-sum modulus + descent) (`riemannHypothesis_oddHyperelliptic`) [L].
- AET: Stepanov over Z reaches only the base: lcm(1..n+1)∫₀¹P ∈ Z gives log(1/∫P) ≤ ψ(n+1), Nair
  ψ(2m+1) ≥ m log 4 (`log_inv_integral_le_psi`, `nair_psi_ge`); over F_q it needs Frobenius-flat
  coefficients (x^q = x, Hasse derivatives); over Z no coefficients are flat [L].
- AET: theta h⁰ obeys every linear Riemann law on every surface and the quadratic one on none
  (`thetaEffectivity_not_riemannInequality`) [L].

## F14. Successor gauge connection, chirality, quantized deformations

- BGG: multiplicative operators are unitarily intertwined across the prime gauge torus; real sign gauges
  intertwine product kernels (Euler vacuum ζ vs Liouville vacuum) (`nonneg_realSign_latticeForm_iff`) [L].
- BGG: successor gauge connection A_ω(n) = conj(χ_ω(n))χ_ω(n+1); flatness on [1,N] forces ω(p) = 1 for
  p ≤ N + 1; links A_ω(2), A_ω(3) reconstruct ω(2), ω(3): Catalan {1,2,3,4} is the minimal gauge-fixing
  plaquette (`succConn_flat_iff_primes_eq_one`, `catalan_holonomy_two`) [L].
- BGG: Liouville–Kronecker repulsion (1 + cos(γ log 2)) + (1 + cos(γ log 3)) ≥ (1/50)e^{−|γ|} from 2^a ≠ 3^b
  (no Baker) (`liouville_kronecker_repulsion_ge`); N primes: exp(−c|γ|^{1/(N−1)}) (`multiPrime_repulsion`) [L].
- BGG: at a critical zero the outward splitting W_β = ((s−½)² + β²)/(s−½)² is Bochner-positive and stays
  in the height-coupled class; inward collapse is not Bochner-positive: chiral (`not_forall_coupledRigid`,
  `not_isEvenPosDef_inwardCollapseMultiplier`) [L].
- BGG: central vanishing ceiling ord_{1/2}Λ ≤ ord_{1/2}Λ_γ on the coupled class for all γ implies RH
  (`riemannHypothesis_of_forall_centralVanishingCeiling`); RH ⇔ every positive deformation is trivial or
  strictly lowers the centre (`riemannHypothesis_iff_forall_positiveChiral`) [L].
- BGG: Abel residue quantization: (σ − ½)·Lν(σ) → central drop, an even integer; prime mass added at the
  √x scale comes in even integer units ≤ 2·ord ξ, zero at zero-free ordinates
  (`tendsto_abel_excess_eq_centralDrop`, `tendsto_surplus_residue_eq_centralDrop`) [L].
- BGG: critical conservation: each net created critical zero costs two central orders
  (`centralDrop_ge_two_mul_created_sub_destroyed`) [L].
- BGG: Landau–Wronskian: entire Λ, Λ₀ with Λ₀'/Λ₀ − Λ'/Λ = Lν + E (ν ≥ 0) share their divisor right of the
  abscissa (`landauWronskian_orders_and_anchor`); ζ^d deformations are trivial (`zetaPowDeformation_trivial`) [L].
- BGG: over all pairs [2,X]² the linear archimedean growth is a rank-one polar square vanishing on the
  polar-neutral hyperplane (`reflectedDiag_add_offDiagPolar_eq_neg_levy`); log-cells subdivide log m-shifts
  exactly (Σ_{r<m} w_{am+r} = w_a) [L].
- CDG: Hecke defect D(T_Lf) + D(T_{−L}f) − 2D(f) = Σm(2cosh(2δL) − 2)|f̂(ρ)|² = first source moment
  (`heckeDefect_eq_second_difference`, `xiSourceMoment_one_eq_heckeDefect`); polynomial integer-prefix
  theta sources recover all normalized tests with multiplicities and no critical-line assumption
  (`polynomialThetaSource_uniform_test_aperture_moments`, `tendsto_sourceCurrentReading_heckeDefect`) [L].

## F15. Electrostatics and torsion on the circle

- AES: virial laws on every configuration: Σ m(Re ρ − ½)Re E(ρ) = transverse energy
  (`sum_mul_re_fieldAt_eq_transverseEnergy`); equilibrium (zero transverse field) ⇔ critical on
  reflection-closed configurations (`critical_iff_equilibrium`); reflection-closed transverse energy is 0
  or ≥ 1 (`critical_iff_transverseEnergy_lt_one`) [L].
- AES: RH ⇔ divisor transverse energy < 1 (`riemannHypothesis_iff_divisorTransverseEnergy_lt_one`); finite ⇔
  finitely many off-line zeros; RH ⇔ window energy < 2; RH ⇔ transverse field ≤ 1 at every right zero [L].
- AES: the field at a zero is computed: residue of (F'/F)² and of F''/F at an order-m zero is 2m·R(ρ), R the
  regular part; damped tapered work of the Laurent residues of (ζ'/ζ)² converges to the
  multiplicity-weighted transverse energy (`xiDampedSourceWork_tendsto_energy`) [L].
- AES: energy of an off-line zero is logarithmic: 1 ≤ E(ρ) ≤ 16(C + log(|γ|+4)); the field has no
  unconditional bound [L].
- AES: Λ₂ = μ⋆log² = Λlog + Λ⋆Λ ≥ 0, L(Λ₂) = ζ''/ζ (`selbergSource_nonneg`); circle: I(n,n) = φ(n)log n −
  (φ⋆Λ)(n), the different of Q(ζ_n) per point (`orbitIntersection_self_eq`) [L].
- AES: torsion is the stable equilibrium on the circle: Σ_{i≠j} log|z_i − z_j| ≤ N log N, attained by roots of
  unity (`sum_sum_log_norm_sub_le`); the arithmetic point carries the divergence: I(1,n) = Λ(n), any
  counterterm has c(1) ≥ ΣΛ²/(cφ) (`le_counterterm_one`) [L].
- AES: stability at atomic resolution: below a power of the spacing (w ≤ atomicWidth N = N^{−O(1)})
  arch − prime ≥ 0 on atomic tests; Re W + 2S² ≥ 0; Re W ≥ 0 on nonnegative atomic tests; the stability law
  holds for every sign twin (`markovEnergy_atomicTest_nonneg`, `re_W_add_sinh_sq_nonneg`,
  `twinMarkovEnergy_atomicTest_nonneg`) [L].
- AES: the minimal constant counterterm on orders ≤ N lies in [½log(N/2), 4 log N + O(1)]; the atomic Weil
  prime form has the same sharp two-sided log N + O(1) rate with the pole vector (`torsionCounterterm_rate`) [L].
- AIT: I(n,m) = log#(O_{Q(ζ_n)}/(Φ_m(ζ_n))), Λ(n) = log#(O/(ζ_n − 1)); self-intersection of O_{p^k} =
  log|d_{Q(ζ_{p^k})}| (`log_card_quotient_cyclotomicValue`, `orbitIntersection_self_eq_log_discr`) [L].
- AIT: at Abel radius r < 1 torsion energies are positive; the Hecke map [t] sends r ↦ r^t and moves the
  counterterm by log t; Hecke cocycle β(n,t) = log t − Σ_{p|t,p∤n} log p/(p−1) is not a bounded coboundary
  (`heckeCocycle_eq`, `not_exists_bounded_potential`) [L].
- AIT: local Hodge index: on a p-ladder {cp^j} the finite intersection is the KMS Toeplitz form (q^{|i−j|}),
  q = p^{−1/2}, spectrum in [(1−q)/(1+q), (1+q)/(1−q)]; Weil's prime kernel = Σ_p log p(K_p − 1) ⊗ 1,
  transverse ladders, each bounded, the sum not (`kmsForm_eq_orbit_levels`, `weilPrimeKernel_eq_sum_ladderKernel`,
  `not_exists_primeForm_le`) [L].
- AIT: along the pole direction x_n = n^{−1/2} the prime form is ≍ (log M)² at mass ≍ log M; paying towers
  separately costs √M against log M jointly [L].
- AIT: rotations diagonalize torsion energy on μ_N with eigenvalues the archimedean local factor at rational
  points (Gauss digamma, `gauss_digamma_theorem`); zeros enter only through hyperbolic Hecke maps [L].
- AIT: spacing regulator e^{−ε/n}: positive at every ε, covariant up to tame ramification, indefinite limit
  (`spacingForm_nonneg`, `spacingLimit_transport`) [L].
- AIT: the successor is transverse to every ladder except 1 → 2 (`sameLadder_succ_iff`) [L].
- AIT: positive index of the torsion form on boxes between cN^{1/5}/log N and N^{4/5+ε}; numerically ≈ N^{0.38} [L].
- AIT: "adjunction beats the tower": above the second level of every ladder the renormalized torsion form is
  negative definite (`renormalized_ladder_le`) [L].

## F16. Renormalization, horizon regulator, spacing scale

- RAPT: the horizon (orders ≤ N, Weil's own regulator) has as counterterm the tensor product of the two
  places' counterterms and is Hecke covariant: the anomaly log p of [p] becomes density scaling 1/p and
  cancels (`finitePart_heckeShift`) [L].
- RAPT: covariant scalar counterterm κ_cov(N) = log N − γ + o(1) (`renormalizedPrimeForm_covariant_iff`);
  torsion counterterm φ_golden·log N + O(1), extremal charges φ^{ω(n)}/√n (`torsionCounterterm_golden`) [L].
- RAPT: finite part −2γ on uniform profiles; on p-adic classes −2γ_p·1 + log p(K_{p^{−1/2}} − 1) (the tower
  form); matched operator A_Q = diag(log n) − P_Q + γ_Q·1 has a complete basis with simple energies
  γ + log m + tameDifferent(m) and compact resolvent; the same energies appear in the full prime matrix via
  Ramanujan profiles (`sieveAdjunctionInverse_isCompact`, `eventually_fullPrime_spectral_count_eq`) [L].
- RAPT: limiting pole gap is exactly 2 log 2 (2-adic step) (`exists_poleDefect_ge`) [L].
- RAPT: tower deficit changes sign between 43 and 47; the archimedean valuation potential pays it
  (`towerDeficit_eq_div_sinh`) [L].
- RAPT: polar matching selects the Euler gauge: ζ diverges along the polar direction with coefficient +1,
  Liouville with −1 (`liouville_matching`, `exists_pole_hyperplane_separates_liouville`) [L].
- RBG: survival law: positivity passes a scale limit exactly on the counterterm's null cone; for periodic
  Abel germs the survival cone = module of linear relations among modes; archimedean germ: polar
  hyperplane; torsion germ: {0} (`survivalCone_eq_of_regularized`, `counterterm_rank_dichotomy`) [L].
- RBG: pole-node completion H(x) + H(y) − H(x+y) ≥ 0, H = ψ(1+·) + γ (`harmonicKernel_nonneg`); Ramanujan
  twins' pole-node block carries −φ(m)Λ(t) at orders m, mt, a digamma sum at rational points
  (`ramanujanTwin_carries_primes`, `totient_mul_vonMangoldt_eq_digamma_sum`) [L].
- RBG: lossless amplification E(2^kL) ≥ D·(2cosh(2^kθ) − 2) with loss D independent of k; RH ⇔
  sub-doubly-exponential dyadic growth (`heckeDefect_dyadic_ge`, `riemannHypothesis_iff_dyadic_subexp`) [L].
- RBG: cells satisfy the Baumslag–Solitar relation M_mS = S^mM_m; cell dilation is covariant only at the
  Euler point, pinning primes up to 2X + 1 on [1,X] (`cellDilate_two_covariant_on_horizon_iff`) [L].
- RBG: gauge blindness = square class (`realSignBlind_iff_isSquare`); successor couplings are never square
  class (`successor_coupling_charged`) [L].
- RBG: RH ⇔ no right terminal; terminal ceiling at depth a ⇔ strip of width a
  (`riemannHypothesis_iff_no_right_terminal`, `zeroFreeStrip_iff_terminal_ceiling`) [L].
- SSHA: the spacing scale δ_N = log(1 + 1/N) is the Nyquist scale of the atomic family (zero density log T/2π
  vs Dirichlet polynomial Nyquist density log N/2π match at T ≍ N) [L].
- SSHA: Weil's form is nonnegative up to the pole on atomic tests of width c₀δ_N for every N, universally over
  real twists |ω| ≤ 1 (`re_W_add_sinh_sq_nonneg_spacing`, `twistedMarkov_atomicTest_nonneg_spacing_of_abs_le`);
  without the pole the Markov form fails at every width cδ_N, c > e/(2π) (`archRobinConstant_eq`) [L].
- SSHA: the tilt r(n) = 1 + n/N gives P_N(x) ≤ Σ x_m²(log N + C − (m/4N)log m); power weights cannot
  (`atomicWeilForm_le_tilted`) [L].
- SSHA diamagnetic inequality: Lévy energy is a Dirichlet form, so ζ is the ground state of its gauge orbit
  (`diamagnetic_inequality`); the gauge defect lives only on non-ratio lags [L].
- SSHA: once overlap beats (log log N)^{1+ε} narrow atoms synthesize every fixed test and positivity is RH;
  negative index counts right zeros (`riemannHypothesis_iff_atomicFamilies_nonneg`,
  `riemannHypothesis_iff_splineAtomic_negIndex_eq_zero_of_width`); the universal threshold over sign twists
  is finite (`universalThreshold_finite`) [L].

## F17. Signature certificates (Lorentzian / Metzler)

- ALG: over F_q, Bézout makes the Frobenius Gram Metzler, Frobenius acts conformally with factor q, Hodge
  index = trickle-down on one Frobenius ladder; trickle-down on every ladder ⇔ |β_i| = 1 ⇔ one-sided
  square-root count; hyperelliptic curves satisfy it via Stepanov; golden datum is Metzler, connected and
  violates (TD_π) (`forall_weightedTrickleDown_iff_exists_pointCount_ge`, `hyperelliptic_weightedTrickleDown`) [L].
- ALG: below the spacing the atomic Gram of H, V, g₁..g_N is Metzler and connected; Weil positivity ⇔
  weighted trickle-down (`weilQuad_finAtomicTest_nonneg_iff_weightedTrickleDown`); Metzler threshold of the
  overlap ratio is exactly K = 1 (odd triangle frustrates every unimodular gauge beyond) (`metzlerThreshold_overlapRatio`);
  a twin flipping a prime ≤ N has no Metzler gauge below the spacing [L].
- ALG: Hecke dilations are boosts with factor one (isometries); decaying isometric ladders carry no positive
  square; conformal ladders carry it iff normalized couplings do not decay; along p-ladders the prime
  pairing grows like w p^{k/2} (candidate conformal weight) (`forall_isHyperbolic_conformalLadder_iff`) [L].
- ALG: a local factor is Lorentzian only at the Weil bound, never at a prime (`ramanujan_lorentzian_rigid`,
  `not_isLorentzianPoly_at_prime`); Euler products of Lorentzian local factors are Lorentzian, blind to the
  Euler point [L].
- ALG: Cayley points w_ρ = 1 − 1/ρ; FE is the reflection w ↦ 1/w̄; RH ⇔ reflection positivity ⇔ Metzler sign
  of the Li ladder (`RHIsReflectionPositivityOfTheCayleyLadder`) [L].
- ALG open problem: a conformal correspondence with λ ≠ 1, or a source-built reflection-positive functional
  whose Cayley ladder is the Li ladder (candidate: KMS states of N ⋊ N^×, reflection β ↦ 3 − β) (README) [L].
- IGP: the cosine Gabor kernel's zeros are non-lattice (sumset disjointness on [0,3]) and force
  macroscopic off-diagonal Frobenius energy among simple critical zeros: simple critical proportion
  ≥ H_D(1) + 10^{−8} (`simple_critical_proportion_ge_67250071`); boxcar windows admit lattice orthogonality [L].
- AID: index ≤ distinct transverse energy; damped source work detects every amount below a finite negative
  index; bounded work ⇔ finite off-line support ⇔ uniformly bounded spline indices; a new off-line zero in a
  doubled annulus forces an increment ≥ 21/100 (`TheIndexIsPaidByTransverseEnergy`,
  `TheWorkAndIndexHaveTheSameFiniteStratum`) [L].
- AID: R²(W(2R) − W(R)) is monotone, converges to a height-square energy and classifies off-line support
  (zero/finite/infinite); index cost is quadratic ≥ 50k² − 3k/2 (`TheCriticalRateClassifiesAllOffLineSupport`,
  `TheSourceBudgetMakesTheIndexCostQuadratic`) [L].
- AID: Gamma boundary operator has exact Schur weight with norm exactly π/2, no maximizer
  (`GammaBoundaryHasAnExactSchurWeight`) [L].
- AID: every prime-power exponent ≥ 2 (squares, odd higher powers, every finite Euler collection) is
  Gamma-small with uniform finite index; the open part is the first-prime source (exponent one), coarse
  archimedean mass and first-prime mixing (`AllHigherPrimePowerMixedFormsHaveUniformFiniteIndex`,
  `FiniteEulerMixedFormsHaveUniformFiniteIndex`, `TheEntireSquareSourceSharesTheFullDetailReserve`) [L].
- AID: |primeSum(f) − P(f)| ≤ εe^R(Γ(f) + ∫f²) for large R, all BV profiles in [−R,R], all prime powers and
  both poles retained (`exists_primePolar_gamma_bound_bv`) [L].

## F18. ζ is extremal: the Weil cone is at most one point

- SMAP (citing RHTower): Weil cone uniqueness: the full Weil cone (weights making the complete form
  positive with ζ's Gamma and pole) is {Λ} under RH, empty otherwise; on atomic families at any root of
  finite overlap order positivity of a bounded weight is RH and forces the weight to be Λ
  (`atomicPositiveAt_iff`, `riemannHypothesis_of_atomicPositiveAt`) [L].
- SMAP: on atomic tests the continuous pole moment ∫f e^{−u/2} is a multiple of Σx_n/√n; on that hyperplane
  the pole term vanishes and twins differ only in the prime form
  (`integral_atomicTest_mul_exp_neg_half`, `weilQuadTw_atomicTest_sub_weilQuad`) [L].
- SMAP: the selective hyperplane gap is exactly 2 log 2, maximal among sign gauges, Liouville's gap is 0
  (`isGreatest_zeta_hyperplaneGap`, `isGreatest_signGauge_hyperplaneGap`, `not_liouville_hasHyperplaneGap`);
  bottleneck log m + τ(m) ≥ 2 log 2 with equality only at m = 2 [L].
- SMAP: harmonic correlation decides the margin: Σ_{n≤N} ω(n)/n = o(√log N) ⇒ margin 0; full harmonic-density
  agreement ⇒ full 2 log 2 (`not_hasHyperplaneGap_of_harmonicSum_small`, `hasHyperplaneGap_two_mul_log_two_of_correlation`) [L].
- SMAP: doubled cell C_{2a} + C_{2a+1} = T_{log 2}C_a: the complete source is a sum over levels of translates
  of one generator; off the pole hyperplane pole couplings grow like 2^{|k−j|/2} and form one hyperbolic
  plane; on it the entire arithmetic content is the signed Chebyshev error along the dyadic orbit [L].
- SMAP dyadic sign rigidity: two weights both dyadic-positive along a generator have the dyadic prime mass of
  their difference bounded by the two diagonals at every lag (`primeMass_add_le_of_dyadicPositive`,
  `not_dyadicPositive_and_of_unbounded`) [L].
- SMAP traps: ζ is the hardest member, not the most positive; ζ is the minimum of its gauge orbit only on
  nonnegative atomic tests [L].
- SAHT: one Gamma reserve pays all dyadic parent variances; dyadic clock W₂e_a = α_ae_{2a} + β_ae_{2a+1} is a
  pure isometry whose wandering details are the balanced Haar sources
  (`TheLogCellClockHasACompleteWanderingDecomposition`, `OneGammaReservePaysAllDyadicParentVariances`) [L].
- SAHT: the coefficient tail from exponent r+1 is summable exactly when r ≥ 2: Σ_p 2log p/√p and Σ_p 2log p/p
  diverge; all higher powers (k ≥ 3) have finite mass H and one Gamma reserve
  (`CriticalEulerCoefficientMassStartsAtCubes`, `AllHigherPrimePowersHaveAllLevelGeneratorApproximation`) [L].
- SAHT: canonical critical energy E_crit = lim R²(W(2R) − W(R)); finiteness ⇔ finite off-line support;
  E_crit ≤ 1294047/2000 ⇔ RH (README) [L].

## F19. Additive characters diagonalize the multiplicative prime operator

- RAPT/ACountP: for log N·I − P_N (P_N(m,n) = Λ(n/m)(n/m)^{−1/2} on [1,N]) the eventual eigenlines are
  Ramanujan profiles v_m(n) = c_m(n)/√(φ(m)n) with simple limiting energies E_m = γ + log m +
  tameDifferent(m); exact counts with multiplicity hold eventually at regular thresholds
  (`eventually_fullPrime_spectral_count_eq`, `exists_simple_fullPrime_eigenline`) [L].
- ACountP: prime parity ω_p(n) = (−1)^{v_p(n)}: exact pairing p(H_N − S_N) = H_{⌊N/p⌋} + S_{⌊N/p⌋}; harmonic
  correlation → (p−1)/(p+1); gap 2log2·((p−1)/(p+1))² (`prime_parity_pairing`, `primeFlip_hasHyperplaneGap`) [L].
- ACountP: every prime p ≥ 11 gives a completely multiplicative, polar-matched sign twin with the maximal
  hyperplane gap 2 log 2 and a negative complete Weil test: the maximal gap does not select the source;
  maximal gap ⇔ p ≥ 11 (`maximal_gap_does_not_select_the_source`, `primeFlip_hasHyperplaneGap_two_mul_log_two_iff`) [L].
- ACountP: full-cone uniqueness kills every flip: a full-Weil-positive weight equals Λ on n ≥ 2
  (`primeFlip_exists_negative_complete_test`, `near_maximal_gaps_do_not_force_weil_positivity`) [L].
- ACountP: the counted Ramanujan tower of ω_p has coefficients a₀ = c_p, a_k = 2c_p(−1)^k/√φ(p^k), squared sum
  one; the secular series Σ a_k²/(D_k − s) has a unique root α_p in (0, D₁); greatest gap δ_p = min(2 log 2, α_p)
  (`primeFlip_hasHyperplaneGap_min_secularRoot`) [L].
- ACountP: for any finite prime set F, b_F = μ⋆ω_F has b_F(p^k) = 2(−1)^k on F; Σ_m a_F(m)² = 1 because the local
  factors 1 + 4p/(p−1)² = (p+1)²/(p−1)² are cancelled by c_F² (`hasSum_finiteFlipConductorCoefficient_sq`);
  every prime pattern has an exact Euler-product harmonic mean c = inf_Q Π(p−1)/(p+1)
  (`primeSetFlip_harmonicCorrelation_tendsto`); zero density ⇔ escape from every bounded energy window
  (`primeSet_bounded_spectral_mass_vanishes_iff`) [L].
- ACountP: flipping all primes ≤ Q agrees with Liouville below Q; each finite stage has a positive gap, no
  uniform gap over cutoffs (`finitePrimeExhaustion_no_uniform_positive_gap`); joint gaps of primes in (B,Q]
  decay ≤ (64/3)D_B²/(log Q)³ though each constituent flip is maximal
  (`eventually_primeTailGreatestGap_le_inverse_log_cube`) [L].
- ACountP: one fixed dyadic probe selects the trivial sign among finite prime flips
  (`finiteFlip_two_gap_selection`), with no fixed positive tolerance (`exists_maximal_flip_with_almost_unchanged_dyadic_gap`) [L].

## F20. Krein–Langer structure of the Weil kernel on Q_{>0}

- HKT: Hecke orbit kernel K_g(u) = W(g, τ_{log u}g) = Σ_ρ ω_ρ(g)u^{ρ−1/2}; on-line zeros are unitary characters
  (points (p^{iγ})_p of the prime torus) with weight |ĝ(γ)|² ≥ 0; each off-line pair is a hyperbolic plane [L].
- HKT index formula: κ(p + Σ_J h_{χ_j,ω_j}) ≤ |J| for every PD p, equality under separation; finite
  exponential sums: index = #negative unitary weights + #reflected pairs (`negIndex_expSum`); absolutely
  convergent Bohr series: index = #negative coefficients (`negIndex_bohrSum`) [L].
- HKT: "a positive part never pays a pair": every separated pair survives any PD addition (growth beats
  boundedness) (`negIndex_add_pairKernel_eq_one`) [L].
- HKT: bounded index is closed under pointwise convergence of kernels (`negIndex_le_of_tendsto`); Weil's form is
  not L²-continuous [L].
- HKT aliasing: two right zeros alias on ⟨p⟩ iff same real part and ordinates differing by 2πZ/log p; on
  ⟨p,q⟩ iff equal; ≤ κ(κ−1)/2 primes are blind; positivity on infinitely many prime towers forces index zero
  for the arithmetic class (`negIndex_eq_zero_of_posDef_on_infinitely_many_towers`), while a kernel on Z²
  positive on both axes can fail on the diagonal (`locality_fails`) [L].
- HKT: golden datum has index one on its own tower but infinite index on the Hecke lattice, already on two
  primes: its periodic zeros alias only at its own characteristic (`golden_tower_vs_lattice`,
  `negIndex_orbitKernel_golden_twoPrime`) [L].
- HKT: κ(K_ζ) = #right zeros, even; RH ⇔ κ ≤ 1 (`negIndex_zetaKernel_eq_two_mul`); finite index ⇔ finite
  off-line support ⇔ bounded heat counts ⇔ critical above some height (`zetaZeroKernel_finiteIndex_tfae` /
  `zetaKernel_finiteIndex_tfae`); finite index ⇒ LH and a zero-free strip (`lindelof_of_negIndex_zetaKernel_lt_top`) [L].
- HKT: index is energy: m negative squares force E_crit ≥ 50m² − 3m/2; κ² ≤ 2E_crit/97 [L].
- HKT: over F_q and over Z, index zero ⇔ the one-sided square-root count
  (`negIndex_traceKernel_eq_zero_iff_count`, `negIndex_zetaKernel_eq_zero_iff_count`, `global_law_count`) [L].
- HKT Stepanov compressions: compressing by P = Σp_α δ_{y_α} multiplies a pair's weight by P̂(χ)·conj P̂(χ†);
  the compression is PD iff P̂ annihilates one character of every pair; on Q_{>0} P̂ is a Dirichlet polynomial
  (`negIndex_compress_eq_zero_iff`, `hat_logChar`) [L].
- HKT: precision rigidity: tower kernels of Λ and Λ + εn^{−η} (η < ½), and of Λ and λΛ, are never both of index
  zero along a nonnegative generator (`not_negIndex_towerKernel_and_perturbed`,
  `not_negIndex_towerKernel_liouville_and_vonMangoldt`); every weight ≠ Λ has a negative square on every prime
  tower (`exists_negIndex_towerKernel_ne_zero`) [L].
- HKT: the pole on a tower is one hyperbolic plane h_{w,(A+B̄)/2}, w = e^{ℓ/2}; tower index and Arch − Prime
  index differ by ≤ 1 (`negIndex_towerKernel_le_archPrime_add_one`) [L].
- HKT index-one window: atomic kernel Dδ₁ − P on {1..N}, L = log N − γ: index 0 above L, exactly 1 on
  [L − 2log2, L) carried by the pole, ≥ 2 below; every adjunction energy is a rung; index is twin-blind
  (congruence), the carrier is not: ζ's first square lies on the pole, Liouville's never below L
  (`eventually_hermNegIndex_atom_eq_one`, `hermNegIndex_gaugeAtom_eq`, `eventually_exists_neg_on_pole_liouville`);
  at every fixed counterterm the atomic kernel has infinite index on Γ (`negIndex_atomKernel_eq_top`) [L].
- HKT: compactly supported Gevrey profiles exist exactly for s > 1; atomic receivers decide RH at width
  (log log N)^α/N for every α > 1 (`atomicReceivers_quasiAnalytic_boundary`) [L].
- HKT open: the covariant converse Krein–Langer theorem on Γ needs a common invariant κ-dimensional negative
  subspace for all prime translations of the Pontryagin space (README §9.1) [L].
- HKT coalescence law: a pair u^{t+iγ} with weight ω has one square for t ≠ 0 and loses it at t → 0 iff
  Re ω ≥ 0 (`coalescence_law`); damping by r unitary characters multiplies index by ≤ r, attained
  (`negIndex_mul_sum_le`, `negIndex_damped_pair_eq_two`) [L].

## F21. Local-to-global for the index (AKLT)

- AKLT: each local kernel L_p(n) = log p·p^{−|n|/2} is a Poisson kernel, positive definite with all unitary
  twins (`isPosDefKernel_poissonKernel`, `isPosDefKernel_eulerKernel`, `isPosDefKernel_twist`); the
  constituent log p·δ₀ − L_p is not [L].
- AKLT zero-or-infinity: an axis-supported kernel on Z^S, |S| ≥ 2, has index 0 or ∞; Σ_s a_s(δ₀ − L_s) has
  infinite index; no finite set of places carries a finite nonzero index (`negIndex_eq_zero_or_top_of_isAxisSupported`,
  `negIndex_localAssembly_eq_top`); with one tower the law fails (`rankOne_axis_pair`) as over F_q [L].
- AKLT: index = least number of exceptional waves of a bounded count along a separating tower; minimal counts
  are rigid (waves = outer nodes with the pair weights) (`negIndex_eq_card_waves`, `minimal_waves_eq_outerNodes`) [L].
- AKLT fine towers: the consecutive-integer ratio towers ⟨(n+2)/(n+1)⟩ decide every orbit kernel and carry its
  whole index; RH ⇔ positivity of the Weil kernel on them (`riemannHypothesis_iff_zetaKernel_consecutive`,
  `negIndex_zetaKernel_eq_iSup_consecutive`); prime towers are coarse grids and alias [L].
- AKLT: an attained largest depth is seen by all but finitely many prime towers; RH ⇔ positivity on infinitely
  many prime towers whenever the least real part is attained (`riemannHypothesis_iff_infinite_primes_posDef_of_attained`) [L].
- AKLT parity form: parity classes {λ = ±1}; RH ⇔ upper counts for both; one class suffices: RH ⇔ the odd class
  upper count ⇔ κ(K_ζ) = 0 (`riemannHypothesis_iff_oddClass_upper`, `negIndex_zetaKernel_eq_zero_iff_oddClass_upper`).
  Over F_q one twist does not complete (eigenvalues ±2, ±½: `one_twist_does_not_complete`); the twist tower of
  2-power base changes does (`unitary_iff_twistTower_upper`); Stepanov bounds both Legendre parity classes by
  q/2 + (deg h + 1)√q (`stepanov_parity_classes_upper`) [L].
- AKLT: compressions are receivers: Frobenius char poly annihilates the trace kernel (`compress_traceKernel_charPoly`);
  over Z Euler-factor compressions keep the index (`negIndex_compress_euler`): a producer must vanish at the primes
  (point side), as Stepanov's polynomial vanishes at rational points [L].
- AKLT Bézout ledger: Σ m_x ≤ deg P over F_q[X], Σ m_p log p ≤ log A over Z (`sum_le_natDegree_of_vanishing`,
  `sum_mul_log_le_log_of_dvd`); Stepanov gets multiplicity ≈ √q from x^q = x; p^m | C(N,k) forces p^m ≤ N, so
  binomial auxiliaries vanish simply above √N (`le_one_of_dvd_choose`); divisibility is parity-blind
  (`abs_log_lcm_oddPoints_sub_theta_le`); Chebyshev's ratio gives ψ(x) ≥ 0.89x − O(log x) (`psi_ge_of_chebyshev`) [L].
- AKLT: over F_q the vertical shift by π/log q is (−1)^deg at every place; over Z every vertical shift is −1 at
  most at one prime (unique factorization) (`shiftChar_eq_neg_one_subsingleton`); the Liouville twin is a
  pointwise limit of shifts (Kronecker) (`exists_shifts_tendsto_liouville`) [L].
- AKLT: pointwise-closed statements on the weights that hold for every vertical shift hold for every unitary
  completely multiplicative twist; Weil positivity is pointwise-closed, so its selectivity lives in the pole
  and the Gamma factor (`liouvilleTwin_mem_of_isClosed`, `flip_mem_of_isClosed`) [L].
- AKLT structure ladder: sign excludes Liouville and flips; support (Euler product) excludes Λ + εn^{−η} and
  Davenport–Heilbronn; normalization excludes cΛ; only the ring level (gcd(n,n+1) = 1, the curve's equation)
  excludes over-regular Beurling systems and the golden datum (README §4.17) [L].
- AKLT: over F_q[T] the pole vector is an exact eigenvector of the prime kernel with eigenvalue N log q
  (Σ_{d|j} dπ_q(d) = q^j); D·1 − P_N ≥ 0 ⇔ D ≥ N log q (`atomFq_nonneg_iff`); Euler's γ in the Z ceiling
  log N − γ is the archimedean defect of Mertens' theorem [L].
- AKLT polar index formula: the index of a curve datum's trace kernel = number of pole classes of the continued
  affine A₁ Weyl sum right of Re s = −½ (`negIndex_traceKernel_eq_card_rightPoles`); over Z confinement is RH
  (`RHTower.InfiniteSymmetry`) [L].

## F22. Precision is lost in extraction, not absent from Z (ASRP)

- ASRP: identities have precision class {0}: Σ_d Λ(d)⌊n/d⌋ = log n! determines Λ; ψ(n) = Σ_k μ(k) log⌊n/k⌋!
  (`psi_eq_sum_moebius_log_factorial`, `eq_of_chebyshevTransform_eq`); the inversion operator sends some E with
  |E(y)| ≤ y^θ to ≥ π(x) (`not_inversion_bounded`); monotone errors invert at exactly Mertens precision;
  RH ⇔ monotone errors bounded by 1 invert to O(x^{1/2+δ}) (`riemannHypothesis_iff_monotone_inversion`) [L].
- ASRP Stirling split: |ψ(n) − I_n(F) − I_n(h)| ≤ 3(1 + ½log n)max|M(k)|; the smooth term inverts exactly to the
  Möbius moments, the sawtooth to < n (`abs_psi_sub_moments_sub_sawtooth_le`) [L].
- ASRP integrality lattice: {∫₀¹P : P ∈ Z[x], deg ≤ n} = d_{n+1}^{−1}Z (Bézout over the horizon); least positive
  Nair integral 1/d_{n+1}, ψ(n+1) = max_P log(1/∫P) (`nairLattice_eq`, `isLeast_positive_nairIntegral`) [L].
- ASRP: the integrality exponent is the zero width: Siegel half (small positive integrals exist at scale
  e^{−(n+1)+Cφ}) and Liouville half both hold at x^θ for θ > Θ and fail for θ < Θ; square-root integrality in
  either half is RH (`siegelExponent_eq_zeroReSup`, `riemannHypothesis_iff_siegelHalf_sqrtScale`) [L].
- ASRP: each half of the count alone is RH (`upperCount_vonMangoldt_iff`, `lowerCount_vonMangoldt_iff`);
  precision exponent of Λ = Θ; stabilizer of the count = square-root class Q; εn^{−η} ∈ Q ⇔ η ≥ ½ [L].
- ASRP: twin's reciprocal torsion: Σ_{m≤n} λΛ(m) = 2ψ(⌊√n⌋) − ψ(n), so e^{A_λ(n)} = 1/r_n with
  r_n = d_n/d_{⌊√n⌋}² ∈ N (`exp_partialSum_liouvilleWeight`) [L].
- ASRP: integer Dirichlet polynomials: d_N^m D(m) ∈ Z, so integrality speaks at s ∈ Z (sharp on the pole side),
  not at nontrivial zeros; a nonzero D has fewer real zeros than nonzero coefficients
  (`card_lt_of_intDirichlet_eq_zero`) [L].
- ASRP: sup-norm ceilings force vanishing: b^nP(a/b) ∈ Z, so sup_{[0,1]}|P| < b^{−n} forces P(a/b) = 0; every
  sup-norm certificate at precision θ < 1 vanishes at 0, ½, 1 (`eventually_vanish_of_supCeiling`) [L].
- ASRP: two prime towers certify every ordinate difference Δ with margin c·min(|Δ|,(2+|Δ|)^{−C}) by Baker;
  integrality alone gives e^{−O(|Δ|)} (`exists_baker_separation`, `two_prime_alias_bound_in_Δ`) [L].
- ASRP: tower positivity is precision-exact (stabilizer {0}): Λ + δ tower positive ⇔ RH ∧ δ = 0 on n ≥ 2
  (`towerIndexZero_add_iff`); aperture-A positivity is window-determined and weight-blind below log 2/2 [L].
- ASRP: the successor enters only modulo Q: the count for a is a − 1 ∈ Q (`count_iff_sub_one_mem_sqrtClass`,
  `riemannHypothesis_iff_vonMangoldt_sub_one_mem_sqrtClass`); integer-count precision cannot decide [L].
- ASRP calibration: over F_q precision exponent ½ + max log|β|/log q; the golden datum has exponent
  ½ + log φ/log 5 and satisfies the upper half N_k ≤ q^k + 1 (`golden_upperCount_and_not_lowerCount`) [L].

## F23. Cyclotomic integrality inside the complete Weil matrix (CACT)

- CACT: primitive-root prefix energy P_m(k) = Σ_{ζ prim. order m}|Σ_{j<k}ζ^j|² = Σ_{d|m} μ(m/d)(k mod d)(d − k mod d);
  vanishes iff m | k; otherwise the prefix is a nonzero cyclotomic integer, its norm has |·| ≥ 1, and AM–GM over
  the embeddings gives P_m(k) ≥ φ(m); interpolation: A_m(t)/φ(m) ≥ {t}(1−{t}) for m > 1
  (`PrimitiveRootPrefixEnergyIsAMobiusQuadraticRemainder`, `CyclotomicNormGivesAConductorUniformCurvatureFloor`) [L].
- CACT: Σ_{a|n} Λ(a)c_m(n/a) = log n·c_m(n) − J_m(n), J_m(n) = Σ_{d|m, d|n} μ(m/d)d log d; at n = m:
  Σ_{d|m} μ(m/d)d log d = φ(m)(log m + tameDifferent(m)) — the source of the conductor energies
  (`TheDownwardPrimeRowIsAnExactLogarithmicDivisorJet`) [L].
- CACT: Σ_{(r,q)=1} c_q(rn+h) = c_q(n)c_q(h): Ramanujan modes are eigenfunctions of affine unit averaging with
  eigenvalue c_q(h)/φ(q) (`UnitAveragesDiagonalizeSuccessorCorrections`); actual prime windows realize the average:
  lim Σ_{AN<k≤BN} Λ(k)/k·c_q(kn+h) = (log B − log A)c_q(n)c_q(h)/φ(q)
  (`ActualPrimeWindowsDiagonalizeAffineRamanujanModes`) [L].
- CACT: every eigenvalue of the normalized complete Weil matrix ≥ b for all 0 < c ≤ 1 with one smooth plateau
  and one horizon, any b < 2 − log(2π) (`OneHorizonMakesTheCompleteWeilMatrixPositiveThroughTouching`) [L].
- CACT: at touching only the boundary star N, N+1 carries non-ratio prime lags
  (`OnlyTheBoundaryStarEntersAtTouching`) [L].
- CACT: growing Ramanujan families: (log(N+1) − log(K+1))·Σa_m² ≤ Σ_{n≤N}F_a(n)², K = Q(Q−1), via resolution into
  primitive roots and the large sieve (`GrowingRamanujanFamiliesHaveASquareRootHorizon`); on annuli (A,2A] with
  A ≥ 4Q(Q−1) two-sided frames ¼ ≤ · ≤ 5/4; the prime kernel compressed to a dyadic annulus is zero (no divisibility
  inside (A,2A]) (`AnnularRamanujanFamiliesHaveTwoSidedFrames`) [L].
- CACT: completed source work 0 ≤ W(R) ≤ 64R L_R(L_R+1) (`xiDampedSourceWork_le_logarithmic_ceiling`); every
  off-line quartet forces W(2|γ|) − W(|γ|) > 39/50 (AID) [L].

## F24. Crossing the Metzler wall; zero density is indispensable

- TMWP: complete Weil positivity crosses the Metzler wall c = 1: completeWeilMatrix φ₀ c N eventually PD on
  (0, c₀], c₀ = 1 + 10^{−18}, φ₀ = plateau(1/1000), while no unimodular gauge makes the atomic Markov form Metzler
  (`exists_gt_one_eventually_completeWeilMatrix_posDef`, `eventually_transMetzler_atomSpacing_posDef_and_frustrated`);
  mechanism: convex combination of Ramanujan norm-quasimode spectral exclusion and strict-variance prime-defect
  coercivity paying successor pairs (kn, kn ± 1) in the top third [L].
- TMWP: the Liouville twin fails inside the separated regime above the Robin–Euler ratio
  c_RE(φ) = e^{β(φ)/‖φ‖²}/(2π) < ½ (→ e/(2π) on thin plateaus) (`eventually_liouville_weilQuadTw_neg_of_gt_robinEuler`) [L].
- TMWP: the tempered configuration `isolatedPairConfig` (one off-line pair, vertical period 2π/log 2) fails at every
  c > 0 with x₁ = 1, x₂ = −1: fixed-c positivity is not a zero-side deduction; ζ's growing (log T)/2π density is
  indispensable (`isolatedPairConfig_atomic_negative_every_ratio`) [L].
- TMWP: under finite off-line support the atomic negative index is ≤ #right zeros uniformly in c > 0, N
  (`hermNegIndex_atomicShiftWeilGram_le_of_finiteOffLine`) [L].
- TMWP: one fixed Steklov Denjoy–Carleman profile makes RH equivalent to eventual atomic positivity at
  c_N = (log log N)(log log log N)^β, β > 2 (`riemannHypothesis_iff_steklovDCProfile_nonneg_superGevrey`) [L].
- RAPT (via AHA): single-prime flip thresholds: flipped form eventually positive when max(c,1)^8 log p ≤ κ√p, negative
  on the prime-square trial when c ≥ K and c^7 ≥ Kp (`TheFlipThresholdGrowsLikeAPowerOfThePrime`) [L].
- AHA: |χ_x(n) − 1| ≤ 2k·D_N(x) for n ≤ min(N, 2^k), D_N the max successor defect; D_N(x) = 0 ⇔ χ_x(p) = 1 for all
  p ≤ N (`DyadicSuccessorRigidity`) [L].
- AHA: an auxiliary with full multiplicity r on the order-(d+1) Adams fixed locus needs integer support 2^{dr},
  attained by (z₂^d − 1)^r (`AdamsMultiplicityResolution`, `TorsionMultiplicityBoundary`) [L].
- AHA: at an algebraic torus point, vanishing of the first vertical jet ⇔ all prime partials vanish (Baker)
  (`AlgebraicVerticalFirstJets`); fixed-degree homogeneous families in log p, log q are independent over Q̄
  (Gelfond–Schneider) (`TwoPrimeHomogeneousLogRigidity`) [L].

## F25. Same-point vs reflection-paired; shells

- HEF calibration rigidity: an entire weight h with h = |F|² on R equals F·F^# (`eq_weilWeight_of_calibrated`);
  every line-calibrated explicit statistic is the Weil form; at a pair {z, z̄} it misses the same-point value by
  |F(z) − F(z̄)|² (`samePoint_sub_explicit_pair`); correct on every pair forces F constant
  (`const_of_explicit_eq_samePoint_everywhere`) [L].
- HEF: holomorphic clocks e^{λ(s−½)} have Cesàro excess 0 or ∞ (`cesaroBounded_holomorphicClock_iff`); the
  ordinate clock c(s)c(1−s̄) = e^{2iλ Im s} is unimodular (antiholomorphic in one factor) and reads the collision
  charge O at non-resonant frequencies (`tendsto_cesaro_ordinateClock_sub_diag_of_nonResonant`) [L].
- HEF: O ∈ 2N, O = 0 ⇔ critical, N ≤ N₀ + O (`even_collisionCharge`, `total_le_lineMass_add_collisionCharge`);
  over F_q unitary ⇔ charge 0 ⇔ charge < 2; golden datum has charge exactly 2; every circle-calibrated
  explicit formula is the Rosati pairing (`unitary_tfae`, `goldenDatum_curveCollisionCharge`,
  `explicit_eq_rosatiPairing`) [L].
- HEF resolvent: (σ−½)S(s) = E(s) + D(s), D ≥ 0, D = 0 ⇔ critical; ∫D dt = πΣ m d²/(u² − d²) = πΣ M_{2k}u^{−2k}
  (`sub_mul_samePointResolvent_eq`, `integral_resolventDefect_vertical`); same-point positivity ⇔ effectivity, a pole
  makes the form indefinite (`signedSamePointForm_nonneg_iff`, `exists_signedSamePointForm_neg`) [L].
- SSh: on a conductor-m mode a shell of shift h acts by c_m(h) (average of c_m(ℓ)c_m(ℓ+h)); Möbius collapse
  c_m(h) = Σ_{d|(m,h)} μ(m/d)d + Poisson on each dZ turn the shell symbol into the coprimality indicator:
  E_m(c) = (2/(Mφ(m)))Σ_{(a,m)=1}(m/a)∫_{ac/m}^∞ |φ̂(2πt)|² ≥ 0 (`hasSum_completedConductorEnergy`) [L].
- SSh: the continuum average of the shells is exactly the pole charge cq; only the lattice part repays log c;
  without the shells every nonpolar reference energy is negative past touching
  (`exists_overlap_all_nonpolar_reference_energies_negative`) [L].
- SSh: ground-state transform P_N + D = Σ(A(⌊N/n⌋) + log n)x_n², D = Σ_{mt≤N} Λ(t)(x_{mt} − x_m/√t)², the
  Dirichlet energy of the pole relation (`atomicWeilForm_add_poleDefect`) [L].
- SSh: the reserve W ≥ (δ/4)D − C(c)‖x‖² with δ ∝ c^{−7}, C ∝ c^9; negative vectors have D ≤ C'c^{16}
  (`tiltedUnitSpline_complete_defect_reserve_explicit`, `exists_negative_completeWeil_poleDefect_polynomial_bound`);
  defect-only capture is exponential (`not_eventually_defect_coordinate_capture_below_binary_cutoff`) [L].

## F26. Realizations and amplifiers (ART)

- ART: commutative realization (one loop of length log p per prime) has zeta ζ; its transfer operator is diagonal
  with eigenvalues p^{−s}, spectral radius 2^{−σ} < 1, trace norm P(σ) finite exactly for σ > 1: the pole of ζ is a
  nuclearity pole, not a Perron–Frobenius crossing [L].
- ART: free realization (one vertex, a loop per prime) is mixing with zeta 1/(1 − P(s)), spectral pole at a unique
  σ* ∈ (1,2): wrong entropy [L].
- ART: unique factorization forbids additive concatenation: every additive realization of the primes is
  commutative (two first-return loops would concatenate to log(pq)) [L].
- ART: finite even realizations Z = 1/det(I − M(s)) have no zeros; zeros need an odd part; over F_q the odd part is
  H¹ [L].
- ART: integrality forbids super-conformal roofs (Pisot: integers p_{n+1} − p·p_n → 0 force composites); primes obey
  no eventual affine recurrence (Cunningham) [L].
- ART: a realization by a Hölder suspension of a mixing finite-type subshift gives a zero-free strip (Pollicott);
  oscillation fails on additive and free realizations (Dolgopyat modulus 1 at the abscissa, Kronecker density) [L].
- ART rank law: a Brauer family at level k on r phases has ≥ C(r+k−1,k) members and never beats the trivial bound;
  loss → 1 exactly at finite rank; over Z the rank at scale x is π(x) [L].
- ART: open "Mills boundary": does a prime sequence p_n = Cp^n + O(1) exist (needed along every cycle family of a
  Hölder finite-type realization) [L].

## F27. Bézout and Riemann–Roch of G_m(Q); the twist tower collapses (EAHT)

- EAHT Bézout of G_m(Q): points are the Frobenius progressions s_j = 2πij/log p (zeros of 1 − p^{−s}); a nonzero
  Dirichlet polynomial of length N vanishing to order m_p along the progression of p (p ∈ S) has Π p^{m_p} ≤ N;
  1 − p^{−s} attains it; distinct progressions meet only at s = 0 (log q/log p irrational)
  (`prod_pow_le_of_vanishesAlong`, `sum_mul_log_le_of_vanishesAlong`, `cpow_neg_frobPoint_ne_one`) [L].
- EAHT Riemann–Roch of G_m(Q): sections of length N with divisor m have dimension h⁰(N,m) = ⌊N/Π p^{m_p}⌋
  (`finrank_sections_eq`), h⁰(N,0) = N; nonzero section ⇔ Π p^{m_p} ≤ N. Over F_q[T] with u = q^{−s}: divisibility by
  (u^e − 1)^m cuts dimension d + 1 − em (`finrank_divisibleLT_eulerFactor`): places of one degree share one
  progression; over Z each prime has its own and costs N − ⌊N/p⌋ conditions [L].
- EAHT: approximate vanishing is almost divisibility: Frobenius roots are 4/(Np log p) apart by integrality; values
  ≤ ε on J ≥ N²p log p consecutive points force Σ|C_w|² ≤ 2ε² (`sum_normSq_towerSums_le`); integer auxiliaries
  small to order m_p along p ∈ S satisfy Π p^{m_p} ≤ N (`prod_pow_le_of_small`) [L].
- EAHT twist tower: over Z the base-change levels w_j(n) = (−1)^{Ω(n)/2^j}Λ(n) on 2^j | Ω(n) live on prime powers
  p^k, 2^j | k, for j ≥ 1, so lie in Q (`twistLevel_mem_sqrtClass`): every prime has degree one; the tower is its
  first level [L].
- EAHT: the explicit Gevrey/Denjoy–Carleman schedules reach the index: hermNegIndex G_N → κ(K_ζ)
  (`tendsto_hermNegIndex_atomicGram`, `dcProfile_atomicGram_reaches_index`) [L].
- EAHT Hasse with heights: a tower of scale ℓ with ℓT < π separates all right zeros of ordinate ≤ T (π sharp);
  the tower of 3^k/2^j with k = O(T) certifies height T (`twoPrime_tower_certifies_height`) [L].
- EAHT: atomic family at unit-mass width 1/T has transform window × Dirichlet polynomial of length N; overlap
  c = N/T, bandwidth log N/log T = 1 + log c/log T (`bandwidth_eq_one_add_log_overlap`) [L].
- EAHT: a twin failing Weil positivity is seen by every large Gevrey section (`eventually_negative_iff_of_gevrey`) [L].

## F28. RH without primes: prime-blind positivity (RHTower)

- `RHTower.WeilSpectral.eq_vonMangoldt_of_weilPositiveFull`: every real weight lam : ℕ → ℝ whose full Weil
  functional A(k_f) − Σ_{n≥2} lam(n)ℓ_n(f) is ≥ 0 on all autocorrelations of C² compactly supported tests equals Λ
  on n ≥ 2. No hypothesis on lam (sign, growth, multiplicativity) or on ζ (`WeilConeUniquenessUnconditional`) [L].
- Proof shape (module docstring): the twisted arc minimum principle gives a probability measure on the modular
  bottom arc annihilating every twisted integer moment; its arc Gamma weights produce a jointly prime-blind,
  Ξ-divisible shifted-Gamma family Ξ·Q_j (j = 0 is Ξ); family rigidity `eq_vonMangoldt_of_xiDivisibleBlindFamily`
  forces lam = Λ [L].
- `weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt`: the Weil cone is {Λ} under RH and empty otherwise [L].
- `twistedArcMinimumPrinciple_holds` (`TwistedArcMinimumPrincipleProof`): no finite combination of twisted arc moments
  M_i(u) = ∫ g_u(x)cos(2π(i+2)x)dx is strictly positive on the closed bottom arc u ∈ [−½,½]. Proof via a stream
  function ψ = Σ a_i yK₁(k_i y)sin(k_i x) on the half fundamental domain of SL₂(Z), vanishing on both walls,
  decaying at the cusp, and a minimum principle with a corner argument at ρ = e^{iπ/3} [L].
- `exists_weilPositiveFull_iff_primeBlindPositive` (`WeilFullConeOneSidedCriterion`): some real lam is full-cone
  Weil-positive ⇔ PrimeBlindPositive, by the M. Riesz extension / finite feasibility theorem [L].
- `PrimeBlindPositive`: for every nonnegative finite combination of autocorrelations whose symmetric values vanish at
  every ±log n, n ≥ 2, the pole + archimedean part of the Weil functional is ≥ 0. "No prime enters" [L].
- `riemannHypothesis_iff_primeBlindPositive_unconditional`: RH ⇔ PrimeBlindPositive [L].
- `riemannHypothesis_iff_positiveOnNonnegCone` / `…NonposCone`: RH ⇔ W_Λ ≥ 0 on the cone of combinations whose
  values at ±log n are all ≥ 0 (resp. ≤ 0); robust forms for weights with summable excess/deficit over Λ [L].
- (obs) In this formulation the arithmetic input is only the node set {log n : n ≥ 2} (by BSU node criticality,
  equivalently the prime powers); Λ, the Euler product and the primes as weights are gone. None of the review-3010
  reports cites PrimeBlindPositive or the twisted arc minimum principle.
- `riemannHypothesis_iff_zeroPoleBlindPositive` (`ArchimedeanPoleValueFunction`): RH ⇔ the archimedean symbol
  Re ψ(¼ + ir/2) − log π, integrated against the spectral measure, is ≥ 0 on every nonnegative blind combination of
  total pole mass zero. "The pole enters only as a constraint; the functional is the archimedean symbol alone."
  Blind tests of both pole signs exist by support (two bumps at ±1/5) [L].
- `poleValue_eq` (under RH): the value function in (node vector v, pole mass p) is linear with gradient (Λ, −1);
  `riemannHypothesis_iff_bddBelow_poleFibre`: RH ⇔ one fibre is bounded below [L].
- `WeilPoleWeightWindow`: for pole weight β, Farkas holds at every β (`exists_weilPositiveAt_iff`); the admissible set
  of β is an interval; RH ⇔ β = 1 lies in it (`riemannHypothesis_iff_primeBlindPositiveAt_one`); pole-weight rigidity
  `eq_one_of_weilPositiveAt` [L].
- `TwistedArcN1Reduction`: the twisted arc vectors g_u (u on the bottom arc of the modular domain) are even, satisfy
  g_u(1/x) = |x|g_u(x), have zero mean and strictly positive cosine transform of the log profile; the minimum principle
  plus Prokhorov gives h = ∫g_u dμ(u) with h(1/x) = |x|h(x), ∫h = 0, PD log profile, and ∫h'(x)sin(2πmx)dx = 0 for every
  integer m ≥ 2 (additive integer blindness) (`exists_decayClass_fullLineWitness`) [L].
- `HTGeometry.le_of_halfDomainStreamMinimum`: minimum principle for y(Z_xx + Z_yy) − Z_y = 0 on the half fundamental
  domain {0 ≤ x ≤ ½, x² + y² ≥ 1} with wall, cusp and arc (ray-derivative) conditions [L].
- `WeilConeXiDivisibleBlindTest`: an (N1) object F (exp-decay C², prime-blind autocorrelation, F̂ vanishing at every
  zero of ζ, nonzero elsewhere on R) forces every Weil-positive system to be Λ; F̂ = Ξ·g, |F̂|² = Ξ²R with R a prime-blind
  radical multiplier (`eq_vonMangoldt_of_xiDivisibleBlindTest`, `archPoleEnergy_eq_zero_of_xiDivisibleBlindTest`) [L].

## F29. Hecke normalization, affine induction, off-line Λ-positive models, infinite symmetry

- APD `isPosDefOnGroup_heckeState_iff`: Hecke states φ_s(x ↦ ax+b) = (nd)^{−s}·1[db ∈ Z] on Aff(Q) are PD iff s ≥ ½;
  below ½ the Hecke–Bessel law nd·|φ(ux)|² ≤ 1 fails at u = 2; φ_s = Haar state × slope weight (nd)^{−(s−½)}; slope
  weights are PD multipliers via gcd^{2t} = Σ J_{2t}(d)1[d|A_i]1[d|A_j], J_α = μ⋆n^α ≥ 0. "The integer successor costs
  exactly half a unit of exponent" (module docstring) [L].
- APD `integer_successor_hecke_weight`: every PD φ on Aff(Q) with integer successor satisfies nd·|φ(dilation u)|² ≤ 1,
  attained [L]. (obs) ½ here is the square root of the commensurability index [Z : Z ∩ uZ][uZ : Z ∩ uZ] = nd.
- APD `heckeState_kakutani_wall`: φ_s PD ⇔ s ≥ ½; its torus measure is the prime Poisson measure; that measure ≪ Haar ⇔
  s > ½, mutually singular for s ≤ ½ [L].
- APD `riemannHypothesis_iff_exists_affine_posDef`: RH ⇔ some PD function on Aff(Q) restricts on dilations to the
  spline correlation; restriction–induction: affine positivity adds nothing beyond the dilation Gram; the successor
  coordinates are free unless prescribed by arithmetic [L].
- RHTower `PoleOrderTwoRealStray`: F(s) = ζ(s)((s−½)² − w²)/(s(s−1)) is Λ-positive (correction density
  (e^{u/2} − e^{wu})(e^{u/2} − e^{−wu}) ≥ 0), satisfies the exact FE, has entire order-one completion, real zeros ½ ± w,
  pole of order 2; a complex off-line quartet costs pole order 3 (`EntireFunctionalEquationOffLine`); "two is optimal" [L].
- (obs) all Λ-positive off-line models add a continuous density to the prime measure, so they leave the discrete node
  set log N; PBAP is vacuous for continuous support.
- RHTower `InfiniteSymmetry`: the affine A₁ Weyl sum of every curve datum (unitary or golden) has its poles exactly at
  the shifted zeros; polar confinement ⇔ the lower square-root count (`polarConfinement_iff_lowerCount`); the golden
  datum passes every test but the lower count; a priori Eisenstein information (Godement chamber, Maass–Selberg,
  closed positive chamber) certifies exactly {Re ρ ≥ 1} (`certified_closedChamber`); entirety of cuspidal loop
  Eisenstein series certifies nothing about zeros of Ξ (`pole_iff_zero_of_mul`) [L].
- `PrimeBlindFiniteLevelFarkas`: at level L (tests in [−L,L]) only nodes log n < 2L carry values; Φ ≥ 0 on blind
  nonnegative level-L combinations ⇔ ∃ node weights lam (supported on log n < 2L) with Σ lam(n)ℓ_n(f) ≤ Φ(f)
  (`levelBlindNonneg_iff_exists_weights`); strong duality as equality of sets of floors and margins
  (`levelFloors_eq_levelMargins`); RH ⇔ at every level some node weights give a Weil-positive level-L form
  (`riemannHypothesis_iff_forall_level_exists_weights`) [L].
- `PrimeBlindPoleWeightLevelWindow`: level windows of admissible pole weights β are closed intervals, decreasing in L,
  compact from L ≥ 3/10; they squeeze to {1} unconditionally (`exists_level_forall_abs_sub_one_lt`); RH ⇔ every level
  window is nonempty (`riemannHypothesis_iff_forall_level_exists_mem_levelWindow`) — "the pole weight is free at each
  level and determined only in the limit" [L].
- `PrimeBlindNonnegativeConeReduction`: nonnegative prime-blind g has positivity set of measure ≤ log 2 (dilation-free
  support); quantile transport reduces the nonnegative blind cone to one window (0, log 2) [L].
- `PrimeBlindPoleCriticalZetaDefect`: for f supported in [α,β] ⊂ (0,∞), Σ_{m≥1} A_f(m) = (∫f)(∫f/y) +
  (1/2π)∫|Mf(½+it)|² Re ζ(½+it)dt (`tsum_dilationAutocorr_eq_pole_add_integral_zeta`); for blind f the prime-blind energy
  is (1/π)∫|Mf(½+it)|²(θ'(t) + 1 − Re ζ(½+it))dt; a violator has S = ∫|M|²|ζ|² ≥ (m + πP)²/m: violators live on large
  values of |ζ| on the line (`pole_ge_of_blind_secondMoment`) [L].
- `BlindArchimedeanNodeTwoCertificate`: 2(1 − cos(r log 2)) ≤ γ(r) − γ(0) for γ(r) = Re ψ(¼ + ir/2) − log π
  (`two_mul_one_sub_cos_le_gammaBracket_sub`); BlindSymbolSlack(−γ(0) − 2) holds unconditionally, fails for every
  M ≤ 0; RH ⇔ ZeroPoleBlindSymbolSlack M for every M > 0: "the pole constraint must remove the whole negative part that
  the symbol alone retains" [L].
- AOT `TheLatticeOddLedgerIsBalanced`: on log-integer positions a prime-sum pair (log p^i, log p^j) is also a
  prime-difference pair with larger weight Λ(p^{i+j})/√p^{i+j} ≤ Λ(p^{|i−j|})/√p^{|i−j|} (`primeKernel_log_add_le`), so
  the odd Weil ledger is balanced; frustration exists only between lattice points [L].
- APD `measure_eq_of_measureTheta_relation`: a positive Borel measure ν on [1,∞) with ∫u^{−2}dν < ∞ whose
  θ_ν(x) = ∫e^{−πu²x}dν obeys Riemann's theta law is c·Σ_k δ_{k+1}; mechanism: a collar-blind Fejér pairing leaves
  ∫(sin πu/πu)²dν = 0; Beurling prime measures with the theta law are Riemann's Σ Λ(n)/log n·δ_n
  (`eq_riemannPrimeMeasure_of_beurling_theta_relation`) [L].
