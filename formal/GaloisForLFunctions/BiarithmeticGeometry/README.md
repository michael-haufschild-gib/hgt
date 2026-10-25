# Biarithmetic Geometry

Biarithmetic Geometry studies the joint additive and multiplicative action of the integers at
finite horizon. Its central question is whether this joint action supplies signed arithmetic
estimates that disappear when one keeps only multiplicative identities, complete-period quadratic
data, or a limiting energy. Its intended analytic target is the critical arithmetic form shared
by the corpus's approaches to the Riemann hypothesis. An exact finite identity is a foundation
for that target; an independent estimate uniform in the horizon is still required.

## Motivation and position

For a curve over a finite field, Frobenius is a ring map and the relevant point counts come from
a complete finite object. Over the integers, divisor incidence on `{1,...,N}` has common period
`L_N = lcm(1,...,N)`. Completing that period changes the scale of observation. In the corpus,
complete-period quadratic observations retain squared Selberg coordinates and lose their
individual signs. Normalized escape limits retain dilation but lose fixed successor translations.
Local prime-power payments exist, yet their shared resources need not suffice globally.

The programme therefore keeps four things together: the horizon, signed linear data, both ring
operations, and integer invariants. Its task is to find a source-derived relation between these
objects and the analytic norm, or to classify exactly why a proposed relation fails.

| Neighbouring programme | Interface |
|---|---|
| [Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md) | Divisor rows, Selberg coordinates, complete-period blindness, signed prefix observations. |
| [Trans-Horizon Incidence Mechanics](../TransHorizonIncidenceMechanics/README.md) | Centered prefixes, critical Wiener convolution, additive selectivity, horizon order. |
| [Arithmetic Defect Rigidity](../ArithmeticDefectRigidity/README.md) | Actual escaping energies, common cofactor Gram limits, antipodality, moving boundary costs. |
| [Arithmetic Orientation Theory](../ArithmeticOrientationTheory/README.md) | Critical Wiener algebra, repairing ideals, Bohr hulls, integer indices and weighted box invariants. |
| [Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md) | Scaling surface, effectivity, Riemann–Roch, Hodge index, finite-field calibration. |
| [Arithmetic Orientation Geometry](../ArithmeticOrientationGeometry/README.md) | Correspondences, orbit orientation, source-versus-sign distinctions. |
| [Arithmetic Incidence Positivity](../ArithmeticIncidencePositivity/README.md) | Local prime-power payments, shared surplus and the two-pole Chebyshev defect. |
| [Bi-Scale Uncertainty](../BiScaleUncertainty/README.md) | Square-root resolution, prime-power node criticality and countermodels. |

The affine relations have an established operator-algebraic setting in
[Cuntz's ax+b-semigroup algebra](https://arxiv.org/abs/math/0611541). Here truncation and its
boundary are part of the object. Arithmetic real-valued analogues of dimensions also have a
precedent in [van der Geer–Schoof's theta construction](https://arxiv.org/abs/math/9802121).
They must remain distinct from ordinary integer dimensions.

## Objects and language

**Horizon space.** `HorizonSpace N` is the real vector space on cells `{0,...,N}`. Write `e_j` for
the `j`th cell and set `e_j=0` for `j>N`. The origin is a genuine cell; the zero vector represents
absorption beyond the horizon. The interval itself is a partial arithmetic object, not a quotient
ring modulo `N`.

**Affine pushforward.** For positive integer `a` and nonnegative integer `b`,
`T_(a,b)e_j = e_(aj+b)`. Positive affine maps never return an escaped cell to the horizon.
Successor is `U=T_(1,1)` and dilation is `D_a=T_(a,0)`. Signed coefficients are retained by
linearity. No periodic identification is made.

**Arithmetic box invariant.** The existing source quantity is

`E(s) = exp(s) + s - 1 - ψ(exp(s))`.

Its continuous polar part and its prime-power masses are real-valued. Calling it an ordinary
Euler characteristic would impose an additional integrality statement, which is false.

**Horizon torsion.** Set `Q_N=L_N/N` for `N≥1`. This is a positive integer, and the finite cyclic
group `Z/Q_N Z` records a canonical torsion order. Lean uses parameter `N-1`, so
`horizonTorsionOrder n = L_(n+1)/(n+1)`. The group is represented through its integer order;
the construction does not enumerate a full divisor period.

**Escape modules.** The desired analytic objects are completions of finite cofactor packets in
their limiting Gram norm, with the critical Wiener algebra acting by dilation. The signed
residual, forcing trace and moving successor data must accompany this norm. An arbitrary
positive kernel satisfying dilation bounds is a calibration model, not an actual arithmetic
escape state.

**Payment obstruction.** A local allocation assigns available resource to prime-power charges.
A cohomological construction must define its resource locations, restrictions, admissibility,
and comparison with the source energy. Ambient geometric `H¹`, an adverse index, a capacity
deficit and a real weighted Euler invariant are four different objects.

## Foundational pillar theorems

### Exact affine composition at polynomial horizon

For every horizon,

`T_(a,b) T_(c,d) = T_(ac,ad+b)`, and `D_a U = U^a D_a`.

The proof checks a single cell and uses the fact that no positive affine map can bring an
out-of-range cell back. Every row is the sum of its signed cell coefficients. Thus retaining
finite horizon does not require replacing the ring relation by an approximate one.

Source: `HorizonAffineActions.lean`, `horizonAffine_comp`, `horizon_ring_relation`.

### The faithful finite affine quotient

An affine operator is zero precisely when its origin has escaped. Otherwise its image of
`e_0` determines the translation, and its image of `e_1` either determines the slope or says
that every positive cell is absorbed. Thus those two cell images determine the whole operator.
The canonical states are one zero state and, for every `0<=b<=N`, slopes
`1<=a<=N-b+1`, with the last slope representing all larger slopes. They are closed under
composition and give exactly `1+(N+1)(N+2)/2` distinct operators. This is a polynomial-size
faithful quotient of the positive affine action; no complete period is introduced.

Source: `FiniteAffineQuotient.lean`, `horizonAffine_eq_iff_origin_first`,
`horizonAffineImageEquiv`, `card_horizonAffine_image`, `horizonCodeAction_comp`.

### Joint rigidity of successor and dilation

The common commutant of `U` and `D_2` on `{0,...,N}` consists exactly of scalar operators.
The fixed space of `D_2` is the origin line: each positive even coordinate reduces to a smaller
coordinate, while odd coordinates vanish. If `A` commutes with both operators, `Ae_0` lies on
that line. Since `e_j=U^j e_0`, every cell has the same scalar.

This is a joint additive/multiplicative classification. It does not imply a norm bound for a
signed arithmetic source. The origin and the exact boundary convention are essential parts of
its statement. Scalar common commutant does not imply irreducibility here: every tail
`span(e_k,...,e_N)` is invariant under all positive affine maps.

Source: `horizon_double_fixed_iff`, `horizon_joint_commutant`.

In fact these tails are all invariant subspaces. For a nonzero invariant subspace, choose
its least possible nonzero coordinate `m`. Shifting a vector with that leading coordinate
and eliminating higher cells recovers every `e_j` for `j>=m`. This gives exactly `N+2`
invariant subspaces, including zero, all comparable. The natural affine representation is
therefore indecomposable. This is the classical single-Jordan-block classification in the
absorbing horizon model; it does not classify every representation of the finite semigroup.

Source: `AffineInvariantSubspaces.lean`, `horizon_affine_submodules`,
`card_horizonInvariantSubspaces`, `horizon_affine_indecomposable`.

### Exact signed boundary loss

For the cell pairing `B_N(v,w)=Σ_j v_j w_j`, every positive affine map satisfies

`B_N(T_(a,b)v,T_(a,b)w) + Σ_(aj+b>N) v_j w_j = B_N(v,w)`.

Injectivity preserves every surviving coefficient once; the omitted tail gives the entire
defect. The diagonal case is an energy contraction with its exact loss. Moreover an observable
invariant under the absorbing successor must be constant, because `N+1` successors send every
vector to zero. Finite-horizon covariance therefore needs this boundary calculus. Exact
translation invariance would erase the observable itself.

Source: `HorizonBoundaryCalculus.lean`, `horizonPairing_affine_add_boundary`,
`horizonPairing_affine_self_le`, `horizon_successor_invariant_iff`.

### Classification of scalar normalization freedom

Every multiplicative real character `w` gives another exact action,
`T^w_(a,b)=w(a)T_(a,b)`. Its origin coefficient is exactly `w(a)`, so two such dilation
operators agree precisely when their character values agree. The identity and inverse-linear
characters already give distinct operators at every horizon, with the same ring relation.
Covariance alone therefore cannot select the analytic normalization.

Source: `AffineNormalizationFreedom.lean`, `twistedHorizonAffine_comp`,
`twisted_dilation_eq_iff`, `twisted_dilation_two_distinct`.

### The box defect is not an ordinary cohomological index

At the node-free aperture `s=log(3/2)`,

`E(s) = 1/2 + log(3/2)`, with `0 < E(s) < 1`.

Consequently no natural-valued functions `h⁰,h¹` on all apertures satisfy `h⁰-h¹=E`.
In particular the corpus's positive and negative parts of `E` cannot be upgraded to ordinary
cohomology dimensions by relabelling them.

Source: `ArithmeticEulerCharacteristic.lean`, `no_dimension_model_for_boxDefect`.

### Arithmetic degree minus logarithmic torsion

The positive replacement is exact:

`E(log N) = (N-1) - log # (Z/Q_N Z)`.

Indeed `N | L_N`, and the classical identity `ψ(N)=log L_N` gives the formula. It retains a
genuine finite-group cardinality without asserting that its logarithm is an ordinary dimension.
This establishes the arithmetic type of a possible Euler formula. It supplies neither a payment
complex nor its vanishing theorem. The underlying least-common-multiple identity is classical;
the role here is to correct the proposed cohomological foundation.

Source: `boxDefect_eq_degree_sub_log_torsion`, `boxDefect_eq_degree_sub_log_card`.

Within the cell `log N ≤ s < log(N+1)`, the exact extension adds
`(exp(s)-N)+(s-log N)`. Thus every nonnegative aperture separates into its integer degree,
logarithmic torsion charge and continuous polar evolution, with no loss at noninteger horizons.
Source: `boxDefect_cell_interpolation`, `boxDefect_all_apertures`.

The torsion group is also the kernel of the canonical reduction
`Z/L_N Z → Z/N Z`. Period reductions `Z/L_(N+1) Z → Z/L_N Z` compose exactly and
are surjective. Their cyclic kernels have order `p` when `N+1` is a power of `p`,
and order one otherwise; their logarithmic orders are precisely `Λ(N+1)`.
Thus the charge has a finite-group restriction law. These symbolic period groups can have
more than polynomially many elements, and do not supply horizon-complete observations or
a payment Mayer–Vietoris sequence.

Source: `PrimePowerTransitionGroups.lean`, `horizonTorsionKernel_exact`,
`card_horizonTransition_prime_pow`, `horizonPeriodJump_eq_one_iff`,
`boxDefect_all_apertures_kernel`.

### Exact cost of shared-budget descent

Give each singleton in a `k`-atom set access to the same nonnegative resource `B`. Every
singleton-admissible allocation has globally admissible total precisely when `k≤1` or `B=0`.
On `k+1` atoms, the sharp possible excess is `kB`, attained by spending `B` on every atom.
This classifies the elementary shared-resource obstruction and gives its exact price. It does
not identify the actual arithmetic allocation problem with this model.

Source: `SharedBudgetDescent.lean`, `singletonPaymentsGlue_iff`, `sharedBudget_sharp_excess`.

### Repairing kernels disappear in actual escape normalization

For the damped Möbius source `c_ε` and every critical Wiener kernel `k`, the full cofactor action
is `P_k(n)=Σ_(j≤n) k(j) A_ε(floor(n/j))`. The exact convolution identity reads

`P_k = A_(k*c_ε) - m_ε A_k`.

The critical Wiener bound uniformly pays `A_k`. Whenever `k*c_ε` is paid, `P_k` consequently has
uniformly bounded pronic norm. Thus either the actual receiver is admitted, or every repairing
kernel has `‖P_k‖²/E_ε → 0`. The conclusion includes infinite kernels; it does not rely on paid
truncations. This source estimate also passes to the completed escape module.

Source: `PaidKernelsVanishOnEscape.lean`, `admitted_or_paidKernelAction_vanishes`.

### Full Wiener annihilation and the actual obstruction hull

ADR constructs the actual common cofactor limit with cyclic vectors `delta_j` and bounded
dilations `V_n`; AOT integrates their coefficient series into a contractive unital Wiener
representation. On escape, every paid kernel lies in this representation's annihilator.
To prove this for an infinite kernel, pair its full action with one fixed cofactor. The paid
action has bounded norm, while the cofactor norm is at most `sqrt(E_T)/sqrt(k)`, so the
normalized pairing tends to zero. The bound `|K_T(j,k)|<=1/sqrt(jk)` permits dominated
convergence of the single Wiener series. Every cofactor then pairs to zero with the
represented receiver image. Totality kills that image, and cyclicity kills the operator.

The module annihilator is proper, closed, and has a nonempty Bohr hull. Ideal inclusion
therefore gives a nonempty module hull contained in the actual source obstruction hull.
This proves the module–ideal bridge for every actual common Gram limit at every escaping
subcritical damping. The source-defined class has a constructed member; the universal
statement covers every other actual realization as well. It does not classify the possible
kernels or identify their hulls with the translated zero hull. The proof reuses ADR's full
covariance and cyclic-module comparison.

Source: `FullWienerAnnihilation.lean`, `admits_or_all_actual_annihilators`,
`admits_or_all_actual_moduleHulls`.

### Exact visibility within a covariance fibre

Let `Y_q` be a finite row's Selberg coordinate and `R_q(M)` the real Ramanujan primitive at
prefix `M`. Its precise visibility radius is

`V_N(M,c) = Σ_(q=2)^N |R_q(M) Y_q|`.

Every row with the same complete-period covariance has centered prefix bounded in absolute
value by `V_N(M,c)`. Independent coordinate signs attain both endpoints, preserve every
complete-period covariance, and preserve the mean. The fibre's exact prefix diameter is
therefore `2 V_N(M,c)`.

Covariance determines this centered prefix precisely when every product `R_q(M)Y_q` vanishes;
the determined value is then zero. This gives a mode-by-mode information criterion at every
horizon. A ratio of horizon to period alone discards the mode dependence retained here.
The result classifies observation loss for arbitrary signed rows; it supplies no bound for
the visibility of the Möbius row itself.

Source: `ExactPrefixVisibility.lean`, `prefix_visibility_diameter`,
`abs_prefix_readout_le_of_covariance_eq`, `prefix_covariance_determines_iff`,
`prefixVisibility_eq_zero_iff`.

### Diagonal scaling does not determine the metric

There is a cyclic three-dimensional dilation representation with positive kernel `K`,
`K(j,j)=j⁻²`, the critical cofactor radius bound, and every packet contraction `1/p`, yet
`K(2,4)=0≠K(1,2)/4=1/24`. Its metric is
`B(x,y)=x·y+(x₀y₁+x₁y₀)/3`; dilation is `V_p=p⁻¹P^(v₂(p))`, where `P` cyclically
permutes the coordinates. The vectors at cofactors 1, 2 and 4 span the representation.
Even the stronger `1/p²` packet contraction fails on a mixed vector.

Averaging `B`, `B(P·,P·)` and `B(P²·,P²·)` produces a positive `P`-invariant metric.
Its kernel has full mixed homogeneity and exactly the same diagonal as `K`. This identifies
the missing stationarity information. The example is a multiplicative calibration model;
no realization by the actual receiver is asserted. A stationary average of source tangents
would also require proof that it is an admissible source limit.

Source: `DiagonalScalingCountermodel.lean`, `cyclicKernel_packet_dilation_le`,
`cyclicKernel_not_homogeneous`, `cyclicDilation_two_not_quarter_contractive`,
`stationaryCyclicKernel_homogeneous`, `stationaryCyclicKernel_diagonal`.

### Finite-dimensional unitary covariance is rigid

Let `U_t` be a continuous family of unitary matrices with `U_0=1`. If an invertible matrix
`D` satisfies `D U_t=U_(pt) D` for some real `p>1`, then every `U_t=1`. A translation group
law is unnecessary. Conjugacy preserves trace, so iteration towards zero gives
`tr(U_t)=tr(1)`. The squared Hilbert–Schmidt norm of `U_t-1` is then zero.

Thus a nontrivial unitary translation limit with invertible expanding dilation needs an
infinite-dimensional carrier. This classifies the finite-dimensional calibration; it does
not establish existence, unitarity, or nontriviality of actual moving successor limits.

Source: `FiniteAffineUnitaryRigidity.lean`, `finite_affine_unitary_rigidity`.

### The domain of positive prime-log jump sums

For ordinary real `L²(R)` translations and nonnegative prime weights, the positive series
`Σ_p w_p ||f-τ_(log p)f||²` is finite exactly when the weights are summable or `f=0`.
Compact-support approximation proves that every translation correlation tends to zero;
the jump square therefore tends to `2||f||²`. Summable weights give the explicit bound
`4(Σ_p w_p)||f||²`. Nonsummable weights leave only the zero vector in the finite-energy domain.

This is a classical regular-representation domain test. It does not classify the signed Weil
form, a renormalized series, or a Bohr representation with nonvanishing translation coefficients.
Infinite weights at shifts tending to zero also lie outside this obstruction.

Source: `PrimeLogJumpDomain.lean`, `tendsto_physical_autocorr_zero`,
`primeJump_summable_iff`, `primeJump_tsum_le`.

### Exact weighted digit laws

The geometric prime-five receiver has a finite digit foundation. Evaluate the ordinary
base-five digits of `n` at a real parameter `a`, obtaining `D_a(n)`. Euclidean splitting gives
`D_a(5n+r)=r+a D_a(n)` for `r<5`, and at every depth
`a^k D_a(floor(n/5^k))=D_a(n)-D_a(n mod5^k)`. These exact signed identities hold before any
limit; for nonnegative `a`, the leading digit also gives `D_a(n)>=a^k` on the `k`th block.
The finite identities are proved in `WeightedBaseFiveDigits.lean`.

They identify the actual receiver of the geometric source `I_a(5^r)=a^r`, zero elsewhere.
For `|a|<5`, its mean converges absolutely to `5/(5-a)` and its centered ordinary-floor
prefix is exactly `-a/(5-a) D_a(n)`. The Euler-factor convolution identity gives the same
Euclidean recurrence as the digit row, so strong induction proves equality at every horizon.
No asymptotic profile is needed for this source comparison. The completed escape module
still requires its separate asymptotic comparison.
Source: `GeometricTowerDigitReceiver.lean`, `hasSum_fiveTower_div`,
`fiveTower_actualPrefix_eq_digitRow`.

For arbitrary signed digit coefficients `x_i`, complete enumeration also gives the exact
second moment `5^M[2 sum_i x_i^2+4(sum_i x_i)^2]`. On a block with nonzero leading
coefficient `z`, the second moment is
`4*5^M[(5/4)z^2+2 sum_i x_i^2+((5/2)z+2 sum_i x_i)^2]`, hence at least
`5^(M+1)z^2`. Lower-digit signs cannot remove this variance. These classical moment
identities retain all signed cross terms.
Source: `WeightedDigitMoments.lean`, `sum_sq_fiveDigitBlock`, `fiveDigitBlock_leading_lower`.
The base-five word equivalence transfers these formulas to the exact ordinary
integer intervals `n<5^M` and `5^M<=n<5^(M+1)`. Geometric coefficients recover
`D_a` at every integer, so the combinatorial lower bound applies directly to
its receiver indexing. Source: `WeightedDigitEnumeration.lean`,
`sum_sq_fiveWeightedDigitRow_block`, `fiveWeightedDigitRow_geometric`.

The pronic mass of the same block is exactly `4/(5*5^M)`. Comparing its largest
denominator with the variance lower bound, and using the pointwise digit bound
for the upper estimate, gives
`x_M^2/5^(M+1) <= E_block(W_x) <= (64/5)5^(-M)(sum_(i<=M)|x_i|)^2`.
Source: `DigitPronicBlocks.lean`, `fiveDigitPronicBlock_lower`,
`fiveDigitPronicBlock_upper`.

The finite geometric convolution `C_q(u)_M=sum_(l<=M)q^(M-l)u_l` satisfies
`(1-q)^2 sum_(M<=R) C_q(u)_M^2 <= sum_(M<=R)u_M^2` for every `0<=q<1`.
Weighted Cauchy--Schwarz and the exact finite mass identity prove this bound,
including the endpoint remainder. This supplies the upper norm estimate needed
for digit energy without imposing a summability premise on the coefficients.
Source: `FiniteGeometricConvolution.lean`, `sum_sq_finiteGeometricConvolution_le`.

Together these finite bounds identify the entire signed digit-energy domain:
`sup_N E_N(W_x)<infinity` exactly when `sum_l x_l^2/5^l<infinity`.
At every complete prefix the lower constant is `1/5`, and the upper constant is
`(64/5)/(1-1/sqrt(5))^2`. Arbitrary cutoffs lie below the next complete block.
Source: `WeightedDigitPronicEnergy.lean`, `fiveDigitPronicEnergyTo_complete_bounds`,
`bounded_fiveDigitPronicEnergy_iff`.

Every prime-five cofactor packet has these digit coefficients exactly:
`sum_(r<=log_5(n)) f_r D_a(floor(n/5^r)) = W_(C_a(f))(n)`, where
`C_a(f)_l=sum_(r<=l)a^(l-r)f_r`. For nonzero `a`, this is
`a^l sum_(r<=l)f_r/a^r`. Finite triangular reindexing proves the identity
for arbitrary signed coefficients, including the zero horizon.
Source: `DigitCofactorConvolution.lean`, `fiveWeightedDigitRow_convolution`,
`finiteGeometricConvolution_eq_partialPoleSum`.

For every source with an absolutely convergent mean and every critical Wiener
kernel, payment is equivalent to bounded norm of the full cofactor action.
The exact convolution law differs from that action by the source mean times
the kernel's centered prefix; the critical Wiener bound pays this correction
uniformly. This equivalence uses actual means and the entire kernel.
Source: `CofactorPaymentCriterion.lean`,
`receiverBounded_dirichletConv_iff_cofactorNorm`.

These identities determine actual payment on the prime-five subalgebra.
For `a!=0`, `|a|<5`, and `sum_r |f_r|/sqrt(5)^r<infinity`, the kernel
`k(5^r)=f_r`, zero elsewhere, repairs `I_a` exactly when
`sum_l (a^2/5)^l (sum_(r<=l)f_r/a^r)^2<infinity`.
At `a=sqrt(5)`, writing `f_r=sqrt(5)^r g_r` turns this into square
summability of the ordinary partial sums of `g`. This is a source-domain
classification, obtained before any limiting module or hull comparison.
Source: `PrimeFivePaymentCriterion.lean`, `receiverBounded_fiveTowerKernelLift_iff`,
`receiverBounded_critical_fiveTower_iff_partialSums`.

For complex kernels, the real and imaginary energies add to the squared
complex norm. The same criterion therefore holds with complex partial sums.
The actual golden ideal identity transfers it to `a=alpha*t`, `0<t<=1`.
Its exact critical parameter is `tcrit=sqrt(5)/alpha`, strictly between
zero and one. At that parameter payment is square summability of the
partial sums of `k(5^r)/sqrt(5)^r`. At `t=0`, every Wiener kernel pays.
Source: `GoldenPrimePayment.lean`, `mem_paidIdeal_golden_fiveTower_iff`,
`mem_paidIdeal_golden_critical_fiveTower_iff`, `mem_paidIdeal_golden_zero`.

The boundary has an explicit coefficient obstruction. Set `u_n=1/sqrt(n+1)`,
`g_0=-1`, and `g_(n+1)=u_n-u_(n+1)`. Its absolute sum is two and its total
sum is zero, but its partial sums are `-u_n`, whose squares have divergent
sum. Truncating after `N` and adding `u_N` to the constant coefficient gives
a finite zero-sum repair, at exact coefficient distance `2u_N` from `g`.
Thus zero evaluation alone is weaker than the critical energy condition.
Source: `CriticalUnpaidSequence.lean`, `criticalUnpaidCoeff_partialSum`,
`not_summable_sq_criticalUnpaidCoeff_partialSum`, `criticalFiniteRepair_distance`.

The normalization is isometric in the actual Wiener algebra. The real lift
`k_g(5^r)=sqrt(5)^r g_r`, zero elsewhere, satisfies
`||k_g||_W=sum_r|g_r|` and `||k_g-k_h||_W=sum_r|g_r-h_r|`.
The exact critical weight cancellation proves these identities, and the
actual tower paid-ideal criterion reads the partial-sum energy of `g`.
Source: `CriticalWienerLift.lean`, `norm_fiveCriticalWienerLift`,
`norm_fiveCriticalWienerLift_sub`, `mem_paidIdeal_critical_fiveCriticalWienerLift_iff`.

The same coordinates preserve the complex coefficient norm and distance.
For `g` in complex `ell1`, the lifted kernel has coefficient
`sqrt(5)^r*g_r` at `5^r` and zero elsewhere. Its critical golden payment
criterion is exactly `sum_M |sum_(r<=M)g_r|^2<infinity`, with real and
imaginary payment combined into the complex square norm.
Source: `ComplexCriticalWienerLift.lean`, `norm_fiveComplexCriticalWienerLift`,
`fiveComplexCriticalWienerLift_linear`,
`mem_golden_critical_fiveComplexCriticalWienerLift_iff`.

The critical coefficient domain has a finite core over the complex numbers.
For `S_M=sum_(r<=M)g_r`, retain `g_r` through `N`, subtract `S_N` from
the last retained coefficient, and delete all later terms. The corrected
partial sums equal `S_M` for `M<N` and vanish thereafter. Its exact
coefficient error is `|S_N|+sum_(r>N)|g_r|`, tending to `|sum_r g_r|`.
If the original partial sums are square summable, their limit forces
`sum_r g_r=0`; the squared partial-sum error is exactly the deleted
energy tail. Thus the same finite corrections converge in both parts
of the critical graph norm.
Source: `CriticalPartialSumCore.lean`, `criticalCorrectedTruncation_norm_error`,
`criticalCorrectedTruncation_sq_error`, `criticalCorrectedTruncation_graph_errors_tendsto`.

The geometric future tail `B_b g(m)=sum_(s>=0)b^(s+1)g(m+s+1)` has
absolute coefficient norm at most `b/(1-b)||g||_1` for `0<=b<1`.
It satisfies `B_b g(m)=b*g(m+1)+b*B_b g(m+1)`. Joint absolute
summability justifies both the recurrence and the series reordering.
This supplies the analytic tail estimate for division away from criticality.
Source: `GeometricFutureTail.lean`, `geometricFutureTail_recurrence`,
`tsum_norm_geometricFutureTail_le`.

### Admission and total pronic energy

For any real row `f`, the positive cells have energies
`e_n=f(n+1)^2/[(n+1)(n+2)]`, and `sum_(n<T)e_n=||f||_T^2` exactly.
Their positivity makes uniform finite-horizon norm bounds equivalent to
summability of the full energy. Applied to the actual centered prefix, this
identifies receiver admission with a total-energy domain. Complex energy
splits exactly into its real and imaginary parts. These domain identities
do not supply an admission estimate for an escaping source.
Source: `PronicEnergyDomain.lean`, `bounded_pronicNorm_iff_summable`,
`receiverBounded_iff_summable_pronicCellEnergy`, `summable_complex_pronicEnergy_iff`.

For an arbitrary complex source row, every normalized cofactor coordinate
is a finite continuous linear combination of Wiener coefficients. Equating
these coordinates with an `ell2` output defines a closed submodule of
`W_(1/2) x ell2`. Its inherited maximum norm is complete; the input
projection is injective, with image exactly the finite-total-energy domain.
The source's origin value is irrelevant. A complete graph can have a
nonclosed image in the input Wiener norm, so these are distinct properties.
Source: `CofactorGraphDomain.lean`, `isClosed_cofactorGraphDomain`,
`cofactorGraphDomain_completeSpace`, `mem_range_cofactorGraphInput_iff`.

For the actual centered prefix of any source with absolutely convergent
mean, this graph image is exactly its complex paid ideal. Every paid
kernel has one unique square-summable output. The source convolution law
and the paid critical-Wiener mean correction prove the identification in
both real and imaginary parts.
Source: `PaidGraphIdentification.lean`,
`mem_range_actualSourceCofactorGraphInput_iff`,
`paidIdeal_iff_existsUnique_cofactorGraph`.

The ordinary completed pronic space also has exact dilations. In normalized
positive-cell coordinates, the floor action has weight
`sqrt(m(m+1))/sqrt(n(n+1))`, where `m=floor(n/j)`. Its block mass is exactly
`1/j`, so `||D_j f||=||f||/sqrt(j)`. The operators compose as `D_j D_k=D_(jk)`
and integrate to a unital representation of the critical Wiener algebra with
`||pi(a)||<=||a||_W`. This ordinary energy module precedes normalization by
escaping source energy. Source: `PronicDilationOperators.lean`,
`norm_pronicDilationOp`, `pronicDilationOp_comp`, `pronicWienerRepresentation`.

Undoing the normalization at any integer cell gives a continuous row
coordinate. It reads dilation as exact floor division and the completed
Wiener action as the finite sum `sum_(1<=j<=n) a(j) f(floor(n/j))`.
Terms above the cell vanish, so the full operator series agrees with the
arithmetic formula at every horizon.
Source: `PronicWienerCoordinates.lean`, `pronicRowCoordinate_dilation`,
`pronicRowCoordinate_wiener`.

### Paid perturbations preserve the complete ideal

For sources with absolutely convergent means, adding a paid source leaves the entire
complex repairing ideal unchanged. Every critical Wiener kernel sends the added source
to a paid source; linearity then proves both inclusions by addition and subtraction.
Critical Wiener sources are themselves paid, so they give a useful application without
an additional receiver estimate. Nonzero scalar multiplication also preserves the ideal.
These equalities concern actual payment, including when the ideal is not norm closed.

Source: `PaidSourcePerturbations.lean`, `paidIdeal_add_paid`,
`paidIdeal_smul_add_criticalWiener`.

### The golden source has exact geometric inverse coefficients

For the actual ACS golden roots `alpha,beta`, let `a=alpha*t`, `b=beta*t`. Rescaling the
golden zeta variable by any complex `t` gives a formal series with inverse
`(1-tX)(1-5tX)/[(1-aX)(1-bX)]`. Its constant coefficient is one, and its positive-degree
coefficient is `-(a^n-b^n)/sqrt(5)`. The proof uses the actual root sum, product, and difference
and geometric power-series cancellation. At `t=1` the zeta series is exactly
`goldenDatum.zetaSeries`. No convergence or choice of numerical roots enters this identity.

For real `0<=t<=1`, reading these coefficients at norms `5^r` and extending by zero gives
the exact arithmetic source `delta_1-I_a/sqrt(5)+I_b/sqrt(5)`. Its mean converges absolutely
and equals `(5-6t+t^2)/(5-5t+t^2)`. The unit and secondary tower form a critical Wiener
source because `b<sqrt(5)`. Paid perturbation invariance therefore identifies the complete
golden repairing ideal with the primary tower's ideal. The limiting module still requires
the separate norm comparison.
Source: `GoldenInverseSeries.lean`, `goldenZetaSeriesAt_one`, `goldenInverseSeriesAt_mul`,
`goldenInverseSeriesAt_coeff`.
Source comparison: `GoldenArithmeticSource.lean`, `goldenArithmeticSource_mean`,
`paidIdeal_goldenArithmeticSource`.

The ordinary-floor admission threshold is exact. For `0<=a<5`, the geometric tower is
paid precisely when `a<sqrt(5)`. The critical tower already escapes; nonnegative digits
and the increasing factor `a/(5-a)` force every larger tower to escape as well. Thus
the golden source at `0<=t<=1` is paid precisely when `alpha*t<sqrt(5)`. Equality is
unpaid. This threshold follows from finite digit monotonicity and the existing critical
sharpness theorem, before constructing the limiting profile.
Source: `GoldenSourceAdmission.lean`, `receiverBounded_fiveTower_iff`,
`receiverBounded_goldenArithmeticSource_iff`.

Signed parameters have the same exact radius: for every real `|a|<5`,
the tower is paid precisely when `|a|<sqrt(5)`. Both critical signs escape,
and changing the sign of the prime-five generator preserves admission.
The proof uses signed digit variance and includes the zero parameter.
Source: `SignedTowerAdmission.lean`, `receiverBounded_fiveTower_abs_iff`,
`receiverBounded_fiveTower_neg_iff`,
`not_receiverBounded_negative_critical_fiveTower`.

The actual roots also test normalized amplification. Sending each root
`z` to `z^3/5` preserves their product five and gives trace ten. The first
two transformed point counts are exactly `-4` and `-64`, while every
original golden point count is nonnegative. Thus this operation fails
to preserve the positive-count class even with fixed rank and determinant.
Those invariants do not define analytic conductor, so the general
bounded-conductor question requires a separate formulation and theorem.
Source: `GoldenNormalizedCube.lean`, `goldenNormalizedCube_product`,
`goldenNormalizedCubePointCount_two`,
`golden_pointCount_positive_but_normalizedCube_negative`.

The integral trace obstruction has a complete prime-by-prime classification.
If `p*U=T^3-3p*T` and both second point-count bounds
`T^2,U^2<=(p+1)^2` hold, then `p` divides `T`. For `p>=5` only
`T=U=0` survives; the nonzero cases are `(p,T,U)=(2,2,-2),(2,-2,2),
(3,3,0),(3,-3,0)`. Every survivor satisfies `T^2<=4p`, and `U` is unique.
Source: `NormalizedCubicTrace.lean`, `exists_normalizedCubicTrace_iff`,
`normalizedCubicTrace_pure_bound`, `normalizedCubicTrace_unique`.

### Intrinsic counting changes the golden receiver

Using the golden system's own generalized-integer count gives cumulative series
`B(X)=Z(X)/(1-X)`, with exact coefficients
`B_M=(5/16)5^M-M/4+11/16` and bounds `0<=B_M<=5^M`.
Centering its convolution with the damped inverse by the actual arithmetic mean
cancels the counting pole. For `D=5-5t+t^2`, `a=alpha*t`, `b=beta*t`, the result is

`A_t(X)=(t/D)(1-5X+5X^2)(1-t^2X)/[(1-X)^2(1-aX)(1-bX)]`.

It is zero at `t=0` and `1/(1-X)` at `t=1`. Thus a golden calibration must specify
its counting kernel and cofactor action: the intrinsic coefficient row at `t=1`
is constant, whereas the ordinary-floor receiver escapes. The series identities
do not themselves identify the completed intrinsic tangent module.
Source: `IntrinsicGoldenSeries.lean`, `goldenIntrinsicCount_eq`,
`goldenIntrinsicCount_bounds`, `goldenIntrinsicReceiverSeries_factorization`,
`goldenIntrinsicReceiverSeries_one`.

## Mechanisms and traps

1. **Affine identities need a normalization.** Multiplying every dilation by a multiplicative
   scalar character preserves the affine relation. Excluding a positive escape exponent requires
   a source-derived metric, trace or normalization that detects that twist.
2. **Integer indices and real charges are complementary.** An arithmetic Euler formula may
   combine degree with logarithmic torsion. An ordinary finite-dimensional index cannot equal
   the continuously varying box defect.
3. **Local existence is not a sheaf axiom.** Reusing a shared budget on two windows need not
   define a sheaf of admissible allocations. Restrictions and the gluing law must be proved.
   Linearization may discard precisely the inequalities responsible for unpaid demand.
4. **Curve cohomology does not vanish under RH.** Its ambient first cohomology has dimension
   `2g`. A vanishing obstruction for purity must be a different group or a specified adverse
   part; otherwise positive-genus curves already contradict the proposed calibration.
5. **Finite kernels do not automatically approximate inside the paid ideal.** Wiener truncations
   approximate a kernel, but truncations of a repairing kernel need not repair. Use the norm
   bound for the full action when extending annihilation to infinite kernels.
6. **A finite Gram limit does not control moving tails.** White-noise and power-law kernels are
   calibration models. Passing an unbounded cofactor sum, a pole trace, or a moving translation
   through the limit needs a separate estimate.
   In particular, the proposed exclusion of white noise by antipodality is false: ADR's
   `whiteNoise_has_unique_antipodal_extension` constructs its unique positive extension with
   unit residual mass and antipodal receiver pairing. Additional source relations are essential.
7. **Structural selectivity is not source selectivity.** A theorem involving integer addition
   and multiplication may still hold after changing Euler weights. It cannot then orient the
   actual source solely by that theorem.

## Research questions and tools to develop

The programme retains the full three-wall target: a signed square-root estimate for one zeta
source, independent arithmetic Riemann–Roch on the scaling surface, and classification of actual
escape states. The following are open mathematical obligations.

- **Horizon-complete observation.** Quantify sign visibility between a prefix and a full period,
  with polynomial horizon and the complete signed source retained.
- **Escape classification.** Classify all actual common-limit Wiener modules, compare their
  annihilators with the paid ideal, and determine which source information their hulls retain.
  Annihilation and hull inclusion are proved for every actual common limit; the golden family and the
  translated zero-hull comparison remain open.
- **Critical translations.** Determine a scale at which moving successors can retain nontrivial
  source information, prove their covariance with dilations, and state the order of every limit.
  For actual damping `epsilon`, ADR proves raw displacement energy is uniformly
  `o(k^(2(1-epsilon)))` and recentered energy is uniformly `o(k^(1-epsilon))`.
  A bounded ratio of the corresponding power to escaping energy still forces disappearance.
  Thus the square-root energy proposal is excluded; a larger scale needs its own existence
  theorem. Source: `ArithmeticDefectRigidity/TheSourcePowerSavingControlsMovingSuccessors.lean`.
- **Arithmetic payment theory.** Define an allocation site or complex that retains shared
  capacity. Relate its integer obstruction to the real degree/torsion invariant; prove exact
  sequences, prime-power transition laws and a source-derived duality.
- **Quantitative Class III.** Use joint additive and multiplicative structure to bound signed
  off-diagonal Vaughan entries. An identity without such a bound leaves the analytic wall intact.
- **Stepanov at integer horizon.** Recover the finite-field count in packet coordinates, then
  identify a simultaneous prime-power vanishing mechanism that fails for parity twins.
- **Infinite-rank coercivity.** Determine when prime-coordinate bounds transfer to the dense
  logarithmic orbit. State and prove the uniformity needed for this transfer.
- **Amplification and orientation.** Specify the operations and conductor notion before stating
  a bounded-conductor amplification theorem. Construct an independently positive polarization
  compatible with the ring action and arithmetic normalization.

## Selectivity and calibration

The battery comprises genuine curve data, the golden datum, Beurling systems with off-line zeros,
shifted zeta pairs, single-prime Euler deformations, parity twins, and deletion of the nodes
`log 4` and `log 6`. Every proposed closing theorem must say which data it distinguishes and why.

The affine-action theorems concern the integer cell geometry and make no assertion about changing
Euler weights. The arithmetic Euler formula uses the actual integer prime-power weights. Neither
is claimed to pass the battery as an orientation theorem. Complete-period blindness remains the
existing BVI obstruction. Finite-field cohomology and analytic escape models require their own
comparison maps; a shared notation is insufficient.

The affine identities belong to the structural ring-selective class III; their freedom under
changing scalar characters prevents a source-selective conclusion. The shared-budget theorem is
a universal capacity calibration. The paid-kernel argument proves the full module–ideal bridge for every actual common limit;
it supplies no new source-selective cancellation estimate.
These distinctions prevent a useful foundational tool from being counted as a closing estimate.

## Success and contribution criteria

Full success requires the original programme's five gates: recover curve `H¹` and duality with
the correct obstruction comparison; pass the source-selectivity battery; recover PNT, the VK
band and the Guth–Maynard density bound in source-defined coordinates; produce new unconditional
analytic output or an actual escape-family classification; and formalize every finite-horizon
claim without new analytic premises. These gates are not all proved by the foundations above.

A contribution must state a precise source object and horizon, retain signed information, identify
its selectivity class, provide an unconditional paper proof and a kernel-checked Lean theorem,
and distinguish a structural classification from a new analytic estimate. A failed mechanism must
yield its strongest positive theorem before retirement. No result may obtain its missing source
estimate by placing it in an assumption, an interface, or an imported dependency.
