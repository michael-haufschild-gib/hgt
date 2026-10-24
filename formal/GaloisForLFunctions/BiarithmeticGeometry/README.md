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
truncations. This is the source estimate needed for annihilation in an escape module. Constructing
and identifying the completed module and its Bohr spectrum are additional steps.

Source: `PaidKernelsVanishOnEscape.lean`, `admitted_or_paidKernelAction_vanishes`.

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
7. **Structural selectivity is not source selectivity.** A theorem involving integer addition
   and multiplication may still hold after changing Euler weights. It cannot then orient the
   actual source solely by that theorem.

## Research questions and tools to develop

The programme retains the full three-wall target: a signed square-root estimate for one zeta
source, independent arithmetic Riemann–Roch on the scaling surface, and classification of actual
escape states. The following are open mathematical obligations.

- **Horizon-complete observation.** Quantify sign visibility between a prefix and a full period,
  with polynomial horizon and the complete signed source retained.
- **Escape representation.** Construct the completed Wiener module from the actual cofactor
  Gram limit. Prove annihilation by the paid ideal and inclusion of its spectrum in the
  obstruction hull. Classify the actual families, including the golden calibration.
- **Critical translations.** Construct moving successor limits at the square-root energy scale,
  prove their covariance with dilations, and state the order of every limit.
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
