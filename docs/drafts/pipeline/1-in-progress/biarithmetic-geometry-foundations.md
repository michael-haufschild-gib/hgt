# Biarithmetic Geometry: finite horizons, signed incidence, and obstruction theory

- **ID:** biarithmetic-geometry-foundations
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** ../../../reports/review-2410/opus.md, especially §§2–4
- **Statement:** Develop the finite-horizon geometry of the joint additive and multiplicative action of the integers, including signed observation, payment obstructions, and arithmetic escape modules.

## Goal

Carry out the full programme requested in the attached brief. Its completion criterion includes
the questions, tools, and criteria K1–K5 in the source report; a collection of definitions or
receiver equivalences does not complete it. All new Lean leaves belong to
`formal/GaloisForLFunctions/BiarithmeticGeometry/`, with sibling umbrella
`BiarithmeticGeometry.lean`. A foundational README must explain mathematics, not record sessions.
The `hgtl7` skill is expressly excluded. No numerical experiments or computation-based proofs.

## Gates

- [x] 0 → 1: source report read fully; existing ACS/AOG foundations and relevant corpus searched.
- [ ] 1 → 2: dependency-closed paper proofs for each claimed contribution.
- [ ] 2 → 3: each new leaf passes `lake --old env lean`; all main declarations audited with
  `#print axioms`; imports wired without compiling umbrellas.
- [ ] Full programme: every source question and K1–K5 discharged, or a false proposed statement
  replaced by its strongest proved positive survivor without claiming the original statement.

## Requirements and evidence needed

| Source requirement | Required evidence | Status |
|---|---|---|
| Own folder, umbrella, foundational README | Current files, verified imports, mathematical exposition | Open |
| Horizon-complete objects; sign visibility | Exact signed finite-horizon laws and quantitative period/prefix comparison | Open |
| Truncated affine representation theory | Source-defined action, boundary calculus, classification/calibration | Open |
| A1–A2: paid ideal annihilates escape; hull inclusion | Actual receiver theorem, not an assumed ideal inclusion | Open |
| A3: regular-variation dilation law | Precise subsequence hypotheses proved for source or exact unconditional classification | Open |
| A4: moving translations and covariance | Construction at critical scale with controlled boundaries | Open |
| Golden module and white-noise battery | Actual signed-data checks, not just positivity/dilation checks | Open |
| B1: payment cohomology and Euler characteristic | Well-posed definition and exact relation to corpus box defect | Literal dimension identity under audit |
| B2: Mayer–Vietoris and prime-power jumps | Exact sequence with source-defined restriction maps | Open |
| B3–B4: duality and certified-window vanishing | Independent duality and source comparison | Open |
| C1–C2: Stepanov calibration and replacement identity | Finite-field calibration and signed integer source test | Open |
| Quantitative Class III | New off-diagonal signed estimate, or sharp obstruction plus positive survivor | Open |
| Infinite-rank coercivity | Precise transfer law or complete countermodel classification | Open |
| Bounded-conductor amplification | Well-defined operation class; proof or counterexample | Open |
| Orientation | Ring-selective polarization with independent sign proof | Open |
| K1 | Curve cohomology dimension `2g`, Serre duality, Weil calibration | Open |
| K2 | Golden, Beurling, shifted-pair, Estermann, parity, node-4/node-6 tests | Open |
| K3 | Source-defined recovery of PNT, VK band, Guth–Maynard density | Open |
| K4 | New certified window, band exponent, or actual escape-family classification | Open |
| K5 | Every finite-horizon assertion formalized without unproved analytic premises | Open |

## Approach

Audit proposed foundations before importing their conclusions. Preserve two distinct invariants:
integer cohomological indices and real weighted arithmetic masses. Construct finite-horizon affine
actions directly, retaining cutoff defects and signed coefficients. Compare all abstractions to
actual divisor rows before asserting consequences for RH.

## Mathematical audit: Euler characteristic

The proposed literal identity `dim H⁰ - dim H¹ = E(s)` cannot hold for ordinary finite-dimensional
vector spaces. Below the first prime, the existing corpus gives `E(s) = exp(s) + s - 1`.
At `s = log(3/2)`, this is `1/2 + log(3/2)`, strictly between `1/2` and `1` because
`0 < log(3/2) < 1/2`. It is not an integer. This is a paper proof awaiting Lean certification.

Positive replacement to develop: a real weighted Euler characteristic / arithmetic degree together
with a separate integer obstruction index. Prove exact finite additivity and node-jump laws for
the weighted object; do not call positive and negative parts dimensions. A weighted identity
alone does not provide a payment sheaf, duality, or a vanishing theorem.

### Stronger positive replacement: horizon torsion

[PROVED HERE, paper; Lean pending] Let `L_N = lcm(1,...,N)` and `Q_N=L_N/N` for `N≥1`.
Since `N | L_N`, `Q_N` is a positive integer. The classical identity `ψ(N)=log L_N` gives

`E(log N) = (N-1) - log Q_N`.

Thus the box defect is an integer degree minus a logarithmic torsion charge, not an ordinary
Euler characteristic. The finite group `Z/Q_N Z` has order `Q_N`. This is a canonical arithmetic
candidate for the torsion term, with no positivity or zero-location hypothesis. The formula does
not yet construct sheaf cohomology. It uses a succinct integer invariant, not an enumeration of a
complete period. The identity `log L_N=ψ(N)` is classical (Mathlib
`Chebyshev.psi_eq_log_lcmUpto`); the programme contribution is the exact type-correct replacement
for B1 and its subsequent obstruction calculus, not a novelty claim for that identity.

[PROVED HERE, paper; Lean pending] The full positive replacement extends across each cell:
for `log N ≤ s < log(N+1)` with `N≥1`,

`E(s) = (N-1) - log Q_N + (exp(s)-N) + (s-log N)`.

The prime-power count is constant within this half-open cell, so subtract its value at `log N`.
The two remaining terms are exactly the archimedean evolution. Every nonnegative aperture lies
in exactly one such cell (`N=floor(exp s)`). This separates the quantized torsion datum from
continuous evolution on all apertures, not merely at the integer lattice. Add this theorem before
closing the literal-B1 no-go; an integer-horizon formula alone is not the strongest survivor.

### Finite-horizon joint rigidity

[PROVED HERE, paper and Lean] On `V_N = span(e_0,...,e_N)`, define truncated pushforwards
`Ue_j=e_(j+1)` and `D_p e_j=e_(pj)`, with out-of-range vectors zero. They satisfy
`D_p U = U^p D_p` exactly. For `p≥2`, the common commutant of `U` and `D_p` consists precisely of
scalar operators. Indeed `D_p A e_0=Ae_0`; a `D_p`-fixed vector has all positive coordinates zero,
by induction using the coordinate `i/p<i` when `p|i`, and zero otherwise. Hence `Ae_0=c e_0`.
Commutation with `U` gives `Ae_j=c e_j` for every `j`, and linearity proves the claim.

The origin is essential: it is the multiplicatively fixed vector that generates the entire
horizon under addition. This is a joint additive/multiplicative rigidity theorem, not an energy
estimate or an orientation theorem. Scalar twists `D_p -> a(p)D_p` preserve the affine relation;
the relation cannot select an analytic dilation normalization by itself.

Lean: `HorizonAffineActions.lean` passed the direct leaf check
`lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/HorizonAffineActions.lean`.
Main declarations: `horizonAffine_comp`, `horizon_ring_relation`,
`horizon_double_fixed_iff`, `horizon_joint_commutant`. Axiom audit of composition, fixed space
and common commutant reports only `propext`, `Classical.choice`, `Quot.sound`.
The module's olean was created for the normalization and boundary leaves that import it.

### Repairing kernels and escape: proof plan with exact corpus dependencies

For a coefficient source `c` with absolutely convergent mean `m_c`, write `A_c` for its centered
divisor prefix. THIM `weightCenteredPrefix_dirichletConv` gives exactly

`A_(k*c)(n) = Σ_(j≤n) k(j) A_c(floor(n/j)) + m_c A_k(n)`.

THIM `pronicNorm_weightCenteredPrefix_le_critical` uniformly bounds `A_k` for every critical
Wiener kernel. If `k*c` is paid, its prefix is uniformly bounded as well. Therefore the cofactor
packet on the right has uniformly bounded pronic norm. On actual escape its squared norm divided
by `dampedMobiusEnergy ε T` tends to zero. For finite `k`, ADR
`cofactorGram_quadratic_eq` and convergence of the common Gram table imply its limiting quadratic
form is zero. This proves the finite-kernel part of A1 once the source and norm bridges are checked.

For infinite kernels, do NOT assume that finite truncations of a paid kernel are paid. Extend the
packet action using the proved `j^(-1/2)` contraction and its Wiener tail, then use the exact full
convolution law. This supplies a valid route to the full annihilator statement; density of finite
supports in the entire algebra alone is insufficient.

[PROVED HERE, paper; Lean pending] `PaidKernelsVanishOnEscape.lean` proves the full-kernel
normalization statement directly, before a Hilbert completion. For every subcritical damping,
either the actual receiver is admitted, or **every** critical Wiener kernel whose convolution
with the actual source is paid has normalized cofactor-action energy tending to zero.
The finite-horizon action is `Σ_(j≤n) k(j) A_ε(floor(n/j))`. The convolution identity and the
uniform critical-kernel prefix bound give a constant independent of `T`; division by escaping
receiver energy proves convergence. No truncation is asserted paid. The GNS and Bohr-hull
comparison remain separate obligations.

### Distinct meanings of first cohomology

The finite-field calibration also requires separating ambient geometric `H¹` from unpaid
obstruction. A genus-`g` curve has ambient `dim H¹=2g` even when its Weil bound holds. Thus the
same unmodified group cannot simultaneously have dimension `2g` and vanish precisely when the
Weil bound holds for every positive-genus curve. An adverse subspace, relative group, or a separate
obstruction complex is needed. No comparison of such complexes has yet been proved.

### Shared-capacity descent

[PROVED HERE, paper; Lean pending] On a finite discrete set of `k` atoms, let an admissible
allocation have nonnegative values and total mass at most a common budget `B≥0`. Restrictions
are admissible. Every singleton-admissible allocation glues to an admissible global allocation
iff `k≤1` or `B=0`. Necessity: the constant allocation `B` would require `kB≤B`. Sufficiency:
sum the pointwise bounds when `k≤1`, and all entries vanish when `B=0`.
For `k+1` singleton windows the sharp possible excess is exactly `kB`, attained by the constant
allocation. This is a complete calibration of the shared-resource failure, not a theorem that
the actual arithmetic allocation functor is this model. It proves that local payment plus
restriction alone does not justify naming a payment sheaf. Positive repair requires tracking
resource locations and compatible quotas in the site.

### Absorbing boundary calculus

[PROVED HERE, paper; Lean pending] With the cell pairing
`<v,w>_N = Σ_(j=0)^N v_j w_j`, every positive affine map has the exact signed identity

`<T_(a,b)v,T_(a,b)w>_N + Σ_(aj+b>N) v_j w_j = <v,w>_N`.

The map `j -> aj+b` is injective. Each surviving cell therefore contributes its original
bilinear coefficient once, and each escaped cell contributes only to the boundary term.
For `v=w`, this gives contraction with the exact nonnegative loss, rather than a false
isometry claim. This is a source-independent boundary law, not an arithmetic cancellation bound.

More generally, every observable invariant under the absorbing successor is constant: iterate
the successor `N+1` times to send every vector to zero. This classifies the failure of exact
translation invariance at finite horizon. The signed boundary identity above is its positive
replacement. Also, scalar common commutant does not imply irreducibility; all tail subspaces
are invariant under positive affine maps. No irreducibility assertion is used.

### Exact visibility inside a complete-period observation fibre

[PROVED HERE, paper; Lean pending] Fix the actual finite row `c` and let
`Y_q=selbergMultiplesCoord N c q`, `R_q(M)=Re(pmRamanujanPrimitive q M)`.
Define `V_N(M,c)=Σ_(q=2)^N |R_q(M)Y_q|`. Among all independent Selberg sign changes fixing
the mean, the maximum absolute centered-prefix readout is exactly `V_N(M,c)`, and the diameter
of the readouts is exactly `2 V_N(M,c)`. All these rows have identical complete-period lag
covariances. This is a quantitative classification inside an observation fibre, not a bound
for the Möbius source itself.

Proof: the corpus's exact signed expansion is
`L_N(M,c^ε)=Σ_(q=2)^N ε_q R_q(M)Y_q`. The triangle inequality gives the upper bound.
Choose `ε_q=sign(R_q(M)Y_q)`, with either sign at zero, and choose the opposite signs for the
minimum. Set `ε_1=1` separately, so the mean is preserved. The extrema are `V` and `-V`.
The existing orbit classification identifies these independent sign choices with the complete
period observation fibre. The primitive `R_q(M)` retains the precise horizon dependence;
replacing it by a coarse horizon/period ratio would discard this mode information.

### Dilation of tangent kernels: quantifiers to retain

[PAPER DERIVATION; Lean pending] For `m=floor(T/p)`, rows `v,w` vanishing at zero satisfy

`<D_p v,D_p w>_T = (1/p)<v,w>_m
  - v(m)w(m) [1/(T+1)-1/(p(m+1))]`.

Every complete dilation fibre has exactly `1/p` of its original pronic mass; only the last
incomplete fibre contributes the displayed boundary term. For actual damped receiver rows,
the existing `O(n^(1-ε))` source bound makes this correction `O(T^(-2ε))` for fixed cofactors.
Thus regular variation of the base energy transfers a tangent kernel at horizons `T_n` to a
kernel at `floor(T_n/p)`, with scalar factor `p^(-1-α)`. It does **not** by itself identify
these two tangent kernels. The off-diagonal assertion A3 needs a dilation-stationary extraction
or a proved uniqueness of the tangent; regular variation of the scalar energy proves only the
diagonal law without that additional argument. This is an open quantifier audit, not a claimed
counterexample for the actual Möbius source. Preserve the entire family of tangents before
asserting an isometry law inside one member.

### A finite countermodel to inferring off-diagonal scaling from diagonal scaling

[PROVED HERE, paper; Lean pending] Let `B(x,x)=x₀²+x₁²+x₂²+(2/3)x₀x₁` on `R³`, and let
`P` cyclically permute the three coordinate vectors. Then
`(2/3)|x|² ≤ B(x,x) ≤ (4/3)|x|²`, so every power of `P` distorts `B` by at most a factor 2.
Put `u_j=P^(v₂(j))e₀`, `V_p=p⁻¹P^(v₂(p))` and `K(j,k)=B(u_j,u_k)/(jk)`.
Unique factorization gives the multiplicative action and `V_p(u_j/j)=u_(pj)/(pj)`.
The three vectors at indices 1, 2 and 4 span the whole space, so this is a cyclic rank-three
module, not a merely formal kernel.

It satisfies every coarse cofactor Gram constraint: `K(1,1)=1`, PSD, the radius bound,
and packet dilation contraction `1/p`. For `p≥2`, the last follows from `2/p²≤1/p`; for `p=1`
it is equality. Every diagonal is exactly `K(j,j)=j⁻²`, so all diagonals have the exponent-one
scaling law. Nevertheless `K(1,2)=1/6` whereas `K(2,4)=0`, contradicting homogeneous
off-diagonal scaling by `2⁻²`. On `x=e₀+e₂`, `B(V₂x,V₂x)/B(x,x)=1/3>1/4`, so the stronger
operator contraction also fails.

This model does not claim realization by the actual receiver or a regularly varying scalar
row. It isolates exactly the invalid implication from diagonal scaling plus the existing Gram
constraints to the full A3 identity. Its positive survivor is a complete explicit cyclic
representation with a uniform distortion bound and exact orbit norms. Formalize the exact
countermodel and its positive representation before retiring that implication.

## External calibration

- Joachim Cuntz, *C*-algebras associated with the ax+b-semigroup over N*,
  <https://arxiv.org/abs/math/0611541>: existing operator-algebraic setting for the affine relations.
- Gerard van der Geer and René Schoof, *Effectivity of Arakelov Divisors and the Theta Divisor
  of a Number Field*, <https://arxiv.org/abs/math/9802121>: arithmetic `h⁰` is real-valued; it is
  not an ordinary vector-space dimension. This distinction must survive the new definitions.

## No-go closure

No route retired yet. Every negative result must carry its strongest dependency-closed positive
survivor and a separate paper and Lean audit.

## Worktree preservation

At entry, unrelated edits existed in ADR, AOG, BVI, RHTower and research reports. Preserve them.
New work is confined to this programme and its own pipeline cards unless a required import is
added to a shared umbrella.
