# Zero current-period limit: original source rigidity and flat-node alternative

Status: dependency-closed paper proof and complete Lean audit passed.
RH remains open. Frontier map is read-only.

## Original-source statements

Use the complete congruence Maass source F, density D=||F||², horizontal
first-derivative energy G₁=Σ_q|F_q,x|², and the full period-current limit E₀(y).
Previous work proved E_e(y)→E₀(y)≥0 through common source zeros, with every
pair, phase and regulator-gradient contribution retained.

The following source constraints are now proved:

1. Any nonzero horizontal pair/phase numerator at height y forces E₀(y)>0.
2. If E₀(y)=0, the horizontal pair energy and total phase current vanish at
   every point of that height.
3. At positive density, every component derivative then has the same real
   radial slope: F_q,x=aF_q, where a is the original trace current divided
   by 2D.
4. If D(z)=0 and G₁(z)>0, the complete current has a positive lower bound at
   every sufficiently small regulator. Consequently E₀(Im z)>0 and the
   complete resistance/current product tends to +∞.
5. If E₀(y)=0, every component's horizontal derivative vanishes at every
   common zero at that height. The common real radial derivative law
   therefore extends through all common zeros as well.
6. Bounded resistance/current products at a nodal height force all these
   zero-limit constraints: pair/phase vanishing, a common real radial
   derivative, and vanishing first horizontal derivatives at the nodes.

For an exceptional source with eigenvalue μ∈(0,1/4), actual Maass zero means
supply an additional conclusion:

    A zero-free complete period implies E₀(y)>0.

Equivalently as a proved necessary alternative, every positive height has

    E₀(y)>0  OR  ∃x∈[0,1], D(x+iy)=0 and G₁(x+iy)=0.

The alternatives need not be exclusive. No exceptional source, common zero,
nonzero nodal derivative or zero-energy height is asserted to exist. The
flat-node alternative is retained, not excluded. Flatness here concerns
only the horizontal first derivatives; no vanishing of the full gradient
is established.

## Dependency-closed proof

Write J=pairEnergy₁+phaseCurrent₁²≥0 and, for fixed b>0,

    W_b(x)=J(x+iy)/(D(x+iy)+b²)^(3/2).

For every smaller positive regulator e≤b, decreasing the denominator and
retaining the nonnegative regulator-gradient term gives W_b≤H_e, where H_e
is the complete original horizontal current density. Actual continuity
proves integrability on each complete period. Periodicity identifies the
integral of H_e with E_e(y), regardless of the starting point. Passing to
its proved limit gives

    ∫ₐᵃ⁺¹ W_b(x) dx ≤ E₀(y).

If J(a+iy)>0, continuity and nonnegativity make the left side strictly
positive. Thus E₀=0 forces J=0 at every point, and nonnegativity separates
pairEnergy₁=0 and phaseCurrent₁=0. The exact original Gram identity
D·radialResidual₁=J, together with D>0, makes the residual zero. Its proved
sum-of-squares equality case gives the common real radial derivative for
every component.

At an original node z=a+iy with G₁(z)>0, source derivative continuity gives
d∈(0,1] such that G₁(x+iy)≥k=G₁(z)/2>0 on [a,a+d]. The previous original
nodal amplitude estimate gives a source-dependent L≥1 satisfying
√D(x+iy)≤L(x−a) on [a,a+1]. For e≤d and x∈[a,a+e],

    r_e(x+iy) ≤ (L+1)e,
    H_e(x+iy) ≥ e²G₁(x+iy)/r_e(x+iy)³
               ≥ k/((L+1)³e).

The shrinking interval has length e, so its complete current mass is at
least c=k/(L+1)³>0. Nonnegativity charges that mass to the complete period:
E_e(y)≥c for every sufficiently small e. Passing to the existing full
current limit gives E₀(y)≥c>0. This retains the actual regulator-gradient
term before integration; it assumes no nodal measure and uses no pointwise
current-limit interchange.

Consequently E₀=0 forces G₁=0 at every common zero. Since G₁ is the complete
finite sum of component derivative squared norms, every such derivative
vanishes. The original component value already vanishes there, so the
common radial equation extends through the nodes. Previously proved
logarithmic resistance divergence and strictly positive E₀ give full
product divergence at any nonflat node. The existing bounded-product
criterion E₀=0 gives its stated converse constraint.

Finally suppose an exceptional source has a zero-free complete unit period
and E₀(y)=0. Unit periodicity of D extends zero-freeness to the entire
horizontal line. The original normalized component derivative formula and
the common radial equation give derivative zero for each normalized
component everywhere on that line. The mean value theorem makes every
normalized component constant there. However, the actual Maass zero-mean
and correlation theorem gives, from any positive-density base point, a
same-height point whose normalized squared chord is greater than two.
Constant normalized components give chord zero, a contradiction. Hence
E₀(y)>0 on each zero-free exceptional-source period. If E₀=0 instead,
nonnegativity of D gives a node in the unit period, and the nodal derivative
result makes it flat to first horizontal order.

## Remaining proof obligation

The zero-limit case is now constrained by the original source itself,
rather than by an arbitrary decay rate. It requires a common zero with zero
first horizontal derivative energy, together with horizontal pair/phase
vanishing and the common real radial derivative law. These are necessary
conditions; the reverse implication is not claimed. In particular, a
single flat node does not imply E₀=0, and the radial coefficient has not
been shown regular across zeros.

The original source must supply any further exclusion, rate control or
quantitative lower bound. The quotient-area comparison
`totalOrbitCurvature ≥ amplitudeMass/8` remains open, as does independent
full-Xi spectral occurrence. This does not prove RH or retire the full SQB
candidate. The frontier map remains read-only.

## Broad corpus discovery

Searches used the repository research tool with OR matching, no per-module
cap and full declaration-result retrieval:

- Zero energy, vanishing energy, rigidity, transverse zero, nodal, unique
  continuation: 5,008 rows in 778 modules.
- Concentration, shrinking interval, boundary layer, jump, positive integral,
  local mass: 2,305 rows in 538 modules.
- Local positivity, positive mass, compact minimum, zero integral,
  vanishing derivative: 303 rows in 208 modules.

Counts describe discovery metadata, not proof inspections. Selected source
inspection covered original pair/phase Gram identities, radial residual
equality cases, period current/resistance limits, original nodal amplitude
control, actual Maass component means and negative correlation, current
weight monotonicity, and Mathlib interval positivity, local continuity,
periodic representatives and derivative-zero constancy. Search hits named
unique continuation were not treated as an actual Maass continuation
proof. No numerical experiment or external certificate supplied a result.

Outputs: `/tmp/sqb19_rigidity_broad.json`,
`/tmp/sqb19_local_mass_broad.json`, `/tmp/sqb19_positivity_broad.json`.

## Lean and audit

Module `GaloisForLFunctions.RHTower.SelbergMaassPeriodCurrentRigidity` contains
31 public definitions/theorems. Main results:

- `horizontalWeight_integral_le_limit`
- `periodCurrentLimit_pos_of_numerator`
- `pair_phase_eq_zero_of_limit_zero`
- `component_radial_of_limit_zero`
- `exists_node_current_floor`
- `periodCurrentLimit_pos_of_nonflat_node`
- `component_radial_everywhere_of_limit_zero`
- `periodCost_tendsto_atTop_of_nonflat_node`
- `component_derivative_eq_zero_of_node_bddCost`
- `direction_constant_of_zero_free_limit_zero`
- `exceptional_periodCurrentLimit_pos_of_zero_free`
- `exceptional_exists_flat_node_of_limit_zero`
- `exceptional_positive_limit_or_flat_node`

Complete scratch and final source checks passed without warnings. The
sole-target final build passed; preflight and build logs identify only the
new leaf as requiring compilation. No full or umbrella build ran. Existing
cached EvenL2LogUnitary informational output was replayed.

All 31 public declarations have checked axiom inventories containing only
`propext`, `Classical.choice`, and `Quot.sound`. All 31 are indexed exactly
once, and the module is imported once in the RHTower umbrella. Repository
formal lint passed with existing large-file warnings. No owned compiler
remains. No frontier-map edits, numerical computations, commits or pushes
were made; peer work was preserved.

Logs: `/tmp/sqb19_rigidity_scratch.log`, `/tmp/sqb19_rigidity_source.log`,
`/tmp/sqb19_rigidity_preflight.log`, `/tmp/sqb19_rigidity_build.log`,
`/tmp/sqb19_axioms.lean`, `/tmp/sqb19_axioms.log`,
`/tmp/sqb19_audit_names.txt`, `/tmp/sqb19_index.log`, `/tmp/sqb19_lint.log`.
