# Original current-period limit and joint path costs

Status: dependency-closed paper proof and complete Lean audit passed.
RH remains open. Frontier map is read-only.

## Full original-source result

Let F be the complete finite congruence Maass source, D=||F||², y>0,
r_e=√(D+e²), and

    H_e = (pairEnergy₁ + phaseCurrent₁² + e² directionalEnergy₁)/r_e³,
    E_e(y) = ∫₀¹ H_e(x+iy) dx.

Define original source quantities

    A_x(z) = Re Σ_q F_q,xx(z) conjugate(F_q(z)),
    B_x(z) = Σ_q |F_q,xx(z)|,
    E₀(y) = −∫₀¹ A_x(x+iy)/√D(x+iy) dx.

The quotient at a common source zero is zero; its numerator already
vanishes there. Then, at every positive height, without a zero-free premise,

    E_e(y) = −∫₀¹ A_x(x+iy)/r_e(x+iy) dx,
    E_e(y) → E₀(y),
    0 ≤ E₀(y) ≤ ∫₀¹ B_x(x+iy) dx,
    0 ≤ E_e(y) ≤ ∫₀¹ B_x(x+iy) dx.

All displayed integrals are genuinely integrable. Original C² regularity
constructs the integrable majorant. No separate derivative bound, current
integrability or regulator-limit hypothesis is assumed.

The limiting expression represents the complete current integral, including
nodal concentration. It is not the integral of the pointwise limit of H_e.
It retains the original full finite-family pairing and exact periodic
boundary cancellation.

## Joint resistance/current products

Put R_e(y)=∫₀¹1/r_e and C_e(y)=R_e(y)E_e(y), with R₀ the literal reciprocal
integral when the period is zero-free. The original resistance classification
gives the following fully proved conclusions:

- On every zero-free period, C_e(y)→R₀(y)E₀(y).
- If the period contains a common zero and E₀(y)>0, then C_e(y)→+∞.
- At an original common-zero height, boundedness of the full family C_e(y)
  requires E₀(y)=0.
- With E₀(y)>0, divergence of C_e(y) is equivalent to existence of an
  original common zero in [0,1].

No original common zero or strict positivity of E₀ is asserted to exist.
When R_e→∞ and E₀=0, the product's behavior still depends on relative rates.
The finite limit of E_e alone does not decide that case.

Let m be the original finite-group source mean, y'=Im(S⁻¹z), and
M_N=N(2N+1)/12. If both complete periods at y=Im(z) and y' are zero-free,
the original complete block comparison has the exact regulator-free limit

    K_e(z) → M_N [R₀(y)E₀(y)+R₀(y')E₀(y')],
    D(z) ≤ |Deck N||m(z)|²
      +16 D(z) M_N [R₀(y)E₀(y)+R₀(y')E₀(y')].

For D(z)>0 and m(z)=0 this gives the sharper limiting requirement

    1 ≤ (4/3)N(2N+1) [R₀(y)E₀(y)+R₀(y')E₀(y')].

The two original period zero-freeness conditions are retained. This is not
an extension across nodal heights or a uniform bound over varying sources.

## Dependency-closed proof

1. Differentiate each literal component squared norm twice horizontally:

       (|F_q|²)_xx = 2(|F_q,x|² + Re(F_q,xx conjugate F_q)).

   Finite summation gives D_xx=2(G_x+A_x), where G_x is full horizontal
   derivative energy. Differentiating r_e²=D+e² gives
   D_xx=2(r_e,x²+r_e r_e,xx). The proved regularized energy decomposition
   G_x=r_e,x²+directionalRemainder₁ therefore implies

       r_e,xx = H_e + A_x/r_e.

   This identity holds at common source zeros as well.

2. The actual regulated radius is C² and has unit horizontal period.
   Its horizontal derivative is periodic, and the fundamental theorem of
   calculus cancels ∫₀¹r_e,xx exactly. Continuity of all regulated terms
   proves integrability before splitting the integral. This yields the
   complete signed-acceleration representation of E_e.

3. Every original coordinate satisfies |F_q|≤√D. The triangle inequality
   and complex norm product give

       |A_x| ≤ B_x√D ≤ B_x r_e,
       |A_x/r_e| ≤ B_x.

   At D=0, the first inequality forces A_x=0. Off that locus, r_e→√D>0;
   at the locus, the numerator vanishes for every regulator. Thus A_x/r_e
   tends pointwise everywhere to the literal zero-extended quotient.
   That quotient is measurable and also bounded by B_x. Original C²
   regularity makes B_x continuous on each compact horizontal interval,
   hence integrable. Dominated convergence applies to the signed expression
   and establishes the complete current limit through common zeros.

4. Nonnegativity of each retained E_e passes to E₀. Integration of the
   same majorant bounds every E_e and E₀ by the actual acceleration budget.
   These are source-derived statements; the majorant is not assumed.

5. Multiply the proved finite limits on zero-free periods. At a nodal
   height, previous logarithmic resistance divergence times a strictly
   positive finite E₀ gives C_e→∞. Hence bounded nodal products require
   E₀=0. Conversely, a zero-free period has a finite product limit, excluding
   divergence. This establishes the stated joint classification while
   retaining the undecided zero-current-limit case.

6. Substitute both zero-free product limits into the exact complete block
   identity. The original density comparison holds for every positive
   regulator; passing to its finite right-side limit replaces D+e² by D.
   With positive D and zero original mean, divide the resulting inequality
   by D and substitute M_N=N(2N+1)/12. No factor-two regulator estimate is
   needed in this exact limiting comparison.

## What remains in the full proof chain

Original source → independent current comparison or full-Xi spectral
occurrence → critical-line classification → RH remains the active objective.

The current factor is now controlled jointly with resistance wherever its
finite limit or strict positivity decides the product. Nodal products with
zero limiting current still require relative rates. The original invariant
mean, varying heights, level factor and nodal curvature remain present.
The passage to a quotient-area lower bound strong enough for
`totalOrbitCurvature ≥ amplitudeMass/8` remains open. Independent full-Xi
spectral occurrence remains open as well. No complete route is retired.

## Broad corpus discovery

All four searches used the repository research tool, OR matching, no
per-module cap and full declaration-result retrieval:

- Weighted length, arc length, resistance energy, capacity, Cauchy defect,
  weighted variation: 2,495 rows in 367 modules.
- Transverse zero, simple zero, nodal, boundary layer, concentration:
  1,480 rows in 324 modules.
- Oscillation, harmonic mean, Poincare, coarea, isoperimetric, Cheeger:
  2,478 rows in 375 modules.
- Acceleration, second derivative, periodic integration, boundary
  cancellation, signed curvature: 1,041 rows in 430 modules.

Counts describe discovery metadata, not proof inspections. Source inspection
covered complete original unipotent paths, original period resistance,
trace energy/direction/regularization, source currents, retained current
density and regulator convergence, scalar horizontal averages, regularized
cusp periodicity, and the exact toy nodal-curvature profile. The generic
periodic boundary cancellation and source norm-square second derivative
were the decisive reusable theorems. The toy current limit was not promoted
to an actual Maass result. Mathlib dominated-convergence, interval-integral
and product-limit APIs were checked in scratch on this toolchain.
No numerical experiment or external certificate supplied a proof result.

Search outputs: `/tmp/sqb18_product_broad.json`,
`/tmp/sqb18_nodal_broad.json`, `/tmp/sqb18_area_broad.json`,
`/tmp/sqb18_acceleration_broad.json`.

## Lean and audit

Module `GaloisForLFunctions.RHTower.SelbergMaassPeriodCurrentLimit` has 33
public definitions/theorems plus two local square-differentiation helpers.
Main results:

- `radius_horizontal_second`
- `periodCurrentEnergy_eq_acceleration`
- `sourceAccelerationDensity_intervalIntegrable`
- `acceleration_integral_tendsto`
- `periodCurrentEnergy_tendsto`
- `periodCurrentEnergy_le_accelerationBound`
- `periodCost_tendsto_of_zero_free`
- `periodCurrentLimit_eq_zero_of_node_bddCost`
- `periodCost_tendsto_atTop_iff_node`
- `blockPathCost_tendsto_of_zero_free`
- `density_le_mean_add_limiting_periods`
- `limiting_period_cost_lower_of_mean_zero`

Complete scratch and final source checks passed without warnings. The final
sole-target build passed; preflight and build logs show only the new leaf
requiring compilation. No full or umbrella build ran. Cached informational
output from EvenL2LogUnitary was replayed.

All 33 public declarations have checked axiom inventories containing only
`propext`, `Classical.choice`, and `Quot.sound`; their dependencies include
the two local differentiation helpers. All 33 public declarations are
indexed exactly once, alongside the two helpers. The module is imported
once in the RHTower umbrella. Repository formal lint passed with existing
large-file warnings. No frontier-map edits, numerical computations,
commits or pushes were made. Peer work was preserved.

Logs: `/tmp/sqb18_current_limit_scratch.log`,
`/tmp/sqb18_current_limit_source.log`, `/tmp/sqb18_current_limit_preflight.log`,
`/tmp/sqb18_current_limit_build.log`, `/tmp/sqb18_axioms.lean`,
`/tmp/sqb18_axioms.log`, `/tmp/sqb18_audit_names.txt`,
`/tmp/sqb18_index.log`, `/tmp/sqb18_lint.log`.
