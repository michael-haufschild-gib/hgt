# Full closed-period resistance/current product

Status: dependency-closed paper proof and complete Lean audit passed.
RH remains open. Frontier map is read-only.

## Exact original-source result

Let f be the actual nonzero principal-congruence Maass cusp eigenform with
eigenvalue 0<μ<1/4. Put w=N+1. Retain every coordinate F_q of its finite
congruence source, and define

    D = Σ_q |F_q|²,       r_ε = sqrt(D+ε²),       u_ε = (ε,F)/r_ε,
    H_ε = (pairEnergy_x + phaseCurrent_x² + ε² directionalEnergy_x)/r_ε³,
    R_ε(y) = ∫₀¹ 1/r_ε(x,y) dx,
    E_ε(y) = ∫₀¹ H_ε(x,y) dx,
    C_ε(y) = R_ε(y) E_ε(y).

The full original vector u_ε closes after period w. The scalar integrands
1/r_ε and H_ε have period one. These periods are used separately.

At every y>0 there exist r>0 and c>8 such that

    0<ε≤r  ⇒  c ≤ w² C_ε(y).

Both r and c may depend on the actual source, level and height. No common
node, nodal order, zero-free period, positive limiting current or bounded
product is supplied as an extra hypothesis. The theorem uses the original
eigenform data; it does not assert that an exceptional eigenform exists.

Consequently:

1. The complete product cannot tend to zero.
2. Every finite product limit L satisfies 8<w²L.
3. For all sufficiently small regulators,
   E_ε(y)>8/(w²R_ε(y)).
4. On a zero-free unit period, the already identified exact limit
   R₀(y)E₀(y) satisfies 8<w²R₀(y)E₀(y).
5. If the full current limit E₀(y) is zero, E_ε(y) still tends to zero while
   retaining the same fixed positive product floor and reciprocal-resistance
   lower rate.

## Complete proof

Take a<b<a+w. The original weighted chord inequality applies on both arcs
[a,b] and [b,a+w]. Let d_ε=|u_ε(a,y)−u_ε(b,y)|². Full-vector closure makes
this the squared chord of the second arc as well. With R₁,R₂>0 the two arc
resistances and E₁,E₂ their complete current energies, the inequalities are

    d_ε ≤ R₁E₁,       d_ε ≤ R₂E₂.

Multiply the first by R₂ and the second by R₁, then add:

    d_ε(R₁+R₂) ≤ R₁R₂(E₁+E₂).

Multiplying by R₁+R₂ and using
d_ε(R₁−R₂)²≥0 gives

    4d_ε ≤ (R₁+R₂)(E₁+E₂).

All arc integrals split exactly. Exact integer-period scaling identifies
the right side with w²C_ε(y). Every pair/phase term and the regulator term
ε² directionalEnergy_x are retained in E₁,E₂.

At the fixed positive height, original slice rigidity supplies a point z
with D(z)>0. Original zero means then supply t in the centered interval
[Re(z)−w/2,Re(z)+w/2] with negative original correlation

    κ = Re Σ_q F_q(z) conjugate(F_q(t,y)) < 0.

The points are distinct. Ordering their horizontal coordinates gives
a<b<a+w, with the same correlation. Put

    Q = r₁(z)r₁(t,y)>0,
    δ = −κ/Q>0,
    r = min(1,sqrt(−κ)/2)>0.

For 0<ε≤r, monotonicity of the original radii gives
r_ε(z)r_ε(t,y)≤Q, while ε²≤−κ/4. The exact augmented correlation identity is

    κ+ε² = r_ε(z)r_ε(t,y) Re⟨u_ε(z),u_ε(t,y)⟩.

Since δQ=−κ, these inequalities imply

    δ ≤ −2 Re⟨u_ε(z),u_ε(t,y)⟩.

The actual augmented vectors have unit norm, so d_ε≥2+δ. The two-arc
comparison now gives

    8+4δ ≤ w²C_ε(y).

This supplies c=8+4δ>8 for every sufficiently small regulator. Positivity
of R_ε permits division to obtain the current lower rate. Passing this
fixed c through any finite product limit proves its strict threshold.
The existing full-current convergence and zero-free product convergence
give the remaining consequences. All limits use the complete integrated
current, including any nodal concentration.

## Consequences and remaining gap

The vanishing-current alternative cannot discard the joint product. A
positive product floor can coexist with E_ε→0 when R_ε diverges; no upper
bound or finite limit of that product is asserted. Common flat nodes and
zero limiting current remain unexcluded. The constant eight is a proved
lower threshold after level-period scaling; no optimality claim is made.

This result supplies no uniform quotient-area quarter comparison and no
independent full-Xi spectral occurrence. Those remain required in the full
SQB proof chain. RH is not proved or falsified.

## Broad corpus discovery

Repository research-tool searches used OR matching, no per-module cap and
complete declaration-result retrieval:

- Joint limits, effective resistance, capacity, closed curves, two arcs,
  periodic Poincaré and finite-order zeros: 2,517 rows in 367 modules.
- Weighted means, zero means, chords, loop energy, Wirtinger and Lyapunov
  inequalities: 1,004 rows in 276 modules.

These are metadata counts, not claims that every proof was inspected.
The finite-current completion in `StokesCartanCoronaCapacity.lean` supplied
an independently inspected algebraic lead. The new proof acts directly on
the two original source arcs and does not import a generic tree model.
Selected source reads also covered actual augmented correlation, original
path Cauchy bounds, scalar periodicity, exact integer periods and slice
mass rigidity. `CirclePoincareWirtinger.lean` was located by metadata but
was not used. No numerical or nodal-order experiment was performed.
Search outputs: `/tmp/sqb22_capacity_broad.json`,
`/tmp/sqb22_loop_broad.json`.

## Lean audit

Module: `GaloisForLFunctions.RHTower.SelbergMaassClosedPeriodProduct`.
It contains 21 public theorems. Main results:

- `two_arc_effective_resistance`
- `four_chord_le_level_product`
- `uniform_chord_margin_of_negative_correlation`
- `source_period_product_floor`
- `finite_product_limit_strict_lower`
- `period_product_not_tendsto_zero`
- `zero_current_retains_product_floor`

Scratch and canonical source checks passed without warnings:
`/tmp/sqb22_product.lean`, `/tmp/sqb22_product.log`,
`/tmp/sqb22_product_source.log`. Both used `lake env lean`.

Preflight found only the intended leaf stale. Final audit
`lake build GaloisForLFunctions.RHTower.SelbergMaassClosedPeriodProduct`
passed, compiling that module in 4.3 seconds. The remaining jobs in the
8,822-job dependency graph were cached. No full or umbrella build ran.
Logs: `/tmp/sqb22_product_preflight.log`, `/tmp/sqb22_product_build.log`.

All 21 declarations were individually checked in `/tmp/sqb22_axioms.lean`.
Every inventory contains only `propext`, `Classical.choice` and `Quot.sound`
(`/tmp/sqb22_axioms.log`). No proof hole, added axiom, unsafe declaration
or external computational result was introduced. The module is wired
once into `RHTower.lean`.

All 21 public theorems are indexed exactly once
(`/tmp/sqb22_indexed_declarations.json`). Index and formal lint passed
(`/tmp/sqb22_index.log`, `/tmp/sqb22_lint.log`); lint reported only existing
large-file warnings. Whitespace checks passed. No Lean/Lake process remains
from this work. This work made no edits to the read-only frontier map.
