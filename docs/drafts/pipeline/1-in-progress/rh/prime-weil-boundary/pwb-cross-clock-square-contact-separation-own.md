# PW-B cross-clock forcing is not a renormalized square contact

- **ID:** PWB-cross-square-separation
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper; Lean pending)
- **Statement:** For every `q : XiZeroCopy` and `c : ℂ`, the positive-height covector fields `crossBranchForcingCovector q` and `c • fullSquareCovector q` are unequal.

## Proof-chain role

Literal complementary source legs → cross-rate metric forcing → **new ordered contact sector**, not a scalar renormalization of the one-branch square contact → metric/CTP boundary incidence → oriented optical extinction → RH. This kills only a constant-normalization identification, not differential, nonlocal, or genuinely ordered contacts.

## Paper proof

Use the notation and spectral rigidity proof in [the cross-clock forcing card](../../pwb-cross-branch-clock-forcing-own.md): `H=U_true U_false`, `D=(Δ−20)H`, `Q=fullSquarePotential q`, and `β=sourceGrowthExponent q∈[1,2)`. The corpus proves `crossBranchForcingCovector=coexact D` and `fullSquareCovector=coexact Q`. If the stated fields agreed, both coordinate derivatives of `D−cQ` would vanish on the connected upper half-plane. Thus

`(Δ−20)H = cQ + C` for one constant `C∈ℂ`.

Let `h(y)` and `m(y)` be width-one horizontal means of `H` and `Q` above height `3`. Periodicity and smoothness yield `y²h''−20h=c m+C`. The corpus's full-square growth law gives `|m(y)|≤A y^β`. Variation of constants for homogeneous powers `y⁵,y⁻⁴` produces a particular solution `O(y^β)`: its two integrals are bounded by `y⁵∫_y^∞t^(β−6)dt` and `y⁻⁴∫_3^y t^(β+3)dt`. The weighted `L¹(y⁻⁴)` bound on `H` from the first card excludes the free `y⁵` term. Hence `h(y)=O(y^β)` and `∫_3^∞|h(y)|y^(−β)dy/y²<∞`.

On the same cusp, `H=(K_true+R_true)(K_false+R_false)`. Each `R_b` is in hyperbolic `L²`, and `|K_b(y)|≤A_b y^β`. By Cauchy–Schwarz and finite cusp volume, all three error terms `K_true R_false`, `R_true K_false`, and `R_true R_false` have finite `L¹(y⁻β)` mass. Therefore the previous bound on `h` would make `∫_3^∞|K_true K_false|y^(−β)dy/y²` finite.

That is impossible. Off the line, the leading `2q` or `2−2q` Weyl coefficient is nonzero on **both** branches by the corpus's zero-free-side coefficient, nonzero branch parameter, and nonresonant denominator laws; `|K_b|≥a y^β` eventually. On the line, `K_b/y` is a nonzero periodic exponential polynomial in `log y` on each branch; their common nonzero intervals recur periodically. In either case `|K_true K_false|y^(−β)dy/y²` has divergent mass (`y^(β−2)dy`, at least logarithmic). Contradiction.

## Audit status

- Corpus declarations inspected: `fullSquarePotential_coexact`, `fullSquarePotential_global_growth`, `sourceGrowthExponent_bounds`, `cuspResponse_eq_sum`, `denominator_ne_zero`, `globalResponse_ae_lift`, and the cross-rate product equation.
- Paper proof only. Lean statement and targeted audit remain pending under the OOM constraint. No equality with literal CTP or optical flux is claimed.
