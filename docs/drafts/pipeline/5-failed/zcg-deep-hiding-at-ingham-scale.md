# Deep configurations between the Ingham scale and the window scale

- **ID:** zcg-deep-hiding-at-ingham-scale
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** formal/GaloisForLFunctions/ZeroConfigurationGeometry/README.md §6 Q2 (last bullet)
- **Statement:** Two tempered configurations whose union is separated at `g` apart from FE partners,
  and which are mimics at aperture `a > π/(2g)`, coincide, for any mix of depths.

## Goal
Close the factor 2 between the shallow/column threshold `a > π/(2g)`
(`exists_depth_resolving_at_ingham_scale`, `deepColumn_mimic_iff`) and the any-depth threshold
`a > π/g` (`eq_of_weil_eq_of_heightSeparated_of_lt`).

## Reduction (paper)
FE symmetry gives each orbit `{z, 1 − z̄}` the same coefficient `c_k ∈ ℤ`. With `γ = t_k ∓ iδ_k`,
mimicry at aperture `a` is the vanishing on `(−2a, 2a)` of the weighted exponential sum
`S(v) = Σ_k c_k cosh(δ_k v) e^{i t_k v}` (on-line orbits carry weight `1/2`). Tested against
`φ ∈ C_c^∞(−2a, 2a)` with `φ` real and even, this reads `Σ_k c_k Re φ̂(t_k + iδ_k) = 0`. Each orbit
imposes one real condition on `φ̂`, an entire function of type `2a`, real on `ℝ`, with real-zero
density `2a/π`. The count therefore puts the threshold at `2a/π > 1/g`, which is the Ingham scale.

## The tested mechanism: parity windows plus the tilted block Ingham inequality
- **Parity windows do not reach it.** The FE pair at site `k` has the image
  `F̂(λ)Ĝ*(λ) + F̂(λ̄)Ĝ*(λ̄)`, with `Ĝ*(w) = conj Ĝ(conj w)`. Every way of killing it by zeros costs
  two zeros in total across `F, G`: `F̂(λ) = F̂(λ̄) = 0`, or `F̂(λ) = Ĝ(λ) = 0`, or the conjugate
  choices. The diagonal window kills the pair with the single zero `f̂(λ) = 0`, but cannot be split
  by parity. So a deep site always needs zero density `1/g` per window, hence `a > π/g`. Parity
  splitting gains the factor 2 only on on-line orbits, which need one zero per site.
- **The tilted block Ingham inequality covers only shallow depth.** FE symmetry gives `p_k = q_k`,
  so the aligned alternative `Re(p_k q̄_k) ≥ 0` of `block_ingham_inequality` holds at every site.
  The inequality still needs `2·sqrt((π/(2V))² + 4s²) < g`, that is depth `s < g/4`.
- **The two combine only partially.** A diagonal window `E` with one zero per deep orbit (density
  `ρ_d`) multiplies the shallow terms by the nonvanishing weight `Ê Ê*`. The tilted Ingham
  inequality then resolves the shallow orbits on the remaining aperture. This gives identification
  for `a > πρ_d + π/(2g)`, which interpolates between the two thresholds. It does not close the gap
  when deep orbits have density `≍ 1/g`.

## Periodic patterns
For configurations of period `Ng` with depths `δ_r`, Poisson summation reduces mimicry at aperture
`a` to `Σ_r c_r cosh(δ_r v_m) ω^{rm} = 0` for all `v_m = 2πm/(Ng)` with `|v_m| < 2a`. With
`P_r = cosh(2πδ_r/(Ng))` the weights are Chebyshev values `T_m(P_r)`.
- `N ≤ 4`: the weights `cosh > 0` force `c = 0` just above the Ingham scale. For `N = 3` the
  `m = 1` equation makes `c_r P_r` constant, and then `m = 0` is a sum of terms of one sign. For
  `N = 4`, `m = 1` pairs the residues mod 2, while `m = 0` and `m = 2` demand opposite and equal
  signs of the two pair values.
- `N = 5`: the `5 × 5` determinant changes sign on `[1, ∞)⁵` (high-precision check), so real
  weights hide up to `3π/(5g)`.
- `N = 6`, symmetric residue classes `0, ±1, ±2, 3`: the cosines `cos(πrm/3)` are rational, and the
  `4 × 4` determinant vanishes at many rational points `P`, giving integer weights. One of them is
  `P = (367/6, 8, 5/3, 3/2)` with weights `(29, 6016, −50995, 89929)`, which hides up to
  `2π/(3g)`. With rows `m ≤ 4`, real solutions exist (`σ_min ≈ 10⁻⁴⁵` at 50 digits, e.g.
  `P = (1, 2.302, 59.93, 32.47)`), so real weights hide up to `5π/(6g)`. A search on `[1, 60]⁴`
  found no solution for rows `m ≤ 5`.

## No-go closure
- **Exact killing theorem:** `not_eq_of_mimic_at_ingham_scale` (Lean,
  `MixedDepthsHideBeyondTheInghamScale.lean`). The pair `mixedZ`, `mixedZ'` at `L = 734`,
  `g = 2π/L`, consists of tempered, disjoint, nonempty configurations. Their union is separated at
  `g` apart from FE partners, and they are mimics at every aperture `a < 2π/(3g)`
  (`mixedDepth_mimics_beyond_ingham`).
- **Strongest positive survivor:** configurations of one depth are resolved at the Ingham scale
  (`eq_of_mimic_of_oneDepth`; card `zcg-one-depth-resolved-at-ingham-scale`, formalized). So are
  shallow configurations (`eq_of_weil_eq_of_shallow`) and deep columns (`deepColumn_mimic_iff`).
- **New insight:** the threshold depends on the depth structure. One depth: `π/(2g)`, sharp. Mixed
  depths: in `[2π/(3g), π/g]`, with `π/g` proved sufficient. The factor `cosh(δ_r v)` is common to
  all sites at one depth and divides out of the test function. With different depths the weights
  give each residue an independent profile, and these profiles pay for the extra lag conditions.
- **Status:** killing theorem and survivor formalized, unconditional (`#print axioms`: `propext`,
  `Classical.choice`, `Quot.sound`). Open: the sharp mixed-depth threshold in `[2π/(3g), π/g]`.

## Positive survivor: configurations of one depth (Lean)
Tempered mimics at `a > π/(2g)` whose union lies at one depth `|Re ρ − ½| = δ` coincide
(`eq_of_mimic_of_oneDepth`; paper proof and Lean names on card
`zcg-one-depth-resolved-at-ingham-scale`).

*Insight.* Averaging the modulated lag identity over the modulation removes the asymmetry of the FE
pair weights `ĥ(t ∓ iδ)` and recovers the depth profile `cosh(δv)` exactly. So Q2 is the weighted
Ingham problem for `S(v) = Σ_k c_k cosh(δ_k v) e^{it_k v}`, with the depth entering only through
the weights. At one depth the weight divides out of the test function. Mixed depths (columns against
on-line lattices are the extremal case) remain open.

## Gates
- [x] 0 → 1  in-progress: reduction to the cosh-weighted exponential sum; mechanism tested
- [x] falsified: `not_eq_of_mimic_at_ingham_scale`
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Log
- 2026-11-04 — created; parity-plus-tilted-Ingham test recorded
- 2026-11-05 — one-depth survivor formalized; conjecture falsified in Lean for mixed depths
