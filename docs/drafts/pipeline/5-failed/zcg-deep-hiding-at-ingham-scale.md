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
  `2π/(3g)`. With rows `m ≤ 4`, the slice `P₀ = 1` reduces to a genus-one quartic with the rational
  point `P = (1, 11381/3358, 2131/73, 30292/1679)`, which hides up to `5π/(6g)` (card
  `zcg-mixed-depths-hide-beyond-ingham`). Searches on `[1, 60]⁴` (symmetric) and `[1, 60]⁶` found
  no solution for rows `m ≤ 5`.
- Larger periods, real weights (minimum singular value of the column-normalized system on
  `[1, 60]^N`, solutions at `σ ≈ 10⁻¹⁸`, none where the minimum sits on the box boundary): the
  largest order found is `K = 2, 4, 4, 5, 6, 7` for `N = 5, 6, 7, 8, 9, 10`, i.e. hiding ratios
  `(K + 1)/N = 0.6, 0.83, 0.71, 0.75, 0.78, 0.8` of `π/g`. The ratio grows with `N`, consistent
  with `π/g` being sharp for real weights. Integer weights need rational rows, which period `6`
  provides.
- Period `6` with rows `m ≤ 5` (aperture up to `π/g`): with all six depths free in `x_r ∈ [0, 20]`,
  every small singular value found sits at the boundary `x = 20`, a degenerate limit in which one
  column tends to the top row. No interior solution. For `N = 2, 3, 4` the order `K = N − 1` is
  excluded by the sign arguments above. A period-`N` pattern hides only below
  `(N − 1)π/(Ng)`, i.e. `K ≤ N − 2` (card `zcg-periodic-patterns-last-lag`, Lean
  `eq_zero_of_lagSymbol_eq_zero`); so `5π/(6g)` is exact for period `6`.
- **Integer weights (count).** Fix the integer weights `C` and solve for the depths. A pattern
  with residue classes of equal depth and weight has `c` free depth cosines and, at lag order `K`,
  `K` real conditions beyond `Σ C = 0` (symmetric patterns have real rows), so generically
  `K ≤ c`. Symmetric period `N` has `c = ⌊N/2⌋ + 1`, and with `K ≤ N − 2` the hiding ratio
  `(K + 1)/N` is at most `4/5, 5/6, 5/7, 3/4` for `N = 5, 6, 7, 8` and tends to `1/2`.
  Non-symmetric patterns have `2K` conditions on `N` depths, ratio at most `1/2 + 1/N`. Conjecture:
  separated configurations with integer weights are resolved above `5π/(6g)`, so that
  `mixedDepth_five_sixths_sharp` is the sharp mixed-depth threshold. Real weights, which escape the
  count, reach `(N − 1)/N`.
- **Reduction of the extreme order (paper).** Take `K = N − 1` with all `x_r > 0`. Then the
  `2N` nodes `ζ = e^{±x_r} ω^r` carry a unique linear relation on Laurent polynomials of degree
  `≤ N − 1`, the space of the `2N − 1` conditions, with weights `ζ^{N−1}/P'(ζ)`,
  `P = Π_r (z − e^{x_r}ω^r)(z − e^{−x_r}ω^r)`. A period pattern realizes it exactly when the two
  weights of every residue agree. With `q_s(e^y ω^r) = 2ω^{r+s}e^y (cosh(y + iθ_{r−s}) − cosh x_s)`
  this becomes: every `A_r = Π_{s≠r}(cosh(x_r + iθ_{r−s}) − cosh x_s)` is purely imaginary. The
  weights are then `C_r ∝ 1/(sinh(x_r) A_r)`, automatically real. So hiding at the extreme order is
  the real `N × N` system `Re A_r = 0`.
- Numerically, `min_x Σ_r cos²(arg A_r)` equals `4 sin²(π/N)` for `N = 4, 6, 7, 8` (`2, 1, 0.753,
  0.586`; depths up to `300`, least squares from 250–400 starts). For `N = 5` the best value found
  is `1.69`. Unsolvability is now a theorem (next card); the defect values tend to `0`,
  consistent with `π/g` being approached only as the period grows. At one depth every `A_r` is
  real, since the factors for `s` and `2r − s` are conjugate.

## No-go closure
- **Exact killing theorem:** `not_eq_of_mimic_at_ingham_scale` and
  `not_eq_of_mimic_below_five_sixths` (Lean, `MixedDepthsHideBeyondTheInghamScale.lean`). The pair `mixedZ`, `mixedZ'` at `L = 734`,
  `g = 2π/L`, consists of tempered, disjoint, nonempty configurations. Their union is separated at
  `g` apart from FE partners, and they are mimics at every aperture `a < 2π/(3g)`
  (`mixedDepth_mimics_beyond_ingham`). The pair `mixedZ4`, `mixedZ4'` hides up to `5π/(6g)`
  (`mixedDepth_mimics_to_five_sixths`).
- **Strongest positive survivor:** configurations of one depth are resolved at the Ingham scale
  (`eq_of_mimic_of_oneDepth`; card `zcg-one-depth-resolved-at-ingham-scale`, formalized). So are
  shallow configurations (`eq_of_weil_eq_of_shallow`) and deep columns (`deepColumn_mimic_iff`).
- **New insight:** the threshold depends on the depth structure. One depth: `π/(2g)`, sharp. Mixed
  depths: in `[5π/(6g), π/g]`, with `π/g` proved sufficient. The factor `cosh(δ_r v)` is common to
  all sites at one depth and divides out of the test function. With different depths the weights
  give each residue an independent profile, and these profiles pay for the extra lag conditions.
- **Status:** killing theorem and survivor formalized, unconditional (`#print axioms`: `propext`,
  `Classical.choice`, `Quot.sound`). Open: the sharp mixed-depth threshold in `[5π/(6g), π/g]`.

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
