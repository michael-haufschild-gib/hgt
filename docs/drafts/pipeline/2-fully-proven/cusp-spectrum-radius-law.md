# The Cusp–Spectrum Radius Law for the Selberg class

- **ID:** cusp-spectrum-radius-law
- **Stage:** 2-fully-proven (paper proof complete; independent of Selberg's conjectures)
- **Type:** THEOREM (paper)
- **Source:** `../1-in-progress/selberg-orthogonality-working-log.md` §§13.1, 14.1, 23.1, 24.2, 25
- **Statement:** the shift-lattice expansion of the degree-`d` theta function of `F ∈ S^♯` at any
  base point has radius of convergence exactly the distance from that point to the rest of the
  standard-twist spectrum; at the cusp this reads `d q^{−1/d}`.

## Statement

Let `F ∈ S^♯` have degree `d ≥ 1` and conductor `q`. Put
```
Φ_F(s,z) := Σ_{n≥1} a_F(n) n^{−s} e(z n^{1/d})        (z ∈ H),
F_α(w)   := Σ_{n≥1} a_F(n) n^{−w} e(−α n^{1/d})       (the K–P standard twist; F_0 = F),
Δ(α₀)    := dist( α₀ , Spec(F) \ {α₀} ) ,             Spec(F) = { d(m/q)^{1/d} : a_F(m) ≠ 0 }.
```

> **Theorem.** For every `s ∈ C` off the exceptional lattice `{s*_ℓ + k/d}` and every `α₀ ≥ 0`,
> ```
> limsup_{k→∞} | F_{α₀}(s − k/d) / k! |^{1/k}  =  1 / ( 2π Δ(α₀) ) .
> ```
> Equivalently, `Φ_F(s, −α₀+ζ) − (explicit singular part at α₀) = Σ_{k≥0} ((2πiζ)^k/k!) F_{α₀}(s−k/d)`
> with radius of convergence exactly `Δ(α₀)`.
>
> **Cusp case.** Since `a_F(1) = 1`, `Δ(0) = min Spec(F) = d q^{−1/d}`, so
> `limsup_k |F(s−k/d)/k!|^{1/k} = q^{1/d}/(2πd)`.

## Proof

1. **The expansion.** Mellin–Barnes: `e^{−x} = (2πi)^{−1}∫_{(c)}Γ(u)x^{−u}du` with
   `x = −2πiζ·n^{1/d}` (legitimate, `Re(−2πiζ) = 2π Im ζ > 0`) gives, for `c` large,
   `Φ_F(s,−α₀+ζ) = (2πi)^{−1}∫_{(c)} Γ(u)(−2πiζ)^{−u} F_{α₀}(s+u/d) du`.
   Shifting to `Re u = −M` crosses `u = 0,−1,−2,…` (poles of `Γ`, giving the displayed power series)
   and the poles of `F_{α₀}` — at `u = d(1−s)` when `α₀ = 0` (the pole of `F` at `1`, giving `P_F`),
   at `u = d(s*_ℓ − s)` when `α₀ ∈ Spec(F)` (giving the `ℓ`-sum with exponents `d(s−s*_ℓ)`).
   The singular part is singular only at `ζ = 0`.
2. **Radius = distance to the nearest other singularity.** `Φ_F(s,·)` is holomorphic on `H`;
   by K–P it continues across every boundary point `−α` with `α ∉ Spec(F)` (there `F_α` is entire in
   `s`), and by the jump lemma it is genuinely singular at `−α` for `α ∈ Spec(F)`:
   `sup_{|s−s*_0|=r}|F_{α}(s) − F_{α'}(s)| ≥ |ρ_0(α)|/r > 0` for all `α' ∉ Spec(F)`, because
   `∮ F_{α'} = 0` while `∮ F_α = 2πi ρ_0(α) ≠ 0` (K–P: `ρ_0(α) ≠ 0` on the spectrum).
   Hadamard's formula for the radius then gives the stated `limsup`.
3. **Cusp constant, independently.** By the functional equation and uniform Stirling, for `σ → −∞`
   with `t` fixed, `|X(σ+it)| ≍ C[q/(2π)^d]^{|σ|}|σ|^{d|σ|}e^{−d|σ|}` and `|F(1−s)| → 1`; with
   `|σ| = k/d + O(1)` and `k! ≍ (k/e)^k` this yields `|F(s−k/d)/k!|^{1/k} → q^{1/d}/(2πd)`,
   matching `1/(2πΔ(0)) = q^{1/d}/(2πd)`. The two computations use **disjoint data** — the first only
   the archimedean invariants, the second only `a_F(1)=1` and the location of the first prime-side
   singularity — so their agreement is a local–global identity.

## Verifications (all exact, with constants)

| `F` | `d` | `q` | predicted radius | independent check |
|---|---|---|---|---|
| `ζ` | 1 | 1 | 1 | Lerch `Σ n^{−s}e(nz)` singular exactly on `Z` ✓ |
| `L(·,χ)`, `χ` mod `q` | 1 | `q` | `1/q` | singularities on `(1/q)Z` ✓ |
| `L(·,Δ)` level 1 | 2 | 1 | 2 | `Γ`-computation gives `limsup = 1/(4π)` ✓ |
| level-1 Maass, any `r` | 2 | 1 | 2 | `Γ_R Γ_R` computation gives `1/(4π)`, independent of `r` ✓ |

## Consequences

- **Lower bound on the far-left growth of the standard twist.** `Δ(α_m) ≍ q^{−1}(α_m/d)^{1−d} → 0`
  for `d ≥ 2`, so `limsup_k |F_{α_m}(s−k/d)/k!|^{1/k} ≍ q(α_m/d)^{d−1}/2π → ∞`. K–P's upper bounds on
  `F(s,α)` **must** degrade in `α`, at the reciprocal of the local spectral spacing.
- **Radius 0 for the degree-1 shift lattice when `d ≥ 2`.** The same computation with spacing `1`
  gives `k`-th term `≍ (d^d k^{d−1}|2πz|)^k`. This is the quantitative reason Dirichlet-character
  twists (built from additive characters in `n`) are available in degree 1 and open beyond: the
  standard twist supplies additive characters in `n^{1/d}`, and matching them would need
  `α ∝ n^{1−1/d}`, not a constant.

## Novelty

Searched (2026-07): K–P's twist papers (arXiv:1911.10497, 1304.4734, 1507.07177, 2303.02417/20),
the degree-2 conductor-1 classification (arXiv:2009.12329, 2503.02492), the Annals `1<d<2` paper,
and the surveys (Dixit, Zheng, Perelli, Kaczorowski). No statement of this shape found. Both
ingredients are standard; the combination and the sharp two-sided radius are the new item.
Recorded as **plausibly new, not certainly new**.

## Relation to Selberg's conjectures

Independent of them. It does not advance Conjecture B — the three structural obstructions recorded
in the working log (§9.1, §10.1, §20.4) are untouched — but it supplies the exact `α`-dependence any
spike-type analysis of the standard twist needs.

## Log
- 2026-07-25 — proved (cusp case), sharpened to two-sided, unified over base points, verified on all
  four families with explicit constants.

## Formalization status

The analytic bridge and the arithmetic of the spectrum are `[LEAN-PROVED]` in
`formal/GaloisForLFunctions/HTGeometry/ShiftLatticeRadiusLaw.lean`
(axioms: `propext`, `Classical.choice`, `Quot.sound`):

| Card item | Declaration |
|---|---|
| `limsup_k ‖c_k‖^{1/k}` as a growth functional | `hadamardLimsup` |
| **Cauchy--Hadamard** `radius = 1/limsup` | `radius_ofScalars_eq_inv_hadamardLimsup` |
| the geometric factor scales the growth functional by `\|A\|` | `hadamardLimsup_geometric` |
| **radius `R` ⟺ `limsup ‖c_k‖^{1/k} = 1/(\|A\|R)`** | `hadamardLimsup_of_radius` |
| `Spec(F) = { d(m/q)^{1/d} : a_F(m) ≠ 0 }` | `shiftSpectrum` |
| `Spec(F) ⊆ (0,∞)`, so `Spec \ {0} = Spec` | `shiftSpectrum_pos`, `zero_notMem_shiftSpectrum`, `shiftSpectrum_diff_zero` |
| `a_F(1) ≠ 0 ⇒ d q^{-1/d} ∈ Spec(F)` | `base_mem_shiftSpectrum` |
| **`Δ(0) = d q^{-1/d}`** | `infDist_zero_shiftSpectrum` |
| `1/(2π · d q^{-1/d}) = q^{1/d}/(2πd)` | `cusp_constant_eq` |
| **cusp case**: radius `Δ(0)` ⇒ `limsup \|F(s-k/d)/k!\|^{1/k} = q^{1/d}/(2πd)` | `hadamardLimsup_cusp` |

`hadamardLimsup_of_radius` is Step 1 of the proof combined with "Hadamard's
formula for the radius then gives the stated `limsup`" at the end of Step 2: with
`A = 2πi` and `c_k = F_{α₀}(s-k/d)/k!` it turns any radius statement for the
shift-lattice expansion into the boxed `limsup` and back.  `infDist_zero_shiftSpectrum`
is the boxed cusp reduction `Δ(0) = min Spec(F) = d q^{-1/d}`, proved from
`a_F(1) ≠ 0` and monotonicity of `m ↦ d(m/q)^{1/d}` alone.

The convergence layer of the theta series and of the standard twist is
`[LEAN-PROVED]` in `HTGeometry/ShiftLatticeThetaSeries.lean`:

| Card item | Declaration |
|---|---|
| `∑_n n^A exp(-c n^{1/d}) < ∞` for every `A`, every `c > 0` | `summable_rpow_mul_exp_neg_rpow` |
| `Θ(w,z) = ∑_{n≥1} a(n) n^{-w} e(z n^{1/d})` | `thetaTerm`, `thetaSeries` |
| `\|a(n) n^{-w} e(z n^{1/d})\| = \|a(n)\| n^{-Re w} e^{-2π (Im z) n^{1/d}}` | `norm_thetaTerm` |
| `Φ_F(s,·)` converges absolutely on `H`, for **every** `s` | `summable_thetaTerm_of_im_pos` |
| `F_α(w)` converges absolutely to the right of the abscissa | `summable_thetaTerm_of_re` |

`summable_thetaTerm_of_im_pos` is the reason the theta function is entire in the
spectral variable on the open half plane: above the real axis the factor
`exp(-2π (Im z) n^{1/d})` beats every polynomial, so no abscissa condition is
needed.  `summable_thetaTerm_of_re` is the complementary boundary statement, where
`Im z = 0` and only the Dirichlet abscissa controls convergence — that is the
regime in which the standard twist `F_α` is defined before continuation.

The interior shift-lattice expansion is `[LEAN-PROVED]` in
`HTGeometry/ShiftLatticeExpansion.lean`:

| Card item | Declaration |
|---|---|
| the geometric factor `2πi`, with `\|2πi\| = 2π` | `shiftFactor`, `norm_shiftFactor`, `shiftFactor_ne_zero` |
| `n^{-(s-k/d)} = n^{-s} (n^{1/d})^k` | `natCast_cpow_shift` |
| the termwise expansion `e((z₀+ζ)n^{1/d}) = e(z₀ n^{1/d}) ∑_k (2πiζ n^{1/d})^k/k!` | `hasSum_thetaTerm_shift` |
| exact modulus of one member of the double family | `norm_shiftDouble` |
| absolute summability of the double family for `\|ζ\| < Im z₀` | `summable_shiftDouble` |
| `F_{α₀}(s-k/d)/k!` as the normalized spectral family | `shiftLatticeCoeff` |
| **`Θ(s, z₀+ζ) = ∑_k (2πiζ)^k Θ(s-k/d, z₀)/k!`** | `hasSum_shiftLatticeExpansion` |
| each `k`-fibre of the double family | `hasSum_shiftDouble_fiber` |
| absolute summability of the weighted family for `r < Im z₀` | `summable_norm_shiftLatticeCoeff_mul_pow` |
| **`limsup_k ‖Θ(s-k/d,z₀)/k!‖^{1/k} ≤ 1/(2π Im z₀)`** | `hadamardLimsup_shiftLatticeCoeff_le` |

`summable_shiftDouble` is the reason no Mellin--Barnes is needed in the interior:
summing the exponential series back up replaces the decay rate `Im z₀` by
`Im z₀ - |ζ|`, still positive, so the whole double family over `ℕ × ℕ` is
absolutely summable and Fubini applies directly.  The card's Step 1 is therefore
complete *inside* `H`; only the boundary base point `z₀ = -α₀ ∈ ℝ`, where the
spectral family is the continued standard twist rather than a convergent series,
still needs the contour argument.

The other half of the Hadamard argument — that a genuine singularity caps the
radius — is `[LEAN-PROVED]` in `HTGeometry/PowerSeriesSingularRadius.lean`:

| Card item | Declaration |
|---|---|
| the sum function of the expansion, recentred at `z₀` | `shiftSumFun`, `shiftSumFun_eq_tsum` |
| it is analytic on every ball inside the radius | `analyticOnNhd_shiftSumFun` |
| a radius above `R` *produces* an analytic continuation past `R` | `exists_analytic_extension_of_lt_radius` |
| **no continuation ⇒ radius ≤ `R`** | `radius_le_of_no_analytic_extension` |
| **no continuation ⇒ `limsup ‖c_k‖^{1/k} ≥ 1/R`** | `le_hadamardLimsup_of_no_analytic_extension` |

Together with `hadamardLimsup_shiftLatticeCoeff_le` this is the complete Hadamard
mechanism of Step 2, phrased so that the only remaining input is the *analytic*
fact the card cites from Kaczorowski--Perelli: that `Φ_F(s,·)` admits no analytic
extension past a boundary point of `Spec(F)`.  Feeding that into
`le_hadamardLimsup_of_no_analytic_extension` gives the lower bound, and the
convergence bound gives the upper one, so the two combine to the boxed equality.

### What is not yet formalized

Two inputs remain, both genuinely external to the above:

1. **Step 1 at the boundary.**  The interior expansion is done
   (`hasSum_shiftLatticeExpansion`).  What remains is the base point
   `z₀ = -α₀ ∈ ℝ`, where the coefficients are the *continued* standard twists
   `F_{α₀}(s-k/d)` rather than convergent series, so the Mellin--Barnes contour
   argument and the explicit singular part are genuinely needed.
   The interior half of the two-sided bound is now proved
   (`hadamardLimsup_shiftLatticeCoeff_le`): the expansion converges on the whole
   disk of radius `Im z₀`, so the radius is at least `Im z₀` and the growth is at
   most `1/(2π Im z₀)`.  What the boundary case adds is the *lower* bound — that
   the radius is not larger — which is exactly where the jump lemma and
   `ρ_0(α) ≠ 0` enter.
2. **Step 2, the analytic input to `radius = Δ(α₀)`.**  The Hadamard *mechanism*
   is now complete in both directions (`hadamardLimsup_shiftLatticeCoeff_le` and
   `le_hadamardLimsup_of_no_analytic_extension`).  What is still needed is the
   single analytic fact those consume: that `Φ_F(s,·)` admits **no** analytic
   extension past a boundary point of `Spec(F)`.  That is Kaczorowski--Perelli
   standard-twist theory — continuation of `F_α` across every `α ∉ Spec(F)`, and
   `ρ_0(α) ≠ 0` on the spectrum for the jump lemma.  The corpus has no
   Selberg-class layer at all (the `Selberg*` modules under `RHTower/` are the
   Selberg *sieve*), so this is a construction from scratch: the class axioms,
   the standard twist, and K--P's continuation theorem.

Step 3 (the independent cusp constant via the functional equation and uniform
Stirling) is a separate route to the same constant and would also need the class
axioms plus `Γ`-asymptotics along a leftward horizontal shift.

Step 3's `k`-th-root mechanism is `[LEAN-PROVED]` in
`HTGeometry/RootGrowthEngine.lean`:

| Card item | Declaration |
|---|---|
| a positive constant is invisible to the `k`-th root | `tendsto_const_rpow_inv_nat` |
| a power of the index is invisible to the `k`-th root | `tendsto_nat_rpow_div_self` |
| **polynomial envelopes are invisible to the `k`-th root** | `tendsto_rpow_inv_of_polynomial_bounds` |
| such a family has growth functional one | `hadamardLimsup_eq_one_of_tendsto` |
| **only the geometric factor survives** | `hadamardLimsup_geometric_of_tendsto_one` |
| ratio-to-root: consecutive ratios `→ 1` give `k`-th roots `→ 1` | `tendsto_rpow_inv_one_of_ratio_one` |
| `(w+k)/(1+k) → 1` | `tendsto_gammaRatioFactor` |
| **the Gamma ratio `Γ(w+k)/Γ(1+k)` is invisible to the `k`-th root** | `tendsto_norm_gammaRatio_rpow_inv` |

This is exactly the shape of Step 3's computation: after the functional equation
the shifted `L`-value is the geometric factor `(2π)^{-k}` times a ratio of Gamma
values and an `L`-value tending to one, and
`hadamardLimsup_geometric_of_tendsto_one` says the `k`-th root sees only the
geometric factor.  The `L`-value input is already corpus-owned —
`RHTower.tendsto_riemannZeta_of_re_atTop` (zeta tends to one along any sequence
escaping to the right) and `RHTower.tendsto_LSeries_atTop` for Dirichlet
characters.  The Gamma ratio is handled too: `tendsto_norm_gammaRatio_rpow_inv` avoids
Stirling entirely, since the consecutive ratio of `Γ(w+k)/Γ(1+k)` is exactly
`(w+k)/(1+k) → 1` and `tendsto_rpow_inv_one_of_ratio_one` converts that into the
`k`-th-root statement by telescoping and Cesàro.  What remains for Step 3 is only
the oscillating factor `cos(π(1-s+k)/2)`, which vanishes at odd integers, so its
`limsup` must be taken along a subsequence where it is bounded below.

The degree-one twist's **analytic** dichotomy is `[LEAN-PROVED]` in
`HTGeometry/LatticeTwistConvergence.lean`:

| Card item | Declaration |
|---|---|
| the real weight `n^{-σ}`, antitone and vanishing | `twistWeight`, `antitone_twistWeight`, `tendsto_twistWeight` |
| **off the lattice `∑ n^{-σ} e(αn)` converges for every `σ > 0`** | `cauchySeq_latticeTwist`, `exists_tendsto_latticeTwist` |
| on the lattice the same series is the real `p`-series | `latticeTwist_at_integer` |
| which diverges for `σ ≤ 1` | `not_summable_twistWeight` |

This is Kaczorowski--Perelli's continuation statement in the one case where it is
elementary: off `Spec(F)` the bounded character sums let Dirichlet's test carry
the twist from the abscissa `σ > 1` of absolute convergence all the way down to
`σ > 0`, while on `Spec(F)` no cancellation is available and the series is the
divergent `p`-series that carries the pole.  So in degree one the card's Step 2
input is available; the general degree needs the full K--P theory.

The degree-one *mechanism* behind rows 1 and 2 — why the twist is entire off the
lattice and singular on it — is `[LEAN-PROVED]` in
`HTGeometry/LatticeExpSumDichotomy.lean`:

| Card item | Declaration |
|---|---|
| the Dirichlet-sum bound, extracted from the Fejér layer | `norm_fejerSum_le` |
| the additive character `e(α)` of the lattice | `latticeChar`, `latticeChar_eq` |
| `α ∉ ℤ ⇒ e(α) ≠ 1` | `latticeChar_ne_one` |
| **off the lattice: `‖∑_{k≤N} e(αk)‖ ≤ 2/‖e(α)-1‖`, uniformly in `N`** | `norm_latticeExpSum_le` |
| **on the lattice: `∑_{k≤N} e(mk) = N+1`** | `latticeExpSum_at_integer` |

This is the exact dichotomy the row-1 and row-2 checks rest on: bounded character
sums off `Spec(F)` make `F_α` entire there, while on the lattice the sums are the
full length and carry the pole of the underlying `L`-function.  The geometric
estimate was already present inside the proof of
`GaloisForLFunctions.fejerKernel_norm_le`; it is extracted here rather than
reproved.

The **Verifications** table's predicted radii and growth constants are
`[LEAN-PROVED]` in `HTGeometry/ShiftLatticeVerification.lean`:

| Card row | Declaration |
|---|---|
| in degree one the spectrum is the rational lattice `{m/q : a(m) ≠ 0}` | `shiftSpectrum_degree_one` |
| `ζ`: `d = 1`, `q = 1`, radius `1` | `infDist_zero_shiftSpectrum_zeta`, `cusp_constant_zeta` |
| `L(·,χ)` of conductor `q`: radius `1/q` | `infDist_zero_shiftSpectrum_dirichlet`, `cusp_constant_dirichlet` |
| `L(·,Δ)` and level-one Maass: `d = 2`, `q = 1`, radius `2`, growth `1/(4π)` | `infDist_zero_shiftSpectrum_degree_two`, `cusp_constant_degree_two` |

The degree-two row holds for every archimedean parameter, which is the card's
observation that the level-one Maass answer `1/(4π)` is independent of the
spectral parameter `r`.

The arithmetic of the **Consequences** section is `[LEAN-PROVED]` in
`HTGeometry/ShiftSpectrumSpacing.lean`:

| Card item | Declaration |
|---|---|
| `α_m = d(m/q)^{1/d}` and the spectral map | `shiftSpectrumPoint`, `shiftSpectrumMap` |
| its derivative `q^{-1}(x/q)^{1/d-1}` | `shiftSpectrumSlope`, `hasDerivAt_shiftSpectrumMap` |
| the consecutive spacing | `shiftSpectrumGap`, `shiftSpectrumGap_nonneg` |
| **the spacing is a derivative at an interior point** | `exists_shiftSpectrumGap_eq` |
| `Δ(α_m) ≤ q^{-1}(α_m/d)^{1-d}` | `shiftSpectrumGap_le` |
| **`Δ(α_m) → 0` for `d > 1`** | `tendsto_shiftSpectrumGap_nhds_zero` |
| **degree-one lattice: `d^d k^{d-1}\|2πz\| → ∞` for `d ≥ 2`** | `tendsto_degreeOneLatticeRoot_atTop` |

`exists_shiftSpectrumGap_eq` is the mean-value form of the card's `≍`: since
`x ↦ d(x/q)^{1/d}` is concave for `d ≥ 1`, its slope at an interior point is
squeezed between the endpoint slopes, and the left endpoint gives exactly
`q^{-1}(α_m/d)^{1-d}`.  `tendsto_shiftSpectrumGap_nhds_zero` is the card's
`Δ(α_m) → 0`, the quantitative reason Kaczorowski--Perelli's upper bounds on
`F(s,α)` must degrade in `α`.  `tendsto_degreeOneLatticeRoot_atTop` is the second
Consequence: with spacing one the `k`-th root of the coefficient diverges, so
that expansion has radius zero above degree one.

The **jump lemma** of Step 2 was already in the corpus and is reused, not
rebuilt: `HTGeometry/ResidueJumpLowerBound.lean` proves
`HTGeometry.residue_jump_bound` and
`HTGeometry.residue_jump_of_integral_eq_zero`, which is exactly the card's
`sup_{|s-s*_0|=r}|F_α(s) - F_{α'}(s)| ≥ |ρ_0(α)|/r`, with `∮ F_{α'} = 0` and
`∮ F_α = 2πi ρ_0(α)`.  Its two missing consequences are `[LEAN-PROVED]` in
`HTGeometry/ResidueJumpNoLimit.lean`:

| Card item | Declaration |
|---|---|
| a non-vanishing circle integral certifies non-analyticity | `HTGeometry.not_analyticOnNhd_of_circleIntegral_ne_zero` |
| a non-zero residue is not a uniform limit of residue-free functions | `HTGeometry.not_tendstoUniformlyOn_of_residue_ne_zero` |

The first is the certificate consumed by `radius_le_of_no_analytic_extension`;
the second is the qualitative form of the jump, which is what makes the twist
family `α ↦ F_α` discontinuous exactly on `Spec(F)`.

### Corpus reuse audit (before continuing)

Checked the existing Lean corpus for overlap.  Nothing duplicates the modules
above: the other users of `FormalMultilinearSeries.radius`
(`HTGeometry/GutzmerIdentity.lean`, and the two
`*MagnitudeHypertranscendence.lean` files) prove `radius = ⊤` for entire phase
series or Gutzmer's identity, and `HTGeometry/BarnesSourceRepresentative.lean` is
the Barnes cone-product logarithmic derivative, not Mellin--Barnes.

Four existing layers should be *reused* rather than rebuilt when the remaining
inputs are constructed:

- `Bottcher/NaturalBoundary*.lean` (seven modules, including
  `no_unit_min_of_analytic`) — the corpus's natural-boundary engine, the closest
  existing analogue of the "no analytic extension past a boundary point" input
  that `le_hadamardLimsup_of_no_analytic_extension` consumes.
- `RHTower/BVPrimeWindowContinuation.lean` — a worked template for
  "Dirichlet series + meromorphic continuation + residue at a zero"
  (`continuedSource`, `meromorphicOn_continuedSource_rightHalf`,
  `LSeries_polarCoefficient_eq_continuedSource`).  The same
  `LSeries_…_eq_continuation` idiom recurs across the `CCM*` modules.  The
  standard twist `F_α` should follow this shape.
- mathlib's `mellin`, already used in `HTGeometry/SmoothWeightPerron.lean` for
  Perron/contour estimates and in `HTGeometry/MellinConjugate.lean`; plus
  `CompactBVPrimeWindow.mellinTransform` with its exact dilation character.
- `RHTower/SelfDualDirichletRealZeros.lean`'s `SelfDualPrimitiveDirichletDatum`
  — the corpus idiom for bundling L-function axioms as structure fields, to be
  the model for the Selberg class `S^♯`.

Confirmed absent: any Selberg-class structure, standard twist, or
Kaczorowski--Perelli continuation.
