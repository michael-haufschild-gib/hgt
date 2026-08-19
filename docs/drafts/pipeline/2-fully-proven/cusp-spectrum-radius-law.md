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
| the expansion converges on the whole disk of that radius | `le_radius_shiftLattice` |
| **the radius is *exactly* the height, given a genuine singularity** | `radius_shiftLattice_eq` |
| **the boxed law, interior form: `limsup_k ‖Θ(s-k/d,z₀)/k!‖^{1/k} = 1/(2π Im z₀)`** | `hadamardLimsup_shiftLatticeCoeff_eq` |
| the disk of radius the height stays in the half plane | `im_pos_of_mem_ball` |
| **the height is exactly the distance to the real axis** | `infDist_realAxis_eq_im` |
| the expansion is a genuine power-series representation | `hasFPowerSeriesOnBall_thetaSeries` |
| **`Φ_F(s,·)` is holomorphic on `H`** | `analyticAt_thetaSeries` |

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
| **unboundedness is a genuine singularity** | `no_analytic_extension_of_unbounded` |
| an unbounded represented function caps the radius | `radius_le_of_unbounded` |
| the constant family in degree one, spectral parameter zero | `oneCoeff`, `thetaTerm_geometric` |
| `Θ(iy) ≥ N e^{-2πyN}` for every truncation | `le_norm_thetaSeries_geometric` |
| **`Θ` is unbounded on every disk touching the real axis** | `unbounded_thetaSeries_geometric` |
| **the boxed law with NO hypotheses, for the geometric family** | `hadamardLimsup_geometricShiftLattice` |
| **radius of convergence exactly the gap, with NO hypotheses** | `radius_geometricShiftLattice` |
| the constant family at a general **real** spectral parameter `σ` | `powTerm`, `thetaTerm_pow`, `thetaSeries_pow` |
| `Θ(iy) ≥ (∑_{n≤N} n^{-σ}) e^{-2πyN}` for every truncation | `pSum`, `le_norm_thetaSeries_pow` |
| the `p`-series partial sums diverge for `σ ≤ 1` | `tendsto_pSum_atTop` |
| **`Θ` unbounded on every disk touching the axis, all `σ ≤ 1`** | `unbounded_thetaSeries_pow` |
| **the boxed law with NO hypotheses, for every real `σ ≤ 1`** | `hadamardLimsup_powShiftLattice` |
| the constant family in **every degree** `d > 0` | `degTerm`, `thetaTerm_deg`, `thetaSeries_deg`, `shiftExp_imag` |
| `Θ(iy) ≥ (∑_{n≤N} n^{-σ}) e^{-2πyN^{1/d}}` | `le_norm_thetaSeries_deg` |
| **`Θ` unbounded on every disk touching the axis, all `d > 0`, `σ ≤ 1`** | `unbounded_thetaSeries_deg` |
| **the boxed law with NO hypotheses, every degree and every real `σ ≤ 1`** | `hadamardLimsup_degShiftLattice` |
| **radius exactly the gap, NO hypotheses, every degree, every `σ ≤ 1`** | `radius_degShiftLattice` |

Together with `hadamardLimsup_shiftLatticeCoeff_le` this is the complete Hadamard
mechanism of Step 2, phrased so that the only remaining input is the *analytic*
fact the card cites from Kaczorowski--Perelli: that `Φ_F(s,·)` admits no analytic
extension past a boundary point of `Spec(F)`.  Feeding that into
`le_hadamardLimsup_of_no_analytic_extension` gives the lower bound, and the
convergence bound gives the upper one, so the two combine to the boxed equality.

### What is not yet formalized

Two inputs remain, both genuinely external to the above:

0. **The boxed theorem holds in the interior.**
   `hadamardLimsup_shiftLatticeCoeff_eq` is the card's boxed equality
   `limsup_k |F_{α₀}(s-k/d)/k!|^{1/k} = 1/(2π Δ(α₀))` for an interior base
   point, with `Δ` the interior gap `Im z₀`.  Its one hypothesis is the
   singularity — everything else (expansion, convergence, Hadamard, geometry) is
   proved.  `no_analytic_extension_of_unbounded` reduces that hypothesis to a
   checkable one: it suffices that `Φ_F(s,·)` be *unbounded* on the disk, since an
   analytic extension would be continuous on the compact closed disk and hence
   bounded.  That is how a boundary singularity is verified in practice, and it is
   what the row-1 check needs.  `unbounded_thetaSeries_geometric` then supplies
   it outright for the constant coefficient family in degree one at spectral
   parameter zero: on the imaginary axis every term is a positive real, so the
   sum dominates any truncation, and `N` terms at height `1/N` give the lower
   bound `N e^{-2π}`, which diverges.  Composing the three steps gives
   `hadamardLimsup_geometricShiftLattice`: the boxed radius law holding
   **with no hypotheses at all** for the constant coefficient family in degree
   one at spectral parameter zero.  That is the first fully unconditional
   instance of the card's boxed theorem, in both of the card's phrasings:
   `radius_geometricShiftLattice` gives "radius of convergence exactly `Δ`" and
   `hadamardLimsup_geometricShiftLattice` gives the `limsup` form.

   The same argument runs at every **real** spectral parameter `σ ≤ 1`.  On the
   imaginary axis the terms are `n^{-σ} e^{-2πyn}`, still positive reals, so the
   truncation bound becomes `(∑_{n≤N} n^{-σ}) e^{-2πyN}`
   (`le_norm_thetaSeries_pow`); at height `y = 1/N` the exponential is the
   constant `e^{-2π}` and the prefactor is the `p`-series partial sum, which
   diverges precisely because `σ ≤ 1` (`tendsto_pSum_atTop`, from
   `Real.summable_one_div_nat_rpow`).  This gives `unbounded_thetaSeries_pow`
   and hence `hadamardLimsup_powShiftLattice`: the boxed radius law, **with no
   hypotheses at all**, for the constant coefficient family in degree one at
   every real spectral parameter at or below the abscissa.  For `σ > 1` this
   route genuinely fails — the series converges at `z = 0`, so the singularity
   there is a branch point rather than a pole, and its detection needs the
   Mellin--Barnes asymptotic instead.

   The degree is not a restriction either.  In degree `d` the terms on the
   imaginary axis are `n^{-σ} e^{-2π y n^{1/d}}`, still positive reals and still
   decreasing in `n` because `1/d > 0`, so the truncation bound
   `le_norm_thetaSeries_deg` reads `(∑_{n≤N} n^{-σ}) e^{-2π y N^{1/d}}`; taking
   the height `y = N^{-1/d}` again makes the exponential the constant `e^{-2π}`.
   This gives `unbounded_thetaSeries_deg` and hence
   `hadamardLimsup_degShiftLattice` and `radius_degShiftLattice`: **the card's
   boxed theorem, with no hypotheses at all, for the constant coefficient family
   in every degree `d > 0` and at every real spectral parameter `σ ≤ 1`**, in
   both of the card's phrasings.  The gap is `Δ = y₀`, matching
   `infDist_zero_shiftSpectrum` for the constant family, whose spectrum is
   `{d (m/q)^{1/d}}` with nearest point `d q^{-1/d}`.

   **The constant family is not special either.**  Everything the argument uses
   is that the terms are non-negative reals and that the Dirichlet series
   diverges at `σ`, so it runs for an arbitrary non-negative coefficient family.
   `HTGeometry/NonnegThetaCuspGrowth.lean`:

| Card item | Declaration |
|---|---|
| a real family, viewed as a complex one | `realCoeff`, `realCoeff_apply` |
| its theta terms on the imaginary axis are real | `nonnegTerm`, `thetaTerm_realCoeff`, `thetaSeries_realCoeff` |
| the Dirichlet partial sums | `dirichletPartial`, `dirichletPartial_one` |
| **non-summability at `σ` ⇒ the partial sums diverge** | `tendsto_dirichletPartial_atTop` |
| `Θ(iy) ≥ (∑_{n≤N} a(n) n^{-σ}) e^{-2πyN^{1/d}}` | `le_norm_thetaSeries_nonneg` |
| **`Θ` unbounded on every disk touching the real axis** | `unbounded_thetaSeries_nonneg` |
| **the boxed law, NO hypotheses, any non-negative family below its abscissa** | `hadamardLimsup_nonnegShiftLattice` |
| **radius exactly the gap, same generality** | `radius_nonnegShiftLattice` |

   Basing the expansion at height `Δ` itself converts this into the card's
   *local--global identity* with no hypotheses at all.
   `HTGeometry/CuspGapUnconditionalInstances.lean`:

| Card item | Declaration |
|---|---|
| a family bounded below by one diverges at and below `σ = 1` | `not_summable_of_one_le` |
| **`limsup_k \|F(s-k/d)/k!\|^{1/k} = 1/(2πΔ)` at the base point `iΔ`** | `hadamardLimsup_at_cuspGap` |
| **radius of convergence exactly `Δ`, at the base point `iΔ`** | `radius_at_cuspGap` |
| degree one, conductor one: `Δ = 1`, constant `1/(2π)` | `constCoeff`, `infDist_shiftSpectrum_constCoeff`, `hadamardLimsup_constCoeff_cusp` |
| the divisor function is a legitimate coefficient family | `divisorCoeff`, `divisorCoeff_bound`, `one_le_divisorCoeff`, `card_divisors_le` |
| **degree two, conductor one: `Δ = 2`, constant `1/(4π)`** | `infDist_shiftSpectrum_divisorCoeff`, `hadamardLimsup_divisorCoeff_cusp`, `radius_divisorCoeff_cusp` |

   What `hadamardLimsup_at_cuspGap` proves, stated precisely: the base point is
   the *interior* point `iΔ`, the disk of radius `Δ` is the largest one inside
   the half plane, and its boundary point directly below is the origin — which
   for a divergent Dirichlet series really is a singularity of `Φ_F(s,·)`.  So
   the radius is exactly `Δ` and the growth functional exactly `1/(2πΔ)`.  The
   height `Δ` is *chosen* to be `infDist 0 Spec(F)`, so the identity is the
   interior shadow of the card's boundary statement, not yet the boundary
   statement itself: what is proved is that the singularity directly below the
   base point sits at distance exactly the height.  Locating the *next* spectral
   point — the content of `Δ(α₀)` for `α₀ ∈ Spec(F)` — still needs the boundary
   expansion of item 1 below.  `hadamardLimsup_divisorCoeff_cusp` is the first
   **degree-two** instance, and it reproduces `cusp_constant_degree_two`
   numerically: gap two, growth constant `1/(4π)`.

   **Step 2's opening clause is proved.**  `analyticAt_thetaSeries` is the card's
   "`Φ_F(s,·)` is holomorphic on `H`", obtained directly from the shift-lattice
   expansion rather than from a separate convergence argument: the expansion at an
   interior base point *is* a power-series representation on the disk of radius
   the height (`hasFPowerSeriesOnBall_thetaSeries`).

   **The interior boxed theorem is closed, and its geometry is exact.**
   `infDist_realAxis_eq_im` says the height of an interior base point *is* its
   distance to the real axis, so the disk in `radius_shiftLattice_eq` is the
   largest one inside `H` and the nearest possible singularity is the boundary
   point directly below — which is why the interior radius law is the correct
   interior shadow of the boundary statement `Δ(α₀)`.  `radius_shiftLattice_eq` is the
   card's "radius of convergence exactly `Δ(α₀)`" for an interior base point:
   `le_radius_shiftLattice` gives `≥` from absolute convergence and
   `radius_le_of_no_analytic_extension` gives `≤` from the singularity, so the
   only remaining input is the singularity itself.

1. **Step 1 at the boundary.**  The interior expansion is done
   (`hasSum_shiftLatticeExpansion`).  What remains for a general class member is
   the base point `z₀ = -α₀ ∈ ℝ`, where the coefficients are the *continued*
   standard twists `F_{α₀}(s-k/d)` rather than convergent series.

   **For the zeta function this is now proved, and no Mellin--Barnes contour was
   needed.**  The Hurwitz formula already writes the continued twist at a
   rightward-shifted argument in closed form, and the growth of its two Hurwitz
   zeta values is elementary.  Three modules:

   `RHTower/HurwitzZetaRightAsymptotics.lean` — the analytic input:

| Card item | Declaration |
|---|---|
| the ratios of the Hurwitz series to its first term | `hurwitzRatio`, `hurwitzRatio_zero`, `hurwitzRatio_succ_le` |
| normalising by the first term replaces the summands by their ratios | `cpow_hurwitzRatio`, `hasSum_hurwitzRatio` |
| the tail is geometrically small | `hurwitzTailConst`, `norm_normalizedHurwitz_sub_one_le` |
| **`a^{w} ζ(w,a) → 1` as `Re w → ∞`: exact geometric growth `a^{-Re w}`** | `tendsto_normalizedHurwitz` |

   `RHTower/ZetaTwistShiftDecomposition.lean` — the decomposition:

| Card item | Declaration |
|---|---|
| the smallest exponent of the Hurwitz series at a real shift | `twistFirst`, `twistFirst_pos`, `twistFirst_le_one` |
| a shift and its fractional part agree on the circle | `coe_fract_unitAddCircle` |
| **the normalized Hurwitz value tends to one, integer shifts included** | `tendsto_normalizedTwist` |
| the cusp gap `Δ(α)` as the smaller of the two exponents | `twistGap`, `twistGap_of_fract_zero`, `twistGap_of_fract_ne_zero` |
| **`F(s₀-k,α)/k! = (2π)^{-k} · (const · Γ(1-s₀+k)/Γ(1+k) · bracket)`** | `twistRemainder`, `zetaTwist_decomposition` |

   `RHTower/ZetaTwistCuspRadius.lean` + `RHTower/ZetaTwistGapGeometry.lean` — the law:

| Card item | Declaration |
|---|---|
| the two halves of the bracket, geometric factor extracted | `twistP`, `twistLead`, `twistTerm`, `twistTerm_eq`, `norm_twistTerm` |
| the dominant half has constant modulus, the other decays | `tendsto_norm_twistTerm_of_eq`, `tendsto_norm_twistTerm_of_lt` |
| the bracket, recombined | `twistBracket`, `twistSum`, `twistBracket_eq` |
| equal exponents force equal shifts on the circle | `coe_neg_eq_of_twistFirst_eq`, `twistP_neg_eq` |
| in that case the bracket is a period-four factor times one Hurwitz value | `twistWave`, `twistWave_periodic`, `exists_norm_twistWave_pos`, `twistSum_eq_wave` |
| **the bracket has root growth exactly one after extraction** | `limsup_norm_twistSum_eq_one`, `hadamardLimsup_twistT` |
| **`limsup_k \|F(s₀-k,α)/k!\|^{1/k} = 1/(2π Δ(α))`** | `hadamardLimsup_zetaTwistShift` |
| the gap is the distance to the integers | `fract_eq_zero_iff`, `infDist_intRange` |
| **`Δ(α) = dist(α, Sing ∖ {α})`** | `infDist_singular_sdiff_eq_twistGap` |
| **the boxed law with `Δ` read off from the singular set** | `hadamardLimsup_zetaTwistShift_eq_infDist` |
| at an integer shift the constant is `1/(2π)` | `hadamardLimsup_zetaTwistShift_int` |

   `hadamardLimsup_zetaTwistShift_eq_infDist` is the card's boxed theorem at a
   **boundary** base point, unconditionally, for the zeta function in degree one
   and conductor one.  Here the two sides really are computed from disjoint data:
   the left from the Hurwitz formula plus the rightward growth of the two Hurwitz
   zeta values, the right from the location of the singularities of the family
   `α ↦ F(·,α)`.  Nothing is chosen to make them agree.

   The mechanism replaces the card's Mellin--Barnes step entirely.  Writing
   `A` and `B` for the smallest exponents of the Hurwitz series at `α` and `-α`,
   the bracket of the Hurwitz formula is `E_k ζ(w_k,α) + E'_k ζ(w_k,-α)` with
   `|E_k|`, `|E'_k|` constant in `k`; the two Hurwitz values grow like `A^{-k}`
   and `B^{-k}`.  If `A ≠ B` the faster term dominates and no cancellation is
   possible; if `A = B` then `α` and `-α` are the same point of the circle, the
   two Hurwitz values coincide, and the bracket is a period-four factor times a
   single Hurwitz value — invisible to the root.  Either way the root growth is
   `1/min(A,B)`, and `min(A,B)` is the distance from `α` to the integer lattice,
   which is `Δ(α)`.

   **The conductor is not a restriction either.**  For any periodic coefficient
   function the same mechanism runs off mathlib's `ZMod.LFunction_one_sub`, whose
   right-hand side is the Fourier-transformed series rather than a Hurwitz value.
   `RHTower/PeriodicLSeriesRightAsymptotics.lean` supplies the analytic input:

| Card item | Declaration |
|---|---|
| a periodic coefficient function is bounded | `exists_bound_zmod` |
| the scaled terms of the Dirichlet series | `norm_natCast_cpow`, `norm_scaled_term` |
| the tail past the first non-vanishing term is geometrically small | `norm_normalizedLFunction_sub_le` |
| **`n₀^{w} L(Θ,w) → Θ(n₀)`: exact geometric growth `n₀^{-Re w}`** | `tendsto_normalizedLFunction` |

   `RHTower/ZModLFunctionCuspRadius.lean` runs the decomposition and the law:

| Card item | Declaration |
|---|---|
| the Fourier transform of a non-zero function is non-zero | `dft_ne_zero` |
| the dual index: the first exponent of the transformed series | `dualSupport`, `dualSupport_nonempty`, `dualIndex`, `dualIndex_pos`, `dualIndex_spec`, `dualIndex_min` |
| both dual series grow at the rate of the dual index | `dualP`, `dualQ`, `tendsto_dualP`, `tendsto_dualQ` |
| **`L(s₀-k)/k! = (N/(2π n₀))^k · remainder`** | `dualSum`, `zmodRemainder`, `zmod_shift_decomposition` |
| the quarter-turn exponentials split off | `exp_neg_quarter_turn`, `exp_shift_pos`, `exp_shift_neg` |
| the period-four limit shape of the bracket | `dualWave`, `dualWave_periodic`, `exists_norm_dualWave_pos` |
| the bracket converges to that shape, and is bounded | `tendsto_dualSum_sub_dualWave`, `exists_bound_norm_dualSum` |
| **the bracket has root growth one** | `limsup_norm_dualSum_eq_one`, `hadamardLimsup_zmodRemainder` |
| **`limsup_k \|L(s₀-k)/k!\|^{1/k} = N/(2π n₀)`** | `hadamardLimsup_zmodShift` |
| dual coefficient non-vanishing at one pins the index | `ne_zero_of_dft_one_ne_zero`, `dualIndex_eq_one` |
| **degree one, conductor `N`: the constant is `N/(2π)`** | `hadamardLimsup_zmodShift_of_dft_one` |

   `hadamardLimsup_zmodShift_of_dft_one` is the card's Dirichlet verification row
   proved analytically: gap `1/N`, growth constant `N/(2π)`, matching
   `infDist_zero_shiftSpectrum_dirichlet` and `cusp_constant_dirichlet`.  The
   general form `hadamardLimsup_zmodShift` is sharper — it shows the constant is
   `N/(2π n₀)` with `n₀` the first exponent of the *dual* series, so a family
   whose dual coefficients start later has a correspondingly smaller constant.

   The non-cancellation step is where the minimality of `n₀` is used.  The bracket
   converges to the period-four shape
   `e·i^k·Θ(n₀) + e'·(-i)^k·Θ(-n₀)`, whose four values over a period vanish
   simultaneously only if both `Θ(n₀)` and `Θ(-n₀)` vanish — which is exactly what
   `n₀` was chosen to exclude.  No hypothesis beyond `Φ ≠ 0` is needed.

   For degree `d > 1` the same route needs the class member's own Hurwitz-type
   formula, which is the general Kaczorowski--Perelli input of item 2.
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
   Selberg *sieve*), so for a general class member this is a construction from
   scratch: the class axioms, the standard twist, and K--P's continuation
   theorem.

   **For the zeta function itself the K--P input is already available, and is now
   formalized.**  mathlib's `HurwitzZeta.expZeta` *is* the continued standard
   twist `ζ(s, α) = ∑_{n ≥ 1} e^{2πiαn} n^{-s}`, and mathlib proves it entire
   for `α ∉ ℤ`.  `RHTower/ZetaStandardTwistDichotomy.lean` identifies it with the
   card's objects and completes the dichotomy:

| Card item | Declaration |
|---|---|
| the standard twist of `ζ` at a real shift | `zetaStandardTwist` |
| **it is the theta series on the half plane of convergence** | `thetaSeries_eq_zetaStandardTwist` |
| `ζ` is not differentiable at its pole | `not_differentiableAt_riemannZeta_one` |
| the untwisted series is `ζ`, hence not entire | `not_differentiable_expZeta_zero` |
| **the spectral dichotomy: entire ⟺ off the spectrum** | `differentiable_expZeta_iff` |
| a real shift is spectral exactly when it is an integer | `coe_unitAddCircle_eq_zero_iff`, `not_differentiable_zetaStandardTwist_iff` |
| the singular set of the twist family | `zetaTwistSingularSet`, `mem_zetaTwistSingularSet` |
| **the shift spectrum consists of singular shifts** | `shiftSpectrum_subset_singular` |
| **every singular shift is a spectral point translated by the lattice** | `singular_iff_spectrum_translate` |
| **the cusp gap of `ζ` is one: `Δ(α₀) = 1` for every `α₀ ∈ Spec`** | `infDist_zetaTwistSingularSet_sdiff` |

   `differentiable_expZeta_iff` is exactly K--P's continuation statement in
   degree one and conductor one: `F_α` continues to an entire function for every
   `α ∉ Spec(F)`, and fails to for every `α ∈ Spec(F)`.  The failure is not an
   abstract non-continuation but an explicit pole, inherited from the pole of `ζ`
   at `s = 1`.  `infDist_zetaTwistSingularSet_sdiff` then computes the card's
   `Δ(α₀)` at a *boundary* base point, from the singular set rather than from a
   chosen height: from any spectral shift the nearest other spectral shift is at
   distance exactly one, so `1/(2π Δ(α₀)) = 1/(2π)`, matching both
   `hadamardLimsup_zetaShift` and `cusp_constant_zeta`.

   What is still missing for `ζ` is only the *transport* of this dichotomy into
   the `z`-variable: the shift-lattice expansion at a real base point `α₀`
   requires continuing `Φ_ζ(s, ·)` from the upper half plane across the real
   interval `(α₀ - 1, α₀ + 1)` minus its endpoints, which is item 1.

Step 3 (the independent cusp constant via the functional equation) is a separate
route to the same constant.  It is now proved in degree one (zeta and, in the
general conductor-`N` form, `hadamardLimsup_zmodShift`) and in **degree two**,
for `ζ²`.

The degree-two case needed two pieces of new infrastructure, because a lattice of
degree `d` advances by `1/d` and so its root exponents are `1/(am+b)` rather than
`1/m`.  `HTGeometry/ScaledRootGrowth.lean`:

| Card item | Declaration |
|---|---|
| the rescaling ratio `m/(am+b) → 1/a` | `scaled_denom_pos`, `tendsto_scaleRatio` |
| **a root limit survives the rescaling of the exponent** | `tendsto_rpow_scaled_of_tendsto_rpow_inv` |
| constants and polynomial envelopes are invisible to a rescaled root | `tendsto_const_rpow_scaled`, `tendsto_rpow_scaled_of_polynomial_bounds` |
| rescaled roots of a bounded factor are bounded | `rpow_scaled_le_const`, `isBoundedUnder_rpow_scaled` |
| **bounded above, frequently bounded below ⇒ rescaled root `limsup` is one** | `limsup_rpow_scaled_eq_one` |

`HTGeometry/ParityLimsupSplit.lean` supplies the second piece:

| Card item | Declaration |
|---|---|
| **`atTop` is the supremum of the even and odd pushforwards** | `atTop_eq_sup_parity` |
| `limsup` along a pushforward is `limsup` of the composite | `limsup_map_comp` |
| **the growth functional is the larger of its two parity parts** | `hadamardLimsup_eq_parity_sup` |
| the extended-real image of a bounded real `limsup` | `limsup_ofReal_eq`, `coe_nnnorm_rpow_eq_ofReal` |

`HTGeometry/CentralBinomialRoot.lean` handles the factorial ratio:

| Card item | Declaration |
|---|---|
| the reciprocal quotient `4^m/C(2m,m)` | `centralQuot`, `centralQuot_pos` |
| it lies between one and `2m` | `one_le_centralQuot`, `centralQuot_le` |
| **it is invisible to a rescaled root** | `tendsto_centralQuot_rpow_scaled` |
| `C(2m,m)·(m!)² = (2m)!` | `centralBinom_mul_factorial_sq` |

`RHTower/ZetaSquareCuspRadius.lean` assembles them:

| Card item | Declaration |
|---|---|
| the non-oscillating part of the shifted remainder | `gpart`, `norm_zetaShiftRemainder_eq`, `tendsto_gpart_rpow_inv` |
| its square is invisible to a rescaled root | `tendsto_gpart_sq_rpow_scaled` |
| the squared oscillating factor has rescaled root `limsup` one | `cosShift_sq_periodic`, `limsup_cosShift_sq_rpow_scaled` |
| **the squared remainder has rescaled root `limsup` one** | `limsup_norm_zetaShiftRemainder_sq_rpow_scaled`, `isBoundedUnder_norm_zetaShiftRemainder_sq_rpow_scaled` |
| the degree-two coefficients `ζ(s₀-k/2)²/k!` | `zetaSquareCoeff`, `half_shift_even`, `half_shift_odd` |
| **the even and odd closed forms** | `zetaSquareCoeff_even`, `zetaSquareCoeff_odd` |
| their moduli, with `1/(4π)` extracted | `vEven`, `vOdd`, `quarter_pow_identity`, `norm_zetaSquareCoeff_even`, `norm_zetaSquareCoeff_odd` |
| the two remainders have rescaled root `limsup` one | `limsup_vEven`, `limsup_vOdd`, `pOdd`, `tendsto_pOdd_rpow` |
| **both parity parts equal `1/(4π)`** | `limsup_parity_even`, `limsup_parity_odd` |
| **`limsup_k \|ζ(s₀-k/2)²/k!\|^{1/k} = 1/(4π)`** | `hadamardLimsup_zetaSquareShift` |

`hadamardLimsup_zetaSquareShift` is the card's Step 3 in degree two: the growth
constant of the squared zeta shift lattice, computed from the functional equation
alone, is `1/(4π)` — matching `cusp_constant_degree_two` and the spectral value
`1/(2π Δ(0))` with `Δ(0) = 2` from `infDist_zero_shiftSpectrum_degree_two`.  It
also matches the *analytic* degree-two instance
`hadamardLimsup_divisorCoeff_cusp`, which reaches the same constant from the
divisor function's theta series rather than from the functional equation.

No uniform Stirling estimate was needed.  The factorial ratio `(m!)²/(2m)!` is
the reciprocal of the central binomial coefficient, and the classical bound
`4^m/(2m) ≤ C(2m,m) ≤ 4^m` is a polynomial envelope, hence invisible to the
root.

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
`k`-th-root statement by telescoping and Cesàro.  The oscillating factor is handled as well, in
`HTGeometry/OscillatingRootLimsup.lean`:

| Card item | Declaration |
|---|---|
| the roots of a bounded factor are bounded | `rpow_inv_le_const_rpow_inv`, `isBoundedUnder_rpow_inv` |
| **bounded above, frequently bounded below ⇒ root `limsup` is one** | `limsup_rpow_inv_eq_one` |
| a periodic sequence is bounded | `exists_bound_of_periodic` |
| a periodic sequence is frequently bounded below at any index | `frequently_le_of_periodic` |
| **the root `limsup` of a periodic factor is one** | `limsup_rpow_inv_eq_one_of_periodic` |
| **a factor tending to one leaves a `limsup` of one unchanged** | `limsup_mul_eq_one_of_tendsto_one` |
| the growth functional is the extended-real image of the root `limsup` | `hadamardLimsup_eq_ofReal_limsup` |
| **growth functional one from root `limsup` one** | `hadamardLimsup_eq_one_of_limsup_eq_one` |
| the geometric factor `(2π)^{-k}` splits off | `two_pi_cpow_shift` |
| **`ζ(s₀-k)/k! = (2π)^{-k} · (const · Γ(1-s₀+k)/Γ(1+k) · cos(π(1-s₀+k)/2) · ζ(1-s₀+k))`** | `zetaShift_decomposition` |
| the oscillating factor, with period four | `cosShift`, `cosShift_periodic` |
| it cannot vanish at both index zero and one | `exists_cosShift_pos` |
| **the oscillating factor contributes nothing to the root growth** | `limsup_cosShift_rpow_inv_eq_one` |

Only a *frequent* lower bound is needed, which is exactly the situation for
`cos(π(1-s+k)/2)`: as `k` runs over the residues modulo four the factor takes the
four values `±cos θ`, `±sin θ`, so it is bounded, it may vanish on a whole
residue class, and at least one of `cos θ`, `sin θ` is non-zero — giving the
frequent lower bound.  `limsup_rpow_inv_eq_one_of_periodic` applies to `k ↦ cos(π(1-s+k)/2)` directly:
it has period four, so it is bounded, and it is positive at some index because
`cos² + sin² = 1` forbids it vanishing on every residue class.

`limsup_mul_eq_one_of_tendsto_one` is the combination step: three of the four
factors have `k`-th roots converging to one and only the oscillating factor has a
genuine `limsup`, so they cannot simply be multiplied — the convergent group is
absorbed into the oscillating one.

`hadamardLimsup_eq_ofReal_limsup` is the bridge between the two limsups in play:
the growth functional lives in the extended non-negative reals, while the
squeeze arguments for the four factors are real.  With it, a real root `limsup`
of one transfers to a growth functional of one.

Every analytic ingredient of Step 3 is therefore formalized, together with the
combination law and the transfer.  The splitting itself is now proved: `zetaShift_decomposition` applies mathlib's
`riemannZeta_one_sub` at `s = 1-s₀+k`, uses `k! = Γ(1+k)`, and separates the
geometric factor, under the single hypothesis that `s₀` is not a natural number
(which is exactly what keeps `1-s₀+k` off the poles of `Γ` and away from the
pole of `ζ`).  **Step 3 is complete for the zeta function.**  `RHTower/ZetaCuspRadiusConstant.lean`
assembles the decomposition against the root laws:

| Card item | Declaration |
|---|---|
| the remainder of the decomposition | `RHTower.zetaShiftRemainder` |
| its Gamma quotient has `k`-th roots tending to one | `RHTower.tendsto_gammaQuotient` |
| its zeta value has `k`-th roots tending to one | `RHTower.tendsto_zetaShiftValue` |
| the remainder has growth functional one | `RHTower.hadamardLimsup_zetaShiftRemainder` |
| **`limsup_k \|ζ(s₀-k)/k!\|^{1/k} = 1/(2π)`** | `RHTower.hadamardLimsup_zetaShift` |
| **the local--global identity: analytic constant = `1/(2πΔ(0))`** | `RHTower.hadamardLimsup_zetaShift_eq_spectral` |

This is the card's independent cusp-constant computation for `ζ`, degree one and
conductor one.  `hadamardLimsup_zetaShift_eq_spectral` states the agreement
directly: the constant obtained from the functional equation *equals*
`1/(2π Δ(0))` with `Δ(0)` the spectral gap of the standard-twist spectrum.  The
two sides use disjoint data — the first only the archimedean functional
equation, the second only `a(1) ≠ 0` and the location of the first prime-side
singularity — so the card's "local--global identity" is now a Lean theorem.  The
only hypothesis is that `s₀` is not a natural number.

The assembly lives in `RHTower` because the fourth factor's limit,
`RHTower.tendsto_riemannZeta_of_re_atTop`, does; `HTGeometry` may not import
`RHTower`.

Earlier note, superseded: three of the four factors are discharged against the
root laws: the constant (`tendsto_const_rpow_inv_nat`), the Gamma quotient
(`tendsto_norm_gammaRatio_rpow_inv`) and the oscillating cosine
(`limsup_cosShift_rpow_inv_eq_one`).  The fourth, `ζ(1-s₀+k) → 1`, is the
corpus theorem `RHTower.tendsto_riemannZeta_of_re_atTop`; since that lives in
`RHTower`, the final assembly module must be placed there rather than in
`HTGeometry`.

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
| **`Δ(α₀) = dist(α₀, Spec(F) \ {α₀})`** | `spectralGap` |
| `Δ(0) = d q^{-1/d}` | `spectralGap_zero` |
| `Δ(α_m)` is at most the distance to the next spectral point | `spectralGap_le_shiftSpectrumGap` |
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

## Corpus audit correction (2026-08-19)

The "Corpus reuse audit" above ends with *"Confirmed absent: any Selberg-class structure, standard
twist, or Kaczorowski--Perelli continuation."*  **That is now stale.**  The corpus carries two
Selberg-class layers:

* `formal/GaloisForLFunctions/RHTower/SelbergClass/` (31 modules).  `Basic.lean` has the exact
  carrier of `S^♯` -- `EntireFiniteOrder`, `SelbergAnalyticContinuation`, `SelbergGammaData` with
  `degree`, `conductor`, `internalShift`, and `ExtendedSelbergClass` with the Dirichlet series,
  the analytic continuation, the gamma presentation and the completed functional equation.  The
  folder also carries the asymmetric functional equation, the affine gamma pole lattice and
  residues, Barnes rectangle integrals, finite order, and root-number invariance.
* `formal/GaloisForLFunctions/SelbergClass/` (24 modules) formalising Kaczorowski--Perelli,
  *Multiple standard twists of `L`-functions*: `MultipleStandardTwistData`, the damping parameter,
  joint holomorphy of the damped twist, the termwise Mellin--Barnes representation, spectral data
  `(1.4)`--`(1.9)` with finite fibres and the residual `Ξ`, normal-family bounds on the initial
  domain, and uniqueness from the initial domain.

The continuation itself is **not yet proved there** -- those modules state explicitly that they
assert no meromorphic continuation and that the sum--integral interchange is the next obligation --
so item 2 below is still open, but it is an *in-progress* construction rather than an absent one,
and the standard twist and the class axioms must be reused from those folders rather than rebuilt.

## Lean progress -- the card's statement, for an actual class member (2026-08-19)

`formal/GaloisForLFunctions/RHTower/SelbergCuspSpectrumRadius.lean` (new, umbrella-wired,
axiom-clean) transports the whole interior layer from the abstract coefficient family to a genuine
`F ∈ S^♯`, i.e. to `RHTower.ExtendedSelbergClass`.

| Card item | Declaration |
|---|---|
| **the class axioms give a polynomial coefficient bound** `‖a(n)‖ ≤ C n²` | `ExtendedSelbergClass.exists_coeff_bound` |
| `Φ_F(s,z) = ∑ a(n) n^{-s} e(z n^{1/d})` for a class member | `ExtendedSelbergClass.theta` |
| its shift-lattice coefficients `Φ_F(s-k/d, z₀)/k!` | `ExtendedSelbergClass.shiftCoeff` |
| the standard-twist spectrum `Spec(F)` of a class member | `ExtendedSelbergClass.shiftSpectrum` |
| absolute convergence on the upper half plane, every spectral parameter | `ExtendedSelbergClass.summable_thetaTerm` |
| **Step 2's opening clause: `Φ_F(s,·)` is holomorphic on `H`** | `ExtendedSelbergClass.analyticAt_theta` |
| **Step 1 in the interior: the shift-lattice expansion** | `ExtendedSelbergClass.hasSum_shiftLatticeExpansion` |
| **the unconditional half of the boxed law** | `ExtendedSelbergClass.hadamardLimsup_shiftCoeff_le` |
| **the boxed law at an interior base point** | `ExtendedSelbergClass.hadamardLimsup_shiftCoeff_eq` |
| **radius of convergence exactly the height** | `ExtendedSelbergClass.radius_shiftLattice_eq` |
| **`Δ(0) = d q^{-1/d}`** for the presentation degree and conductor | `ExtendedSelbergClass.infDist_zero_shiftSpectrum` |
| **the cusp constant `q^{1/d}/(2πd)`** | `ExtendedSelbergClass.cuspConstant_eq` |
| **the cusp case of the boxed law for a class member** | `ExtendedSelbergClass.hadamardLimsup_shiftCoeff_cusp` |

The only new mathematics is the coefficient bound, and it is genuinely a consequence of the class
axioms rather than an extra assumption: `LSeriesSummable a 2` makes the terms `a(n)/n²` a null
sequence, hence bounded, so `‖a(n)‖ ≤ C n²` with `a(0) = 0` handled by the arithmetic-function
convention.  Everything else is the abstract layer applied to `a := F.coeff`,
`d := F.presentationDegree`, `q := F.presentationConductor`.

So the card's statement is now formal *for the actual class object*, with two named hypotheses
carried through unchanged: `0 < d` (the card's `d ≥ 1`) and, at an interior base point, the
singularity below the base point -- which is exactly the Kaczorowski--Perelli input of item 2.

Axiom audit: `propext`, `Classical.choice`, `Quot.sound`.
