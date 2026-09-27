# The Cusp–Spectrum Radius Law for the Selberg class

- **ID:** cusp-spectrum-radius-law
- **Stage:** 3-formalized (corrected statement; independent of Selberg's conjectures)
- **Type:** THEOREM (paper + Lean)
- **Source:** `../1-in-progress/selberg-orthogonality-working-log.md` §§13.1, 14.1, 23.1, 24.2, 25
- **Statement (corrected 2026-09-27):** the shift-lattice expansion of the degree-`d` theta
  function of `F ∈ S^♯` at the cusp represents `Φ_F − (singular part)` and has radius of convergence
  exactly the cusp gap `Δ(0) = dist(0, Spec F) = d(m₀/q)^{1/d}` (`= d q^{−1/d}` when `a_F(1) = 1`),
  at every base point `s`; for `ζ` the boundary law holds at every real base point with the gap
  measured to the full singular set `ℤ`.  The original claim at every `α₀ ≥ 0` with the gap
  measured to `Spec(F)` alone is false (Lean counterexample, §Correction); its corrected form is the
  open conjecture `../0-backlog/standard-twist-boundary-radius-conjecture.md`.

## Statement

Let `F ∈ S^♯` have degree `d ≥ 1` and conductor `q`. Put
```
Φ_F(s,z) := Σ_{n≥1} a_F(n) n^{−s} e(z n^{1/d})        (z ∈ H),
F_α(w)   := Σ_{n≥1} a_F(n) n^{−w} e(−α n^{1/d})       (the K–P standard twist; F_0 = F),
Δ(α₀)    := dist( α₀ , Spec(F) \ {α₀} ) ,             Spec(F) = { d(m/q)^{1/d} : a_F(m) ≠ 0 }.
```

> **Theorem (cusp radius law; corrected, Lean).** Let `m₀` be the first index with `a_F(m₀) ≠ 0`,
> so `Δ(0) = dist(0, Spec F) = d (m₀/q)^{1/d}`.  For **every** `s ∈ ℂ`,
> ```
> limsup_{k→∞} | F(s − k/d) / k! |^{1/k}  =  1 / ( 2π Δ(0) ) ,
> ```
> and for `s ∉ 1 + ℕ/d`, `ζ ∈ H`, `|ζ| < Δ(0)`,
> ```
> Φ_F(s, ζ) − P_F(s, ζ) = Σ_{k≥0} ((2πiζ)^k/k!) F(s−k/d),
> ```
> with radius of convergence exactly `Δ(0)`; `P_F(s,ζ)` is the residue at `u₀ = d(1−s)` of
> `(−2πiζ)^{−u} Γ(u) F(s+u/d)`, analytic in `ζ` on `H` (zero when `F` is entire).
> With `a_F(1) = 1` the constant is `q^{1/d}/(2πd)`.
>
> **Degree one, every boundary base point (Lean).** For `F = ζ` and every `α₀ ∈ ℝ`, `s ∉ ℕ`:
> `limsup_k |F_{α₀}(s−k)/k!|^{1/k} = 1/(2π dist(α₀, ℤ \ {α₀}))` — the gap is measured to the full
> singular set of the twist family, which contains `0`.
>
> **Original claim (refuted).** "For every `α₀ ≥ 0`, `limsup_k |F_{α₀}(s−k/d)/k!|^{1/k} =
> 1/(2π dist(α₀, Spec(F) \ {α₀}))`" is false: for `ζ` and `0 < α₀ < 1/2` the left side is
> `1/(2πα₀)` and the right side `1/(2π(1−α₀))`.

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

## Lean progress -- Step 3 in general degree, archimedean half (2026-08-19)

Step 3's opening clause -- *"by the functional equation and uniform Stirling, for `σ → −∞` with `t`
fixed, `|X(σ+it)| ≍ C[q/(2π)^d]^{|σ|}|σ|^{d|σ|}e^{−d|σ|}`"* -- is now `[LEAN-PROVED]` in **every
degree**, for the archimedean factor of Kaczorowski--Perelli's asymmetric functional equation, with
**no hypothesis beyond `0 < d`**.  The uniform Stirling estimate the card cites is replaced by an
exact root asymptotic, so no `≍` and no implied constants appear anywhere.

`formal/GaloisForLFunctions/RHTower/SelbergCuspArchimedeanRoot.lean` (new, umbrella-wired,
axioms `propext`, `Classical.choice`, `Quot.sound`):

| Card item | Declaration |
|---|---|
| the rate `λ_j/d` at which the `j`-th Gamma argument advances | `SelbergGammaData.shiftRate` |
| the two constant shifts `λ_j(1−s₀)+\bar μ_j` and `1−λ_j s₀−μ_j` | `SelbergGammaData.shiftUp`, `shiftDown` |
| the `2r` rates and shifts of the archimedean factor | `SelbergGammaData.pairRate`, `pairShift` |
| **the rates sum to one** — this *is* the definition of the degree | `SelbergGammaData.sum_pairRate` |
| the two Gamma arguments along the lattice `s₀ − k/d` | `SelbergGammaData.gammaArg_up_shift`, `gammaArg_down_shift` |
| the modulus of `h_F(s₀−k/d)`: constant, `Q`-power, `2r` Gamma moduli | `SelbergGammaData.norm_asymmetricH_shift` |
| **the root constant equals the cusp constant `q^{1/d}/(2πd)`** | `SelbergGammaData.archimedeanRootConstant_eq` |
| a `Q`-power advancing at rate `2/d` has `k`-th root `Q^{2/d}` | `tendsto_rpow_linear_rpow_inv` |
| **`(‖h_F(s₀−k/d)‖/k!)^{1/k} → q^{1/d}/(2πd)`** | `SelbergGammaData.tendsto_norm_asymmetricH_shift_rpow_inv` |

`archimedeanRootConstant_eq` is the arithmetic identity behind the card's constant:
`Q^{2/d}·∏_j(λ_j/d)^{2λ_j/d} = q^{1/d}/(2πd)` with `q = (2π)^d Q²∏λ_j^{2λ_j}`.  The `2π` on the
right is exactly the `(2π)^{-r}` prefactor of `h_F` becoming invisible to the root, and the `1/d`
is exactly `∏_j d^{-2λ_j/d} = d^{-1}` — the same "rates sum to one" that makes the factorial
cancel.  Nothing is tuned: both sides are computed from the gamma presentation alone.

### The analytic layer this rests on

Four new reusable `HTGeometry` modules, all axiom-clean.  None of them existed in the corpus;
the corpus's previous root technology (`RootGrowthEngine`, `ScaledRootGrowth`) deliberately avoids
Stirling and therefore cannot see the constant `(c/e)^c`, which is exactly what a degree-`d`
lattice needs.

`HTGeometry/GammaWendelInequality.lean` — log-convexity of `Γ`:

| Item | Declaration |
|---|---|
| **Wendel's inequality** `Γ(x+a) ≤ Γ(x)x^a` for `0 ≤ a ≤ 1` | `Gamma_add_le` |
| its lower companion `Γ(x)x ≤ Γ(x+a)(x+a)^{1−a}` | `le_Gamma_add` |

`HTGeometry/GammaRatioAsymptotic.lean` — the ratio law:

| Item | Declaration |
|---|---|
| `Γ(x+a)/(Γ(x)x^a) → 1` for a shift in `[0,1]` | `tendsto_Gamma_add_div_rpow_unit` |
| the same after peeling whole units | `tendsto_Gamma_add_div_rpow_nat` |
| **`Γ(x+a) ∼ Γ(x)x^a` for every `a ≥ 0`** | `tendsto_Gamma_add_div_rpow` |

`HTGeometry/GammaRootAsymptotic.lean` — Stirling with an explicit remainder, and the root law:

| Item | Declaration |
|---|---|
| `∫_0^∞ (x+a)^{-2}dx = 1/a` | `integrableOn_invSqShift`, `integral_Ioi_inv_sq_shift` |
| **the Binet kernel is at most `1/(8a)`** | `abs_binetKernel_le` |
| **Stirling with an explicit remainder** | `abs_log_Gamma_sub_stirling_le` |
| `log Γ(cx+b)/x − c log x → c log c − c` | `tendsto_log_Gamma_linear_div` |
| `exp(c log c − c) = (c/e)^c` | `exp_stirling_eq_rpow` |
| **`Γ(cx+b)^{1/x}/x^c → (c/e)^c`** | `tendsto_Gamma_linear_rpow_inv`, `..._nat` |
| **`(k!)^{1/k}/k → 1/e`** | `tendsto_factorial_rpow_inv_div` |

`HTGeometry/GammaVerticalRootAsymptotic.lean` — the vertical line is invisible to the root:

| Item | Declaration |
|---|---|
| the comparison ratio `Γ(x)/‖Γ(x+iy)‖` | `gammaVerticalRatio` |
| **it decreases along unit steps**, by the functional equation | `gammaVerticalRatio_add_one_le`, `gammaVerticalRatio_add_nat_le` |
| `Γ ≤ 1` on `[1,2]`, from Wendel | `Gamma_le_one_of_mem_Icc` |
| a positive minimum of `‖Γ(·+iy)‖` on `[1,2]` | `exists_pos_le_norm_Gamma_verticalPoint` |
| **`Γ(x) ≤ C‖Γ(x+iy)‖` for all `x ≥ 1`** | `exists_const_Gamma_le_norm_Gamma_vertical` |
| a positive constant is invisible to the root | `tendsto_const_rpow_inv` |
| **`‖Γ(cx+β)‖^{1/x}/x^c → (c/e)^c`** for complex `β` | `tendsto_norm_Gamma_linear_rpow_inv`, `..._nat` |

`HTGeometry/GammaProductRootLaw.lean` — the combination law:

| Item | Declaration |
|---|---|
| a constant base with a family of exponents | `prod_rpow_const` |
| **`k/(k!)^{1/k} → e`** | `tendsto_div_factorial_rpow_inv` |
| **`(∏_i ‖Γ(c_i k+β_i)‖/k!)^{1/k} → ∏_i c_i^{c_i}`** when `∑ c_i = 1` | `tendsto_prod_norm_Gamma_div_factorial_rpow_inv` |

The last statement is the whole mechanism in one line: the powers of `k` contributed by the `2r`
Gamma factors multiply to `k^{∑c_i} = k`, which is exactly the factorial's root, and the `e`'s
cancel for the same reason.  The vertical comparison is what lets the *complex* shifts `μ_j` and
the base point `s₀` be arbitrary: the ratio `Γ(x)/‖Γ(x+iy)‖` is multiplied by `x/‖x+iy‖ ≤ 1` at
each unit step, so it is bounded by its values on `[1,2]`, and a bounded factor cannot change a
`k`-th root.  No Euler product, no Weierstrass factorization, and no Laplace method is used.

### What Step 3 still needs in general degree

Three items, all of them the card's own hypotheses rather than missing mathematics:

1. **The sine factor.**  `S_F(s) = 2^r ∏_j sin(π(λ_j s+μ_j))` is bounded along the lattice (its
   imaginary part is constant in `k`), so it cannot raise the root; what is needed is a *frequent*
   lower bound, which is exactly the card's "`s` off the exceptional lattice `{s*_ℓ+k/d}`".  When
   some `Im(λ_j s₀+μ_j) ≠ 0` the factor is bounded below outright; when the presentation has rank
   one — every degree at most two — the rate is `λ_1/d = 1/2` and the factor has period four in
   `k`, so `cos²+sin² = 1` supplies the frequent lower bound unconditionally, exactly as
   `exists_cosShift_pos` does for `ζ`.
2. **`\bar F(1−\bar s) → \bar a_F(1)`.**  This is a Dirichlet-series limit to the right along a
   horizontal ray, not the real axis.
3. **Applicability of the functional equation at `s₀−k/d`**, i.e. membership in
   `ExtendedSelbergClass.asymmetricFERegularSet` — pair-analyticity of the completed value and
   Gamma-pole-freeness.  This is where the class's own analytic continuation enters.

## Lean progress -- Step 3 in general degree, complete assembly (2026-08-19)

The three items listed above as "what Step 3 still needs" are now items **1 and 3 only**: the
Dirichlet-series limit is proved, the sine factor's boundedness is proved unconditionally, and the
frequent lower bound is proved unconditionally whenever the gamma presentation has rank one --
which is every degree at most two, i.e. every row of the card's Verifications table.

`formal/GaloisForLFunctions/HTGeometry/LSeriesRightLimit.lean` (new, umbrella-wired, axiom-clean):

| Card item | Declaration |
|---|---|
| the terms decrease as the real part grows | `norm_term_le_of_re_le` |
| past the second term the decay is geometric in `Re s` | `norm_term_le_two_pow` |
| a polynomial coefficient bound gives absolute convergence | `summable_norm_term_of_rpow_bound` |
| **`L(f,s) → f(1)` along *every* family with `Re s → ∞`** | `tendsto_LSeries_of_re_atTop` |

This is the general form of the corpus's `tendsto_riemannZeta_of_re_atTop`, and the form Step 3
needs: the reflected argument `1-\bar s` travels along a *horizontal* ray, not the real axis, so
mathlib's `LSeries.tendsto_cpow_mul_atTop` (real ray only) does not apply.

`formal/GaloisForLFunctions/HTGeometry/LimsupPositiveFactor.lean` (new, umbrella-wired,
axiom-clean):

| Card item | Declaration |
|---|---|
| a positive constant scales a `limsup` | `limsup_const_mul` |
| **`a → κ > 0` and `limsup b = 1` give `limsup (a·b) = κ`** | `limsup_mul_eq_of_tendsto` |

The corpus's `limsup_mul_eq_one_of_tendsto_one` handles a convergent group tending to *one*, which
is what degree one needs; in degree `d` the archimedean group converges to the cusp constant
instead, so the unit-factor law has to be scaled.

`formal/GaloisForLFunctions/RHTower/SelbergShiftRootLaw.lean` (new, umbrella-wired, axiom-clean):

| Card item | Declaration |
|---|---|
| **the invariant phase `ω_F` is unimodular** | `SelbergGammaData.norm_invariantRootNumber` |
| `‖sin w‖ ≤ e^{\|Im w\|}` | `norm_sin_le_exp_abs_im` |
| the sine arguments keep their imaginary parts along the lattice | `SelbergGammaData.sine_arg_im` |
| **the sine factor is bounded along the lattice, no hypotheses** | `SelbergGammaData.exists_bound_norm_asymmetricS_shift` |
| **`‖\bar F(1-\bar s_k)‖ → \|a_F(1)\|`** | `ExtendedSelbergClass.tendsto_norm_reflection_shift` |
| **`limsup_k (‖F(s₀-k/d)‖/k!)^{1/k} = q^{1/d}/(2πd)`** | `ExtendedSelbergClass.limsup_norm_shift_rpow_inv` |

`formal/GaloisForLFunctions/RHTower/SelbergRankOneSineFactor.lean` (new, umbrella-wired,
axiom-clean):

| Card item | Declaration |
|---|---|
| a half rate forces rank one | `SelbergGammaData.rank_eq_one_of_halfRate` |
| the unique index and its product law | `SelbergGammaData.soleIndex`, `eq_soleIndex`, `prod_eq_soleIndex` |
| **the sine factor has period four in `k`** | `SelbergGammaData.asymmetricS_shift_periodic` |
| it cannot vanish at both `k = 0` and `k = 1`, since `sin²+cos² = 1` | `SelbergGammaData.exists_pos_norm_asymmetricS_shift` |
| **the frequent lower bound, unconditionally** | `SelbergGammaData.exists_frequently_le_norm_asymmetricS_shift` |
| **Step 3 with the sine hypothesis discharged** | `ExtendedSelbergClass.limsup_norm_shift_rpow_inv_of_halfRate` |

`limsup_norm_shift_rpow_inv` is the card's Step 3 in full generality.  Its hypotheses are exactly
the card's own: `d > 0`, `a_F(1) ≠ 0` (the card's `a_F(1) = 1`), applicability of the functional
equation along the lattice, and the frequent non-degeneracy of the sine factor (the card's "`s` off
the exceptional lattice").  Everything else is proved: the phase is unimodular, the archimedean
factor has root exactly `q^{1/d}/(2πd)`, the reflected series has root one, and the sine factor is
bounded, hence cannot raise the root.

`limsup_norm_shift_rpow_inv_of_halfRate` removes the sine hypothesis outright for a rank-one
presentation.  In that case the single rate is `λ_1/d = 1/2`, so the sine factor has period four in
`k`; if it vanished at both `k = 0` and `k = 1` then `sin z` and `cos z` would both vanish, which
`sin²+cos² = 1` forbids.  This is the same mechanism the corpus already used for `ζ`
(`exists_cosShift_pos`), now derived from the class axioms rather than from the explicit zeta
functional equation, and it covers every member of degree at most two -- the whole Verifications
table.

### Remaining for Step 3

Only membership in `ExtendedSelbergClass.asymmetricFERegularSet` along the lattice, i.e.
pair-analyticity of the completed value at `s₀-k/d` and `1-\bar s₀+k/d` together with
Gamma-pole-freeness.  That is a statement about the class member's own analytic continuation, and
is the same input items 1 and 2 of "What is not yet formalized" need.

## Lean progress -- Step 3 has no remaining hypothesis (2026-08-20)

The last item of "Remaining for Step 3" -- membership of the shift lattice in
`ExtendedSelbergClass.asymmetricFERegularSet` -- is discharged.

`formal/GaloisForLFunctions/RHTower/SelbergShiftLatticeRegularity.lean` (new, umbrella-wired,
axiom-clean):

| Card item | Declaration |
|---|---|
| a nonzero height excludes the reflected continuation pole, with no real-part condition | `selbergVerticalPoint_reflection_ne_one_of_im_ne_zero` |
| the reflected completed value is analytic at every nonzero height | `analyticAt_selbergCompletedValue_verticalTail_reflection_of_im_ne_zero` |
| pair-analyticity from the height alone | `ExtendedSelbergClass.mem_completedFEContourSafeSet_of_im_ne_zero` |
| the Gamma-tail bound is non-negative | `SelbergGammaData.gammaTailHeight_nonneg` |
| **the height criterion for regularity, with no real-part hypothesis** | `ExtendedSelbergClass.mem_asymmetricFERegularSet_of_height` |
| the shift lattice is horizontal | `selbergShiftPoint_eq` |
| **the whole shift lattice is regular** | `ExtendedSelbergClass.shiftLattice_mem_asymmetricFERegularSet` |
| **Step 3, regularity hypothesis discharged** | `ExtendedSelbergClass.limsup_norm_shift_rpow_inv_of_height` |
| **Step 3 for a rank-one presentation, every continuation hypothesis discharged** | `ExtendedSelbergClass.limsup_norm_shift_rpow_inv_of_halfRate_of_height` |

The point is that all three regularity conditions -- analyticity of the completed value, analyticity
of its reflection, and Gamma-pole-freeness -- depend only on the **height** of the point, while the
shift lattice `s₀ - k/d` is *horizontal*.  So one height inequality on the base point,
`gammaTailHeight(F) < |Im s₀|`, puts the entire lattice inside the regular set.

The corpus already carried the height criterion, but with a spurious `0 < σ` side condition; that
condition was only excluding the reflected continuation pole at `s = 1`, i.e. only ruling out
`1 - \bar s = 1`, which a nonzero height already rules out.  Removing it is what makes the criterion
usable on a lattice that runs to the left, where the real part goes to `-∞`.

So Step 3 of the card -- *"the independent cusp constant via the functional equation and uniform
Stirling"* -- now reads, in every degree and with no analytic-continuation premise:

```
theorem ExtendedSelbergClass.limsup_norm_shift_rpow_inv_of_halfRate_of_height
    (F : ExtendedSelbergClass) (hd : 0 < F.gammaData.degree) {s₀ : ℂ}
    (ha1 : (F.coeff 1 : ℂ) ≠ 0)
    (hrate : ∀ j, F.gammaData.lambda j = F.gammaData.degree / 2)
    (hheight : F.gammaData.gammaTailHeight < |s₀.im|) :
    limsup (fun k : ℕ =>
        (‖F (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖ / (k.factorial : ℝ)) ^ (1 / (k : ℝ)))
      atTop
      = F.gammaData.conductor ^ (1 / F.gammaData.degree) / (2 * Real.pi * F.gammaData.degree)
```

`ha1` is the class normalisation `a_F(1) = 1` (an axiom of the full class `SelbergClass`, a
hypothesis for the extended carrier); `hrate` is the rank-one/half-rate presentation, which covers
the whole Verifications table; `hheight` is a condition on the base point, which the card's own
statement already allows ("for every `s ∈ ℂ` off the exceptional lattice").

### What remains on this card

Items 1 and 2 of "What is not yet formalized", for a **general** class member: Kaczorowski--Perelli
standard-twist theory -- entire continuation of `F_α` for `α ∉ Spec(F)` and `ρ_0(α) ≠ 0` on the
spectrum.  (The note there that "the corpus has no Selberg-class layer at all" is now stale: the
`RHTower/SelbergClass/` layer exists and carries the axioms, the completed value, the asymmetric
functional equation and its regular set.)  Everything else -- Step 1 interior, Step 2 mechanism,
Step 3 in every degree, and the whole Verifications table at degree one (`ζ`, every Dirichlet
character) and degree two (divisor function) -- is unconditional in Lean.

## Full-class normalization wrapper (2026-08-25)

`formal/GaloisForLFunctions/RHTower/SelbergFullShiftRootLaw.lean` now states Step 3 directly for the
actual full `SelbergClass`, rather than asking callers to re-supply the extended carrier's
first-coefficient premise:

```text
SelbergClass.limsup_norm_shift_rpow_inv_of_height
SelbergClass.limsup_norm_shift_rpow_inv_of_halfRate_of_height
```

Both replace `ha1 : a_F(1) ≠ 0` by the full-class normalization `F.coeff_one : a_F(1) = 1`.  The
second also discharges sine nondegeneracy for a rank-one/half-rate gamma presentation, so its only
inputs are positive degree, the presentation identity, and the base-height inequality already in
the card.  Direct check and targeted leaf build pass; both declarations audit to
`[propext, Classical.choice, Quot.sound]` and are wired into `RHTower` without building the
umbrella.

This removes a representational premise from the exact full-class cusp constant.  Card remains at
Stage 2 solely because the general Kaczorowski--Perelli standard-twist spectrum theorem is still
unformalized.

## Exact standard-twist spectral spacing (2026-08-31)

`formal/GaloisForLFunctions/HTGeometry/ShiftSpectrumSpacing.lean` now formalizes the arithmetic
spacing law for the standard-twist lattice

```text
shiftSpectrumValue degree conductor m = degree * (m / conductor)^(1 / degree).
```

The module proves, for positive degree and conductor:

```text
strictMono_shiftSpectrumValue
shiftSpectrumValue_mem
min_adjacent_gap_le_dist_of_mem_shiftSpectrum_ne
infDist_shiftSpectrum_diff_eq_min_adjacent
```

Thus every distinct supported spectral point is at least the smaller adjacent full-lattice gap
away.  When `m > 1` and both adjacent coefficients are nonzero, the distance from the `m`-th
spectral point to the rest of the spectrum is exactly the minimum of those two adjacent gaps.
This discharges all set-theoretic and order-theoretic premises in the nearest-neighbour argument.

It also exposes a necessary qualification in the paper wording: arbitrary zero coefficients can
create support gaps larger than the adjacent full-lattice gap.  Therefore an unconditional upper
comparison `Delta(alpha_m) \asymp m^(1/degree - 1)` for the coefficient-supported spectrum needs a
support-density or adjacent-support theorem.  The full-lattice lower bound and the exact law under
adjacent support are unconditional.

Direct `lake env lean` checking, targeted leaf build, and axiom audit pass.  All five public
declarations use exactly `[propext, Classical.choice, Quot.sound]`; no heartbeat override was added.
The module is wired into `HTGeometry` without building the umbrella.  This card remains at Stage 2
because general Kaczorowski--Perelli continuation and nonzero-residue theorems are still absent.

`formal/GaloisForLFunctions/HTGeometry/ShiftSpectrumSpacingAsymptotic.lean` adds the exact leading
asymptotic behind the card's spacing scale:

```text
shiftSpectrumValue_forwardGap_isEquivalent:
  alpha_(m+1) - alpha_m ~ q^(-(1/d)) * m^(1/d - 1).
```

The proof discharges the differentiability step through the corpus's general finite-difference
theorem `polynomialPowerFiniteDifference_isEquivalent`; callers supply no differentiability
witness.  Its reusable real-power lemma is `realPower_forwardGap_isEquivalent`.  Direct check,
targeted leaf build, and axiom audit pass; both declarations use exactly
`[propext, Classical.choice, Quot.sound]`.  The result deliberately concerns the full lattice and
does not assert that a sparse coefficient-supported spectrum has an adjacent supported point.

### 2026-08-31 general-rank sine recurrence

`formal/GaloisForLFunctions/RHTower/SelbergGeneralSineRecurrence.lean` removes the rank-one
presentation restriction from the independent cusp-growth proof.  For every finite Selberg gamma
presentation and every base point with `asymmetricS s₀ ≠ 0` (the card's stated exclusion of the
exceptional lattice), it constructs explicit positive factor margins, a positive product
tolerance, and an explicit positive product floor.  Delayed simultaneous `2π`-phase recurrence
then proves that the asymmetric sine factor exceeds that floor frequently along the full shift
lattice.  Consequently
`SelbergClass.limsup_norm_shift_rpow_inv_of_height_of_asymmetricS_ne_zero` proves the general-rank
cusp constant; normalization constructs the nonzero first coefficient, lattice-height regularity
constructs every analytic-regularity witness used by the existing internal theorem, and recurrence
constructs the former frequent-lower-bound witness.  No Hilbert, differentiability,
commensurability, rank-one, or supplied recurrence structure remains as a premise.

The leaf direct check, targeted build, and axiom audit pass.  All 17 new declarations use exactly
`[propext, Classical.choice, Quot.sound]`.  The build also exposed and repaired a removed mathlib
name in `GeometricThetaUnbounded.lean` and `NonnegThetaCuspGrowth.lean`; reusable
`tendsto_natCast_rpow_neg_atTop` now supplies the required inverse-real-power limit and has the same
axiom footprint.  The module is wired into `RHTower` without an umbrella build.

This does not yet formalize the card's external Kaczorowski--Perelli boundary-continuation and
nonzero-residue input for arbitrary standard twists.  Card therefore remains Stage 2.

### 2026-08-31 canonical premise-free positive-rank law

`formal/GaloisForLFunctions/RHTower/SelbergCanonicalCuspRootLaw.lean` removes the remaining three
proposition arguments from the independent cusp-growth theorem.  It defines the canonical base
point

```text
s_F = i * (gammaTailHeight(F) + 1)
```

and proves internally that its height is above every selected Gamma pole line and that every
affine sine argument has nonzero imaginary part.  Hence the complete asymmetric sine product is
nonzero.  For `PositiveRankSelbergClass`, positivity of presentation degree is derived from the
positive Gamma slopes.  The capstone

```text
PositiveRankSelbergClass.canonicalCuspRootLaw
```

has no proposition premise: positive rank is part of its carrier type, while positive degree,
safe height, normalization, analytic regularity, sine nonvanishing, and simultaneous recurrence
are all discharged in Lean.  Direct source check and the single targeted leaf build pass.  All
eight new theorems audit to exactly `[propext, Classical.choice, Quot.sound]`; the module is wired
into `RHTower` without building that umbrella.

This closes every representational premise in the card's independent general-rank radius law.  It
does not supply the external Kaczorowski--Perelli standard-twist boundary continuation and
nonzero-residue theorem, so the card remains at Stage 2.

## Correction — the boxed theorem is false off the spectrum (2026-09-27)

**The boxed statement, read literally, is false.**  For `F = ζ` (`d = q = 1`, `Spec(ζ) = {1,2,3,…}`)
and every base point `0 < α₀ < 1/2`, the growth constant of `F_{α₀}(s−k)/k!` is `1/(2π α₀)`, not
`1/(2π Δ(α₀)) = 1/(2π(1 − α₀))`.  Lean certificate, `RHTower/ZetaTwistOffSpectrumGap.lean`:

```text
infDist_shiftSpectrum_oneCoeff                 dist(α, Spec(ζ) \ {α}) = 1 − α   for α < 1
twistGap_neg_of_lt_half                        the true gap at −α is α            for 0 < α < 1/2
zetaTwist_growth_ne_shiftSpectrumGap           the boxed law fails at every 0 < α₀ < 1/2, every s₀ ∉ ℕ
zetaTwist_growth_ne_shiftSpectrumGap_tenth     the instance α₀ = 1/10, s₀ = 1/2: 5/π ≠ 5/(9π)
```

The left side is the corpus's unconditional `hadamardLimsup_zetaTwistShift`; the right side is the
card's own `Δ`.  All four declarations audit to `[propext, Classical.choice, Quot.sound]`.

*Where the proof breaks.*  Step 2 lists as singular only the boundary points `−α` with
`α ∈ Spec(F)`.  Two further kinds of singular shift exist:

1. `α = 0` whenever `F` has a pole at `s = 1`: then `F_0 = F` is not entire, and `Φ_F(s,·)` is
   singular at `z = 0` (for `ζ`, `Li_s(e^{2πiz})` has its branch point there).  `Spec(F)` omits `0`.
2. `α = −β`, `β ∈ Spec(F)`: `F_{−β}(s) = conj(F̄_β(s̄))` and `Spec(F̄) = Spec(F)`, so the reflected
   spectrum is singular as well.

So the gap must be measured to the full singular set
`Sing(F) = {α ∈ ℝ : F_α is not entire} ⊇ Spec(F) ∪ (−Spec(F)) ∪ {0 if F has a pole}`.  For `ζ` this
is exactly the corpus theorem `hadamardLimsup_zetaTwistShift_eq_infDist` (singular set `ℤ`).

A second gap: the radius of a Taylor expansion at `−α₀` is the distance to the nearest singularity
of the continuation *anywhere in `ℂ`*, including the lower half plane, where `Φ_F(s,·)` is not given
by its series.  Step 2 controls only real boundary points.  In degree two the Voronoi transform of
`ζ²` already exhibits nonreal singular points (`z = −2i√n`, from the `K_0` kernel); they are not the
nearest ones there, but no argument excludes nearer nonreal singularities in general degree.  The
boundary law for general `α₀ ≠ 0` and `d ≥ 2` is therefore an open conjecture, not a theorem; it is
moved to its own card.

**Positive survivor — the cusp law holds at every base point, for every class member.**  At
`α₀ = 0` the boxed law is true, and unconditionally so.  New modules:

```text
HTGeometry/ShiftSpectrumFirstIndex.lean
  tendsto_cpow_mul_LSeries_of_re_atTop        m^w L(f,w) → f(m) when f vanishes below m, Re w → ∞
  infDist_zero_shiftSpectrum_of_first         dist(0, Spec) = d (m/q)^{1/d} at the first index m
RHTower/SelbergCuspGrowthEveryBasePoint.lean
  ExtendedSelbergClass.firstIndex             m₀ = first n with a(n) ≠ 0
  ExtendedSelbergClass.value_eq_asymmetric_of_farLeft
                                              the asymmetric FE pointwise far to the left, including
                                              at trivial zeros (continuity from nonreal points)
  SelbergGammaData.exists_asymmetricS_shift_ne_zero
                                              the sine factor is nonzero among 2r+1 lattice points:
                                              zeros of the j-th factor are spaced d/λ_j, Σ λ_j/d = 1/2
  SelbergGammaData.exists_frequently_le_norm_asymmetricS_shift_everywhere
  ExtendedSelbergClass.tendsto_norm_reflection_shift_rpow_inv      reflected root → m₀^{-1/d}
  ExtendedSelbergClass.limsup_norm_shift_rpow_inv_firstIndex
  ExtendedSelbergClass.cuspGrowthLaw
      ∀ F ∈ S^♯, d > 0, ∀ s₀ ∈ ℂ:  limsup_k (‖F(s₀−k/d)‖/k!)^{1/k} = 1/(2π dist(0, Spec F))
  SelbergClass.cuspGrowthLaw                  a_F(1) = 1:  = q^{1/d}/(2πd)
```

This removes every premise of the earlier Step-3 theorems (height above the Gamma tail, `a_F(1) ≠ 0`,
nonvanishing of the sine factor at the base point): there is no exceptional set of base points at
all, and `a_F(1) = 0` is allowed (the gap is then `d(m₀/q)^{1/d}`, still the distance from the cusp
to the spectrum).  Remaining for this card: the cusp expansion identity
`Φ_F(s,ζ) − P_F(s,ζ) = Σ_k (2πiζ)^k F(s−k/d)/k!` on `H ∩ {|ζ| < Δ(0)}` (Step 1 at the cusp, by
Mellin–Barnes), then the card is restated to the proved cusp law plus the degree-one boundary law
with the corrected gap.

## Lean progress — the cusp expansion is formal; Stage 3 (2026-09-27)

Step 1 at the cusp — the Mellin–Barnes expansion with its singular part — is now a Lean theorem for
every class member, completing the corrected card.  New leaves:

```text
HTGeometry/GammaHalfIntegerLineBound.lean
  Real.Gamma_nat_add_three_halves      Γ(K+3/2) = √π ∏_{j≤K}(j+1/2)
  norm_Gamma_neg_half_line_le(_exp)    ‖Γ(−K−1/2+it)‖ ≤ π√2 e^{−π|t|/2}/Γ(K+3/2), uniformly in K
  norm_Gamma_le_Gamma_re_div           ‖Γ(z)‖ ≤ Γ(Re z)/(1 + (Im z)²/(Re z+1)²)
  integral_inv_one_add_affine_sq       ∫ (1 + (a+bt)²/B²)^{-1} dt = πB/|b|
HTGeometry/FinitePoleVerticalContourShift.lean
  verticalIntegral_sub_eq_sum_laurentCoeff_of_horizontal_tendsto_seq
                                       vertical contour shift across finitely many poles of any order
  laurentCoeff_neg_one_of_eq_div       residue of G(z)/(z−p) is G(p)
RHTower/SelbergStripPolynomialGrowth.lean
  ExtendedSelbergClass.exists_polynomial_bound_strip
                                       ‖F(w)‖ ≤ C |Im w|^N on every vertical strip (Phragmén–Lindelöf
                                       against finite order; the FE edge bound cancels the sine growth)
RHTower/SelbergThetaMellinBarnes.lean
  ExtendedSelbergClass.theta_imag_eq_mellinBarnes
                                       Φ_F(s, iy) = (1/2π) ∫ (2πy)^{-(c+it)} Γ(c+it) F(s+(c+it)/d) dt
RHTower/SelbergCuspMellinResidues.lean
  ExtendedSelbergClass.laurentCoeff_cuspMellinIntegrand_neg_nat
                                       residue at u = −k is x^k (−1)^k/k! F(s−k/d)
  ExtendedSelbergClass.cuspPolarPart, analyticOnNhd_cuspPolarPart
                                       the singular part, analytic on H (Leibniz on the clearing shift)
RHTower/SelbergCuspMellinEstimates.lean
  integrable_cuspMellinIntegrand_right, tendsto_hIntegral_cuspMellinIntegrand
RHTower/SelbergCuspLeftLineDecay.lean
  eventually_norm_cuspMellinIntegrand_left_le, eventually_integrable_norm_integral_left_le
  tendsto_integral_cuspMellinIntegrand_left
                                       the far-left integrals → 0 for y < Δ(0): their K-th roots
                                       tend to y/Δ(0)
RHTower/SelbergCuspExpansion.lean
  ExtendedSelbergClass.hadamardLimsup_shift        growth functional = 1/(2πΔ(0)), extended reals
  ExtendedSelbergClass.radius_cuspExpansion        radius of Σ (2πiζ)^k F(s−k/d)/k! is exactly Δ(0)
  ExtendedSelbergClass.hasSum_cuspExpansion_imag   the expansion on the imaginary axis
  ExtendedSelbergClass.hasSum_cuspExpansion        the expansion on H ∩ {|ζ| < Δ(0)}
```

| Corrected card item | Lean |
|---|---|
| cusp growth law, every `s`, every `F ∈ S^♯` | `ExtendedSelbergClass.cuspGrowthLaw`, `hadamardLimsup_shift` |
| cusp constant `q^{1/d}/(2πd)` for the Selberg class | `SelbergClass.cuspGrowthLaw` |
| expansion `Φ_F − P_F = Σ (2πiζ)^k F(s−k/d)/k!` at the cusp | `ExtendedSelbergClass.hasSum_cuspExpansion` |
| radius exactly `Δ(0)` | `ExtendedSelbergClass.radius_cuspExpansion` |
| singular part analytic | `ExtendedSelbergClass.analyticOnNhd_cuspPolarPart` |
| degree one, every boundary base point, corrected gap | `hadamardLimsup_zetaTwistShift_eq_infDist` |
| the original general law is false | `zetaTwist_growth_ne_shiftSpectrumGap(_tenth)` |
| interior law, Verifications arithmetic, Consequences arithmetic, jump lemma | earlier tables above |

The "Consequences" that rest on the boundary law at spectral points (`Δ(α_m) → 0` forcing the
far-left growth of `F_{α_m}` to blow up) are statements about the refuted/open general law; their
arithmetic halves are formal (`tendsto_shiftSpectrumGap_nhds_zero`,
`tendsto_degreeOneLatticeRoot_atTop`), their analytic halves move with the conjecture card.

All 114 declarations of the eleven new leaves audit to `[propext, Classical.choice, Quot.sound]`
(or fewer); each leaf passes `lake env lean` with no messages and a targeted `lake build --old`, and
all are wired into `HTGeometry`/`RHTower`.  No `sorry`, no axioms, no heartbeat options.

- 2026-09-27 -- boxed general law refuted in Lean; cusp law proved for every base point and every
  class member; cusp expansion with singular part and exact radius proved; card restated and moved
  to `3-formalized`; corrected general boundary law opened as
  `0-backlog/standard-twist-boundary-radius-conjecture.md`.
