# Recurrence of ζ at every point of the strip, modulo its zeros

- **ID:** bag-recurrence-modulo-zeros
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/rh-current-frontier-map.md §BAG (open obstacle: recurrence at a point not known to be zero-free); walls 2, 7
- **Statement:** (1) a strip point carries a strongly recurrent disc iff `ζ(z₀) ≠ 0`; (2) every point with `1 − 1/(58 log(|Im z₀|+5)) < Re z₀ < 1` carries an explicit recurrent disc; (3) on every line `Re z = σ` the heights without a recurrent disc are countable, so the heights with one fill `[0, T]` up to measure zero; (4) at every strip point, with no premise, `ζ = ∏_{u∈S}(z−u)^{D(u)}·g` on a disc with `g` analytic nonvanishing and `S` the local zeros, and `ζ(·+iτ)` approaches `g` on the disc at positive lower density; at a zero `ρ₀ ∈ S`.

## Goal
Measure the zero-free premise of `zetaDiscStronglyRecurrentOn_of_zeroFree` exactly and discharge it
wherever the corpus allows. Corpus pieces reused (found with the search tool): the pointwise exclusion
`riemannZeta_ne_zero_of_exists_zetaDiscStronglyRecurrentOn`, the explicit zero-free region
`ZetaZeroFreeRegionUnrestricted.riemannZeta_ne_zero_of_lt_re`, the countability of line zeros
`XiWardCapGlobalIntegrability.countable_setOf_riemannZeta_line_eq_zero`, the disc factorization
`BacklundConverse.exists_zeta_factor_ball` (ζ on a disc about a nonvanishing point is a polynomial of its
zeros times a zero-free cofactor), the isolating circle `exists_zetaIsolatingDisc_le`, and the universality
theorem `exists_pos_density_zetaTargetReturnSet_of_analyticOnNhd` of the previous card.

What it says for the obstacle: the premise is exactly `ζ(z₀) ≠ 0`, i.e. the triviality of the local zero
divisor `S`; the orbit of ζ erases that divisor and returns to the cofactor at every point. RH is the
statement that `S = ∅` at every point of the strip. Item 2 is the first explicit unconditional recurrence
region; item 3 is the almost-every-height form (infrastructure by Wall 7, but now with a countable, not
merely density-zero, exceptional set).

## Gates
- [x] 0 → 1  well-posed, source-pure
- [x] 1 → 2  paper proofs: continuity + existing theorems (1, 2); countable line zeros (3); isolating circle → nonvanishing point → disc factorization → universality of the cofactor (4)
- [x] 2 → 3  Lean: `formal/GaloisForLFunctions/RHTower/ZetaRecurrenceAtEveryPointModuloItsZeros.lean`; `lake env lean` green; `#print axioms` standard on all eleven declarations; wired into `GaloisForLFunctions/RHTower.lean` after `ZetaVoroninUniversalityOnSmallDiscs`; lint clean for the module
- [ ] 3 → 4  not pursued

## Theorems
- `exists_zetaDiscStronglyRecurrentOn_iff_ne_zero`, `exists_headTargetUniformlyDense_iff_ne_zero`;
- `zetaDiscStronglyRecurrentOn_explicit_of_zeroFree` (radius `min(R/4,(Re z₀−1/2)/4,(1−Re z₀)/8)/2`), `riemannZeta_ne_zero_on_ball_of_mem_zeroFreeRegion` (zero-free ball of radius `(Re z₀ − 1 + a)/2`, `a = 1/(58 log(|Im z₀|+5))`), `zetaDiscStronglyRecurrentOn_of_mem_zeroFreeRegion`, `exists_zetaDiscStronglyRecurrentOn_of_mem_zeroFreeRegion`;
- `countable_setOf_not_exists_zetaDiscStronglyRecurrentOn`, `volume_setOf_not_exists_zetaDiscStronglyRecurrentOn`, `volume_setOf_exists_zetaDiscStronglyRecurrentOn_inter_Icc`;
- `exists_zeta_recurrence_modulo_zeros` (radius `r = r'/2`, zeros in `|z − z₀| < 8r`, margins `1/2 < Re z₀ − 4r`, `Re z₀ + 4r < 1`, every zero of ζ on the disc lies in `S`), `exists_zeta_recurrence_modulo_zeros_of_zero`.
- `zetaTargetReturnSet_diff_discTailBadSet_subset_headTarget` (tail-good target heights are head-target heights, any target), `exists_uniform_pos_density_headTarget_cofactor` (at every strip point the Dirichlet heads `Σ_{n≤M} n^{−z−iτ}` approximate the cofactor `g` on the disc at positive lower density, one constant for all large `M`: the cutoff-uniform head-target density of the base disc, modulo the local zero divisor).

## What remains
The obstacle itself: show `S = ∅` at a point not known to be zero-free. The factorization places it as a statement about the orbit: the self-target `P·g` is returned to at positive density iff `P = 1`. The orbit mechanism is Beurling-invariant (finite Euler products with rationally independent prime logs obey the same Kronecker–Weyl law), so no contradiction at a hypothetical zero can come from the orbit structure alone; the arithmetic must enter through the explicit formula. The bridge found: at the cofactor return heights the phases of the primes `≤ y` realize `−g'/g` on the disc (weights `n^{−Re z}`, `Re z > 1/2`), while the height-localized prime polynomial of SRT reads the same phases with weights `n^{−1/2}`; the gap between the two weightings on a fixed finite prime range is exactly the square-root threshold of SRT (open problem 1 there).

**The bridge computed (2026-10-21).** `primePolynomial f N ξ = Σ_{2≤n≤N} Λ(n) n^{−1/2} [k_f(log n) n^{−iτ} + k_f(−log n) n^{iτ}]`, `τ = 2πξ`, weights `n^{−1/2}`, frequencies `±log n`. At a cofactor-return height with Euler cutoff `y ≥ N` the phases `ω(n) = n^{−iτ}` satisfy `Σ_{y-smooth n} Λ(n) ω(n) n^{−z} ≈ −g′/g(z)` on the disc, weights `n^{−Re z}`, `Re z ≥ Re z₀ − r > 1/2`. The uniform-density mechanism shows the disc constraint has a large kernel: the phases of the primes in `(y₁, y]` move the disc values by `< δ` on a Haar-`1/2` event (Hilbert-space second moment `Σ_{p>y₁} ‖u_p‖² ≍ Σ_{p>y₁} p^{−2σ₀}`), while they move the critical-line sum `Σ_{y₁<p≤N} Λ(p) p^{−1/2} k_f(log p) ω_p` by its full random size. So for `N ≥ y₁` the prime polynomial is unconstrained by cofactor returns, and for `N ≤ y₁` it only ranges over the image of an open set of phases. Independently, the localized criterion at aperture `a` is automatic beyond the archimedean horizon `τ ≥ exp(C e^{a})` (SRT README mechanism 20: positive for `√X ≤ (¼ − ε) log T`), so its RH content sits at `√X ≳ log T`, i.e. cutoff growing with height, while universality fixes the cutoff `y` as `T → ∞`. At bandwidth `≥ 1` (head length `≥ height`) the head approximates `ζ` deterministically up to the Abel pole term `x^{1−s}/(s−1)` (Euler–Maclaurin), and Kronecker–Weyl no longer applies. Conclusion: the Bagchi orbit controls the prime phases at bandwidth zero; the criterion's content is at bandwidth `> 1` (Montgomery–Vaughan length `T`); no inequality crosses. NO POSITIVE SALVAGE on this bridge beyond the identity.

## Log
- 2026-10-21 — natural-rate constraint propagated through the calls to the recurrence and universality theorems; recompiled, olean rebuilt, axioms standard, lint clean. Bandwidth-above-one (SRT open problem 1): the lane's windowed variance is reduced exactly to the prime-pair sum `Σ_{n} Σ_{h ≲ 2ρn} Λ(n)Λ(n+h) (n(n+h))^{−1/2} k_f(log n) k_f(log(n+h)) k_η k_ω(log(1+h/n)) (1+h/n)^{2πiT}` and tied to the zero-side exchange rate (`DoubleWindowMinApertureAndPairCorrelationExchange`, `RHTower.PairCorrelationExchangeRate`); the open unit is its asymptotic for `α = log X/log T > 1`, the pair-correlation conjecture beyond one; a sieve bound reproduces the constant `2` only. No composition reaches it.
- 2026-10-21 — bridge to the SRT localized criterion computed: bandwidth mismatch, no inequality (recorded above).
- 2026-10-21 — section 5 added (cofactor head-target density, uniform in the cutoff); recompiled, olean rebuilt, axioms standard, lint clean.
- 2026-10-21 — created directly in 3-formalized; compiled, olean built single-threaded, umbrella wired, lint clean.
