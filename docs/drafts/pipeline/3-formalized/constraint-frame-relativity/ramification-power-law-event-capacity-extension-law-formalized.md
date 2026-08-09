# Ramification-power law event, capacity response, and analytic excess — formalized

- **ID:** `cfr-ramification-power-law-event-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `ramification-power-law-event-capacity-extension-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellRamificationPower` | new |
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellExcessDirichlet` | new |
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.BernoulliBooleanGibbs` | new, reusable |
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.SchurCapacity` | new, reusable |
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellCapacityDepth` | new |
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellCapacitySharpScale` | new |
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellCapacityAsymptotic` | new |

All wired into `GaloisForLFunctions.HTGeometry`.

## New infrastructure

`ShellRamificationPower` computes the high-exponent shell indicator of a perfect power.  A corpus
search over `shellIndicator`, `MFree`, and `mFreeIndicator` found the shell layer
(`RHTower/HighExponentShell*`) but no statement about `k ↦ k^r`; the module supplies

* `mFree_iff_forall_factorization_lt` — `MFree j n ↔ ∀ p prime, v_p(n) < j` for `n ≠ 0`;
* `mFree_pow_succ_iff`, `mFree_pow_iff` — the two divisibility transfers along `k ↦ k^r`;
* `IsRPow`, `not_isRPow_of_factorization_not_dvd`, `factorization_two_pow_mul_three_apply`.

`SchurCapacity` and `BernoulliBooleanGibbs` are the reusable finite-covariance layer described in
the companion of the Boolean-descent card.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintFrameRelativity`.

Theorem 1.1 — exact ramification-law pullback, card `(RP.4)`:

1. `shellIndicator_pow` — `shellIndicator (r*m) (k^r) = shellIndicator m k` for `r ≠ 0`, every `k`.
2. `shellIndicator_powMonoidHom` — the same law stated for the monoid endomorphism
   `powMonoidHom r : ℕ →* ℕ`, so `P_1 = id` and `P_s ∘ P_r = P_{sr}` are the monoid identities.

Theorem 2.1 — positive affine excess, card `(RP.5)`–`(RP.7)`:

3. `powerImageStream`, `excessStream` — the two `{0,1}`-valued streams; their sum is the shell
   stream (`powerImageStream_add_excessStream`), and both are bounded by one in absolute value.
4. `powerImageStream_pow` — the image stream restricted to `r`-th powers is the level-`m` shell.
5. `excess_witness`, `excessStream_witness` — `2^{rm}·3` lies in the level-`rm` shell and is not an
   `r`-th power, so the excess is nonzero.
6. `lSeries_powerImageStream` — reindexing along `k ↦ k^r` gives `S_m(r s)`.
7. `lSeries_shell_eq_dilate_add_excess` — the boxed decomposition
   `S_{rm}(s) = S_m(r s) + C_{m,r}(s)` on `re s > 1`, with both summands `LSeriesSummable`.

Theorem 3.1 — one power event changes capacity, card `(RP.9)`–`(RP.13)`:

8. `occVar`, `occVar_eq`, `occVar_le`, `occVar_ge`, `occVar_mono` — `w = x/(1+x)²` with the two
   bounds `x/4 ≤ w ≤ x` on `(0,1]` and monotonicity there.
9. `Aperture` — an ordered aperture `p_0 < ⋯ < p_{d-1}` of at least two primes, with `fug`, `wt`,
   `clock`, and `capacity`.
10. `Aperture.capacity_pos` — strict positivity `(RP.11)` left inequality.
11. `Aperture.capacity_le_sum_fug`, `Aperture.capacity_le_card_mul_fug_least` — the two upper
    bounds of `(RP.11)`.
12. `Aperture.tendsto_capacity_atTop` — `(RP.12)`.
13. `Aperture.exists_depth_capacity_lt` — `(RP.13)`: some `r ≥ 2` has `D_F(rmτ) < D_F(mτ)`.

Theorem 3.2 — sharp depth scale and uniform jump threshold, card `(RP.14)`–`(RP.18)`:

14. `Aperture.gram_lower`, `Aperture.gram_upper` — two-sided bounds on the Cauchy--Binet numerator.
15. `Aperture.capC_le`, `Aperture.capC_ge` — two-sided bounds on the energy moment.
16. `Aperture.cLower`, `Aperture.cUpper`, `Aperture.cLower_pos`, `Aperture.cUpper_pos` — the two
    constants `c_F` and `C_F⁺` of `(RP.14)`.
17. `Aperture.cLower_mul_fug_le_capacity`, `Aperture.capacity_le_cUpper_mul_fug` — the boxed
    two-sided scale `(RP.15)`.
18. `Aperture.tendsto_capacity_div_fug_second` — the boxed asymptotic `(RP.16)`:
    `D(σ)/p_1^{-σ} → π²(λ_1-λ_0)²/λ_0²`.
19. `Aperture.jumpThreshold`, `Aperture.fug_second_depth`,
    `Aperture.capacity_lt_of_jumpThreshold_le` — the threshold `(RP.17)` and the strict contraction
    `(RP.18)`.

Section 4 of the card imports the shell hypertranscendence theorem rather than proving it; the
Lean parents are `RHTower.highExponentShellUpperEndCarrier_differentialIndependent_of_injective`
and `RHTower.highExponentShellUpperEndCarrier_differentialIndependent_twelve`, already in the tree.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/ShellRamificationPower.lean   # clean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/ShellExcessDirichlet.lean     # clean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/ShellCapacityDepth.lean       # clean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/ShellCapacitySharpScale.lean  # clean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/ShellCapacityAsymptotic.lean  # clean
#print axioms  ⇒  propext, Classical.choice, Quot.sound
```
