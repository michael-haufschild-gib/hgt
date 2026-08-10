# Ramification Kummer-phase excess and Parseval detection law — formalized

- **ID:** `cfr-ramification-kummer-phase-excess-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `ramification-kummer-phase-excess-parseval-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.KummerPhaseExcess` | new |

Reused without duplication:

| Module | Supplies |
|---|---|
| `…ConstraintFrameRelativity.ShellRamificationPower` | `IsRPow`, `shellIndicator_pow`, `excess_witness`, `factorization_two_pow_mul_three_apply` |
| `…ConstraintFrameRelativity.ShellExcessDirichlet` | `powerImageStream`, `excessStream`, `lSeries_powerImageStream`, `lSeries_shell_eq_dilate_add_excess` |
| `…ConstraintFrameRelativity.ShellExcessSupport` | `excessSupport`, `excessSupport_mul_eq_union`, `excessSupport_disjoint_image` |

Wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintFrameRelativity`.

Theorem 1.1 — intrinsic image/complement grading, card `(KP.4)`–`(KP.5)`:

1. `isRPow_iff_factorization_dvd` — an integer is an `r`-th power exactly when `r` divides every
   prime valuation. The reverse direction constructs the root explicitly as
   `∏_{p ∈ primeFactors} p^{v_p/r}` and closes with `Nat.prod_primeFactors_pow_factorization`.
   No `r ≠ 0` hypothesis is needed.
2. `kummerResidue r N p` — the Kummer residue vector `[v(N)]_r ∈ Λ/rΛ`, coordinatewise.
3. `isRPow_iff_kummerResidue_zero` — the trivial Kummer sector is exactly the set of `r`-th
   powers.
4. `powerImageStream_eq_trivialSector`, `excessStream_eq_nontrivialSector` — card `(KP.5)`:
   `b_{m,r} = a_{rm} · 1_{[v]=0}` and `c_{m,r} = a_{rm} · 1_{[v]≠0}`, i.e. the inherited power
   image is the trivial Kummer sector of the marked shell and the marked split defect is the sum
   of all nontrivial sectors. The support form `P_r(A_m) = A_{rm} ∩ rΛ` is
   `powerImageSupport_eq_image` of the reused support module.

Theorem 2.1 — Haar extraction, card `(KP.7)`–`(KP.9)`:

5. `sectorTransform A ψ = ∑_α A_α ψ(α)` — the Kummer-phase transform on a finite aperture, whose
   Kummer quotient is a finite abelian group `G`; `haarAvg` is the normalised average over the
   dual group `Ĝ = AddChar G ℂ`, which for a finite group *is* normalised Haar measure.
6. `haarAvg_char` — card `(KP.9)`: character orthogonality, the dual average of `ψ ↦ ψ(α)` is the
   indicator of the trivial class. Built on `AddChar.sum_apply_eq_ite`.
7. `haarAvg_sectorTransform` — card `(KP.7)`: the Haar average of the phase transform is the
   trivial sector mass `A₀`.
8. `excessLSeries_eq_sub` — card `(KP.8)`: `C_{m,r}(z) = S_{rm}(z) - S_m(rz)` for `Re z > 1`.
   This is the full-strength (all primes, no aperture) form of the extraction statement: the
   trivial-sector Dirichlet series is exactly `S_m(rz)`, by the reindexing `N = k^r` already
   proved in `lSeries_powerImageStream`.

Theorem 3.1 — Parseval detector, card `(KP.10)`–`(KP.14)`:

9. `sectorTransform_sub` — the centred transform is the sum over nontrivial sectors.
10. `parseval_sectorTransform` — card `(KP.13)`, the equality:
    `|Ĝ|⁻¹ ∑_ψ ‖Φ(ψ) - A₀‖² = ∑_{α≠0} A_α²`. Proved by expanding `‖z‖² = z z̄`, using
    `ψ(α) conj ψ(β) = ψ(α-β)` (`AddChar.map_neg_eq_conj` plus the character law) and collapsing
    the inner dual sum with orthogonality.
11. `sectorEnergy_pos` — card `(KP.13)`, the strict inequality: one occupied nontrivial sector
    makes the detector positive.
12. `sqrt_sectorEnergy_le_sectorExcess` — card `(KP.14)`: `√V ≤ C`, the `ℓ² ≤ ℓ¹` inequality.

Corollary 3.2 — finite-aperture inverse-loss bound, card `(KP.15)`:

13. `sectorExcess_le_sqrt_card_mul` — `C ≤ √(|G| - 1) · √V` by Cauchy–Schwarz over the `|G| - 1`
    nontrivial classes.
14. `card_apertureKummer` — on an aperture of `d` primes the Kummer quotient `(ℤ/r)^d` has exactly
    `r^d` sectors, so the factor of `(KP.15)` is literally `√(r^d - 1)`.
15. `excess_witness_kummerResidue` — the arithmetic witness: `2^{rm} · 3` lies in the level-`rm`
    shell, is not an `r`-th power, and its Kummer residue at the prime `3` is the nonzero class
    of `1`. This is what makes the detector non-vacuous.

Theorem 4.1 — Kummer carry extension class, card `(KP.16)`–`(KP.17d)`:

16. `kummerIncl s r : ℤ/r →+ ℤ/(sr)` — multiplication by `s`, built with `ZMod.lift` from
    `n ↦ n • s`; `kummerIncl_intCast`, `kummerIncl_natCast` compute it.
17. `kummerRed s r : ℤ/(sr) →+* ℤ/s` — reduction, `ZMod.castHom`.
18. `kummerIncl_injective`, `kummerRed_surjective`, `kummerRed_comp_kummerIncl`,
    `kummerRed_eq_zero_iff` — card `(KP.16)`: the sequence
    `0 → ℤ/r →^{×s} ℤ/(sr) → ℤ/s → 0` is exact.
19. `kummerCarry s r a b = ((a.val + b.val)/s : ℤ/r)` — card `(KP.17d)`, the carry of the standard
    representatives.
20. `val_add_split` — the defining identity `a.val + b.val = s·carry + (a+b).val`.
21. `kummerCarry_cocycle` — the carry is a two-cocycle. Proved by reducing to the natural-number
    identity `carry(b,c) + carry(a,b+c) = carry(a,b) + carry(a+b,c)`, which follows from the four
    split identities by cancelling `s`.
22. `kummerCarry_extension_defect` — the carry *is* the extension defect of the standard section:
    `σ(a) + σ(b) - σ(a+b) = kummerIncl(κ(a,b))` for `σ(a) = a.val`.
23. `coboundary_cocycle` — changing the set-theoretic section changes the carry by a coboundary,
    which is itself a two-cocycle, so the class of `(KP.17b)` is unchanged.
24. `extension_class_zero_iff_coprime` — card `(KP.17c)` in its group-theoretic form: the class of
    `1` in `(ℤ/r)/s(ℤ/r)` vanishes exactly when `s` is invertible mod `r`, i.e. exactly when
    `gcd(s,r) = 1`.
25. `splits_iff_coprime` — the same criterion in extension form: the composite stage admits an
    additive section of `kummerRed` exactly when `gcd(s,r) = 1`. The forward direction shows
    `s • σ(1) = 0` forces `r ∣ σ(1).val`, making `r` a unit mod `s`; the reverse builds the
    section from a Bézout coefficient with `ZMod.lift`, avoiding CRT.

Theorem 4.2 — outer/transported sector decomposition, card `(KP.18)`–`(KP.19)`:

26. `excessSupport_mul_eq_union`, `excessSupport_disjoint_image` (reused) — card `(KP.18)`:
    `X_{m,sr} = X_{rm,s} ⊔ P_s(X_{m,r})`.
27. `excessLSeries_cocycle` — card `(KP.19)`: `C_{m,sr}(z) = C_{m,r}(sz) + C_{rm,s}(z)` for
    `Re z > 1`, from three instances of `excessLSeries_eq_sub` and
    `(sr)m = s(rm)`, `r(sz) = (sr)z`.

Capstones:

28. `kummer_parseval_detector` — Theorems 2.1 and 3.1 with Corollary 3.2 in one statement, on the
    aperture group `(ℤ/r)^F`: Haar extraction, the Parseval identity, strict positivity, and the
    two-sided bound with the explicit factor `√(r^d - 1)`.
29. `kummer_composition` — Theorem 4.2 with Theorem 4.1: the support partition, its disjointness,
    the analytic cocycle, exactness of the stage sequence in all three positions, the carry
    two-cocycle identity, and the coprime splitting criterion.

## Verification

```
lake build GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.KummerPhaseExcess
```

builds clean, no warnings.

```
#print axioms kummer_parseval_detector
#print axioms kummer_composition
#print axioms excess_witness_kummerResidue
#print axioms isRPow_iff_kummerResidue_zero
```

all report `[propext, Classical.choice, Quot.sound]` — no `sorry`, no project axiom.

## Scope

Following the card's own Lean-return note ("formalize finite-aperture character orthogonality
before the infinite compact product"), the Haar layer is developed on the finite aperture, where
the Kummer quotient is a finite abelian group and normalised counting measure on the dual group *is*
Haar measure. The infinite-rank statement `(KP.8)` — the one that carries the analytic content of
`(KP.7)` — is proved unconditionally over all of `ℕ` through the reindexing
`lSeries_powerImageStream`, so nothing analytic is lost; only the pro-toric packaging of `Ω_r` as a
compact measure space is left unformalized, and mathlib v4.32 has no infinite product measure with
which to build it.

The card's own open gates (incompatible non-Fourier comparison, nonzero curvature/interchange
defect, withheld Stokes/extension/flux response) remain open by the card's statement.
