# Suzuki critical-radical anchoring and finite-head reduction

- **ID:** `suzuki-critical-radical-anchor-finite-head-reduction`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-critical-radical-anchor-finite-head-reduction.md`
- **Lean:**
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalRadicalAnchor.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiAnnularCriticalPayment.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiAnnularTailSumPayment.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGeneralWitnessAnnularPayment.lean`
  - `formal/GaloisForLFunctions/RHTower/XiAnnularCopyCount.lean` (and its provider chain)

## Formal content

**`(SR-64.1)`, `(SR-64.12)` — the anchored cofinite payment.**  `exists_finset_anchor_payment`
produces, for *any* anchor copy, a finite head outside which the complete shifted transverse charge
is covered by the Hilbert response dispersion; `transverseCharge_le_dispersion_of_chargeFree_head`
closes the minor when the head is charge-free.  No critical-line anchor is needed: the anchor's own
charge sits inside the head.

**`(SR-64.13)`–`(SR-64.22)` — the exact height estimates.**  `chargeRatio_lt_inv_cube`,
`slope_gt_of_height`, `criticalLine_mass_and_slope`, `annular_single_witness` and
`two_witness_annular_payment` give the atomwise charge bound `29/(625(1+h)³)`, the sector floor
`83/(85(1+h))`, and the two-witness payment with the exact margin `32/675 − 29/625`.

**`(SR-64.28)`–`(SR-64.29)` — the tail-sum form.**  `tailSum_annular_payment` and
`annulus_mass_floor` replace the two-witness restriction by the single scalar condition
`Σ_{r∈S} a_r ≥ 29/(256(1+h))`, so a fixed annulus of ratio `K` suffices once it carries
`(87/256)K²` copies.

**`(SR-64.31)`–`(SR-64.34)` — the critical line leaves the statement.**  With `X = 1 + k − u`,
`Y² = 4uk` and the strip bound `u < 1/4`, every copy obeys `τ_r ≤ 1/(k+3/4)` and `a_r ≥ 1/(k+3)`
(`responseSlope_le_inv_height`, `responseMass_ge_inv_height`), so `slope_gap_sq_gt_general`,
`tailSum_general_payment`, `annulus_general_mass_floor` and `annulus_general_payment` hold for
arbitrary Xi copies above the band floor `3(1+h)`.

**`(SR-64.35)` — the zero-counting provider, unconditional.**  `exists_annular_copies` gives, for
any prescribed count, a height beyond which every annulus of ratio `10` carries that many
divisor-multiplicity copies.  It rests on the complete Riemann–von Mangoldt chain built for this
card: the rectangle argument principle for `ξ` from the residue theorem
(`rectangleIntegral_logDeriv_xi`), the Gamma phase from the vertical digamma asymptotic
(`tendsto_gammaVerticalPhase_ratio`, no Stirling expansion), Backlund's disc count from Jensen
(`exists_zetaRealTrace_count_bound`) with the sign-change-to-argument step
(`abs_im_sub_le_of_finite_re_zeros`) and `card_le_divisor_sum`, the symmetry fold
(`two_pi_mul_regionOrderSum_eq`), the two-sided bound `(1/2π)T log T ≤ mass ≤ (2/π)T log T`
(`exists_xiSymmetricMass_two_sided`), density of admissible heights
(`exists_admissible_height`), and the identification of a mass difference with a band copy count
(`xiSymmetricMass_diff_eq_card`).

**The conclusion.**

```text
exists_annular_payment_of_large_height :
  ∃ h₀, ∀ q : XiZeroCopy, h₀ ≤ Im(q)²,
    ∃ S : Finset XiZeroCopy,
      A · χ_q < a_q · Σ_{r ∈ S} a_r (τ_q − τ_r)².
```

Every declaration audits to `[propext, Classical.choice, Quot.sound]`.  No `sorry`, `axiom`,
numerical computation, or RH premise occurs, and no hypothesis wrapper stands in for a literature
theorem: Selberg, Hardy–Littlewood, Pratt–Robles–Zaharescu–Zeindler and Hardy's theorem all left
the critical path.

## Open boundary

Formalization certifies the payment and its provider, not the forward research.  The finite head of
`(SR-64.1)` is still a head: eliminating its transverse charge, the safe-shift minor positivity, the
source-selected two-angle Suzuki limit, and RH itself remain open.
