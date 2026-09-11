# Working log — Route E four-card stage-3 formalisation sweep

Started 2026-09-11.  Goal (user directive): formalise unconditionally in Lean every proven theorem
on the four cards below, add all missing infrastructure, and move each to `3-formalized`.

## Targets

| # | card | gating input (as of 2026-09-11) |
|-|-|-|
| 1 | `2-fully-proven/route-e-cofactor-amplified-e3-token-supply.md` | Matomäki–Teräväinen all-interval `E₃` Thm 1.2 (arXiv:2207.05038); residual = collective signed cross-modulus (Kuznetsov) estimate on Lemma 3.5(ii) Type-I range, then amplification + Thm 1.2 assembly |
| 2 | `2-fully-proven/route-e-coprime-square-root-mobius-product-sign-law.md` | general-`h` all-interval quantitative transport / representation input (Matomäki–Radziwiłł lane) |
| 3 | `2-fully-proven/route-e-forbidden-support-e3-stability.md` | same as #1 |
| 4 | `2-fully-proven/route-e-growing-reciprocal-marker-low-breadth-transport.md` | Menon quantitative mean square → integer-start `DyadicTranslates.dyadicMeanSquare`; residual = initial-exceptional/Case-II volume specialisation, final-block + frequency-band summation, terminal harmonic→integer-start receiver |

Shared programme cards: `1-in-progress/matomaki-teravainen-e3-lean-programme.md`,
`1-in-progress/matomaki-radziwill-lean-programme.md`.

## Session state

- 2026-09-11: orientation.  Cards read; gaps as above.  Starting with card 4 (closest to closure).

## Reconnaissance, 2026-09-11 (card 4 / Menon lane)

### What the receiver chain needs

`Sieve/MenonMobiusLargeValues.eventually_dyadicMeanSquare_moebius_le_menonCentral` is already
unconditional, but its frequency radius is `menonHarmonicCentralRadius x = (log x)^2000`.  In the
Gallagher receiver `dyadicMeanSquare_harmonic_le_menonFinalRange_boundedDyadicHead_two` the head is
weighted by `log(1+l/A)^2 ≍ (l/A)^2` and the tail by `1/w^2`, so the complementary term
`4·menonHarmonicAffineConst A/(3π²W²)` is only negligible once `W ≳ (A/l)·(log A)^{20}`.  With the
card's window `l ≍ √X·h` the required radius is `≍ √X/h`, i.e. exactly `twoRangeTop β X`
(`Sieve/TwoRangeSchedule`: `twoRangeTop β x = (⌊√x + cardLength β x⌋/cardLength β x)·log log x`).

So the single receiver-level target for card 4 is

```text
∀ᶠ x, ∫_{|w| ≤ twoRangeTop (2/3) x} ‖logPoly harmonicMoebiusC (menonFinalRangeShell x) w‖² ≤ (log x)^{-A}
```

for some `A > 3` (the receiver only needs `I·K ≪ 1/log A` with `K ≍ (log A)^2`; the `80` in the
current statements is slack, not a requirement).

### Structural finding: the ladder needs BOTH orderings

`Sieve/MenonHarmonicRamareLadderOnHM.setIntegral_normSq_harmonicRamareBlock_geom_le_HM` pays the
prime block **pointwise** and the cofactor by reciprocal Halász–Montgomery.  On a block at prime
scale `q_j` the cofactor factor is `Ω²·card ≍ 2q_j/A₀`, so the ambient-mean-square part of the
cofactor costs `≍ W·q_j/A₀`.  For the blocks with `q_j ≍ B₀` that is `≍ W`, while the truth for
such a block is `≍ (2W + B₀)·∑_{p ∈ B_j} p^{-2} ≍ harmonicPrimeMass B_j`.  The pointwise ordering
is therefore off by a factor `≍ A₀` on the top blocks and cannot be used there.

The missing receiver is the **reverse ordering**: cofactor bounded by its own harmonic supremum
(`≤ ∑_{m ∈ D_j} 1/m`, `O(1)` for a geometric block) and the *prime* polynomial paid by reciprocal
Halász–Montgomery at the block's own endpoints (coefficient bound `1/⌊Q(1+η)^j⌋₊`).

Built today — see the log entries below.

### Brick 1 landed (2026-09-11) — swapped + hybrid harmonic Ramaré receivers

`Sieve/MenonHarmonicRamareBlockSwapped.lean`, `Sieve/MenonHarmonicRamareLadderSwapped.lean`,
`Sieve/MenonHarmonicRamareLadderSwappedVolume.lean`.  Fifteen declarations, axiom-clean, leaf-built
(`12254`, `12697`, `12703`), umbrella-wired.  Card 4 updated.

### Next objective

Plain Cauchy–Schwarz over `L ≍ (log x)^{11}` ladder blocks loses a factor `L`, and the true total
mass of the bilinear form over a prime range reaching the source scale is `O(1)`.  So **no**
per-block estimate over a ladder whose top is `≍ x` can reach `(log x)^{-A}`: the prime range must
have sub-polynomial top, and the integers with no prime factor in it must be counted by
`∏_{P₁<p≤P₂}(1-1/p) ≍ log P₁/log P₂`.  That is precisely the corpus's two-range architecture
(`Sieve/TwoRangeSchedule`, `Sieve/TwoRangeAssembly`), which already proves
`averagedMeanSquare_moebius_cardLength_all` at every `0 < β < 1` — but only as
`Tendsto … (𝓝 0)`.

**Objective:** make `Sieve/TwoRangeAssembly` quantitative — replace the seven group limits by
explicit `(log x)^{-A}` majorants, giving card 4 its `(15)`–`(17)` rate at the radius
`twoRangeTop β x` that the receiver actually needs.

### Size audit of the final-range ladder (2026-09-11) — the block-Cauchy factor is the bottleneck

Normalisations (shell `[A,3A]`, harmonic coefficients `μ(n)/(n(ω_P(n)+1))`, frequency radius
`W ≍ √A/h`, ladder `η = exp(1/H)−1`, `H = (log A)^{10}`, `L = menonFinalRangeLadderSteps ≍ (log A)^{11}`):

| quantity | size |
|-|-|
| target `I = ∫_{|w|≤W}‖logPoly harmonicMoebiusC (shell)‖²` | `≤ (log A)^{-3}/87` suffices for the receiver |
| trivial MVT value of `I` | `≍ 2` (the `N·∑|a_n|²` term) |
| true value of `I` | `≍ 4W/(3A) ≍ A^{-1/2}` |
| one block's true mass `∫_{|w|≤W}‖z_j‖²` | `≍ 4W·m_j/(A(log log A)²)`, `m_j = harmonicPrimeMass B_j` |
| MVT upper bound for one block | `≍ 6 m_j/(log log A)²` |
| `∑_j m_j` over `(P(A), 3A]` | `≍ log log log A` |

The exact inequality currently used to split the ladder,
`setIntegral_normSq_harmonicRamareBilinear_le_blocks`, costs a factor `L = (#blocks)`.  Since the
per-block **upper** bounds sum to `Θ((log log A)^{-2})` at best, that factor alone puts the
assembled bound at `≳ (log A)^{11}` — eleven logarithms above the trivial bound and fourteen above
the target.  No choice of per-block receiver (pointwise, swapped, or their min) repairs it: the
loss is in the split, not in the block estimates.

**Consequences.**

1. The split must be Cauchy–Schwarz **weighted by the blocks' own harmonic masses**,
   `|∑_j z_j|² ≤ (∑_j m_j)(∑_j ‖z_j‖²/m_j)`, replacing `L ≍ (log A)^{11}` by
   `∑_j m_j ≍ log log log A`.  With it the low blocks (`q_j ≤ W`) close comfortably:
   `(∑_j m_j)·∑_j V_j²·6/(m_j (log log A)²) ≍ (log A)^{-18}` at the Route-T threshold
   `V_j = C(log q_j)^{-20}`.
2. The top blocks (`q_j > W`) still do not close, for a reason independent of the split: for a
   polynomial of length `N ≫ W` the mean-value theorem's `N·∑|a_n|²` term is lossy by `N/W`, so
   every available upper bound for `∫_{|w|≤W}‖P_j‖²` is `≍ m_j` where the truth is `≍ 2W m_j/q_j`.
   A prime range whose top reaches the source scale therefore cannot be run through this receiver
   at all — Ramaré must be applied to a range with **sub-polynomial top**, where every cofactor has
   length `≥ A^{1-o(1)} ≫ W`, and the integers missing that range must be paid by the rough/friable
   count and their own Route-T saving.
3. Separately confirmed: quantifying `Sieve/TwoRangeAssembly` cannot give the rate.  Its rough
   group carries the explicit majorant `(1+1/δ)(10W/(𝔄M) + 7/𝔄)` with `𝔄 = ∑_{p∈P}1/p ≤ log log x
   + O(1)` and `δ = (log log x)^{-1/2}`, i.e. `Θ((log log x)^{-1/2})`.  This is the Ramaré `1/W`
   diagonal the card already identified; it is structural, and it is why card 4's `o(1/log X)` needs
   Menon's Halász route rather than the two-range Ramaré route.

**Next brick:** the harmonic-weighted block split (consequence 1).

### Bricks 2–3 landed (2026-09-11) — weighted and mass-weighted ladder splits

`Sieve/MenonHarmonicRamareLadderWeighted.lean` (`..._le_blocks_weighted`, `..._le_min_weighted`)
and `Sieve/MenonHarmonicRamareLadderMass.lean` (`harmonicPrimeMass_biUnion`,
`..._le_blocks_mass`, `..._le_min_mass`).  Five declarations, axiom-clean, leaf-built
(`12698`, `12699`), umbrella-wired.  Card 4 updated.

Open, now isolated: the **top blocks** of the final-range ladder (`q_j ≫ W`).  Next step is to read
Menon 2026 (arXiv:2607.15574) §3 to see how the large-prime range is actually organised, rather
than continue guessing; the corpus's `MenonHeathBrown*` leaves suggest a Heath--Brown identity
(Case II) treatment rather than a Ramaré block.

### Menon 2026 architecture, from the source (2026-09-11)

arXiv:2607.15574, S. Menon, *Improved bounds for multiplicative functions in almost all short
intervals*.  Theorem 1.1: for fixed `B>0`, `X ≥ h ≥ 10`, `q ≤ (log X)^B`, χ mod q,

```text
(1/X)∫_X^{2X} |(1/h)∑_{x≤n≤x+h} χ(n)λ(n)|² dx  ≪_B  (log log h)²/(log h)² + (log log X)⁴/(log X)².
```

Architecture (§1.1): `L²–L^∞` + a Ramaré-type decomposition along the final prime range
`P = exp((log X)(log log log X)/(R log log X))`, `Q = 3X` (2.7), then Heath–Brown's identity on the
prime-supported polynomial.  The one new point is the wide final range: integers with no prime
factor in `[P,Q]` have density `≪_R (log X)^{-R+o(1)}` (Lemma 2.15), `R > 2` free.

Lemma 2.19 (block split) and Lemma 2.20 (Perron decoupling, cost `(log D)(log Q)` instead of
`H log(Q/P)`, error `1/D`, `D < P`) — see the card entry for the displayed forms.

**My size audit's scope was wrong**: the ladder is applied on the exceptional set `𝒯`, not the
ambient window, so the block count is affordable.  Corrected on the card.  Net: the mass-weighted
split (brick 3) is a ten-logarithm relaxation of the exceptional-measure requirement, and makes
Menon's Lemma 2.20 unnecessary for this corpus.

**Next brick:** the `L²–L^∞` split itself — `∫_{[-T,T]}‖F‖² ≤ V²·2T + ∫_{𝒯}‖F‖²` with
`𝒯 = {t : ‖F(1+it)‖ > V}` — in the corpus's harmonic normalisation, and then the ladder-on-`𝒯`
receiver assembled from bricks 1–3.

### Bricks 4–8 landed (2026-09-11) — the level-split/moment receiver

`Sieve/MenonHarmonicBlockLevelSplit.lean`, `MenonHarmonicRamareLadderLevelSplit.lean`,
`MenonHarmonicBlockLevelSplitHM.lean`, `MenonHarmonicBlockLevelMoment.lean`,
`MenonHarmonicRamareLadderLevelMoment.lean`.  Capstone
`setIntegral_normSq_harmonicRamareBilinear_le_levelMoment_mass`.  All axiom-clean, leaf-built,
umbrella-wired.  Card 4 updated.

Session total: 8 leaves, 29 declarations, all `[propext, Classical.choice, Quot.sound]`.

**Next:** the schedule — choose `V₀ j`, `J j`, `k`, the ambient threshold `V` and the radius
`twoRangeTop β x`, and show `harmonicPrimeMass P · ∑_j menonHarmonicLevelMomentBlockCost/m_j`
together with `V²·2T` is below `(log x)^{-A}`.  Everything feeding that sum is now explicit.

### Bricks 9–12 landed (2026-09-11) — the `L²`--`L^∞` window estimate

`Sieve/MenonHarmonicBlockLevelTrivial.lean`, `MenonHarmonicRamareLadderLevelTrivial.lean`,
`MenonHarmonicWindowThresholdSplit.lean`, `MenonHarmonicWindowLadderAssembly.lean`.  Capstone
`integral_Icc_normSq_harmonicRamareBilinear_le_threshold_levelTrivial`.

**Session total: 12 leaves, 41 declarations, every one `[propext, Classical.choice, Quot.sound]`,
every one leaf-built and umbrella-wired (no umbrella build).**

Why the trivial receiver and not HM on the exceptional set: `hmMassRecip N T volE` contains
`48π N log(2+2T)`, independent of `volE`; at the final-range blocks `N·Ω²·card ≍ 6`, so that term
is `≍ 452 log x` per block and survives however small the set is.  The trivial receiver
`|E|·(∑_{m∈D}1/m)²` is `≍ |E|` instead, and `∑_{m∈D_j}1/m ≍ log 3` on a geometric cofactor block.
Both are now available and a schedule can take either.

### Remaining obligations of the Menon lane, as of this session

1. the ambient threshold `V` with `V²·2W` below target;
2. the base levels `V₀ j`, level counts `J j` and moment order `k`;
3. a large-values bound for `volume.real (windowSuperLevel (harmonicRamareBilinear …) W V)`;
4. the rough/friable half (already `(log x)^{-8}` in `MenonHarmonicRoughMeanSquare`, and Menon's
   Lemma 2.15 allows `(log x)^{-R}` for any `R`);
5. insertion into the receiver at radius `twoRangeTop β x` and then into the marker chain.

### Bricks 13–14 landed (2026-09-11)

`Sieve/MenonHarmonicWindowChebyshev.lean` (`volume_windowSuperLevel_le`,
`..._le_threshold_chebyshev`) and `Sieve/MenonFinalRangeWindowEstimate.lean`
(`integral_Icc_normSq_menonFinalRangeShell_le_threshold_chebyshev`).

**Session total: 14 leaves, 44 declarations, all axiom-clean, all leaf-built, all umbrella-wired.**

New leaves, in dependency order:

```text
MenonHarmonicRamareBlockSwapped          MenonHarmonicRamareLadderSwapped
MenonHarmonicRamareLadderSwappedVolume   MenonHarmonicRamareLadderWeighted
MenonHarmonicRamareLadderMass            MenonHarmonicBlockLevelSplit
MenonHarmonicRamareLadderLevelSplit      MenonHarmonicBlockLevelSplitHM
MenonHarmonicBlockLevelMoment            MenonHarmonicRamareLadderLevelMoment
MenonHarmonicBlockLevelTrivial           MenonHarmonicRamareLadderLevelTrivial
MenonHarmonicWindowThresholdSplit        MenonHarmonicWindowLadderAssembly
MenonHarmonicWindowChebyshev             MenonFinalRangeWindowEstimate
```

Remaining for the Menon lane: choose `V`, `V₀ j`, `J j`, `k`; supply the large-values bound for the
exceptional measure (Chebyshev is in place as the base case); then insert at radius
`twoRangeTop β x` into `dyadicMeanSquare_moebius_le_menonFinalRange_boundedDyadicHead_two` and on
into the marker/grid/count chain of card 4.

### Brick 15 landed (2026-09-11) — rough half discharged

`Sieve/MenonFinalRangeWindowRough.lean`.  **Session total: 15 leaves, 46 declarations.**

### Bricks 16–17 landed (2026-09-11) — the frequency partition under the mass split

`Sieve/MenonHarmonicWindowPartitionMass.lean`, `Sieve/MenonFinalRangeWindowPartition.lean`.
Capstone `integral_Icc_normSq_menonFinalRangeShell_le_partition_mass`.
**Session total: 17 leaves, 50 declarations.**

Next: instantiate at Menon's literal schedule (`Sieve/MenonHarmonicFinalRangeSchedule`,
`MenonHarmonicFinalProductSchedule` already prove the endpoint/positivity side conditions), then
choose `V j`, `V₀ j`, `J j`, `k`.

### Bricks 18–20 landed (2026-09-11) — prime-gap hypothesis removed

`Sieve/MenonHarmonicRamareLadderMassFilter.lean`,
`Sieve/MenonHarmonicWindowPartitionMassFilter.lean`,
`Sieve/MenonFinalRangeWindowPartitionFilter.lean`.  Capstone
`integral_Icc_normSq_menonFinalRangeShell_le_partition_mass_filter`.
**Session total: 20 leaves, 58 declarations, all axiom-clean, all leaf-built, all umbrella-wired.**

### Brick 21 landed (2026-09-11) — the estimate at Menon's literal ladder

`Sieve/MenonFinalRangeWindowSchedule.lean`:
`eventually_integral_Icc_normSq_menonFinalRangeShell_le_ladderSchedule` plus `exists_levelCount`.
**Session total: 21 leaves, 60 declarations.**

All structural side conditions of the window estimate are now discharged at the paper's own
schedule.  The remaining work in this lane is numerical: choose `V j`, `V₀ j`, `k`, and bound the
two mass-split sums and the rough energy by `(log x)^{-A}` at `W = twoRangeTop β x`.

### The lane's open core, located precisely (2026-09-11)

Top blocks (`q_j ≳ W`): cofactor has `O(1)` terms, so any mean-square bound for it on a set of
measure `≍ W` is `≍ W`, while the truth for the product is `≍ m_j`.  The all-small contribution is
then `≍ 6Wθ²·logloglog x`, needing `θ ≲ x^{-1/4}`; and at that threshold the moment method is
vacuous, since `|{|Q_j| > θ m_j}| ≤ k!/(θ^{2k}m_j^k)` beats the ambient length only when
`θ² ≫ 1/m_j`, i.e. never for `m_j ≪ 1` — which holds at every block width, including Menon's
ratio-`e` blocks.

So the top blocks must be handled by Heath--Brown's identity on the prime-supported polynomial
(Menon §1.1), not by a factorisation receiver.  `Sieve/MenonHeathBrown*` is the relevant family.
This is now the lane's only open core.

### Accurate session tally (2026-09-11)

**23 new leaf modules, 63 exported declarations audited, every one
`[propext, Classical.choice, Quot.sound]`.**  Verified mechanically: every one of the 23 files
exists, carries an `import` line in `GaloisForLFunctions/RHTower.lean`, and has a built `.olean`.
No umbrella build was run.  No Lean process of this session was left running.

```text
MenonHarmonicRamareBlockSwapped            MenonHarmonicRamareLadderSwapped
MenonHarmonicRamareLadderSwappedVolume     MenonHarmonicRamareLadderWeighted
MenonHarmonicRamareLadderMass              MenonHarmonicBlockLevelSplit
MenonHarmonicRamareLadderLevelSplit        MenonHarmonicBlockLevelSplitHM
MenonHarmonicBlockLevelMoment              MenonHarmonicRamareLadderLevelMoment
MenonHarmonicBlockLevelTrivial             MenonHarmonicRamareLadderLevelTrivial
MenonHarmonicWindowThresholdSplit          MenonHarmonicWindowLadderAssembly
MenonHarmonicWindowChebyshev               MenonFinalRangeWindowEstimate
MenonFinalRangeWindowRough                 MenonHarmonicWindowPartitionMass
MenonFinalRangeWindowPartition             MenonHarmonicRamareLadderMassFilter
MenonHarmonicWindowPartitionMassFilter     MenonFinalRangeWindowPartitionFilter
MenonFinalRangeWindowSchedule
```

Capstone: `eventually_integral_Icc_normSq_menonFinalRangeShell_le_ladderSchedule`.

**Cards 1, 2, 3 received no formalisation work this session** — all three are gated on
Matomäki–Teräväinen Theorem 1.2 (cards 1, 3) and on Matomäki–Radziwiłł's bilinear all-interval
theorem at `h ≍ log log x` (card 2), and neither of those inputs has an open elementary brick at
present.  Card 4's lane is the one with an open elementary frontier, which is why all effort went
there.

## The four cards share ONE gate (2026-09-11)

Following the top-block obstruction to its root changes the picture: the four cards do not have
four independent gates.  They have one.

**Card 4's residue, traced.**  Integers of `[X,3X]` with a prime factor above `T = X/h` are
`n = pm` with `m < h`; they have density `≍ 1/log log X`, so they are not negligible.  Splitting
them dyadically in `m` and applying the corpus's own Heath--Brown Lemma 3.4
(`Sieve/HeathBrownSparseMeanValueLemma34.integral_Icc_normSq_heathBrown_oneLine_le_lemma34_refined`,
already closed and axiom-clean) with the **roles swapped** — sparse `=` the short cofactor
`m ≍ M`, dense `=` the prime factor in `(N,2N]`, `N ≍ X/M` — satisfies every hypothesis, including
the regime condition `T^{2/3} ≤ N` (because `M < h ≪ X^{1/3}`).  It yields `≍ C_η` per dyadic
block.  But the *truth* at mean-value-theorem level for this part is only

```text
∑_{M dyadic ≤ h} (2T + X/M)·∑_n |coeff|²  ≍  (1/log X)·∑_M 1/M  ≍  2/log X ,
```

still a full logarithm above the `(log x)^{-2}` target.  So no split, no receiver, and no
rearrangement closes it: **a genuine saving inside `∑_{p ≍ y} p^{-1-it}` at heights up to
`X^{1-o(1)}` is required**, i.e. a large-values / zero-density estimate for prime-supported
Dirichlet polynomials well beyond the Vinogradov--Korobov contour range
(`|t| ≤ exp((log X)^{3/5-ε})`, which is what Route T supplies).

**The same object gates the other three.**  Cards 1 and 3 wait on Matomäki--Teräväinen Theorem 1.2,
whose residual on its own programme card is the collective cross-modulus estimate on the
Lemma 3.5(ii) Type-I range — a large-values statement for the same prime polynomials.  Card 2 waits
on Matomäki--Radziwiłł at `h ≍ log log x`, whose hard half is the same.

So the one shared gate is: **large values / zero density for prime-supported Dirichlet polynomials
at heights up to a power of `X`.**  The corpus already owns the *sparse×dense* half of the
machinery (Heath--Brown Theorem 4(iii) in `Sieve/HeathBrownSparseMeanValueTheoremFour`, Lemma 3.4 in
`Sieve/HeathBrownSparseMeanValueLemma34`, both closed) and the *contour* half below the
Vinogradov--Korobov range (Route T).  What is missing is the prime large-values estimate joining
them, which is exactly what the 43 unassembled `Sieve/MenonHeathBrown*` leaves are building.

**Consequence for planning:** effort on any one of the four cards should go into that single
object, not into the four lanes separately.

### Quantitative ceiling of the existing tools on the large-prime part (2026-09-11)

The corpus already owns the sharp dyadic prime mean square,
`Sieve/DyadicPrimeMeanSquare.integral_normSq_dyadicPrimePoly_le` (two-dimensional sieve, closed and
axiom-clean):

```text
∫_{-W}^{W} |∑_{R<p≤2R} p^{-1+2πiw}|² dw
   ≤ (5/(4δR²))( π(2R)−π(R) + 2( 8e·K·R/E² + K·(Selberg remainder) ) ),
   2πδW ≤ 1,  K ≥ 6Rδ,  E = exp(mertensS h − mertensS P₁) ≍ log h/log P₁ .
```

At `δ = 1/(2πW)`, `K ≍ R/W` it gives `≍ 5πW/(2R log R) + 60e/E²`: a sharp diagonal plus an
off-diagonal of order `(log R)^{-2}` — genuinely one logarithm past the mean-value theorem.

Feeding it into the large-prime part (`n = pm`, `m < h`, split dyadically in `m`) with the swapped
receiver gives, after the Cauchy–Schwarz over the `≍ 1.44 log h` dyadic `m`-blocks,

```text
∑_{M dyadic ≤ h} ≍ 10.9 / (log log X)³ .
```

So the existing tools do drive the large-prime part to zero — but at rate `(log log X)^{-3}`, not
`(log X)^{-2}`.  The gap is exactly the `sup|S_M|` loss: replacing the short factor by its supremum
costs `M` per block, and recovering it needs genuine bilinear cancellation between the two
variables, not a sharper bound on either.

**This is the quantitative statement of the shared gate.**  Rate `o(1)` is reachable with what the
corpus has; rate `o(1/log X)` — which is what card 4's Markov step consumes and what
Matomäki–Teräväinen Thm 1.2 encodes for cards 1 and 3 — is not.

### Brick 22 landed (2026-09-11) — the sieve-swapped receiver

`Sieve/MenonHarmonicSieveSwappedReceiver.lean`: the generic swapped ordering
(`setIntegral_normSq_product_le_meanSquareSup`) and the composition of the corpus's
two-dimensional sieve mean square with the harmonic cofactor supremum
(`integral_Icc_normSq_dyadicPrimePoly_mul_harmonicCofactor_le`).  This is a strictly better
receiver for the top blocks than the Halasz--Montgomery one: no mean-value diagonal enters, and the
sieve's off-diagonal is `≍ (log R)^{-2}`.  Leaf build `12271/12271`; both declarations axiom-clean;
umbrella-wired.

### Brick 23 landed (2026-09-11) — the canonical sieve-swapped receiver

`Sieve/MenonHarmonicSieveSwappedCanonical.lean`: `sieveSwappedDelta/Budget/Dimension/Level` and the
receiver with all five sieve parameters chosen, only structural inequalities left.
**Session total: 25 leaves, 66 declarations, all axiom-clean, leaf-built and umbrella-wired.**
