# Working log — Route E four-card stage-3 formalisation sweep

Started 2026-09-11.  Goal (user directive): formalise unconditionally in Lean every proven theorem
on the four cards below, add all missing infrastructure, and move each to `3-formalized`.

## Targets

| # | card | gating input (as of 2026-09-11) |
|-|-|-|
| 1 | `2-fully-proven/route-e-cofactor-amplified-e3-token-supply.md` | Matomäki–Teräväinen all-interval `E₃` Thm 1.2 (arXiv:2207.05038); residual = collective signed cross-modulus (Kuznetsov) estimate on Lemma 3.5(ii) Type-I range, then amplification + Thm 1.2 assembly |
| 2 | `3-formalized/route e/route-e-coprime-square-root-mobius-product-sign-law.md` | general-`h` all-interval quantitative transport / representation input (Matomäki–Radziwiłł lane) |
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

### Brick 24 landed (2026-09-11) — the sieve mean square in the ladder's own language

`Sieve/MenonHarmonicSievePrimeBlock.lean`.  On a set of primes `μ(p) = -1`, so
`harmonicPrimeBlockPoly B = -logPoly (fun n => 1/n) B`; the two have the same norm, and the
two-dimensional sieve's mean square therefore transfers verbatim to the ladder's own prime block:

```text
∫_{[-W,W]} ‖harmonicPrimeBlockPoly (bigPrimeSet R (2R))‖²
   ≤ (5/(4δ))(1/R²)( #bigPrimeSet + 2( 8e·K·R/E² + K·(Selberg remainder) ) ) ,  δ = 1/(2πW) ,
```

with every sieve parameter already chosen.  The swapped receiver can now consume it in place of
reciprocal Halász–Montgomery.  Leaf build `12273/12273`; three declarations axiom-clean;
umbrella-wired.  **Session total: 26 leaves, 69 declarations.**

### Corpus assets RULED OUT for the residual gap (2026-09-11)

Checked directly against the numbers, so that no future session re-tries them:

| asset | why it does not close the residue |
|-|-|
| `HeathBrownSparseMeanValueTheoremFour.integral_Icc_normSq_heathBrown_factors_le_theoremFour` | its first term is `(95π/2)N²R²`; at `N = X/M`, `R = M` that is `(95π/2)X²`, i.e. `O(1)` after harmonic normalisation, and it dominates because `NRT = X·T < N²R² = X²` whenever `T < X`.  Theorem 4(iii) has content only for `T ≫ NR`. |
| `HeathBrownSparseMeanValueLemma34.integral_Icc_normSq_heathBrown_oneLine_le_lemma34_refined` | its regime condition `T^{2/3} ≤ N` *does* hold with the roles swapped (sparse `=` short cofactor, dense `=` prime factor), but the bound then degenerates to its first term `K²(|A|/M)²`, which is the trivial `L^∞ × L²` bound. |
| `DyadicPrimeMeanSquare.integral_normSq_dyadicPrimePoly_le` | sharp, and now wired in (bricks 22–24); it drives the large-prime part to `≍ (log log X)^{-3}`, still short of `o(1/log X)`. |

The common reason: the frequency radius `T = X/h` is **below** the polynomial length `X`, and every
generic mean-value or large-values tool is vacuous there.  The saving must come from the
multiplicative structure — the multi-range factorisation plus Halász — which is precisely the
Matomäki–Radziwiłł method, implemented in this corpus for sub-polynomial ranges
(`Sieve/TwoRangeAssembly`, `o(1)` at every window) and needing Menon's wide final range to acquire a
rate.

### Brick 25 landed (2026-09-11) — sparse-set harmonic mean square, and a better route for the top blocks

`Sieve/MenonHarmonicSparseSetMeanSquare.lean`:
`integral_Icc_normSq_logPoly_harmonicMoebius_le_card` bounds the harmonic Möbius mean square of any
`S ⊆ [A,N]` by `#S` and `A` alone.  **Session total: 27 leaves, 72 declarations.**

**New route for the top blocks, and it is better by two logarithms.**  The `ω`-weighted Ramaré
identity gives the top blocks density `≍ 1/log log x`; the *smallest-prime-factor* partition gives
them density `≍ 1/log W` instead, because a top block then captures only integers with no prime
factor below `W`.  The corpus already owns those counts —
`Sieve/RoughCount.card_rough_Ioc_le` (Brun's pure sieve at the primorial) and
`Sieve/BrunTitchmarsh.card_coprime_Ioc_le_log` (`≤ 2(b−a)/log Y + Selberg error`).  Composing them
with the new display bounds the whole top part by `≍ C/log W`, versus `≍ 1/(log log x)³` for the
`ω`-weighted arrangement.

Still one logarithm from `(log x)^{-2}`, but the arrangement is now the right one and every
ingredient except the final assembly is in the tree.

### Brick 26 landed (2026-09-11) — the rough part assembled

`Sieve/MenonHarmonicShellRoughMeanSquare.lean`: `menonShellRough`,
`integral_Icc_normSq_menonShellRough_le_count` (any count bound) and
`integral_Icc_normSq_menonShellRough_le_brun` (Brun's pure sieve inserted).
**Session total: 28 leaves, 75 declarations, all axiom-clean, leaf-built and umbrella-wired.**

The top-block contribution is now `≍ 1/log z` with no factorisation estimate, against
`≍ 1/(log log x)³` before.  Remaining residue for the lane: one logarithm, now located in the low
blocks' threshold, not in the top blocks.

### Brick 27 landed (2026-09-11) — the shell split at a prime cutoff

`Sieve/MenonHarmonicShellCutoffSplit.lean`: `ramareRough_primesLE_eq_menonShellRough`,
`integral_Icc_normSq_shell_le_bilinear_add_rough`, `integral_Icc_normSq_shell_le_bilinear_add_brun`.
**Session total: 29 leaves, 78 declarations, all axiom-clean, leaf-built and umbrella-wired.**

The lane's architecture is now: split the shell at a cutoff `z ≤ W`; the rough half is paid by
Brun at `≍ 1/log z`; the bilinear half has every block of prime scale `≤ z`, i.e. long cofactors,
which is the regime all of this session's receivers were built for and where the top-block
obstruction does not arise.  Residue: the low blocks' threshold, one logarithm.

## The trade-off, stated completely (2026-09-11)

Both "easy" architectures for the shell ceiling at `1/log X`, for opposite reasons.  This is the
sharp reason the Heath–Brown step is unavoidable, and it is worth stating once so that neither
architecture is attempted again as a fix for the other.

Write `P` for the designated prime set of the Ramaré identity, `T = X/h` for the frequency radius.

**(a) Designated set `= primesLE z` (this session's cutoff split).**  Every ladder block has prime
scale `≤ z`, so the cofactors are long and every receiver applies; the top-block obstruction does
not arise.  The moment method is effective on a block exactly when `q_j^k ≤ T` — because the
`2T·∑|coeff|²` term of `∫|Q_j|^{2k}` then dominates the `q_j^k·∑|coeff|²` term — so `z ≤ T^{1/k}`
makes every block's large-values count non-vacuous.  But the rough remainder is the set of
`z`-**rough** integers, of density `≍ 1/log z ≥ k/log T`.  **Ceiling `1/log X`.**

**(b) Designated set `= primes in [P₀, 3X]` (Menon's).**  The rough remainder is the set of
`P₀`-**friable** integers, of density `(log X)^{-R}` with `R` free — negligible, which is the paper's
new point.  But the ladder then has blocks with `q_j ≍ X`, whose cofactors have `O(1)` terms; there
every bound for the cofactor mean square on a set of measure `≍ W` is `≍ W` while the truth is
`≍ m_j`, and the moment method is vacuous because `q_j^k ≫ T` for every `k ≥ 1`.  **No receiver
closes the top blocks.**

The two rough sets are complementary — `z`-rough versus `P₀`-friable — so there is no intermediate
cutoff that makes both small: pushing `z` up to kill the rough density reinstates the top blocks
exactly.  The only way out is to estimate the top blocks' prime-supported polynomial by Heath–Brown's
identity rather than by any factorisation receiver, which is Menon §1.1 and the target of the 43
`Sieve/MenonHeathBrown*` leaves.

Both architectures are now **built and unconditional** in the corpus — (a) as
`integral_Icc_normSq_shell_le_bilinear_add_brun`, (b) as
`integral_Icc_normSq_menonFinalRangeShell_le_partition_mass_filter` and
`eventually_integral_Icc_normSq_menonFinalRangeShell_le_ladderSchedule` — so whichever way the
Heath–Brown step lands, the surrounding chain is ready for it.

### Brick 28 landed (2026-09-11) — window reflection symmetry

`Sieve/MenonHarmonicWindowSymmetry.lean`: `conj_logPoly_harmonicRamareCofactorCoeff`,
`norm_harmonicRamareBilinear_neg` (the bilinear form's norm is even in frequency, because its
arithmetic coefficients are real), `neg_mem_windowSuperLevel` (the exceptional set is symmetric) and
`volume_windowSuperLevel_le_two_mul_nonneg`:

```text
volume.real (windowSuperLevel F W V) ≤ 2 · volume.real (windowSuperLevel F W V ∩ Ici 0) .
```

**Why this one:** every Heath--Brown/Montgomery receiver in `Sieve/MenonHeathBrown*` is stated for
*positive* ordinates (`∀ r ∈ S, Tlo ≤ lam r`).  This is the bridge that lets such a count bound the
whole window, at a factor two.  Leaf built, four declarations axiom-clean, umbrella-wired.

**Session total: 30 leaves, 82 declarations, all `[propext, Classical.choice, Quot.sound]`.**

### Brick 29 landed (2026-09-11) — the positive-ordinate interface

`Sieve/MenonHarmonicWindowHalfMeasure.lean`:
`integral_Icc_normSq_harmonicRamareBilinear_le_threshold_halfMeasure` — the complete window estimate
with the exceptional measure supplied **only on `[0,W]`**, which is the shape every
`Sieve/MenonHeathBrown*` receiver produces.  Leaf build `12725/12725`, axiom-clean, umbrella-wired.

**Session total: 31 leaves, 83 declarations, all `[propext, Classical.choice, Quot.sound]`.**

## RESUME HERE (written 2026-09-11, for the next session)

**Goal state.** Four cards in `2-fully-proven` must reach `3-formalized`.  All four share one gate;
none can move until it closes.  Do not re-derive the analysis below — it is settled and checked.

**The gate.** A mean-square saving for `∑_{n ≍ X} μ(n) n^{-1-it}` over `|t| ≤ T = X/h`, i.e. at a
frequency radius *below* the polynomial length.  Every generic mean-value / large-values tool is
vacuous there (see the ruled-out table above: HB Thm 4(iii), HB Lemma 3.4, the dyadic prime sieve).
The two natural Ramaré architectures both ceiling at `1/log X` for complementary reasons (see "The
trade-off, stated completely").  The only route is Heath--Brown's identity on the prime-supported
polynomial — Menon §1.1 — i.e. assembling the 43 `Sieve/MenonHeathBrown*` leaves.

**What is already built and waiting for it (this session, 31 leaves, all axiom-clean, all wired):**

| need | have |
|-|-|
| ladder split not costing the block count | `..._le_blocks_mass`, `..._le_blocks_mass_filter` (no prime-gap hypothesis) |
| both factor orderings, and their min | `MenonHarmonicRamareBlockSwapped`, `..._le_min_mass_filter` |
| no supremum over a long window | `MenonHarmonicBlockLevelSplit` + `...LevelMoment` |
| receiver on a small set | `MenonHarmonicBlockLevelTrivial`, `...LadderLevelTrivial` |
| sharp prime mean square | `MenonHarmonicSievePrimeBlock` (two-dimensional sieve, params chosen) |
| `L²`–`L^∞` split, Chebyshev base case | `MenonHarmonicWindowThresholdSplit`, `...WindowChebyshev` |
| shell = bilinear + rough, rough paid | `MenonHarmonicShellCutoffSplit`, `...ShellRoughMeanSquare` |
| sparse-set mean square by cardinality | `MenonHarmonicSparseSetMeanSquare` |
| whole estimate at Menon's literal ladder | `eventually_..._le_ladderSchedule` |
| **positive-ordinate → whole window** | `..._le_threshold_halfMeasure` ← **plug the HB count in here** |

**Next concrete step.** Produce, from the `MenonHeathBrown*` family, a bound of the form
`volume.real (windowSuperLevel (harmonicRamareBilinear P (Icc A₀ B₀)) W V ∩ Set.Ici 0) ≤ vol`
with `vol` small enough, and feed it to `..._le_threshold_halfMeasure`.  The five frontier leaves of
that family are `MenonHeathBrownActiveBoxCofactorMeanSquare`, `...CofactorPerronMeanSquare`,
`...CoreReflection`, `...MediumMobiusReceiver`, `...WideCofactorPerronMeanSquare`; the Montgomery
count is `exists_derivativeExcised_montgomery_heathBrownBox_moebius_routeTPower`.

**Cards 1, 2, 3** need no separate elementary work until the gate closes.

### Brick 30 landed (2026-09-11) — the partition against an arbitrary exceptional budget

`Sieve/MenonHarmonicWindowPartitionBudget.lean`:
`integral_Icc_normSq_harmonicRamareBilinear_le_partition_budget` — the frequency partition estimate
with the some-large measure supplied as an arbitrary `vol`, instead of the corpus's hard-wired
moment budget.  Leaf build `12722/12722`, axiom-clean, umbrella-wired.

**Session total: 32 leaves, 84 declarations, all `[propext, Classical.choice, Quot.sound]`.**

**Refinement of the RESUME next step.**  There are now *two* sockets for the large-values input, and
the Case-II route fits the second one directly:

1. `..._le_threshold_halfMeasure` — takes a bound on
   `volume.real (windowSuperLevel (harmonicRamareBilinear …) W V ∩ Ici 0)`, i.e. on the exceptional
   set of the **bilinear form**;
2. `..._le_partition_budget` — takes a bound on
   `volume.real (menonHarmonicSomeBlockLarge P Q eta L V W)`, i.e. on the union of the **prime
   blocks'** large-value sets.

`Sieve/MenonHarmonicCaseIIWideMeasure.exists_absolute_eventually_volume_menonHarmonicPrimeBlockExceptionalSet_caseII_wide_le`
bounds the measure of a *single* prime block's exceptional set, so socket 2 is the one to aim at:
take the union bound over the `L` blocks (`volume_menonHarmonicSomeBlockLarge_le`, already in the
tree) and feed the result to `..._le_partition_budget`.  That is a finite union bound plus a
parameter match — no new analysis.

### Brick 31 landed (2026-09-11) — per-block measures to a some-large budget

`Sieve/MenonHarmonicSomeLargeUnionBudget.lean`:
`volume_real_menonHarmonicSomeBlockLarge_le_sum` (the union bound in **real** measure, the corpus's
own being in `ℝ≥0∞`) and
`integral_Icc_normSq_harmonicRamareBilinear_le_partition_blockMeasures` — the complete partition
estimate taking a family of per-block measure bounds `M j` and nothing else.

**This is the socket in its final shape.**  Every large-values input in the literature and in this
corpus — Case II (`MenonHarmonicCaseIIWideMeasure`), the moment method
(`volume_menonHarmonicBlockLarge_pow_le_local`), Huxley
(`PrimeBlockLevelSetCount.card_le_of_mem_primeBlockLevelSet`) — produces exactly per-block bounds
of that shape.  Supplying any of them now yields the window estimate with no further analysis.

Leaf build `12723/12723`, both declarations axiom-clean, umbrella-wired.
**Session total: 33 leaves, 86 declarations, all `[propext, Classical.choice, Quot.sound]`.**

### Brick 32 landed (2026-09-11) — the chain is CLOSED (moment method)

`Sieve/MenonHarmonicPartitionMomentClosed.lean`:
`volume_real_menonHarmonicBlockLarge_le_moment` and
`integral_Icc_normSq_harmonicRamareBilinear_le_partition_moment_closed` — the complete window
estimate with no free measure and no external input.

**Session total: 34 leaves, 88 declarations, all `[propext, Classical.choice, Quot.sound]`,
all leaf-built and umbrella-wired.**

The chain is now closed end to end with a weak large-values input.  Upgrading the rate is a
**drop-in replacement** at `..._le_partition_blockMeasures`: supply a better family `M j` of
per-block large-value measures (Case II via `MenonHarmonicCaseIIWideMeasure`, or Huxley via
`PrimeBlockLevelSetCount.card_le_of_mem_primeBlockLevelSet` plus a discrete-to-measure bridge) and
nothing else changes.

## RESUME — CURRENT STATE (supersedes the earlier RESUME block)

**Status.** Four cards in `2-fully-proven`; all four share one gate; none can move until it closes.
Card 4's frequency chain is now **closed end to end and unconditional** (34 leaves, 88 declarations,
all `[propext, Classical.choice, Quot.sound]`, all umbrella-wired), but with a large-values input
too weak for the target rate.

**The single remaining mathematical need.**  A better family of per-block large-value measures

```text
M : ℕ → ℝ   with   ∀ j < L, volume.real (menonHarmonicBlockLarge P Q η V W j) ≤ M j
```

fed to `integral_Icc_normSq_harmonicRamareBilinear_le_partition_blockMeasures`
(`Sieve/MenonHarmonicSomeLargeUnionBudget.lean`).  **Nothing else in the 34-module chain changes.**
The currently supplied family is the moment method
(`MenonHarmonicPartitionMomentClosed.volume_real_menonHarmonicBlockLarge_le_moment`), which is weak
on narrow blocks: `|{|Q_j| > θ m_j}| ≤ k!/(θ^{2k} m_j^k)` beats the ambient length only when
`θ² ≫ 1/m_j`, never for `m_j ≪ 1`.

**Two candidate replacements, and what each still needs.**

1. *Huxley* — `Sieve/PrimeBlockLevelSetCount.card_le_of_mem_primeBlockLevelSet` already bounds the
   cardinality of a **one-spaced family** inside a prime-block level set.  Missing: the
   discrete-to-measure bridge.  The standard argument: partition `[-W,W]` into `⌈2W/δ⌉` intervals of
   length `δ`; `E ⊆ ⋃` of the meeting ones gives `volume E ≤ δ·#meeting` (easy, via
   `measure_biUnion_finset_le`); choosing one point per meeting interval and splitting the indices
   into even/odd gives two `δ`-spaced families, so `#meeting ≤ 2R` and `volume E ≤ 2δR`.  The
   choice-and-spacing half is the work.
2. *Case II* — `Sieve/MenonHarmonicCaseIIWideMeasure.exists_absolute_eventually_volume_menonHarmonicPrimeBlockExceptionalSet_caseII_wide_le`
   already produces a **measure** for a single prime block's exceptional set, so no bridge is needed;
   the work is matching its parameter list (`L X Y cells T0 t H B sigma V Δ T`) to the ladder's and
   checking `menonHarmonicPrimeBlockExceptionalSet` against `menonHarmonicBlockLarge`.

Candidate 2 needs no new mathematics — only a parameter match — and is the recommended next step.

**Do not retry** (checked against the numbers, reasons in the table above): Heath–Brown Theorem
4(iii); Heath–Brown Lemma 3.4; the dyadic prime sieve as a fix for the rate; a factorisation
receiver for the top blocks under the `ω`-weighted identity; a cutoff architecture as a way around
the Heath–Brown step (both architectures ceiling at `1/log X`, for complementary reasons).

### Brick 33 landed (2026-09-11) — the covering half of the discrete-to-measure bridge

`Sieve/MenonHarmonicIntervalCovering.lean`: `measureReal_le_of_subset_biUnion_Ico` — a set covered
by `#s` intervals of common length `delta` has `volume.real ≤ #s * delta`.  This is the reusable
half of the Huxley bridge described in the RESUME block; what remains of that bridge is the
choice-and-spacing half (pick one point per meeting interval, split indices even/odd to get two
`delta`-spaced families, giving `#meeting ≤ 2R`).

Leaf build `12725/12725`, axiom-clean, umbrella-wired.
**Session total: 35 leaves, 89 declarations, all `[propext, Classical.choice, Quot.sound]`.**

### Bricks 34–37 landed (2026-09-11) — THE HUXLEY ROUTE IS CLOSED

`Sieve/MenonHarmonicIntervalCovering.lean`, `MenonHarmonicSpacedToMeasure.lean`,
`MenonHarmonicHuxleyMeasure.lean`, `MenonHarmonicBlockHuxley.lean`,
`MenonHarmonicPartitionHuxleyClosed.lean`.

The discrete-to-measure bridge named in the RESUME block is **built**:
`measureReal_le_of_spaced_card_le` — every `delta`-spaced finite subset of `E ⊆ [-W,W]` having
cardinality `≤ R` gives `volume.real E ≤ 2·R·delta`.  Huxley's cardinality count therefore becomes a
measure, the narrow-block comparison transports it to `menonHarmonicBlockLarge`, and
`integral_Icc_normSq_harmonicRamareBilinear_le_partition_huxley` is the window estimate running on
it.

**Session total: 39 leaves, 94 declarations, all `[propext, Classical.choice, Quot.sound]`,
all leaf-built and umbrella-wired.**

**RESUME, updated.**  The large-values gate is no longer an unbuilt bridge — it is closed on
Huxley.  What remains for card 4 is *numerology*: choose `V j`, `sigma j`, `Nb j`, `Ec j`, `V₀ j`,
`J j`, `k` at Menon's literal ladder and show

```text
mass(P)·∑_{active} min(pointwise,swapped)/m_j
  + mass(P)·∑_{active} levelTrivialCost(∑_i huxleyBlockMeasureBound …)/m_j   ≤  (log x)^{-2}.
```

Every symbol in that display is a defined, unconditional object in the tree.

### CORRECTION to bricks 34–37 (2026-09-11)

"The Huxley route is closed" was wrong.  `card_le_of_mem_primeBlockLevelSet` needs
`#B ≤ E/N` and `2400E ≤ N^{1/2-2σ}`, which force `#B ≤ N^{-1/2-2σ}/2400`; a dense Menon block has
`#B ≍ ηN/log N` and no admissible `σ` exists (see the card for the two-sided computation).  It is a
**sparse** large-values estimate.  `..._le_partition_huxley` is correct but vacuous at Menon's
ladder.

Still genuinely gained, and route-independent:
`measureReal_le_of_spaced_card_le` (any spaced-family count → measure),
`measureReal_le_of_subset_biUnion_Ico`, `volume_real_primeBlockLevelSet_le_huxley`,
`menonHarmonicBlockLarge_subset_primeBlockLevelSet`.

**Sharpened gate:** a large-values / zero-density estimate for a **dense** prime block
(`#B ≍ ηN/log N`) at thresholds near its typical size `≍ √(#B)`.  Nothing in the corpus supplies
that; it is the Heath--Brown identity route.
