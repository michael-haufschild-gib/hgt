# Chebyshev readout of the incidence ledger

- **ID:** chebyshev-ledger-readout
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** AIP README §3 mech. 42–43 ("What the floor is made of at large aperture"); APT README §1.2 receiver 1
- **Statement:** For every real `F ∈ C²_c`, the prime side and the pole plane of the critical form
  cancel to PNT accuracy, and their exact difference is a single linear functional of the two-pole
  Chebyshev defect `E(s) = e^s + s − 1 − ψ(e^s)` against the lag weight of `F`.

## Goal

AIP mechanism 43 states as a heuristic that "beyond lag `O(1)` the ledger's balance is the
prime–polar difference and nothing else": the prime measure has density `≍ e^{t/2}dt`, the polar
measure `2cosh(t/2)` the same, and the archimedean density is smaller by `e^t`. The goal is to turn
that paragraph into an identity, which (i) makes the rate-`1` obstruction a theorem rather than an
estimate, (ii) exhibits the incidence face and APT's receiver 1 (`D(T) ≤ B(1+T)e^{T/2}`) as one
object at every aperture, and (iii) converts test design into kernel design against `ψ(x) − x`.

## The theorem

Write `A = autoCorr F`, `A(t) = ∫ F(x)F(x+t) dx`, and for `x ∈ ℝ` the **lag weight**
`h_x(s) = 2 e^{−s/2} F(x+s)`, `h_x'(s) = 2 e^{−s/2}(F'(x+s) − ½F(x+s))`.

1. **Lag Abel summation.** For `C¹` `h` vanishing from `S` on, `Σ_n Λ(n) h(log n) = −∫_{s>0} ψ(e^s) h'(s) ds`.
   Finite Fubini: each term is `−Λ(n)∫_{s ≥ log n} h'`, and on `(0,S]` the atoms below `s` sum to
   `ψ(e^s)` exactly (`n ≤ ⌊e^s⌋ ⟺ log n ≤ s`).
2. **Two-pole comparison weight.** `w(s) = e^s + s − 1` is the primitive, vanishing at `0`, of the
   polar density `e^s + 1 = 2 e^{s/2} cosh(s/2)`. Its two pieces are the poles of the completed zeta
   function at `s = 1` and `s = 0`. By parts, `∫_{s>0} w h' = −∫_{s>0}(e^s+1) h`.
3. **Per point.** Subtracting at `h = h_x`:
   `Σ_n 2Λ(n)n^{−1/2}F(x+log n) − 4∫_{s>0} cosh(s/2) F(x+s) ds = ∫_{s>0} E(s) h_x'(s) ds`.
4. **Paired with `F` and Fubini.** With `polarHankel F = ∫_ℝ cosh(s/2) A(s) ds` and
   `lagDefectWeight F s = 2e^{−s/2}(∫F(x)F'(x+s)dx − ½A(s))`:

       2·primeSideCharge F − 2·polarHankel F = ∫_{s>0} E(s) · lagDefectWeight F s ds .

5. **The pole plane is the cosh-Hankel pairing.** `polarHankel F = evenPoleMoment F² − oddPoleMoment F²`
   (corpus: `RHTower.ArchimedeanExactForm.integral_autocorr_mul_cosh`, since
   `(∫Fe^{u/2})(∫Fe^{−u/2}) = (∫F cosh)² − (∫F sinh)²`). Hence, from `fullZeroForm`'s definition,

       fullZeroForm F = markovEnergy F + 2·polarHankel F
                      = markovEnergy F + 2·primeSideCharge F − ∫_{s>0} E(s)·lagDefectWeight F s ds,

   and `markovEnergy + 2·primeSideCharge` is the purely archimedean channel
   (`RHTower.markovEnergy_eq_arch_sub_primes_atom`, with `weilTest F F (±log n) = A(log n)` for real `F`).

## What it gives

- **The prime–polar balance is exact, not heuristic.** The atoms and the pole cancel identically
  against the two-pole prediction; the entire residue is `E`.
- **The Weil-natural Chebyshev defect is `ψ(x) − x − log x + 1`, not `ψ(x) − x`.** The reflected pole
  at `s = 0` contributes the `log x`. This is the structural reason receiver 1 carries `(1+T)`.
- **The two faces are one.** `Ẑ ≥ 0` on odd compact tests becomes a family of one-sided weighted
  bounds on `E`, indexed by the lag weights `lagDefectWeight F` realisable at aperture `r`.
- **Why rate `1` is the unconditional floor.** Unconditionally only `E(s) = o(e^s)` (PNT) is known,
  and `|∫E·W| ≤ sup|E e^{−s}| ∫ e^s|W|`, giving a loss `≍ e^r`. RH is `E(s) = O(s e^{s/2})`.
- **Test design becomes kernel design.** Any odd test at aperture `r` is a kernel against `ψ(x) − x`;
  the graded target (deficit `C e^{2σ r}` ⟹ strip `½+σ`) is a growth condition on that kernel.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven on paper (steps 1–5 complete and dependency-closed)
- [ ] 2 → 3  formalized. Steps 1–3 are in
      `GaloisForLFunctions/ArithmeticIncidencePositivity/LagChebyshevAbelSummation.lean`, compiled,
      wired into the area umbrella, axioms `[propext, Classical.choice, Quot.sound]` only:
      * `lagChebyshev`, `twoPoleWeight`, `chebyshevTwoPoleDefect` (the objects)
      * `lagChebyshev_eq_sum_step` — the atoms at lags `≤ s` sum to `ψ(e^s)`, exactly
      * `sum_vonMangoldt_mul_eq_neg_integral` — lag Abel summation
      * `integral_twoPoleWeight_mul_deriv` — the two-pole weight returns the polar density
      * `sum_vonMangoldt_sub_polar_eq_chebyshev` — **the balance**, for every `C¹` lag weight
      * `primeShift_sub_polarDensity_eq_chebyshev` — the balance on one translate of a compact
        `C²_c` test, in elementary terms:
        `Σ_{n≤N} 2Λ(n)n^{−1/2}F(x+log n) − 4∫_{s>0} cosh(s/2)F(x+s) ds = ∫_{s>0} E(s)·h_x'(s) ds`
      * `stripMass`, `stripMass_cost_eq_polar_add_chebyshev` — **the strip masses of the global
        allocation**: `m(s) = ∫_{s−r}^{r} F²` is a `C¹` lag weight with `m'(s) = −F(s−r)²`, so the
        balance applies verbatim and

            Σ_{n≤N} 2Λ(n)n^{−1/2} m_n(F)
              = ∫_{s>0} 4cosh(s/2) m(s) ds
                + ∫_{s>0} E(s)·2e^{−s/2}(−F(s−r)² − ½m(s)) ds .

        The polar density pays the entire strip-mass cost at PNT level; the whole arithmetic
        content of the strip-mass side of the allocation is the `E`-integral.  This answers
        "what pays the strip masses" (AIP open problem 7(c), research topic 6) in the only form
        the ledger can use: an explicit arithmetic-free term plus a Chebyshev-defect residue.
      * `abs_sum_vonMangoldt_sub_polar_le`, `tailWeight`,
        `sum_vonMangoldt_sub_polar_tailWeight` — the balance is a two-way dictionary: it bounds the
        imbalance by `∫|E||h'|`, and on the tail weight of a continuous bump the imbalance is
        exactly `−∫Eφ`, so the imbalances determine `E` (the visibility witness the field's
        "pairs" criterion demands).
      * `integral_chebyshev_mul_deriv_eq_Ioc` — **the horizon law**: a weight dying at `S` reads
        `E` only on `(0, S]`, so an aperture-`r` ledger sees the defect up to `e^{2r}` and no
        further.  With `lagChebyshev_mono`, `lagChebyshev_nonneg`, and
        `chebyshevTwoPoleDefect_eq_twoPoleWeight_of_lt_log_two` — **the lag-side quiet zone**:
        below `s = log 2` the defect is exactly the two-pole weight, so the balance carries no
        arithmetic there and the arithmetic begins precisely at the first prime.
      * `chebyshevError`, `sum_vonMangoldt_sub_polar_eq_chebyshevError` — **the receiver bridge**.
        Splitting `E(s) = (e^s − ψ(e^s)) + (s − 1)` and integrating the elementary half by parts,

            Σ_n Λ(n)h(log n) − ∫_{s>0}(e^s+1)h = ∫_{s>0} (e^s − ψ(e^s))·h'(s) ds + h(0) − ∫_{s>0} h .

        The only arithmetic datum left is the Chebyshev error `e^s − ψ(e^s)`, the integrand of the
        critical-scale cancellation functional `D(T) = ∫_0^T(e^t − ψ(e^t))dt` whose one-sided bound
        `D(T) ≤ B(1+T)e^{T/2}` is RH-equivalent.  The incidence face's prime–polar imbalance and
        that receiver are the same arithmetic datum, read through `h'`.
      * `rampSum`, `integral_Ioi_ramp_mul_deriv2`, `sum_vonMangoldt_mul_eq_integral_rampSum` —
        **second-order lag Abel summation**: summing by parts twice reads every atom through its
        ramp, `Σ_n Λ(n)h(log n) = ∫_{s>0} (Σ_n Λ(n)(s − log n)_+) h''(s) ds`.
      * `polarRamp`, `integral_polarRamp_mul_deriv2`,
        `sum_vonMangoldt_sub_polar_eq_rampDefect` — the same for the polar side, giving the
        second-order balance against the ramp defect `polarRamp − rampSum`.
      * `integral_step_eq_ramp`, `rampSum_eq_integral_lagChebyshev` — the ramp sum *is* the
        primitive of Chebyshev's function, `Σ_n Λ(n)(s−log n)_+ = ∫_0^s ψ(e^u)du`.
      * `criticalScalePrefix`, `polarRamp_sub_rampSum`,
        `sum_vonMangoldt_sub_polar_eq_criticalScalePrefix` — **the receiver-primitive form**:

            Σ_n Λ(n)h(log n) − ∫_{s>0}(e^s+1)h = −∫_{s>0} (D(s) + s²/2 − s)·h''(s) ds,
            D(s) = ∫_0^s (e^u − ψ(e^u)) du .

        `D` is exactly the critical-scale cancellation functional of the Riemann tower, whose
        one-sided bound `D(T) ≤ B(1+T)e^{T/2}` at one constant for every scale is RH-equivalent.
        The incidence face's prime–polar imbalance and that receiver are one functional, paired
        through `h''`.
      * `tailTailWeight`, `sum_vonMangoldt_sub_polar_tailTailWeight` — **the ledger computes the
        receiver**: the double tail of a bump has `H'' = φ`, so the imbalance on that family is
        exactly `−∫(D + s²/2 − s)φ`.  Every mollified value of the receiver is an imbalance of the
        incidence ledger; the pairing is non-degenerate in both directions.
      * `lagStripWeight`, `deriv_lagStripWeight_nonpos`, `negPart_chebyshevTwoPoleDefect_le`,
        `balance_lagStripWeight_le` — **the strip-mass weight is sign-definite** (the strip mass
        decreases in the lag), so the balance becomes an unconditional *inequality*: the
        prime–polar imbalance of the strip-mass weight is at most the negative part of `E`
        weighted by the weight's own decrease.  The pole therefore fails to pay a strip mass only
        at scales where `ψ(x) > x + log x − 1` — the open end of the global allocation is a
        one-sided Chebyshev bound, and nothing else.
      * `autoCorrelation`, `crossCorrelation`, `hasDerivAt_autoCorrelation`,
        `continuous_crossCorrelation`, `contDiff_one_autoCorrelation`, `lagTestWeight`,
        **`testBalance`** — **step 4, the test-level balance.**  The autocorrelation of a
        compactly supported `C¹` test is itself `C¹` with derivative the cross-correlation against
        `F'` (differentiation under the integral, dominated by `‖F‖·sup|F'|`), so `2e^{−s/2}A(s)`
        is a lag weight and

            Σ_{n≤N} 2Λ(n)n^{−1/2}A(log n) − ∫_{s>0} 4cosh(s/2)A(s) ds
              = ∫_{s>0} E(s)·2e^{−s/2}(A_×(s) − ½A(s)) ds .

        The prime side of the critical form and the polar density paired with the autocorrelation
        cancel identically at PNT level; the whole residue is `E`.  Done without the
        `ArithmeticCriticalityTheory` cone by defining the autocorrelation locally.
      * `leftPart`, `rightPart`, `mul_shift_eq_leftPart_mul_rightPart`,
        `autoCorrelation_le_half`, `mul_shift_eq_zero_of_bump`,
        `autoCorrelation_half_attained` — **the sharp aperture law past the aperture.**  Beyond
        the aperture the overlap and its translate occupy disjoint halves of the support, so
        `A(t) ≤ A(0)/2` for every `t > r`; and the constant is *attained*, by two copies of one
        bump of width `2r − t` at spacing `t`.  This closes the per-lag reading of the prime side
        exactly at `½` — strictly better than the chord-cascade `3/4` available before, and no
        further improvement is possible atom by atom, so the remaining deficit of the ledger is
        genuinely multi-atom.
      * `autoCorrelation_rightPart_eq_zero`, `integral_rightPart_shift_mul`,
        `two_mul_sum_lag_le_bipartite` — **the bipartite reduction.**  Past the aperture every lag
        pairs the left half of the test against the right half, so the whole prime side beyond the
        aperture is one bilinear pairing and a single Cauchy–Schwarz gives

            2 Σ_n c_n A(t_n) ≤ ε ‖F|_{x<0}‖² + ε⁻¹ Σ_{n,m} c_n c_m A_v(t_m − t_n),

        where `A_v` is the autocorrelation of the *right half*, supported on a window of half the
        diameter.  So the bilinear problem only ever sees lag differences below `r` — prime
        ratios below `e^{r}`, not `e^{2r}`: the ratio range the cross-prime aggregate must control
        is square-rooted.
      * `autoCorrelation_neg`, `hasCompactSupport_polarPair`,
        `integral_cosh_mul_autoCorrelation`, `integral_eq_two_mul_Ioi`,
        `hasCompactSupport_autoCorrelation`, **`testBalance_poleplane`** — **step 5.**  A Fubini
        on the compactly supported two-variable integrand and the `cosh` subtraction formula give
        `∫_ℝ cosh(s/2)A(s) ds = (∫F cosh(x/2))² − (∫F sinh(x/2))²`: the polar term of the balance
        *is* the hyperbolic pole plane of the Weil form.  Hence

            Σ_{n≤N} 2Λ(n)n^{−1/2}A(log n) − 2[(∫F cosh(x/2))² − (∫F sinh(x/2))²]
              = ∫_{s>0} E(s)·2e^{−s/2}(A_×(s) − ½A(s)) ds .

        The prime channel of the critical form and its pole plane — the two arithmetic channels of
        `Ẑ` — cancel to the accuracy of the prime number theorem, and the two-pole Chebyshev
        defect is the entire residue.  Done Mathlib-only, so it no longer waits on
        `ArithmeticCriticalityTheory`; what that cone would add is only the renaming of
        `(∫F cosh)² − (∫F sinh)²` as `evenPoleMoment² − oddPoleMoment²` inside `fullZeroForm`.
      * `integral_eq_zero_of_odd`, **`testBalance_odd`** — on an odd test the `cosh` moment
        vanishes, so the prime side and the pole charge `2(∫F sinh(x/2))²` — the two nonnegative
        *costs* of the incidence ledger (mechanism 43) — sum exactly to the Chebyshev functional:

            primeSide(F) + poleCharge(F) = ∫_{s>0} E(s)·2e^{−s/2}(A_×(s) − ½A(s)) ds .

      * `abs_testBalance_le` — the explicit unconditional rate: the arithmetic channels are
        bounded by the Chebyshev defect below the horizon weighted by the test's own lag weight,
        so any improvement in the one-sided size of `ψ(x) − x − log x + 1` transfers directly
        into the ledger's rate.
      * `lagPrefix`, `lagSourceDefect`, `lagPrefix_eq_sum_step`,
        `sum_weight_mul_eq_neg_integral`, **`sum_weight_sub_polar_eq_defect`** — the balance for
        an **arbitrary arithmetic source**: every weight vanishing at `0` and `1` has its own lag
        prefix and two-pole defect, and the identity holds verbatim.  The von Mangoldt statements
        are now instances of it.  What distinguishes a source is therefore not the identity but
        the *size* of its own defect.
      * `shiftedPairWeight`, `two_mul_vonMangoldt_le_shiftedPairWeight`,
        `lagSourceDefect_shiftedPair_le`, `sum_shiftedPair_sub_polar_eq_defect` — **the
        selectivity audit.**  The shifted pair `ζ(s−α)ζ(s+α)` carries `Λ(n)(n^α + n^{−α}) ≥ 2Λ(n)`
        at every index, so its prefix exceeds twice Chebyshev's function and

            lagSourceDefect(shiftedPair α)(s) ≤ E(s) − ψ(e^s) .

        A two-pole comparison calibrated to `ζ` is displaced by a *full Chebyshev count* for the
        shifted pair: the two sources cannot share a calibration, which is what the test-model
        criterion of the shared target demands of any mechanism.
      * `lagPrefix_log_nat`, `lagPrefix_neg_one`, **`eq_of_lagPrefix_eq`**,
        `lagSourceDefect_ne_of_ne`, `chebyshevTwoPoleDefect_le_lagSourceDefect` — **source
        rigidity.**  The lag prefix determines the source index by index, so the balance's residue
        is a *complete invariant*: distinct arithmetic sources have distinct defects.  The
        identity is universal but loses no information — a Beurling system with a different
        weight is separated from `ζ` at some index.  And every weight dominated by `Λ` (a sign
        twist, a character twist, a thinned weight) has a *larger* defect, so `ζ` is the closest
        source to the two-pole calibration among them: with the shifted pair on the other side
        (#18), `ζ` is pinned between the two test models.
      * `abs_autoCorrelation_le`, `abs_crossCorrelation_le`,
        **`abs_lagTestWeight_deriv_le`** — the lag weight of a test is exponentially damped with
        an explicit constant: `|W_F(s)| ≤ e^{−s/2}(2A(0) + ‖F'‖²)`.  With the horizon law this
        makes the grading fully quantitative and test-uniform: the ledger's deficit at aperture
        `r` is the Chebyshev defect tested against a weight of total size `O(A(0) + ‖F'‖²)`
        damped by `e^{−s/2}`, so `|E(s)| ≲ e^{s}` reproduces the unconditional rate `e^{r}` and
        `|E(s)| ≲ s e^{s/2}` (RH) gives a deficit polynomial in the aperture — the `σ = 0` end of
        the graded family, with no loss in the exponent anywhere in the dictionary.
      * `chainIndex`, `chainRungs`, `chainWeight`, `chainWeight_add_add_sub`,
        **`autoCorrelation_le_chainConstant`** — **the aperture–lag ladder.**  At a general lag
        the points of the support reachable by steps of `t` form chains of at most `⌊2r/t⌋ + 1`
        points, and the discrete sine on the chain index is the Schur weight realising the path's
        top eigenvalue, giving

            A(t) ≤ cos(π / (⌊2r/t⌋ + 2)) · A(0)   for every t > 0.

        Past the aperture (`⌊2r/t⌋ = 1`) this is the sharp `½` of #12; beyond `2r` it is `0`; at
        small lags it is the quadratic decorrelation floor `A(0) − A(t) ≳ A(0)·t²/r²`, about five
        times the chord-cascade floor.  The per-lag reading of the prime side is thus solved
        exactly at every rung, not only past the aperture.
      * **`shiftDefect_ge_quadratic`**, **`sum_atom_mul_autoCorrelation_le_ladder`** — the
        **price list of the per-lag reading.**  In defect coordinates the ladder is a quadratic
        decorrelation floor `A(0) − A(t) ≥ 2A(0)/(⌊2r/t⌋+2)²` (half-angle plus Jordan), and
        summed over the atoms it is the best bound on the prime side available to any estimate
        reading one lag at a time: each atom weighted by its own ladder constant.  Since the
        ladder is attained at every rung, this is the exact resolution limit of that class of
        methods — an admissibility price in the sense of the shared target's units.
      * `integral_Ioi_deriv_eq_zero`, **`integral_chebyshev_mul_deriv_add_const`**,
        `sum_vonMangoldt_sub_polar_eq_chebyshev_centred` — **band tests see only the increment of
        the defect.**  A weight vanishing near the origin and past `S` has `∫h' = 0`, so adding a
        constant to `E` changes nothing: the residue is `∫(E − c)h'` for *every* reference level
        `c`.  The ledger on a band therefore charges the *variation* of `ψ(x) − x − log x` across
        the band, never its absolute size — which is why the programme's window and light-cone
        mechanisms are the natural ones, and it replaces `sup|E|` by the oscillation of `E` in
        every band-localised estimate.
      * `integrableOn_Ioi_lagSourceDefect_mul_deriv`,
        `integral_lagSourceDefect_mul_deriv_add_const`, `sum_weight_eq_band`,
        **`sum_weight_band_sub_polar_eq_increment`** — **the band-localised dictionary**, for an
        arbitrary source.  A weight supported in `[s₁, S]` sees only the atoms of the band and
        charges exactly the band's own increments:

            Σ_{e^{s₁} < n} a(n) h(log n) − ∫(e^s+1)h
              = ∫ [ (e^s + s − A(e^s)) − (e^{s₁} + s₁ − A(e^{s₁})) ] h'(s) ds .

        The growth of the two-pole prediction against the growth of the source's prefix across
        the band, and nothing else.
      * `deriv_eq_zero_of_vanishing_left`, `integral_Ioi_deriv_deriv_eq_zero`,
        `integral_Ioi_id_mul_deriv_deriv_eq_zero`, **`integral_affine_mul_deriv_deriv_eq`** —
        **second-order gauge invariance.**  A band weight vanishing to first order at both ends
        has `∫h'' = 0` and `∫ s·h'' = 0`, so adding any affine function to the receiver primitive
        leaves the second-order balance unchanged.  A second-order band test therefore charges
        only the **curvature** of `D(s) = ∫_0^s(e^u − ψ(e^u))du` across the band — neither its
        value (killed already at first order, #23) nor its slope.  This is the exact reason
        second-order tests are the strong ones: they annihilate the two cheapest degrees of
        freedom of the receiver and leave only the part no calibration can absorb.
      * `intervalIntegrable_criticalScaleIntegrand`, `continuous_criticalScalePrefix`,
        `integrableOn_Ioi_criticalScalePrefix_mul_deriv_deriv`,
        **`sum_vonMangoldt_band_eq_receiver_curvature`** — the capstone of the band layer.  For a
        `C²` weight supported in `[s₁, S]`, `s₁ > 0`,

            Σ_{band} Λ(n)h(log n) − ∫(e^s+1)h = −∫ (D(s) + s²/2 − s + αs + β) h''(s) ds

        for *every* `α, β`.  The ledger of a band test is the curvature of the critical-scale
        receiver across the band: the band restriction removes the atoms outside, the first-order
        invariance removes the accumulated defect, the second-order invariance removes its slope,
        and what is left is the one part of `D` no recalibration can absorb.
      * `liouvilleTwistWeight`, `sum_liouvilleTwist_sub_polar_eq_defect`,
        `lagSourceDefect_liouville_sub`, **`chebyshevTwoPoleDefect_le_liouville`** — **the third
        test model.**  The Liouville-twisted weight `λ(n)Λ(n)` is dominated by `Λ`, so its defect
        exceeds `ζ`'s, and the excess is exactly `Σ_{n ≤ e^s}(1 − λ(n))Λ(n)` — twice the mass of
        the prime powers with an odd number of factors, which includes every prime.  With the
        shifted pair displaced by a full `ψ` on the other side (#18) and the rigidity theorem
        (#19) saying the defect is a complete invariant, the three test models the shared target
        names are all separated from `ζ` at the level of the mechanism.
      * **`abs_residue_le_centred`**, **`abs_residue_band_le_affine`** — the citable estimates.
        The two gauge invariances turn the ledger's deficit into an *approximation error*:
        bounded at first order by `∫|E − c||h'|` for every level `c`, and at second order on a
        band by `∫|D + s²/2 − s + αs + β||h''|` for every affine function.  Optimising, the
        deficit is the oscillation, respectively the affine deviation, of the critical-scale
        receiver across the band — never its size.  This is the sharpest form of the grading the
        programme asks for, and it is what a user of the dictionary actually cites.
      * `secondCrossCorrelation`, `hasDerivAt_crossCorrelation`,
        `continuous_secondCrossCorrelation`, `contDiff_one_crossCorrelation`,
        `contDiff_one_deriv_lagTestWeight`, **`testBalance_band_receiver_curvature`** — **the
        second-order calculus of a test.**  For a `C²` test the cross-correlation is itself
        differentiable with the second cross-correlation as derivative, so the lag weight is `C²`
        with `h'' = 2e^{−s/2}(A'' − A' + ¼A)`, and the band/curvature capstone applies to actual
        tests: the prime channel and the pole plane of a `C²` test, restricted to a band, are the
        curvature of the critical-scale receiver paired with the test's own second-order lag
        weight.
      * `autoCorrelation_translate`, `eq_zero_of_odd`, `continuous_rightPart_of_odd`,
        **`autoCorrelation_rightPart_le_chainConstant`** — **the half-test ladder.**  For an odd
        test the right half is continuous (oddness gives `F 0 = 0`) and lives on `[0, r]`, so
        after centring it is a test of aperture `r/2` and the ladder applies with that aperture:

            A_v(t) ≤ cos(π/(⌊r/t⌋ + 2))·A_v(0).

        The Gram matrix of the bipartite reduction (#13), whose entries are exactly these
        half-test correlations at the lag differences, therefore decays by the ladder at **half**
        the aperture — twice as fast as the full test's, which is the quantitative content of the
        bipartite halving.
      * `autoCorrelation_rightPart_le_chainConstant_abs`, **`sum_gram_le_ladder`** — **the Gram
        bound.**  Assembling the bipartite reduction with the half-test ladder: every entry of
        the Gram matrix of the bipartite reduction is the half-test's mass on the diagonal and
        ladder-damped at aperture `r/2` off it.  The prime side beyond the aperture is therefore
        controlled by an explicit matrix whose off-diagonal decay is known exactly — the
        cross-prime aggregate is no longer an opaque bilinear form.
      * **`one_div_le_log_sub_log`**, `chainRungs_eq_three`,
        **`autoCorrelation_rightPart_le_half_of_annulus`** — **where the Gram damping bites.**
        Distinct integers below `N` have logarithms at least `1/N` apart, so almost every lag
        difference of the prime side is far below the aperture and the ladder damps it not at
        all.  The damping is effective exactly on the annulus `r/2 < |δ| ≤ r` — prime ratios
        between `e^{r/2}` and `e^{r}` — where the Gram entry is at most *half* the half-test's
        mass.  This is the exact reach of the bipartite route: a factor two on that annulus and
        nothing elsewhere, so any further gain in the cross-prime aggregate must come from the
        arithmetic of the ratios, not from the geometry of the test.
      * **`sub_div_le_log_sub_log`**, **`abs_sub_le_of_abs_log_sub_le`**,
        `abs_sub_le_of_dyadic_window` — **the arithmetic input for the near-diagonal block.**  A
        small lag difference forces a small *integer* difference, by a factor equal to the size:
        `|b − a| ≤ M·δ` whenever `a, b ≤ M` and `|log b − log a| ≤ δ`.  On a dyadic window this
        says the pairs in the Gram's near-diagonal block — the one place the ladder cannot act
        (#32) — are exactly those within `2Xδ` of each other, converting the remaining question
        about prime ratios into one about prime differences in short intervals.
      * **`card_lagClose_le`** — **the near-diagonal block is banded.**  On a dyadic window each
        row of the Gram has at most `2⌊2Xδ⌋ + 1` entries with lag gap below `δ`.  So the block
        the ladder cannot damp (#32) is a banded matrix whose bandwidth is set by the integer
        spacing of the window, not by the number of atoms in it: the cross-prime aggregate is a
        banded form with explicitly damped tails, which is the shape a Schur or Gershgorin bound
        can use.
      * **`sum_mul_mul_le_rowSum`** (the Schur test), **`two_mul_sum_lag_le_schur`** — **the
        `ℓ²` form of the prime side beyond the aperture.**  A symmetric form with nonnegative
        weights is bounded by its largest absolute row sum times the coefficient energy, so

            2 Σ_n c_n A(t_n) ≤ ε‖F|_{x<0}‖² + ε⁻¹·R·Σ_n c_n² ,

        with `R` the largest row sum of the half-test's correlations at the lag differences.  The
        atoms now enter through `Σ c_n²` — an `ℓ²` norm, not `ℓ¹` — and the whole rate question
        is concentrated in `R`, a banded matrix with ladder-damped tails (#31–#34).  This is the
        exact shape the programme needs for a power saving: the remaining unknown is a row sum of
        prime-ratio correlations, nothing else.
      * `hasCompactSupport_rightPart`, **`rowSum_le_bandwidth`**,
        **`two_mul_sum_lag_le_of_schurConstant`** — **the row sum and the replacement
        hypothesis.**  The Gram's row sums are carried by the lag-gap ball of radius `r`, so the
        Schur constant is the half-test's mass times the bandwidth.  Because the ladder is
        *one-sided* it cannot shrink an absolute row sum, so the honest conclusion is a
        replacement hypothesis, proved sufficient: a Schur constant `κ` for the prime-ratio
        correlations gives

            2 Σ_n c_n A(t_n) ≤ ε‖F|_{x<0}‖² + ε⁻¹ κ A_v(0) Σ_n c_n² ,

        an `ℓ²` bound.  A power saving over the `ℓ¹` cost is therefore *equivalent* to a bounded
        Schur constant for the prime-ratio correlations, and no further property of the test can
        supply one — the test side of the problem is closed.
      * **`log_sub_log_eq_iff`**, **`autoCorrelation_rightPart_ratio_eq`** — **the Gram is
        multiplicatively Toeplitz.**  Two pairs have the same lag difference exactly when they
        have the same ratio (`log a − log b = log c − log d ↔ ad = cb`), so the bipartite Gram is
        a function of the *ratio* alone.  Its entries are indexed by rationals and its
        multiplicities by the divisor structure of the window — which is precisely the incidence
        structure AIP's ratio pairs describe, now realised inside the bilinear form that carries
        the rate.
      * **`ratio_param`**, **`card_ratioFirsts_le`** — **the multiplicity of a ratio.**  The
        pairs of a window realising a reduced ratio `a/b` are exactly the multiples `(ka, kb)`,
        so a ratio of height `a` occurs at most `Y/a` times below `Y`.  With #37 this organises
        the Gram completely: its entries are indexed by rationals, their sizes are given by the
        half-test's correlation at `log(a/b)`, and their multiplicities fall off like the
        reciprocal of the height — the Gram's mass concentrates on ratios of small height, which
        is the divisor structure of the window acting directly on the bilinear form that carries
        the rate.
      * `le_sqrt_mul_of_two_mul_le`, **`sum_lag_le_sqrt`** — **the optimised `ℓ²` bound.**
        Optimising the free parameter of the bipartite split turns the two-term estimate into a
        single geometric mean:

            Σ_n c_n A(t_n) ≤ √( ‖F|_{x<0}‖² · R · Σ_n c_n² ) .

        The prime side beyond the aperture is at most the geometric mean of the left half's mass
        and the Schur constant times the coefficient energy — the final form of the bipartite
        route, with the atoms entering only in `ℓ²`.
      * **`autoCorrelation_dilate`**, `sum_lag_dilate`, `lam_mul_log_eq_log_rpow` — **dilating
        the test is a change of source.**  `A(F(λ·))(t) = λ⁻¹A(F)(λt)`, so the dilated test reads
        the original at the lags `λ log n = log n^λ`: it is the Beurling system of `λ`-th powers,
        whose zeta has its pole at `1/λ`.  A dilation-invariant positivity statement would
        therefore be a statement about a whole family of pole positions, not about `ζ`.
      * **`sum_gram_eq_integral_sq`**, `sum_gram_nonneg`, `sum_gram_split`,
        **`sum_gram_offDiag_ge`** — **the Gram form is a square.**  The full lag Gram form of any
        family of atoms is `∫(Σ cₙF(·+tₙ))²`, hence nonnegative with no arithmetic input: all the
        content of a positivity statement lies in the comparison with the polar side.  Splitting
        off the diagonal gives the sharp lower bound `−A(0)Σcₙ²` for the off-diagonal sum, the
        matching counterpart of the ladder and Schur upper bounds.
      * **`two_mul_displacement_eq`**, **`displacement_add_le`**, `displacement_two_mul_le`,
        `autoCorrelation_two_mul_ge`, `autoCorrelation_le_seven_eighths` — **the displacement
        energy is the square of a metric.**  `D(t) = A(0) − A(t)` is half the squared `L²`
        distance to the translate, so `D(s+t) ≤ 2D(s)+2D(t)` and `D(2t) ≤ 4D(t)`.  Read
        backwards, a gap at a large lag forces a gap at every smaller dyadic lag: the half law
        past the aperture already yields `A ≤ 7A(0)/8` at *half* the aperture, where no overlap
        argument applies.
      * **`displacement_two_pow_le`**, **`autoCorrelation_le_of_two_pow`**, `exists_gap_of_pos` —
        **a quantitative gap at every positive lag.**  `D(2ʲt) ≤ 4ʲD(t)` is exact square scaling
        along dyadic multiples; against the half law it gives
        `A(u) ≤ A(0)(1 − 1/(2·4ʲ))` whenever `u` reaches past the aperture in `j` doublings, and
        hence a strict gap at every `u > 0`.  This is the first quantitative control below the
        aperture, where the one-sided ladder is vacuous.
      * **`crossAggregate_eq_meanSquare`**, **`crossAggregate_ge`**, **`crossAggregate_le`** —
        **the cross-prime aggregate** (AIP research topic 8).  The aggregate
        `Σ_{p≠q} w_p w_q A(log(q/p))` is the mean square of the prime field
        `Φ = Σ_p w_p F(·+log p)` minus its diagonal.  Hence it never falls below
        `−A(0)Σ_p w_p²` — no cancellation can make it exponentially negative, so the question is
        one-sided — and for nonnegative weights it is at most `A(0)((Σ_p w_p)² − Σ_p w_p²)`.  The
        upper bound is governed by the `ℓ¹` norm of the weights: for the first-power Euler
        weights `log p/(p−1)` on `p ≤ e^{2r}` Mertens gives `Σ_p w_p = 2r + O(1)`, so that family's
        aggregate is `O(r²)A(0)` — polynomial, as the grading asks.  The open case is the
        half-power family `√p log p/(p−1)`, whose `ℓ¹` norm is exponential while its `ℓ²` norm
        stays `≍ r²`.
      * **`sourceOfPrefix`**, `lagPrefix_sourceOfPrefix`, **`existsUnique_source_of_prefix`**,
        **`ledger_difference_eq`**, `abs_ledger_difference_le` — **realisation and separation.**
        Differencing a prescribed prefix realises it by a source, so with rigidity the map
        source ↦ prefix is a bijection onto the functions vanishing at the origin.  And the
        ledgers of two sources differ by exactly `∫(prefix difference)·h′`: the polar density
        cancels, so a perturbation of the prefix is detected at precisely the rate at which it
        pairs with the derivative of the test.
      * **`index_eq_prefix_sub`**, `lagPrefix_singleIndexPerturb`, `sum_singleIndexPerturb_sub`,
        **`integral_step_mul_deriv_eq`**, **`ledger_separates_singleIndex`** — **the one-point
        cone** (APT research topic 6).  When the cone is a single weight, membership is an
        identification, and the ledger supplies it: consecutive prefix values differ by one atom,
        a single-index perturbation is read as `ε·h(log m)`, and the ledger separates it exactly
        when the test is nonzero at that lag.  That is the replacement for a cone-membership
        proof.
      * **`sum_weight_dilate_sub_polar_eq_defect`** (with `deriv_dilate`) — **the ledger of the
        Beurling system of `λ`-th powers.**  Reading the atoms at the lags `λ log n` gives the
        balance whose polar density is `λ⁻¹(e^{s/λ}+1)` — pole at `1/λ` — and whose residue is the
        source's own defect read at scale `s/λ`.  The critical line of the `λ`-system is at
        `1/(2λ)` while a fixed receiver's lag weight `e^{−s/2}` stays put, so no criterion
        calibrated to the half-line can be dilation-invariant.
      * **`ledger_mono`**, `ledger_le_vonMangoldt` — **the comparison principle.**  Against a test
        whose lag weight is nonincreasing, the reading is monotone in the prefix.  Domination of
        weights therefore upgrades from a statement about defects to one about the readings
        themselves; the strip weight of a compactly supported test is such a weight, so the
        principle is not vacuous.
      * **`sum_lag_eq_integral_primeField`**, `two_mul_sum_lag_le_energy`,
        **`two_mul_sum_lag_le_aggregate`** — **the prime cost and the aggregate are two moments
        of one field.**  The prime side is `∫F·Φ` with `Φ = Σ_n c_nF(·+log n)`, and the
        cross-prime aggregate is the energy of that same `Φ`.  So `2⟨F,Φ⟩ ≤ t‖F‖² + t⁻¹‖Φ‖²`
        converts any bound on the aggregate (AIP topic 8) into a bound on the `ℓ¹` prime cost
        (APT topic 2): the two fields' sharpest questions are the first and second moment of one
        object.
      * **`poleplane_eq_moment_mul`**, **`poleplane_eq_zero_iff`**, `expMomentPos_odd`,
        **`poleplane_odd`**, **`testBalance_poleFree`** — **the pole plane factorises.**  The
        difference of squares is the product `(∫Fe^{−x/2})(∫Fe^{x/2})` of the two
        half-exponential moments, so the pole plane is a rank-one readout in each: it vanishes
        exactly on the union of the two pole-free hyperplanes, its sign is the agreement of the
        two moments' signs, and on an odd test it is minus a perfect square.  On a pole-free test
        the prime side equals the Chebyshev residue outright, with no polar subsidy.
      * **`lagChebyshev_eq_log_two`**, `integral_chebyshevError_of_const`,
        **`criticalScalePrefix_first_cell`**, **`criticalScalePrefix_second_cell`** — **the
        receiver on the first two cells, exactly:** `D(s) = e^s − 1` below `log 2`, and
        `e^s − 1 − (s − log 2)log 2` on `[log 2, log 3)`.  These are the exact receiver values at
        the apertures of the first prime window.
      * **`criticalScalePrefix_succ`**, **`criticalScalePrefix_log_natCast_succ`** — **the
        receiver is an exact recursion over the integers:**
        `D(log(N+1)) = D(log N) + 1 − ψ(N)log(1+1/N)`, hence the closed form
        `D(log(M+1)) = M − Σ_{k<M} ψ(k+1)log(1+1/(k+1))`.  RH is the one-sided bound
        `D(T) ≤ B(1+T)e^{T/2}` on this completely explicit sequence.
      * **`criticalScalePrefix_on_cell`**, **`hasDerivAt_criticalScalePrefix_of_mem_cell`**,
        `slope_jump_eq_vonMangoldt` — **the receiver is sawtooth-convex and its kinks are the
        atoms.**  On each integer cell `D(u) = e^u − ψ(N)u + const`, strictly convex with slope
        `e^u − ψ(N)`; at each integer scale the slope drops by exactly `Λ(N+1)`.  The arithmetic
        is recoverable from the corners of the graph — source rigidity in analytic form.
      * **`poleWeightAt`**, `hasDerivAt_poleWeightAt`, **`sum_weight_sub_polarAt_eq_defect`** —
        **the ledger at an arbitrary pole.**  For every `ρ ≠ 0` the weight `(e^{ρs} − 1)/ρ + s`
        gives a balance with comparison density `e^{ρs} + 1`; at `ρ = 1` it is the two-pole
        weight.  This is the calibration a Beurling system with its pole off `1` must be read
        with.
      * **`autoCorrelation_sub`**, `two_mul_autoCorrelation_sub_le`,
        **`abs_autoCorrelation_sub_le`** — **the modulus of continuity of the Gram:**
        `|A(s) − A(t)| ≤ √(A(0)·2D(s−t))`.  The Gram entries move no faster than the square root
        of the displacement energy at the separation of their lags.
      * **`two_mul_displacement_le`**, **`abs_autoCorrelation_sub_le_lipschitz`** — **the
        displacement energy from above.**  A derivative bound `M` and aperture `r` give
        `2D(t) ≤ M²t²(2r+2|t|)`, so the Gram entries are Lipschitz in the lag with explicit
        constant: the quantitative form of the banded near-diagonal block.
      * **`sum_lag_eq_of_horizon`**, `abs_sum_lag_le_l1` — **the reading has a horizon.**  A test
        of aperture `r` sees no lag beyond `2r`, so the prime side is a finite sum independent of
        the horizon once it passes `e^{2r}`, and each surviving atom is read at most at the full
        mass: the `ℓ¹` prime cost, the rate `1` of the grading, before any arithmetic.
      * **`sum_cross_gram_eq_integral`**, `two_mul_integral_primeField_mul_le`,
        **`abs_sum_cross_gram_le`** — **the bilinear Gram and Cauchy–Schwarz between fields.**
        A cross Gram form is the inner product of two fields, so the cross-aggregate of two
        weight families is at most the geometric mean of their own energies: a family whose field
        has small energy cannot correlate strongly with any other, whatever its arithmetic.
      * **`ledgerField`**, **`testBalance_field`** — **the whole balance is one inner product.**
        The ledger of a test is the test paired with its arithmetic field minus the rank-one polar
        field `2(∫Fe^{x/2})e^{−x/2}`; the tests of zero residue are exactly those orthogonal to
        their own ledger field.
      * **`displacement_ge_min`**, **`fold_defect_ge`**, `sum_weight_mul_autoCorrelation_le` —
        **the tower discount from below** (AIP research topic 7).  The fold defect
        `A(0) − A(log p)` is at least `A(0)·min(log²p/8r², ½)` at every prime, so the reduced cost
        side is `≤ A(0)Σ_p w_p(1 − min(log²p/8r², ½))`: an explicit gain over the trivial `ℓ¹`
        cost, determined by where the prime logarithms sit inside the aperture.
      * **`autoCorrelation_le_min`**, **`window_coupling_le`**, `window_coupling_eq_zero`,
        **`window_degree_lt`** — **the coupling graph between dyadic windows** (AIP open problem
        6).  Windows `k` apart couple through the lag `k log 2` with edge weight at most
        `A(0)(1 − min(k²log²2/8r², ½))`, and exactly zero once `k log 2 ≥ 2r`: the graph has
        degree at most `2r/log 2` and quadratically decaying edges.
      * **`idealSource`**, `idealSource_apply`, **`abs_lagSourceDefect_idealSource_le`** — **the
        two-pole calibration is achievable.**  Differencing the calibration at the integer scales
        gives an integer source whose defect is a sawtooth vanishing at every integer and never
        exceeding `1 + log 2`; its weights are `1 + log(1+1/(n−1))`, every integer carrying weight
        about one — the pole at `1` as an arithmetic.  An `O(1)` defect is thus neither automatic
        nor impossible: the content of the Chebyshev ledger is entirely that the weight is `Λ`.
      * **`abs_ledger_idealSource_le`**, **`ledger_vonMangoldt_sub_ideal`** — the ideal source's
        ledger is uniformly `O(1)` against any test, and the difference between `ζ`'s ledger and
        it is exactly the prime number theorem's error paired with `h′`.  The whole arithmetic
        content of the balance is that one difference.
      * **`sourceScalePrefix`**, `sourceScalePrefix_vonMangoldt`,
        **`sum_weight_sub_polar_tailWeight`**, `ledger_eq_of_defect_integral_eq` — **every
        source's defect is a ledger reading.**  On the tail of a bump the ledger returns
        `−∫(defect)·φ` for an arbitrary source; with realisation and rigidity this closes the
        question of what the ledger exposes.
      * **`integral_autoCorrelation`**, **`integral_autoCorrelation_odd`**,
        **`exists_autoCorrelation_neg`** — **an odd test's Gram kernel is not positive.**  The
        autocorrelation integrates to `(∫F)²`, hence to zero on an odd test, so an odd test of
        positive mass reads some lag negatively: no argument treating the prime side as a sum of
        nonnegative contributions can work on the odd cone.
      * **`autoCorrelation_ge_half_of_mem`**, **`integral_compl_autoCorrelation_le`** — **how
        much negative mass is forced.**  The autocorrelation stays above half the mass on a window
        whose width is set by the test's regularity, so outside that window it integrates to at
        most `−δ·A(0)`: the negative correlation at far lags is forced, not chosen.
      * **`poleWeightAt_half_cell_ge`**, **`defect_half_cell_lower_bound`**,
        **`abs_lagSourceDefectAt_idealSourceAt_le`** — **which poles an integer system can
        calibrate.**  Between consecutive integers the prefix is frozen while the calibration at
        `ρ` keeps growing, so for `ρ > 1` every integer source has defect at least
        `N^{ρ−1}/4ρ` — unbounded.  For every `0 < ρ ≤ 1` the calibration *is* realisable, with
        defect at most `1/ρ + log 2`.  So `1` is exactly the largest pole an integer-indexed
        system can calibrate: the arithmetic origin of the two-pole weight.
      * **`lagPrefix_jump`**, **`defect_ge_of_atom`** — **the ledger cannot hide an atom.**
        Across an integer the prefix jumps by the atom while the calibration moves by at most
        `½ + log 2`, so the defect is at least half the atom minus that constant: source rigidity
        made quantitative.
      * **`exists_abs_chebyshevTwoPoleDefect_gt`** — the Chebyshev defect is unbounded: the
        receiver's one-sided bound is a statement about the *rate* of growth, never about
        boundedness.
      * **`integral_calibration_mul_deriv`**, **`sum_weight_sub_calibration_eq_defect`** — **the
        universal calibration dictionary.**  For any `C¹` calibration `W` vanishing at the origin,
        the reading of a source and the integral of `W′` against the test differ by exactly
        `W − prefix` tested on `h′`.  The two-pole weight and every pole calibration are
        instances.
      * **`oscWeight`**, `hasDerivAt_oscWeight`, **`sum_weight_sub_oscPolar_eq_defect`** — **the
        calibration of a conjugate pair of poles** at `β ± iγ`, with density `e^{βs}cos(γs)`:
        the comparison density for a Beurling system carrying an off-line zero, which is the test
        model both selectivity audits ask for.
      * **`leftPart_eq_neg_rightPart_neg`**, **`autoCorrelation_eq_neg_conv`**,
        **`autoCorrelation_nonpos_of_odd_nonneg`** — **odd tests with a nonnegative half read the
        far lags nonpositively.**  Past the aperture an odd test's correlation is minus the
        *convolution* of its right half with itself, so a nonnegative half makes every far atom
        read with the favourable sign: the sign of the far prime side is a property of the
        half-test's sign pattern, not of the arithmetic.
      * **`sum_lag_le_truncated`** — for an odd test with a nonnegative half the prime side is
        bounded by its part below the aperture: the far arithmetic can only help.
      * **`allOnes`**, **`lagSourceDefect_allOnes`** — **why the calibration carries the reflected
        pole.**  Weight one on every integer gives defect `(e^s − ⌊e^s⌋) + s`: pure integer
        density misses the calibration by exactly the reflected pole, and the `log n` correction
        in the ideal source's weights is its price.  The `+ s` in `e^s + s − 1` is arithmetic,
        not convention.
      * **`autoCorrelation_eq_conv`**, `autoCorrelation_nonneg_of_halves` — past the aperture the
        Gram is the convolution of the two halves of the test, so the far reading depends on the
        halves only through that convolution.
      * **`autoCorrelation_eq_zero_abs`**, **`aggregate_le_bandwidth`**,
        **`aggregate_dyadic_le`**, **`aggregate_dyadic_diagonal`** — **the aggregate's Schur bound
        with an explicit bandwidth** (AIP topic 8).  Only pairs whose ratio lies inside the
        aperture contribute, so the aggregate is at most `A(0)·B·Σw²` with `B` the number of
        partners within the aperture; on a dyadic window `B ≤ 2⌊4Xr⌋+1`, and for `2r < 1/2X` the
        aggregate is exactly diagonal.
      * **`genPrefix`**, **`sum_gen_mul_eq_neg_integral`**,
        **`sum_gen_sub_calibration_eq_defect`** — **the ledger of an arbitrary lag system.**
        Abel summation and the balance against any calibration hold for any finite family of
        positive real lags: the ledger a Beurling system is read with in its own lags, with the
        integer case as the instance `λ_n = log n`.
      * **`geoWeight`**, `genPrefix_geo_cell`, **`geo_defect_half_cell`**,
        **`geo_reading_gap`** — **a geometric Beurling system read by the same ledger.**  With
        generalised integers `g^n` the prefix is frozen across each cell while the calibration
        climbs, so on the whole upper half-cell the defect is at least `(1 − g^{−1/2})e^s`, and a
        nonnegative bump there reads the ledger below the polar side by that much.  The ledger
        separates `ζ` from a geometric system at the size of the main term, not at
        prime-number-theorem level.
      * **`fourier_ofReal_autoCorrelation_eq`**, `fourier_ofReal_neg`,
        **`fourier_ofReal_autoCorrelation_sq`** — **the spectral density of the Gram kernel is
        `|F̂|²`.**  The autocorrelation is the convolution of the test with its reflection, so its
        Fourier transform is the squared modulus of the test's: the analytic source of every
        positivity in the programme, and the statement that the arithmetic form is the prime
        Dirichlet polynomial measured against a nonnegative spectral density.
      * **`integral_exp_mul_autoCorrelation`**, **`integral_Ioi_cosh_mul_autoCorrelation`** —
        **the Laplace transform of the Gram kernel factorises:** `∫e^{αt}A(t)dt` is the product
        of the test's two exponential moments at `∓α`, and the half-line `cosh` pairing is half
        that product.  The pole plane is the case `α = ½` and the total mass `α = 0`: every polar
        side, at every pole, is a rank-one readout of the test.
      * **`expMoment_odd`**, **`integral_Ioi_cosh_mul_autoCorrelation_odd`** — on an odd test the
        pole pairing is `−½(∫Fe^{αx})²` at *every* `α`: whatever pole a calibration is built
        around, its polar side never charges an odd test.
- [ ] 3 → 4  publication-ready

## Note on the Lean route

The module depends on `Mathlib` alone, so it is independent of the `ArithmeticCriticalityTheory`
and `RHTower` olean cones, which are intermittently unloadable while the `RHTower/ThetaCusp/` and
`HTGeometry/PolynomialODE/` module moves are completed. Steps 4–5 do need
`ArithmeticCriticalityTheory` (`fullZeroForm`, `markovEnergy`, `oddPoleMoment`, `evenPoleMoment`)
and the ledger objects, and are queued behind that cone.

## Log
- 2026-10-22 — created; paper proof complete; steps 1–3 formalized and compiled.
