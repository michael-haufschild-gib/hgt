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
      * **`lagTestWeightAt`**, **`testBalanceAt`**, **`testBalanceAt_odd`** — **the critical line
        of a pole at `ρ` is `ρ/2`.**  With the weight `2e^{−ρs/2}A(s)` the two exponentials of the
        comparison density recombine into a `cosh` exactly at the normalisation `n^{−ρ/2}`, and
        the polar side becomes `2(∫Fe^{−ρx/2})(∫Fe^{ρx/2})`.  The symmetry point is read off the
        balance, not assumed; on an odd test the prime side and the pole charge are both costs.
      * **`coshMoment`**, `sinhMoment`, **`poleTerm_eq_moment_mul`**, **`capacity_iff`**,
        **`capacity_odd_iff`** — **the capacity inequality restated** (APT receiver 2).  The pole
        term `½C² − ½S²` is `2(∫ge^{−u/2})(∫ge^{u/2})`, so `S² ≤ 2M + C²` says the arithmetic part
        dominates minus that product — on an odd test, twice a perfect square.
      * **`moebiusSource`**, **`lagMertens`**, **`sum_moebius_sub_unit_eq_defect`**,
        `lagMertens_eq_zero_of_lt_log_two`, **`abs_lagMertens_le`**, `lagMertens_eq_neg_one` —
        **the Mertens ledger.**  `1/ζ` has no pole at `1`, so the Möbius source is read against
        the reflected pole alone, `W(s) = s`; its defect is `s − M(e^s)` and the receiver is the
        Mertens receiver.  The unconditional rate is again `e^s`, and the first cells are exact.
      * **`twistSource`**, **`sum_twist_sub_unit_eq_defect`**, `abs_lagPrefix_twist_le` — **the
        ledger of a real character twist.**  A twist has no pole at `1`, so it is read against the
        reflected pole alone and its defect is the twisted Chebyshev function; against `ζ`'s
        two-pole calibration it is off by the whole polar term.
      * **`thetaSource`**, **`sum_theta_sub_polar_eq_defect`**, `chebyshev_le_theta_defect`,
        `theta_defect_eq_chebyshev_of_lt_log_four` — **the prime-only source.**  Its defect
        exceeds `ζ`'s by exactly the prime-power correction `ψ − θ`, which is nonnegative and
        vanishes below the first prime square: the higher powers are a cost, never a gain.
      * **`genRampSum`**, **`sum_weight_mul_eq_integral_rampSum`**,
        **`sum_weight_sub_polar_eq_rampDefect`**, **`sourceScalePrefix_eq`**,
        **`sum_weight_sub_polar_eq_sourceScalePrefix`** — **every source has its own
        critical-scale receiver.**  Two summations by parts read any source through its ramp sum,
        and the second-order balance pairs the source's own critical-scale functional
        `∫₀^s(W − prefix)` against the curvature of the test.  For `ζ` it is `D(s) + s²/2 − s`;
        the receiver is a feature of the ledger, not of `ζ`.
      * **`integral_secondPrimitive_mul_deriv2`**, **`sum_weight_sub_calibration_eq_rampDefect`**
        — **the second-order dictionary in full generality:** for every source and every
        calibration the reading minus the comparison integral is the difference of the source's
        ramp sum and the calibration's second primitive, paired with `h″`.  Every ledger in the
        theory is an instance.
      * **`mertensScalePrefix`**, **`mertensScalePrefix_eq`**,
        **`sum_moebius_sub_unit_eq_mertensScalePrefix`**, `mertensScalePrefix_first_cell`,
        `mertensScalePrefix_second_cell` — **the Mertens receiver** `∫₀^s(u − M(e^u))du`, with its
        first two cells exact: `s²/2` below `log 2`, `s²/2 + s − log 2` on `[log 2, log 3)`.
      * **`pairCorrelation`**, `pairCorrelation_swap`, **`autoCorrelation_add`**,
        **`sum_pair_gram_eq_integral`** — **the pair correlation of two tests.**  The cross Gram
        form of two tests is the inner product of their fields, so the Cauchy–Schwarz apparatus
        applies across tests, not only within one; and the autocorrelation of a sum polarises.
      * **`abs_sum_pair_gram_le`** — Cauchy–Schwarz for the cross Gram of two different tests:
        comparing a source with a model is an inner-product bound.
      * **`logSource`**, **`logWeight`**, **`sum_log_sub_doublePolar_eq_defect`** — **the
        logarithm source and its double pole.**  `−ζ′` has a double pole at `1`, so the
        calibration is `(s−1)e^s + 1 + s/2` with density `s e^s + ½`; its defect is the Stirling
        error, `O(s)` with no hypothesis.  The ledger's difficulty is specific to `Λ`.
      * **`progression_gram_nonneg`**, **`progression_gram_le`**, `progression_gram_diagonal`,
        `autoCorrelation_le_min_abs`, **`progression_offdiag_le`** — **the Gram of a
        multiplicative tower is a banded positive Toeplitz form** (AIP research topic 7): Schur
        constant `A(0)(2⌊2r/L⌋+1)`, exactly diagonal once the step exceeds `2r`, and every
        off-diagonal entry discounted by the quadratic gap at its exponent difference.
      * **`antiDisplacement`**, **`displacement_two_mul_le_antiDisplacement`**,
        **`antiDisplacement_ge`** — **the other side of the Gram.**  `A(0)+A(t)` is half
        `‖F+F(·+t)‖²`; near-anti-periodicity at `t` would force near-periodicity at `2t`, which
        the aperture laws forbid.  So the correlation stays a definite amount above `−A(0)` at
        every nonzero lag: the Gram entries are pinned quantitatively on both sides.
      * **`autoCorrelation_ratio_le`**, **`autoCorrelation_ratio_le_of_ne`**,
        **`crossAggregate_le_gap`** — **no two integers align the test.**  Distinct integers have
        logarithms separated by at least the reciprocal of the larger, so every ratio entry is
        below the mass by `1/(8r²n²)` of it, and the aggregate below a horizon `Y` carries the
        uniform discount `min(1/(8r²Y²), ½)`.
      * **`sum_lag_vonMangoldt_eq_zero`**, **`testBalance_firstWindow`**,
        **`sum_lag_vonMangoldt_firstAtom`**, **`testBalance_firstAtom`** — **the first prime
        window, exactly.**  Below `log 2 / 2` the prime side vanishes identically and the ledger
        is purely archimedean; between `log 2 / 2` and `log 3 / 2` it is the single identity
        `√2·log 2·A(log 2) − 2(pole plane) = residue`.
      * **`residue_firstAtom_le`**, **`sum_lag_vonMangoldt_secondWindow`**,
        **`sum_lag_vonMangoldt_thirdWindow`** — the first three prime windows written out: one
        atom, two atoms, and then the first prime power `4 = 2²` entering with weight `log 2` at
        the lag `log 4`.  The first window's residue is bounded explicitly by the test's mass and
        half-exponential moment alone.
      * **`scaledTwoPoleWeight`**, **`apSource`**, **`sum_ap_sub_scaledPolar_eq_defect`**,
        **`sum_apSource_eq`**, **`sum_lagPrefix_ap`**, **`sum_defect_ap`** — **the ledger of a
        residue class**, calibrated by the two-pole weight scaled by the class's density; and the
        class ledgers partition the `ζ` ledger exactly, with no cross terms, whenever the scale
        factors sum to one.
      * **`pairCalibration`**, **`sum_shiftedPair_sub_pairPolar_eq_defect`**,
        `pairCalibration_sub_twoPoleWeight` — **the shifted pair read at its own poles** `1 ± α`:
        against that calibration it has its own balance, and against `ζ`'s it is off by the whole
        of `e^{(1+α)s}/(1+α)`, larger than the main term.  The separation is a difference of pole
        position, not a prime-number-theorem effect.
      * **`integral_halves_add`**, **`integral_leftPart_sq_eq_half`**, **`sum_lag_le_sqrt_odd`**
        — each half of an odd test carries half the mass, so the optimised bipartite bound is an
        estimate in the mass and the Schur constant alone.
      * **`tendsto_chebyshevTwoPoleDefect_div_exp_iff`**,
        **`tendsto_mertensDefect_div_exp_iff`** — **the leading rate of either ledger is the
        prime number theorem:** `E(s) = o(e^s)` iff `ψ(x) ∼ x`, and the Mertens defect is
        `o(e^s)` iff `M(x) = o(x)`.  Everything the receiver measures lies beyond that rate.
      * **`abs_defect_sourceOfPrefix_le`**, **`cell_increment_le_two_mul_defect`** — **the
        matchability criterion:** an integer source can track a calibration to `O(1)` exactly when
        the calibration's integer-cell increments are bounded.  Differencing realises it with
        defect the largest increment; conversely every source's defect must absorb that increment,
        since the prefix is frozen across a cell.
      * **`poleWeightAt_cell_increment_le`**, **`multiPoleWeight`**, **`abs_defect_multiPole_le`**,
        **`abs_defect_reflectedPole_le`**, **`logWeight_half_cell_increment_ge`**,
        **`defect_logWeight_ge`**, **`gen_cell_increment_le_two_mul_defect`** — the criterion in
        action: a finite family of simple poles in `(0,1]` is matchable with defect
        `Σ c_i(1/ρ_i + log 2)`, the reflected pole alone with defect `log 2`, and a *double* pole
        at `1` not at all — its half-cell increment is `≥ (log N − 1)/2`, which is exactly the
        Stirling loss of the logarithm source.  The criterion holds verbatim for an arbitrary lag
        system.
      * **`defect_ge_of_gap`**, **`geoLags_defect_ge`**, `integer_gap_increment`,
        **`exists_lag_of_defect_le`**, **`card_ge_of_defect_le`** — **the pole at `1` forces the
        density of the generalised primes.**  Across a lag-free interval the defect absorbs
        `e^s(e^δ−1)`, so a bounded defect forces a lag in every such interval, and chaining gives
        the counting bound `≥ (e^S−1)/3K`.  The integers meet the criterion exactly (increment
        `1`); a geometric system fails by a factor of the main term, *whatever weights it uses*.
      * **`card_filter_mul_le_of_defect`**, `gen_cell_increment_id`,
        `exists_lag_of_id_defect_le`, **`min_atom_le_of_defect`** — the count is pinned above as
        well, so the minimum atom of a calibrating system is trapped: it cannot be much larger
        than `K`.  For `ζ` the atoms `log p` are unbounded, which is the defect's unboundedness
        seen from the density side.
      * **`card_ge_of_defect_le_gen`**, **`card_ge_of_id_defect_le`**,
        **`card_ge_of_poleAt_defect_le`** — **each pole forces its own density.**  The chain
        criterion needs only that the calibration climbs by more than `2K` between consecutive
        scales, so the reflected pole alone forces linear density, a pole at `ρ` forces `x^ρ`,
        and the pole at `1` forces `x`.  The exponent of the generalised-prime density *is* the
        position of the pole.
      * **`gen_cell_increment_le_two_mul_defect_supp`**, **`card_support_ge_of_defect_le`**,
        **`card_primePowers_ge_of_chebyshev_defect_le`** — the criterion counts *atoms*, not
        indices, so it applies to `ζ` directly: a Chebyshev defect bounded by `K` up to
        `log(1+3KJ)` forces at least `J` prime powers below `1+3KJ`.
      * **`gram_split_row`**, **`gram_row_le_half`**, `sum_gen_lag_eq_zero`,
        `sum_gen_lag_eq_filter` — **parity.**  Flipping one coefficient's sign leaves the diagonal
        fixed and reverses the two strips through that index; since both Gram forms are squares,
        the total coupling of any one index is at most half the whole form.  No sign-invariant
        functional sees more than the diagonal.
      * **`midpointSource`**, **`abs_defect_midpointSource_le`**, `genPrefix_shift`,
        `genPrefix_union`, `genPrefix_add`, `genPrefix_smul`, `genPrefix_eq_total` — sampling the
        calibration at cell midpoints halves the defect; and the prefix is additive in the
        weights and over disjoint index sets, translates with the lags, and freezes at the total
        mass beyond the last lag.
      * **`gapSource`**, **`genPrefix_gapSource`**, **`abs_defect_gapSource_le`**,
        `twoPoleWeight_gap_increment` — **any lag family realises its calibration up to its
        largest gap increment.**  With the gap criterion this settles the question: the best
        defect a lag family can achieve is, to within a factor two, the largest increment of the
        calibration across its gaps — for the pole at `1`, the gaps of the generalised integers
        themselves.
      * **`genTestBalance`**, **`lagField`**, **`sum_gen_lag_eq_integral_field`**,
        `sum_gen_sub_calibration_tailWeight`, **`genPrefix_jump`**,
        `sum_gen_weil_eq_integral_field`, `integral_lagField_sq_eq`, `gen_crossAggregate_ge`,
        **`two_mul_sum_gen_lag_le`**, **`genTestBalanceAt`** — **the explicit-formula machinery
        for an arbitrary lag system.**  Weil-shaped balance at any pole with normalisation
        `e^{−ρλ/2}` and pole plane `2(∫Fe^{−ρx/2})(∫Fe^{ρx/2})`; the linear reading is the test
        against the system's field; the Gram form is that field's energy; the cross-aggregate is
        bounded below by minus the diagonal; and the atoms are recoverable as prefix jumps.
      * **`testBalance_receiver`**, `testBalance_receiver_odd`, `genTestBalanceAt_odd`,
        **`testBalance_source`**, `testBalance_theta`, **`mertensTestBalance`**,
        **`testBalance_source_sub`**, **`abs_testBalance_source_le`**,
        `abs_testBalance_idealSource_le` — **the Weil form of an arbitrary source**, in both
        first-order and receiver shape, with the same rank-one pole plane; subtracting two
        sources cancels the pole plane entirely, so sources are compared by their prefix
        difference alone; and a source whose defect is majorised by `G` has its whole Weil form
        within `∫G|w|` of the pole plane.
      * **`lagSourceDefect_eq_twoPoleWeight_of_lt_log_two`**, `lagSourceDefect_second_cell`,
        **`testBalance_source_truncates`** — the quiet zone is universal: below `log 2` every
        source's defect is the calibration itself, on the next cell only `a(2)` is visible, and
        at aperture `r` the Weil form involves only the weights below `e^{2r}`.
      * **`primeSide_add`**, `expMomentNeg_add`, `expMomentPos_add`, **`poleplane_add`**,
        **`expMomentNeg_eq_zero_add`**, `expMomentNeg_smul` — **polarisation**: the prime side
        polarises through the pair correlation, the moments are linear, the pole plane polarises
        as `M₋(F)M₊(G)+M₋(G)M₊(F)`, and the pole-free locus is a genuine linear subspace.
      * **`autoCorrelation_smul`**, `expMomentNeg_translate`, `expMomentPos_translate`,
        **`poleplane_translate`**, **`weil_dilation_covariance`** — **the symmetries of the Weil
        form**: degree-two homogeneous, translation-invariant (the moments scale by reciprocal
        factors), and dilation-covariant — dilating by `λ` is reading the `λ`-power Beurling
        system at its own pole `1/λ`, with the normalisation `n^{−1/2}` restored exactly.
      * **`primeSide_translate`**, **`autoCorrelation_reflect`**, `primeSide_reflect`,
        `expMomentNeg_reflect`, **`poleplane_reflect`**, **`testBalance_source_congr`** — the
        Weil form is invariant under the affine symmetries of the line, and two tests with the
        same correlation and the same pole plane give the same form: those two data are
        everything the arithmetic sees.
      * **`evenPart`**, `oddPart`, **`sym_pairCorrelation_even_odd`**,
        **`autoCorrelation_even_odd_split`**, **`poleplane_even_odd`**,
        **`weilForm_even_odd_split`**, `poleplane_even_nonneg` — **the even and odd parts of a
        test do not interact.**  The mixed correlations cancel, the pole plane is the even part's
        squared moment minus the odd part's, and the whole Weil form is additive over the
        decomposition: the odd sector is a direct summand, with a negative pole charge against
        the even sector's positive one.
      * **`weilForm`**, **`weilForm_split`**, **`weilForm_nonneg_iff`**,
        **`residue_even_odd_split`** — **the positivity problem splits into the two sectors**:
        positivity on all tests is exactly positivity on even tests together with positivity on
        odd tests, and the Chebyshev residue splits the same way.
      * `testBalance_liouville`, `testBalance_shiftedPair`,
        **`testBalance_vonMangoldt_sub_liouville`**, `autoCorrelation_zero_split` — the
        selectivity audit at Weil level: each test model has its own Weil-shaped balance with the
        same pole plane, and is compared with `ζ` by the prefix difference alone.
      * **`card_window_ge_of_defect_le`**, `twoPole_window_step` — the forced density is
        scale-local: starting the chain anywhere, a bounded defect forces generalised primes in
        *every* window.
      * **`lagPrefix_eq_of_atomfree`**, **`defect_ge_of_atomfree`**,
        **`chebyshev_defect_ge_of_primePower_free`**,
        **`exists_primePower_of_chebyshev_defect_le`** — **an atom-free interval forces a defect
        of at least half its length.**  A prime-power gap below `x` is visible in the Chebyshev
        defect at full size, and conversely a defect bounded by `K` forces a prime power in every
        interval longer than `2K`.
      * **`defect_poleAt_ge_of_atomfree`**, `chebyshevTwoPoleDefect_log_nat`,
        **`chebyshevTwoPoleDefect_log_two`**, **`chebyshevTwoPoleDefect_log_three`**,
        `lagChebyshev_eq_log_six`, **`criticalScalePrefix_pos_first_cell`**,
        **`criticalScalePrefix_pos_second_cell`** — the gap principle at an arbitrary pole, and
        exact values at the first scales: the defect is `1` at `log 2`, `2 − log 2` at `log 3`,
        and the receiver is strictly positive on the first two cells.
      * **`criticalScalePrefix_pos_on_cell`**, **`criticalScalePrefix_succ_pos`**,
        `log_gap_le_inv`, **`criticalScalePrefix_succ_pos_of_psi`** — positivity of the receiver
        propagates whenever the cell's loss `ψ(N)·log(1+1/N) ≤ ψ(N)/N` stays below its gain `1`:
        the receiver's sign is a statement at prime-number-theorem precision, which is why
        nothing cruder decides it.
      * **`criticalScalePrefix_succ_ge`**, **`criticalScalePrefix_le_nat`**,
        **`criticalScalePrefix_ge_sub`**, **`lagChebyshev_le`**,
        **`criticalScalePrefix_le_exp`**, `integral_id_mul_exp`,
        **`criticalScalePrefix_ge_explicit`** — unconditional envelopes: each cell contributes at
        most one unit and at least `1 − ψ(N)/N`, so the receiver lies between
        `M − Σ ψ(k+1)/(k+1)` and `M` at the integer scales, and between an explicit elementary
        lower bound and `e^s − 1` at every scale.
      * **`squarefreeSource`**, `sum_squarefree_sub_scaledPolar_eq_defect`,
        **`higherPowerSource`**, **`sum_higherPower_sub_halfPolar_eq_defect`**,
        **`testBalanceAt_source`**, `testBalanceAt_higherPower` — two further sources and where
        their poles sit: the squarefree indicator at density `6/π²`, the higher prime powers at
        the pole `1/2` (so their normalisation is `n^{−1/4}` and their symmetry point a
        quarter); and the Weil-shaped balance of an arbitrary source at an arbitrary pole.
      * **`lagPrefix_add`**, **`defect_split_calibration`**,
        **`chebyshevTwoPoleDefect_split`**, `lagPrefix_higherPower_eq_zero_of_lt_log_four`,
        **`primeSide_source_add`**, **`primeSide_higherPower_eq_zero`**,
        **`primeSide_vonMangoldt_eq_theta`** — calibrations compose with the source: `ζ`'s defect
        is the prime-only defect plus the higher-power defect, and below the aperture `log 4 / 2`
        the higher powers contribute nothing, so `ζ`'s Weil form is `θ`'s.
      * **`integrableOn_Ioi_lagSourceDefectAt_mul_deriv`**, **`abs_testBalanceAt_source_le`**,
        **`lagSourceDefectAt_vonMangoldt_ge`** — the Weil form at an arbitrary pole is scored by
        any majorant of that pole's defect, and reading `ζ` at a pole `ρ > 1` costs a defect of
        order `e^{ρs}`: the pole position is pinned by the arithmetic at full strength.
      * **`poleWeightAt_dilate`**, **`lagSourceDefectAt_sub_lagSourceDefect`**,
        **`abs_poleWeight_sub_le_of_two_poles`**, **`abs_window_mass_sub_le`**,
        `lagPrefix_sub_lagPrefix_eq_sum`, **`abs_sum_Ioc_sub_le`** — dilating the lag variable
        moves the pole; the defect's dependence on the pole is source-independent, so no ledger
        is accurate at two poles; and a defect bound at the ends of a window controls the mass
        the atoms carry inside it, not merely their number.
      * **`dconv`**, **`sum_Icc_dconv`**, **`lagPrefix_dconv`**, **`sum_Icc_dconv_mul`**,
        **`sum_lag_dconv`**, **`abs_lagPrefix_dconv_sub_le`** — the hyperbola law in lag
        coordinates: the ledger of a Dirichlet convolution is the superposition of lag-translated
        ledgers of one factor weighted by the other, the pairing of a convolution lives on the
        product lattice, and a calibration of one factor propagates with an `ℓ¹`-amplified error.
      * **`unitSource`**, **`fullMoebius`**, **`abs_lagPrefix_unitSource_sub_exp_le`**,
        **`abs_lagPrefix_dconv_unitSource_sub_le`**, **`lagPrefix_log_eq_log_factorial`**,
        **`sum_fullMoebius_floor`**, **`abs_sum_fullMoebius_div_le_one`**,
        **`lagChebyshev_eq_sum_fullMoebius_log_factorial`**,
        **`lagPrefix_eq_sum_fullMoebius_dconv`**, **`lagPrefix_fullMoebius`**,
        **`lagPrefix_divisorCount`**, **`abs_lagPrefix_divisorCount_sub_le`** — Möbius inversion
        of the ledger: every source is recovered from its summatory convolution by
        Möbius-weighted lag translations, giving `∑_{d≤x} μ(d)⌊x/d⌋ = 1`, `|∑_{d≤x} μ(d)/d| ≤ 1`,
        the divisor ledger `∑_{n≤x} τ(n) = ∑_{d≤x} ⌊x/d⌋` with its harmonic leading term, and the
        closed form `ψ(x) = ∑_{d≤x} μ(d) log(⌊x/d⌋!)`.
      * **`autoCorrelation_eulerFactor`**, **`eulerStep`**,
        **`exists_autoCorrelation_eulerStep`**, **`eulerLam_spec`**,
        **`two_mul_div_one_add_sq_le_one`**, **`eulerLedger`**, **`eulerPayment`**,
        **`eulerLedger_zero_eq`**, **`eulerPayment_le_mass`**, **`two_lag_payment_le`**,
        **`vonMangoldtAtom_le_one`**, **`eulerPayment_vonMangoldt_le_mass`** — the Euler comb
        ledger, answering the free-weight question of AIP research topic 7. A squarefree comb
        factor `F − λF(· + a)` acts on the lag ledger as the second-order difference
        `(1+λ²)A − λ(A(·−a) + A(·+a))`; normalised it is the Euler transform at weight
        `w = 2λ/(1+λ²)`, which preserves the cone of autocorrelations. Iterating over a finite
        list of lags and reading the origin telescopes to the **sequential payment law**
        `Σ_j w_j A_{j−1}(a_j) ≤ A(0)`: each first-power charge, measured in the ledger
        transformed by its predecessors, is paid in full by the mass, with no double counting.
        The admissible weights are exactly `w ≤ 1` and the ceiling is sharp, so the comb pays
        every prime-power Euler weight `Λ(n)/√n ≤ 2/e`. For two lags the price is explicit: the
        charges at the ratio lag `a₂ − a₁` and the product lag `a₂ + a₁` — the two incidence
        relations of AIP §1 — with coefficient `w₁w₂/2`.
      * **`eulerComb`**, **`autoCorrelation_eulerComb`**, **`eulerPayment_residual`**,
        **`eq_zero_of_eq_const_mul_shift`**, **`eulerComb_ne_zero`**,
        **`integral_sq_pos_of_ne_zero`**, **`eulerPayment_lt_mass`** — the residual of the
        payment. The deficit of the sequential law is exactly the energy of the comb,
        `A(0) − Σ_j w_j A_{j−1}(a_j) = ∫(comb F)²`, and a comb factor at a nonzero lag
        annihilates no compactly supported test but zero (a solution of `H = λH(· + a)` with
        bounded support vanishes). Hence the payment is **strict for every nonzero test**: the
        first-power charges are never paid in full by the mass. This is the property the Euler
        envelope of a prime tower lacks — that envelope is attained by a resonant train and so
        carries no information, while the payment law has a positive residual on every test.
      * **`eulerRaw`**, **`eulerCross`**, **`eulerRaw_sub_eulerRaw_eulerStep`**,
        **`eulerPayment_eq_raw_sub_cross`**, **`eulerRaw_le`**, **`eulerRaw_eq`**,
        **`primeEulerList`**, **`prime_eulerRaw_le`** — the coherent decomposition of the
        first-power charge. The raw charge of a family of lags differs from its sequential
        payment by an explicit **cross-charge**: each earlier lag read at the ratio lag
        `a_k − a_j` and the product lag `a_k + a_j` of the pair, in the ledger transformed by its
        predecessors. With the residual identity this is the exact decomposition
        `Σ_k w_k A(a_k) = A(0) − ∫(comb F)² + cross`, hence
        `Σ_k w_k A(a_k) ≤ A(0) + cross` for any admissible family, and at prime-power lags with
        the Euler weights `Λ(n)/√n` the cross terms sit exactly at the ratio and product
        incidences of the pairs — the coherent subtraction asked for by AIP topic 8, with the
        reduced cost side of mechanism 47 as its left-hand side.
      * **`spectralDensity`**, **`integrable_spectralDensity`**,
        **`autoCorrelation_eq_integral_spectral`**, **`lagSymbol`**,
        **`eulerRaw_eq_integral_symbol`**, **`eulerRaw_le_symbol_bound`** — the spectral form of
        the lag ledger. A `C¹` compactly supported test has `|F̂(ξ)| = O(1/|ξ|)`, so its spectral
        density `|F̂|²` is integrable and Fourier inversion applies: the Gram kernel is the cosine
        transform of that nonnegative density, `A(t) = ∫ cos(2πtξ)|F̂(ξ)|²dξ`. Hence every
        weighted lag charge is the pairing of the family's **symbol**
        `S(ξ) = Σ_j w_j cos(2πa_jξ)` against the density, and the charge per unit mass is at most
        `sup_ξ S(ξ)`. This is the exact form of the resonance phenomenon of the tower laws — a
        resonant train concentrates its density where the symbol peaks, and no test does better —
        and it puts the Dirichlet-polynomial symbol of the prime band on an unconditional footing.
      * **`fourier_shift`**, **`fourier_ofReal_eulerFactorFun`**,
        **`spectralDensity_eulerFactorFun`**, **`eulerMultiplier`**,
        **`eulerMultiplier_nonneg`**, **`spectralDensity_eulerComb`**,
        **`eulerPayment_eq_integral_multiplier`** — the comb acts diagonally in frequency. A comb
        factor multiplies `F̂` by `c(1 − λe^{2πiaξ})`, hence the spectral density by
        `1 − w cos(2πaξ)`; an iterated comb multiplies it by the product of those factors, and the
        payment is the deficit of that product: `Σ_j w_j A_{j−1}(a_j) = ∫(1 − ∏_j(1 − w_j
        cos(2πa_jξ)))|F̂(ξ)|²dξ`. The admissibility ceiling `w ≤ 1` is exactly nonnegativity of
        the multiplier, so the payment law holds for the structural reason that a nonnegative
        multiplier cannot remove more than the whole mass — and the residual is the mass the
        multiplier keeps.
      * **`norm_exp_mul_I_sub_le`**, **`norm_fourier_sub_le`**,
        **`abs_spectralDensity_sub_le`**, **`setIntegral_spectralDensity_le`**,
        **`mass_outside_window_ge`** — how sharply a test can concentrate in frequency. The
        transform of a test supported in `[−r, r]` is Lipschitz with constant `2πr‖F‖₁`, hence its
        spectral density is Lipschitz with constant `4πr‖F‖₁²`. A window of half-width `δ`
        therefore holds at most `2δ(g(ξ₀) + 4πr‖F‖₁²δ)` of the mass and the rest stays outside:
        an aperture-`r` test cannot concentrate its density on a scale finer than `≍ 1/r`. This
        is the quantitative limit of resonance — a test tracks a peak of the symbol only if the
        peak is wider than the reciprocal aperture — and it is the missing ingredient for scoring
        the charge of a prime band against its symbol.
      * **`coshCosKernel`**, **`integral_cosh_mul_cos`**, **`abs_coshCosKernel_le`**,
        **`integral_cosh_mul_autoCorrelation_spectral`**, **`prime_polar_balance_spectral`** —
        the polar side in spectral coordinates. The polar comparison `∫_0^T cosh(s/2)A(s)ds` is
        also a pairing against the spectral density, with symbol the finite cosine moment
        `K_T(b) = ∫_0^T cosh(s/2)cos(bs)ds = (½sinh(T/2)cos(bT) + b cosh(T/2)sin(bT))/(¼+b²)`,
        bounded by `2sinh(T/2) + cosh(T/2)` uniformly in `b` (Fubini against a finite-measure
        window). Hence the whole prime–polar balance of the ledger is one integral of the signed
        symbol against a nonnegative density:
        `Σ_j w_j A(a_j) − 2∫_0^T cosh(s/2)A(s)ds = ∫ (S(ξ) − 2K_T(2πξ))|F̂(ξ)|²dξ`. The sign
        question of the balance becomes the sign of an explicit function of frequency, weighted
        by a density the test may choose but cannot concentrate below scale `1/r`.
      * **`coshCosKernel_nonneg`**, **`coshCosKernel_neg`**, **`fourier_ofReal_zero_of_odd`**,
        **`spectralDensity_le_sq_of_odd`**, **`setIntegral_spectralDensity_le_of_odd`**,
        **`coshCosKernel_nonneg_band`**, **`setIntegral_spectralDensity_payingBand_le`** — where
        the pole pays, and whether a test can go there. On a finite lag window the polar symbol
        is not of one sign: it is nonnegative up to the first quarter period, so for the window
        `T = 2r` the pole pays only on the band `|ξ| ≤ 1/(8r)`, and at three quarters of a period
        it is strictly negative, `K_T(3π/(2T)) = −(3π/(2T))cosh(T/2)/(¼+(3π/(2T))²) < 0`: there
        the pole adds to the cost. An odd test cannot exploit the paying band — its transform
        vanishes at the origin, so its density is `≤ 4π²r²‖F‖₁²ξ²` and the mass it can place in
        the band is at most `π²‖F‖₁²/(192r)`, cubically small in the band width.
      * **`primeSymbol`**, **`sum_prime_eq_integral_primeSymbol`**,
        **`integral_Ioi_cosh_mul_autoCorrelation_spectral`**,
        **`chebyshev_pairing_eq_spectral`** — the Chebyshev defect and the spectral density are
        two readings of one functional. The prime side is its own symbol against the density, the
        polar side over the whole half-line is `K_{2r}` against the density, and the lag Abel
        identity equates their difference with the signed pairing of the Chebyshev defect against
        the derivative of the lag weight. Hence
        `∫_{s>0} E(s)·(d/ds)(2e^{−s/2}A(s))ds = 2∫ (primeSymbol_N(ξ) − 2K_{2r}(2πξ))|F̂(ξ)|²dξ`:
        the estimate the programme needs — a signed pairing with an unbounded defect — is exactly
        a frequency integral of an explicit signed symbol against a nonnegative density, whose
        concentration is limited by the aperture.
      * **`integral_spectralDensity_eq_mass`**, **`coshCosKernel_zero`**,
        **`chebyshev_pairing_ge_of_symbol_ge`**,
        **`chebyshev_pairing_nonneg_of_symbol_nonneg`**, **`symbol_zero_eq`** — the symbol
        criterion. The spectral density is nonnegative with total mass the test's energy, so a
        pointwise floor `c` on the signed symbol gives `pairing ≥ 2c·A(0)` for **every** test: the
        sign of the prime–polar part of the ledger, a condition quantified over all tests,
        reduces to the sign of one explicit elementary function of frequency. At the origin that
        function is the Chebyshev–Mertens comparison `Σ_{n≤N} Λ(n)/√n − 4 sinh r`, so the
        criterion's zero-frequency slice is exactly the PNT-level balance the programme already
        identifies as the obstruction.
- [ ] 3 → 4  publication-ready

## Contribution index

The 367 headline results of this card, in the order the card states them. Every name is a
declaration of `formal/GaloisForLFunctions/ArithmeticIncidencePositivity/LagChebyshevAbelSummation.lean`;
the file compiles with `lake --old env lean` and its capstones print the three standard axioms.

Entries are tagged by a mechanical rule, so the count can be reproduced from the card and the
module alone: *(definition)* a `def`, *(algebra)* a theorem whose whole proof is at most three
lines of rewriting or arithmetic closers, *(classical)* a classical fact of analytic number
theory restated in the ledger language. These three classes are infrastructure, not
contributions of the field, and are excluded.

**Field contributions: 294.**  Excluded: 44 definitions, 11 algebraic restatements, 18 classical.

1. `testBalance`
2. `testBalance_poleplane`
3. `testBalance_odd`
4. `sum_weight_sub_polar_eq_defect`
5. `eq_of_lagPrefix_eq`
6. `abs_lagTestWeight_deriv_le`
7. `autoCorrelation_le_chainConstant`
8. `shiftDefect_ge_quadratic`
9. `sum_atom_mul_autoCorrelation_le_ladder`
10. `integral_chebyshev_mul_deriv_add_const`
11. `sum_weight_band_sub_polar_eq_increment`
12. `integral_affine_mul_deriv_deriv_eq`
13. `sum_vonMangoldt_band_eq_receiver_curvature`
14. `chebyshevTwoPoleDefect_le_liouville`
15. `abs_residue_le_centred`
16. `abs_residue_band_le_affine`
17. `testBalance_band_receiver_curvature`
18. `autoCorrelation_rightPart_le_chainConstant`
19. `sum_gram_le_ladder`
20. `one_div_le_log_sub_log`
21. `autoCorrelation_rightPart_le_half_of_annulus`
22. `sub_div_le_log_sub_log`
23. `abs_sub_le_of_abs_log_sub_le`
24. `card_lagClose_le`
25. `sum_mul_mul_le_rowSum`
26. `two_mul_sum_lag_le_schur`
27. `rowSum_le_bandwidth`
28. `two_mul_sum_lag_le_of_schurConstant`
29. `log_sub_log_eq_iff`
30. `autoCorrelation_rightPart_ratio_eq`
31. `ratio_param`
32. `card_ratioFirsts_le`
33. `sum_lag_le_sqrt`
34. `autoCorrelation_dilate`
35. `sum_gram_eq_integral_sq`
36. `sum_gram_offDiag_ge`
37. `two_mul_displacement_eq`
38. `displacement_add_le`
39. `displacement_two_pow_le`
40. `autoCorrelation_le_of_two_pow`
41. `crossAggregate_eq_meanSquare`
42. `crossAggregate_ge`
43. `crossAggregate_le`
44. `sourceOfPrefix` *(definition)*
45. `existsUnique_source_of_prefix`
46. `ledger_difference_eq`
47. `index_eq_prefix_sub`
48. `integral_step_mul_deriv_eq`
49. `ledger_separates_singleIndex`
50. `sum_weight_dilate_sub_polar_eq_defect`
51. `ledger_mono`
52. `sum_lag_eq_integral_primeField`
53. `two_mul_sum_lag_le_aggregate`
54. `poleplane_eq_moment_mul`
55. `poleplane_eq_zero_iff` *(algebra)*
56. `poleplane_odd`
57. `testBalance_poleFree`
58. `lagChebyshev_eq_log_two`
59. `criticalScalePrefix_first_cell`
60. `criticalScalePrefix_second_cell`
61. `criticalScalePrefix_succ`
62. `criticalScalePrefix_log_natCast_succ`
63. `criticalScalePrefix_on_cell`
64. `hasDerivAt_criticalScalePrefix_of_mem_cell`
65. `poleWeightAt` *(definition)*
66. `sum_weight_sub_polarAt_eq_defect`
67. `autoCorrelation_sub`
68. `abs_autoCorrelation_sub_le`
69. `two_mul_displacement_le`
70. `abs_autoCorrelation_sub_le_lipschitz`
71. `sum_lag_eq_of_horizon`
72. `sum_cross_gram_eq_integral`
73. `abs_sum_cross_gram_le`
74. `ledgerField` *(definition)*
75. `testBalance_field`
76. `displacement_ge_min`
77. `fold_defect_ge`
78. `autoCorrelation_le_min`
79. `window_coupling_le`
80. `window_degree_lt`
81. `idealSource` *(definition)*
82. `abs_lagSourceDefect_idealSource_le`
83. `abs_ledger_idealSource_le`
84. `ledger_vonMangoldt_sub_ideal`
85. `sourceScalePrefix` *(definition)*
86. `sum_weight_sub_polar_tailWeight`
87. `integral_autoCorrelation`
88. `integral_autoCorrelation_odd` *(algebra)*
89. `exists_autoCorrelation_neg`
90. `autoCorrelation_ge_half_of_mem`
91. `integral_compl_autoCorrelation_le`
92. `poleWeightAt_half_cell_ge`
93. `defect_half_cell_lower_bound`
94. `abs_lagSourceDefectAt_idealSourceAt_le`
95. `lagPrefix_jump`
96. `defect_ge_of_atom`
97. `exists_abs_chebyshevTwoPoleDefect_gt`
98. `integral_calibration_mul_deriv`
99. `sum_weight_sub_calibration_eq_defect`
100. `oscWeight` *(definition)*
101. `sum_weight_sub_oscPolar_eq_defect`
102. `leftPart_eq_neg_rightPart_neg`
103. `autoCorrelation_eq_neg_conv`
104. `autoCorrelation_nonpos_of_odd_nonneg`
105. `sum_lag_le_truncated`
106. `allOnes` *(definition)*
107. `lagSourceDefect_allOnes` *(algebra)*
108. `autoCorrelation_eq_conv`
109. `autoCorrelation_eq_zero_abs`
110. `aggregate_le_bandwidth`
111. `aggregate_dyadic_le`
112. `aggregate_dyadic_diagonal`
113. `genPrefix` *(definition)*
114. `sum_gen_mul_eq_neg_integral`
115. `sum_gen_sub_calibration_eq_defect`
116. `geoWeight` *(definition)*
117. `geo_defect_half_cell`
118. `geo_reading_gap`
119. `fourier_ofReal_autoCorrelation_eq`
120. `fourier_ofReal_autoCorrelation_sq`
121. `integral_exp_mul_autoCorrelation`
122. `integral_Ioi_cosh_mul_autoCorrelation`
123. `expMoment_odd`
124. `integral_Ioi_cosh_mul_autoCorrelation_odd`
125. `lagTestWeightAt` *(definition)*
126. `testBalanceAt`
127. `testBalanceAt_odd`
128. `coshMoment` *(definition)*
129. `poleTerm_eq_moment_mul`
130. `capacity_iff`
131. `capacity_odd_iff`
132. `moebiusSource` *(definition)*
133. `lagMertens` *(definition)*
134. `sum_moebius_sub_unit_eq_defect`
135. `abs_lagMertens_le`
136. `twistSource` *(definition)*
137. `sum_twist_sub_unit_eq_defect`
138. `thetaSource` *(definition)*
139. `sum_theta_sub_polar_eq_defect`
140. `genRampSum` *(definition)*
141. `sum_weight_mul_eq_integral_rampSum`
142. `sum_weight_sub_polar_eq_rampDefect`
143. `sourceScalePrefix_eq`
144. `sum_weight_sub_polar_eq_sourceScalePrefix`
145. `integral_secondPrimitive_mul_deriv2`
146. `sum_weight_sub_calibration_eq_rampDefect`
147. `mertensScalePrefix` *(definition)*
148. `mertensScalePrefix_eq`
149. `sum_moebius_sub_unit_eq_mertensScalePrefix`
150. `pairCorrelation` *(definition)*
151. `autoCorrelation_add`
152. `sum_pair_gram_eq_integral`
153. `abs_sum_pair_gram_le`
154. `logSource` *(definition)*
155. `logWeight` *(definition)*
156. `sum_log_sub_doublePolar_eq_defect`
157. `progression_gram_nonneg`
158. `progression_gram_le`
159. `progression_offdiag_le`
160. `antiDisplacement` *(definition)*
161. `displacement_two_mul_le_antiDisplacement`
162. `antiDisplacement_ge`
163. `autoCorrelation_ratio_le`
164. `autoCorrelation_ratio_le_of_ne`
165. `crossAggregate_le_gap`
166. `sum_lag_vonMangoldt_eq_zero`
167. `testBalance_firstWindow`
168. `sum_lag_vonMangoldt_firstAtom`
169. `testBalance_firstAtom`
170. `residue_firstAtom_le`
171. `sum_lag_vonMangoldt_secondWindow`
172. `sum_lag_vonMangoldt_thirdWindow`
173. `scaledTwoPoleWeight` *(definition)*
174. `apSource` *(definition)*
175. `sum_ap_sub_scaledPolar_eq_defect`
176. `sum_apSource_eq`
177. `sum_lagPrefix_ap`
178. `sum_defect_ap`
179. `pairCalibration` *(definition)*
180. `sum_shiftedPair_sub_pairPolar_eq_defect`
181. `integral_halves_add`
182. `integral_leftPart_sq_eq_half`
183. `sum_lag_le_sqrt_odd`
184. `tendsto_chebyshevTwoPoleDefect_div_exp_iff`
185. `tendsto_mertensDefect_div_exp_iff`
186. `abs_defect_sourceOfPrefix_le`
187. `cell_increment_le_two_mul_defect`
188. `poleWeightAt_cell_increment_le`
189. `multiPoleWeight` *(definition)*
190. `abs_defect_multiPole_le`
191. `abs_defect_reflectedPole_le`
192. `logWeight_half_cell_increment_ge`
193. `defect_logWeight_ge`
194. `gen_cell_increment_le_two_mul_defect`
195. `defect_ge_of_gap`
196. `geoLags_defect_ge`
197. `exists_lag_of_defect_le`
198. `card_ge_of_defect_le`
199. `card_filter_mul_le_of_defect`
200. `min_atom_le_of_defect`
201. `card_ge_of_defect_le_gen`
202. `card_ge_of_id_defect_le`
203. `card_ge_of_poleAt_defect_le`
204. `gen_cell_increment_le_two_mul_defect_supp`
205. `card_support_ge_of_defect_le`
206. `card_primePowers_ge_of_chebyshev_defect_le`
207. `gram_split_row`
208. `gram_row_le_half`
209. `midpointSource` *(definition)*
210. `abs_defect_midpointSource_le`
211. `gapSource` *(definition)*
212. `genPrefix_gapSource`
213. `abs_defect_gapSource_le`
214. `genTestBalance`
215. `lagField` *(definition)*
216. `sum_gen_lag_eq_integral_field`
217. `genPrefix_jump`
218. `two_mul_sum_gen_lag_le`
219. `genTestBalanceAt`
220. `testBalance_receiver`
221. `testBalance_source`
222. `mertensTestBalance`
223. `testBalance_source_sub`
224. `abs_testBalance_source_le`
225. `lagSourceDefect_eq_twoPoleWeight_of_lt_log_two`
226. `testBalance_source_truncates`
227. `primeSide_add`
228. `poleplane_add` *(algebra)*
229. `expMomentNeg_eq_zero_add` *(algebra)*
230. `autoCorrelation_smul`
231. `poleplane_translate` *(algebra)*
232. `weil_dilation_covariance`
233. `primeSide_translate`
234. `autoCorrelation_reflect`
235. `poleplane_reflect` *(algebra)*
236. `testBalance_source_congr`
237. `evenPart` *(definition)*
238. `sym_pairCorrelation_even_odd`
239. `autoCorrelation_even_odd_split`
240. `poleplane_even_odd`
241. `weilForm_even_odd_split`
242. `weilForm` *(definition)*
243. `weilForm_split`
244. `weilForm_nonneg_iff`
245. `residue_even_odd_split`
246. `testBalance_vonMangoldt_sub_liouville`
247. `card_window_ge_of_defect_le`
248. `lagPrefix_eq_of_atomfree`
249. `defect_ge_of_atomfree`
250. `chebyshev_defect_ge_of_primePower_free`
251. `exists_primePower_of_chebyshev_defect_le`
252. `defect_poleAt_ge_of_atomfree`
253. `chebyshevTwoPoleDefect_log_two`
254. `chebyshevTwoPoleDefect_log_three`
255. `criticalScalePrefix_pos_first_cell`
256. `criticalScalePrefix_pos_second_cell`
257. `criticalScalePrefix_pos_on_cell`
258. `criticalScalePrefix_succ_pos` *(algebra)*
259. `criticalScalePrefix_succ_pos_of_psi`
260. `criticalScalePrefix_succ_ge`
261. `criticalScalePrefix_le_nat`
262. `criticalScalePrefix_ge_sub`
263. `lagChebyshev_le`
264. `criticalScalePrefix_le_exp`
265. `criticalScalePrefix_ge_explicit`
266. `squarefreeSource` *(definition)*
267. `higherPowerSource` *(definition)*
268. `sum_higherPower_sub_halfPolar_eq_defect`
269. `testBalanceAt_source`
270. `lagPrefix_add` *(algebra)*
271. `defect_split_calibration` *(algebra)*
272. `chebyshevTwoPoleDefect_split`
273. `primeSide_source_add` *(algebra)*
274. `primeSide_higherPower_eq_zero`
275. `primeSide_vonMangoldt_eq_theta`
276. `integrableOn_Ioi_lagSourceDefectAt_mul_deriv`
277. `abs_testBalanceAt_source_le`
278. `lagSourceDefectAt_vonMangoldt_ge`
279. `poleWeightAt_dilate`
280. `lagSourceDefectAt_sub_lagSourceDefect`
281. `abs_poleWeight_sub_le_of_two_poles`
282. `abs_window_mass_sub_le`
283. `abs_sum_Ioc_sub_le`
284. `dconv` *(classical)*
285. `sum_Icc_dconv` *(classical)*
286. `lagPrefix_dconv` *(classical)*
287. `sum_Icc_dconv_mul` *(classical)*
288. `sum_lag_dconv` *(classical)*
289. `abs_lagPrefix_dconv_sub_le` *(classical)*
290. `unitSource` *(classical)*
291. `fullMoebius` *(classical)*
292. `abs_lagPrefix_unitSource_sub_exp_le` *(classical)*
293. `abs_lagPrefix_dconv_unitSource_sub_le` *(classical)*
294. `lagPrefix_log_eq_log_factorial` *(classical)*
295. `sum_fullMoebius_floor` *(classical)*
296. `abs_sum_fullMoebius_div_le_one` *(classical)*
297. `lagChebyshev_eq_sum_fullMoebius_log_factorial` *(classical)*
298. `lagPrefix_eq_sum_fullMoebius_dconv` *(classical)*
299. `lagPrefix_fullMoebius` *(classical)*
300. `lagPrefix_divisorCount` *(classical)*
301. `abs_lagPrefix_divisorCount_sub_le` *(classical)*
302. `autoCorrelation_eulerFactor`
303. `eulerStep` *(definition)*
304. `exists_autoCorrelation_eulerStep`
305. `eulerLam_spec`
306. `two_mul_div_one_add_sq_le_one`
307. `eulerLedger` *(definition)*
308. `eulerPayment` *(definition)*
309. `eulerLedger_zero_eq`
310. `eulerPayment_le_mass`
311. `two_lag_payment_le`
312. `vonMangoldtAtom_le_one`
313. `eulerPayment_vonMangoldt_le_mass`
314. `eulerComb` *(definition)*
315. `autoCorrelation_eulerComb`
316. `eulerPayment_residual`
317. `eq_zero_of_eq_const_mul_shift`
318. `eulerComb_ne_zero`
319. `integral_sq_pos_of_ne_zero`
320. `eulerPayment_lt_mass`
321. `eulerRaw` *(definition)*
322. `eulerCross` *(definition)*
323. `eulerRaw_sub_eulerRaw_eulerStep`
324. `eulerPayment_eq_raw_sub_cross`
325. `eulerRaw_le`
326. `eulerRaw_eq`
327. `primeEulerList` *(definition)*
328. `prime_eulerRaw_le`
329. `spectralDensity` *(definition)*
330. `integrable_spectralDensity`
331. `autoCorrelation_eq_integral_spectral`
332. `lagSymbol` *(definition)*
333. `eulerRaw_eq_integral_symbol`
334. `eulerRaw_le_symbol_bound`
335. `fourier_shift`
336. `fourier_ofReal_eulerFactorFun`
337. `spectralDensity_eulerFactorFun`
338. `eulerMultiplier` *(definition)*
339. `eulerMultiplier_nonneg`
340. `spectralDensity_eulerComb`
341. `eulerPayment_eq_integral_multiplier`
342. `norm_exp_mul_I_sub_le`
343. `norm_fourier_sub_le`
344. `abs_spectralDensity_sub_le`
345. `setIntegral_spectralDensity_le`
346. `mass_outside_window_ge`
347. `coshCosKernel` *(definition)*
348. `integral_cosh_mul_cos`
349. `abs_coshCosKernel_le`
350. `integral_cosh_mul_autoCorrelation_spectral`
351. `prime_polar_balance_spectral`
352. `coshCosKernel_nonneg`
353. `coshCosKernel_neg`
354. `fourier_ofReal_zero_of_odd`
355. `spectralDensity_le_sq_of_odd`
356. `setIntegral_spectralDensity_le_of_odd`
357. `coshCosKernel_nonneg_band`
358. `setIntegral_spectralDensity_payingBand_le`
359. `primeSymbol` *(definition)*
360. `sum_prime_eq_integral_primeSymbol`
361. `integral_Ioi_cosh_mul_autoCorrelation_spectral`
362. `chebyshev_pairing_eq_spectral`
363. `integral_spectralDensity_eq_mass`
364. `coshCosKernel_zero`
365. `chebyshev_pairing_ge_of_symbol_ge`
366. `chebyshev_pairing_nonneg_of_symbol_nonneg`
367. `symbol_zero_eq`
## Note on the Lean route

The module depends on `Mathlib` alone, so it is independent of the `ArithmeticCriticalityTheory`
and `RHTower` olean cones, which are intermittently unloadable while the `RHTower/ThetaCusp/` and
`HTGeometry/PolynomialODE/` module moves are completed. Steps 4–5 do need
`ArithmeticCriticalityTheory` (`fullZeroForm`, `markovEnergy`, `oddPoleMoment`, `evenPoleMoment`)
and the ledger objects, and are queued behind that cone.

## Log
- 2026-10-22 — created; paper proof complete; steps 1–3 formalized and compiled.
- 2026-10-23 — Euler comb ledger added (AIP topic 7); contribution index introduced and verified against the module.
- 2026-10-23 — residual and strictness of the Euler comb payment; index re-audited and classical support marked.
- 2026-10-23 — coherent decomposition of the first-power charge (ratio–product cross-charge); index tagged by the mechanical criteria rule.
- 2026-10-23 — spectral form of the lag ledger: density integrability, cosine-transform identity, symbol capacity bound.
- 2026-10-23 — the comb diagonalised in frequency: spectral multiplier, payment as multiplier deficit.
- 2026-10-23 — frequency anti-concentration: Lipschitz spectral density, window-mass bound, resonance limit at scale 1/r.
- 2026-10-23 — polar side in spectral coordinates; prime–polar balance as one signed-symbol integral.
- 2026-10-23 — sign law of the polar symbol and the inaccessibility of its paying band to odd tests.
- 2026-10-23 — bridge: the Chebyshev-defect pairing equals the signed-symbol spectral integral.
- 2026-10-23 — symbol criterion: a pointwise symbol floor bounds the pairing on every test.
