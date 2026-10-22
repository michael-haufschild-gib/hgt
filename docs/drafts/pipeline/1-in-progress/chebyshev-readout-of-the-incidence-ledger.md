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
- [ ] 3 → 4  publication-ready

## Note on the Lean route

The module depends on `Mathlib` alone, so it is independent of the `ArithmeticCriticalityTheory`
and `RHTower` olean cones, which are intermittently unloadable while the `RHTower/ThetaCusp/` and
`HTGeometry/PolynomialODE/` module moves are completed. Steps 4–5 do need
`ArithmeticCriticalityTheory` (`fullZeroForm`, `markovEnergy`, `oddPoleMoment`, `evenPoleMoment`)
and the ledger objects, and are queued behind that cone.

## Log
- 2026-10-22 — created; paper proof complete; steps 1–3 formalized and compiled.
