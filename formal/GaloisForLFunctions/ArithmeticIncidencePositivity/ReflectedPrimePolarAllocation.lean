import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeTowerLedgerReduction
import GaloisForLFunctions.ArithmeticIncidencePositivity.LagChebyshevAbelSummation
import GaloisForLFunctions.ArithmeticIncidencePositivity.EdgeTentLogarithmicCapacity
import GaloisForLFunctions.HTGeometry.CompactSupportIntegrationByParts
import GaloisForLFunctions.SquareRootThreshold.TheIncidenceLedgerGradedByTheZeroWidth

/-!
# Full reflected-prime/polar allocation across arbitrary tests

In the global incidence ledger (`fullZeroForm_eq_incidenceLedger`), the full zero form of an odd
test `F ∈ C²_c(ℝ)` supported in `[−r, r]` at plateau radius `R > r` is

    Ẑ(F) = surplusPool + crossingPotentialTerm + Σ_n evenStripGain_n − Σ_n oddStripCost_n
           + gaugeRemainder − poleCharge.

Restricted-horizon certificates (`GlobalSharedSurplusAllocation`, `FirstPrimeWindowPositivity`)
decouple the reflected-prime and polar terms into two separate coercivity estimates: paying
`Σ_n oddStripCost_n` from the archimedean surplus pool `stripBoxEnergy F 0 r`, and paying
`poleCharge F` from the crossing potential via the restricted-horizon bound
`poleCharge F ≤ (R³/3) cosh²(R/2) ∫ F²` (`R ≤ 3/5`).

This module proves two unconditional results:

1. **Restricted-horizon coercivity does not supply reflected-prime/polar allocation across arbitrary
   tests.**
   * On the odd edge tent `F = edgeTentOdd r ε` (`0 < ε ≤ 1`, `ε < r`), the integrand
     `F(x) sinh(x/2)` is nonnegative on all of `ℝ` and carries
     `oddPoleMoment F ≥ (ε²/8) sinh((r − ε)/2)`, hence
     `poleCharge F ≥ (ε⁴/32) sinh²((r − ε)/2) ≍ ε⁴ e^r` (`poleCharge_edgeTentOdd_ge`), whereas
     `stripBoxEnergy F 0 r ≤ 3ε²r`. Thus for every fixed `ε ∈ (0, 1]` and every linear budget `C r`,
     `poleCharge F` eventually exceeds `stripBoxEnergy F 0 r + C r`
     (`eventually_stripBoxEnergy_add_linear_lt_poleCharge_edgeTentOdd`).
   * Whenever `0 < ε ≤ log 2` and `ε < r`, the shift product `F(x) F(x + L)` of `F = edgeTentOdd r ε`
     is nonpositive for every `L ≥ ε` and vanishes identically for **every** `L ∈ [ε, 2(r − ε)]`
     (including all sub-half-width shifts `log n < r`, not only the thin band `r ≤ log n ≤ 2(r − ε)`).
     Consequently `evenStripGain F r n = oddStripCost F r n` for every `n ≥ 2` with
     `log n ≤ 2(r − ε)`, and `oddStripCost F r n ≤ evenStripGain F r n` for every `n ∈ relevantShifts r`
     (`oddStripCost_edgeTentOdd_le_evenStripGain`, `sum_oddStripCost_edgeTentOdd_le_sum_evenStripGain`).
     On edge tests the net prime charge `Σ (oddStripCost − evenStripGain) ≤ 0` is a net gain that
     directly opposes the exponentially growing `poleCharge F` in the light cone `(2(r − ε), 2r)`.

2. **Unconditional full reflected-prime/polar allocation across arbitrary tests.**
   * Each favorable strip gain `evenStripGain F r n = 2 Λ(n)/√n · stripMass F r (log n)` is allocated
     against the two-pole hyperbolic density `4 cosh(s/2)` across all relevant shifts, with the
     two-pole Chebyshev defect `E(s) = e^s + s − 1 − ψ(e^s)` as the exact residue
     (`sum_evenStripGain_eq_polar_add_chebyshev`).
   * The joint **reflected-prime/polar cost**
     `reflectedPrimePolarCost F r = Σ_n oddStripCost_n − Σ_n evenStripGain_n + poleCharge F`
     combines the reflected prime charges and the pole charge into one channel whose leading
     rate-`1` prime and polar terms cancel identically across all odd compactly supported tests:
     - in correlation form (`reflectedPrimePolarCost_eq_prime_sub_polar_autoCorrelation`), it is
       `Σ_{n ∈ relevantShifts r} 2 Λ(n)/√n · A(log n) − ∫_{s>0} 4 cosh(s/2) A(s) ds`;
     - at first order for every odd `F ∈ C¹_c(ℝ)` supported in `[−r, r]`
       (`reflectedPrimePolarCost_eq_chebyshevTwoPoleDefect`), it equals
       `∫_{s>0} E(s) · 2 e^{−s/2} (A'(s) − ½ A(s)) ds`, supported on `(0, 2r]`;
     - at second order for every odd `F ∈ C²_c(ℝ)` supported in `[−r, r]`
       (`reflectedPrimePolarCost_eq_criticalScalePrefix`), it equals
       `−∫_{s>0} (D(s) + s²/2 − s) (lagTestWeight F)''(s) ds`, where
       `D(s) = ∫_0^s (e^u − ψ(e^u)) du` is the critical-scale cancellation functional.
   * Substituting this joint balance into the incidence ledger (`fullZeroForm_eq_reflectedPrimePolarLedger`,
     `fullZeroForm_nonneg_of_reflectedPrimePolarAllocation`) replaces the separate restricted-horizon
     conditions by a single all-aperture allocation of the Chebyshev-defect pairing against
     `surplusPool + crossingPotentialTerm + gaugeRemainder`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ## Part I: Why restricted-horizon coercivity fails on arbitrary tests -/

/-! ### Full sub-light-cone cancellation and light-cone sign of the edge tent -/

/-- Whenever `ε ≤ L` and `ε ≤ r`, neither the positive tent `(r − ε, r)` nor the negative tent
`(−r, −(r − ε))` can meet its own `L`-translate, and the positive tent cannot meet the negative
tent's `L`-translate. Every nonzero point of `edgeTentOdd r ε x * edgeTentOdd r ε (x + L)`
therefore pairs the negative tent at `x` with the positive tent at `x + L`. -/
theorem mem_of_edgeTentOdd_mul_shift_ne_zero {r ε L x : ℝ} (hεr : ε ≤ r)
    (hεL : ε ≤ L) (h : edgeTentOdd r ε x * edgeTentOdd r ε (x + L) ≠ 0) :
    (r - ε < -x ∧ -x < r) ∧ (r - ε < x + L ∧ x + L < r) := by
  have h1 := mem_of_edgeTentOdd_ne_zero (left_ne_zero_of_mul h)
  have h2 := mem_of_edgeTentOdd_ne_zero (right_ne_zero_of_mul h)
  rcases h1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases h2 with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · exfalso; linarith
  · exfalso; linarith
  · exact ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
  · exfalso; linarith

/-- **Full sub-light-cone vanishing of the edge tent.** For **every** shift `L` with
`0 < ε ≤ L ≤ 2(r − ε)` (including all sub-half-width shifts `L < r`, not only `r ≤ L`), the shift
product `edgeTentOdd r ε x * edgeTentOdd r ε (x + L)` vanishes identically on `ℝ`. -/
theorem edgeTentOdd_mul_shift_eq_zero_of_le {r ε L : ℝ} (hε0 : 0 < ε) (hεL : ε ≤ L)
    (hL : L ≤ 2 * (r - ε)) (x : ℝ) :
    edgeTentOdd r ε x * edgeTentOdd r ε (x + L) = 0 := by
  by_contra h
  have hεr : ε ≤ r := by linarith
  obtain ⟨⟨a1, _⟩, ⟨b1, _⟩⟩ := mem_of_edgeTentOdd_mul_shift_ne_zero hεr hεL h
  linarith

/-- **Pointwise nonpositivity of the edge-tent shift product across all lags `L ≥ ε`.** For every
`L ≥ ε` (including the light cone `2(r − ε) < L < 2r`), `edgeTentOdd r ε x * edgeTentOdd r ε (x + L) ≤ 0`
at every point `x ∈ ℝ`, because the left factor is nonpositive on `(−r, −(r − ε))` while the right
factor is nonnegative on `(r − ε, r)`. -/
theorem edgeTentOdd_mul_shift_nonpos {r ε L : ℝ} (hεr : ε < r) (hεL : ε ≤ L)
    (x : ℝ) :
    edgeTentOdd r ε x * edgeTentOdd r ε (x + L) ≤ 0 := by
  by_cases h : edgeTentOdd r ε x * edgeTentOdd r ε (x + L) = 0
  · rw [h]
  · obtain ⟨⟨a1, _⟩, ⟨b1, _⟩⟩ := mem_of_edgeTentOdd_mul_shift_ne_zero hεr.le hεL h
    have hxneg : 0 ≤ -x := by linarith
    have hxlpos : 0 ≤ x + L := by linarith
    have hleft : edgeTentOdd r ε x = -edgeTent r ε (-x) := by
      have h1 := edgeTentOdd_odd r ε (-x)
      rw [neg_neg, edgeTentOdd_of_nonneg hεr hxneg] at h1
      exact h1
    have hright : edgeTentOdd r ε (x + L) = edgeTent r ε (x + L) :=
      edgeTentOdd_of_nonneg hεr hxlpos
    rw [hleft, hright]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (edgeTent_nonneg r ε (-x)))
      (edgeTent_nonneg r ε (x + L))

/-- **Exact odd–even cancellation on the edge tent for all sub-light-cone shifts.** Whenever
`0 < ε ≤ log 2`, `ε < r`, and `n ≥ 2` satisfies `log n ≤ 2(r − ε)`, the autocorrelation at `log n`
vanishes and `evenStripGain` equals `oddStripCost` at `n` — even for small shifts `log n < r`. -/
theorem evenStripGain_edgeTentOdd_eq_oddStripCost_of_le {r ε : ℝ} {n : ℕ}
    (hε0 : 0 < ε) (hε2 : ε ≤ Real.log 2) (hεr : ε < r) (hn2 : 2 ≤ n)
    (hn : Real.log n ≤ 2 * (r - ε)) :
    autoCorr (edgeTentOdd r ε) (Real.log n) = 0 ∧
      evenStripGain (edgeTentOdd r ε) r n = oddStripCost (edgeTentOdd r ε) r n := by
  have hlog2 : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
  have hεL : ε ≤ Real.log n := hε2.trans hlog2
  have hzero : autoCorr (edgeTentOdd r ε) (Real.log n) = 0 := by
    unfold autoCorr
    simp_rw [edgeTentOdd_mul_shift_eq_zero_of_le hε0 hεL hn, integral_zero]
  refine ⟨hzero, ?_⟩
  have hdiff := evenStripGain_sub_oddStripCost_eq (continuous_edgeTentOdd r ε)
    (edgeTentOdd_odd r ε) (by linarith : 0 ≤ r)
    (fun x hx => edgeTentOdd_eq_zero_of_lt hε0 hεr hx) (by linarith : Real.log n ≤ 2 * r)
  rw [hzero, mul_zero, mul_zero, neg_zero] at hdiff
  linarith

/-- **Every relevant shift is a net gain on the edge tent.** For `0 < ε ≤ log 2` and `ε < r`, every
shift `n ∈ relevantShifts r` satisfies `autoCorr (edgeTentOdd r ε) (log n) ≤ 0` and
`oddStripCost (edgeTentOdd r ε) r n ≤ evenStripGain (edgeTentOdd r ε) r n`. -/
theorem oddStripCost_edgeTentOdd_le_evenStripGain {r ε : ℝ} {n : ℕ}
    (hε0 : 0 < ε) (hε2 : ε ≤ Real.log 2) (hεr : ε < r) (hn : n ∈ relevantShifts r) :
    autoCorr (edgeTentOdd r ε) (Real.log n) ≤ 0 ∧
      oddStripCost (edgeTentOdd r ε) r n ≤ evenStripGain (edgeTentOdd r ε) r n := by
  obtain ⟨hn2, hnlt⟩ := mem_relevantShifts.mp hn
  have hlog2 : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
  have hεL : ε ≤ Real.log n := hε2.trans hlog2
  have hF : Continuous (edgeTentOdd r ε) := continuous_edgeTentOdd r ε
  have hFc : HasCompactSupport (edgeTentOdd r ε) := hasCompactSupport_edgeTentOdd hε0 hεr
  have hint : Integrable fun x => edgeTentOdd r ε x * edgeTentOdd r ε (x + Real.log n) :=
    (hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hA : autoCorr (edgeTentOdd r ε) (Real.log n) ≤ 0 := by
    unfold autoCorr
    have hmono := integral_mono hint (integrable_zero ℝ ℝ volume)
      (edgeTentOdd_mul_shift_nonpos hεr hεL)
    simpa using hmono
  refine ⟨hA, ?_⟩
  have hdiff := evenStripGain_sub_oddStripCost_eq hF (edgeTentOdd_odd r ε) (by linarith : 0 ≤ r)
    (fun x hx => edgeTentOdd_eq_zero_of_lt hε0 hεr hx) hnlt.le
  have hΛ : 0 ≤ vonMangoldtAtom n := vonMangoldtAtom_nonneg n
  nlinarith

/-- Summed over all relevant shifts of the aperture, the odd strip costs of `edgeTentOdd r ε`
never exceed its even strip gains when `0 < ε ≤ log 2`: the prime channel as a whole is nonpositive
in cost, so the light-cone prime atoms cannot be decoupled from the pole charge. -/
theorem sum_oddStripCost_edgeTentOdd_le_sum_evenStripGain {r ε : ℝ}
    (hε0 : 0 < ε) (hε2 : ε ≤ Real.log 2) (hεr : ε < r) :
    (∑ n ∈ relevantShifts r, oddStripCost (edgeTentOdd r ε) r n) ≤
      ∑ n ∈ relevantShifts r, evenStripGain (edgeTentOdd r ε) r n :=
  Finset.sum_le_sum fun _ hn => (oddStripCost_edgeTentOdd_le_evenStripGain hε0 hε2 hεr hn).2

/-! ### Exponential blowup of `poleCharge` vs. archimedean surplus and linear potential budgets -/

/-- The integrand `edgeTentOdd r ε x * sinh(x/2)` of the odd pole moment is nonnegative everywhere
on `ℝ` when `ε < r`. -/
theorem edgeTentOdd_mul_sinh_nonneg {r ε : ℝ} (hεr : ε < r) (x : ℝ) :
    0 ≤ edgeTentOdd r ε x * Real.sinh (x / 2) := by
  rcases le_or_gt 0 x with hx | hx
  · rw [edgeTentOdd_of_nonneg hεr hx]
    exact mul_nonneg (edgeTent_nonneg r ε x) (Real.sinh_nonneg_iff.mpr (by linarith))
  · have hnx : 0 ≤ -x := by linarith
    have hodd : edgeTentOdd r ε x = -edgeTent r ε (-x) := by
      have h1 := edgeTentOdd_odd r ε (-x)
      rw [neg_neg, edgeTentOdd_of_nonneg hεr hnx] at h1
      exact h1
    have hsh : Real.sinh (x / 2) = -Real.sinh (-x / 2) := by
      rw [show x / 2 = -(-x / 2) by ring, Real.sinh_neg]
    rw [hodd, hsh, neg_mul_neg]
    exact mul_nonneg (edgeTent_nonneg r ε (-x)) (Real.sinh_nonneg_iff.mpr (by linarith))

/-- **Lower bound on the odd pole moment of the edge tent.** On the middle half
`[r − 3ε/4, r − ε/4]` of the positive tent, `edgeTentOdd r ε x ≥ ε/4` and
`sinh(x/2) ≥ sinh((r − ε)/2)`, so `oddPoleMoment (edgeTentOdd r ε) ≥ (ε²/8) sinh((r − ε)/2)`. -/
theorem oddPoleMoment_edgeTentOdd_ge {r ε : ℝ} (hε0 : 0 < ε) (hεr : ε < r) :
    ε ^ 2 / 8 * Real.sinh ((r - ε) / 2) ≤ oddPoleMoment (edgeTentOdd r ε) := by
  set F := edgeTentOdd r ε with hFdef
  set a := r - ε + ε / 4 with hadef
  set b := r - ε + 3 * ε / 4 with hbdef
  have hab : a ≤ b := by rw [hadef, hbdef]; linarith
  have hcont : Continuous fun x => F x * Real.sinh (x / 2) :=
    (continuous_edgeTentOdd r ε).mul (Real.continuous_sinh.comp (continuous_id.div_const 2))
  have hint : Integrable fun x => F x * Real.sinh (x / 2) :=
    hcont.integrable_of_hasCompactSupport ((hasCompactSupport_edgeTentOdd hε0 hεr).mul_right)
  have hsub : (∫ x in a..b, F x * Real.sinh (x / 2)) ≤ oddPoleMoment F := by
    rw [oddPoleMoment, intervalIntegral.integral_of_le hab]
    exact setIntegral_le_integral hint (Eventually.of_forall (edgeTentOdd_mul_sinh_nonneg hεr))
  have hlow := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun _ => ε / 4 * Real.sinh ((r - ε) / 2))
    (g := fun x => F x * Real.sinh (x / 2)) hab
    intervalIntegrable_const (hcont.intervalIntegrable a b) fun x hx => by
      have hx0 : 0 ≤ x := by linarith [hx.1]
      have htent : ε / 4 ≤ F x := by
        rw [hFdef, edgeTentOdd_of_nonneg hεr hx0]
        exact edgeTent_ge_quarter hx.1 hx.2
      have hsh : Real.sinh ((r - ε) / 2) ≤ Real.sinh (x / 2) :=
        Real.sinh_le_sinh.mpr (by linarith [hx.1])
      have hsh0 : 0 ≤ Real.sinh ((r - ε) / 2) := Real.sinh_nonneg_iff.mpr (by linarith)
      exact mul_le_mul htent hsh hsh0 (by linarith [hε0])
  rw [intervalIntegral.integral_const, smul_eq_mul] at hlow
  have hlen : (b - a) * (ε / 4 * Real.sinh ((r - ε) / 2)) =
      ε ^ 2 / 8 * Real.sinh ((r - ε) / 2) := by
    rw [hadef, hbdef]; ring
  linarith

/-- **Exponential lower bound on `poleCharge` of the edge tent.** For `0 < ε < r`,
`poleCharge (edgeTentOdd r ε) ≥ (ε⁴/32) sinh²((r − ε)/2)`. -/
theorem poleCharge_edgeTentOdd_ge {r ε : ℝ} (hε0 : 0 < ε) (hεr : ε < r) :
    ε ^ 4 / 32 * Real.sinh ((r - ε) / 2) ^ 2 ≤ poleCharge (edgeTentOdd r ε) := by
  have hm := oddPoleMoment_edgeTentOdd_ge hε0 hεr
  have hsh0 : 0 ≤ Real.sinh ((r - ε) / 2) := Real.sinh_nonneg_iff.mpr (by linarith)
  have hsq : (ε ^ 2 / 8 * Real.sinh ((r - ε) / 2)) ^ 2 ≤ oddPoleMoment (edgeTentOdd r ε) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hm 2
  unfold poleCharge
  nlinarith

/-- For `1 ≤ u`, `exp u / 4 ≤ sinh u`. -/
theorem exp_div_four_le_sinh {u : ℝ} (hu : 1 ≤ u) : Real.exp u / 4 ≤ Real.sinh u := by
  rw [Real.sinh_eq]
  have h1 : (2 : ℝ) ≤ Real.exp u := by
    have := Real.add_one_le_exp u
    linarith
  have h2 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

/-- **Archimedean surplus and linear potential budgets cannot pay `poleCharge` across arbitrary
tests.** For every fixed tent width `ε ∈ (0, 1]` and every constant `C`, eventually as `r → ∞` the
pole charge of `edgeTentOdd r ε` strictly exceeds `stripBoxEnergy (edgeTentOdd r ε) 0 r + C * r`.
Restricted-horizon potential coercivity therefore cannot decouple the pole charge from the
reflected-prime channel at large apertures. -/
theorem eventually_stripBoxEnergy_add_linear_lt_poleCharge_edgeTentOdd
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (C : ℝ) :
    ∀ᶠ r in atTop,
      stripBoxEnergy (edgeTentOdd r ε) 0 r + C * r < poleCharge (edgeTentOdd r ε) := by
  have hexp : Tendsto (fun r : ℝ => Real.exp (r - ε) / (r - ε) ^ 1) atTop atTop :=
    (Real.tendsto_exp_div_pow_atTop 1).comp (tendsto_atTop_add_const_right atTop (-ε) tendsto_id)
  have hev := hexp.eventually (eventually_ge_atTop
    (1024 / ε ^ 4 * (3 * ε ^ 2 + |C| + 1)))
  filter_upwards [hev, eventually_ge_atTop (ε + 2)] with r hr1 hr2
  simp only [pow_one] at hr1
  have hεr : ε < r := by linarith
  have hu : 1 ≤ (r - ε) / 2 := by linarith
  have hsh := exp_div_four_le_sinh hu
  have hsh2 : (Real.exp ((r - ε) / 2) / 4) ^ 2 ≤ Real.sinh ((r - ε) / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsh 2
  have hexp_sq : (Real.exp ((r - ε) / 2) / 4) ^ 2 = Real.exp (r - ε) / 16 := by
    rw [div_pow, ← Real.exp_nat_mul]
    ring_nf
  have hpole := poleCharge_edgeTentOdd_ge hε0 hεr
  have hpole_exp : ε ^ 4 / 512 * Real.exp (r - ε) ≤ poleCharge (edgeTentOdd r ε) := by
    have hmul := mul_le_mul_of_nonneg_left (hexp_sq ▸ hsh2) (show 0 ≤ ε ^ 4 / 32 by positivity)
    linarith
  have hbox := stripBoxEnergy_edgeTent_le hε0 hε1 hεr
  have hr_sub : 2 ≤ r - ε := by linarith
  have hr_le : r ≤ 2 * (r - ε) := by linarith
  rw [le_div_iff₀ (by linarith : 0 < r - ε)] at hr1
  have hε4 : 0 < ε ^ 4 := by positivity
  have hscale : (3 * ε ^ 2 + |C| + 1) * (2 * (r - ε)) ≤ ε ^ 4 / 512 * Real.exp (r - ε) := by
    have h1 := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ ε ^ 4 / 512 by positivity)
    have hcancel : ε ^ 4 / 512 * (1024 / ε ^ 4 * (3 * ε ^ 2 + |C| + 1) * (r - ε)) =
        (3 * ε ^ 2 + |C| + 1) * (2 * (r - ε)) := by
      field_simp
      ring
    linarith
  have hCr : C * r ≤ |C| * (2 * (r - ε)) := by
    calc C * r ≤ |C| * r := mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
      _ ≤ |C| * (2 * (r - ε)) := mul_le_mul_of_nonneg_left hr_le (abs_nonneg C)
  have hbox' : 3 * ε ^ 2 * r ≤ 3 * ε ^ 2 * (2 * (r - ε)) := by nlinarith
  nlinarith

/-- **Simultaneous decoupling failure on edge tests.** For every fixed tent width
`0 < ε ≤ log 2` and every linear budget constant `C`, there exists `r₀` such that for all `r ≥ r₀`
the odd edge tent `F = edgeTentOdd r ε` satisfies:
* `evenStripGain F r n = oddStripCost F r n` for all sub-light-cone shifts `2 ≤ n` with
  `log n ≤ 2(r − ε)`;
* `oddStripCost F r n ≤ evenStripGain F r n` for every `n ∈ relevantShifts r` (so the net prime
  charge `Σ oddStripCost − Σ evenStripGain ≤ 0` is a net gain);
* `stripBoxEnergy F 0 r + C * r < poleCharge F` (the pole charge outgrows the archimedean surplus
  pool plus any linear potential budget). -/
theorem exists_edgeTent_reflectedPrimePolar_decoupling_fails
    {ε : ℝ} (hε0 : 0 < ε) (hε2 : ε ≤ Real.log 2) (C : ℝ) :
    ∃ r₀ : ℝ, ∀ r ≥ r₀,
      (∀ n : ℕ, 2 ≤ n → Real.log n ≤ 2 * (r - ε) →
        evenStripGain (edgeTentOdd r ε) r n = oddStripCost (edgeTentOdd r ε) r n) ∧
      (∀ n ∈ relevantShifts r,
        oddStripCost (edgeTentOdd r ε) r n ≤ evenStripGain (edgeTentOdd r ε) r n) ∧
      (∑ n ∈ relevantShifts r, oddStripCost (edgeTentOdd r ε) r n) ≤
        (∑ n ∈ relevantShifts r, evenStripGain (edgeTentOdd r ε) r n) ∧
      stripBoxEnergy (edgeTentOdd r ε) 0 r + C * r < poleCharge (edgeTentOdd r ε) := by
  have hε1 : ε ≤ 1 := hε2.trans (by linarith [Real.log_two_lt_d9])
  obtain ⟨r₀, hr₀⟩ := Filter.eventually_atTop.mp
    ((eventually_stripBoxEnergy_add_linear_lt_poleCharge_edgeTentOdd hε0 hε1 C).and
      (eventually_ge_atTop (ε + 1)))
  refine ⟨r₀, fun r hr => ?_⟩
  obtain ⟨hpole, hrε⟩ := hr₀ r hr
  have hεr : ε < r := by linarith
  exact ⟨fun n hn2 hn => (evenStripGain_edgeTentOdd_eq_oddStripCost_of_le hε0 hε2 hεr hn2 hn).2,
    fun n hn => (oddStripCost_edgeTentOdd_le_evenStripGain hε0 hε2 hεr hn).2,
    sum_oddStripCost_edgeTentOdd_le_sum_evenStripGain hε0 hε2 hεr,
    hpole⟩


/-! ## Part II: Unconditional full reflected-prime/polar allocation across arbitrary tests -/

/-! ### Bridge between the incidence-ledger functionals and the lag-Abel functionals -/

/-- `autoCorr` in the incidence ledger and `autoCorrelation` in the lag-Abel calculus are
definitionally identical. -/
theorem autoCorr_eq_autoCorrelation (F : ℝ → ℝ) (t : ℝ) :
    autoCorr F t = autoCorrelation F t := rfl

/-- Each favorable strip gain `evenStripGain F r n` is `2 Λ(n)/√n` times `stripMass F r (log n)`. -/
theorem evenStripGain_eq_stripMass (F : ℝ → ℝ) (r : ℝ) (n : ℕ) :
    evenStripGain F r n = 2 * vonMangoldtAtom n * stripMass F r (Real.log n) := rfl

/-- The incidence-ledger atom `vonMangoldtAtom n` coincides with `Λ(n) n^{−1/2}` at every natural
number `n` (since `Λ(0) = Λ(1) = 0`). -/
theorem vonMangoldtAtom_eq_mul_inv_sqrt (n : ℕ) :
    vonMangoldtAtom n = (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.sqrt n)⁻¹ := by
  unfold vonMangoldtAtom
  by_cases hn : 2 ≤ n
  · rw [if_pos hn, div_eq_mul_inv]
  · rw [if_neg hn]
    have hle : n ≤ 1 := by omega
    have hz : (ArithmeticFunction.vonMangoldt n : ℝ) = 0 := by
      interval_cases n <;> simp
    rw [hz, zero_mul]

/-- Any lag weight `g` vanishing on `[2r, ∞)` has the same `vonMangoldtAtom`-sum over
`relevantShifts r` and over `Finset.range (N + 1)` whenever `e^{2r} ≤ N`. -/
theorem sum_relevantShifts_eq_sum_range {g : ℝ → ℝ} {r : ℝ} {N : ℕ}
    (hg : ∀ s, 2 * r ≤ s → g s = 0) (hN : Real.exp (2 * r) ≤ N) :
    (∑ n ∈ relevantShifts r, 2 * vonMangoldtAtom n * g (Real.log n)) =
      ∑ n ∈ Finset.range (N + 1),
        (ArithmeticFunction.vonMangoldt n : ℝ) * (2 * (Real.sqrt n)⁻¹ * g (Real.log n)) := by
  have hsub : relevantShifts r ⊆ Finset.range (N + 1) := fun n hn => by
    obtain ⟨hn2, hlog⟩ := mem_relevantShifts.mp hn
    rw [Finset.mem_range]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlt : (n : ℝ) < Real.exp (2 * r) := (Real.log_lt_iff_lt_exp hn0).mp hlog
    have hle : (n : ℝ) < (N : ℝ) + 1 := by linarith
    exact_mod_cast hle
  rw [Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [vonMangoldtAtom_eq_mul_inv_sqrt]
    ring
  · intro n _ hnr
    rw [mem_relevantShifts, not_and_or, not_lt] at hnr
    rcases hnr with h1 | h2
    · unfold vonMangoldtAtom
      rw [if_neg h1, mul_zero, zero_mul]
    · rw [hg (Real.log n) h2, mul_zero]

/-! ### Exact polar-Chebyshev allocation of `evenStripGain` across all relevant shifts -/

/-- **Unconditional polar-Chebyshev allocation of the favorable strip gains.** For every continuous
test `F` supported in `[−r, r]` (`r > 0`), the sum of `evenStripGain F r n` over `relevantShifts r`
equals the hyperbolic polar integral of `stripMass F r` plus the two-pole Chebyshev defect tested
against the strip-mass lag derivative. -/
theorem sum_evenStripGain_eq_polar_add_chebyshev {F : ℝ → ℝ} {r : ℝ} (hF : Continuous F)
    (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) :
    (∑ n ∈ relevantShifts r, evenStripGain F r n) =
      (∫ s in Ioi (0 : ℝ), 4 * Real.cosh (s / 2) * stripMass F r s) +
        ∫ s in Ioi (0 : ℝ), chebyshevTwoPoleDefect s *
          (2 * Real.exp (-s / 2) * (-(F (s - r)) ^ 2 - stripMass F r s / 2)) := by
  set N := ⌈Real.exp (2 * r)⌉₊
  have hN : Real.exp (2 * r) ≤ N := Nat.le_ceil _
  simp_rw [evenStripGain_eq_stripMass]
  rw [sum_relevantShifts_eq_sum_range (fun s hs => stripMass_eq_zero hF hr hsupp hs) hN]
  exact stripMass_cost_eq_polar_add_chebyshev hF hr hsupp hN

/-! ### Exact identification of `poleCharge` with the hyperbolic autocorrelation integral -/

/-- `autoCorrelation F` is even: `autoCorrelation F (−t) = autoCorrelation F t`. -/
theorem autoCorrelation_neg_eq (F : ℝ → ℝ) (t : ℝ) :
    autoCorrelation F (-t) = autoCorrelation F t := by
  rw [autoCorrelation, autoCorrelation]
  have h := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun x => F x * F (x + -t)) t
  rw [← h]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show F (x + t) * F (x + t + -t) = F x * F (x + t)
  rw [show x + t + -t = x by ring, mul_comm]

/-- For a continuous test supported in `[−r, r]`, `autoCorrelation F` has compact support in
`[−2r, 2r]`. -/
theorem hasCompactSupport_autoCorrelation_of_support {F : ℝ → ℝ} {r : ℝ}
    (hF : Continuous F) (hr : 0 < r) (hsupp : ∀ y, r < |y| → F y = 0) :
    HasCompactSupport (autoCorrelation F) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * r)) (b := 2 * r)) fun t ht => ?_
  rcases lt_or_ge t 0 with h | h
  · rw [← autoCorrelation_neg_eq]
    refine autoCorrelation_eq_zero hF hr hsupp ?_
    by_contra hc
    exact ht (Set.mem_Icc.mpr ⟨by linarith [not_le.mp hc], by linarith⟩)
  · refine autoCorrelation_eq_zero hF hr hsupp ?_
    by_contra hc
    exact ht (Set.mem_Icc.mpr ⟨by linarith, by linarith [not_le.mp hc]⟩)

/-- The two-variable integrand `(s, x) ↦ cosh(s/2) F(x) F(x + s)` has compact support when `F` is
supported in `[−r, r]`. -/
theorem hasCompactSupport_cosh_mul_shift {F : ℝ → ℝ} {r : ℝ}
    (hsupp : ∀ y, r < |y| → F y = 0) :
    HasCompactSupport fun p : ℝ × ℝ => Real.cosh (p.1 / 2) * (F p.2 * F (p.2 + p.1)) := by
  refine HasCompactSupport.intro
    ((isCompact_Icc (a := -(2 * r)) (b := 2 * r)).prod (isCompact_Icc (a := -r) (b := r)))
    fun p hp => ?_
  by_cases hx : r < |p.2|
  · rw [hsupp p.2 hx]; ring
  by_cases hxs : r < |p.2 + p.1|
  · rw [hsupp _ hxs]; ring
  exfalso
  refine hp ⟨?_, Set.mem_Icc.mpr (abs_le.mp (not_lt.mp hx))⟩
  have h1 := abs_le.mp (not_lt.mp hx)
  have h2 := abs_le.mp (not_lt.mp hxs)
  exact Set.mem_Icc.mpr ⟨by linarith [h1.2, h2.1], by linarith [h1.1, h2.2]⟩

/-- Fubini identity for the hyperbolic autocorrelation pairing:
`∫ cosh(s/2) autoCorrelation F s ds = (∫ F(x) cosh(x/2) dx)² − (∫ F(x) sinh(x/2) dx)²`. -/
theorem integral_cosh_mul_autoCorrelation_eq {F : ℝ → ℝ} {r : ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hsupp : ∀ y, r < |y| → F y = 0) :
    (∫ s, Real.cosh (s / 2) * autoCorrelation F s) =
      (∫ x, F x * Real.cosh (x / 2)) ^ 2 - (∫ x, F x * Real.sinh (x / 2)) ^ 2 := by
  have hcont : Continuous fun p : ℝ × ℝ => Real.cosh (p.1 / 2) * (F p.2 * F (p.2 + p.1)) := by
    fun_prop
  have hint : Integrable
      (fun p : ℝ × ℝ => Real.cosh (p.1 / 2) * (F p.2 * F (p.2 + p.1))) :=
    hcont.integrable_of_hasCompactSupport (hasCompactSupport_cosh_mul_shift hsupp)
  have hvp : ((volume : Measure ℝ).prod volume) = (volume : Measure (ℝ × ℝ)) :=
    (MeasureTheory.Measure.volume_eq_prod ℝ ℝ).symm
  have hintprod : Integrable (Function.uncurry fun (s : ℝ) (x : ℝ) =>
      Real.cosh (s / 2) * (F x * F (x + s))) ((volume : Measure ℝ).prod volume) :=
    hvp ▸ hint
  have hswap := MeasureTheory.integral_integral_swap hintprod
  have hleft : (∫ s, Real.cosh (s / 2) * autoCorrelation F s) =
      ∫ s, ∫ x, Real.cosh (s / 2) * (F x * F (x + s)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    show Real.cosh (s / 2) * autoCorrelation F s = ∫ x, Real.cosh (s / 2) * (F x * F (x + s))
    rw [autoCorrelation, MeasureTheory.integral_const_mul]
  have hco : Integrable fun u => F u * Real.cosh (u / 2) :=
    (hF.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hsi : Integrable fun u => F u * Real.sinh (u / 2) :=
    (hF.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hinner : ∀ x : ℝ, (∫ s, Real.cosh (s / 2) * (F x * F (x + s))) =
      F x * (Real.cosh (x / 2) * (∫ u, F u * Real.cosh (u / 2)) -
        Real.sinh (x / 2) * ∫ u, F u * Real.sinh (u / 2)) := by
    intro x
    have htr := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun u => Real.cosh ((u - x) / 2) * (F x * F u)) x
    have hstep : (∫ s, Real.cosh (s / 2) * (F x * F (x + s))) =
        ∫ u, Real.cosh ((u - x) / 2) * (F x * F u) := by
      rw [← htr]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      show Real.cosh (s / 2) * (F x * F (x + s)) =
        Real.cosh ((s + x - x) / 2) * (F x * F (s + x))
      rw [show s + x - x = s by ring, show x + s = s + x by ring]
    rw [hstep]
    have hexpand : ∀ u : ℝ, Real.cosh ((u - x) / 2) * (F x * F u) =
        F x * (Real.cosh (x / 2) * (F u * Real.cosh (u / 2)) -
          Real.sinh (x / 2) * (F u * Real.sinh (u / 2))) := by
      intro u
      have : Real.cosh ((u - x) / 2) =
          Real.cosh (u / 2) * Real.cosh (x / 2) - Real.sinh (u / 2) * Real.sinh (x / 2) := by
        rw [show (u - x) / 2 = u / 2 - x / 2 by ring, Real.cosh_sub]
      rw [this]; ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hexpand),
      MeasureTheory.integral_const_mul,
      MeasureTheory.integral_sub (hco.const_mul _) (hsi.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hleft, hswap, MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hinner)]
  have hfin : ∀ x : ℝ, F x * (Real.cosh (x / 2) * (∫ u, F u * Real.cosh (u / 2)) -
        Real.sinh (x / 2) * ∫ u, F u * Real.sinh (u / 2)) =
      (∫ u, F u * Real.cosh (u / 2)) * (F x * Real.cosh (x / 2)) -
        (∫ u, F u * Real.sinh (u / 2)) * (F x * Real.sinh (x / 2)) := fun _ => by ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hfin),
    MeasureTheory.integral_sub (hco.const_mul _) (hsi.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  ring

/-- **The pole charge of an odd compactly supported test in autocorrelation form.** For every odd
continuous test `F` supported in `[−r, r]` (`r > 0`),
`poleCharge F = −∫_{s>0} 4 cosh(s/2) autoCorrelation F s ds`. -/
theorem poleCharge_eq_neg_integral_cosh_autoCorrelation {F : ℝ → ℝ} {r : ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) :
    poleCharge F = -∫ s in Ioi (0 : ℝ), 4 * Real.cosh (s / 2) * autoCorrelation F s := by
  have hAc : Continuous (autoCorrelation F) := by
    obtain ⟨M, hM⟩ := hFc.exists_bound_of_continuous hF
    refine continuous_of_dominated (bound := fun x => ‖F x‖ * M)
      (fun u => (hF.mul (hF.comp (continuous_id.add continuous_const))).aestronglyMeasurable)
      (fun u => Filter.Eventually.of_forall fun x => ?_)
      ((hF.norm.mul continuous_const).integrable_of_hasCompactSupport hFc.norm.mul_right)
      (Filter.Eventually.of_forall fun x =>
        continuous_const.mul (hF.comp (continuous_const.add continuous_id)))
    rw [Real.norm_eq_abs, abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hM (x + u)) (norm_nonneg _)
  have hAcs : HasCompactSupport (autoCorrelation F) :=
    hasCompactSupport_autoCorrelation_of_support hF hr hsupp
  have hg : Integrable fun s => Real.cosh (s / 2) * autoCorrelation F s :=
    ((Real.continuous_cosh.comp (continuous_id.div_const 2)).mul hAc).integrable_of_hasCompactSupport
      hAcs.mul_left
  have heven : ∀ s : ℝ, Real.cosh (-s / 2) * autoCorrelation F (-s) =
      Real.cosh (s / 2) * autoCorrelation F s := fun s => by
    rw [autoCorrelation_neg_eq, show -s / 2 = -(s / 2) by ring, Real.cosh_neg]
  have hhalf := integral_eq_two_mul_Ioi_of_even hg heven
  have hpolar := integral_cosh_mul_autoCorrelation_eq hF hFc hsupp
  have hcosh : (∫ x, F x * Real.cosh (x / 2)) = 0 := evenPoleMoment_eq_zero_of_odd hodd
  have hre : (∫ s in Ioi (0 : ℝ), 4 * Real.cosh (s / 2) * autoCorrelation F s) =
      4 * ∫ s in Ioi (0 : ℝ), Real.cosh (s / 2) * autoCorrelation F s := by
    rw [← MeasureTheory.integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by ring
  rw [hcosh] at hpolar
  unfold poleCharge oddPoleMoment
  linarith [hpolar, hhalf, hre]

/-! ### The joint reflected-prime/polar cost and its exact Chebyshev-defect allocations -/

/-- **The joint reflected-prime/polar cost** of the incidence ledger at aperture `r`: the net
reflected-prime charge `Σ_n oddStripCost_n − Σ_n evenStripGain_n` together with the pole charge
`poleCharge F`. -/
def reflectedPrimePolarCost (F : ℝ → ℝ) (r : ℝ) : ℝ :=
  (∑ n ∈ relevantShifts r, oddStripCost F r n) -
    (∑ n ∈ relevantShifts r, evenStripGain F r n) + poleCharge F

/-- The reflected-prime/polar cost equals `2 * primeSideCharge F + poleCharge F` on every odd
continuous test supported in `[−r, r]`. -/
theorem reflectedPrimePolarCost_eq_two_primeSide_add_poleCharge {F : ℝ → ℝ} {r : ℝ}
    (hF : Continuous F) (hodd : ∀ x, F (-x) = -F x) (hr : 0 ≤ r)
    (hsupp : ∀ x, r < |x| → F x = 0) :
    reflectedPrimePolarCost F r = 2 * primeSideCharge F + poleCharge F := by
  unfold reflectedPrimePolarCost
  have h := sum_evenStripGain_sub_sum_oddStripCost hF hodd hr hsupp
  linarith

/-- The reflected-prime/polar cost written over `relevantShifts r` in terms of `autoCorrelation`. -/
theorem reflectedPrimePolarCost_eq_sum_autoCorrelation_add_poleCharge {F : ℝ → ℝ} {r : ℝ}
    (hF : Continuous F) (hodd : ∀ x, F (-x) = -F x) (hr : 0 ≤ r)
    (hsupp : ∀ x, r < |x| → F x = 0) :
    reflectedPrimePolarCost F r =
      (∑ n ∈ relevantShifts r, 2 * vonMangoldtAtom n * autoCorrelation F (Real.log n)) +
        poleCharge F := by
  rw [reflectedPrimePolarCost_eq_two_primeSide_add_poleCharge hF hodd hr hsupp,
    primeSideCharge_eq_sum_relevantShifts hr hsupp, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [autoCorr_eq_autoCorrelation]
  ring

/-- **Correlation form of the reflected-prime/polar cost.** For every odd continuous test `F`
supported in `[−r, r]` (`r > 0`), the reflected-prime/polar cost is the difference between the
prime-power autocorrelation sum and the hyperbolic polar autocorrelation integral. -/
theorem reflectedPrimePolarCost_eq_prime_sub_polar_autoCorrelation {F : ℝ → ℝ} {r : ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) :
    reflectedPrimePolarCost F r =
      (∑ n ∈ relevantShifts r, 2 * vonMangoldtAtom n * autoCorrelation F (Real.log n)) -
        ∫ s in Ioi (0 : ℝ), 4 * Real.cosh (s / 2) * autoCorrelation F s := by
  rw [reflectedPrimePolarCost_eq_sum_autoCorrelation_add_poleCharge hF hodd hr.le hsupp,
    poleCharge_eq_neg_integral_cosh_autoCorrelation hF hFc hodd hr hsupp]
  ring

/-- **First-order Chebyshev-defect allocation of the reflected-prime/polar cost across arbitrary
odd `C¹_c` tests.** For every odd `F ∈ C¹_c(ℝ)` supported in `[−r, r]` (`r > 0`), the rate-`1`
prime and polar main terms in `reflectedPrimePolarCost F r` cancel identically, leaving only the
two-pole Chebyshev defect `E(s) = e^s + s − 1 − ψ(e^s)` paired against the test's lag derivative. -/
theorem reflectedPrimePolarCost_eq_chebyshevTwoPoleDefect {F : ℝ → ℝ} {r : ℝ}
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) :
    reflectedPrimePolarCost F r =
      ∫ s in Ioi (0 : ℝ), chebyshevTwoPoleDefect s *
        (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)) := by
  set N := ⌈Real.exp (2 * r)⌉₊
  have hN : Real.exp (2 * r) ≤ N := Nat.le_ceil _
  rw [reflectedPrimePolarCost_eq_prime_sub_polar_autoCorrelation hF.continuous hFc hodd hr hsupp,
    sum_relevantShifts_eq_sum_range (fun s hs => autoCorrelation_eq_zero hF.continuous hr hsupp hs) hN]
  exact testBalance hF hFc hr hsupp hN

/-- **Horizon-localized Chebyshev-defect allocation.** Because `lagTestWeight F` vanishes on
`[2r, ∞)`, the reflected-prime/polar cost of an odd `F ∈ C¹_c(ℝ)` supported in `[−r, r]` reads
`chebyshevTwoPoleDefect` only on the finite horizon `(0, 2r]`. -/
theorem reflectedPrimePolarCost_eq_chebyshevTwoPoleDefect_Ioc {F : ℝ → ℝ} {r : ℝ}
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) :
    reflectedPrimePolarCost F r =
      ∫ s in Ioc (0 : ℝ) (2 * r), chebyshevTwoPoleDefect s *
        (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)) := by
  set N := ⌈Real.exp (2 * r)⌉₊
  have hN : Real.exp (2 * r) ≤ N := Nat.le_ceil _
  have hS : (0 : ℝ) < 2 * r := by linarith
  have hvan : ∀ s, 2 * r ≤ s → lagTestWeight F s = 0 := fun s hs => by
    rw [lagTestWeight, autoCorrelation_eq_zero hF.continuous hr hsupp hs, mul_zero]
  have hloc := integral_chebyshev_mul_deriv_eq_Ioc (contDiff_one_lagTestWeight hF hFc) hS hvan hN
  rw [reflectedPrimePolarCost_eq_chebyshevTwoPoleDefect hF hFc hodd hr hsupp]
  have hcongr1 : (∫ s in Ioi (0 : ℝ), chebyshevTwoPoleDefect s *
        (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2))) =
      ∫ s in Ioi (0 : ℝ), chebyshevTwoPoleDefect s * deriv (lagTestWeight F) s :=
    setIntegral_congr_fun measurableSet_Ioi fun s _ => by rw [deriv_lagTestWeight hF hFc s]
  have hcongr2 : (∫ s in Ioc (0 : ℝ) (2 * r), chebyshevTwoPoleDefect s * deriv (lagTestWeight F) s) =
      ∫ s in Ioc (0 : ℝ) (2 * r), chebyshevTwoPoleDefect s *
        (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)) :=
    setIntegral_congr_fun measurableSet_Ioc fun s _ => by rw [deriv_lagTestWeight hF hFc s]
  rw [hcongr1, hloc, hcongr2]

/-- **Unconditional Chebyshev-defect bound on the reflected-prime/polar cost.** For every odd
`F ∈ C¹_c(ℝ)` supported in `[−r, r]` (`r > 0`), `|reflectedPrimePolarCost F r|` is bounded by the
`L¹` pairing of `|chebyshevTwoPoleDefect s|` against `|(lagTestWeight F)'(s)|` on `(0, 2r]`. -/
theorem abs_reflectedPrimePolarCost_le_integral_abs_chebyshevTwoPoleDefect {F : ℝ → ℝ} {r : ℝ}
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) :
    |reflectedPrimePolarCost F r| ≤
      ∫ s in Ioc (0 : ℝ) (2 * r),
        |chebyshevTwoPoleDefect s| *
          |2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)| := by
  rw [reflectedPrimePolarCost_eq_chebyshevTwoPoleDefect_Ioc hF hFc hodd hr hsupp]
  refine le_trans abs_integral_le_integral_abs (le_of_eq ?_)
  exact setIntegral_congr_fun measurableSet_Ioc fun s _ => abs_mul _ _

/-- The second cross-correlation `∫ F(x) F''(x + t) dx` of a `C²_c` test. -/
def secondCrossCorr (F : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x, F x * deriv (deriv F) (x + t)

theorem hasDerivAt_crossCorrelation_of_contDiff {F : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (hF' : ContDiff ℝ 1 (deriv F))
    (hFc : HasCompactSupport F) (t : ℝ) :
    HasDerivAt (crossCorrelation F) (secondCrossCorr F t) t := by
  have hFcont : Continuous F := hF.continuous
  have hdcont : Continuous (deriv F) := hF.continuous_deriv le_rfl
  have hd2cont : Continuous (deriv (deriv F)) := hF'.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := hFc.deriv.deriv.exists_bound_of_continuous hd2cont
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (u : ℝ) (x : ℝ) => F x * deriv F (x + u))
    (F' := fun (u : ℝ) (x : ℝ) => F x * deriv (deriv F) (x + u))
    (x₀ := t) (bound := fun x => ‖F x‖ * M) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun u =>
      (hFcont.mul (hdcont.comp (continuous_id.add continuous_const))).aestronglyMeasurable)
    ((hFcont.mul (hdcont.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right)
    ((hFcont.mul (hd2cont.comp (continuous_id.add continuous_const))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x u _ => by
      rw [Real.norm_eq_abs, abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM (x + u)) (norm_nonneg _))
    (integrable_bound hF hFc M)
    (Filter.Eventually.of_forall fun x u _ =>
      (HasDerivAt.comp_const_add x u
        ((hF'.differentiable one_ne_zero (x + u)).hasDerivAt)).const_mul (F x))
  exact key.2

theorem contDiff_one_deriv_lagTestWeight_of_contDiff {F : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (hF' : ContDiff ℝ 1 (deriv F)) (hFc : HasCompactSupport F) :
    ContDiff ℝ 1 (deriv (lagTestWeight F)) := by
  have hFcont : Continuous F := hF.continuous
  have hd2cont : Continuous (deriv (deriv F)) := hF'.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := hFc.deriv.deriv.exists_bound_of_continuous hd2cont
  have hcont2 : Continuous (secondCrossCorr F) := by
    refine continuous_of_dominated (bound := fun x => ‖F x‖ * M)
      (fun u => (hFcont.mul (hd2cont.comp (continuous_id.add continuous_const))).aestronglyMeasurable)
      (fun u => Filter.Eventually.of_forall fun x => ?_) (integrable_bound hF hFc M)
      (Filter.Eventually.of_forall fun x =>
        continuous_const.mul (hd2cont.comp (continuous_const.add continuous_id)))
    rw [Real.norm_eq_abs, abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hM (x + u)) (norm_nonneg _)
  have hcc : ContDiff ℝ 1 (crossCorrelation F) := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun t => (hasDerivAt_crossCorrelation_of_contDiff hF hF' hFc t).differentiableAt, ?_⟩
    have hd : deriv (crossCorrelation F) = secondCrossCorr F :=
      funext fun t => (hasDerivAt_crossCorrelation_of_contDiff hF hF' hFc t).deriv
    rwa [hd]
  have hd : deriv (lagTestWeight F) =
      fun s => 2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2) :=
    funext fun s => deriv_lagTestWeight hF hFc s
  rw [hd]
  exact (contDiff_const.mul ((contDiff_id.neg.div_const 2).exp)).mul
    (hcc.sub ((contDiff_one_autoCorrelation hF hFc).div_const 2))

/-- **Second-order critical-scale receiver allocation across arbitrary odd `C²_c` tests.** For
every odd `F ∈ C²_c(ℝ)` supported in `[−r, r]` (`r > 0`), the reflected-prime/polar cost equals
minus the critical-scale cancellation functional `D(s) + s²/2 − s` paired against the second
derivative of `lagTestWeight F`. -/
theorem reflectedPrimePolarCost_eq_criticalScalePrefix {F : ℝ → ℝ} {r : ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) :
    reflectedPrimePolarCost F r =
      -∫ s in Ioi (0 : ℝ),
        (criticalScalePrefix s + s ^ 2 / 2 - s) * deriv (deriv (lagTestWeight F)) s := by
  set N := ⌈Real.exp (2 * r)⌉₊
  have hN : Real.exp (2 * r) ≤ N := Nat.le_ceil _
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hF' : ContDiff ℝ 1 (deriv F) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) F from hF)).2.2
  have hS : (0 : ℝ) < 2 * r := by linarith
  have hvan : ∀ s, 2 * r ≤ s → lagTestWeight F s = 0 := fun s hs => by
    rw [lagTestWeight, autoCorrelation_eq_zero hF.continuous hr hsupp hs, mul_zero]
  have hkey := sum_vonMangoldt_sub_polar_eq_criticalScalePrefix
    (contDiff_one_lagTestWeight hF1 hFc)
    (contDiff_one_deriv_lagTestWeight_of_contDiff hF1 hF' hFc) hS hvan hN
  rw [reflectedPrimePolarCost_eq_prime_sub_polar_autoCorrelation hF.continuous hFc hodd hr hsupp,
    sum_relevantShifts_eq_sum_range (fun s hs => autoCorrelation_eq_zero hF.continuous hr hsupp hs) hN,
    ← hkey]
  congr 1
  · refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h0 : n = 0
    · subst h0; simp
    · have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero h0
      rw [lagTestWeight, exp_neg_half_log hn]
  · refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [lagTestWeight, ← mul_assoc, polarDensity_mul_half_weight, mul_assoc]

/-- **Integration by parts for the second cross-correlation.** For every `F ∈ C²_c(ℝ)`,
`secondCrossCorr F s = ∫ F(x) F''(x + s) dx = −∫ F'(x) F'(x + s) dx = −autoCorrelation (deriv F) s`. -/
theorem secondCrossCorr_eq_neg_autoCorrelation_deriv {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (s : ℝ) :
    secondCrossCorr F s = -autoCorrelation (deriv F) s := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hF' : ContDiff ℝ 1 (deriv F) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) F from hF)).2.2
  have hFcont : Continuous F := hF.continuous
  have hdcont : Continuous (deriv F) := hF1.continuous_deriv le_rfl
  have hd2cont : Continuous (deriv (deriv F)) := hF'.continuous_deriv le_rfl
  set g : ℝ → ℝ := fun x => F x * deriv F (x + s)
  set g' : ℝ → ℝ := fun x => deriv F x * deriv F (x + s) + F x * deriv (deriv F) (x + s)
  have hg : ∀ x, HasDerivAt g (g' x) x := fun x => by
    have h1 : HasDerivAt F (deriv F x) x := (hF1.differentiable one_ne_zero x).hasDerivAt
    have h2 : HasDerivAt (fun y => deriv F (y + s)) (deriv (deriv F) (x + s)) x := by
      have hc : HasDerivAt (fun y => deriv F (s + y)) (deriv (deriv F) (s + x)) x :=
        HasDerivAt.comp_const_add s x ((hF'.differentiable one_ne_zero (s + x)).hasDerivAt)
      have heq : (fun y => deriv F (s + y)) = fun y => deriv F (y + s) :=
        funext fun y => by rw [add_comm]
      rwa [heq, add_comm s x] at hc
    exact h1.mul h2
  have hg'c : Continuous g' :=
    (hdcont.mul (hdcont.comp (continuous_id.add continuous_const))).add
      (hFcont.mul (hd2cont.comp (continuous_id.add continuous_const)))
  have hgc : HasCompactSupport g := hFc.mul_right
  have hzero := GaloisForLFunctions.HTGeometry.integral_deriv_eq_zero_of_hasCompactSupport
    hg hg'c hgc
  have hint1 : Integrable fun x => deriv F x * deriv F (x + s) :=
    (hdcont.mul (hdcont.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.deriv.mul_right
  have hint2 : Integrable fun x => F x * deriv (deriv F) (x + s) :=
    (hFcont.mul (hd2cont.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hsplit : (∫ x, g' x) = autoCorrelation (deriv F) s + secondCrossCorr F s := by
    change (∫ x, deriv F x * deriv F (x + s) + F x * deriv (deriv F) (x + s)) = _
    rw [integral_add hint1 hint2]
    rfl
  linarith

/-- Explicit formula for the second lag derivative `(lagTestWeight F)''(s)` of a `C²_c` test in
terms of the derivative autocorrelation `autoCorrelation (deriv F) s`, the cross-correlation
`crossCorrelation F s`, and the autocorrelation `autoCorrelation F s`. -/
theorem deriv_deriv_lagTestWeight {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (s : ℝ) :
    deriv (deriv (lagTestWeight F)) s =
      -2 * Real.exp (-s / 2) *
        (autoCorrelation (deriv F) s + crossCorrelation F s - autoCorrelation F s / 4) := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hF' : ContDiff ℝ 1 (deriv F) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) F from hF)).2.2
  have hd1 : deriv (lagTestWeight F) =
      fun u => 2 * Real.exp (-u / 2) * (crossCorrelation F u - autoCorrelation F u / 2) :=
    funext fun u => deriv_lagTestWeight hF1 hFc u
  rw [hd1]
  have hexp : HasDerivAt (fun u : ℝ => 2 * Real.exp (-u / 2)) (-Real.exp (-s / 2)) s := by
    have hlin : HasDerivAt (fun u : ℝ => -u / 2) (-1 / 2 : ℝ) s := by
      simpa [neg_div] using (hasDerivAt_id s).neg.div_const (2 : ℝ)
    have h := (Real.hasDerivAt_exp (-s / 2)).comp s hlin
    have h2 : HasDerivAt (fun u : ℝ => 2 * Real.exp (-u / 2))
        (2 * (Real.exp (-s / 2) * (-1 / 2))) s := h.const_mul (2 : ℝ)
    exact h2.congr_deriv (by ring)
  have hcc : HasDerivAt (crossCorrelation F) (-autoCorrelation (deriv F) s) s := by
    rw [← secondCrossCorr_eq_neg_autoCorrelation_deriv hF hFc s]
    exact hasDerivAt_crossCorrelation_of_contDiff hF1 hF' hFc s
  have hac : HasDerivAt (fun u => autoCorrelation F u / 2) (crossCorrelation F s / 2) s :=
    (hasDerivAt_autoCorrelation hF1 hFc s).div_const 2
  have hprod : HasDerivAt
      (fun u => 2 * Real.exp (-u / 2) * (crossCorrelation F u - autoCorrelation F u / 2))
      (-Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2) +
        2 * Real.exp (-s / 2) * (-autoCorrelation (deriv F) s - crossCorrelation F s / 2)) s :=
    hexp.mul (hcc.sub hac)
  rw [hprod.deriv]
  ring

/-- **Second-order critical-scale receiver allocation in terms of `autoCorrelation (deriv F)`.**
For every odd `F ∈ C²_c(ℝ)` supported in `[−r, r]` (`r > 0`), the reflected-prime/polar cost pairs
the critical-scale prefix functional `D(s) + s²/2 − s` directly against the derivative
autocorrelation `autoCorrelation (deriv F) s + crossCorrelation F s − autoCorrelation F s / 4`. -/
theorem reflectedPrimePolarCost_eq_criticalScalePrefix_autoCorrelation_deriv {F : ℝ → ℝ} {r : ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) :
    reflectedPrimePolarCost F r =
      ∫ s in Ioi (0 : ℝ),
        (criticalScalePrefix s + s ^ 2 / 2 - s) *
          (2 * Real.exp (-s / 2) *
            (autoCorrelation (deriv F) s + crossCorrelation F s - autoCorrelation F s / 4)) := by
  rw [reflectedPrimePolarCost_eq_criticalScalePrefix hF hFc hodd hr hsupp, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [deriv_deriv_lagTestWeight hF hFc s]
  ring

/-- **Full allocation of the total cost side `(Σ_n oddStripCost_n) + poleCharge` across arbitrary
odd `C¹_c` tests.** Combining the polar-Chebyshev allocation of `evenStripGain` with the joint
prime-polar Chebyshev balance decomposes `(Σ_n oddStripCost_n) + poleCharge F` into the hyperbolic
polar integral of `stripMass F r` plus the two Chebyshev-defect integrals. -/
theorem sum_oddStripCost_add_poleCharge_eq_polar_stripMass_add_chebyshev {F : ℝ → ℝ} {r : ℝ}
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) :
    (∑ n ∈ relevantShifts r, oddStripCost F r n) + poleCharge F =
      (∫ s in Ioi (0 : ℝ), 4 * Real.cosh (s / 2) * stripMass F r s) +
        (∫ s in Ioi (0 : ℝ), chebyshevTwoPoleDefect s *
          (2 * Real.exp (-s / 2) * (-(F (s - r)) ^ 2 - stripMass F r s / 2))) +
        ∫ s in Ioi (0 : ℝ), chebyshevTwoPoleDefect s *
          (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)) := by
  have heven := sum_evenStripGain_eq_polar_add_chebyshev hF.continuous hr hsupp
  have hcost := reflectedPrimePolarCost_eq_chebyshevTwoPoleDefect hF hFc hodd hr hsupp
  unfold reflectedPrimePolarCost at hcost
  linarith

/-! ### The all-aperture reflected-prime/polar incidence ledger -/

/-- **The reflected-prime/polar incidence ledger at every aperture.** For every odd `F ∈ C²_c(ℝ)`
supported in `[−r, r]` (`r > 0`) and every plateau radius `R > r`,
`Ẑ(F) = surplusPool + crossingPotentialTerm + gaugeRemainder − reflectedPrimePolarCost F r`. -/
theorem fullZeroForm_eq_reflectedPrimePolarLedger {F : ℝ → ℝ} {r R : ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) (hrR : r < R) :
    fullZeroForm F =
      surplusPool (aperturePlateau r R) F +
        crossingPotentialTerm (aperturePlateau r R) F +
        gaugeRemainder (aperturePlateau r R) F -
        reflectedPrimePolarCost F r := by
  rw [fullZeroForm_eq_incidenceLedger hF hFc hodd hr hsupp hrR]
  unfold reflectedPrimePolarCost
  ring

/-- **The incidence ledger with the prime and polar main terms cancelled.** For every odd
`F ∈ C²_c(ℝ)` supported in `[−r, r]` (`r > 0`) and every plateau radius `R > r`, the full zero
form equals the archimedean gauge terms minus the Chebyshev-defect lag integral on `(0, 2r]`. -/
theorem fullZeroForm_eq_chebyshevDefectLedger {F : ℝ → ℝ} {r R : ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) (hrR : r < R) :
    fullZeroForm F =
      surplusPool (aperturePlateau r R) F +
        crossingPotentialTerm (aperturePlateau r R) F +
        gaugeRemainder (aperturePlateau r R) F -
        ∫ s in Ioi (0 : ℝ), chebyshevTwoPoleDefect s *
          (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)) := by
  rw [fullZeroForm_eq_reflectedPrimePolarLedger hF hFc hodd hr hsupp hrR,
    reflectedPrimePolarCost_eq_chebyshevTwoPoleDefect (hF.of_le (by norm_num)) hFc hodd hr hsupp]

/-- `GlobalIncidenceAllocation r R F` holds if and only if the joint reflected-prime/polar cost is
paid by the surplus pool, the crossing potential, and the gauge remainder. -/
theorem globalIncidenceAllocation_iff_reflectedPrimePolarCost_le (r R : ℝ) (F : ℝ → ℝ) :
    GlobalIncidenceAllocation r R F ↔
      reflectedPrimePolarCost F r ≤
        surplusPool (aperturePlateau r R) F +
          crossingPotentialTerm (aperturePlateau r R) F +
          gaugeRemainder (aperturePlateau r R) F := by
  unfold GlobalIncidenceAllocation reflectedPrimePolarCost
  constructor <;> intro h <;> linarith

/-- **All-aperture positivity from reflected-prime/polar Chebyshev allocation.** Unlike
`fullZeroForm_nonneg_of_stripAllocation` (which requires `R ≤ 3/5` and decouples the prime strips
from the pole moment), paying the single Chebyshev-defect lag integral from
`surplusPool + crossingPotentialTerm + gaugeRemainder` implies `0 ≤ fullZeroForm F` at any aperture
`0 < r < R`. -/
theorem fullZeroForm_nonneg_of_reflectedPrimePolarAllocation {F : ℝ → ℝ} {r R : ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) (hrR : r < R)
    (halloc :
      (∫ s in Ioi (0 : ℝ), chebyshevTwoPoleDefect s *
          (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2))) ≤
        surplusPool (aperturePlateau r R) F +
          crossingPotentialTerm (aperturePlateau r R) F +
          gaugeRemainder (aperturePlateau r R) F) :
    0 ≤ fullZeroForm F := by
  rw [fullZeroForm_eq_chebyshevDefectLedger hF hFc hodd hr hsupp hrR]
  linarith

/-- **Equivalence with the Riemann Hypothesis.** The Riemann Hypothesis holds if and only if for
every aperture `r > 0` and every odd `F ∈ C²_c(ℝ)` supported in `[−r, r]`, there is a plateau
radius `R > r` at which the finite-horizon Chebyshev-defect integral of `F` on `(0, 2r]` is paid by
`surplusPool + crossingPotentialTerm + gaugeRemainder`. -/
theorem riemannHypothesis_iff_reflectedPrimePolarAllocation :
    RiemannHypothesis ↔
      ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r → ContDiff ℝ 2 F → HasCompactSupport F →
        (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
          ∃ R, r < R ∧
            (∫ s in Ioc (0 : ℝ) (2 * r), chebyshevTwoPoleDefect s *
                (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2))) ≤
              surplusPool (aperturePlateau r R) F +
                crossingPotentialTerm (aperturePlateau r R) F +
                gaugeRemainder (aperturePlateau r R) F := by
  rw [riemannHypothesis_iff_exists_plateau_globalIncidenceAllocation]
  constructor
  · intro h r F hr hF hFc hodd hsupp
    obtain ⟨R, hrR, hGIA⟩ := h r F hr hF hFc hodd hsupp
    refine ⟨R, hrR, ?_⟩
    rw [globalIncidenceAllocation_iff_reflectedPrimePolarCost_le,
      reflectedPrimePolarCost_eq_chebyshevTwoPoleDefect_Ioc
        (hF.of_le (by norm_num)) hFc hodd hr hsupp] at hGIA
    exact hGIA
  · intro h r F hr hF hFc hodd hsupp
    obtain ⟨R, hrR, halloc⟩ := h r F hr hF hFc hodd hsupp
    refine ⟨R, hrR, ?_⟩
    rw [globalIncidenceAllocation_iff_reflectedPrimePolarCost_le,
      reflectedPrimePolarCost_eq_chebyshevTwoPoleDefect_Ioc
        (hF.of_le (by norm_num)) hFc hodd hr hsupp]
    exact halloc

/-! ### Graded Chebyshev-defect allocation: constant mass deficit and every-positive-rate deficit -/

/-- `GradedIncidenceAllocation σ C` is equivalent to bounding the joint reflected-prime/polar cost
`reflectedPrimePolarCost F r` by the archimedean ledger budget plus the graded mass deficit
`C * e^{2σ r} * ∫ F²`. -/
theorem gradedIncidenceAllocation_iff_reflectedPrimePolarCost_le (σ C : ℝ) :
    GaloisForLFunctions.SquareRootThreshold.GradedIncidenceAllocation σ C ↔
      ∀ (r R : ℝ) (F : ℝ → ℝ), 0 < r → r < R → ContDiff ℝ 2 F → HasCompactSupport F →
        (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
        reflectedPrimePolarCost F r ≤
          surplusPool (aperturePlateau r R) F +
            crossingPotentialTerm (aperturePlateau r R) F +
            gaugeRemainder (aperturePlateau r R) F +
            C * Real.exp (2 * σ * r) * ∫ x, F x ^ 2 := by
  unfold GaloisForLFunctions.SquareRootThreshold.GradedIncidenceAllocation reflectedPrimePolarCost
  constructor <;> intro h r R F hr hrR hF hFc hodd hsupp <;>
     specialize h r R F hr hrR hF hFc hodd hsupp <;> linarith

/-- `GradedIncidenceAllocation σ C` is equivalent to bounding the horizon-localized Chebyshev-defect
integral on `(0, 2r]` by the archimedean ledger budget plus the graded mass deficit
`C * e^{2σ r} * ∫ F²`. -/
theorem gradedIncidenceAllocation_iff_chebyshevTwoPoleDefect_le (σ C : ℝ) :
    GaloisForLFunctions.SquareRootThreshold.GradedIncidenceAllocation σ C ↔
      ∀ (r R : ℝ) (F : ℝ → ℝ), 0 < r → r < R → ContDiff ℝ 2 F → HasCompactSupport F →
        (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
        (∫ s in Ioc (0 : ℝ) (2 * r), chebyshevTwoPoleDefect s *
            (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2))) ≤
          surplusPool (aperturePlateau r R) F +
            crossingPotentialTerm (aperturePlateau r R) F +
            gaugeRemainder (aperturePlateau r R) F +
            C * Real.exp (2 * σ * r) * ∫ x, F x ^ 2 := by
  rw [gradedIncidenceAllocation_iff_reflectedPrimePolarCost_le]
  constructor <;> intro h r R F hr hrR hF hFc hodd hsupp
  · rw [← reflectedPrimePolarCost_eq_chebyshevTwoPoleDefect_Ioc
      (hF.of_le (by norm_num)) hFc hodd hr hsupp]
    exact h r R F hr hrR hF hFc hodd hsupp
  · rw [reflectedPrimePolarCost_eq_chebyshevTwoPoleDefect_Ioc
      (hF.of_le (by norm_num)) hFc hodd hr hsupp]
    exact h r R F hr hrR hF hFc hodd hsupp

/-- **Zero-width bound from graded Chebyshev-defect allocation.** If at rate `2σ` (`σ ≥ 0`) every
odd `F ∈ C²_c(ℝ)` supported in `[−r, r]` (`r > 0`) admits a plateau radius `R > r` at which the
Chebyshev-defect integral `C_F` on `(0, 2r]` is paid by the archimedean ledger budget up to
`C * e^{2σ r} * ∫ F²`, then `zetaZeroWidth ≤ σ`. -/
theorem zetaZeroWidth_le_of_chebyshevDefectAllocation_graded {σ C : ℝ} (hσ : 0 ≤ σ)
    (halloc : ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r → ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
        ∃ R, r < R ∧
          (∫ s in Ioc (0 : ℝ) (2 * r), chebyshevTwoPoleDefect s *
              (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2))) ≤
            surplusPool (aperturePlateau r R) F +
              crossingPotentialTerm (aperturePlateau r R) F +
              gaugeRemainder (aperturePlateau r R) F +
              C * Real.exp (2 * σ * r) * ∫ x, F x ^ 2) :
    GaloisForLFunctions.SquareRootThreshold.zetaZeroWidth ≤ σ := by
  refine GaloisForLFunctions.SquareRootThreshold.zetaZeroWidth_le_of_graded_odd_fullZeroForm_floor
    (C := C) hσ ?_
  intro r hr F hF hFc hodd hsupp
  obtain ⟨R, hrR, hCF⟩ := halloc r F hr hF hFc hodd hsupp
  rw [fullZeroForm_eq_reflectedPrimePolarLedger hF hFc hodd hr hsupp hrR,
    reflectedPrimePolarCost_eq_chebyshevTwoPoleDefect_Ioc
      (hF.of_le (by norm_num)) hFc hodd hr hsupp]
  linarith

/-- **Riemann Hypothesis from Chebyshev-defect allocation with a uniform constant mass deficit.**
If there is a uniform constant `C` such that for every aperture `r > 0` and every odd `F ∈ C²_c(ℝ)`
supported in `[−r, r]` there exists `R > r` with the Chebyshev-defect integral `C_F` bounded by
`surplusPool + crossingPotentialTerm + gaugeRemainder + C * ∫ F²`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_chebyshevDefectAllocation_const_deficit {C : ℝ}
    (halloc : ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r → ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
        ∃ R, r < R ∧
          (∫ s in Ioc (0 : ℝ) (2 * r), chebyshevTwoPoleDefect s *
              (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2))) ≤
            surplusPool (aperturePlateau r R) F +
              crossingPotentialTerm (aperturePlateau r R) F +
              gaugeRemainder (aperturePlateau r R) F +
              C * ∫ x, F x ^ 2) :
    RiemannHypothesis := by
  rw [GaloisForLFunctions.SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero]
  refine le_antisymm ?_ GaloisForLFunctions.SquareRootThreshold.zetaZeroWidth_nonneg
  refine zetaZeroWidth_le_of_chebyshevDefectAllocation_graded (C := C) le_rfl ?_
  intro r F hr hF hFc hodd hsupp
  obtain ⟨R, hrR, hR⟩ := halloc r F hr hF hFc hodd hsupp
  refine ⟨R, hrR, ?_⟩
  simpa using hR

/-- **Riemann Hypothesis from Chebyshev-defect allocation with every-positive-rate graded deficit.**
If for every rate `σ > 0` there is a constant `C` such that for every aperture `r > 0` and every
odd `F ∈ C²_c(ℝ)` supported in `[−r, r]` there exists `R > r` with the Chebyshev-defect integral
`C_F` bounded by `surplusPool + crossingPotentialTerm + gaugeRemainder + C * e^{2σ r} * ∫ F²`, then
`RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_chebyshevDefectAllocation_every_pos_rate
    (halloc : ∀ σ : ℝ, 0 < σ → ∃ C : ℝ, ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r → ContDiff ℝ 2 F →
      HasCompactSupport F → (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
        ∃ R, r < R ∧
          (∫ s in Ioc (0 : ℝ) (2 * r), chebyshevTwoPoleDefect s *
              (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2))) ≤
            surplusPool (aperturePlateau r R) F +
              crossingPotentialTerm (aperturePlateau r R) F +
              gaugeRemainder (aperturePlateau r R) F +
              C * Real.exp (2 * σ * r) * ∫ x, F x ^ 2) :
    RiemannHypothesis := by
  rw [GaloisForLFunctions.SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero]
  refine le_antisymm ?_ GaloisForLFunctions.SquareRootThreshold.zetaZeroWidth_nonneg
  refine le_of_forall_pos_le_add fun σ hσ => ?_
  obtain ⟨C, hC⟩ := halloc σ hσ
  simpa using zetaZeroWidth_le_of_chebyshevDefectAllocation_graded (C := C) hσ.le hC

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
