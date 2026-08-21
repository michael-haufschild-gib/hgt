import GaloisForLFunctions.RHTower.CCMActualHeadMatchedApertureFiniteSupport
import GaloisForLFunctions.RHTower.CCMActualHeadOutgoingQuantileTransportProducer

/-!
# Matched-cell boundary collar and source coverage seam

Mass-matched symmetric cells and monotone quantile cells solve different assembly problems. This
module connects the matched construction directly to the actual restricted-Weil source without
pretending that the local matched cells partition the polar interval.

One matched cell is first rewritten as an exact autocorrelation transport. At a prime index beyond
the physical cutoff `floor (exp (2a))`, its atomic center already has zero aperture autocorrelation.
The part of its polar cell beyond `2a` also has zero autocorrelation. Therefore its whole signed
contribution is exactly the portion of the cell crossing the physical boundary:

```text
matchedCell_n(f) = 2 integral_[log n - rho_n, 2a]
  exp(h/2) * autocorrelation_f(h) dh.
```

Farther cells vanish as a special case, but near-cutoff cells survive as a literal finite boundary
collar. This exposes why an all-prime matched sum cannot be substituted silently for the physical
prime cutoff.

The second result inserts the canonical finite matched block into the actual source quadratic.
The exact remainder is a polar coverage seam: matched local polar mass minus the true polar
interval. Expanding the matched block preserves its symmetric-minus-Suzuki signs. No sign premise,
RH premise, numerical computation, or rearrangement of conditionally convergent streams is used.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

/-- The symmetric exponential polar cell has exactly the critical Mellin mass used to define its
radius. This is the scalar mass identity behind all matched-cell transport formulas. -/
theorem integral_exp_half_matchedPrimePolarCell_eq_atomWeight (n : ℕ) :
    (∫ h in (Real.log n - ccmActualHeadMatchedPrimePolarRadius n)..
        (Real.log n + ccmActualHeadMatchedPrimePolarRadius n),
      Real.exp (h / 2)) = criticalMellinAtomWeight n := by
  let s := Real.log n
  let ρ := ccmActualHeadMatchedPrimePolarRadius n
  let A := Real.exp (s / 2)
  rw [intervalIntegral_exp_half_eq]
  have hplus : Real.exp ((s + ρ) / 2) = A * Real.exp (ρ / 2) := by
    dsimp only [A]
    rw [show (s + ρ) / 2 = s / 2 + ρ / 2 by ring, Real.exp_add]
  have hminus : Real.exp ((s - ρ) / 2) = A * Real.exp (-(ρ / 2)) := by
    dsimp only [A]
    rw [show (s - ρ) / 2 = s / 2 + -(ρ / 2) by ring, Real.exp_add]
  rw [hplus, hminus]
  rw [show 2 * (A * Real.exp (ρ / 2)) - 2 * (A * Real.exp (-(ρ / 2))) =
      4 * A * Real.sinh (ρ / 2) by rw [Real.sinh_eq]; ring]
  dsimp only [ρ, s]
  unfold ccmActualHeadMatchedPrimePolarRadius
  rw [show (2 * Real.arsinh
      (criticalMellinAtomWeight n / (4 * Real.exp (Real.log n / 2)))) / 2 =
      Real.arsinh
        (criticalMellinAtomWeight n / (4 * Real.exp (Real.log n / 2))) by ring,
    Real.sinh_arsinh]
  dsimp only [A, s]
  field_simp [Real.exp_ne_zero]

/-- Exact same-head autocorrelation transport form of one mass-matched prime--polar cell. -/
theorem ccmActualHeadMatchedPrimePolarCellDifference_eq_autocorrelationTransport
    (n : ℕ) (f : SoninL2) :
    criticalMellinAtomWeight n *
          ccmActualHeadTranslationDefect (Real.log n) f -
        ccmActualHeadOutgoingPolarSymmetricCell
          (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f =
      2 * ∫ h in
          (Real.log n - ccmActualHeadMatchedPrimePolarRadius n)..
          (Real.log n + ccmActualHeadMatchedPrimePolarRadius n),
        Real.exp (h / 2) *
          (ccmActualHeadSymmetricAutocorrelation h f -
            ccmActualHeadSymmetricAutocorrelation (Real.log n) f) := by
  let lo := Real.log n - ccmActualHeadMatchedPrimePolarRadius n
  let hi := Real.log n + ccmActualHeadMatchedPrimePolarRadius n
  let E : ℝ → ℝ := fun h => ccmActualHeadTranslationDefect h f
  have hweight : Continuous fun h : ℝ => Real.exp (h / 2) := by fun_prop
  have hE : Continuous E := by
    dsimp only [E]
    unfold ccmActualHeadTranslationDefect
    exact (((continuous_logTranslationCLM f).sub continuous_const).norm).pow 2
  have hconst : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * E (Real.log n)) volume lo hi :=
    (hweight.mul continuous_const).intervalIntegrable _ _
  have hvar : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * E h) volume lo hi :=
    (hweight.mul hE).intervalIntegrable _ _
  have hmass := integral_exp_half_matchedPrimePolarCell_eq_atomWeight n
  have hfirst : (∫ h in lo..hi,
      Real.exp (h / 2) * E (Real.log n)) =
      criticalMellinAtomWeight n * E (Real.log n) := by
    calc
      _ = E (Real.log n) * ∫ h in lo..hi, Real.exp (h / 2) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro h hh
        ring
      _ = _ := by rw [hmass]; ring
  unfold ccmActualHeadOutgoingPolarSymmetricCell
  change criticalMellinAtomWeight n * E (Real.log n) -
      (∫ h in lo..hi, Real.exp (h / 2) * E h) = _
  calc
    _ = (∫ h in lo..hi, Real.exp (h / 2) * E (Real.log n)) -
        ∫ h in lo..hi, Real.exp (h / 2) * E h := by rw [hfirst]
    _ = ∫ h in lo..hi,
        Real.exp (h / 2) * (E (Real.log n) - E h) := by
      rw [← intervalIntegral.integral_sub hconst hvar]
      apply intervalIntegral.integral_congr
      intro h hh
      ring
    _ = _ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro h hh
      dsimp only [E]
      rw [ccmActualHeadTranslationDefect_sub_eq_two_autocorrelationTransport]
      ring

/-- **Exact boundary-collar localization.** Every matched atom beyond the physical prime cutoff
sees only the part of its symmetric polar cell crossing the aperture boundary. The nominal
all-prime tail is therefore a boundary autocorrelation phenomenon, not a remote prime tail. -/
theorem ccmActualHeadMatchedPrimePolarCellDifference_eq_boundaryCollar_of_cutoff_lt
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) (n : ℕ)
    (hn : Nat.floor (Real.exp (2 * a.1)) < n) :
    criticalMellinAtomWeight n *
          ccmActualHeadTranslationDefect (Real.log n) f.1 -
        ccmActualHeadOutgoingPolarSymmetricCell
          (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f.1 =
      2 * ∫ h in
          (Real.log n - ccmActualHeadMatchedPrimePolarRadius n)..(2 * a.1),
        Real.exp (h / 2) * ccmActualHeadSymmetricAutocorrelation h f.1 := by
  let T := 2 * a.1
  let s := Real.log n
  let ρ := ccmActualHeadMatchedPrimePolarRadius n
  let C : ℝ → ℝ := fun h =>
    Real.exp (h / 2) * ccmActualHeadSymmetricAutocorrelation h f.1
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hexp : Real.exp T < (n : ℝ) :=
    (Nat.floor_lt (Real.exp_pos T).le).mp hn
  have hTs : T < s := by
    dsimp only [T, s]
    exact (Real.lt_log_iff_exp_lt hnpos).mpr hexp
  have hsauto : ccmActualHeadSymmetricAutocorrelation s f.1 = 0 :=
    ccmActualHeadSymmetricAutocorrelation_eq_zero_of_two_aperture_le a f hTs.le
  have hρ : 0 ≤ ρ := ccmActualHeadMatchedPrimePolarRadius_nonneg n
  have hThi : T ≤ s + ρ := by linarith
  have hC : Continuous C := by
    dsimp only [C]
    exact (by fun_prop : Continuous fun h : ℝ => Real.exp (h / 2)).mul
      (continuous_ccmActualHeadSymmetricAutocorrelation f.1)
  have htail : (∫ h in T..(s + ρ), C h) = 0 := by
    calc
      (∫ h in T..(s + ρ), C h) = ∫ _h in T..(s + ρ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro h hh
        rw [uIcc_of_le hThi] at hh
        dsimp only [C]
        rw [ccmActualHeadSymmetricAutocorrelation_eq_zero_of_two_aperture_le a f hh.1]
        ring
      _ = 0 := by simp
  rw [ccmActualHeadMatchedPrimePolarCellDifference_eq_autocorrelationTransport]
  dsimp only [s, ρ] at hsauto ⊢
  rw [hsauto]
  simp only [sub_zero]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hC.intervalIntegrable (μ := volume) (s - ρ) T)
    (hC.intervalIntegrable (μ := volume) T (s + ρ))
  symm at hsplit
  change (∫ h in (s - ρ)..(s + ρ), C h) =
      (∫ h in (s - ρ)..T, C h) + ∫ h in T..(s + ρ), C h at hsplit
  rw [htail, add_zero] at hsplit
  rw [hsplit]

/-- Boundary-overlap packet selected exactly beyond the physical prime cutoff. -/
def ccmActualHeadMatchedBoundaryCollar
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) (n : ℕ) : ℝ :=
  if Nat.floor (Real.exp (2 * a.1)) < n then
    2 * ∫ h in
      (Real.log n - ccmActualHeadMatchedPrimePolarRadius n)..(2 * a.1),
      Real.exp (h / 2) * ccmActualHeadSymmetricAutocorrelation h f.1
  else 0

/-- The boundary collar is precisely the post-cutoff indicator of the intact matched-cell
producer. -/
theorem ccmActualHeadMatchedBoundaryCollar_eq_indicator
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ccmActualHeadMatchedBoundaryCollar a f =
      ({n : ℕ | Nat.floor (Real.exp (2 * a.1)) < n} : Set ℕ).indicator
        (fun n => criticalMellinAtomWeight n *
            ccmActualHeadTranslationDefect (Real.log n) f.1 -
          ccmActualHeadOutgoingPolarSymmetricCell
            (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f.1) := by
  funext n
  by_cases hn : Nat.floor (Real.exp (2 * a.1)) < n
  · rw [Set.indicator_of_mem (show n ∈
      {m : ℕ | Nat.floor (Real.exp (2 * a.1)) < m} by exact hn)]
    unfold ccmActualHeadMatchedBoundaryCollar
    rw [if_pos hn]
    exact
      (ccmActualHeadMatchedPrimePolarCellDifference_eq_boundaryCollar_of_cutoff_lt
        a f n hn).symm
  · rw [Set.indicator_of_notMem (show n ∉
      {m : ℕ | Nat.floor (Real.exp (2 * a.1)) < m} by exact hn)]
    simp [ccmActualHeadMatchedBoundaryCollar, hn]

/-- The whole boundary collar is summable because aperture extinction makes it a subseries of the
already summable intact matched family. -/
theorem summable_ccmActualHeadMatchedBoundaryCollar
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    Summable (ccmActualHeadMatchedBoundaryCollar a f) := by
  rw [ccmActualHeadMatchedBoundaryCollar_eq_indicator]
  exact
    (summable_ccmActualHeadMatchedPrimePolarCellDifference_of_aperture a f).indicator _

/-- A boundary collar vanishes once its matched cell begins at or beyond the physical aperture
diameter. This includes the equality case omitted by the strict remote-cell theorem. -/
theorem ccmActualHeadMatchedBoundaryCollar_eq_zero_of_two_aperture_le_lowerEndpoint
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) (n : ℕ)
    (hsep : 2 * a.1 ≤
      Real.log n - ccmActualHeadMatchedPrimePolarRadius n) :
    ccmActualHeadMatchedBoundaryCollar a f n = 0 := by
  unfold ccmActualHeadMatchedBoundaryCollar
  split_ifs with hn
  · have hint : (∫ h in
        (Real.log n - ccmActualHeadMatchedPrimePolarRadius n)..(2 * a.1),
        Real.exp (h / 2) * ccmActualHeadSymmetricAutocorrelation h f.1) = 0 := by
      calc
        _ = ∫ _h in
            (Real.log n - ccmActualHeadMatchedPrimePolarRadius n)..(2 * a.1),
            (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro h hh
          rw [uIcc_comm, uIcc_of_le hsep] at hh
          change Real.exp (h / 2) * ccmActualHeadSymmetricAutocorrelation h f.1 = 0
          rw [ccmActualHeadSymmetricAutocorrelation_eq_zero_of_two_aperture_le
            a f hh.1]
          ring
        _ = 0 := by simp
    rw [hint, mul_zero]
  · rfl

/-- Nonzero boundary packets necessarily lie beyond the canonical physical cutoff. -/
theorem ccmActualHeadMatchedBoundaryCollar_ne_zero_imp_cutoff_lt
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) (n : ℕ)
    (hne : ccmActualHeadMatchedBoundaryCollar a f n ≠ 0) :
    Nat.floor (Real.exp (2 * a.1)) < n := by
  by_contra hn
  exact hne (by simp [ccmActualHeadMatchedBoundaryCollar, hn])

/-- A nonzero collar packet is equivalent to a matched cell that genuinely crosses the physical
aperture boundary, at least at the level of its necessary support condition. -/
theorem ccmActualHeadMatchedBoundaryCollar_ne_zero_imp_lowerEndpoint_lt_two_aperture
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) (n : ℕ)
    (hne : ccmActualHeadMatchedBoundaryCollar a f n ≠ 0) :
    Real.log n - ccmActualHeadMatchedPrimePolarRadius n < 2 * a.1 := by
  by_contra h
  exact hne
    (ccmActualHeadMatchedBoundaryCollar_eq_zero_of_two_aperture_le_lowerEndpoint
      a f n (le_of_not_gt h))

/-- A nonzero collar index lies in a critical-Mellin-thin arithmetic strip immediately above
the physical exponential boundary. -/
theorem ccmActualHeadMatchedBoundaryCollar_ne_zero_imp_criticalMellin_width
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) (n : ℕ)
    (hne : ccmActualHeadMatchedBoundaryCollar a f n ≠ 0) :
    (n : ℝ) - Real.exp (2 * a.1) <
      (n : ℝ) * criticalMellinAtomWeight n /
        (2 * Real.exp (Real.log n / 2)) := by
  let T := 2 * a.1
  let ρ := ccmActualHeadMatchedPrimePolarRadius n
  have hcut := ccmActualHeadMatchedBoundaryCollar_ne_zero_imp_cutoff_lt a f n hne
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (Nat.zero_lt_of_lt hcut)
  have hratio : 0 < (n : ℝ) / Real.exp T :=
    div_pos hnpos (Real.exp_pos T)
  have hlog := Real.one_sub_inv_le_log_of_pos hratio
  have hlogdiv : Real.log ((n : ℝ) / Real.exp T) = Real.log n - T := by
    rw [Real.log_div (ne_of_gt hnpos) (Real.exp_ne_zero T), Real.log_exp]
  rw [inv_div, hlogdiv] at hlog
  have hquot : ((n : ℝ) - Real.exp T) / n ≤ Real.log n - T := by
    calc
      ((n : ℝ) - Real.exp T) / n = 1 - Real.exp T / n := by
        field_simp
      _ ≤ Real.log n - T := hlog
  have hwidth0 : (n : ℝ) - Real.exp T ≤
      (Real.log n - T) * n :=
    (div_le_iff₀ hnpos).mp hquot
  have hlower :=
    ccmActualHeadMatchedBoundaryCollar_ne_zero_imp_lowerEndpoint_lt_two_aperture
      a f n hne
  have hgap : Real.log n - T < ρ := by
    dsimp only [T, ρ] at hlower ⊢
    linarith
  have hwidth1 : (Real.log n - T) * n < ρ * n :=
    mul_lt_mul_of_pos_right hgap hnpos
  have hρ := ccmActualHeadMatchedPrimePolarRadius_le_weight_div n
  have hwidth2 : ρ * n ≤
      (criticalMellinAtomWeight n /
        (2 * Real.exp (Real.log n / 2))) * n :=
    mul_le_mul_of_nonneg_right hρ hnpos.le
  dsimp only [T, ρ] at hwidth0 hwidth1 hwidth2 ⊢
  calc
    (n : ℝ) - Real.exp (2 * a.1) ≤
        (Real.log n - 2 * a.1) * n := hwidth0
    _ < ccmActualHeadMatchedPrimePolarRadius n * n := hwidth1
    _ ≤ (criticalMellinAtomWeight n /
          (2 * Real.exp (Real.log n / 2))) * n := hwidth2
    _ = (n : ℝ) * criticalMellinAtomWeight n /
          (2 * Real.exp (Real.log n / 2)) := by ring

/-- The critical-Mellin strip width is exactly half of the ordinary von Mangoldt atom. -/
theorem ccmActualHeadMatchedBoundaryCollar_ne_zero_imp_vonMangoldt_width
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) (n : ℕ)
    (hne : ccmActualHeadMatchedBoundaryCollar a f n ≠ 0) :
    (n : ℝ) - Real.exp (2 * a.1) <
      ArithmeticFunction.vonMangoldt n / 2 := by
  have hcut := ccmActualHeadMatchedBoundaryCollar_ne_zero_imp_cutoff_lt a f n hne
  have hn : 0 < n := Nat.zero_lt_of_lt hcut
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hweight := criticalMellinAtomWeight_mul_exp_log_half hn
  have hsquare :
      Real.exp (Real.log n / 2) * Real.exp (Real.log n / 2) = (n : ℝ) := by
    rw [← Real.exp_add]
    rw [show Real.log n / 2 + Real.log n / 2 = Real.log n by ring,
      Real.exp_log hnpos]
  have hnormalize :
      (n : ℝ) * criticalMellinAtomWeight n /
          (2 * Real.exp (Real.log n / 2)) =
        ArithmeticFunction.vonMangoldt n / 2 := by
    calc
      (n : ℝ) * criticalMellinAtomWeight n /
            (2 * Real.exp (Real.log n / 2)) =
          (Real.exp (Real.log n / 2) * Real.exp (Real.log n / 2)) *
              criticalMellinAtomWeight n /
            (2 * Real.exp (Real.log n / 2)) := by rw [hsquare]
      _ = (criticalMellinAtomWeight n * Real.exp (Real.log n / 2)) / 2 := by
        field_simp [Real.exp_ne_zero]
      _ = ArithmeticFunction.vonMangoldt n / 2 := by rw [hweight]
  rw [← hnormalize]
  exact ccmActualHeadMatchedBoundaryCollar_ne_zero_imp_criticalMellin_width
    a f n hne

/-- Logarithmic corollary of the exact von Mangoldt strip width. -/
theorem ccmActualHeadMatchedBoundaryCollar_ne_zero_imp_log_width
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) (n : ℕ)
    (hne : ccmActualHeadMatchedBoundaryCollar a f n ≠ 0) :
    (n : ℝ) - Real.exp (2 * a.1) < Real.log n / 2 := by
  exact lt_of_lt_of_le
    (ccmActualHeadMatchedBoundaryCollar_ne_zero_imp_vonMangoldt_width
      a f n hne)
    (div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (by norm_num))

/-- **Prime-power thin-collar theorem.** A nonzero matched boundary packet can occur only at a
prime power in an additive strip of width `a + 1/2` above the physical boundary `exp (2a)`. -/
theorem ccmActualHeadMatchedBoundaryCollar_ne_zero_imp_primePower_mem_thinStrip
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) (n : ℕ)
    (hne : ccmActualHeadMatchedBoundaryCollar a f n ≠ 0) :
    IsPrimePow n ∧
      Real.exp (2 * a.1) < (n : ℝ) ∧
      (n : ℝ) < Real.exp (2 * a.1) + a.1 + 1 / 2 := by
  have hcut := ccmActualHeadMatchedBoundaryCollar_ne_zero_imp_cutoff_lt a f n hne
  have hn : 0 < n := Nat.zero_lt_of_lt hcut
  have hexp : Real.exp (2 * a.1) < (n : ℝ) :=
    (Nat.floor_lt (Real.exp_pos (2 * a.1)).le).mp hcut
  have hvwidth :=
    ccmActualHeadMatchedBoundaryCollar_ne_zero_imp_vonMangoldt_width a f n hne
  have hvpos : 0 < ArithmeticFunction.vonMangoldt n := by
    nlinarith
  have hprimePower : IsPrimePow n :=
    ArithmeticFunction.vonMangoldt_pos_iff.mp hvpos
  have hlower :=
    ccmActualHeadMatchedBoundaryCollar_ne_zero_imp_lowerEndpoint_lt_two_aperture
      a f n hne
  have hρ := ccmActualHeadMatchedPrimePolarRadius_le_one_of_one_le
    (Nat.one_le_iff_ne_zero.mpr hn.ne')
  have hlog : Real.log n < 2 * a.1 + 1 := by linarith
  have hlogwidth :=
    ccmActualHeadMatchedBoundaryCollar_ne_zero_imp_log_width a f n hne
  refine ⟨hprimePower, hexp, ?_⟩
  linarith

/-- Explicit additive collar containing every possible nonzero post-cutoff matched packet. Its
width is only `a + 1/2`, rather than multiplicative in the physical boundary `exp (2a)`. -/
def ccmActualHeadMatchedThinBoundaryCollarFinset
    (a : SuzukiPositiveAperture) : Finset ℕ :=
  Finset.Ioc (Nat.floor (Real.exp (2 * a.1)))
    (Nat.floor (Real.exp (2 * a.1) + a.1 + 1 / 2))

/-- The boundary collar vanishes outside its explicit additive thin-strip finset. -/
theorem ccmActualHeadMatchedBoundaryCollar_eq_zero_of_not_mem_thinBoundaryCollarFinset
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) (n : ℕ)
    (hn : n ∉ ccmActualHeadMatchedThinBoundaryCollarFinset a) :
    ccmActualHeadMatchedBoundaryCollar a f n = 0 := by
  by_contra hne
  have hcut := ccmActualHeadMatchedBoundaryCollar_ne_zero_imp_cutoff_lt a f n hne
  have hstrip :=
    ccmActualHeadMatchedBoundaryCollar_ne_zero_imp_primePower_mem_thinStrip
      a f n hne
  apply hn
  rw [ccmActualHeadMatchedThinBoundaryCollarFinset, Finset.mem_Ioc]
  exact ⟨hcut, Nat.le_floor hstrip.2.2.le⟩

/-- The summable all-prime collar is in fact the sum over an explicit additive thin strip. -/
theorem tsum_ccmActualHeadMatchedBoundaryCollar_eq_thinBoundaryCollarFinset_sum
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    (∑' n : ℕ, ccmActualHeadMatchedBoundaryCollar a f n) =
      ∑ n ∈ ccmActualHeadMatchedThinBoundaryCollarFinset a,
        ccmActualHeadMatchedBoundaryCollar a f n := by
  rw [tsum_eq_sum (s := ccmActualHeadMatchedThinBoundaryCollarFinset a)
    (ccmActualHeadMatchedBoundaryCollar_eq_zero_of_not_mem_thinBoundaryCollarFinset a f)]

/-- Total local polar mass carried by a finite family of matched symmetric cells. -/
def ccmActualHeadMatchedPolarFiniteBlock
    (F : Finset ℕ) (f : SoninL2) : ℝ :=
  ∑ n ∈ F, ccmActualHeadOutgoingPolarSymmetricCell
    (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f

/-- Autocorrelation mass of a finite family of matched polar cells. Unlike the scalar polar mass,
this quantity retains overlaps and gaps exactly. -/
def ccmActualHeadMatchedPolarAutocorrelationFiniteBlock
    (F : Finset ℕ) (f : SoninL2) : ℝ :=
  ∑ n ∈ F, ∫ h in
      (Real.log n - ccmActualHeadMatchedPrimePolarRadius n)..
      (Real.log n + ccmActualHeadMatchedPrimePolarRadius n),
    Real.exp (h / 2) * ccmActualHeadSymmetricAutocorrelation h f

/-- One matched polar defect cell is its exact scalar mass minus its autocorrelation mass. -/
theorem ccmActualHeadMatchedPolarCell_eq_mass_sub_autocorrelation
    (n : ℕ) (f : SoninL2) :
    ccmActualHeadOutgoingPolarSymmetricCell
        (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f =
      2 * criticalMellinAtomWeight n * ‖f‖ ^ 2 -
        2 * ∫ h in
          (Real.log n - ccmActualHeadMatchedPrimePolarRadius n)..
          (Real.log n + ccmActualHeadMatchedPrimePolarRadius n),
          Real.exp (h / 2) * ccmActualHeadSymmetricAutocorrelation h f := by
  let lo := Real.log n - ccmActualHeadMatchedPrimePolarRadius n
  let hi := Real.log n + ccmActualHeadMatchedPrimePolarRadius n
  let W : ℝ → ℝ := fun h => Real.exp (h / 2)
  let C : ℝ → ℝ := fun h => ccmActualHeadSymmetricAutocorrelation h f
  have hW : Continuous W := by dsimp only [W]; fun_prop
  have hC : Continuous C := continuous_ccmActualHeadSymmetricAutocorrelation f
  have hmass : IntervalIntegrable (fun h => (2 * ‖f‖ ^ 2) * W h)
      volume lo hi := (continuous_const.mul hW).intervalIntegrable _ _
  have hcorr : IntervalIntegrable (fun h => 2 * (W h * C h))
      volume lo hi := (continuous_const.mul (hW.mul hC)).intervalIntegrable _ _
  unfold ccmActualHeadOutgoingPolarSymmetricCell
  rw [show (∫ h in lo..hi,
      Real.exp (h / 2) * ccmActualHeadTranslationDefect h f) =
      ∫ h in lo..hi, (2 * ‖f‖ ^ 2) * W h - 2 * (W h * C h) by
    apply intervalIntegral.integral_congr
    intro h hh
    change Real.exp (h / 2) * ccmActualHeadTranslationDefect h f =
      (2 * ‖f‖ ^ 2) * Real.exp (h / 2) -
        2 * (Real.exp (h / 2) * ccmActualHeadSymmetricAutocorrelation h f)
    rw [ccmActualHeadTranslationDefect_eq_norm_sub_symmetricAutocorrelation]
    ring]
  rw [intervalIntegral.integral_sub hmass hcorr,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_exp_half_matchedPrimePolarCell_eq_atomWeight]
  dsimp only [W, C]
  ring

/-- Finite matched polar mass in scalar-minus-autocorrelation normal form. -/
theorem ccmActualHeadMatchedPolarFiniteBlock_eq_mass_sub_autocorrelation
    (F : Finset ℕ) (f : SoninL2) :
    ccmActualHeadMatchedPolarFiniteBlock F f =
      2 * (∑ n ∈ F, criticalMellinAtomWeight n) * ‖f‖ ^ 2 -
        2 * ccmActualHeadMatchedPolarAutocorrelationFiniteBlock F f := by
  unfold ccmActualHeadMatchedPolarFiniteBlock
    ccmActualHeadMatchedPolarAutocorrelationFiniteBlock
  simp_rw [ccmActualHeadMatchedPolarCell_eq_mass_sub_autocorrelation,
    Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_mul]

/-- Signed failure of canonical matched cells to cover the true outgoing polar interval. This is
the exact seam that must be retained when replacing quantile assembly by local matched cells. -/
def ccmActualHeadMatchedPolarCoverageSeam
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) : ℝ :=
  ccmActualHeadMatchedPolarFiniteBlock
      (Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1)))) f.1 -
    ccmActualHeadOutgoingPolarEnergy a f

/-- Actual restricted-Weil source in finite matched-cell normal form. The coverage seam is exact;
no claim that local symmetric cells form a partition is inserted. -/
theorem ccmRestrictedWeilSourceQuadratic_eq_matchedCoverageSeam
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    let F := Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1)))
    ccmRestrictedWeilSourceQuadratic a u =
      2 * gammaHardyPhaseRate 0 * ‖f‖ ^ 2 +
        ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2) +
        (2 * Real.exp a.1 - criticalMellinPrimeMass (2 * a.1)) *
          ccmActualHeadTranslationDefect (2 * a.1) f.1 +
        ccmActualHeadMatchedPrimePolarFiniteBlock F f.1 +
        ccmActualHeadMatchedPolarCoverageSeam a f := by
  let f := ccmArchimedeanFormToAperture a u
  let F := Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1)))
  rw [← ccmRestrictedWeilActualHeadGammaWallOutgoingProducer_eq_sourceQuadratic]
  unfold ccmRestrictedWeilActualHeadGammaWallOutgoingProducer
  dsimp only
  rw [ccmActualHeadPrimeWallChordEnergy_formDomain]
  have hprime : ccmPrimeTranslationDefectEnergy a f =
      ccmActualHeadMatchedPrimePolarFiniteBlock F f.1 +
        ccmActualHeadMatchedPolarFiniteBlock F f.1 := by
    unfold ccmPrimeTranslationDefectEnergy
      ccmActualHeadMatchedPrimePolarFiniteBlock
      ccmActualHeadMatchedPolarFiniteBlock
    change (∑ n ∈ F, criticalMellinAtomWeight n *
        ccmActualHeadTranslationDefect (Real.log n) f.1) =
      (∑ n ∈ F, (criticalMellinAtomWeight n *
          ccmActualHeadTranslationDefect (Real.log n) f.1 -
        ccmActualHeadOutgoingPolarSymmetricCell
          (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f.1)) +
      ∑ n ∈ F, ccmActualHeadOutgoingPolarSymmetricCell
        (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f.1
    rw [Finset.sum_sub_distrib]
    ring
  rw [hprime]
  unfold ccmActualHeadMatchedPolarCoverageSeam
  dsimp only [F, f]
  ring

/-- **Endpoint/coverage cancellation law.** The completed endpoint coefficient absorbs every
scalar mass in the matched coverage seam. What survives is the universal `4‖f‖²` reserve and the
literal difference between true and locally matched polar autocorrelation masses. -/
theorem ccmActualHeadMatchedEndpoint_add_coverageSeam_eq_autocorrelationSeam
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    (2 * Real.exp a.1 - criticalMellinPrimeMass (2 * a.1)) *
          ccmActualHeadTranslationDefect (2 * a.1) f.1 +
        ccmActualHeadMatchedPolarCoverageSeam a f =
      4 * ‖f‖ ^ 2 +
        2 * (∫ h in Icc (0 : ℝ) (2 * a.1),
          Real.exp (h / 2) * ccmActualHeadSymmetricAutocorrelation h f.1) -
        2 * ccmActualHeadMatchedPolarAutocorrelationFiniteBlock
          (Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1)))) f.1 := by
  let F := Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1)))
  have hmass : (∑ n ∈ F, criticalMellinAtomWeight n) =
      criticalMellinPrimeMass (2 * a.1) := by
    dsimp only [F]
    exact (criticalMellinPrimeMass_eq_atomSum (2 * a.1)).symm
  have hlocal := ccmActualHeadMatchedPolarFiniteBlock_eq_mass_sub_autocorrelation F f.1
  have hout := ccmActualHeadOutgoingPolarEnergy_eq_mass_sub_autocorrelation a f
  have hend := ccmActualHeadTranslationDefect_two_aperture a f
  have hnorm : ‖(f.1 : SoninL2)‖ = ‖f‖ := rfl
  unfold ccmActualHeadMatchedPolarCoverageSeam
  dsimp only [F] at hlocal ⊢
  rw [hend, hlocal, hout, hmass, hnorm]
  ring

/-- **Cancellation-preserving source bridge.** The true source is higher Gamma plus endpoint
reserve, the even matched residual, the signed Suzuki current, and the literal polar coverage
seam. This is the finite hard core exposed by matched-cell aperture extinction. -/
theorem ccmRestrictedWeilSourceQuadratic_eq_matchedSymmetric_sub_suzuki_add_coverageSeam
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    let F := Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1)))
    ccmRestrictedWeilSourceQuadratic a u =
      2 * gammaHardyPhaseRate 0 * ‖f‖ ^ 2 +
        ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2) +
        (2 * Real.exp a.1 - criticalMellinPrimeMass (2 * a.1)) *
          ccmActualHeadTranslationDefect (2 * a.1) f.1 +
        ccmActualHeadMatchedSymmetricFiniteBlock F f.1 -
        ccmActualHeadMatchedSuzukiFiniteBlock F f.1 +
        ccmActualHeadMatchedPolarCoverageSeam a f := by
  rw [ccmRestrictedWeilSourceQuadratic_eq_matchedCoverageSeam]
  rw [ccmActualHeadMatchedPrimePolarFiniteBlock_eq_symmetric_sub_suzuki]
  ring

/-- **Matched autocorrelation-seam normal form.** Scalar prime and polar masses cancel completely.
The RH-bearing source is a finite even-minus-Suzuki matched block plus the exact difference between
the true polar autocorrelation interval and the overlapped/gapped matched-cell autocorrelation.
This is the route-neutral finite hard core exposed by the boundary-collar calculation. -/
theorem ccmRestrictedWeilSourceQuadratic_eq_matchedAutocorrelationSeam
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    let F := Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1)))
    ccmRestrictedWeilSourceQuadratic a u =
      2 * gammaHardyPhaseRate 0 * ‖f‖ ^ 2 +
        ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2) +
        4 * ‖f‖ ^ 2 +
        ccmActualHeadMatchedSymmetricFiniteBlock F f.1 -
        ccmActualHeadMatchedSuzukiFiniteBlock F f.1 +
        2 * (∫ h in Icc (0 : ℝ) (2 * a.1),
          Real.exp (h / 2) * ccmActualHeadSymmetricAutocorrelation h f.1) -
        2 * ccmActualHeadMatchedPolarAutocorrelationFiniteBlock F f.1 := by
  let f := ccmArchimedeanFormToAperture a u
  let F := Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1)))
  have hsource :=
    ccmRestrictedWeilSourceQuadratic_eq_matchedSymmetric_sub_suzuki_add_coverageSeam a u
  have hseam := ccmActualHeadMatchedEndpoint_add_coverageSeam_eq_autocorrelationSeam a f
  dsimp only [f, F] at hsource hseam ⊢
  linear_combination hsource + hseam

/-- **All-prime/physical-cutoff sewing law.** The unconditional all-prime matched `tsum` is the
canonical physical finite block plus exactly one summable boundary collar. No remote arithmetic
tail remains, and no prime beyond the cutoff is discarded silently. -/
theorem tsum_ccmActualHeadMatchedPrimePolarCellDifference_eq_physicalBlock_add_boundaryCollar
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    (∑' n : ℕ, (criticalMellinAtomWeight n *
          ccmActualHeadTranslationDefect (Real.log n) f.1 -
        ccmActualHeadOutgoingPolarSymmetricCell
          (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f.1)) =
      ccmActualHeadMatchedPrimePolarFiniteBlock
          (Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1)))) f.1 +
        ∑' n : ℕ, ccmActualHeadMatchedBoundaryCollar a f n := by
  let M := Nat.floor (Real.exp (2 * a.1))
  let F := Finset.Icc 2 M
  let D : ℕ → ℝ := fun n => criticalMellinAtomWeight n *
      ccmActualHeadTranslationDefect (Real.log n) f.1 -
    ccmActualHeadOutgoingPolarSymmetricCell
      (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f.1
  let I : ℕ → ℝ := fun n => if n ∈ F then D n else 0
  have hI : Summable I := by
    apply summable_of_ne_finset_zero (s := F)
    intro n hn
    simp [I, hn]
  have hC := summable_ccmActualHeadMatchedBoundaryCollar a f
  have hpoint (n : ℕ) : D n = I n + ccmActualHeadMatchedBoundaryCollar a f n := by
    by_cases hn : M < n
    · have hnF : n ∉ F := by
        intro hnmem
        exact (not_lt_of_ge (Finset.mem_Icc.mp hnmem).2) hn
      rw [show I n = 0 by simp [I, hnF]]
      simp only [zero_add]
      dsimp only [D, M] at hn ⊢
      rw [ccmActualHeadMatchedBoundaryCollar, if_pos hn]
      exact
        ccmActualHeadMatchedPrimePolarCellDifference_eq_boundaryCollar_of_cutoff_lt
          a f n hn
    · have hnle : n ≤ M := Nat.le_of_not_gt hn
      by_cases hn2 : 2 ≤ n
      · have hnF : n ∈ F := Finset.mem_Icc.mpr ⟨hn2, hnle⟩
        rw [show I n = D n by simp [I, hnF]]
        simp [ccmActualHeadMatchedBoundaryCollar, M, hn]
      · have hnlt : n < 2 := Nat.lt_of_not_ge hn2
        dsimp only [M] at hn
        interval_cases n <;>
          simp [D, I, F, ccmActualHeadMatchedBoundaryCollar,
            criticalMellinAtomWeight, ccmActualHeadMatchedPrimePolarRadius,
            ccmActualHeadOutgoingPolarSymmetricCell, hn]
  calc
    (∑' n : ℕ, D n) = ∑' n : ℕ,
        (I n + ccmActualHeadMatchedBoundaryCollar a f n) := by
      apply tsum_congr
      exact hpoint
    _ = (∑' n : ℕ, I n) +
        ∑' n : ℕ, ccmActualHeadMatchedBoundaryCollar a f n :=
      hI.tsum_add hC
    _ = (∑ n ∈ F, D n) +
        ∑' n : ℕ, ccmActualHeadMatchedBoundaryCollar a f n := by
      rw [tsum_eq_sum (s := F) (fun n hn => by simp [I, hn])]
      simp [I]
    _ = _ := by rfl

/-- **Finite thin-collar sewing law.** The unconditional all-prime matched family is exactly the
canonical physical block plus a finite sum over prime-power candidates in the additive strip of
width `a + 1/2` immediately above `exp (2a)`. -/
theorem tsum_ccmActualHeadMatchedPrimePolarCellDifference_eq_physicalBlock_add_thinBoundaryCollar
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    (∑' n : ℕ, (criticalMellinAtomWeight n *
          ccmActualHeadTranslationDefect (Real.log n) f.1 -
        ccmActualHeadOutgoingPolarSymmetricCell
          (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f.1)) =
      ccmActualHeadMatchedPrimePolarFiniteBlock
          (Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1)))) f.1 +
        ∑ n ∈ ccmActualHeadMatchedThinBoundaryCollarFinset a,
          ccmActualHeadMatchedBoundaryCollar a f n := by
  rw [
    tsum_ccmActualHeadMatchedPrimePolarCellDifference_eq_physicalBlock_add_boundaryCollar,
    tsum_ccmActualHeadMatchedBoundaryCollar_eq_thinBoundaryCollarFinset_sum]

end RHTower
