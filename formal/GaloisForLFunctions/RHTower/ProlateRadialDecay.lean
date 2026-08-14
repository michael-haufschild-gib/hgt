import GaloisForLFunctions.RHTower.ProlatePolarSource
import GaloisForLFunctions.HTGeometry.HalfDensityEnvelopePolarCharge

/-!
# The exact radial mode decays like `1/x`, and its channels are square-summable

The two-branch representation of the dilated mode has amplitudes bounded by `M x^{-1/2}`, so the
mode itself obeys

```text
|R (k x)| ≤ 600 M / (√c · k · x).
```

Two consequences the source estimate needs.  First, the mode is square integrable on every ray
away from the endpoint, with an explicit tail.  Second, the `k`-th channel source in the
logarithmic variable has squared mass at most `C² / k²`, so the channels' masses are summable —
the exact size input a Bessel/Gram argument for the radial sum consumes.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.RHTower

/-- The decay constant of the exact radial mode. -/
def radialDecayConstant (s c : ℝ) (R DR : ℝ → ℝ) : ℝ :=
  600 * exactEnergyBudget s c R DR 2 / Real.sqrt c

theorem radialDecayConstant_nonneg {s c : ℝ} {R DR : ℝ → ℝ} (hc : 0 < c) :
    0 ≤ radialDecayConstant s c R DR := by
  have h1 : (0 : ℝ) ≤ exactEnergyBudget s c R DR 2 := Real.sqrt_nonneg _
  have h2 : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc
  rw [radialDecayConstant]
  positivity

/-- **The dilated exact mode decays like `1 / (k x)`.**  Both exponential branches have unit
modulus, so the mode is bounded by the sum of the two amplitude bounds. -/
theorem abs_radialProlate_dilate_le {s c k x : ℝ} {R DR DDR : ℝ → ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hk : 1 ≤ k) (hx : 1 ≤ x) (hkx2 : 2 ≤ k * x)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    |R (k * x)| ≤ radialDecayConstant s c R DR / (k * x) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hkx1 : (1 : ℝ) < k * x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsc : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc
  set M : ℝ := exactEnergyBudget s c R DR 2 with hMdef
  have hM : (0 : ℝ) ≤ M := Real.sqrt_nonneg _
  have heq := sqrt_mul_radialProlate_dilate_eq_branches (R := R) (DR := DR) hs1 hc hk hkx1
  have h1 := abs_exactBranchAmp_le (DDR := DDR) (eps := 1) hs0 hs1 hc hk hx hkx2
    (by norm_num) hR hDR hode
  have h2 := abs_exactBranchAmp_le (DDR := DDR) (eps := -1) hs0 hs1 hc hk hx hkx2
    (by norm_num) hR hDR hode
  rw [← hMdef] at h1 h2
  have hnorm1 : ‖Complex.exp (Complex.I *
      ((1 * (c * k) * dilatedPhase s k x : ℝ) : ℂ))‖ = 1 := by
    rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I _
  have hnorm2 : ‖Complex.exp (Complex.I *
      ((-1 * (c * k) * dilatedPhase s k x : ℝ) : ℂ))‖ = 1 := by
    rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I _
  have hbound : |Real.sqrt x * R (k * x)|
      ≤ 300 * M / (Real.sqrt c * k) / Real.sqrt x + 300 * M / (Real.sqrt c * k) / Real.sqrt x := by
    have hc1 : ‖((Real.sqrt x * R (k * x) : ℝ) : ℂ)‖ = |Real.sqrt x * R (k * x)| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [← hc1, heq]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul, hnorm1, hnorm2, mul_one, mul_one]
    exact add_le_add h1 h2
  have habs : |Real.sqrt x * R (k * x)| = Real.sqrt x * |R (k * x)| := by
    rw [abs_mul, abs_of_nonneg hsx.le]
  have hsum : 300 * M / (Real.sqrt c * k) / Real.sqrt x
      + 300 * M / (Real.sqrt c * k) / Real.sqrt x
      = 600 * M / (Real.sqrt c * k) / Real.sqrt x := by ring
  rw [habs, hsum] at hbound
  have hsxsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hkey : x * |R (k * x)| ≤ 600 * M / (Real.sqrt c * k) := by
    calc x * |R (k * x)| = Real.sqrt x * (Real.sqrt x * |R (k * x)|) := by
          rw [← mul_assoc, hsxsq]
      _ ≤ Real.sqrt x * (600 * M / (Real.sqrt c * k) / Real.sqrt x) :=
          mul_le_mul_of_nonneg_left hbound hsx.le
      _ = 600 * M / (Real.sqrt c * k) := by
          field_simp
  have hkey2 : x * |R (k * x)| * (Real.sqrt c * k) ≤ 600 * M := by
    rw [← le_div_iff₀ (by positivity : (0 : ℝ) < Real.sqrt c * k)]
    exact hkey
  rw [radialDecayConstant, ← hMdef, div_div, le_div_iff₀ (by positivity)]
  calc |R (k * x)| * (Real.sqrt c * (k * x)) = x * |R (k * x)| * (Real.sqrt c * k) := by ring
    _ ≤ 600 * M := hkey2

/-- **The exact radial mode decays like `1 / x`.** -/
theorem abs_radialProlate_le {s c y : ℝ} {R DR DDR : ℝ → ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hy : 2 ≤ y)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    |R y| ≤ radialDecayConstant s c R DR / y := by
  have h := abs_radialProlate_dilate_le (k := 1) (x := y) (DDR := DDR) hs0 hs1 hc le_rfl
    (by linarith) (by linarith) hR hDR hode
  simpa using h

/-! ### The channel masses -/

/-- **The channel source decays exponentially.**  In the logarithmic variable the `1/x` decay of
the mode becomes a half-density factor. -/
theorem abs_channelSource_le {s c k u : ℝ} {R DR DDR : ℝ → ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hk : 2 ≤ k) (hu : 0 ≤ u)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    |channelSource k R u| ≤ radialDecayConstant s c R DR / k * Real.exp (-u / 2) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_two hk
  have hexp : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp hu
  have hexp0 : (0 : ℝ) < Real.exp u := Real.exp_pos u
  have hkx : 2 ≤ k * Real.exp u := by nlinarith
  have hdec := abs_radialProlate_dilate_le (k := k) (x := Real.exp u) (DDR := DDR) hs0 hs1 hc
    (by linarith) hexp hkx hR hDR hode
  have hE : Real.exp u = Real.exp (u / 2) * Real.exp (u / 2) := by
    rw [← Real.exp_add]
    ring_nf
  have hsqrt : Real.sqrt (Real.exp u) = Real.exp (u / 2) := by
    rw [hE]
    exact Real.sqrt_mul_self (Real.exp_pos _).le
  have hEn : Real.exp (-u / 2) = 1 / Real.exp (u / 2) := by
    rw [show (-u / 2 : ℝ) = -(u / 2) by ring, Real.exp_neg]
    ring
  have hne : Real.exp (u / 2) ≠ 0 := ne_of_gt (Real.exp_pos _)
  rw [channelSource, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), hsqrt]
  calc Real.exp (u / 2) * |R (k * Real.exp u)|
      ≤ Real.exp (u / 2) * (radialDecayConstant s c R DR / (k * Real.exp u)) :=
        mul_le_mul_of_nonneg_left hdec (Real.exp_pos _).le
    _ = radialDecayConstant s c R DR / k * Real.exp (-u / 2) := by
        rw [hE, hEn]
        field_simp

/-- **The `k`-th channel has squared mass at most `C² / k²`.** -/
theorem integral_channelSource_sq_le {s c k : ℝ} {R DR DDR : ℝ → ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hk : 2 ≤ k)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    IntegrableOn (fun u : ℝ => channelSource k R u ^ 2) (Ioi (0 : ℝ))
      ∧ (∫ u in Ioi (0 : ℝ), channelSource k R u ^ 2)
        ≤ (radialDecayConstant s c R DR / k) ^ 2 := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_two hk
  have hC : (0 : ℝ) ≤ radialDecayConstant s c R DR := radialDecayConstant_nonneg hc
  set C : ℝ := radialDecayConstant s c R DR with hCdef
  have hRc : Continuous R := continuous_iff_continuousAt.mpr fun u => (hR u).continuousAt
  have hcont : Continuous (fun u : ℝ => channelSource k R u ^ 2) := by
    rw [show (fun u : ℝ => channelSource k R u ^ 2)
        = fun u : ℝ => (Real.sqrt (Real.exp u) * R (k * Real.exp u)) ^ 2 from rfl]
    exact (((Real.continuous_sqrt.comp Real.continuous_exp).mul
      (hRc.comp (continuous_const.mul Real.continuous_exp))).pow 2)
  have hmaj : IntegrableOn (fun u : ℝ => (C / k) ^ 2 * Real.exp (-u)) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_neg_Ioi 0).const_mul _
  have hpt : ∀ u ∈ Ioi (0 : ℝ), ‖channelSource k R u ^ 2‖ ≤ (C / k) ^ 2 * Real.exp (-u) := by
    intro u hu
    have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
    have h := abs_channelSource_le (DDR := DDR) hs0 hs1 hc hk hu0 hR hDR hode
    rw [← hCdef] at h
    have hnn : (0 : ℝ) ≤ |channelSource k R u| := abs_nonneg _
    have hbnd : (0 : ℝ) ≤ C / k * Real.exp (-u / 2) := by positivity
    have hsq : channelSource k R u ^ 2 ≤ (C / k * Real.exp (-u / 2)) ^ 2 := by
      have := abs_le_abs h (by linarith [abs_nonneg (channelSource k R u)])
      nlinarith [sq_abs (channelSource k R u), h, hnn, hbnd]
    have hexpsq : (Real.exp (-u / 2)) ^ 2 = Real.exp (-u) := by
      rw [sq, ← Real.exp_add]
      ring_nf
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc channelSource k R u ^ 2 ≤ (C / k * Real.exp (-u / 2)) ^ 2 := hsq
      _ = (C / k) ^ 2 * Real.exp (-u) := by rw [mul_pow, hexpsq]
  have hint : IntegrableOn (fun u : ℝ => channelSource k R u ^ 2) (Ioi (0 : ℝ)) := by
    refine Integrable.mono' hmaj hcont.aestronglyMeasurable.restrict ?_
    exact (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hpt)
  refine ⟨hint, ?_⟩
  have hle : (∫ u in Ioi (0 : ℝ), channelSource k R u ^ 2)
      ≤ ∫ u in Ioi (0 : ℝ), (C / k) ^ 2 * Real.exp (-u) := by
    refine integral_mono_ae hint hmaj ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    have := hpt u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at this
    exact this
  have hval : (∫ u in Ioi (0 : ℝ), (C / k) ^ 2 * Real.exp (-u)) = (C / k) ^ 2 := by
    rw [integral_const_mul, integral_exp_neg_Ioi]
    simp
  rw [hval] at hle
  exact hle

/-- **The channel masses are summable.**  The `k`-th channel contributes `O(1/k²)`, so the total
mass of the exterior channels is finite — the size input a Gram argument for the radial sum
consumes. -/
theorem summable_channelSource_sq_bound {s c : ℝ} {R DR : ℝ → ℝ} :
    Summable (fun j : ℕ => (radialDecayConstant s c R DR / (2 + (j : ℝ))) ^ 2) := by
  set C : ℝ := radialDecayConstant s c R DR with hCdef
  have hbase : Summable (fun n : ℕ => C ^ 2 * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _
  have hshift : Summable (fun j : ℕ => C ^ 2 * (1 / ((j : ℝ) + 2) ^ 2)) := by
    refine ((summable_nat_add_iff 2).mpr hbase).congr fun j => ?_
    push_cast
    ring_nf
  refine hshift.congr fun j => ?_
  rw [div_pow, show (2 + (j : ℝ)) = ((j : ℝ) + 2) by ring]
  ring

/-! ### The unconditional per-channel polar charge -/

theorem continuous_channelSource {k : ℝ} {R : ℝ → ℝ} (hRc : Continuous R) :
    Continuous (channelSource k R) := by
  rw [show channelSource k R = fun u : ℝ => Real.sqrt (Real.exp u) * R (k * Real.exp u) from rfl]
  exact (Real.continuous_sqrt.comp Real.continuous_exp).mul
    (hRc.comp (continuous_const.mul Real.continuous_exp))

/-- **`(18)` for every exterior channel of the exact radial mode, unconditionally.**  The half
density envelope of the channel discharges every integrability hypothesis of the abstract polar
estimate, and the channel primitive bound supplies the constant.  Nothing beyond the radial
differential equation is assumed. -/
theorem abs_polarCharge_channelSource_le_of_ode {s c k a : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 1 ≤ c) (hk : 2 ≤ k) (ha : 0 ≤ a)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    |HTGeometry.polarCharge (channelSource k R) a|
      ≤ 4 * (4500 * exactEnergyBudget s c R DR 2 / (Real.sqrt c * (c * k ^ 2)))
            * (radialDecayConstant s c R DR / k)
        + 4 * (radialDecayConstant s c R DR / k) ^ 2 := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_two hk
  have hRc : Continuous R := continuous_iff_continuousAt.mpr fun u => (hR u).continuousAt
  have hK : (0 : ℝ) ≤ radialDecayConstant s c R DR / k :=
    div_nonneg (radialDecayConstant_nonneg hc0) hk0.le
  have hcont := continuous_channelSource (k := k) hRc
  exact HTGeometry.abs_polarCharge_le_of_envelope hcont.measurable
    (fun x y => HTGeometry.intervalIntegrable_expHalf_mul hcont x y) ha hK
    (fun u hu => abs_channelSource_le (DDR := DDR) hs0 hs1 hc0 hk hu hR hDR hode)
    (abs_halfLineExpPrimitive_channelSource_le (DDR := DDR) hs0 hs1 hc hk hR hDR hode)

end GaloisForLFunctions.RHTower

