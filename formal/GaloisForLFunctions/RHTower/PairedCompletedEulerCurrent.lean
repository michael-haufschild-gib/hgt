import GaloisForLFunctions.RHTower.PacketAutocorrelationLaplace
import GaloisForLFunctions.HTGeometry.DigammaGaussSeries

/-!
# The completed paired Euler value is one Gauss-resolvent form minus one critical current

The paired quadratic form of the completed critical value function

```text
L(w) = 1/(w+1/2) + 1/(w-1/2) - (log π)/2 + ψ(1/4+w/2)/2
        - ∑_{m≥2} Λ(m) m^{-1/2} e^{-w log m}
```

on a finite real damped-exponential core with all real parts above `1/2` equals

```text
8 ( ⟨y, D_Gauss y⟩ - ∫_0^∞ E_crit(h) C_y'(h) dh ),
```

where `D_Gauss` is the compensated digamma resolvent form and `E_crit` is the cumulative completed
critical error.  Every individual prime and prime power has disappeared into the single cumulative
source.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry MeasureTheory Set Complex Filter
open scoped BigOperators Topology

noncomputable section

variable {n : ℕ}

/-! ## The paired quadratic of a convergent series of value functions -/

theorem pairedTransform_eq_linear (g : ℂ → ℂ) (u v : ℂ) :
    pairedTransform g u v
      = 2 * ((1 / (u + (starRingEnd ℂ) v) - 1 / (u + v)) * g u
          + (1 / (u + (starRingEnd ℂ) v)) * (starRingEnd ℂ) (g v)
          + (-(1 / (u + v))) * g v).re := by
  unfold pairedTransform
  congr 2
  ring

theorem hasSum_pairedTransform {ι : Type*} (g : ι → ℂ → ℂ) (G : ℂ → ℂ) (u v : ℂ)
    (hu : HasSum (fun i => g i u) (G u)) (hv : HasSum (fun i => g i v) (G v)) :
    HasSum (fun i => pairedTransform (g i) u v) (pairedTransform G u v) := by
  have hconj : HasSum (fun i => (starRingEnd ℂ) (g i v)) ((starRingEnd ℂ) (G v)) :=
    Complex.hasSum_conj'.mpr hv
  have hlin : HasSum
      (fun i => (1 / (u + (starRingEnd ℂ) v) - 1 / (u + v)) * g i u
        + (1 / (u + (starRingEnd ℂ) v)) * (starRingEnd ℂ) (g i v)
        + (-(1 / (u + v))) * g i v)
      ((1 / (u + (starRingEnd ℂ) v) - 1 / (u + v)) * G u
        + (1 / (u + (starRingEnd ℂ) v)) * (starRingEnd ℂ) (G v)
        + (-(1 / (u + v))) * G v) :=
    ((hu.mul_left _).add (hconj.mul_left _)).add (hv.mul_left _)
  have hre := (Complex.hasSum_re hlin).mul_left 2
  simpa only [pairedTransform_eq_linear] using hre

theorem hasSum_pairedQuadratic {ι : Type*} {w : Fin n → ℂ} (r : Fin n → ℝ)
    (g : ι → ℂ → ℂ) (G : ℂ → ℂ) (hG : ∀ j, HasSum (fun i => g i (w j)) (G (w j))) :
    HasSum (fun i => pairedQuadratic w r (g i)) (pairedQuadratic w r G) := by
  unfold pairedQuadratic
  refine hasSum_sum fun j _ => hasSum_sum fun k _ => ?_
  exact (hasSum_pairedTransform g G (w j) (w k) (hG j) (hG k)).mul_left _

/-! ## Real forms of the two infinite-aperture currents -/

/-- The prime half of the infinite-aperture pairing, in real form. -/
def primeAutocorrCurrentReal (w : Fin n → ℂ) (r : Fin n → ℝ) : ℝ :=
  ∑' m : ℕ, criticalMellinAtomWeight m * packetAutocorrelation w r (Real.log m)

/-- The cumulative critical current, in real form. -/
def criticalCurrentIntegralReal (w : Fin n → ℂ) (r : Fin n → ℝ) : ℝ :=
  ∫ h in Ioi (0 : ℝ), criticalMellinCompletedError h * packetAutocorrelationDeriv w r h

theorem summable_primeAutocorrReal {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ)
    {α : ℝ} (hα : ∀ k, α ≤ (w k).re) (hα2 : 1 / 2 < α) :
    Summable (fun m : ℕ => criticalMellinAtomWeight m * packetAutocorrelation w r (Real.log m)) := by
  have hmaj : Summable (fun k : ℕ => autocorrBound w r *
      (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1 / 2 + α)))) :=
    (GaloisForLFunctions.HTGeometry.summable_vonMangoldt_rpow
      (σ := 1 / 2 + α) (by linarith)).mul_left _
  refine Summable.of_norm_bounded hmaj fun k => ?_
  have h := norm_primeTerm_le hw r hα k
  rw [norm_mul, Complex.norm_real, autocorrTest, Complex.norm_real] at h
  rw [norm_mul]
  exact h

theorem primeAutocorrCurrent_eq_ofReal (w : Fin n → ℂ) (r : Fin n → ℝ) :
    primeAutocorrCurrent w r = ((primeAutocorrCurrentReal w r : ℝ) : ℂ) := by
  rw [primeAutocorrCurrentReal, Complex.ofReal_tsum, primeAutocorrCurrent]
  refine tsum_congr fun m => ?_
  rw [autocorrTest]
  push_cast
  ring

theorem criticalCurrentIntegral_eq_ofReal (w : Fin n → ℂ) (r : Fin n → ℝ) :
    (∫ h in Ioi (0 : ℝ), criticalCurrent w r h)
      = ((criticalCurrentIntegralReal w r : ℝ) : ℂ) := by
  have hof : (∫ h in Ioi (0 : ℝ),
        ((criticalMellinCompletedError h * packetAutocorrelationDeriv w r h : ℝ) : ℂ))
      = ((∫ h in Ioi (0 : ℝ),
        criticalMellinCompletedError h * packetAutocorrelationDeriv w r h : ℝ) : ℂ) :=
    integral_ofReal
  rw [criticalCurrentIntegralReal, ← hof]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  rw [criticalCurrent, autocorrTestDeriv]
  push_cast
  ring

/-- **Equation `(7)` in real form.** -/
theorem polar_sub_prime_real {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ)
    {α : ℝ} (hα : ∀ k, α ≤ (w k).re) (hα2 : 1 / 2 < α) :
    polarAutocorrCurrentReal w r - primeAutocorrCurrentReal w r
      = -criticalCurrentIntegralReal w r := by
  have h := polar_sub_prime_autocorrCurrent hw r hα hα2
  rw [polarAutocorrCurrent_eq_ofReal, primeAutocorrCurrent_eq_ofReal,
    criticalCurrentIntegral_eq_ofReal] at h
  exact_mod_cast h

/-! ## The two value-function series -/

/-- The compensated Gauss-resolvent value function `1/(2(m+1)) - 1/(z + 2m + 1/2)`. -/
def gaussResolventValue (m : ℕ) (z : ℂ) : ℂ :=
  ((1 / (2 * ((m : ℝ) + 1)) : ℝ) : ℂ)
    + ((-1 : ℝ) : ℂ) / (z + ((2 * (m : ℝ) + 1 / 2 : ℝ) : ℂ))

/-- The prime lag value function `-Λ(m) m^{-1/2} e^{-z log m}`. -/
def primeLagValue (m : ℕ) (z : ℂ) : ℂ :=
  -(criticalMellinAtomWeight m : ℂ) * Complex.exp (-((Real.log m : ℝ) : ℂ) * z)

theorem one_div_two_mul (Y : ℂ) : (1 : ℂ) / (2 * Y) = (1 / 2 : ℂ) * (1 / Y) := by
  rw [one_div, one_div, mul_inv]
  ring

theorem gaussResolventValue_sub (m : ℕ) (z : ℂ) :
    gaussResolventValue m z
      = ((1 / (2 * ((m : ℝ) + 1)) : ℝ) : ℂ)
        - (1 : ℂ) / (z + ((2 * (m : ℝ) + 1 / 2 : ℝ) : ℂ)) := by
  unfold gaussResolventValue
  push_cast
  ring

theorem gaussResolventValue_eq (m : ℕ) (z : ℂ) :
    gaussResolventValue m z
      = (1 / 2 : ℂ) * gaussDigammaSeriesTerm (((1 / 4 : ℝ) : ℂ) + z / 2) m := by
  rw [gaussResolventValue_sub, gaussDigammaSeriesTerm, mul_sub]
  congr 1
  · rw [← one_div_two_mul ((m : ℂ) + 1)]
    push_cast
    ring
  · rw [← one_div_two_mul (((1 / 4 : ℝ) : ℂ) + z / 2 + (m : ℂ))]
    congr 1
    push_cast
    ring

theorem hasSum_gaussResolventValue {z : ℂ} (hz : 0 < (((1 / 4 : ℝ) : ℂ) + z / 2).re) :
    HasSum (fun m : ℕ => gaussResolventValue m z)
      ((1 / 2 : ℂ) * Complex.digamma (((1 / 4 : ℝ) : ℂ) + z / 2)
        + (((Real.eulerMascheroniConstant / 2 : ℝ)) : ℂ)) := by
  have hsum := summable_gaussDigammaSeriesTerm hz
  have htsum := digamma_eq_neg_euler_add_tsum_gauss hz
  have hbase : HasSum (gaussDigammaSeriesTerm (((1 / 4 : ℝ) : ℂ) + z / 2))
      (Complex.digamma (((1 / 4 : ℝ) : ℂ) + z / 2)
        + (Real.eulerMascheroniConstant : ℂ)) := by
    have h := hsum.hasSum
    rw [show (∑' m : ℕ, gaussDigammaSeriesTerm (((1 / 4 : ℝ) : ℂ) + z / 2) m)
        = Complex.digamma (((1 / 4 : ℝ) : ℂ) + z / 2) + (Real.eulerMascheroniConstant : ℂ) from by
      rw [htsum]; ring] at h
    exact h
  have h2 := hbase.mul_left (1 / 2 : ℂ)
  have hval : (1 / 2 : ℂ) * (Complex.digamma (((1 / 4 : ℝ) : ℂ) + z / 2)
        + (Real.eulerMascheroniConstant : ℂ))
      = (1 / 2 : ℂ) * Complex.digamma (((1 / 4 : ℝ) : ℂ) + z / 2)
        + (((Real.eulerMascheroniConstant / 2 : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hval] at h2
  have hfun : (fun m : ℕ => gaussResolventValue m z)
      = fun m : ℕ => (1 / 2 : ℂ) * gaussDigammaSeriesTerm (((1 / 4 : ℝ) : ℂ) + z / 2) m :=
    funext fun m => gaussResolventValue_eq m z
  rw [hfun]
  exact h2

/-! ## Summability of the prime lag series -/

theorem norm_primeLagValue_le (m : ℕ) (z : ℂ) :
    ‖primeLagValue m z‖
      ≤ ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-(1 / 2 + z.re)) := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    simp [primeLagValue, criticalMellinAtomWeight]
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hwt : |criticalMellinAtomWeight m| = criticalMellinAtomWeight m :=
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hmR.le _)
      ArithmeticFunction.vonMangoldt_nonneg)
  have hexpNorm : ‖Complex.exp (-((Real.log m : ℝ) : ℂ) * z)‖ = (m : ℝ) ^ (-z.re) := by
    rw [Complex.norm_exp]
    have hre : (-((Real.log m : ℝ) : ℂ) * z).re = -(z.re * Real.log m) := by
      rw [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hre, Real.rpow_def_of_pos hmR]
    congr 1
    ring
  have hsplit : (m : ℝ) ^ (-1 / 2 : ℝ) * (m : ℝ) ^ (-z.re) = (m : ℝ) ^ (-(1 / 2 + z.re)) := by
    rw [← Real.rpow_add hmR]
    congr 1
    ring
  rw [primeLagValue, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, hwt, hexpNorm,
    criticalMellinAtomWeight, ← hsplit]
  exact le_of_eq (by ring)

theorem summable_primeLagValue {z : ℂ} (hz : 1 / 2 < z.re) :
    Summable (fun m : ℕ => primeLagValue m z) := by
  have hmaj : Summable (fun m : ℕ =>
      ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-(1 / 2 + z.re))) :=
    GaloisForLFunctions.HTGeometry.summable_vonMangoldt_rpow
      (σ := 1 / 2 + z.re) (by linarith)
  exact Summable.of_norm_bounded hmaj fun m => norm_primeLagValue_le m z

/-! ## The completed critical value function -/

def polarResolventValueA (z : ℂ) : ℂ := ((1 : ℝ) : ℂ) / (z + ((1 / 2 : ℝ) : ℂ))

def polarResolventValueB (z : ℂ) : ℂ := ((1 : ℝ) : ℂ) / (z + ((-(1 / 2) : ℝ) : ℂ))

def logPiValue (_z : ℂ) : ℂ := ((-(Real.log Real.pi) / 2 : ℝ) : ℂ)

def digammaHalfValue (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * Complex.digamma (((1 / 4 : ℝ) : ℂ) + z / 2)

def primeLagSeries (z : ℂ) : ℂ := ∑' m : ℕ, primeLagValue m z

/-- The completed critical value function `L` of the card. -/
def completedCriticalValue (z : ℂ) : ℂ :=
  polarResolventValueA z + polarResolventValueB z + logPiValue z + digammaHalfValue z
    + primeLagSeries z

/-- The compensated Gauss-resolvent quadratic value `⟨y, D_Gauss y⟩`. -/
def gaussResolventQuadratic (w : Fin n → ℂ) (r : Fin n → ℝ) : ℝ :=
  -((Real.log Real.pi + Real.eulerMascheroniConstant) / 2) * packetEnergy w r
    + ∑' m : ℕ, ((1 / (2 * ((m : ℝ) + 1))) * packetEnergy w r
        - packetResolventPairing w r (2 * (m : ℝ) + 1 / 2))


/-! ## The paired quadratic of each piece -/

theorem pairedQuadratic_polarResolventValueA {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) :
    pairedQuadratic w r polarResolventValueA = 8 * packetResolventPairing w r (1 / 2) := by
  have hc : ∀ j, w j + ((1 / 2 : ℝ) : ℂ) ≠ 0 := by
    intro j h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
    have := hw j
    linarith
  calc pairedQuadratic w r polarResolventValueA
      = 8 * (1 : ℝ) * packetResolventPairing w r (1 / 2) := paired_resolvent_law hw r 1 hc
    _ = 8 * packetResolventPairing w r (1 / 2) := by ring

theorem pairedQuadratic_polarResolventValueB {w : Fin n → ℂ} (hhalf : ∀ j, 1 / 2 < (w j).re)
    (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ) :
    pairedQuadratic w r polarResolventValueB
      = 8 * packetResolventPairing w r (-(1 / 2)) := by
  have hc : ∀ j, w j + ((-(1 / 2) : ℝ) : ℂ) ≠ 0 := by
    intro j h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
    have := hhalf j
    linarith
  calc pairedQuadratic w r polarResolventValueB
      = 8 * (1 : ℝ) * packetResolventPairing w r (-(1 / 2)) := paired_resolvent_law hw r 1 hc
    _ = 8 * packetResolventPairing w r (-(1 / 2)) := by ring

theorem pairedQuadratic_logPiValue {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ) :
    pairedQuadratic w r logPiValue
      = 8 * (-(Real.log Real.pi) / 2) * packetEnergy w r :=
  paired_const_law hw r _

theorem pairedQuadratic_gaussResolventValue {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) (m : ℕ) :
    pairedQuadratic w r (gaussResolventValue m)
      = 8 * ((1 / (2 * ((m : ℝ) + 1))) * packetEnergy w r
          - packetResolventPairing w r (2 * (m : ℝ) + 1 / 2)) := by
  have hc : ∀ j, w j + ((2 * (m : ℝ) + 1 / 2 : ℝ) : ℂ) ≠ 0 := by
    intro j h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
    have := hw j
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hadd : pairedQuadratic w r (gaussResolventValue m)
      = pairedQuadratic w r (fun _ => ((1 / (2 * ((m : ℝ) + 1)) : ℝ) : ℂ))
        + pairedQuadratic w r
          (fun z => ((-1 : ℝ) : ℂ) / (z + ((2 * (m : ℝ) + 1 / 2 : ℝ) : ℂ))) :=
    pairedQuadratic_add w r _ _
  rw [hadd, paired_const_law hw r, paired_resolvent_law hw r (-1) hc]
  ring

theorem pairedQuadratic_primeLagValue {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) (m : ℕ) :
    pairedQuadratic w r (primeLagValue m)
      = -8 * criticalMellinAtomWeight m * packetAutocorrelation w r (Real.log m) :=
  paired_lag_law hw r _ _

/-! ## The completed identity -/

set_option maxHeartbeats 1000000 in
/-- **Equation `(10)`.**  The complete absolute-Euler paired Xi value is one compensated
Gauss-resolvent form minus one cumulative critical-error current. -/
theorem paired_completedCriticalValue {w : Fin n → ℂ} (r : Fin n → ℝ) {α : ℝ}
    (hα : ∀ k, α ≤ (w k).re) (hα2 : 1 / 2 < α) :
    pairedQuadratic w r completedCriticalValue
      = 8 * (gaussResolventQuadratic w r - criticalCurrentIntegralReal w r) := by
  have hhalf : ∀ j, 1 / 2 < (w j).re := fun j => lt_of_lt_of_le hα2 (hα j)
  have hw : ∀ j, 0 < (w j).re := fun j => lt_trans (by norm_num) (hhalf j)
  -- the four algebraic splittings
  have e1 : pairedQuadratic w r completedCriticalValue
      = pairedQuadratic w r (fun z => polarResolventValueA z + polarResolventValueB z
          + logPiValue z + digammaHalfValue z) + pairedQuadratic w r primeLagSeries :=
    pairedQuadratic_add w r _ _
  have e2 : pairedQuadratic w r (fun z => polarResolventValueA z + polarResolventValueB z
        + logPiValue z + digammaHalfValue z)
      = pairedQuadratic w r (fun z => polarResolventValueA z + polarResolventValueB z
          + logPiValue z) + pairedQuadratic w r digammaHalfValue :=
    pairedQuadratic_add w r _ _
  have e3 : pairedQuadratic w r (fun z => polarResolventValueA z + polarResolventValueB z
        + logPiValue z)
      = pairedQuadratic w r (fun z => polarResolventValueA z + polarResolventValueB z)
        + pairedQuadratic w r logPiValue :=
    pairedQuadratic_add w r _ _
  have e4 : pairedQuadratic w r (fun z => polarResolventValueA z + polarResolventValueB z)
      = pairedQuadratic w r polarResolventValueA + pairedQuadratic w r polarResolventValueB :=
    pairedQuadratic_add w r _ _
  -- the digamma piece
  have hzpos : ∀ j, 0 < (((1 / 4 : ℝ) : ℂ) + (w j) / 2).re := by
    intro j
    have := hw j
    simp only [Complex.add_re, Complex.ofReal_re, Complex.div_re]
    norm_num
    nlinarith [this, Complex.normSq_pos.mpr (by norm_num : (2 : ℂ) ≠ 0)]
  have hGaussSum : ∀ j, HasSum (fun m : ℕ => gaussResolventValue m (w j))
      (digammaHalfValue (w j) + ((Real.eulerMascheroniConstant / 2 : ℝ) : ℂ)) :=
    fun j => hasSum_gaussResolventValue (hzpos j)
  have hGaussPaired := hasSum_pairedQuadratic r gaussResolventValue
    (fun z => digammaHalfValue z + ((Real.eulerMascheroniConstant / 2 : ℝ) : ℂ)) hGaussSum
  have hQ4 : pairedQuadratic w r
        (fun z => digammaHalfValue z + ((Real.eulerMascheroniConstant / 2 : ℝ) : ℂ))
      = pairedQuadratic w r digammaHalfValue
        + 8 * (Real.eulerMascheroniConstant / 2) * packetEnergy w r := by
    rw [pairedQuadratic_add w r digammaHalfValue
      (fun _ => ((Real.eulerMascheroniConstant / 2 : ℝ) : ℂ)), paired_const_law hw r]
  rw [hQ4] at hGaussPaired
  have hGaussTsum : (∑' m : ℕ, pairedQuadratic w r (gaussResolventValue m))
      = pairedQuadratic w r digammaHalfValue
        + 8 * (Real.eulerMascheroniConstant / 2) * packetEnergy w r := hGaussPaired.tsum_eq
  have hGaussTerms : (fun m : ℕ => pairedQuadratic w r (gaussResolventValue m))
      = fun m : ℕ => 8 * ((1 / (2 * ((m : ℝ) + 1))) * packetEnergy w r
          - packetResolventPairing w r (2 * (m : ℝ) + 1 / 2)) :=
    funext fun m => pairedQuadratic_gaussResolventValue hw r m
  rw [hGaussTerms, tsum_mul_left] at hGaussTsum
  -- the prime piece
  have hPrimeSum : ∀ j, HasSum (fun m : ℕ => primeLagValue m (w j)) (primeLagSeries (w j)) :=
    fun j => (summable_primeLagValue (hhalf j)).hasSum
  have hPrimePaired := hasSum_pairedQuadratic r primeLagValue primeLagSeries hPrimeSum
  have hPrimeTsum : (∑' m : ℕ, pairedQuadratic w r (primeLagValue m))
      = pairedQuadratic w r primeLagSeries := hPrimePaired.tsum_eq
  have hPrimeTerms : (fun m : ℕ => pairedQuadratic w r (primeLagValue m))
      = fun m : ℕ => (-8 : ℝ) *
          (criticalMellinAtomWeight m * packetAutocorrelation w r (Real.log m)) := by
    funext m
    rw [pairedQuadratic_primeLagValue hw r m]
    ring
  rw [hPrimeTerms, tsum_mul_left, ← primeAutocorrCurrentReal] at hPrimeTsum
  -- the polar pair
  have hpolarA := packetResolventPairing_eq_autocorrLaplace hw r
    (c := 1 / 2) (fun j => by
      have := hw j
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith)
  have hpolarB := packetResolventPairing_eq_autocorrLaplace hw r
    (c := -(1 / 2)) (fun j => by
      have := hhalf j
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith)
  have hpolarPair := autocorrLaplace_polar_pair hw r hhalf
  have hsub := polar_sub_prime_real hw r hα hα2
  rw [e1, e2, e3, e4, pairedQuadratic_polarResolventValueA hw r,
    pairedQuadratic_polarResolventValueB hhalf hw r, pairedQuadratic_logPiValue hw r,
    ← hPrimeTsum, gaussResolventQuadratic]
  rw [hpolarA, hpolarB]
  linarith [hGaussTsum, hpolarPair, hsub]


end

end RHTower
