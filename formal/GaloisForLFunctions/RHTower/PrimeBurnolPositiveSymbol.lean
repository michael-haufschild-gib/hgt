import GaloisForLFunctions.RHTower.PrimeBurnolSymbolClassification
import GaloisForLFunctions.HTGeometry.BurnolPositiveShiftMeasure
import GaloisForLFunctions.HTGeometry.BernsteinWidder

/-! The physical positive cone forces a Bernstein symbol from actual-prime eigenlines. -/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ComplexOrder NNReal

namespace RHTower
open GaloisForLFunctions.HTGeometry _root_.HTGeometry

def BurnolPreservesNonnegativity (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) : Prop :=
  ∀ f, 0 ≤ f → 0 ≤ T f

def BurnolPositivePacketTest (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) : Prop :=
  ∀ (δ : ℝ≥0) (n : ℕ) (lam : Ioi (0 : ℝ)), 0 ≤ T (burnolPositivePacket δ n lam)

theorem BurnolPreservesNonnegativity.packetTest
    {T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2} (hT : BurnolPreservesNonnegativity T) :
    BurnolPositivePacketTest T := fun δ n lam => hT _ (burnolPositivePacket_nonneg δ n lam)

theorem burnolOperatorSymbol_rate
    (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) (a : Nat.Primes → ℂ)
    (ha : ∀ p, T (primeLogCriticalLaplaceFeatureL2 p) = a p • primeLogCriticalLaplaceFeatureL2 p)
    (lam : ℝ) (hlam : 0 < lam) :
    T (burnolRateFeature lam hlam) = burnolOperatorSymbol T lam • burnolRateFeature lam hlam := by
  simpa only [burnolComplexFeature_ofReal, burnolRateFeature] using
    burnolOperatorSymbol_eigen T a ha (z := (lam : ℂ)) hlam

theorem burnolOperatorSymbol_real_nonneg
    (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) (a : Nat.Primes → ℂ)
    (ha : ∀ p, T (primeLogCriticalLaplaceFeatureL2 p) = a p • primeLogCriticalLaplaceFeatureL2 p)
    (hp : BurnolPositivePacketTest T) (lam : ℝ) (hlam : 0 < lam) :
    0 ≤ burnolOperatorSymbol T lam := by
  exact burnolPacketCoefficient_zero_nonneg T (fun x => burnolOperatorSymbol T x)
    (burnolOperatorSymbol_rate T a ha) 1 0 ⟨lam, hlam⟩ (hp 1 0 ⟨lam, hlam⟩)

/-- Positive packets force all finite-difference inequalities, with no point evaluation on L2. -/
theorem burnolOperatorSymbol_completelyMonotone
    (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) (a : Nat.Primes → ℂ)
    (ha : ∀ p, T (primeLogCriticalLaplaceFeatureL2 p) = a p • primeLogCriticalLaplaceFeatureL2 p)
    (hp : BurnolPositivePacketTest T) :
    CompletelyMonotoneOn (fun x : ℝ => (burnolOperatorSymbol T x).re) := by
  constructor
  · intro n δ hδ lam hlam
    have h := (Complex.le_def.mp (burnolPacketCoefficient_zero_nonneg T
      (fun x => burnolOperatorSymbol T x) (burnolOperatorSymbol_rate T a ha)
      ⟨δ, hδ.le⟩ n ⟨lam, hlam⟩ (hp ⟨δ, hδ.le⟩ n ⟨lam, hlam⟩))).1
    simp only [Complex.zero_re, burnolPacketCoefficient_zero_re] at h
    exact h
  · intro x hx
    exact (Complex.continuous_re.continuousAt.comp
      ((burnolOperatorSymbol_analytic T (x : ℂ) hx).continuousAt.comp
        Complex.continuous_ofReal.continuousAt)).continuousWithinAt

/-- The real Bernstein measure is transported to the literal nonnegative shift parameter. -/
theorem exists_burnolPositiveSymbol_measure
    (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) (a : Nat.Primes → ℂ)
    (ha : ∀ p, T (primeLogCriticalLaplaceFeatureL2 p) = a p • primeLogCriticalLaplaceFeatureL2 p)
    (hp : BurnolPositivePacketTest T) :
    ∃ τ : Measure ℝ≥0, IsFiniteMeasure τ ∧ ∀ lam : ℝ, 0 < lam →
      burnolOperatorSymbol T lam = (burnolMeasureLaplace τ lam : ℂ) := by
  let H : ℝ → ℝ := fun x => (burnolOperatorSymbol T x).re
  have hCM : CompletelyMonotoneOn H := burnolOperatorSymbol_completelyMonotone T a ha hp
  have hant : AntitoneOn H (Ioi 0) := fun _ hx _ _ hxy =>
    completelyMonotoneDiff_antitone hCM.1 hx hxy
  have hb : BddAbove (H '' Ioi 0) := by
    refine ⟨‖T‖, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (Complex.re_le_norm _).trans (burnolOperatorSymbol_bound T a ha (z := (x : ℂ)) hx)
  obtain ⟨ν, hν, hνsupport, hLap⟩ :=
    exists_finiteLaplaceMeasure_of_completelyMonotoneOn hCM (hant.tendsto_nhdsGT hb)
  letI : IsFiniteMeasure ν := hν
  let τ : Measure ℝ≥0 := ν.map Real.toNNReal
  have hνpos : ∀ᵐ r ∂ν, 0 ≤ r := by
    apply ae_iff.mpr
    exact hνsupport
  refine ⟨τ, inferInstance, fun lam hlam => ?_⟩
  have hreal : H lam = burnolMeasureLaplace τ lam := by
    rw [hLap lam hlam, burnolMeasureLaplace]
    change _ = ∫ h : ℝ≥0, Real.exp (-(lam * h)) ∂ν.map Real.toNNReal
    rw [integral_map continuous_real_toNNReal.measurable.aemeasurable
      (by exact (by fun_prop : Continuous (fun h : ℝ≥0 => Real.exp (-(lam * h)))).aestronglyMeasurable)]
    apply integral_congr_ae
    filter_upwards [hνpos] with r hr
    rw [Real.coe_toNNReal r hr]
    congr 1
    ring
  apply Complex.ext
  · exact hreal
  · exact (Complex.le_def.mp (burnolOperatorSymbol_real_nonneg T a ha hp lam hlam)).2.symm

/-- A failed finite difference produces a positive input whose continuous output has
negative real part throughout an initial interval. -/
theorem primeBurnol_failed_difference_packet
    (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) (a : Nat.Primes → ℂ)
    (ha : ∀ p, T (primeLogCriticalLaplaceFeatureL2 p) = a p • primeLogCriticalLaplaceFeatureL2 p)
    (δ : ℝ≥0) (n : ℕ) (lam : Ioi (0 : ℝ))
    (hfail : (-1 : ℝ)^n * (fwdDiff (δ : ℝ))^[n]
      (fun x : ℝ => (burnolOperatorSymbol T x).re) lam < 0) :
    0 ≤ burnolPositivePacket δ n lam ∧
      ∃ v : ℝ → ℂ, Continuous v ∧
        (T (burnolPositivePacket δ n lam) : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] v ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε → (v t).re < 0 := by
  let q := burnolPacketCoefficient (fun x => burnolOperatorSymbol T x) δ n lam
  have hq : Continuous q := continuous_burnolPacketCoefficient _ _ _ _
  have hq0 : (q 0).re < 0 := by
    simpa only [q, burnolPacketCoefficient_zero_re] using hfail
  have hnear : {t : ℝ | (q t).re < 0} ∈ 𝓝 (0 : ℝ) :=
    (isOpen_lt (Complex.continuous_re.comp hq) continuous_const).mem_nhds hq0
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨burnolPositivePacket_nonneg δ n lam,
    (fun t => (t * Real.exp (-(lam * t)) : ℂ) * q t), ?_,
    burnolPositivePacket_image_ae T _ (burnolOperatorSymbol_rate T a ha) δ n lam,
    ε, hε, ?_⟩
  · exact (by fun_prop : Continuous (fun t : ℝ => (t * Real.exp (-(lam * t)) : ℂ))).mul hq
  · intro t ht htε
    have hqt : (q t).re < 0 := hball (by
      change dist t 0 < ε
      simpa only [Real.dist_eq, sub_zero, abs_of_pos ht] using htε)
    simpa only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, add_zero, sub_zero] using
      mul_neg_of_pos_of_neg (mul_pos ht (Real.exp_pos (-(lam * t)))) hqt

end RHTower
