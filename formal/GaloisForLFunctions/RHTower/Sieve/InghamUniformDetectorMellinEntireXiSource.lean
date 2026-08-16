import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinFullXiSum
import GaloisForLFunctions.RHTower.ThueMorseMellinFlatness

/-!
# Route T: entire Mellin kernel and Xi source-contour weld

The adjacent physical window vanishes on neighborhoods of both zero and infinity. Its Mellin
transform is therefore entire, strengthening the earlier right-half-plane representation theorem.
After the centered Xi change of variables `rho = 1/2 + z i`, this gives an entire spectral test
whose value on every Xi zero copy is exactly the Route-T buffered Mellin kernel at the underlying
zeta zero.

Combining this identity with the complete exact-multiplicity Xi summability theorem and the cofinal
Guinand--Weil spectral rectangle law proves that admissible normalized prime--archimedean source
contours approximate the complete Route-T zero sum to arbitrary accuracy.
-/

open Complex Filter Metric Set Finset Topology MeasureTheory Asymptotics

namespace RHTower.Sieve

noncomputable section

open GaloisForLFunctions.HTGeometry

private theorem routeTSmoothWindowWeight_isMellinFlatKernel
    {N H : ℝ} (hN : 0 < N) (hH : 0 < H) :
    RHTower.IsMellinFlatKernel
      (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ)) := by
  let W : ℝ → ℂ := fun x => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ)
  have hcont : Continuous W := by
    have hreal : Continuous (routeTSmoothWindowWeight N H) := by
      unfold routeTSmoothWindowWeight
      exact (GaloisForLFunctions.HTGeometry.smoothWeight_contDiff
        (N + H) H (n := 0)).continuous.sub
          (GaloisForLFunctions.HTGeometry.smoothWeight_contDiff N H (n := 0)).continuous
    exact Complex.continuous_ofReal.comp hreal
  have hloc : LocallyIntegrableOn W (Ioi 0) :=
    hcont.locallyIntegrable.locallyIntegrableOn _
  have htop : ∃ a : ℝ, 0 < a ∧ W =O[atTop]
      (fun x : ℝ => Real.exp (-a * x)) := by
    refine ⟨1, by norm_num, ?_⟩
    have heq : W =ᶠ[atTop] (fun _ => 0) := by
      filter_upwards [eventually_ge_atTop (N + 2 * H)] with x hx
      have hplus : GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x = 0 :=
        GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH (by linarith)
      have hbase : GaloisForLFunctions.HTGeometry.smoothWeight N H x = 0 :=
        GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH (by linarith)
      simp only [W, routeTSmoothWindowWeight, hplus, hbase, sub_self,
        Complex.ofReal_zero]
    exact heq.trans_isBigO (isBigO_zero _ _)
  have hzero : RHTower.SuperpolynomialDecayAtZero W := by
    intro b
    have heq : W =ᶠ[𝓝[>] 0] (fun _ => 0) := by
      have hlt : ∀ᶠ x : ℝ in 𝓝[>] 0, x < N :=
        (eventually_lt_nhds hN).filter_mono nhdsWithin_le_nhds
      filter_upwards [hlt] with x hx
      have hplus : GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x = 1 :=
        GaloisForLFunctions.HTGeometry.smoothWeight_eq_one hH (by linarith)
      have hbase : GaloisForLFunctions.HTGeometry.smoothWeight N H x = 1 :=
        GaloisForLFunctions.HTGeometry.smoothWeight_eq_one hH hx.le
      simp only [W, routeTSmoothWindowWeight, hplus, hbase, sub_self,
        Complex.ofReal_zero]
    exact heq.trans_isBigO (isBigO_zero _ _)
  exact ⟨hloc, htop, hzero⟩

theorem analyticOnNhd_routeTNormalizedSmoothWindowMellin_univ
    {N H : ℝ} (hN : 0 < N) (hH : 0 < H) :
    AnalyticOnNhd ℂ (routeTNormalizedSmoothWindowMellin N H) Set.univ := by
  have hmellin := (routeTSmoothWindowWeight_isMellinFlatKernel hN hH).mellin_analyticOnNhd
  exact analyticOnNhd_const.mul hmellin

def routeTBufferedXiSpectralTest (X : ℕ) (z : ℂ) : ℂ :=
  routeTNormalizedSmoothWindowMellin
    (inghamRouteTMellinPhysicalCenter X)
    (inghamRouteTMellinBufferedPhysicalWidth X)
    (1 / 2 + z * I)

theorem analyticOnNhd_routeTBufferedXiSpectralTest_univ
    {X : ℕ} (hX : 1 ≤ X) :
    AnalyticOnNhd ℂ (routeTBufferedXiSpectralTest X) Set.univ := by
  have hK := analyticOnNhd_routeTNormalizedSmoothWindowMellin_univ
    (inghamRouteTMellinPhysicalCenter_pos hX)
    (inghamRouteTMellinBufferedPhysicalWidth_pos hX)
  have hKdiff : Differentiable ℂ
      (routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X)) := fun z =>
    (hK z (Set.mem_univ z)).differentiableAt
  have htestDiff : Differentiable ℂ (routeTBufferedXiSpectralTest X) := by
    intro z
    have haffine : DifferentiableAt ℂ (fun w : ℂ => 1 / 2 + w * I) z := by
      fun_prop
    have hcomp := DifferentiableAt.comp (x := z)
      (g := routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X))
      (f := fun w : ℂ => 1 / 2 + w * I)
      (hKdiff (1 / 2 + z * I)) haffine
    change DifferentiableAt ℂ
      (routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X) ∘
          fun w : ℂ => 1 / 2 + w * I) z
    exact hcomp
  exact htestDiff.differentiableOn.analyticOnNhd isOpen_univ

theorem routeTBufferedXiSpectralTest_xiSpectralPoint
    (X : ℕ) (q : RHTower.XiZeroCopy) :
    routeTBufferedXiSpectralTest X (RHTower.xiSpectralPoint q) =
      routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X) (q.1 : ℂ) := by
  unfold routeTBufferedXiSpectralTest
  congr 1
  rw [RHTower.xiSpectralPoint_eq_support, RHTower.xiSpectralPointSupport,
    mul_assoc]
  have hI : (-I : ℂ) * I = 1 := by simp
  rw [hI, mul_one]
  ring

theorem exists_admissible_routeTBufferedXiSource_contour_approximates_fullZeroSum
    {X : ℕ} (hX : 3 ≤ X) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ z₁ z₂ : ℂ,
      z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
      dist ((2 * Real.pi * I)⁻¹ *
          rectIntegral (fun z => routeTBufferedXiSpectralTest X z *
            RHTower.continuedPrimeArchSourceRelativeTrace z) z₁ z₂)
        (inghamRouteTBufferedXiMellinFullZeroSum X) < epsilon := by
  classical
  let f : RHTower.XiZeroCopy → ℂ := fun q =>
    routeTNormalizedSmoothWindowMellin
      (inghamRouteTMellinPhysicalCenter X)
      (inghamRouteTMellinBufferedPhysicalWidth X) (q.1 : ℂ)
  have hsum : Summable f := summable_routeTBufferedXiMellin hX
  have hball : Metric.ball (∑' q, f q) epsilon ∈ nhds (∑' q, f q) :=
    Metric.ball_mem_nhds _ hepsilon
  have hevent : ∀ᶠ s : Finset RHTower.XiZeroCopy in atTop,
      ∑ q ∈ s, f q ∈ Metric.ball (∑' q, f q) epsilon :=
    hsum.hasSum.eventually hball
  rw [eventually_atTop] at hevent
  obtain ⟨F, hF⟩ := hevent
  obtain ⟨z₁, z₂, hre, him, hcontains, hcontour⟩ :=
    RHTower.exists_admissible_rectIntegral_source_eq_xiZeroCopy_sum_containing F
      (analyticOnNhd_routeTBufferedXiSpectralTest_univ
        (show (1 : ℕ) ≤ X by omega))
  refine ⟨z₁, z₂, hre, him, ?_⟩
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
    have hpi0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [hpi0, Complex.I_ne_zero]
  have hnorm : (2 * Real.pi * I : ℂ)⁻¹ *
      rectIntegral (fun z => routeTBufferedXiSpectralTest X z *
        RHTower.continuedPrimeArchSourceRelativeTrace z) z₁ z₂ =
      ∑ q ∈ RHTower.xiZeroCopyClosedRectangle z₁ z₂, f q := by
    rw [hcontour, ← mul_assoc, inv_mul_cancel₀ hpi, one_mul]
    exact Finset.sum_congr rfl fun q _ =>
      routeTBufferedXiSpectralTest_xiSpectralPoint X q
  rw [hnorm, inghamRouteTBufferedXiMellinFullZeroSum]
  have hsubset : F ⊆ RHTower.xiZeroCopyClosedRectangle z₁ z₂ :=
    fun q hq => hcontains q hq
  exact hF _ hsubset

end


end RHTower.Sieve
