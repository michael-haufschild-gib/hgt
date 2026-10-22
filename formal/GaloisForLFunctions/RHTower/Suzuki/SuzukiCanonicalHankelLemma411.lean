import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelLemma49

/-!
# Suzuki (2012), Lemma 4.11: the completed pair is real entire

The source proof uses real Mellin-convolution representatives.  Here the same content is proved
at the exact `L²` level: the finite Fredholm data and its canonical Hankel image are real almost
everywhere in logarithmic coordinates, compact Fourier transforms obey Schwarz reflection, and
the entire pole-cleared pair from Lemma 4.9 is consequently fixed by Schwarz reflection.
-/

open Complex Real MeasureTheory Set Filter

noncomputable section

namespace RHTower


attribute [local instance] Measure.Subtype.measureSpace

/-! ## Reality in physical and logarithmic coordinates -/

/-- Zero extension preserves almost-everywhere reality of interval data. -/
theorem suzukiPhysicalIntervalZeroExtendFun_real_ae
    {a : ℝ} (f : IntervalL2 0 a)
    (hf : ∀ᵐ x : ClosedInterval 0 a ∂volume, (f x).im = 0) :
    ∀ᵐ x : ℝ ∂volume, (suzukiPhysicalIntervalZeroExtendFun f x).im = 0 := by
  have hzeroSub : ∀ᵐ x : ClosedInterval 0 a ∂volume,
      (suzukiPhysicalIntervalZeroExtendFun f (x : ℝ)).im = 0 := by
    filter_upwards [suzukiPhysicalIntervalRepresentative_ae f, hf] with x hrep hreal
    rw [suzukiPhysicalIntervalZeroExtendFun_apply, hrep]
    exact hreal
  have hzeroIcc : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Icc 0 a),
      (suzukiPhysicalIntervalZeroExtendFun f x).im = 0 :=
    (ae_restrict_iff_subtype measurableSet_Icc).2 hzeroSub
  have hzeroConditional := (ae_restrict_iff' measurableSet_Icc).mp hzeroIcc
  filter_upwards [hzeroConditional] with x hx
  by_cases hmem : x ∈ Icc 0 a
  · exact hx hmem
  · rw [suzukiPhysicalIntervalZeroExtendFun_eq_zero_of_notMem f hmem]
    simp

/-- Passing a real compact interval vector to logarithmic half-density coordinates preserves
reality almost everywhere. -/
theorem suzukiPositiveLogUnitary_interval_real_ae
    {a : ℝ} (f : IntervalL2 0 a)
    (hf : ∀ᵐ x : ClosedInterval 0 a ∂volume, (f x).im = 0) :
    ∀ᵐ t : ℝ ∂volume,
      (l2MeasurableRep
        (suzukiPositiveLogUnitary
          (suzukiPhysicalIntervalPositiveIsometry a f)) t).im = 0 := by
  let u : SuzukiPositiveL2 := suzukiPhysicalIntervalPositiveIsometry a f
  let q : SoninL2 := suzukiPositiveLogUnitary u
  have hcarrier : suzukiPositiveHalfLineUnitary (logEvenUnitary.symm q) = u := by
    change suzukiPositiveHalfLineUnitary
      (logEvenUnitary.symm
        (logEvenUnitary (suzukiPositiveHalfLineUnitary.symm u))) = u
    rw [logEvenUnitary.symm_apply_apply,
      suzukiPositiveHalfLineUnitary.apply_symm_apply]
  have hcoord := suzukiPositiveHalfLineUnitary_logEven_symm_ae q
  rw [hcarrier] at hcoord
  have hcoordWhole := (ae_restrict_iff' measurableSet_Ioi).mp hcoord
  have hcoordExp := realExp_quasiMeasurePreserving.ae hcoordWhole
  have hinputWhole := (ae_restrict_iff' measurableSet_Ioi).mp
    (suzukiPhysicalIntervalPositiveL2_ae f)
  have hinputExp := realExp_quasiMeasurePreserving.ae hinputWhole
  have hrealExp := realExp_quasiMeasurePreserving.ae
    (suzukiPhysicalIntervalZeroExtendFun_real_ae f hf)
  change ∀ᵐ t : ℝ ∂volume, (l2MeasurableRep q t).im = 0
  filter_upwards [hcoordExp, hinputExp, hrealExp] with t hcoord hinput hreal
  have hcoord' : u (Real.exp t) =
      (Real.exp (-t / 2) : ℂ) * l2MeasurableRep q t := by
    simpa only [Real.log_exp] using hcoord (Real.exp_pos t)
  have hinput' : u (Real.exp t) =
      suzukiPhysicalIntervalZeroExtendFun f (Real.exp t) := by
    exact hinput (Real.exp_pos t)
  have hweight : (Real.exp (t / 2) : ℂ) * (Real.exp (-t / 2) : ℂ) = 1 := by
    norm_cast
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have hrep : l2MeasurableRep q t =
      (Real.exp (t / 2) : ℂ) *
        suzukiPhysicalIntervalZeroExtendFun f (Real.exp t) := by
    calc
      l2MeasurableRep q t =
          (Real.exp (t / 2) : ℂ) *
            ((Real.exp (-t / 2) : ℂ) * l2MeasurableRep q t) := by
        rw [← mul_assoc, hweight, one_mul]
      _ = _ := by rw [← hcoord', hinput']
  rw [hrep]
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hreal]
  ring

/-- The canonical logarithmic Hankel image of real interval data is real almost everywhere. -/
theorem suzukiCanonicalLogHankel_interval_real_ae
    {omega a : ℝ} (homega : 1 / 2 < omega) (ha : 1 < a)
    (f : IntervalL2 0 a)
    (hf : ∀ᵐ x : ClosedInterval 0 a ∂volume, (f x).im = 0) :
    ∀ᵐ t : ℝ ∂volume,
      (l2MeasurableRep
        (suzukiCanonicalLogHankelUnitary omega
          (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega)
          (suzukiPositiveLogUnitary
            (suzukiPhysicalIntervalPositiveIsometry a f))) t).im = 0 := by
  let p : SoninL2 :=
    suzukiCanonicalLogHankelUnitary omega
      (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega)
      (suzukiPositiveLogUnitary
        (suzukiPhysicalIntervalPositiveIsometry a f))
  have hp := suzukiCanonicalLogHankel_intervalSource_ae homega ha f
  have hrep : (p : ℝ → ℂ) =ᵐ[volume] l2MeasurableRep p :=
    (l2MeasurableRep_ae p).symm
  change ∀ᵐ t : ℝ ∂volume, (l2MeasurableRep p t).im = 0
  filter_upwards [hp, hrep] with t hp hrep
  rw [← hrep, hp]
  have hIntegral :
      ((∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega (Real.exp t * (y : ℝ)) * f y ∂volume)).im = 0 := by
    apply Complex.conj_eq_iff_im.mp
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [hf] with y hy
    rw [map_mul, conj_suzukiSourceHFinite,
      Complex.conj_eq_iff_im.mpr hy]
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hIntegral]
  ring

/-- The finite Fredholm sum is real almost everywhere. -/
theorem suzukiHankelPhiSum_real_ae
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    ∀ᵐ x : ClosedInterval 0 a ∂volume,
      (suzukiHankelPhiSum omega a homega ha x).im = 0 := by
  filter_upwards [suzukiHankelPhi_real_ae SuzukiHankelSign.positive
      (show 1 / 2 < omega by linarith) ha,
    suzukiHankelPhi_real_ae SuzukiHankelSign.negative
      (show 1 / 2 < omega by linarith) ha,
    Lp.coeFn_add
      (suzukiHankelPhi SuzukiHankelSign.positive omega a (by linarith) ha)
      (suzukiHankelPhi SuzukiHankelSign.negative omega a (by linarith) ha)] with
      x hp hm hadd
  rw [suzukiHankelPhiSum, hadd]
  simp [Complex.add_im, hp, hm]

theorem suzukiHankelPhiSumLog_real_ae
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    ∀ᵐ t : ℝ ∂volume,
      (l2MeasurableRep (suzukiHankelPhiSumLog omega a homega ha) t).im = 0 := by
  exact suzukiPositiveLogUnitary_interval_real_ae
    (suzukiHankelPhiSum omega a homega ha)
      (suzukiHankelPhiSum_real_ae homega ha)

theorem suzukiHankelPhiSumHankelLog_real_ae
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    ∀ᵐ t : ℝ ∂volume,
      (l2MeasurableRep
        (suzukiHankelPhiSumHankelLog omega a homega ha) t).im = 0 := by
  exact suzukiCanonicalLogHankel_interval_real_ae
    (show 1 / 2 < omega by linarith) ha
      (suzukiHankelPhiSum omega a homega ha)
      (suzukiHankelPhiSum_real_ae homega ha)

/-! ## Schwarz reflection of compact `L²` Fourier transforms -/

/-- A compact Fourier transform of real `L²` data obeys the exact Schwarz-reflection law. -/
theorem conj_suzukiCompactL2Fourier_conj
    {A : ℝ} {f : SoninL2}
    (hf : ∀ᵐ x : ℝ ∂volume, (f x).im = 0) (z : ℂ) :
    (starRingEnd ℂ) (suzukiCompactL2Fourier A f ((starRingEnd ℂ) z)) =
      suzukiCompactL2Fourier A f (-z) := by
  have hcutReal : ∀ᵐ x : ℝ ∂volume, ((suzukiCutoff A f) x).im = 0 := by
    filter_upwards [indicatorCutoff_ae (Icc (-A) A) measurableSet_Icc f, hf] with
        x hcut hreal
    rw [hcut]
    by_cases hx : x ∈ Icc (-A) A
    · rw [indicator_of_mem hx]
      exact hreal
    · rw [indicator_of_notMem hx]
      simp
  rw [suzukiCompactL2Fourier, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [hcutReal] with x hreal
  rw [map_mul, Complex.conj_eq_iff_im.mpr hreal]
  congr 1
  rw [← Complex.exp_conj]
  congr 1
  simp

/-! ## Schwarz reflection of the completed entire pair -/

theorem conj_suzukiHankelAiz_conj (a : ℝ) (z : ℂ) :
    (starRingEnd ℂ) (suzukiHankelAiz a ((starRingEnd ℂ) z)) =
      suzukiHankelAiz a (-z) := by
  rw [suzukiHankelAiz, suzukiHankelAiz, ← Complex.exp_conj]
  congr 1
  simp

theorem conj_suzukiCanonicalE_conj (omega : ℝ) (z : ℂ) :
    (starRingEnd ℂ) (suzukiCanonicalE omega ((starRingEnd ℂ) z)) =
      suzukiCanonicalE omega (-z) := by
  exact suzukiCanonicalESharp_eq_E_neg omega z

/-- Schwarz reflection interchanges the two entire pole-cleared `E/E*` numerators. -/
theorem conj_suzukiHankelTildeECleared_conj_eq_starCleared
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    (starRingEnd ℂ)
        (suzukiHankelTildeECleared omega a homega ha ((starRingEnd ℂ) z)) =
      suzukiHankelTildeEStarCleared omega a homega ha z := by
  have hqRep := suzukiHankelPhiSumLog_real_ae homega ha
  have hpRep := suzukiHankelPhiSumHankelLog_real_ae homega ha
  have hqCoe : ∀ᵐ t : ℝ ∂volume,
      ((suzukiHankelPhiSumLog omega a homega ha : SoninL2) t).im = 0 := by
    filter_upwards [l2MeasurableRep_ae
      (suzukiHankelPhiSumLog omega a homega ha), hqRep] with t hrep hreal
    rw [← hrep]
    exact hreal
  have hpCoe : ∀ᵐ t : ℝ ∂volume,
      ((suzukiHankelPhiSumHankelLog omega a homega ha : SoninL2) t).im = 0 := by
    filter_upwards [l2MeasurableRep_ae
      (suzukiHankelPhiSumHankelLog omega a homega ha), hpRep] with t hrep hreal
    rw [← hrep]
    exact hreal
  have hq := conj_suzukiCompactL2Fourier_conj
    (A := Real.log a) hqCoe
  have hp := conj_suzukiCompactL2Fourier_conj
    (A := Real.log a) hpCoe
  have hE := conj_suzukiCanonicalE_conj omega z
  have hEneg := conj_suzukiCanonicalE_conj omega (-z)
  have hAiz := conj_suzukiHankelAiz_conj a z
  have hpz := hp z
  have hqneg := hq (-z)
  have hcoeff : (starRingEnd ℂ) (suzukiHankelTildeCoefficient a) =
      suzukiHankelTildeCoefficient a := by
    simp [suzukiHankelTildeCoefficient, map_ofNat]
  simp only [map_neg, neg_neg] at hEneg hqneg
  simp only [suzukiHankelTildeECleared, suzukiHankelTildeEStarCleared,
    suzukiHankelTildeERegularPart, suzukiHankelTildeEThetaPart,
    map_add, map_mul, map_neg, hE, hEneg, hAiz, hpz, hqneg, hcoeff]
  ring

theorem conj_suzukiHankelTildeEStarCleared_conj_eq_ECleared
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    (starRingEnd ℂ)
        (suzukiHankelTildeEStarCleared omega a homega ha ((starRingEnd ℂ) z)) =
      suzukiHankelTildeECleared omega a homega ha z := by
  calc
    (starRingEnd ℂ)
        (suzukiHankelTildeEStarCleared omega a homega ha
          ((starRingEnd ℂ) z)) =
        (starRingEnd ℂ)
          (suzukiHankelTildeECleared omega a homega ha
            (-((starRingEnd ℂ) z))) := by
      rw [suzukiHankelTildeEStarCleared_eq_ECleared_neg homega ha]
    _ = suzukiHankelTildeEStarCleared omega a homega ha (-z) := by
      simpa only [map_neg] using
        conj_suzukiHankelTildeECleared_conj_eq_starCleared homega ha (-z)
    _ = suzukiHankelTildeECleared omega a homega ha z := by
      rw [suzukiHankelTildeEStarCleared_eq_ECleared_neg homega ha, neg_neg]

theorem conj_suzukiHankelTildeACleared_conj
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    (starRingEnd ℂ)
        (suzukiHankelTildeACleared omega a homega ha ((starRingEnd ℂ) z)) =
      suzukiHankelTildeACleared omega a homega ha z := by
  unfold suzukiHankelTildeACleared
  rw [map_div₀, map_add,
    conj_suzukiHankelTildeECleared_conj_eq_starCleared homega ha,
    conj_suzukiHankelTildeEStarCleared_conj_eq_ECleared homega ha]
  simp only [map_ofNat]
  ring

theorem conj_suzukiHankelTildeBCleared_conj
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    (starRingEnd ℂ)
        (suzukiHankelTildeBCleared omega a homega ha ((starRingEnd ℂ) z)) =
      suzukiHankelTildeBCleared omega a homega ha z := by
  unfold suzukiHankelTildeBCleared
  rw [map_div₀, map_sub, map_mul,
    conj_suzukiHankelTildeEStarCleared_conj_eq_ECleared homega ha,
    conj_suzukiHankelTildeECleared_conj_eq_starCleared homega ha]
  simp only [map_ofNat, Complex.conj_I]
  ring

theorem conj_suzukiHankelCompletedA_conj
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    (starRingEnd ℂ)
        (suzukiHankelCompletedA omega a homega ha ((starRingEnd ℂ) z)) =
      suzukiHankelCompletedA omega a homega ha z := by
  rw [suzukiHankelCompletedA, suzukiHankelCompletedA, map_mul,
    conj_suzukiHankelTildeACleared_conj homega ha]
  simp

theorem conj_suzukiHankelCompletedB_conj
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    (starRingEnd ℂ)
        (suzukiHankelCompletedB omega a homega ha ((starRingEnd ℂ) z)) =
      suzukiHankelCompletedB omega a homega ha z := by
  rw [suzukiHankelCompletedB, suzukiHankelCompletedB, map_mul, map_inv₀,
    conj_suzukiHankelTildeBCleared_conj homega ha]
  simp

/-- **Suzuki (2012), Lemma 4.11, closed theorem:** both functions are entire and real under
Schwarz reflection. -/
theorem suzuki2012_lemma_four_eleven :
    ∀ (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a),
      Differentiable ℂ (suzukiHankelCompletedA omega a homega ha) ∧
      Differentiable ℂ (suzukiHankelCompletedB omega a homega ha) ∧
      (∀ z : ℂ,
        (starRingEnd ℂ)
            (suzukiHankelCompletedA omega a homega ha ((starRingEnd ℂ) z)) =
          suzukiHankelCompletedA omega a homega ha z) ∧
      (∀ z : ℂ,
        (starRingEnd ℂ)
            (suzukiHankelCompletedB omega a homega ha ((starRingEnd ℂ) z)) =
          suzukiHankelCompletedB omega a homega ha z) := by
  intro omega a homega ha
  exact ⟨differentiable_suzukiHankelCompletedA homega ha,
    differentiable_suzukiHankelCompletedB homega ha,
    fun z => conj_suzukiHankelCompletedA_conj homega ha z,
    fun z => conj_suzukiHankelCompletedB_conj homega ha z⟩

end RHTower
