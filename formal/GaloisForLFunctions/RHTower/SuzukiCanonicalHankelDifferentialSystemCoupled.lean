import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelDifferentialSystemPointwise

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace
attribute [local instance 2000] NormedAddCommGroup.toAddCommGroup

theorem intervalIntegrable_suzukiHankelEulerPhi_window
    (epsilon : SuzukiHankelSign) {omega a B : ℝ}
    (homega : 1 < omega) (ha : 1 < a) (hB : 0 < B) :
    IntervalIntegrable (suzukiHankelEulerPhi epsilon omega a homega ha)
      volume 0 B := by
  let P := suzukiHankelPhiGlobal epsilon omega a homega ha
  let phi := suzukiHankelPhiContinuous epsilon omega a homega ha
  let H := suzukiSourceHIntervalIntegral omega a phi
  have hs := intervalIntegrable_suzukiScaledSourceEuler
    homega (by linarith : 0 < a) hB
  have hH := intervalIntegrable_suzukiSourceHIntervalEuler
    homega (by linarith : 0 < a) hB.le phi
  have hP : IntervalIntegrable P volume 0 B := by
    have hc : ContinuousOn P (uIcc 0 B) := by
      rw [uIcc_of_le hB.le]
      exact (continuousOn_suzukiHankelPhiGlobal_nonnegative epsilon homega ha).mono
        (fun _ hx => hx.1)
    exact hc.intervalIntegrable
  have hexplicit : IntervalIntegrable (fun x : ℝ =>
      (x : ℂ) * deriv (fun y : ℝ => suzukiSourceHFinite omega (a * y)) x -
        epsilon.coeff * ((x : ℂ) * deriv H x) +
        (1 / 2 : ℂ) * P x) volume 0 B :=
    (hs.sub (hH.const_mul epsilon.coeff)).add (hP.const_mul (1 / 2 : ℂ))
  have hbad : (Set.range fun n : ℕ => (n : ℝ) / a).Countable := Set.countable_range _
  have hcuspAe : ∀ᵐ x : ℝ ∂volume,
      x ∉ Set.range (fun n : ℕ => (n : ℝ) / a) := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using
      hbad.measure_zero (volume : Measure ℝ)
  have heq : ∀ᵐ x : ℝ ∂(volume.restrict (uIoc 0 B)),
      suzukiHankelEulerPhi epsilon omega a homega ha x =
        (x : ℂ) * deriv (fun y : ℝ => suzukiSourceHFinite omega (a * y)) x -
          epsilon.coeff * ((x : ℂ) * deriv H x) +
          (1 / 2 : ℂ) * P x := by
    filter_upwards [ae_restrict_of_ae hcuspAe,
      ae_restrict_mem measurableSet_uIoc] with x hxcusp hxmem
    have hxmem' : x ∈ Ioc 0 B := by
      simpa only [uIoc_of_le hB.le] using hxmem
    have hxreg : x ∈ SuzukiHankelRegularX a := by
      refine ⟨hxmem'.1, ?_⟩
      intro n hxn
      apply hxcusp
      exact ⟨n, hxn.symm⟩
    have hd := hasDerivAt_suzukiHankelPhiGlobal_spatial_formula
      epsilon homega ha hxreg
    rw [suzukiHankelEulerPhi, hd.deriv]
    dsimp only [H, phi, P]
    ring
  apply hexplicit.congr_ae
  filter_upwards [heq] with x hx
  exact hx.symm

theorem integrable_suzukiHankelEulerPhi_subtype
    (epsilon : SuzukiHankelSign) {omega a B : ℝ}
    (homega : 1 < omega) (ha : 1 < a) (hB : 0 < B) :
    Integrable (fun x : ClosedInterval 0 B =>
      suzukiHankelEulerPhi epsilon omega a homega ha (x : ℝ)) := by
  have hreal : Integrable
      (suzukiHankelEulerPhi epsilon omega a homega ha)
      ((volume : Measure ℝ).restrict (Icc 0 B)) := by
    have h := intervalIntegrable_suzukiHankelEulerPhi_window epsilon homega ha hB
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hB.le] at h
    exact h
  let hmp : MeasurePreserving ((↑) : ClosedInterval 0 B → ℝ)
      (volume : Measure (ClosedInterval 0 B))
      ((volume : Measure ℝ).restrict (Icc 0 B)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  exact (hmp.integrable_comp_emb
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)).mpr hreal

def suzukiHankelEulerPhiL1
    (epsilon : SuzukiHankelSign) (omega a B : ℝ)
    (homega : 1 < omega) (ha : 1 < a) (hB : 0 < B) : IntervalL1 0 B :=
  (integrable_suzukiHankelEulerPhi_subtype epsilon homega ha hB).toL1
    (fun x : ClosedInterval 0 B =>
      suzukiHankelEulerPhi epsilon omega a homega ha (x : ℝ))

theorem suzukiHankelEulerPhiL1_ae
    (epsilon : SuzukiHankelSign) {omega a B : ℝ}
    (homega : 1 < omega) (ha : 1 < a) (hB : 0 < B) :
    (suzukiHankelEulerPhiL1 epsilon omega a B homega ha hB :
        ClosedInterval 0 B → ℂ) =ᵐ[volume]
      fun x => suzukiHankelEulerPhi epsilon omega a homega ha (x : ℝ) :=
  (integrable_suzukiHankelEulerPhi_subtype epsilon homega ha hB).coeFn_toL1

theorem suzukiFixedWindowBoundarySourceDerivativeL1_ae
    {omega B a : ℝ} (homega : 1 < omega) (hB : 1 < B)
    (ha : 0 < a) (haB : a < B) :
    (suzukiFixedWindowBoundarySourceDerivativeL1 omega B homega hB a :
        ClosedInterval 0 B → ℂ) =ᵐ[volume]
      fun x => deriv (fun b : ℝ => suzukiSourceHFinite omega (b * (x : ℝ))) a := by
  let R := suzukiSourceLogExtensionHorizon B (Real.log a)
  have hR : 0 ≤ R := suzukiSourceLogExtensionHorizon_nonneg B (Real.log a)
  have haR : Real.log a + Real.log B < R :=
    lt_suzukiSourceLogExtensionHorizon B (Real.log a)
  have hpull := suzukiLogPullbackL1_realL1Translate_integrableToL1_ae
    B (by linarith)
    (suzukiSourceHLogSmoothExtensionDerivative omega R)
    (integrable_suzukiSourceHLogSmoothExtensionDerivative homega R)
    (Real.log a)
  have hbad : (Set.range fun n : ℕ => (n : ℝ) / a).Countable := Set.countable_range _
  have hcuspAe : ∀ᵐ x : ℝ ∂volume,
      x ∉ Set.range (fun n : ℕ => (n : ℝ) / a) := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using
      hbad.measure_zero (volume : Measure ℝ)
  let hmp : MeasurePreserving ((↑) : ClosedInterval 0 B → ℝ)
      (volume : Measure (ClosedInterval 0 B))
      ((volume : Measure ℝ).restrict (Icc 0 B)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hgood := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae ((volume : Measure ℝ).ae_ne 0 |>.and hcuspAe))
  have hsmul := MeasureTheory.Lp.coeFn_smul (a⁻¹ : ℝ)
    (suzukiFixedWindowBoundarySourceLogDerivativeL1 omega B homega hB (Real.log a))
  filter_upwards [hpull, hgood, hsmul] with x hpull hxgood hsmul
  rw [suzukiFixedWindowBoundarySourceDerivativeL1]
  rw [hsmul]
  change ((a⁻¹ : ℝ) : ℂ) *
      (suzukiFixedWindowBoundarySourceLogDerivativeL1 omega B homega hB
        (Real.log a) x) = _
  rw [show suzukiFixedWindowBoundarySourceLogDerivativeL1 omega B homega hB
      (Real.log a) x =
      suzukiSourceHLogSmoothExtensionDerivative omega R
        (Real.log a + Real.log (x : ℝ)) by exact hpull]
  have hx : 0 < (x : ℝ) :=
    lt_of_le_of_ne x.property.1 (Ne.symm hxgood.1)
  have hxlog : Real.log (x : ℝ) ≤ Real.log B :=
    Real.strictMonoOn_log.monotoneOn hx (lt_trans zero_lt_one hB) x.property.2
  have hreg : ∀ n : ℕ, a * (x : ℝ) ≠ (n : ℝ) := by
    intro n hax
    apply hxgood.2
    refine ⟨n, ?_⟩
    calc
      (n : ℝ) / a = (a * (x : ℝ)) / a := by rw [hax]
      _ = (x : ℝ) := by field_simp
  have hreg' : ∀ n : ℕ, (x : ℝ) * a ≠ (n : ℝ) := by
    intro n hxa
    exact hreg n (by simpa [mul_comm] using hxa)
  have hd0 := hasDerivAt_suzukiScaledSource_of_regular
    (R := R) (c := (x : ℝ)) (x := a) homega hR hx ha (by linarith) hreg'
  have hd' : HasDerivAt
      (fun b : ℝ => suzukiSourceHFinite omega (b * (x : ℝ)))
      ((a⁻¹ : ℝ) • suzukiScaledSourceEulerExtension omega R (x : ℝ) a) a := by
    apply hd0.congr_of_eventuallyEq
    apply Eventually.of_forall
    intro b
    exact congrArg (suzukiSourceHFinite omega) (mul_comm b (x : ℝ))
  rw [hd'.deriv]
  change ((a⁻¹ : ℝ) : ℂ) *
      suzukiSourceHLogSmoothExtensionDerivative omega R
        (Real.log a + Real.log (x : ℝ)) =
    ((a⁻¹ : ℝ) : ℂ) *
      suzukiScaledSourceEulerExtension omega R (x : ℝ) a
  rw [suzukiScaledSourceEulerExtension]
  rw [add_comm]

theorem suzukiFixedWindowSignedSectionDerivativeAtPhiL1_ae
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha : 1 < a) (haB : a < B) :
    (suzukiFixedWindowSignedSectionDerivativeAtPhiL1
        epsilon omega B homega hB a (by linarith) haB :
        ClosedInterval 0 B → ℂ) =ᵐ[volume]
      fun x => epsilon.coeff *
        suzukiHankelPhiGlobal epsilon omega a homega ha a *
          suzukiSourceHFinite omega (a * (x : ℝ)) := by
  let f := suzukiFixedWindowPhiContinuous epsilon omega B homega hB a
    (by linarith : 0 < a) haB.le
  let q := suzukiSmoothedApertureProfileIntegrand omega B homega
    (by linarith : 0 ≤ B) f a
  let qL2 := ContinuousMap.toLp 2 volume ℂ q
  have hq : (qL2 : ClosedInterval 0 B → ℂ) =ᵐ[volume] q :=
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
      (μ := (volume : Measure (ClosedInterval 0 B))) q
  have hinc : (suzukiIntervalL2AsL1 B qL2 : ClosedInterval 0 B → ℂ) =ᵐ[volume]
      qL2 := suzukiIntervalL2AsL1_ae B qL2
  have hsmul := MeasureTheory.Lp.coeFn_smul epsilon.coeff
    (suzukiIntervalL2AsL1 B qL2)
  filter_upwards [hq, hinc, hsmul] with x hq hinc hsmul
  rw [suzukiFixedWindowSignedSectionDerivativeAtPhiL1,
    suzukiFixedWindowL1Lift, smul_apply, suzukiIntervalL2ToL1_apply]
  change ((epsilon.coeff • suzukiIntervalL2AsL1 B qL2 : IntervalL1 0 B) x) = _
  rw [hsmul]
  change epsilon.coeff * (suzukiIntervalL2AsL1 B qL2 x) = _
  rw [hinc, hq]
  dsimp only [q, suzukiSmoothedApertureProfileIntegrand]
  have haMem : a ∈ Icc (0 : ℝ) B := ⟨by linarith, haB.le⟩
  rw [Set.projIcc_of_mem (by linarith : 0 ≤ B) haMem]
  change epsilon.coeff *
      (f ⟨a, haMem⟩ *
        suzukiHankelKernelContinuousRowOnReal omega B homega (by linarith) a x) = _
  have hpoint := suzukiFixedWindowPhiPoint_eq_global
    epsilon homega ha hB haB.le (⟨a, haMem⟩ : ClosedInterval 0 B) (by linarith)
  have hfpoint : f ⟨a, haMem⟩ =
      suzukiHankelPhiGlobal epsilon omega a homega ha a := by
    rw [suzukiFixedWindowPhiContinuous_apply]
    exact hpoint
  rw [hfpoint]
  dsimp only [suzukiHankelKernelContinuousRowOnReal]
  rw [Set.projIcc_of_mem (by linarith : 0 ≤ B) haMem,
    suzukiHankelKernelContinuousRow_apply]
  ring

theorem suzukiFixedWindowResolventOperatorL1_ae
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (f : IntervalL1 0 B) :
    (suzukiFixedWindowResolventOperatorL1 epsilon omega B homega a f :
        ClosedInterval 0 B → ℂ) =ᵐ[volume]
      fun x => f x + epsilon.coeff * ∫ y : ClosedInterval 0 B,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
          (suzukiApertureSet a B).indicator f y ∂volume := by
  let cut := suzukiApertureCutoffL1 a B f
  let out := suzukiCompressedHankelL1ToL2 omega B homega cut
  let inc := suzukiIntervalL2AsL1 B out
  have hcut := suzukiApertureCutoffL1_ae a B f
  have hout := suzukiCompressedHankelL1ToL2_coeFn omega B homega cut
  have hinc := suzukiIntervalL2AsL1_ae B out
  have hsmul := MeasureTheory.Lp.coeFn_smul epsilon.coeff inc
  have hadd := MeasureTheory.Lp.coeFn_add f (epsilon.coeff • inc)
  filter_upwards [hout, hinc, hsmul, hadd] with x hout hinc hsmul hadd
  rw [suzukiFixedWindowResolventOperatorL1, add_apply, one_apply_eq_self,
    suzukiFixedWindowSignedSectionL1, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,
    suzukiIntervalL2ToL1_apply]
  change ((f + epsilon.coeff • inc : IntervalL1 0 B) x) = _
  rw [hadd]
  change f x + (epsilon.coeff • inc : IntervalL1 0 B) x = _
  rw [hsmul]
  change f x + epsilon.coeff * inc x = _
  rw [hinc, hout]
  congr 2
  apply integral_congr_ae
  filter_upwards [hcut] with y hcut
  rw [hcut]

theorem suzuki_equation_409_L1
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha : 1 < a) (haB : a < B) :
    suzukiFixedWindowResolventOperatorL1 epsilon.opposite omega B homega a
        (suzukiHankelEulerPhiL1 epsilon omega a B homega ha (by linarith)) =
      ((1 / 2 : ℂ) - epsilon.coeff * (a : ℂ) *
          suzukiHankelPhiGlobal epsilon omega a homega ha a) •
          suzukiFixedWindowBoundarySourceL1 omega B homega hB a +
        (a : ℂ) •
          suzukiFixedWindowBoundarySourceDerivativeL1 omega B homega hB a := by
  let E := suzukiHankelEulerPhiL1 epsilon omega a B homega ha (by linarith : 0 < B)
  let S := suzukiFixedWindowBoundarySourceL1 omega B homega hB a
  let dS := suzukiFixedWindowBoundarySourceDerivativeL1 omega B homega hB a
  let c : ℂ := (1 / 2 : ℂ) - epsilon.coeff * (a : ℂ) *
    suzukiHankelPhiGlobal epsilon omega a homega ha a
  have hE := suzukiHankelEulerPhiL1_ae epsilon homega ha (by linarith : 0 < B)
  have hS := suzukiFixedWindowBoundarySourceL1_ae homega hB
    (by linarith : 0 < a) haB.le
  have hdS := suzukiFixedWindowBoundarySourceDerivativeL1_ae
    homega hB (by linarith : 0 < a) haB
  have hres := suzukiFixedWindowResolventOperatorL1_ae
    (a := a) epsilon.opposite homega E
  have hcS := MeasureTheory.Lp.coeFn_smul c S
  have haS := MeasureTheory.Lp.coeFn_smul (a : ℂ) dS
  have hadd := MeasureTheory.Lp.coeFn_add (c • S) ((a : ℂ) • dS)
  apply Lp.ext
  have hbad : (Set.range fun n : ℕ => (n : ℝ) / a).Countable := Set.countable_range _
  have hcuspAe : ∀ᵐ x : ℝ ∂volume,
      x ∉ Set.range (fun n : ℕ => (n : ℝ) / a) := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using
      hbad.measure_zero (volume : Measure ℝ)
  let hmp : MeasurePreserving ((↑) : ClosedInterval 0 B → ℝ)
      (volume : Measure (ClosedInterval 0 B))
      ((volume : Measure ℝ).restrict (Icc 0 B)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hgood := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae ((volume : Measure ℝ).ae_ne 0 |>.and hcuspAe))
  filter_upwards [hres, hE, hS, hdS, hcS, haS, hadd, hgood] with
      x hres hEx hS hdS hcS haS hadd hxgood
  rw [hres, hadd]
  change E x + epsilon.opposite.coeff * _ =
    (c • S : IntervalL1 0 B) x + ((a : ℂ) • dS : IntervalL1 0 B) x
  rw [hcS, haS]
  change E x + epsilon.opposite.coeff * _ =
    c * S x + (a : ℂ) * dS x
  rw [hS, hdS]
  change E x + epsilon.opposite.coeff *
      (∫ y : ClosedInterval 0 B,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
          (suzukiApertureSet a B).indicator E y) =
    c * suzukiSourceHFinite omega (a * (x : ℝ)) +
      (a : ℂ) * deriv (fun b : ℝ => suzukiSourceHFinite omega (b * (x : ℝ))) a
  rw [hEx]
  have hint :
      (∫ y : ClosedInterval 0 B,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
          (suzukiApertureSet a B).indicator E y) =
      ∫ y in (0 : ℝ)..a,
        suzukiSourceHFinite omega ((x : ℝ) * y) *
          suzukiHankelEulerPhi epsilon omega a homega ha y := by
    let F : ℝ → ℂ := fun y =>
      suzukiSourceHFinite omega ((x : ℝ) * y) *
        suzukiHankelEulerPhi epsilon omega a homega ha y
    calc
      (∫ y : ClosedInterval 0 B,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
          (suzukiApertureSet a B).indicator E y) =
        ∫ y : ClosedInterval 0 B,
          (suzukiApertureSet a B).indicator (fun y => F (y : ℝ)) y := by
          apply integral_congr_ae
          filter_upwards [hE] with y hEy
          by_cases hya : y ∈ suzukiApertureSet a B
          · rw [Set.indicator_of_mem hya, Set.indicator_of_mem hya, hEy]
          · rw [Set.indicator_of_notMem hya, Set.indicator_of_notMem hya, mul_zero]
      _ = ∫ y in (0 : ℝ)..a, F y :=
        integral_subtype_apertureSet_eq_intervalIntegral B a (by linarith) haB.le F
      _ = _ := rfl
  rw [hint, SuzukiHankelSign.coeff_opposite]
  have hx : 0 < (x : ℝ) :=
    lt_of_le_of_ne x.property.1 (Ne.symm hxgood.1)
  have hxreg : (x : ℝ) ∈ SuzukiHankelRegularX a := by
    refine ⟨hx, ?_⟩
    intro n hxn
    apply hxgood.2
    exact ⟨n, hxn.symm⟩
  have h409 := suzuki_equation_409 epsilon homega ha hxreg
  change _ = c * suzukiSourceHFinite omega (a * (x : ℝ)) + _ at h409
  simpa only [sub_eq_add_neg, neg_mul] using h409

theorem suzukiFixedWindowSignedSectionDerivativeAtPhiL1_eq_smul_source
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha : 1 < a) (haB : a < B) :
    suzukiFixedWindowSignedSectionDerivativeAtPhiL1
        epsilon omega B homega hB a (by linarith) haB =
      (epsilon.coeff *
        suzukiHankelPhiGlobal epsilon omega a homega ha a) •
          suzukiFixedWindowBoundarySourceL1 omega B homega hB a := by
  apply Lp.ext
  have hleft := suzukiFixedWindowSignedSectionDerivativeAtPhiL1_ae
    epsilon homega hB ha haB
  have hsource := suzukiFixedWindowBoundarySourceL1_ae homega hB
    (by linarith : 0 < a) haB.le
  have hsmul := MeasureTheory.Lp.coeFn_smul
    (epsilon.coeff * suzukiHankelPhiGlobal epsilon omega a homega ha a)
    (suzukiFixedWindowBoundarySourceL1 omega B homega hB a)
  filter_upwards [hleft, hsource, hsmul] with x hleft hsource hsmul
  rw [hleft, hsmul]
  change epsilon.coeff * suzukiHankelPhiGlobal epsilon omega a homega ha a *
      suzukiSourceHFinite omega (a * (x : ℝ)) =
    (epsilon.coeff * suzukiHankelPhiGlobal epsilon omega a homega ha a) *
      suzukiFixedWindowBoundarySourceL1 omega B homega hB a x
  rw [hsource]

/-- Suzuki (2012), equation (411): the coupling coefficient is the sum of the two signed
Fredholm boundary traces. -/
def suzukiHankelMu (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) : ℂ :=
  (a : ℂ) *
      suzukiHankelPhiGlobal SuzukiHankelSign.positive omega a homega ha a +
    (a : ℂ) *
      suzukiHankelPhiGlobal SuzukiHankelSign.negative omega a homega ha a

theorem suzuki_equation_411 :
    ∀ (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a),
      suzukiHankelMu omega a homega ha =
        (a : ℂ) *
            suzukiHankelPhiGlobal SuzukiHankelSign.positive omega a homega ha a +
          (a : ℂ) *
            suzukiHankelPhiGlobal SuzukiHankelSign.negative omega a homega ha a := by
  intro omega a homega ha
  rfl

theorem suzukiHankelMu_eq_sign_sum
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) :
    suzukiHankelMu omega a homega ha =
      (a : ℂ) * suzukiHankelPhiGlobal epsilon omega a homega ha a +
        (a : ℂ) * suzukiHankelPhiGlobal epsilon.opposite omega a homega ha a := by
  cases epsilon <;> simp [suzukiHankelMu, add_comm]

/-- Suzuki (2012), equation (410), as a strong `L¹` Fredholm identity.  Aperture derivatives
are the proved strong derivatives, while spatial Euler derivatives are literal weak derivatives
agreeing with the pointwise derivatives off the arithmetic cusp set. -/
theorem suzuki_equation_410_L1
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha : 1 < a) (haB : a < B) :
    suzukiFixedWindowResolventOperatorL1 epsilon omega B homega a
        ((a : ℂ) • suzukiFixedWindowPhiDerivativeL1 epsilon omega B homega hB a
            (by linarith) haB -
          suzukiHankelEulerPhiL1 epsilon.opposite omega a B homega ha (by linarith)) =
      -((1 / 2 : ℂ) + epsilon.coeff * suzukiHankelMu omega a homega ha) •
        suzukiFixedWindowBoundarySourceL1 omega B homega hB a := by
  let dP := suzukiFixedWindowPhiDerivativeL1 epsilon omega B homega hB a
    (by linarith : 0 < a) haB
  let Eopp := suzukiHankelEulerPhiL1 epsilon.opposite omega a B homega ha
    (by linarith : 0 < B)
  let S := suzukiFixedWindowBoundarySourceL1 omega B homega hB a
  let dS := suzukiFixedWindowBoundarySourceDerivativeL1 omega B homega hB a
  let endpoint := suzukiFixedWindowSignedSectionDerivativeAtPhiL1
    epsilon omega B homega hB a (by linarith : 0 < a) haB
  have h406 := suzuki_equation_406_L1 epsilon homega hB
    (by linarith : 0 < a) haB
  have h409opp0 := suzuki_equation_409_L1 epsilon.opposite homega hB ha haB
  have h409opp :
      suzukiFixedWindowResolventOperatorL1 epsilon omega B homega a Eopp =
        ((1 / 2 : ℂ) - epsilon.opposite.coeff * (a : ℂ) *
          suzukiHankelPhiGlobal epsilon.opposite omega a homega ha a) • S +
          (a : ℂ) • dS := by
    simpa only [SuzukiHankelSign.opposite_opposite] using h409opp0
  have hendpoint : endpoint =
      (epsilon.coeff *
        suzukiHankelPhiGlobal epsilon omega a homega ha a) • S := by
    exact suzukiFixedWindowSignedSectionDerivativeAtPhiL1_eq_smul_source
      epsilon homega hB ha haB
  change suzukiFixedWindowResolventOperatorL1 epsilon omega B homega a
      ((a : ℂ) • dP - Eopp) = _
  rw [map_sub, h406, h409opp]
  change ((a : ℂ) • dS - (a : ℂ) • endpoint) -
      (((1 / 2 : ℂ) - epsilon.opposite.coeff * (a : ℂ) *
        suzukiHankelPhiGlobal epsilon.opposite omega a homega ha a) • S +
        (a : ℂ) • dS) =
    -((1 / 2 : ℂ) + epsilon.coeff * suzukiHankelMu omega a homega ha) • S
  rw [hendpoint]
  rw [smul_smul]
  have hmu := suzukiHankelMu_eq_sign_sum epsilon homega ha
  rw [hmu, SuzukiHankelSign.coeff_opposite]
  module

/-- Suzuki (2012), equation (412), first in the natural strong `L¹` space.  This is the Fredholm
uniqueness step: both sides have the same image under the proved invertible resolvent. -/
theorem suzuki_equation_412_L1
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha : 1 < a) (haB : a < B) :
    (a : ℂ) • suzukiFixedWindowPhiDerivativeL1 epsilon omega B homega hB a
          (by linarith) haB -
        suzukiHankelEulerPhiL1 epsilon.opposite omega a B homega ha (by linarith) =
      -((1 / 2 : ℂ) + epsilon.coeff * suzukiHankelMu omega a homega ha) •
        suzukiFixedWindowPhiL1 epsilon omega B homega hB a := by
  let F : IntervalL1 0 B :=
    (a : ℂ) • suzukiFixedWindowPhiDerivativeL1 epsilon omega B homega hB a
        (by linarith : 0 < a) haB -
      suzukiHankelEulerPhiL1 epsilon.opposite omega a B homega ha (by linarith)
  let P := suzukiFixedWindowPhiL1 epsilon omega B homega hB a
  let S := suzukiFixedWindowBoundarySourceL1 omega B homega hB a
  let c : ℂ := -((1 / 2 : ℂ) + epsilon.coeff * suzukiHankelMu omega a homega ha)
  have h410 : suzukiFixedWindowResolventOperatorL1 epsilon omega B homega a F =
      c • S := by
    simpa only [F, S, c] using suzuki_equation_410_L1 epsilon homega hB ha haB
  have hP : suzukiFixedWindowResolventOperatorL1 epsilon omega B homega a P = S :=
    suzukiFixedWindowPhiL1_equation epsilon omega B homega hB a
  have hcP : suzukiFixedWindowResolventOperatorL1 epsilon omega B homega a
      (c • P) = c • S := by
    rw [map_smul, hP]
  have hres : suzukiFixedWindowResolventOperatorL1 epsilon omega B homega a F =
      suzukiFixedWindowResolventOperatorL1 epsilon omega B homega a (c • P) :=
    h410.trans hcP.symm
  have hinv := congrArg
    (suzukiFixedWindowResolventOperatorL1Inverse epsilon omega B homega hB a) hres
  rw [suzukiFixedWindowResolventOperatorL1_inverse_apply,
    suzukiFixedWindowResolventOperatorL1_inverse_apply] at hinv
  exact hinv

/-- Suzuki (2012), equation (413), as the equivalent strong `L¹` first-order system. -/
theorem suzuki_equation_413_L1
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha : 1 < a) (haB : a < B) :
    (a : ℂ) • suzukiFixedWindowPhiDerivativeL1 epsilon omega B homega hB a
          (by linarith) haB +
        ((1 / 2 : ℂ) + epsilon.coeff * suzukiHankelMu omega a homega ha) •
          suzukiFixedWindowPhiL1 epsilon omega B homega hB a =
      suzukiHankelEulerPhiL1 epsilon.opposite omega a B homega ha (by linarith) := by
  have h412 := suzuki_equation_412_L1 epsilon homega hB ha haB
  let A : IntervalL1 0 B :=
    (a : ℂ) • suzukiFixedWindowPhiDerivativeL1 epsilon omega B homega hB a
      (by linarith : 0 < a) haB
  let C : ℂ := (1 / 2 : ℂ) + epsilon.coeff * suzukiHankelMu omega a homega ha
  let P := suzukiFixedWindowPhiL1 epsilon omega B homega hB a
  let E := suzukiHankelEulerPhiL1 epsilon.opposite omega a B homega ha
    (by linarith : 0 < B)
  change A + C • P = E
  change A - E = -C • P at h412
  calc
    A + C • P = (A - E) + E + C • P := by module
    _ = (-C • P) + E + C • P := by rw [h412]
    _ = E := by module

theorem suzukiFixedWindowPhiL1_ae_global
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha : 1 < a) (haB : a < B) :
    (suzukiFixedWindowPhiL1 epsilon omega B homega hB a :
        ClosedInterval 0 B → ℂ) =ᵐ[volume]
      fun x => suzukiHankelPhiGlobal epsilon omega a homega ha (x : ℝ) := by
  let f := suzukiFixedWindowPhiContinuous epsilon omega B homega hB a
    (by linarith : 0 < a) haB.le
  have htoLp : ContinuousMap.toLp 1 volume ℂ f =
      suzukiFixedWindowPhiL1 epsilon omega B homega hB a :=
    suzukiFixedWindowPhiContinuous_toLp_one_eq
      epsilon omega B homega hB a (by linarith) haB.le
  have hcoe := ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (1 : ENNReal))
    (μ := (volume : Measure (ClosedInterval 0 B))) f
  rw [htoLp] at hcoe
  let hmp : MeasurePreserving ((↑) : ClosedInterval 0 B → ℝ)
      (volume : Measure (ClosedInterval 0 B))
      ((volume : Measure ℝ).restrict (Icc 0 B)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hne := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae ((volume : Measure ℝ).ae_ne 0))
  filter_upwards [hcoe, hne] with x hcoe hx0
  rw [hcoe]
  have hx : 0 < (x : ℝ) :=
    lt_of_le_of_ne x.property.1 (Ne.symm hx0)
  change suzukiFixedWindowPhiPoint epsilon omega B homega hB a x = _
  exact suzukiFixedWindowPhiPoint_eq_global
    epsilon homega ha hB haB.le x hx

theorem suzukiFixedWindowPhiDerivativeL1_equation
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha : 0 < a) (haB : a < B) :
    suzukiFixedWindowResolventOperatorL1 epsilon omega B homega a
        (suzukiFixedWindowPhiDerivativeL1 epsilon omega B homega hB a ha haB) =
      suzukiFixedWindowBoundarySourceDerivativeL1 omega B homega hB a -
        suzukiFixedWindowSignedSectionDerivativeAtPhiL1
          epsilon omega B homega hB a ha haB := by
  rw [suzukiFixedWindowPhiDerivativeL1]
  exact suzukiFixedWindowResolventOperatorL1_apply_inverse
    epsilon omega B homega hB a _

theorem suzukiFixedWindowPhiDerivativeL1_ae_formula
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha : 1 < a) (haB : a < B) :
    (suzukiFixedWindowPhiDerivativeL1 epsilon omega B homega hB a
        (by linarith) haB : ClosedInterval 0 B → ℂ) =ᵐ[volume]
      fun x =>
        deriv (fun b : ℝ => suzukiSourceHFinite omega (b * (x : ℝ))) a -
          epsilon.coeff *
            ((∫ y : ClosedInterval 0 B,
              suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
                (suzukiApertureSet a B).indicator
                  (suzukiFixedWindowPhiDerivativeL1 epsilon omega B homega hB a
                    (by linarith) haB) y) +
              suzukiHankelPhiGlobal epsilon omega a homega ha a *
                suzukiSourceHFinite omega (a * (x : ℝ))) := by
  let dP := suzukiFixedWindowPhiDerivativeL1 epsilon omega B homega hB a
    (by linarith : 0 < a) haB
  let dS := suzukiFixedWindowBoundarySourceDerivativeL1 omega B homega hB a
  let endpoint := suzukiFixedWindowSignedSectionDerivativeAtPhiL1
    epsilon omega B homega hB a (by linarith : 0 < a) haB
  have heq : suzukiFixedWindowResolventOperatorL1 epsilon omega B homega a dP =
      dS - endpoint :=
    suzukiFixedWindowPhiDerivativeL1_equation epsilon homega hB
      (by linarith : 0 < a) haB
  have hres := suzukiFixedWindowResolventOperatorL1_ae
    (a := a) epsilon homega dP
  rw [heq] at hres
  have hsub := MeasureTheory.Lp.coeFn_sub dS endpoint
  have hdS := suzukiFixedWindowBoundarySourceDerivativeL1_ae
    homega hB (by linarith : 0 < a) haB
  have hendpoint := suzukiFixedWindowSignedSectionDerivativeAtPhiL1_ae
    epsilon homega hB ha haB
  filter_upwards [hres, hsub, hdS, hendpoint] with x hres hsub hdS hendpoint
  rw [hsub] at hres
  change dS x - endpoint x = _ at hres
  rw [hdS, hendpoint] at hres
  change dP x = _
  change
    deriv (fun b : ℝ => suzukiSourceHFinite omega (b * (x : ℝ))) a -
        epsilon.coeff * suzukiHankelPhiGlobal epsilon omega a homega ha a *
          suzukiSourceHFinite omega (a * (x : ℝ)) =
      dP x + epsilon.coeff *
        (∫ y : ClosedInterval 0 B,
          suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
            (suzukiApertureSet a B).indicator dP y) at hres
  linear_combination -hres

theorem suzukiFixedWindowSmoothedPhiDerivativePoint_eq_integral_add_endpoint
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha : 1 < a) (haB : a < B)
    (x : ClosedInterval 0 B) :
    suzukiFixedWindowSmoothedPhiDerivativePoint
        epsilon omega B homega hB a (by linarith) haB x =
      (∫ y : ClosedInterval 0 B,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
          (suzukiApertureSet a B).indicator
            (suzukiFixedWindowPhiDerivativeL1 epsilon omega B homega hB a
              (by linarith) haB) y) +
        suzukiHankelPhiGlobal epsilon omega a homega ha a *
          suzukiSourceHFinite omega (a * (x : ℝ)) := by
  let dP := suzukiFixedWindowPhiDerivativeL1 epsilon omega B homega hB a
    (by linarith : 0 < a) haB
  let f := suzukiFixedWindowPhiContinuous epsilon omega B homega hB a
    (by linarith : 0 < a) haB.le
  change suzukiCompressedHankelL1ContinuousOutput omega B homega
      (suzukiApertureCutoffL1 a B dP) x +
      suzukiSmoothedApertureProfileIntegrand omega B homega (by linarith) f a x = _
  rw [suzukiCompressedHankelL1ContinuousOutput_eq_integral]
  have hcut := suzukiApertureCutoffL1_ae a B dP
  have hint :
      (∫ y : ClosedInterval 0 B,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
          suzukiApertureCutoffL1 a B dP y) =
      ∫ y : ClosedInterval 0 B,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
          (suzukiApertureSet a B).indicator dP y := by
    apply integral_congr_ae
    filter_upwards [hcut] with y hy
    rw [hy]
  rw [hint]
  congr 1
  dsimp only [suzukiSmoothedApertureProfileIntegrand]
  have haMem : a ∈ Icc (0 : ℝ) B := ⟨by linarith, haB.le⟩
  rw [Set.projIcc_of_mem (by linarith : 0 ≤ B) haMem]
  change f ⟨a, haMem⟩ *
      suzukiHankelKernelContinuousRowOnReal omega B homega (by linarith) a x = _
  have hpoint := suzukiFixedWindowPhiPoint_eq_global
    epsilon homega ha hB haB.le (⟨a, haMem⟩ : ClosedInterval 0 B) (by linarith)
  have hfpoint : f ⟨a, haMem⟩ =
      suzukiHankelPhiGlobal epsilon omega a homega ha a := by
    rw [suzukiFixedWindowPhiContinuous_apply]
    exact hpoint
  rw [hfpoint]
  dsimp only [suzukiHankelKernelContinuousRowOnReal]
  rw [Set.projIcc_of_mem (by linarith : 0 ≤ B) haMem,
    suzukiHankelKernelContinuousRow_apply, mul_comm (x : ℝ) a]

theorem suzukiFixedWindowPhiDerivativeL1_ae_point_deriv
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha : 1 < a) (haB : a < B) :
    (suzukiFixedWindowPhiDerivativeL1 epsilon omega B homega hB a
        (by linarith) haB : ClosedInterval 0 B → ℂ) =ᵐ[volume]
      fun x => deriv
        (fun b : ℝ => suzukiFixedWindowPhiPoint epsilon omega B homega hB b x) a := by
  let dP := suzukiFixedWindowPhiDerivativeL1 epsilon omega B homega hB a
    (by linarith : 0 < a) haB
  have hformula := suzukiFixedWindowPhiDerivativeL1_ae_formula
    epsilon homega hB ha haB
  have hbad : (Set.range fun n : ℕ => (n : ℝ) / a).Countable := Set.countable_range _
  have hcuspAe : ∀ᵐ x : ℝ ∂volume,
      x ∉ Set.range (fun n : ℕ => (n : ℝ) / a) := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using
      hbad.measure_zero (volume : Measure ℝ)
  let hmp : MeasurePreserving ((↑) : ClosedInterval 0 B → ℝ)
      (volume : Measure (ClosedInterval 0 B))
      ((volume : Measure ℝ).restrict (Icc 0 B)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hgood := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae ((volume : Measure ℝ).ae_ne 0 |>.and hcuspAe))
  filter_upwards [hformula, hgood] with x hformula hxgood
  have hx : 0 < (x : ℝ) :=
    lt_of_le_of_ne x.property.1 (Ne.symm hxgood.1)
  have hreg : ∀ n : ℕ, a * (x : ℝ) ≠ (n : ℝ) := by
    intro n hax
    apply hxgood.2
    refine ⟨n, ?_⟩
    calc
      (n : ℝ) / a = (a * (x : ℝ)) / a := by rw [hax]
      _ = (x : ℝ) := by field_simp
  have hpoint := hasDerivAt_suzukiFixedWindowPhiPoint
    epsilon homega hB (by linarith : 0 < a) haB x hx hreg
  rw [hpoint.deriv]
  rw [hformula]
  rw [suzukiFixedWindowPhiPointApertureDerivative,
    suzukiFixedWindowSmoothedPhiDerivativePoint_eq_integral_add_endpoint
      epsilon homega hB ha haB x]

/-- The strong aperture derivative has the literal pointwise formula everywhere almost surely.
Unlike the derivative representative, this statement does not discard the arithmetic cusp set. -/
theorem suzukiFixedWindowPhiDerivativeL1_ae_point_formula
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha : 1 < a) (haB : a < B) :
    (suzukiFixedWindowPhiDerivativeL1 epsilon omega B homega hB a
        (by linarith) haB : ClosedInterval 0 B → ℂ) =ᵐ[volume]
      fun x => suzukiFixedWindowPhiPointApertureDerivative
        epsilon omega B homega hB a (by linarith) haB x := by
  have hformula := suzukiFixedWindowPhiDerivativeL1_ae_formula
    epsilon homega hB ha haB
  filter_upwards [hformula] with x hx
  rw [hx, suzukiFixedWindowPhiPointApertureDerivative,
    suzukiFixedWindowSmoothedPhiDerivativePoint_eq_integral_add_endpoint
      epsilon homega hB ha haB x]

/-- Local full-support principle: two representatives equal almost everywhere and continuous at
one point have the same value at that point. -/
theorem eq_at_of_ae_eq_of_continuousAt
    {X E : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [NormedAddCommGroup E] [BorelSpace X]
    {mu : Measure X} [mu.IsOpenPosMeasure]
    {f g : X → E} {x : X} (hae : f =ᵐ[mu] g)
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    f x = g x := by
  by_contra hne
  have hnorm : ContinuousAt (fun y => ‖f y - g y‖) x := (hf.sub hg).norm
  have hxpos : 0 < ‖f x - g x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hev : {y | 0 < ‖f y - g y‖} ∈ 𝓝 x :=
    hnorm.eventually (Ioi_mem_nhds hxpos)
  rcases mem_nhds_iff.mp hev with ⟨s, hs, hsopen, hxs⟩
  have hsub : s ⊆ {y | f y ≠ g y} := by
    intro y hy heq
    exact (norm_pos_iff.mp (hs hy)) (sub_eq_zero.mpr heq)
  have hnull : mu {y | f y ≠ g y} = 0 := hae
  have hsnull : mu s = 0 := measure_mono_null hsub hnull
  exact (hsopen.measure_ne_zero mu ⟨x, hxs⟩) hsnull

/-- Lebesgue measure induced on a nondegenerate closed interval has full topological support.
Mathlib deliberately does not install this conditional instance globally. -/
theorem closedInterval_volume_isOpenPosMeasure {B : ℝ} (hB : 0 < B) :
    (volume : Measure (ClosedInterval 0 B)).IsOpenPosMeasure := by
  constructor
  intro U hU hUne hzero
  rcases hUne with ⟨x, hxU⟩
  rcases isOpen_induced_iff.mp hU with ⟨V, hVopen, hVU⟩
  have hxV : (x : ℝ) ∈ V := by
    rw [← Set.mem_preimage, hVU]
    exact hxU
  have hxClosure : (x : ℝ) ∈ closure (Ioo (0 : ℝ) B) := by
    rw [closure_Ioo (by linarith : (0 : ℝ) ≠ B)]
    exact x.property
  have hnonempty : (V ∩ Ioo (0 : ℝ) B).Nonempty :=
    mem_closure_iff.mp hxClosure V hVopen hxV
  have hopen : IsOpen (V ∩ Ioo (0 : ℝ) B) := hVopen.inter isOpen_Ioo
  have himageZero : volume (((↑) : ClosedInterval 0 B → ℝ) '' U) = 0 :=
    Measure.volume_subtype_coe_eq_zero_of_volume_eq_zero
      (u := Icc (0 : ℝ) B) (t := U) measurableSet_Icc.nullMeasurableSet hzero
  have hsub : V ∩ Ioo (0 : ℝ) B ⊆
      ((↑) : ClosedInterval 0 B → ℝ) '' U := by
    intro y hy
    let ys : ClosedInterval 0 B := ⟨y, ⟨hy.2.1.le, hy.2.2.le⟩⟩
    refine ⟨ys, ?_, rfl⟩
    rw [← hVU]
    exact hy.1
  exact (hopen.measure_ne_zero volume hnonempty)
    (measure_mono_null hsub himageZero)

/-- Almost-everywhere point representative of Suzuki's equation (413), with the literal aperture
derivative formula rather than an opaque `L¹` value. -/
theorem suzuki_equation_413_ae_point_formula
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha : 1 < a) (haB : a < B) :
    ∀ᵐ x : ClosedInterval 0 B ∂volume,
      (a : ℂ) * suzukiFixedWindowPhiPointApertureDerivative
          epsilon omega B homega hB a (by linarith) haB x +
        ((1 / 2 : ℂ) + epsilon.coeff * suzukiHankelMu omega a homega ha) *
          suzukiHankelPhiGlobal epsilon omega a homega ha (x : ℝ) =
        suzukiHankelEulerPhi epsilon.opposite omega a homega ha (x : ℝ) := by
  let dP := suzukiFixedWindowPhiDerivativeL1 epsilon omega B homega hB a
    (by linarith : 0 < a) haB
  let P := suzukiFixedWindowPhiL1 epsilon omega B homega hB a
  let E := suzukiHankelEulerPhiL1 epsilon.opposite omega a B homega ha
    (by linarith : 0 < B)
  let C : ℂ := (1 / 2 : ℂ) + epsilon.coeff * suzukiHankelMu omega a homega ha
  have h413 : (a : ℂ) • dP + C • P = E := by
    simpa only [dP, P, E, C] using
      suzuki_equation_413_L1 epsilon homega hB ha haB
  have heq : ((a : ℂ) • dP + C • P : IntervalL1 0 B) =ᵐ[volume]
      (E : ClosedInterval 0 B → ℂ) := by
    rw [h413]
  have hadd := MeasureTheory.Lp.coeFn_add ((a : ℂ) • dP) (C • P)
  have hsd := MeasureTheory.Lp.coeFn_smul (a : ℂ) dP
  have hsP := MeasureTheory.Lp.coeFn_smul C P
  have hdP := suzukiFixedWindowPhiDerivativeL1_ae_point_formula
    epsilon homega hB ha haB
  have hP := suzukiFixedWindowPhiL1_ae_global epsilon homega hB ha haB
  have hE := suzukiHankelEulerPhiL1_ae
    epsilon.opposite homega ha (by linarith : 0 < B)
  filter_upwards [heq, hadd, hsd, hsP, hdP, hP, hE] with
      x heq hadd hsd hsP hdP hP hE
  rw [hadd] at heq
  simp only [Pi.add_apply] at heq
  rw [hsd, hsP] at heq
  simp only [Pi.smul_apply, smul_eq_mul] at heq
  change _ * suzukiFixedWindowPhiDerivativeL1 epsilon omega B homega hB a
      (by linarith) haB x + _ *
      suzukiFixedWindowPhiL1 epsilon omega B homega hB a x =
    suzukiHankelEulerPhiL1 epsilon.opposite omega a B homega ha
      (by linarith) x at heq
  rw [hdP, hP, hE] at heq
  exact heq

theorem continuousAt_deriv_of_contDiffAt_one
    {f : ℝ → ℂ} {x : ℝ} (hf : ContDiffAt ℝ 1 f x) :
    ContinuousAt (deriv f) x := by
  have hone : ContinuousAt (fun _ : ℝ => (1 : ℝ)) x := continuousAt_const
  have h := (hf.continuousAt_fderiv (by norm_num)).clm_apply hone
  simpa only [fderiv_apply_one_eq_deriv] using h

/-- At a regular product, aperture differentiation of the arithmetic source varies continuously
with the spatial variable.  This is the local regularity needed to upgrade the `L¹` system. -/
theorem continuousAt_suzukiSourceHApertureDerivative
    {omega a x : ℝ} (homega : 1 < omega) (ha : 0 < a) (hx : 0 < x)
    (hreg : ∀ n : ℕ, a * x ≠ (n : ℝ)) :
    ContinuousAt (fun z : ℝ =>
      deriv (fun b : ℝ => suzukiSourceHFinite omega (b * z)) a) x := by
  let H := suzukiSourceHFinite omega
  have hH : ContDiffAt ℝ 1 H (a * x) :=
    contDiffAt_one_suzukiSourceHFinite_of_not_nat homega (mul_pos ha hx) hreg
  have harg : ContinuousAt (fun z : ℝ => a * z) x :=
    continuousAt_const.mul continuousAt_id
  have hderiv : ContinuousAt (fun z : ℝ => deriv H (a * z)) x :=
    (continuousAt_deriv_of_contDiffAt_one hH).comp harg
  have hmodel : ContinuousAt (fun z : ℝ =>
      (z : ℂ) * deriv H (a * z)) x :=
    Complex.continuous_ofReal.continuousAt.mul hderiv
  have hevCD : ∀ᶠ z : ℝ in 𝓝 x, ContDiffAt ℝ 1 H (a * z) :=
    harg (hH.eventually (by norm_num))
  have hevEq : (fun z : ℝ =>
      deriv (fun b : ℝ => suzukiSourceHFinite omega (b * z)) a) =ᶠ[𝓝 x]
      fun z : ℝ => (z : ℂ) * deriv H (a * z) := by
    filter_upwards [hevCD] with z hz
    have hbase : HasDerivAt H (deriv H (a * z)) (a * z) :=
      (hz.differentiableAt (by norm_num)).hasDerivAt
    have hlinear : HasDerivAt (fun b : ℝ => b * z) z a := by
      simpa using (hasDerivAt_id a).mul_const z
    have hcomp := hbase.scomp a hlinear
    have hcomp' : HasDerivAt
        (fun b : ℝ => suzukiSourceHFinite omega (b * z))
        (z • deriv H (a * z)) a :=
      hcomp.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
    simpa only [H, Complex.real_smul] using hcomp'.deriv
  exact hmodel.congr_of_eventuallyEq hevEq

/-- The smoothed part of the strong aperture derivative is a genuine continuous spatial field. -/
theorem continuous_suzukiFixedWindowSmoothedPhiDerivativePoint
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha0 : 0 < a) (haB : a < B) :
    Continuous (suzukiFixedWindowSmoothedPhiDerivativePoint
      epsilon omega B homega hB a ha0 haB) := by
  let dP := suzukiFixedWindowPhiDerivativeL1 epsilon omega B homega hB a ha0 haB
  let q := suzukiApertureCutoffL1 a B dP
  let f := suzukiFixedWindowPhiContinuous
    epsilon omega B homega hB a ha0 haB.le
  have hfirst : Continuous (fun x : ClosedInterval 0 B =>
      suzukiHankelL1FunctionalContinuous omega B homega x q) :=
    ((ContinuousLinearMap.apply ℂ ℂ) q).continuous.comp
      (suzukiHankelL1FunctionalContinuous omega B homega).continuous
  have hsecond : Continuous (fun x : ClosedInterval 0 B =>
      suzukiSmoothedApertureProfileIntegrand omega B homega
        (by linarith : 0 ≤ B) f a x) :=
    (suzukiSmoothedApertureProfileIntegrand omega B homega
      (by linarith : 0 ≤ B) f a).continuous
  change Continuous (fun x : ClosedInterval 0 B =>
    suzukiHankelL1FunctionalContinuous omega B homega x q +
      suzukiSmoothedApertureProfileIntegrand omega B homega
        (by linarith : 0 ≤ B) f a x)
  exact hfirst.add hsecond

/-- The literal point formula for the aperture derivative is continuous at every arithmetic
regular spatial point. -/
theorem continuousAt_suzukiFixedWindowPhiPointApertureDerivative
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha0 : 0 < a) (haB : a < B)
    (x : ClosedInterval 0 B) (hx : 0 < (x : ℝ))
    (hreg : ∀ n : ℕ, a * (x : ℝ) ≠ (n : ℝ)) :
    ContinuousAt (suzukiFixedWindowPhiPointApertureDerivative
      epsilon omega B homega hB a ha0 haB) x := by
  have hsourceReal := continuousAt_suzukiSourceHApertureDerivative
    homega ha0 hx hreg
  have hsource : ContinuousAt (fun y : ClosedInterval 0 B =>
      deriv (fun b : ℝ => suzukiSourceHFinite omega (b * (y : ℝ))) a) x :=
    hsourceReal.comp continuousAt_subtype_val
  have hsmooth : ContinuousAt
      (suzukiFixedWindowSmoothedPhiDerivativePoint
        epsilon omega B homega hB a ha0 haB) x :=
    (continuous_suzukiFixedWindowSmoothedPhiDerivativePoint
      epsilon homega hB ha0 haB).continuousAt
  change ContinuousAt (fun y : ClosedInterval 0 B =>
    deriv (fun b : ℝ => suzukiSourceHFinite omega (b * (y : ℝ))) a -
      epsilon.coeff * suzukiFixedWindowSmoothedPhiDerivativePoint
        epsilon omega B homega hB a ha0 haB y) x
  exact hsource.sub (continuousAt_const.mul hsmooth)

/-- The spatial Euler field is continuous at each point of Suzuki's arithmetic regular locus. -/
theorem continuousAt_suzukiHankelEulerPhi_of_regular
    (epsilon : SuzukiHankelSign) {omega a x : ℝ}
    (homega : 1 < omega) (ha : 1 < a)
    (hx : x ∈ SuzukiHankelRegularX a) :
    ContinuousAt (suzukiHankelEulerPhi epsilon omega a homega ha) x := by
  have hP := contDiffAt_one_suzukiHankelPhiGlobal_of_regular
    epsilon homega ha hx
  have hd := continuousAt_deriv_of_contDiffAt_one hP
  change ContinuousAt (fun y : ℝ =>
    (y : ℂ) * deriv (suzukiHankelPhiGlobal epsilon omega a homega ha) y +
      (1 / 2 : ℂ) * suzukiHankelPhiGlobal epsilon omega a homega ha y) x
  exact (Complex.continuous_ofReal.continuousAt.mul hd).add
    (continuousAt_const.mul hP.continuousAt)

/-- Pointwise Suzuki equation (413) on a fixed enclosing window.  The equality follows from the
strong resolvent identity and full support, not by redefining either derivative through the ODE. -/
theorem suzuki_equation_413_fixedWindow
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha : 1 < a) (haB : a < B)
    (x : ClosedInterval 0 B) (hx : (x : ℝ) ∈ SuzukiHankelRegularX a) :
    (a : ℂ) * suzukiFixedWindowPhiPointApertureDerivative
        epsilon omega B homega hB a (by linarith) haB x +
      ((1 / 2 : ℂ) + epsilon.coeff * suzukiHankelMu omega a homega ha) *
        suzukiHankelPhiGlobal epsilon omega a homega ha (x : ℝ) =
      suzukiHankelEulerPhi epsilon.opposite omega a homega ha (x : ℝ) := by
  have hprod : ∀ n : ℕ, a * (x : ℝ) ≠ (n : ℝ) := by
    intro n hax
    apply hx.2 n
    apply (eq_div_iff (ne_of_gt (by linarith : 0 < a))).2
    simpa only [mul_comm] using hax
  have hD := continuousAt_suzukiFixedWindowPhiPointApertureDerivative
    epsilon homega hB (by linarith : 0 < a) haB x hx.1 hprod
  have hP : ContinuousAt (fun y : ClosedInterval 0 B =>
      suzukiHankelPhiGlobal epsilon omega a homega ha (y : ℝ)) x :=
    (contDiffAt_one_suzukiHankelPhiGlobal_of_regular epsilon homega ha hx).continuousAt.comp
      continuousAt_subtype_val
  have hE : ContinuousAt (fun y : ClosedInterval 0 B =>
      suzukiHankelEulerPhi epsilon.opposite omega a homega ha (y : ℝ)) x :=
    (continuousAt_suzukiHankelEulerPhi_of_regular epsilon.opposite homega ha hx).comp
      continuousAt_subtype_val
  have hleft : ContinuousAt (fun y : ClosedInterval 0 B =>
      (a : ℂ) * suzukiFixedWindowPhiPointApertureDerivative
          epsilon omega B homega hB a (by linarith) haB y +
        ((1 / 2 : ℂ) + epsilon.coeff * suzukiHankelMu omega a homega ha) *
          suzukiHankelPhiGlobal epsilon omega a homega ha (y : ℝ)) x :=
    (continuousAt_const.mul hD).add (continuousAt_const.mul hP)
  letI : (volume : Measure (ClosedInterval 0 B)).IsOpenPosMeasure :=
    closedInterval_volume_isOpenPosMeasure (by linarith)
  exact eq_at_of_ae_eq_of_continuousAt
    (suzuki_equation_413_ae_point_formula epsilon homega hB ha haB) hleft hE

/-- Exact pointwise Suzuki equation (413) on the printed joint regular locus.  The aperture
derivative is the derivative of the literal global family, while the right side is the independently
defined spatial Euler derivative of the opposite-sign family. -/
theorem suzuki_equation_413
    (epsilon : SuzukiHankelSign) {omega a x : ℝ}
    (homega : 1 < omega) (hx : 0 < x)
    (ha : a ∈ SuzukiHankelRegularAperture x) :
    (a : ℂ) * deriv
        (suzukiHankelPhiGlobalApertureReal epsilon omega x homega) a +
      ((1 / 2 : ℂ) + epsilon.coeff * suzukiHankelMu omega a homega ha.1) *
        suzukiHankelPhiGlobal epsilon omega a homega ha.1 x =
      suzukiHankelEulerPhi epsilon.opposite omega a homega ha.1 x := by
  let B : ℝ := max a x + 1
  have haB : a < B := by dsimp only [B]; linarith [le_max_left a x]
  have hxB : x < B := by dsimp only [B]; linarith [le_max_right a x]
  have hB : 1 < B := ha.1.trans haB
  let xB : ClosedInterval 0 B := ⟨x, ⟨hx.le, hxB.le⟩⟩
  have hprod : ∀ n : ℕ, a * x ≠ (n : ℝ) := by
    intro n hax
    apply (ha.2 n).1
    apply (eq_div_iff hx.ne').2
    exact hax
  have hxRegular : x ∈ SuzukiHankelRegularX a := by
    refine ⟨hx, ?_⟩
    intro n hxn
    apply hprod n
    apply (eq_div_iff (ne_of_gt (lt_trans zero_lt_one ha.1))).1 at hxn
    simpa only [mul_comm] using hxn
  have hfixed := suzuki_equation_413_fixedWindow
    epsilon homega hB ha.1 haB xB hxRegular
  have hlocal := hasDerivAt_suzukiFixedWindowPhiPoint
    epsilon homega hB (lt_trans zero_lt_one ha.1) haB xB hx hprod
  have hev : suzukiHankelPhiGlobalApertureReal epsilon omega x homega =ᶠ[𝓝 a]
      fun b : ℝ => suzukiFixedWindowPhiPoint
        epsilon omega B homega hB b xB := by
    filter_upwards [Ioo_mem_nhds ha.1 haB] with b hb
    rw [suzukiHankelPhiGlobalApertureReal, dif_pos hb.1]
    exact (suzukiFixedWindowPhiPoint_eq_global
      epsilon homega hb.1 hB hb.2.le xB hx).symm
  have hderiv : deriv
      (suzukiHankelPhiGlobalApertureReal epsilon omega x homega) a =
      suzukiFixedWindowPhiPointApertureDerivative
        epsilon omega B homega hB a (lt_trans zero_lt_one ha.1) haB xB :=
    (hlocal.congr_of_eventuallyEq hev).deriv
  rw [hderiv]
  exact hfixed

/-- Exact pointwise Suzuki equation (412), obtained by the printed rearrangement of (413). -/
theorem suzuki_equation_412
    (epsilon : SuzukiHankelSign) {omega a x : ℝ}
    (homega : 1 < omega) (hx : 0 < x)
    (ha : a ∈ SuzukiHankelRegularAperture x) :
    (a : ℂ) * deriv
        (suzukiHankelPhiGlobalApertureReal epsilon omega x homega) a -
      suzukiHankelEulerPhi epsilon.opposite omega a homega ha.1 x =
      -((1 / 2 : ℂ) + epsilon.coeff * suzukiHankelMu omega a homega ha.1) *
        suzukiHankelPhiGlobal epsilon omega a homega ha.1 x := by
  have h413 := suzuki_equation_413 epsilon homega hx ha
  linear_combination h413

end RHTower
