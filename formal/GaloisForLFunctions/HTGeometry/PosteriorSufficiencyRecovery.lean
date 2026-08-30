import GaloisForLFunctions.HTGeometry.PosteriorContrastProjection
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Zero information current is exact recoverability

The vertical information current of a common observation kernel vanishes exactly when the
observed experiment can be pushed back onto the source experiment by one Markov kernel.  The
recovery kernel is the conditional law of the source given the observation under the balanced
joint law, and it is produced by disintegration, not assumed.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X]

/-- The balanced joint law read with the observation first. -/
def swapJoint (κ : Kernel X Y) (P Q : Measure X) : Measure (Y × X) :=
  ((balancedLaw P Q) ⊗ₘ κ).map Prod.swap

instance isProbabilityMeasure_swapJoint (κ : Kernel X Y) [IsMarkovKernel κ] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (swapJoint κ P Q) := by
  rw [swapJoint]
  constructor
  rw [Measure.map_apply measurable_swap MeasurableSet.univ]
  simp

omit [StandardBorelSpace X] [Nonempty X] in
theorem swapJoint_fst (κ : Kernel X Y) [IsMarkovKernel κ] (P Q : Measure X)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    (swapJoint κ P Q).fst = ⇑κ ∘ₘ (balancedLaw P Q) := by
  rw [swapJoint, Measure.fst, Measure.map_map measurable_fst measurable_swap,
    show (Prod.fst ∘ (Prod.swap : X × Y → Y × X)) = Prod.snd from rfl,
    ← Measure.snd, Measure.snd_compProd]

omit [StandardBorelSpace X] [Nonempty X] in
theorem swapJoint_snd (κ : Kernel X Y) [IsMarkovKernel κ] (P Q : Measure X)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    (swapJoint κ P Q).snd = balancedLaw P Q := by
  rw [swapJoint, Measure.snd, Measure.map_map measurable_snd measurable_swap,
    show (Prod.snd ∘ (Prod.swap : X × Y → Y × X)) = Prod.fst from rfl,
    ← Measure.fst, Measure.fst_compProd]

/-- `(PMP.15)`  The recovery kernel: the conditional law of the source given the observation. -/
def recoveryKernel (κ : Kernel X Y) [IsMarkovKernel κ] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] : Kernel Y X :=
  (swapJoint κ P Q).condKernel

instance isMarkovKernel_recoveryKernel (κ : Kernel X Y) [IsMarkovKernel κ] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    IsMarkovKernel (recoveryKernel κ P Q) :=
  Measure.instIsMarkovKernelCondKernel _

theorem swapJoint_disintegration (κ : Kernel X Y) [IsMarkovKernel κ] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    (⇑κ ∘ₘ (balancedLaw P Q)) ⊗ₘ (recoveryKernel κ P Q) = swapJoint κ P Q := by
  rw [← swapJoint_fst κ P Q, recoveryKernel]
  exact (swapJoint κ P Q).disintegrate _

/-! ## Zero current gives exact recovery -/

omit [StandardBorelSpace X] [Nonempty X] in
theorem ae_swapJoint_of_ae_compProd (κ : Kernel X Y) [IsMarkovKernel κ] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {p : X × Y → Prop}
    (hp : MeasurableSet {z | p z}) (h : ∀ᵐ z ∂((balancedLaw P Q) ⊗ₘ κ), p z) :
    ∀ᵐ q ∂(swapJoint κ P Q), p q.swap := by
  rw [swapJoint]
  refine (ae_map_iff measurable_swap.aemeasurable (measurable_swap hp)).mpr ?_
  simpa using h

omit [StandardBorelSpace X] [Nonempty X] in
/-- Zero information current, read on the Radon--Nikodym densities. -/
theorem rnDeriv_eq_of_informationCurrent (κ : Kernel X Y) [IsMarkovKernel κ] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hj : ∀ᵐ z ∂((balancedLaw P Q) ⊗ₘ κ), informationCurrent κ P Q z = 0) :
    ∀ᵐ q ∂(swapJoint κ P Q),
      (⇑κ ∘ₘ P).rnDeriv (⇑κ ∘ₘ (balancedLaw P Q)) q.1 = P.rnDeriv (balancedLaw P Q) q.2 := by
  have hjs : ∀ᵐ q ∂(swapJoint κ P Q), informationCurrent κ P Q q.swap = 0 :=
    ae_swapJoint_of_ae_compProd κ P Q
      (measurableSet_eq_fun (measurable_informationCurrent κ P Q) measurable_const) hj
  have hfin1 : ∀ᵐ q ∂(swapJoint κ P Q),
      (⇑κ ∘ₘ P).rnDeriv (⇑κ ∘ₘ (balancedLaw P Q)) q.1 < ⊤ := by
    have h1 : ∀ᵐ y ∂((swapJoint κ P Q).map Prod.fst),
        (⇑κ ∘ₘ P).rnDeriv (⇑κ ∘ₘ (balancedLaw P Q)) y < ⊤ := by
      rw [← Measure.fst, swapJoint_fst]
      exact Measure.rnDeriv_lt_top _ _
    exact (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_lt (Measure.measurable_rnDeriv _ _) measurable_const)).mp h1
  have hfin2 : ∀ᵐ q ∂(swapJoint κ P Q), P.rnDeriv (balancedLaw P Q) q.2 < ⊤ := by
    have h1 : ∀ᵐ x ∂((swapJoint κ P Q).map Prod.snd), P.rnDeriv (balancedLaw P Q) x < ⊤ := by
      rw [← Measure.snd, swapJoint_snd]
      exact Measure.rnDeriv_lt_top _ _
    exact (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_lt (Measure.measurable_rnDeriv _ _) measurable_const)).mp h1
  filter_upwards [hjs, hfin1, hfin2] with q hq h1 h2
  have hd : posteriorContrast P Q q.2
      = posteriorContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) q.1 := by
    have : informationCurrent κ P Q q.swap
        = posteriorContrast P Q q.2 - posteriorContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) q.1 := rfl
    rw [this] at hq
    linarith [hq]
  have hbal : balancedLaw (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) = ⇑κ ∘ₘ (balancedLaw P Q) := balancedLaw_comp κ P Q
  rw [posteriorContrast, posteriorContrast, hbal] at hd
  have heq : ((⇑κ ∘ₘ P).rnDeriv (⇑κ ∘ₘ (balancedLaw P Q)) q.1).toReal
      = (P.rnDeriv (balancedLaw P Q) q.2).toReal := by linarith
  exact (ENNReal.toReal_eq_toReal_iff' h1.ne h2.ne).mp heq

omit [StandardBorelSpace X] [Nonempty X] in
/-- Composing an absolutely continuous pair with a common kernel preserves absolute
continuity. -/
theorem absolutelyContinuous_comp {κ : Kernel X Y} [IsSFiniteKernel κ] {ν μ : Measure X}
    (h : ν ≪ μ) : ⇑κ ∘ₘ ν ≪ ⇑κ ∘ₘ μ := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hzero => ?_
  rw [Measure.bind_apply hs (Kernel.aemeasurable κ)] at hzero ⊢
  refine (lintegral_eq_zero_iff (Kernel.measurable_coe κ hs)).mpr ?_
  exact h ((lintegral_eq_zero_iff (Kernel.measurable_coe κ hs)).mp hzero)

/-- Exact recovery of one member of the experiment. -/
theorem comp_recoveryKernel_of_rnDeriv (κ : Kernel X Y) [IsMarkovKernel κ] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (R : Measure X) [IsProbabilityMeasure R]
    (hR : R ≪ balancedLaw P Q)
    (heq : ∀ᵐ q ∂(swapJoint κ P Q),
      (⇑κ ∘ₘ R).rnDeriv (⇑κ ∘ₘ (balancedLaw P Q)) q.1 = R.rnDeriv (balancedLaw P Q) q.2) :
    (recoveryKernel κ P Q) ∘ₘ (⇑κ ∘ₘ R) = R := by
  have hRY : (⇑κ ∘ₘ R) ≪ ⇑κ ∘ₘ (balancedLaw P Q) := absolutelyContinuous_comp hR
  have hPY : ⇑κ ∘ₘ R
      = (⇑κ ∘ₘ (balancedLaw P Q)).withDensity ((⇑κ ∘ₘ R).rnDeriv (⇑κ ∘ₘ (balancedLaw P Q))) :=
    (Measure.withDensity_rnDeriv_eq _ _ hRY).symm
  calc (recoveryKernel κ P Q) ∘ₘ (⇑κ ∘ₘ R)
      = ((⇑κ ∘ₘ R) ⊗ₘ (recoveryKernel κ P Q)).snd := (Measure.snd_compProd _ _).symm
    _ = (((⇑κ ∘ₘ (balancedLaw P Q)).withDensity
          ((⇑κ ∘ₘ R).rnDeriv (⇑κ ∘ₘ (balancedLaw P Q)))) ⊗ₘ (recoveryKernel κ P Q)).snd := by
          rw [← hPY]
    _ = (((⇑κ ∘ₘ (balancedLaw P Q)) ⊗ₘ (recoveryKernel κ P Q)).withDensity
          (fun q => (⇑κ ∘ₘ R).rnDeriv (⇑κ ∘ₘ (balancedLaw P Q)) q.1)).snd := by
          rw [compProd_withDensity_fst _ _ (Measure.measurable_rnDeriv _ _)]
    _ = ((swapJoint κ P Q).withDensity
          (fun q => (⇑κ ∘ₘ R).rnDeriv (⇑κ ∘ₘ (balancedLaw P Q)) q.1)).snd := by
          rw [swapJoint_disintegration]
    _ = ((swapJoint κ P Q).withDensity
          (fun q => R.rnDeriv (balancedLaw P Q) q.2)).snd := by
          rw [withDensity_congr_ae heq]
    _ = ((swapJoint κ P Q).map Prod.snd).withDensity (R.rnDeriv (balancedLaw P Q)) := by
          rw [Measure.snd, show (fun q : Y × X => R.rnDeriv (balancedLaw P Q) q.2)
              = (R.rnDeriv (balancedLaw P Q)) ∘ Prod.snd from rfl,
            map_withDensity_comp (swapJoint κ P Q) measurable_snd
              (Measure.measurable_rnDeriv _ _)]
    _ = (balancedLaw P Q).withDensity (R.rnDeriv (balancedLaw P Q)) := by
          rw [← Measure.snd, swapJoint_snd]
    _ = R := Measure.withDensity_rnDeriv_eq _ _ hR

omit [StandardBorelSpace X] [Nonempty X] in
theorem rnDeriv_right_eq_of_informationCurrent (κ : Kernel X Y) [IsMarkovKernel κ]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hj : ∀ᵐ z ∂((balancedLaw P Q) ⊗ₘ κ), informationCurrent κ P Q z = 0) :
    ∀ᵐ q ∂(swapJoint κ P Q),
      (⇑κ ∘ₘ Q).rnDeriv (⇑κ ∘ₘ (balancedLaw P Q)) q.1 = Q.rnDeriv (balancedLaw P Q) q.2 := by
  have hbal : balancedLaw (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) = ⇑κ ∘ₘ (balancedLaw P Q) := balancedLaw_comp κ P Q
  have hjs : ∀ᵐ q ∂(swapJoint κ P Q), informationCurrent κ P Q q.swap = 0 :=
    ae_swapJoint_of_ae_compProd κ P Q
      (measurableSet_eq_fun (measurable_informationCurrent κ P Q) measurable_const) hj
  have hsrc : ∀ᵐ q ∂(swapJoint κ P Q),
      (Q.rnDeriv (balancedLaw P Q) q.2).toReal = 1 - posteriorContrast P Q q.2 := by
    have h1 : ∀ᵐ x ∂((swapJoint κ P Q).map Prod.snd),
        (Q.rnDeriv (balancedLaw P Q) x).toReal = 1 - posteriorContrast P Q x := by
      rw [← Measure.snd, swapJoint_snd]
      exact rnDeriv_right_toReal P Q
    exact (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_eq_fun ((Measure.measurable_rnDeriv _ _).ennreal_toReal)
        (measurable_const.sub (measurable_posteriorContrast P Q)))).mp h1
  have hobs : ∀ᵐ q ∂(swapJoint κ P Q),
      ((⇑κ ∘ₘ Q).rnDeriv (⇑κ ∘ₘ (balancedLaw P Q)) q.1).toReal
        = 1 - posteriorContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) q.1 := by
    have h1 : ∀ᵐ y ∂((swapJoint κ P Q).map Prod.fst),
        ((⇑κ ∘ₘ Q).rnDeriv (⇑κ ∘ₘ (balancedLaw P Q)) y).toReal
          = 1 - posteriorContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) y := by
      rw [← Measure.fst, swapJoint_fst, ← hbal]
      exact rnDeriv_right_toReal _ _
    exact (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_eq_fun ((Measure.measurable_rnDeriv _ _).ennreal_toReal)
        (measurable_const.sub (measurable_posteriorContrast _ _)))).mp h1
  have hfin1 : ∀ᵐ q ∂(swapJoint κ P Q),
      (⇑κ ∘ₘ Q).rnDeriv (⇑κ ∘ₘ (balancedLaw P Q)) q.1 < ⊤ := by
    have h1 : ∀ᵐ y ∂((swapJoint κ P Q).map Prod.fst),
        (⇑κ ∘ₘ Q).rnDeriv (⇑κ ∘ₘ (balancedLaw P Q)) y < ⊤ := by
      rw [← Measure.fst, swapJoint_fst]
      exact Measure.rnDeriv_lt_top _ _
    exact (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_lt (Measure.measurable_rnDeriv _ _) measurable_const)).mp h1
  have hfin2 : ∀ᵐ q ∂(swapJoint κ P Q), Q.rnDeriv (balancedLaw P Q) q.2 < ⊤ := by
    have h1 : ∀ᵐ x ∂((swapJoint κ P Q).map Prod.snd), Q.rnDeriv (balancedLaw P Q) x < ⊤ := by
      rw [← Measure.snd, swapJoint_snd]
      exact Measure.rnDeriv_lt_top _ _
    exact (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_lt (Measure.measurable_rnDeriv _ _) measurable_const)).mp h1
  filter_upwards [hjs, hsrc, hobs, hfin1, hfin2] with q hq h1 h2 h3 h4
  have hd : posteriorContrast P Q q.2 = posteriorContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) q.1 := by
    have : informationCurrent κ P Q q.swap
        = posteriorContrast P Q q.2 - posteriorContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) q.1 := rfl
    rw [this] at hq
    linarith
  refine (ENNReal.toReal_eq_toReal_iff' h3.ne h4.ne).mp ?_
  rw [h2, h1, hd]

/-! ## Theorem 4.1 -/

/-- **Theorem 4.1.**  Zero vertical current, contrast agreement, equality of triangular
discrimination, and exact Blackwell recoverability are equivalent. -/
theorem zeroInformationCurrent_tfae (κ : Kernel X Y) [IsMarkovKernel κ] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    List.TFAE
      [∀ᵐ z ∂((balancedLaw P Q) ⊗ₘ κ), informationCurrent κ P Q z = 0,
       ∀ᵐ z ∂((balancedLaw P Q) ⊗ₘ κ),
          posteriorContrast P Q z.1 = posteriorContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) z.2,
       triangularDiscrimination P Q = triangularDiscrimination (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q),
       ∃ L : Kernel Y X, IsMarkovKernel L ∧ ⇑L ∘ₘ (⇑κ ∘ₘ P) = P ∧ ⇑L ∘ₘ (⇑κ ∘ₘ Q) = Q] := by
  tfae_have 1 ↔ 2 := by
    constructor
    · intro h
      filter_upwards [h] with z hz
      have : informationCurrent κ P Q z
          = posteriorContrast P Q z.1 - posteriorContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) z.2 := rfl
      rw [this] at hz
      linarith
    · intro h
      filter_upwards [h] with z hz
      have : informationCurrent κ P Q z
          = posteriorContrast P Q z.1 - posteriorContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) z.2 := rfl
      rw [this, hz, sub_self]
  tfae_have 1 ↔ 3 := by
    rw [triangularDiscrimination_eq_add κ P Q]
    constructor
    · intro h
      have : ∫ z, (informationCurrent κ P Q z) ^ 2 ∂((balancedLaw P Q) ⊗ₘ κ) = 0 := by
        refine integral_eq_zero_of_ae ?_
        filter_upwards [h] with z hz
        rw [hz]
        norm_num
      rw [this]
      ring
    · intro h
      have hzero : ∫ z, (informationCurrent κ P Q z) ^ 2 ∂((balancedLaw P Q) ⊗ₘ κ) = 0 := by
        linarith
      have := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg _)
        (integrable_sq_informationCurrent κ P Q)).mp hzero
      filter_upwards [this] with z hz
      simpa [pow_eq_zero_iff] using hz
  tfae_have 1 → 4 := by
    intro h
    refine ⟨recoveryKernel κ P Q, inferInstance, ?_, ?_⟩
    · exact comp_recoveryKernel_of_rnDeriv κ P Q P (absolutelyContinuous_balancedLaw_left P Q)
        (rnDeriv_eq_of_informationCurrent κ P Q h)
    · exact comp_recoveryKernel_of_rnDeriv κ P Q Q (absolutelyContinuous_balancedLaw_right P Q)
        (rnDeriv_right_eq_of_informationCurrent κ P Q h)
  tfae_have 4 → 3 := by
    rintro ⟨L, hL, hP, hQ⟩
    refine le_antisymm ?_ (triangularDiscrimination_comp_le κ P Q)
    calc triangularDiscrimination P Q
        = triangularDiscrimination (⇑L ∘ₘ (⇑κ ∘ₘ P)) (⇑L ∘ₘ (⇑κ ∘ₘ Q)) := by rw [hP, hQ]
      _ ≤ triangularDiscrimination (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) :=
          triangularDiscrimination_comp_le L _ _
  tfae_finish

end

end GaloisForLFunctions.HTGeometry
