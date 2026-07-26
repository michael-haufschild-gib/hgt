import GaloisForLFunctions.RHTower.BourgainFejerSpacing

open MeasureTheory
open scoped ComplexConjugate

namespace RHTower

noncomputable section

def bourgainHalfBoxMeasure
    (X : BourgainPhaseSpace) : Measure BourgainPhaseSpace :=
  Measure.pi fun j : Fin 4 =>
    volume.restrict (Set.Ioc (-X j / 2) (X j / 2))

theorem bourgainAdditiveCharacter_eq_prod_unitCharacter
    (z d : BourgainPhaseSpace) :
    bourgainAdditiveCharacter z d =
      ∏ j : Fin 4, bourgainUnitCharacter (d j * z j) := by
  unfold bourgainAdditiveCharacter bourgainUnitCharacter bourgainDot
  rw [← Complex.exp_sum]
  apply congrArg Complex.exp
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem integral_bourgainAdditiveCharacter_halfBox
    {X : BourgainPhaseSpace} (hX : ∀ j, 0 ≤ X j)
    (d : BourgainPhaseSpace) :
    ∫ z : BourgainPhaseSpace,
        bourgainAdditiveCharacter z d ∂bourgainHalfBoxMeasure X =
      ∏ j : Fin 4, bourgainIntervalCharacterIntegral (X j) (d j) := by
  rw [show
      (fun z : BourgainPhaseSpace => bourgainAdditiveCharacter z d) =
        fun z => ∏ j : Fin 4, bourgainUnitCharacter (d j * z j) by
    funext z
    exact bourgainAdditiveCharacter_eq_prod_unitCharacter z d]
  unfold bourgainHalfBoxMeasure
  have hprod :=
    integral_fintype_prod_eq_prod
      (𝕜 := ℂ)
      (fun j : Fin 4 =>
        fun z : ℝ => bourgainUnitCharacter (d j * z))
      (μ := fun j : Fin 4 =>
        volume.restrict (Set.Ioc (-X j / 2) (X j / 2)))
  rw [hprod]
  apply Finset.prod_congr rfl
  intro j hj
  rw [← intervalIntegral.integral_of_le (by linarith [hX j])]
  rfl

theorem norm_sq_integral_bourgainAdditiveCharacter_halfBox
    {X : BourgainPhaseSpace} (hX : ∀ j, 0 ≤ X j)
    (d : BourgainPhaseSpace) :
    ‖∫ z : BourgainPhaseSpace,
        bourgainAdditiveCharacter z d ∂bourgainHalfBoxMeasure X‖ ^
          (2 : ℕ) =
      ∏ j : Fin 4, bourgainFejerKernel (X j) (d j) := by
  rw [integral_bourgainAdditiveCharacter_halfBox hX]
  rw [norm_prod]
  simp only [bourgainFejerKernel, ← Finset.prod_pow]

theorem bourgainAdditiveCharacter_sub_left
    (z w d : BourgainPhaseSpace) :
    bourgainAdditiveCharacter (z - w) d =
      bourgainAdditiveCharacter z d *
        conj (bourgainAdditiveCharacter w d) := by
  unfold bourgainAdditiveCharacter bourgainDot
  have hdot :
      (∑ j : Fin 4, (z j - w j) * d j) =
        (∑ j : Fin 4, z j * d j) -
          ∑ j : Fin 4, w j * d j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp only [Pi.sub_apply]
  rw [hdot, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_sum, map_mul, map_ofNat, Complex.conj_ofReal,
    Complex.conj_I]
  ring

theorem integral_integral_bourgainAdditiveCharacter_sub_halfBox
    {X : BourgainPhaseSpace} (hX : ∀ j, 0 ≤ X j)
    (d : BourgainPhaseSpace) :
    (∫ z : BourgainPhaseSpace,
      ∫ w : BourgainPhaseSpace,
        bourgainAdditiveCharacter (z - w) d
          ∂bourgainHalfBoxMeasure X
        ∂bourgainHalfBoxMeasure X) =
      (∏ j : Fin 4, bourgainFejerKernel (X j) (d j) : ℝ) := by
  let J : ℂ :=
    ∫ z : BourgainPhaseSpace,
      bourgainAdditiveCharacter z d ∂bourgainHalfBoxMeasure X
  have hinner (z : BourgainPhaseSpace) :
      (∫ w : BourgainPhaseSpace,
          bourgainAdditiveCharacter (z - w) d
            ∂bourgainHalfBoxMeasure X) =
        bourgainAdditiveCharacter z d * conj J := by
    rw [show
        (fun w : BourgainPhaseSpace =>
          bourgainAdditiveCharacter (z - w) d) =
          fun w =>
            bourgainAdditiveCharacter z d *
              conj (bourgainAdditiveCharacter w d) by
      funext w
      exact bourgainAdditiveCharacter_sub_left z w d]
    rw [integral_const_mul, integral_conj]
  simp_rw [hinner]
  rw [integral_mul_const]
  change J * conj J = _
  rw [Complex.mul_conj, ← Complex.sq_norm]
  simpa only [J] using
    congrArg (fun r : ℝ => (r : ℂ))
      (norm_sq_integral_bourgainAdditiveCharacter_halfBox hX d)

noncomputable instance bourgainHalfBoxMeasure_isFinite
    (X : BourgainPhaseSpace) :
    IsFiniteMeasure (bourgainHalfBoxMeasure X) where
  measure_univ_lt_top := by
    rw [show
      (Set.univ : Set BourgainPhaseSpace) =
        Set.univ.pi (fun _j : Fin 4 => Set.univ) by simp]
    rw [bourgainHalfBoxMeasure, Measure.pi_pi]
    simp
    apply ENNReal.prod_lt_top
    intro j hj
    exact ENNReal.ofReal_lt_top

/-- Fourier cloud of the six-fold moment vectors. -/
def bourgainSixfoldCharacterCloud
    (H : ℕ) (z : BourgainPhaseSpace) : ℂ :=
  ∑ h : Fin 6 → Fin H,
    bourgainAdditiveCharacter z (bourgainSixfoldMoment h)

theorem bourgainSixfoldCharacterCloud_norm_sq
    (H : ℕ) (z : BourgainPhaseSpace) :
    (‖bourgainSixfoldCharacterCloud H z‖ ^ (2 : ℕ) : ℂ) =
      ∑ h : Fin 6 → Fin H, ∑ h' : Fin 6 → Fin H,
        bourgainAdditiveCharacter z
          (bourgainSixfoldMoment h - bourgainSixfoldMoment h') := by
  let A : (Fin 6 → Fin H) → ℂ := fun h =>
    bourgainAdditiveCharacter z (bourgainSixfoldMoment h)
  rw [show
      (‖bourgainSixfoldCharacterCloud H z‖ ^ (2 : ℕ) : ℂ) =
        bourgainSixfoldCharacterCloud H z *
          conj (bourgainSixfoldCharacterCloud H z) by
    simpa [Complex.normSq_eq_norm_sq] using
      (Complex.mul_conj (bourgainSixfoldCharacterCloud H z)).symm]
  unfold bourgainSixfoldCharacterCloud
  rw [map_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro h
  apply Fintype.sum_congr
  intro h'
  exact
    (bourgainAdditiveCharacter_sub z
      (bourgainSixfoldMoment h) (bourgainSixfoldMoment h')).symm

theorem integrable_bourgainAdditiveCharacter_halfBox
    (X d : BourgainPhaseSpace) :
    Integrable (fun z : BourgainPhaseSpace =>
      bourgainAdditiveCharacter z d) (bourgainHalfBoxMeasure X) := by
  refine Integrable.of_bound ?_ 1 ?_
  · apply Continuous.aestronglyMeasurable
    unfold bourgainAdditiveCharacter bourgainDot
    fun_prop
  · filter_upwards with z
    exact (norm_bourgainAdditiveCharacter z d).le

theorem integrable_bourgainAdditiveCharacter_sub_halfBox
    (X z d : BourgainPhaseSpace) :
    Integrable (fun w : BourgainPhaseSpace =>
      bourgainAdditiveCharacter (z - w) d)
      (bourgainHalfBoxMeasure X) := by
  refine Integrable.of_bound ?_ 1 ?_
  · apply Continuous.aestronglyMeasurable
    unfold bourgainAdditiveCharacter bourgainDot
    fun_prop
  · filter_upwards with w
    exact (norm_bourgainAdditiveCharacter (z - w) d).le

theorem integrable_integral_bourgainAdditiveCharacter_sub_halfBox
    (X d : BourgainPhaseSpace) :
    Integrable
      (fun z : BourgainPhaseSpace =>
        ∫ w : BourgainPhaseSpace,
          bourgainAdditiveCharacter (z - w) d
            ∂bourgainHalfBoxMeasure X)
      (bourgainHalfBoxMeasure X) := by
  let J : ℂ :=
    conj
      (∫ w : BourgainPhaseSpace,
        bourgainAdditiveCharacter w d ∂bourgainHalfBoxMeasure X)
  have heq :
      (fun z : BourgainPhaseSpace =>
        ∫ w : BourgainPhaseSpace,
          bourgainAdditiveCharacter (z - w) d
            ∂bourgainHalfBoxMeasure X) =
        fun z => bourgainAdditiveCharacter z d * J := by
    funext z
    rw [show
        (fun w : BourgainPhaseSpace =>
          bourgainAdditiveCharacter (z - w) d) =
          fun w =>
            bourgainAdditiveCharacter z d *
              conj (bourgainAdditiveCharacter w d) by
      funext w
      exact bourgainAdditiveCharacter_sub_left z w d]
    rw [integral_const_mul, integral_conj]
  rw [heq]
  exact (integrable_bourgainAdditiveCharacter_halfBox X d).mul_const J

theorem bourgainFejerSpacingEnergy_eq_doubleMoment
    {H : ℕ} {X : BourgainPhaseSpace}
    (hX : ∀ j, 0 ≤ X j) :
    bourgainFejerSpacingEnergy H X =
      ∫ z : BourgainPhaseSpace,
        ∫ w : BourgainPhaseSpace,
          ‖bourgainSixfoldCharacterCloud H (z - w)‖ ^ (2 : ℕ)
            ∂bourgainHalfBoxMeasure X
          ∂bourgainHalfBoxMeasure X := by
  have hcomplex :
      (bourgainFejerSpacingEnergy H X : ℂ) =
        ∫ z : BourgainPhaseSpace,
          ∫ w : BourgainPhaseSpace,
            (‖bourgainSixfoldCharacterCloud H (z - w)‖ ^
              (2 : ℕ) : ℂ)
              ∂bourgainHalfBoxMeasure X
            ∂bourgainHalfBoxMeasure X := by
    unfold bourgainFejerSpacingEnergy
    push_cast
    rw [show
        (fun z : BourgainPhaseSpace =>
          ∫ w : BourgainPhaseSpace,
            (‖bourgainSixfoldCharacterCloud H (z - w)‖ ^
              (2 : ℕ) : ℂ)
              ∂bourgainHalfBoxMeasure X) =
          fun z =>
            ∫ w : BourgainPhaseSpace,
              ∑ h : Fin 6 → Fin H, ∑ h' : Fin 6 → Fin H,
                bourgainAdditiveCharacter (z - w)
                  (bourgainSixfoldMoment h -
                    bourgainSixfoldMoment h')
                ∂bourgainHalfBoxMeasure X by
      funext z
      apply integral_congr_ae
      filter_upwards with w
      exact bourgainSixfoldCharacterCloud_norm_sq H (z - w)]
    have hinner (z : BourgainPhaseSpace) :
        (∫ w : BourgainPhaseSpace,
          ∑ h : Fin 6 → Fin H, ∑ h' : Fin 6 → Fin H,
            bourgainAdditiveCharacter (z - w)
              (bourgainSixfoldMoment h - bourgainSixfoldMoment h')
            ∂bourgainHalfBoxMeasure X) =
          ∑ h : Fin 6 → Fin H, ∑ h' : Fin 6 → Fin H,
            ∫ w : BourgainPhaseSpace,
              bourgainAdditiveCharacter (z - w)
                (bourgainSixfoldMoment h - bourgainSixfoldMoment h')
              ∂bourgainHalfBoxMeasure X := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro h hh
        rw [integral_finsetSum]
        intro h' hh'
        exact
          integrable_bourgainAdditiveCharacter_sub_halfBox X z
            (bourgainSixfoldMoment h - bourgainSixfoldMoment h')
      · intro h hh
        exact integrable_finsetSum _ fun h' _ =>
          integrable_bourgainAdditiveCharacter_sub_halfBox X z
            (bourgainSixfoldMoment h - bourgainSixfoldMoment h')
    rw [show
        (fun z : BourgainPhaseSpace =>
          ∫ w : BourgainPhaseSpace,
            ∑ h : Fin 6 → Fin H, ∑ h' : Fin 6 → Fin H,
              bourgainAdditiveCharacter (z - w)
                (bourgainSixfoldMoment h - bourgainSixfoldMoment h')
              ∂bourgainHalfBoxMeasure X) =
          fun z =>
            ∑ h : Fin 6 → Fin H, ∑ h' : Fin 6 → Fin H,
              ∫ w : BourgainPhaseSpace,
                bourgainAdditiveCharacter (z - w)
                  (bourgainSixfoldMoment h - bourgainSixfoldMoment h')
                ∂bourgainHalfBoxMeasure X by
      funext z
      exact hinner z]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro h hh
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro h' hh'
        unfold bourgainProductFejerKernel
        change
          ((∏ j : Fin 4,
            bourgainFejerKernel (X j)
              ((bourgainSixfoldMoment h - bourgainSixfoldMoment h') j) :
                ℝ) : ℂ) = _
        rw [← integral_integral_bourgainAdditiveCharacter_sub_halfBox
          hX (bourgainSixfoldMoment h - bourgainSixfoldMoment h')]
      · intro h' hh'
        exact
          integrable_integral_bourgainAdditiveCharacter_sub_halfBox X
            (bourgainSixfoldMoment h - bourgainSixfoldMoment h')
    · intro h hh
      exact integrable_finsetSum _ fun h' _ =>
        integrable_integral_bourgainAdditiveCharacter_sub_halfBox X
          (bourgainSixfoldMoment h - bourgainSixfoldMoment h')
  have hcast :
      ((∫ z : BourgainPhaseSpace,
        ∫ w : BourgainPhaseSpace,
          ‖bourgainSixfoldCharacterCloud H (z - w)‖ ^ (2 : ℕ)
            ∂bourgainHalfBoxMeasure X
          ∂bourgainHalfBoxMeasure X : ℝ) : ℂ) =
        ∫ z : BourgainPhaseSpace,
          ∫ w : BourgainPhaseSpace,
            (‖bourgainSixfoldCharacterCloud H (z - w)‖ ^
              (2 : ℕ) : ℂ)
              ∂bourgainHalfBoxMeasure X
              ∂bourgainHalfBoxMeasure X := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards with z
    rw [← integral_complex_ofReal]
    push_cast
    rfl
  exact_mod_cast hcomplex.trans hcast.symm

theorem integrable_bourgainSixfoldCharacterCloud_sub_norm_sq_prod
    (H : ℕ) (X : BourgainPhaseSpace) :
    Integrable
      (fun p : BourgainPhaseSpace × BourgainPhaseSpace =>
        ‖bourgainSixfoldCharacterCloud H (p.1 - p.2)‖ ^ (2 : ℕ))
      ((bourgainHalfBoxMeasure X).prod (bourgainHalfBoxMeasure X)) := by
  let C : ℝ :=
    (Fintype.card (Fin 6 → Fin H) : ℝ) ^ (2 : ℕ)
  refine Integrable.of_bound ?_ C ?_
  · apply Continuous.aestronglyMeasurable
    unfold bourgainSixfoldCharacterCloud bourgainAdditiveCharacter
      bourgainDot
    fun_prop
  · filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hsum :
        ‖bourgainSixfoldCharacterCloud H (p.1 - p.2)‖ ≤
          Fintype.card (Fin 6 → Fin H) := by
      calc
        ‖bourgainSixfoldCharacterCloud H (p.1 - p.2)‖ ≤
            ∑ h : Fin 6 → Fin H,
              ‖bourgainAdditiveCharacter (p.1 - p.2)
                (bourgainSixfoldMoment h)‖ := by
          unfold bourgainSixfoldCharacterCloud
          exact norm_sum_le _ _
        _ = Fintype.card (Fin 6 → Fin H) := by simp
    exact pow_le_pow_left₀ (norm_nonneg _) hsum 2

theorem ofReal_bourgainFejerSpacingEnergy_eq_lintegral
    {H : ℕ} {X : BourgainPhaseSpace}
    (hX : ∀ j, 0 ≤ X j) :
    ENNReal.ofReal (bourgainFejerSpacingEnergy H X) =
      ∫⁻ z : BourgainPhaseSpace,
        ∫⁻ w : BourgainPhaseSpace,
          ENNReal.ofReal
            (‖bourgainSixfoldCharacterCloud H (z - w)‖ ^ (2 : ℕ))
            ∂bourgainHalfBoxMeasure X
          ∂bourgainHalfBoxMeasure X := by
  rw [bourgainFejerSpacingEnergy_eq_doubleMoment hX]
  let f : BourgainPhaseSpace × BourgainPhaseSpace → ℝ :=
    fun p => ‖bourgainSixfoldCharacterCloud H (p.1 - p.2)‖ ^ (2 : ℕ)
  have hf :
      Integrable f
        ((bourgainHalfBoxMeasure X).prod (bourgainHalfBoxMeasure X)) :=
    integrable_bourgainSixfoldCharacterCloud_sub_norm_sq_prod H X
  have houter :
      Integrable
        (fun z : BourgainPhaseSpace =>
          ∫ w : BourgainPhaseSpace, f (z, w)
            ∂bourgainHalfBoxMeasure X)
        (bourgainHalfBoxMeasure X) :=
    hf.integral_prod_left
  have houter0 :
      0 ≤ᵐ[bourgainHalfBoxMeasure X]
        fun z : BourgainPhaseSpace =>
          ∫ w : BourgainPhaseSpace, f (z, w)
            ∂bourgainHalfBoxMeasure X := by
    filter_upwards with z
    apply integral_nonneg
    intro w
    exact sq_nonneg _
  rw [ofReal_integral_eq_lintegral_ofReal houter houter0]
  apply lintegral_congr_ae
  filter_upwards [hf.prod_right_ae] with z hz
  have hz0 :
      0 ≤ᵐ[bourgainHalfBoxMeasure X] fun w =>
        f (z, w) := by
    filter_upwards with w
    exact sq_nonneg _
  rw [ofReal_integral_eq_lintegral_ofReal hz hz0]

def bourgainHalfBox
    (X : BourgainPhaseSpace) : Set BourgainPhaseSpace :=
  Set.univ.pi fun j : Fin 4 => Set.Ioc (-X j / 2) (X j / 2)

def bourgainFullBox
    (X : BourgainPhaseSpace) : Set BourgainPhaseSpace :=
  Set.univ.pi fun j : Fin 4 => Set.Ioc (-X j) (X j)

theorem measurableSet_bourgainHalfBox
    (X : BourgainPhaseSpace) :
    MeasurableSet (bourgainHalfBox X) := by
  unfold bourgainHalfBox
  exact MeasurableSet.univ_pi fun j => measurableSet_Ioc

theorem measurableSet_bourgainFullBox
    (X : BourgainPhaseSpace) :
    MeasurableSet (bourgainFullBox X) := by
  unfold bourgainFullBox
  exact MeasurableSet.univ_pi fun j => measurableSet_Ioc

theorem bourgainHalfBoxMeasure_eq
    (X : BourgainPhaseSpace) :
    bourgainHalfBoxMeasure X = volume.restrict (bourgainHalfBox X) := by
  unfold bourgainHalfBoxMeasure bourgainHalfBox
  rw [volume_pi, Measure.restrict_pi_pi]

theorem volume_bourgainHalfBox
    (X : BourgainPhaseSpace) :
    volume (bourgainHalfBox X) =
      ∏ j : Fin 4, ENNReal.ofReal (X j) := by
  unfold bourgainHalfBox
  rw [Real.volume_pi_Ioc]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  ring

theorem bourgain_sub_image_halfBox_subset_fullBox
    {X w : BourgainPhaseSpace}
    (hw : w ∈ bourgainHalfBox X) :
    (fun z : BourgainPhaseSpace => z - w) '' bourgainHalfBox X ⊆
      bourgainFullBox X := by
  rintro u ⟨z, hz, rfl⟩
  have hz' :
      ∀ j : Fin 4, z j ∈ Set.Ioc (-X j / 2) (X j / 2) := by
    simpa [bourgainHalfBox] using hz
  have hw' :
      ∀ j : Fin 4, w j ∈ Set.Ioc (-X j / 2) (X j / 2) := by
    simpa [bourgainHalfBox] using hw
  have htarget :
      ∀ j : Fin 4, (z - w) j ∈ Set.Ioc (-X j) (X j) := by
    intro j
    simp only [Pi.sub_apply, Set.mem_Ioc]
    constructor <;> linarith [(hz' j).1, (hz' j).2,
      (hw' j).1, (hw' j).2]
  simpa [bourgainFullBox] using htarget

theorem setLIntegral_comp_sub_eq_image
    (A : Set BourgainPhaseSpace) (w : BourgainPhaseSpace)
    (g : BourgainPhaseSpace → ENNReal) :
    (∫⁻ z in A, g (z - w)) =
      ∫⁻ u in (fun z : BourgainPhaseSpace => z - w) '' A, g u := by
  simpa only [sub_eq_add_neg] using
    (measurePreserving_add_right volume (-w)).setLIntegral_comp_emb
      (Homeomorph.addRight (-w)).isClosedEmbedding.measurableEmbedding
      g A

theorem bourgainSixfoldCharacterCloud_neg
    (H : ℕ) (u : BourgainPhaseSpace) :
    bourgainSixfoldCharacterCloud H (-u) =
      conj (bourgainSixfoldCharacterCloud H u) := by
  unfold bourgainSixfoldCharacterCloud
  rw [map_sum]
  apply Fintype.sum_congr
  intro h
  have hsub :
      -u = (0 : BourgainPhaseSpace) - u := by simp
  rw [hsub, bourgainAdditiveCharacter_sub_left]
  simp [bourgainAdditiveCharacter, bourgainDot]

theorem norm_bourgainSixfoldCharacterCloud_sub_comm
    (H : ℕ) (z w : BourgainPhaseSpace) :
    ‖bourgainSixfoldCharacterCloud H (z - w)‖ =
      ‖bourgainSixfoldCharacterCloud H (w - z)‖ := by
  have hneg : z - w = -(w - z) := by abel
  rw [hneg, bourgainSixfoldCharacterCloud_neg, Complex.norm_conj]

def bourgainFejerFullBoxMoment
    (H : ℕ) (X : BourgainPhaseSpace) : ENNReal :=
  ∫⁻ u in bourgainFullBox X,
    ENNReal.ofReal
      (‖bourgainSixfoldCharacterCloud H u‖ ^ (2 : ℕ))

theorem lintegral_bourgainFejer_doubleMoment_le_fullBox
    {H : ℕ} {X : BourgainPhaseSpace} :
    (∫⁻ z : BourgainPhaseSpace,
      ∫⁻ w : BourgainPhaseSpace,
        ENNReal.ofReal
          (‖bourgainSixfoldCharacterCloud H (z - w)‖ ^ (2 : ℕ))
          ∂bourgainHalfBoxMeasure X
        ∂bourgainHalfBoxMeasure X) ≤
      (∏ j : Fin 4, ENNReal.ofReal (X j)) *
        bourgainFejerFullBoxMoment H X := by
  let g : BourgainPhaseSpace → ENNReal := fun u =>
    ENNReal.ofReal
      (‖bourgainSixfoldCharacterCloud H u‖ ^ (2 : ℕ))
  let B : ENNReal := bourgainFejerFullBoxMoment H X
  have hinner (w : BourgainPhaseSpace) (hw : w ∈ bourgainHalfBox X) :
      (∫⁻ z : BourgainPhaseSpace, g (z - w)
          ∂bourgainHalfBoxMeasure X) ≤ B := by
    rw [bourgainHalfBoxMeasure_eq]
    change (∫⁻ z in bourgainHalfBox X, g (z - w)) ≤ B
    rw [setLIntegral_comp_sub_eq_image]
    exact lintegral_mono_set
      (bourgain_sub_image_halfBox_subset_fullBox hw)
  rw [bourgainHalfBoxMeasure_eq]
  change
    (∫⁻ z in bourgainHalfBox X,
      ∫⁻ w in bourgainHalfBox X, g (z - w)) ≤ _
  calc
    (∫⁻ z in bourgainHalfBox X,
        ∫⁻ w in bourgainHalfBox X, g (z - w)) ≤
        ∫⁻ z in bourgainHalfBox X, B := by
      apply lintegral_mono_ae
      filter_upwards
        [ae_restrict_mem (measurableSet_bourgainHalfBox X)] with z hz
      have heq :
          (fun w : BourgainPhaseSpace => g (z - w)) =
            fun w => g (w - z) := by
        funext w
        unfold g
        rw [norm_bourgainSixfoldCharacterCloud_sub_comm]
      change (∫⁻ w in bourgainHalfBox X, g (z - w)) ≤ B
      rw [heq]
      rw [← bourgainHalfBoxMeasure_eq]
      exact hinner z hz
    _ = volume (bourgainHalfBox X) * B := by
      rw [setLIntegral_const, mul_comm]
    _ = _ := by
      rw [volume_bourgainHalfBox X]

theorem ofReal_bourgainFejerSpacingEnergy_le_fullBox
    {H : ℕ} {X : BourgainPhaseSpace}
    (hX : ∀ j, 0 ≤ X j) :
    ENNReal.ofReal (bourgainFejerSpacingEnergy H X) ≤
      (∏ j : Fin 4, ENNReal.ofReal (X j)) *
        bourgainFejerFullBoxMoment H X := by
  rw [ofReal_bourgainFejerSpacingEnergy_eq_lintegral hX]
  exact lintegral_bourgainFejer_doubleMoment_le_fullBox

end

end RHTower
