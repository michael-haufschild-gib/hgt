import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.CubeCorrespondences
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheRationalCuspSubtractionScatters

/-!
# The seed defect reads the constant term

The Eisenstein series of the cubic cover is continued as `E(s) = seed(s) − R(s(2 − s)) defect(s)`, the
defect `defect(s) = (Δ − s(2 − s)) seed(s)` supported at heights `[5, 6]` in the cusp. Pairing the defect
with an automorphic function only sees its constant term:

* `kernelSeedDefectTrace_strip`: on the strip the trace of `star(defect(s₀)) · F` over the sheets of the
  kernel cover is `K star(d_{s₀}(v)) F(w)`, `K` the number of sheets, when `F` has multiplier `κ`;
* `integral_star_defect_mul`: `⟨defect(s₀), F⟩ = K ∫_5^6 star(d_{s₀}(v)) (∫_P F(z + jv) dz) v^{−3} dv`;
* `inner_defect_eisensteinRemainder`: for `F = E(s) − seed(s)` (`Re s > 2`) the constant term is
  `|P| ((v^s − χ(v)v^s) + v^{2−s}(π/(s − 1))φ(s))` on `[5, 6]`.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein SpectralTheoryOfTheCubicCover

local instance kernelLevelFiniteCover' : globalKubotaKernel.IsFiniteRelIndex levelThree := by
  letI := globalKubotaKernel_finiteIndex
  exact Subgroup.isFiniteRelIndex_of_finiteIndex

/-! ### Functions with multiplier `κ` on the kernel quotient -/

/-- A function with multiplier `κ` on `levelThree` is invariant under the kernel of `κ`. -/
def kernelLift (F : HyperbolicSpace → ℂ)
    (hauto : ∀ (M : levelThree) (w : HyperbolicSpace), F (complexMatrix M • w) = complexCharacter M * F w) :
    KernelQuotient → ℂ :=
  Quotient.lift F (by
    rintro w u ⟨M, hM⟩
    rw [← hM]
    obtain ⟨hMl, hchar⟩ := (globalKubotaKernel_mem (M : SL(2, O))).mp M.property
    have h := hauto ⟨M, hMl⟩ w
    rw [hchar, one_mul] at h
    exact h.symm)

theorem kernelLift_mk (F : HyperbolicSpace → ℂ)
    (hauto : ∀ (M : levelThree) (w : HyperbolicSpace), F (complexMatrix M • w) = complexCharacter M * F w)
    (w : HyperbolicSpace) : kernelLift F hauto (integralOrbitProjection globalKubotaKernel w) = F w := rfl

theorem kernelLift_continuous (F : HyperbolicSpace → ℂ) (hF : Continuous F)
    (hauto : ∀ (M : levelThree) (w : HyperbolicSpace), F (complexMatrix M • w) = complexCharacter M * F w) :
    Continuous (kernelLift F hauto) :=
  hF.quotient_lift _

/-! ### The defect at a general parameter -/

/-- The defect of the seed at `s₀` lives over the strip `[5, 6]`. -/
theorem smoothCuspSeedDefect_support_strip (s₀ : ℂ) (w : HyperbolicSpace)
    (hw : smoothCuspSeedDefect 5 6 s₀ w ≠ 0) :
    integralOrbitProjection levelThree w ∈ integralOrbitProjection levelThree '' cuspPeriodStrip 5 6 := by
  obtain ⟨r, hr⟩ := smoothCuspSeedDefect_support 5 6 s₀ (by norm_num) w hw
  induction r using Quotient.inductionOn with
  | _ M =>
    change (5 : ℝ) ≤ cosetHeight (cosetOf M) w ∧ cosetHeight (cosetOf M) w ≤ 6 at hr
    rw [cosetHeight_cosetOf] at hr
    have hm := levelProjection_mem_cuspStrip_of_height (complexMatrix M • w) hr
    simpa only [← integralComplexMatrix_levelThree, integralOrbitProjection_eq] using hm

/-- The pairing density `star(defect(s₀)) · F` on the kernel quotient. -/
def defectDensity (s₀ : ℂ) (f : KernelQuotient → ℂ) : KernelQuotient → ℂ :=
  fun q => star (kernelQuotientDefect 5 6 s₀ q) * f q

/-- Its trace to the level-three quotient. -/
def defectTrace (s₀ : ℂ) (f : KernelQuotient → ℂ) : IntegralOrbitQuotient levelThree → ℂ :=
  integralCoverTraceFunction globalKubotaKernel levelThree (defectDensity s₀ f)

theorem defectDensity_continuous (s₀ : ℂ) (f : KernelQuotient → ℂ) (hf : Continuous f) :
    Continuous (defectDensity s₀ f) :=
  (kernelQuotientDefect_contMDiff 5 6 s₀ (by norm_num) (by norm_num)).continuous.star.mul hf

theorem defectTrace_continuous (s₀ : ℂ) (f : KernelQuotient → ℂ) (hf : Continuous f) :
    Continuous (defectTrace s₀ f) :=
  integralCoverTraceFunction_continuous _ _ _ (defectDensity_continuous s₀ f hf)

theorem defectTrace_integral (s₀ : ℂ) (f : KernelQuotient → ℂ) (hf : Continuous f) :
    (∫ q, defectTrace s₀ f q ∂integralQuotientVolume levelThree) =
      ∫ q, defectDensity s₀ f q ∂integralQuotientVolume globalKubotaKernel := by
  apply integralCoverTraceFunction_integral globalKubotaKernel_le_levelThree le_rfl
  · exact (defectDensity_continuous s₀ f hf).measurable
  · apply (defectDensity_continuous s₀ f hf).integrable_of_hasCompactSupport
    exact ((kernelQuotientDefect_hasCompactSupport 5 6 (by norm_num) (by norm_num) s₀).comp_left
      (g := fun z : ℂ => star z) (star_zero _)).mul_right

theorem defectTrace_support (s₀ : ℂ) (f : KernelQuotient → ℂ) (q : IntegralOrbitQuotient levelThree)
    (hq : defectTrace s₀ f q ≠ 0) :
    q ∈ integralOrbitProjection levelThree '' cuspPeriodStrip 5 6 := by
  letI : Fintype (IntegralCoverCosets globalKubotaKernel levelThree) := Fintype.ofFinite _
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection levelThree w ∈ integralOrbitProjection levelThree '' cuspPeriodStrip 5 6
    change (∑ r : IntegralCoverCosets globalKubotaKernel levelThree,
      star (kernelQuotientDefect 5 6 s₀ (integralCoverFiberPoint globalKubotaKernel levelThree r w)) *
        f (integralCoverFiberPoint globalKubotaKernel levelThree r w)) ≠ 0 at hq
    obtain ⟨r, _, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
    have hd := (mul_ne_zero_iff.mp hr).1
    rw [star_ne_zero, integralCoverFiberPoint_rep, integralSubgroup_smul,
      integralComplexMatrix_levelThree] at hd
    have hs := smoothCuspSeedDefect_support_strip s₀
      (complexMatrix ((integralCoverRep globalKubotaKernel levelThree r)⁻¹) • w) hd
    simpa only [← integralComplexMatrix_levelThree, integralOrbitProjection_eq] using hs

/-- **The trace on the strip.** For `F` with multiplier `κ` and `v > 1`:
`trace(star(defect) F)(z + jv) = K star(d_{s₀}(v)) F(z + jv)`. -/
theorem defectTrace_upper (s₀ : ℂ) (F : HyperbolicSpace → ℂ)
    (hauto : ∀ (M : levelThree) (w : HyperbolicSpace), F (complexMatrix M • w) = complexCharacter M * F w)
    (z : ℂ) (v : ℝ) (hv : 0 < v) (hv1 : 1 < v) :
    defectTrace s₀ (kernelLift F hauto) (integralOrbitProjection levelThree (upperPoint z v hv)) =
      (Nat.card (IntegralCoverCosets globalKubotaKernel levelThree) : ℂ) *
        (star (cuspSeedDefectProfile 5 6 s₀ v) * F (upperPoint z v hv)) := by
  letI : Fintype (IntegralCoverCosets globalKubotaKernel levelThree) := Fintype.ofFinite _
  change (∑ r : IntegralCoverCosets globalKubotaKernel levelThree,
    star (kernelQuotientDefect 5 6 s₀ (integralCoverFiberPoint globalKubotaKernel levelThree r
      (upperPoint z v hv))) *
      kernelLift F hauto (integralCoverFiberPoint globalKubotaKernel levelThree r (upperPoint z v hv))) = _
  have hterm : ∀ r : IntegralCoverCosets globalKubotaKernel levelThree,
      star (kernelQuotientDefect 5 6 s₀ (integralCoverFiberPoint globalKubotaKernel levelThree r
        (upperPoint z v hv))) *
        kernelLift F hauto (integralCoverFiberPoint globalKubotaKernel levelThree r (upperPoint z v hv)) =
      star (cuspSeedDefectProfile 5 6 s₀ v) * F (upperPoint z v hv) := by
    intro r
    set M := (integralCoverRep globalKubotaKernel levelThree r)⁻¹
    rw [integralCoverFiberPoint_rep, integralSubgroup_smul, integralComplexMatrix_levelThree]
    change star (smoothCuspSeedDefect 5 6 s₀ (complexMatrix M • upperPoint z v hv)) *
      F (complexMatrix M • upperPoint z v hv) = _
    rw [smoothCuspSeedDefect_automorphy, hauto, smoothCuspSeedDefect,
      cuspCutoffCorrection_upperPoint _ z v hv hv1, star_mul']
    have hk : star (complexCharacter M) * complexCharacter M = 1 := by
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_complexCharacter]
      norm_num
    linear_combination (star (cuspSeedDefectProfile 5 6 s₀ v) * F (upperPoint z v hv)) * hk
  rw [Finset.sum_congr rfl fun r _ => hterm r, Finset.sum_const, Finset.card_univ,
    Nat.card_eq_fintype_card, nsmul_eq_mul]

/-- **The defect pairing reads the constant term.** For `F` continuous with multiplier `κ`:
`∫ star(defect(s₀)) F = K ∫_5^6 star(d_{s₀}(v)) (∫_P F(z + jv) dz) v^{−3} dv`. -/
theorem integral_star_defect_mul (s₀ : ℂ) (F : HyperbolicSpace → ℂ) (hF : Continuous F)
    (hauto : ∀ (M : levelThree) (w : HyperbolicSpace), F (complexMatrix M • w) = complexCharacter M * F w) :
    (∫ q, star (kernelQuotientDefect 5 6 s₀ q) * kernelLift F hauto q
        ∂integralQuotientVolume globalKubotaKernel) =
      (Nat.card (IntegralCoverCosets globalKubotaKernel levelThree) : ℂ) *
        ∫ v in Set.Icc (5 : ℝ) 6, star (cuspSeedDefectProfile 5 6 s₀ v) *
          (∫ z in periodDomain, F (cuspCoordinateLift (v, z))) / (v : ℂ) ^ 3 := by
  have hf := kernelLift_continuous F hF hauto
  set S := integralOrbitProjection levelThree '' cuspPeriodStrip 5 6
  have hS : MeasurableSet S := (cuspPeriodStrip_measurable 5 6).image_of_continuousOn_injOn
    (continuous_integralOrbitProjection levelThree).continuousOn
    (integralProjection_cuspPeriodStrip_injective levelThree le_rfl 5 6 (by norm_num))
  have he : S.indicator (defectTrace s₀ (kernelLift F hauto)) = defectTrace s₀ (kernelLift F hauto) := by
    funext q
    by_cases hq : q ∈ S
    · exact Set.indicator_of_mem hq _
    · rw [Set.indicator_of_notMem hq]
      exact (not_not.mp (fun hn => hq (defectTrace_support s₀ _ q hn))).symm
  set G : HyperbolicSpace → ℂ := fun w => defectTrace s₀ (kernelLift F hauto) (integralOrbitProjection levelThree w)
  have hG : Continuous G :=
    (defectTrace_continuous s₀ _ hf).comp (continuous_integralOrbitProjection _)
  calc (∫ q, star (kernelQuotientDefect 5 6 s₀ q) * kernelLift F hauto q
        ∂integralQuotientVolume globalKubotaKernel)
      = ∫ q, defectTrace s₀ (kernelLift F hauto) q ∂integralQuotientVolume levelThree :=
        (defectTrace_integral s₀ _ hf).symm
    _ = ∫ q in S, defectTrace s₀ (kernelLift F hauto) q ∂integralQuotientVolume levelThree := by
        rw [← integral_indicator hS, he]
    _ = ∫ w in cuspPeriodStrip 5 6, G w ∂hyperbolicVolume := by
        rw [← (integralProjection_cuspPeriodStrip_measurePreserving levelThree le_rfl 5 6
          (by norm_num)).map_eq]
        exact integral_map (measurable_integralOrbitProjection _).aemeasurable
          (defectTrace_continuous s₀ _ hf).aestronglyMeasurable
    _ = ∫ v in Set.Icc (5 : ℝ) 6, (∫ z in periodDomain, G (cuspCoordinateLift (v, z))) / (v : ℂ) ^ 3 :=
        cuspPeriodStrip_integral_coordinates G hG.aestronglyMeasurable
          (cuspCoordinateLift_weighted_integrable G hG)
    _ = _ := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Icc fun v hv => ?_
        have hp : 0 < v := lt_of_lt_of_le (by norm_num) hv.1
        have h1 : 1 < v := lt_of_lt_of_le (by norm_num) hv.1
        have hG' : ∀ z, G (cuspCoordinateLift (v, z)) =
            (Nat.card (IntegralCoverCosets globalKubotaKernel levelThree) : ℂ) *
              (star (cuspSeedDefectProfile 5 6 s₀ v) * F (cuspCoordinateLift (v, z))) := by
          intro z
          simp only [G, cuspCoordinateLift_positive v z hp]
          exact defectTrace_upper s₀ F hauto z v hp h1
        simp_rw [hG']
        rw [integral_const_mul, integral_const_mul]
        ring

/-! ### The Eisenstein remainder -/

/-- `E(s) − seed(s)` with the seed cut off on `[5, 6]`. -/
def eisensteinRemainder (s : ℂ) (w : HyperbolicSpace) : ℂ :=
  hyperbolicEisenstein s w - smoothCuspSeed 5 6 s w

theorem eisensteinRemainder_automorphy (s : ℂ) (hs : 2 < s.re) (M : levelThree) (w : HyperbolicSpace) :
    eisensteinRemainder s (complexMatrix M • w) = complexCharacter M * eisensteinRemainder s w := by
  rw [eisensteinRemainder, eisensteinRemainder, hyperbolicEisenstein_automorphy M s hs,
    smoothCuspSeed_automorphy, mul_sub]

theorem eisensteinRemainder_continuous (s : ℂ) (hs : 2 < s.re) : Continuous (eisensteinRemainder s) :=
  (kernelEisensteinRemainder_smooth 5 6 (by norm_num) (by norm_num) s hs).continuous.comp
    (continuous_integralOrbitProjection _)

/-- **The constant term of the remainder** on heights `v > 1`:
`∫_P (E(s) − seed(s))(z + jv) dz = |P|((v^s − χ(v)v^s) + v^{2−s}(π/(s − 1))φ(s))`. -/
theorem cuspConstant_eisensteinRemainder (s : ℂ) (hs : 2 < s.re) (v : ℝ) (hv : 0 < v) (hv1 : 1 < v) :
    ∫ z in periodDomain, eisensteinRemainder s (cuspCoordinateLift (v, z)) =
      periodArea * (((v : ℂ) ^ s - cuspSeedProfile 5 6 s v) +
        (v : ℂ) ^ (2 - s) * ((Real.pi : ℂ) / (s - 1) * scatteringCoefficient s 0)) := by
  letI := periodDomain_finiteMeasure
  have hseed : ∀ z, smoothCuspSeed 5 6 s (cuspCoordinateLift (v, z)) = cuspSeedProfile 5 6 s v := by
    intro z
    rw [cuspCoordinateLift_positive v z hv, smoothCuspSeed, cuspCutoffCorrection_upperPoint _ z v hv hv1]
  have hlift : (fun z : ℂ => cuspCoordinateLift (v, z)) = fun z => upperPoint z v hv :=
    funext fun z => cuspCoordinateLift_positive v z hv
  have hcont : Continuous (fun z : ℂ => eisensteinRemainder s (cuspCoordinateLift (v, z))) := by
    rw [show (fun z : ℂ => eisensteinRemainder s (cuspCoordinateLift (v, z))) =
        eisensteinRemainder s ∘ (fun z : ℂ => cuspCoordinateLift (v, z)) from rfl, hlift]
    exact (eisensteinRemainder_continuous s hs).comp (upperCoordinatesHomeomorph.continuous.comp
      (show Continuous (fun z : ℂ => (⟨(z, v), hv⟩ : UpperCoordinates)) by fun_prop))
  have hint : Integrable (fun z : ℂ => eisensteinRemainder s (cuspCoordinateLift (v, z)))
      (volume.restrict periodDomain) := (periodDomain_continuous_memLp _ hcont).integrable (by norm_num)
  have hE := cuspConstant_eisenstein s hs v hv
  have hsplit : (fun z => hyperbolicEisenstein s (cuspCoordinateLift (v, z))) =
      fun z => eisensteinRemainder s (cuspCoordinateLift (v, z)) + cuspSeedProfile 5 6 s v := by
    funext z
    rw [eisensteinRemainder, hseed]
    ring
  rw [hsplit, integral_add hint (integrable_const _), integral_const, Measure.real,
    Measure.restrict_apply_univ, periodDomain_volume, ENNReal.toReal_ofReal periodAreaReal_pos.le,
    Complex.real_smul] at hE
  have hP : ((periodAreaReal : ℝ) : ℂ) = periodArea := rfl
  rw [hP] at hE
  linear_combination hE

/-- **The defect pairing of the Eisenstein remainder.** For `Re s > 2`,
`∫ star(defect(s₀)) (E(s) − seed(s)) = K |P| ∫_5^6 star(d_{s₀}(v)) ((v^s − χ(v)v^s) + v^{2−s}(π/(s−1))φ(s)) v^{−3} dv`. -/
theorem integral_star_defect_eisensteinRemainder (s₀ s : ℂ) (hs : 2 < s.re) :
    (∫ q, star (kernelQuotientDefect 5 6 s₀ q) *
        kernelLift (eisensteinRemainder s) (eisensteinRemainder_automorphy s hs) q
        ∂integralQuotientVolume globalKubotaKernel) =
      (Nat.card (IntegralCoverCosets globalKubotaKernel levelThree) : ℂ) * periodArea *
        ∫ v in Set.Icc (5 : ℝ) 6, star (cuspSeedDefectProfile 5 6 s₀ v) *
          (((v : ℂ) ^ s - cuspSeedProfile 5 6 s v) +
            (v : ℂ) ^ (2 - s) * ((Real.pi : ℂ) / (s - 1) * scatteringCoefficient s 0)) / (v : ℂ) ^ 3 := by
  rw [integral_star_defect_mul s₀ _ (eisensteinRemainder_continuous s hs), mul_assoc]
  congr 1
  rw [← integral_const_mul periodArea]
  refine setIntegral_congr_fun (measurableSet_Icc : MeasurableSet (Set.Icc (5 : ℝ) 6)) fun v hv => ?_
  have hp : 0 < v := lt_of_lt_of_le (by norm_num) hv.1
  have h1 : 1 < v := lt_of_lt_of_le (by norm_num) hv.1
  rw [cuspConstant_eisensteinRemainder s hs v hp h1]
  ring

end GaloisForLFunctions.OrderSixMetaplecticTheory
