import GaloisForLFunctions.RHTower.RealCoronaUniversalTransgression
import GaloisForLFunctions.RHTower.SignedReflectionParity

noncomputable section

open Complex Filter Set Metric

namespace GaloisForLFunctions.RHTower

structure CompletedSelfDualAnalyticFamily (T : Type*) where
  completed : T → ℂ → ℂ
  center : ℝ
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  analytic : ∀ t, AnalyticOnNhd ℂ (completed t) Set.univ
  nontrivial : ∀ t, ∃ z, completed t z ≠ 0
  rootNumber : T → ℂ
  rootNumber_ne_zero : ∀ t, rootNumber t ≠ 0
  functionalEquation : ∀ t z,
    completed t (2 * (center : ℂ) - z) = rootNumber t * completed t z

def CompletedSelfDualAnalyticFamily.reflect
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) : ℂ → ℂ :=
  (fun _ : ℂ => 2 * (F.center : ℂ)) - id

theorem CompletedSelfDualAnalyticFamily.analyticOrderAt_reflect
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) (t : T) (z : ℂ) :
    analyticOrderAt (F.completed t) (F.reflect z) =
      analyticOrderAt (F.completed t) z := by
  have hreflectAnalytic : AnalyticAt ℂ F.reflect z := by
    change AnalyticAt ℂ (fun w : ℂ => 2 * (F.center : ℂ) - w) z
    fun_prop
  have hreflectDeriv : deriv F.reflect z ≠ 0 := by
    have hderiv : HasDerivAt F.reflect (-1) z := by
      change HasDerivAt ((fun _ : ℂ => 2 * (F.center : ℂ)) - id) (-1) z
      simpa only [zero_sub] using
        (hasDerivAt_const (x := z) (c := 2 * (F.center : ℂ))).sub (hasDerivAt_id z)
    rw [hderiv.deriv]
    norm_num
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := F.completed t) hreflectAnalytic hreflectDeriv
  have hfun : F.completed t ∘ F.reflect =
      (fun _ : ℂ => F.rootNumber t) * F.completed t := by
    funext w
    exact F.functionalEquation t w
  have hrootOrder :
      analyticOrderAt (fun _ : ℂ => F.rootNumber t) z = 0 :=
    analyticAt_const.analyticOrderAt_eq_zero.mpr (F.rootNumber_ne_zero t)
  rw [hfun, analyticOrderAt_mul analyticAt_const
    (F.analytic t z (Set.mem_univ z)), hrootOrder, zero_add] at hcomp
  exact hcomp.symm

theorem CompletedSelfDualAnalyticFamily.rootNumber_mul_self
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) (t : T) :
    F.rootNumber t * F.rootNumber t = 1 := by
  obtain ⟨z, hz⟩ := F.nontrivial t
  have hfirst := F.functionalEquation t z
  have hsecond := F.functionalEquation t (2 * (F.center : ℂ) - z)
  rw [show 2 * (F.center : ℂ) - (2 * (F.center : ℂ) - z) = z by ring,
    hfirst] at hsecond
  apply mul_right_cancel₀ hz
  calc
    (F.rootNumber t * F.rootNumber t) * F.completed t z =
        F.rootNumber t * (F.rootNumber t * F.completed t z) := by ring
    _ = F.completed t z := hsecond.symm
    _ = 1 * F.completed t z := by rw [one_mul]

theorem CompletedSelfDualAnalyticFamily.rootNumber_eq_one_or_neg_one
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) (t : T) :
    F.rootNumber t = 1 ∨ F.rootNumber t = -1 := by
  exact mul_self_eq_one_iff.mp (F.rootNumber_mul_self t)

theorem CompletedSelfDualAnalyticFamily.centralOrder_ne_top
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) (t : T) :
    analyticOrderAt (F.completed t) (F.center : ℂ) ≠ ⊤ := by
  obtain ⟨w, hw⟩ := F.nontrivial t
  have hworder : analyticOrderAt (F.completed t) w ≠ ⊤ := by
    rw [(F.analytic t w (Set.mem_univ w)).analyticOrderAt_eq_zero.mpr hw]
    exact ENat.zero_ne_top
  exact (F.analytic t).analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ w) (Set.mem_univ (F.center : ℂ)) hworder

theorem CompletedSelfDualAnalyticFamily.centralParity_sign
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) (t : T) :
    (-1 : ℂ) ^ (analyticOrderAt (F.completed t) (F.center : ℂ)).toNat =
      F.rootNumber t := by
  exact _root_.RHTower.neg_one_pow_orderAt_of_signed_reflection
    (F.analytic t) (F.rootNumber_eq_one_or_neg_one t)
      (F.functionalEquation t) (F.centralOrder_ne_top t)

def CompletedSelfDualAnalyticFamily.realWindowZeroSet
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) (t : T) : Set ℝ :=
  {x | x ∈ Metric.closedBall F.center F.radius ∧ F.completed t (x : ℂ) = 0}

theorem CompletedSelfDualAnalyticFamily.complexWindowZeroSet_finite
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) (t : T) :
    {z | z ∈ Metric.closedBall (F.center : ℂ) F.radius ∧ F.completed t z = 0}.Finite := by
  obtain ⟨w, hw⟩ := F.nontrivial t
  have hcod : ((F.completed t) ⁻¹' {0}ᶜ) ∈
      codiscreteWithin (Set.univ : Set ℂ) :=
    (F.analytic t).preimage_zero_mem_codiscreteWithin
      hw (Set.mem_univ w) isConnected_univ
  have hcodK : ((F.completed t) ⁻¹' {0}ᶜ) ∈
      codiscreteWithin (Metric.closedBall (F.center : ℂ) F.radius) :=
    Filter.codiscreteWithin_mono (Set.subset_univ _) hcod
  refine ((isCompact_closedBall (F.center : ℂ) F.radius).finite_sdiff_of_mem_codiscreteWithin
    hcodK).subset ?_
  intro z hz
  rw [Set.mem_sep_iff] at hz
  exact ⟨hz.1, by simp [Set.mem_preimage, hz.2]⟩

theorem CompletedSelfDualAnalyticFamily.realWindowZeroSet_finite
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) (t : T) :
    (F.realWindowZeroSet t).Finite := by
  refine Set.Finite.of_finite_image (f := fun x : ℝ => (x : ℂ))
    (F.complexWindowZeroSet_finite t |>.subset ?_) Complex.ofReal_injective.injOn
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  refine ⟨?_, hx.2⟩
  rw [Metric.mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real]
  exact Metric.mem_closedBall.mp hx.1

def CompletedSelfDualAnalyticFamily.realWindowZeroFinset
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) (t : T) : Finset ℝ :=
  (F.realWindowZeroSet_finite t).toFinset

@[simp] theorem CompletedSelfDualAnalyticFamily.mem_realWindowZeroFinset_iff
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) (t : T) (x : ℝ) :
    x ∈ F.realWindowZeroFinset t ↔
      x ∈ Metric.closedBall F.center F.radius ∧ F.completed t (x : ℂ) = 0 := by
  rw [CompletedSelfDualAnalyticFamily.realWindowZeroFinset,
    Set.Finite.mem_toFinset]
  rfl

def CompletedSelfDualAnalyticFamily.realWindowMultiplicity
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) (t : T) : ℝ →₀ ℕ :=
  Finsupp.onFinset (F.realWindowZeroFinset t)
    (fun x => if x ∈ F.realWindowZeroFinset t then
      (analyticOrderAt (F.completed t) (x : ℂ)).toNat else 0)
    (by intro x hx; by_contra hmem; simp [hmem] at hx)

theorem CompletedSelfDualAnalyticFamily.realWindowMultiplicity_apply_of_mem
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) (t : T) (x : ℝ) :
    x ∈ Metric.closedBall F.center F.radius →
      F.realWindowMultiplicity t x =
        (analyticOrderAt (F.completed t) (x : ℂ)).toNat := by
  intro hx
  by_cases hzero : F.completed t (x : ℂ) = 0
  · have hmem : x ∈ F.realWindowZeroFinset t :=
      (F.mem_realWindowZeroFinset_iff t x).mpr ⟨hx, hzero⟩
    rw [CompletedSelfDualAnalyticFamily.realWindowMultiplicity, Finsupp.onFinset_apply]
    simp [hmem]
  · have horder : analyticOrderAt (F.completed t) (x : ℂ) = 0 :=
      (F.analytic t (x : ℂ) (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hzero
    have hnotmem : x ∉ F.realWindowZeroFinset t := by
      intro hmem
      exact hzero (F.mem_realWindowZeroFinset_iff t x |>.mp hmem).2
    rw [CompletedSelfDualAnalyticFamily.realWindowMultiplicity, Finsupp.onFinset_apply]
    simp [hnotmem, horder]

theorem CompletedSelfDualAnalyticFamily.realWindowMultiplicity_apply_of_not_mem
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) (t : T) (x : ℝ) :
    x ∉ Metric.closedBall F.center F.radius → F.realWindowMultiplicity t x = 0 := by
  intro hx
  rw [CompletedSelfDualAnalyticFamily.realWindowMultiplicity, Finsupp.onFinset_apply]
  have hnotfin : x ∉ F.realWindowZeroFinset t := by
    intro hmem
    exact hx (F.mem_realWindowZeroFinset_iff t x |>.mp hmem).1
  simp [hnotfin]

theorem CompletedSelfDualAnalyticFamily.reflect_mem_realWindow_iff
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) (x : ℝ) :
    2 * F.center - x ∈ Metric.closedBall F.center F.radius ↔
      x ∈ Metric.closedBall F.center F.radius := by
  simp only [Metric.mem_closedBall, Real.dist_eq]
  rw [show 2 * F.center - x - F.center = -(x - F.center) by ring, abs_neg]

theorem CompletedSelfDualAnalyticFamily.realWindowMultiplicity_reflect
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) (t : T) (x : ℝ) :
    F.realWindowMultiplicity t (2 * F.center - x) =
      F.realWindowMultiplicity t x := by
  by_cases hx : x ∈ Metric.closedBall F.center F.radius
  · rw [F.realWindowMultiplicity_apply_of_mem t
        (2 * F.center - x) (F.reflect_mem_realWindow_iff x |>.mpr hx),
      F.realWindowMultiplicity_apply_of_mem t x hx]
    exact congrArg ENat.toNat (by
      simpa [CompletedSelfDualAnalyticFamily.reflect] using
        F.analyticOrderAt_reflect t (x : ℂ))
  · rw [F.realWindowMultiplicity_apply_of_not_mem t
        (2 * F.center - x) (fun h => hx (F.reflect_mem_realWindow_iff x |>.mp h)),
      F.realWindowMultiplicity_apply_of_not_mem t x hx]

def CompletedSelfDualAnalyticFamily.toSelfDualRealZeroFamily
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) : SelfDualRealZeroFamily T where
  center := F.center
  realMultiplicity := F.realWindowMultiplicity
  reflection_multiplicity := F.realWindowMultiplicity_reflect

theorem CompletedSelfDualAnalyticFamily.analyticRank_eq_orderAt_center
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) (t : T) :
    F.toSelfDualRealZeroFamily.analyticRank t =
      (analyticOrderAt (F.completed t) (F.center : ℂ)).toNat := by
  rw [SelfDualRealZeroFamily.analyticRank, analyticRankAt,
    CompletedSelfDualAnalyticFamily.toSelfDualRealZeroFamily,
    F.realWindowMultiplicity_apply_of_mem t F.center
      (Metric.mem_closedBall_self F.radius_nonneg)]

theorem CompletedSelfDualAnalyticFamily.analyticRank_parity_sign
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) (t : T) :
    (-1 : ℂ) ^ F.toSelfDualRealZeroFamily.analyticRank t = F.rootNumber t := by
  rw [F.analyticRank_eq_orderAt_center]
  exact F.centralParity_sign t

theorem CompletedSelfDualAnalyticFamily.defectRank_eq_orderAt_center_add_twice_upper
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) (t : T) :
    F.toSelfDualRealZeroFamily.defectRank t =
      (analyticOrderAt (F.completed t) (F.center : ℂ)).toNat +
        2 * F.toSelfDualRealZeroFamily.upperOffCentralMultiplicity t := by
  rw [F.toSelfDualRealZeroFamily.defectRank_eq_analyticRank_add_twice_upper,
    F.analyticRank_eq_orderAt_center]

/-! ### Concrete Riemann ξ specialization -/

def riemannXiCompletedSelfDualAnalyticFamily (radius : ℝ) (hradius : 0 ≤ radius) :
    CompletedSelfDualAnalyticFamily Unit where
  completed := fun _ => _root_.RHTower.xi
  center := 1 / 2
  radius := radius
  radius_nonneg := hradius
  analytic := fun _ => _root_.RHTower.xi_analyticOnNhd_univ
  nontrivial := fun _ => ⟨2, _root_.RHTower.xi_two_ne_zero⟩
  rootNumber := fun _ => 1
  rootNumber_ne_zero := fun _ => one_ne_zero
  functionalEquation := by
    intro _ z
    have h := _root_.RHTower.xi_one_sub z
    convert h using 1 <;> norm_num

theorem riemannXi_fixedSectorDefect_eq_centralOrder_add_twice_upper
    (radius : ℝ) (hradius : 0 ≤ radius) :
    (riemannXiCompletedSelfDualAnalyticFamily radius hradius).toSelfDualRealZeroFamily.defectRank () =
      (analyticOrderAt _root_.RHTower.xi (1 / 2 : ℂ)).toNat +
        2 * SelfDualRealZeroFamily.upperOffCentralMultiplicity
          (riemannXiCompletedSelfDualAnalyticFamily radius hradius).toSelfDualRealZeroFamily () := by
  simpa [riemannXiCompletedSelfDualAnalyticFamily] using
    CompletedSelfDualAnalyticFamily.defectRank_eq_orderAt_center_add_twice_upper
      (riemannXiCompletedSelfDualAnalyticFamily radius hradius) ()

end GaloisForLFunctions.RHTower


