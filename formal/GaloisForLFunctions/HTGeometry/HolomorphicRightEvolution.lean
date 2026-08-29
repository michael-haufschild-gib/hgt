import GaloisForLFunctions.HTGeometry.LocallyIntegrableLinearEvolution
import GaloisForLFunctions.HTGeometry.CompactConfigurationBaire
import GaloisForLFunctions.HTGeometry.MultivariableVitali
import GaloisForLFunctions.HTGeometry.PolydiscWeierstrass
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

namespace GaloisForLFunctions.HTGeometry

open Set Filter MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

variable {n : ℕ}

/-- Scale the distinguished first complex coordinate and leave all other coordinates fixed. -/
def firstCoordinateScale (s : ℝ) :
    (Fin (n + 1) → ℂ) →L[ℂ] (Fin (n + 1) → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    if i = 0 then (s : ℂ) • ContinuousLinearMap.proj i
    else ContinuousLinearMap.proj i

/-- Projection onto the distinguished first coordinate, returned in the same coordinate space. -/
def firstCoordinateProjection :
    (Fin (n + 1) → ℂ) →L[ℂ] (Fin (n + 1) → ℂ) :=
  (ContinuousLinearMap.single ℂ (fun _ : Fin (n + 1) => ℂ) 0).comp
    (ContinuousLinearMap.proj 0)

theorem firstCoordinateScale_eq (s : ℝ) :
    firstCoordinateScale (n := n) s = ContinuousLinearMap.id ℂ _ +
      ((s : ℂ) - 1) • firstCoordinateProjection := by
  ext q i
  by_cases hi : i = 0
  · subst i
    simp [firstCoordinateScale, firstCoordinateProjection, smul_eq_mul]
    ring
  · simp [firstCoordinateScale, firstCoordinateProjection, hi]

theorem continuous_firstCoordinateScale :
    Continuous (firstCoordinateScale (n := n)) := by
  rw [show firstCoordinateScale (n := n) = fun s : ℝ => ContinuousLinearMap.id ℂ _ +
      ((s : ℂ) - 1) • firstCoordinateProjection by
    funext s
    exact firstCoordinateScale_eq s]
  fun_prop

@[simp]
theorem firstCoordinateScale_apply_zero (s : ℝ) (q : Fin (n + 1) → ℂ) :
    firstCoordinateScale s q 0 = (s : ℂ) * q 0 := by
  simp [firstCoordinateScale, smul_eq_mul]

theorem firstCoordinateScale_apply_ne_zero (s : ℝ) (q : Fin (n + 1) → ℂ)
    {i : Fin (n + 1)} (hi : i ≠ 0) :
    firstCoordinateScale s q i = q i := by
  simp [firstCoordinateScale, hi]

@[simp]
theorem firstCoordinateScale_one (q : Fin (n + 1) → ℂ) :
    firstCoordinateScale 1 q = q := by
  ext i
  by_cases hi : i = 0
  · subst i
    simp
  · simp [firstCoordinateScale_apply_ne_zero, hi]

theorem firstCoordinateScale_comp (s t : ℝ) (q : Fin (n + 1) → ℂ) :
    firstCoordinateScale s (firstCoordinateScale t q) = firstCoordinateScale (s * t) q := by
  ext i
  by_cases hi : i = 0
  · subst i
    simp [firstCoordinateScale_apply_zero]
    ring
  · simp [firstCoordinateScale_apply_ne_zero, hi]

theorem continuous_firstCoordinateScale_uncurry :
    Continuous (fun p : (Fin (n + 1) → ℂ) × ℝ => firstCoordinateScale p.2 p.1) := by
  apply continuous_pi
  intro i
  by_cases hi : i = 0
  · subst i
    simp only [firstCoordinateScale_apply_zero]
    fun_prop
  · simp only [firstCoordinateScale_apply_ne_zero _ _ hi]
    fun_prop

/-- Points whose entire distinguished-coordinate segment remains inside `U`. -/
def firstSegmentDomain (U : Set (Fin (n + 1) → ℂ)) : Set (Fin (n + 1) → ℂ) :=
  compactConfigurationAvoidance
    (fun p : (Fin (n + 1) → ℂ) × ℝ => firstCoordinateScale p.2 p.1)
    Uᶜ (Icc (0 : ℝ) 1)

theorem mem_firstSegmentDomain_iff {U : Set (Fin (n + 1) → ℂ)}
    {q : Fin (n + 1) → ℂ} :
    q ∈ firstSegmentDomain U ↔
      ∀ s ∈ Icc (0 : ℝ) 1, firstCoordinateScale s q ∈ U := by
  simp [firstSegmentDomain, compactConfigurationAvoidance]

theorem isOpen_firstSegmentDomain {U : Set (Fin (n + 1) → ℂ)} (hU : IsOpen U) :
    IsOpen (firstSegmentDomain U) := by
  exact compactConfigurationAvoidance_isOpen
    (fun p : (Fin (n + 1) → ℂ) × ℝ => firstCoordinateScale p.2 p.1)
    continuous_firstCoordinateScale_uncurry Uᶜ hU.isClosed_compl (Icc (0 : ℝ) 1) isCompact_Icc

/-- Complex integral along the distinguished-coordinate segment from zero. -/
def firstSegmentPrimitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (F : (Fin (n + 1) → ℂ) → E) (q : Fin (n + 1) → ℂ) : E :=
  q 0 • ∫ s in (0 : ℝ)..1, F (firstCoordinateScale s q)

def firstSegmentIntegrandFDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : (Fin (n + 1) → ℂ) → E) (q : Fin (n + 1) → ℂ) (s : ℝ) :
    (Fin (n + 1) → ℂ) →L[ℂ] E :=
  (fderiv ℂ F (firstCoordinateScale s q)).comp (firstCoordinateScale s)

theorem firstSegmentIntegrand_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : (Fin (n + 1) → ℂ) → E} {U : Set (Fin (n + 1) → ℂ)}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    {q : Fin (n + 1) → ℂ} {s : ℝ} (hq : firstCoordinateScale s q ∈ U) :
    HasFDerivAt (fun y => F (firstCoordinateScale s y))
      (firstSegmentIntegrandFDeriv F q s) q := by
  exact (((hF _ hq).differentiableAt (hU.mem_nhds hq)).hasFDerivAt.comp q
    (firstCoordinateScale s).hasFDerivAt)

theorem continuousOn_firstSegmentIntegrandFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {F : (Fin (n + 1) → ℂ) → E} {U : Set (Fin (n + 1) → ℂ)}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    ContinuousOn
      (fun p : (Fin (n + 1) → ℂ) × ℝ => firstSegmentIntegrandFDeriv F p.1 p.2)
      (firstSegmentDomain U ×ˢ Icc (0 : ℝ) 1) := by
  let S := firstSegmentDomain U ×ˢ Icc (0 : ℝ) 1
  have hmem : ∀ p ∈ S, firstCoordinateScale p.2 p.1 ∈ U := by
    intro p hp
    exact (mem_firstSegmentDomain_iff.mp hp.1) p.2 hp.2
  have hpoint : ContinuousOn
      (fun p : (Fin (n + 1) → ℂ) × ℝ => fderiv ℂ F (firstCoordinateScale p.2 p.1)) S :=
    (continuousOn_fderiv_of_differentiableOn hU hF).comp
      continuous_firstCoordinateScale_uncurry.continuousOn hmem
  have hscale : ContinuousOn
      (fun p : (Fin (n + 1) → ℂ) × ℝ => firstCoordinateScale (n := n) p.2) S :=
    ((continuous_firstCoordinateScale (n := n)).comp continuous_snd).continuousOn
  exact isBoundedBilinearMap_comp.continuous.comp_continuousOn (hpoint.prodMk hscale)

set_option maxHeartbeats 2000000 in
/-- Integrating along the distinguished complex coordinate preserves holomorphy on every point
whose full segment remains in the original open domain. -/
theorem differentiableOn_firstSegmentPrimitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E]
    {F : (Fin (n + 1) → ℂ) → E} {U : Set (Fin (n + 1) → ℂ)}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    DifferentiableOn ℂ (firstSegmentPrimitive F) (firstSegmentDomain U) := by
  intro q hq
  have hVopen := isOpen_firstSegmentDomain hU
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hVopen q hq
  let r₀ : ℝ := r / 2
  have hr₀ : 0 < r₀ := by dsimp [r₀]; linarith
  have hr₀r : r₀ < r := by dsimp [r₀]; linarith
  have hclosed : Metric.closedBall q r₀ ⊆ firstSegmentDomain U :=
    (Metric.closedBall_subset_ball hr₀r).trans hrsub
  let K : Set ((Fin (n + 1) → ℂ) × ℝ) :=
    Metric.closedBall q r₀ ×ˢ Icc (0 : ℝ) 1
  have hKS : K ⊆ firstSegmentDomain U ×ˢ Icc (0 : ℝ) 1 := by
    intro p hp
    exact ⟨hclosed hp.1, hp.2⟩
  letI : ProperSpace (Fin (n + 1) → ℂ) := FiniteDimensional.proper ℂ _
  have hKcompact : IsCompact K := (isCompact_closedBall q r₀).prod isCompact_Icc
  have hDcont : ContinuousOn
      (fun p : (Fin (n + 1) → ℂ) × ℝ => firstSegmentIntegrandFDeriv F p.1 p.2) K :=
    (continuousOn_firstSegmentIntegrandFDeriv hU hF).mono hKS
  obtain ⟨B, hB⟩ := hKcompact.exists_bound_of_continuousOn hDcont
  let C : NNReal := ⟨max B 0, le_max_right _ _⟩
  have huIoc : uIoc (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 := by
    rw [uIoc_of_le zero_le_one]
    exact Ioc_subset_Icc_self
  have hball : Metric.ball q r₀ ⊆ firstSegmentDomain U :=
    Metric.ball_subset_closedBall.trans hclosed
  have hpath_cont (x : Fin (n + 1) → ℂ) (hx : x ∈ firstSegmentDomain U) :
      ContinuousOn (fun s : ℝ => F (firstCoordinateScale s x)) (Icc (0 : ℝ) 1) := by
    let path : ℝ → (Fin (n + 1) → ℂ) × ℝ := fun s => (x, s)
    have hpath : Continuous path := continuous_const.prodMk continuous_id
    exact hF.continuousOn.comp
      (continuous_firstCoordinateScale_uncurry.comp hpath).continuousOn
      (fun s hs => (mem_firstSegmentDomain_iff.mp hx) s hs)
  have hDpath_cont : ContinuousOn
      (fun s : ℝ => firstSegmentIntegrandFDeriv F q s) (Icc (0 : ℝ) 1) := by
    let path : ℝ → (Fin (n + 1) → ℂ) × ℝ := fun s => (q, s)
    have hpath : Continuous path := continuous_const.prodMk continuous_id
    have hp : ContinuousOn (fun s : ℝ =>
        fderiv ℂ F (firstCoordinateScale s q)) (Icc (0 : ℝ) 1) :=
      (continuousOn_fderiv_of_differentiableOn hU hF).comp
        (continuous_firstCoordinateScale_uncurry.comp hpath).continuousOn
        (fun s hs => (mem_firstSegmentDomain_iff.mp hq) s hs)
    have hscl : ContinuousOn (fun s : ℝ => firstCoordinateScale (n := n) s)
        (Icc (0 : ℝ) 1) := (continuous_firstCoordinateScale (n := n)).continuousOn
    exact isBoundedBilinearMap_comp.continuous.comp_continuousOn (hp.prodMk hscl)
  have hlip : ∀ s ∈ uIoc (0 : ℝ) 1,
      LipschitzOnWith C (fun x => F (firstCoordinateScale s x)) (Metric.ball q r₀) := by
    intro s hs
    have hsI : s ∈ Icc (0 : ℝ) 1 := huIoc hs
    refine (convex_ball q r₀).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x hx => (firstSegmentIntegrand_hasFDerivAt hU hF
        ((mem_firstSegmentDomain_iff.mp (hball hx)) s hsI)).differentiableAt)
      (fun x hx => ?_)
    rw [(firstSegmentIntegrand_hasFDerivAt hU hF
      ((mem_firstSegmentDomain_iff.mp (hball hx)) s hsI)).fderiv]
    rw [← NNReal.coe_le_coe]
    exact le_trans (hB (x, s) ⟨Metric.ball_subset_closedBall hx, hsI⟩) (le_max_left _ _)
  have hmain : HasFDerivAt
      (fun x : Fin (n + 1) → ℂ => ∫ s in (0 : ℝ)..1,
        F (firstCoordinateScale s x))
      (∫ s in (0 : ℝ)..1, firstSegmentIntegrandFDeriv F q s) q := by
    exact (_root_.intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip
      (F := fun x s => F (firstCoordinateScale s x))
      (F' := fun s => firstSegmentIntegrandFDeriv F q s)
      (bound := fun _ : ℝ => (C : ℝ))
      (Metric.ball_mem_nhds q hr₀)
      (by
        filter_upwards [Metric.ball_mem_nhds q hr₀] with x hx
        exact ((hpath_cont x (hball hx)).mono huIoc).aestronglyMeasurable
          measurableSet_uIoc)
      (by
        have hc := hpath_cont q hq
        rw [← uIcc_of_le zero_le_one] at hc
        exact hc.intervalIntegrable)
      ((hDpath_cont.mono huIoc).aestronglyMeasurable measurableSet_uIoc)
      (Filter.Eventually.of_forall fun s hs => by
        simpa [Real.nnabs_of_nonneg C.coe_nonneg] using hlip s hs)
      intervalIntegrable_const
      (Filter.Eventually.of_forall fun s hs =>
        firstSegmentIntegrand_hasFDerivAt hU hF
          ((mem_firstSegmentDomain_iff.mp hq) s (huIoc hs)))).2
  change DifferentiableWithinAt ℂ (firstSegmentPrimitive F) (firstSegmentDomain U) q
  have hhead : DifferentiableAt ℂ (fun x : Fin (n + 1) → ℂ => x 0) q :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) 0).differentiableAt
  have heq : ((fun x : Fin (n + 1) → ℂ => x 0) •
      fun x => ∫ s in (0 : ℝ)..1, F (firstCoordinateScale s x)) =
      firstSegmentPrimitive F := by
    funext x
    rw [Pi.smul_apply']
    rw [firstSegmentPrimitive]
  rw [← heq]
  exact (hhead.smul hmain.differentiableAt).differentiableWithinAt

section ComplexPicard

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

/-- The opposite-algebra embedding as a bounded complex-linear map. -/
def mulOppositeOpCLM : B →L[ℂ] Bᵐᵒᵖ :=
  { toLinearMap :=
      { toFun := MulOpposite.op
        map_add' := by intro x y; rfl
        map_smul' := by intro q x; rfl }
    cont := (LinearIsometry.isometry
      ({ toLinearMap :=
          { toFun := MulOpposite.op
            map_add' := by intro x y; rfl
            map_smul' := by intro q x; rfl }
         norm_map' := MulOpposite.norm_op } : B →ₗᵢ[ℂ] Bᵐᵒᵖ)).continuous }

/-- Forgetting the opposite algebra as a bounded complex-linear map. -/
def mulOppositeUnopCLM : Bᵐᵒᵖ →L[ℂ] B :=
  { toLinearMap :=
      { toFun := MulOpposite.unop
        map_add' := by intro x y; rfl
        map_smul' := by intro q x; rfl }
    cont := (LinearIsometry.isometry
      ({ toLinearMap :=
          { toFun := MulOpposite.unop
            map_add' := by intro x y; rfl
            map_smul' := by intro q x; rfl }
         norm_map' := MulOpposite.norm_unop } : Bᵐᵒᵖ →ₗᵢ[ℂ] B)).continuous }

/-- Complex-time Picard terms for a coefficient with one distinguished time coordinate. -/
def complexPicard (A : (Fin (n + 1) → ℂ) → B) : ℕ → (Fin (n + 1) → ℂ) → B
  | 0, _ => 1
  | k + 1, q => firstSegmentPrimitive (fun w => A w * complexPicard A k w) q

/-- Real path coefficient obtained by pulling a complex coefficient back along the distinguished
coordinate segment. -/
def complexPathCoefficient (A : (Fin (n + 1) → ℂ) → B)
    (q : Fin (n + 1) → ℂ) (s : ℝ) : B :=
  q 0 • A (firstCoordinateScale (Set.projIcc (0 : ℝ) 1 zero_le_one s : ℝ) q)

@[simp]
theorem complexPicard_zero (A : (Fin (n + 1) → ℂ) → B) (q : Fin (n + 1) → ℂ) :
    complexPicard A 0 q = 1 := rfl

theorem complexPicard_succ (A : (Fin (n + 1) → ℂ) → B) (k : ℕ)
    (q : Fin (n + 1) → ℂ) :
    complexPicard A (k + 1) q =
      firstSegmentPrimitive (fun w => A w * complexPicard A k w) q := rfl

/-- Every finite complex Picard term is holomorphic on a first-coordinate star domain. -/
theorem differentiableOn_complexPicard
    {A : (Fin (n + 1) → ℂ) → B} {U : Set (Fin (n + 1) → ℂ)}
    (hU : IsOpen U)
    (hstar : ∀ q ∈ U, ∀ s ∈ Icc (0 : ℝ) 1, firstCoordinateScale s q ∈ U)
    (hA : DifferentiableOn ℂ A U) :
    ∀ k : ℕ, DifferentiableOn ℂ (complexPicard A k) U
  | 0 => differentiableOn_const 1
  | k + 1 => by
      have hk := differentiableOn_complexPicard hU hstar hA k
      have hprod : DifferentiableOn ℂ (fun q => A q * complexPicard A k q) U := hA.mul hk
      exact (differentiableOn_firstSegmentPrimitive hU hprod).mono
        (fun q hq => mem_firstSegmentDomain_iff.mpr (hstar q hq))

/-- Complex Picard terms restricted to a real radial segment are exactly the ordinary
Peano--Baker terms for the pulled-back coefficient. -/
theorem complexPicard_scale_eq_l1Picard
    (A : (Fin (n + 1) → ℂ) → B) (q : Fin (n + 1) → ℂ) :
    ∀ (k : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
      complexPicard A k (firstCoordinateScale t q) =
        l1Picard (complexPathCoefficient A q) k t
  | 0, t, _ => by simp
  | k + 1, t, ht => by
      rcases ht.1.eq_or_lt with rfl | htpos
      · simp [complexPicard_succ, firstSegmentPrimitive, l1Picard_succ,
          firstCoordinateScale_apply_zero]
      · have ht0 : t ≠ 0 := ne_of_gt htpos
        let f : ℝ → B := fun u =>
          complexPathCoefficient A q u * l1Picard (complexPathCoefficient A q) k u
        have hintegrand : ∀ s ∈ uIcc (0 : ℝ) 1,
            q 0 • (A (firstCoordinateScale s (firstCoordinateScale t q)) *
              complexPicard A k (firstCoordinateScale s (firstCoordinateScale t q))) =
              f (s * t) := by
          intro s hs
          have hsI : s ∈ Icc (0 : ℝ) 1 := by
            rw [uIcc_of_le zero_le_one] at hs
            exact hs
          have hst : s * t ∈ Icc (0 : ℝ) 1 :=
            ⟨mul_nonneg hsI.1 ht.1, by nlinarith [hsI.2, ht.2]⟩
          rw [firstCoordinateScale_comp, complexPicard_scale_eq_l1Picard A q k (s * t)
            hst]
          simp [f, complexPathCoefficient, Set.projIcc_of_mem zero_le_one hst]
        have hrewrite :
            ∫ s in (0 : ℝ)..1,
                q 0 • (A (firstCoordinateScale s (firstCoordinateScale t q)) *
                  complexPicard A k (firstCoordinateScale s (firstCoordinateScale t q))) =
              ∫ s in (0 : ℝ)..1, f (s * t) :=
          intervalIntegral.integral_congr hintegrand
        have hsub := intervalIntegral.integral_comp_mul_right
          (a := (0 : ℝ)) (b := 1) (c := t) f ht0
        rw [complexPicard_succ, l1Picard_succ, firstSegmentPrimitive,
          firstCoordinateScale_apply_zero]
        calc
          ((t : ℂ) * q 0) • (∫ x in (0 : ℝ)..1,
              (A (firstCoordinateScale x (firstCoordinateScale t q)) *
                complexPicard A k (firstCoordinateScale x (firstCoordinateScale t q)))) =
              (t : ℂ) • (q 0 • (∫ x in (0 : ℝ)..1,
                (A (firstCoordinateScale x (firstCoordinateScale t q)) *
                  complexPicard A k (firstCoordinateScale x (firstCoordinateScale t q))))) := by
            rw [smul_smul]
          _ = (t : ℂ) • (∫ x in (0 : ℝ)..1, q 0 •
                (A (firstCoordinateScale x (firstCoordinateScale t q)) *
                  complexPicard A k (firstCoordinateScale x (firstCoordinateScale t q)))) := by
            rw [intervalIntegral.integral_smul]
          _ = (t : ℂ) • (∫ x in (0 : ℝ)..1, f (x * t)) := by rw [hrewrite]
          _ = ∫ s in (0 : ℝ)..t,
              complexPathCoefficient A q s * l1Picard (complexPathCoefficient A q) k s := by
            rw [hsub]
            simp [f, smul_smul, ht0]

theorem complexPicard_eq_l1Picard_one
    (A : (Fin (n + 1) → ℂ) → B) (q : Fin (n + 1) → ℂ) (k : ℕ) :
    complexPicard A k q = l1Picard (complexPathCoefficient A q) k 1 := by
  calc
    complexPicard A k q = complexPicard A k (firstCoordinateScale 1 q) := by
      rw [firstCoordinateScale_one]
    _ = l1Picard (complexPathCoefficient A q) k 1 :=
      complexPicard_scale_eq_l1Picard A q k 1 ⟨zero_le_one, le_rfl⟩

omit [CompleteSpace B] in
theorem continuous_complexPathCoefficient
    {A : (Fin (n + 1) → ℂ) → B} {U : Set (Fin (n + 1) → ℂ)}
    (hstar : ∀ q ∈ U, ∀ s ∈ Icc (0 : ℝ) 1, firstCoordinateScale s q ∈ U)
    (hA : DifferentiableOn ℂ A U) {q : Fin (n + 1) → ℂ} (hq : q ∈ U) :
    Continuous (complexPathCoefficient A q) := by
  let clamp : ℝ → ℝ := fun s => (Set.projIcc (0 : ℝ) 1 zero_le_one s : ℝ)
  have hclamp : Continuous clamp := continuous_subtype_val.comp continuous_projIcc
  let path : ℝ → (Fin (n + 1) → ℂ) × ℝ := fun s => (q, clamp s)
  have hpath : Continuous path := continuous_const.prodMk hclamp
  have hscale : Continuous (fun s => firstCoordinateScale (clamp s) q) :=
    continuous_firstCoordinateScale_uncurry.comp hpath
  have hmem : ∀ s, firstCoordinateScale (clamp s) q ∈ U := by
    intro s
    exact hstar q hq (clamp s) (Set.projIcc (0 : ℝ) 1 zero_le_one s).property
  have hcomp : Continuous (fun s => A (firstCoordinateScale (clamp s) q)) := by
    have hAcont : ContinuousOn A U := hA.continuousOn
    rw [← continuousOn_univ]
    exact hAcont.comp hscale.continuousOn (fun s _ => hmem s)
  have heq : complexPathCoefficient A q =
      ((fun _ : ℝ => q 0) • fun s => A (firstCoordinateScale (clamp s) q)) := by
    funext s
    rw [Pi.smul_apply', complexPathCoefficient]
  rw [heq]
  exact continuous_const.smul hcomp

theorem summable_complexPicard
    {A : (Fin (n + 1) → ℂ) → B} {U : Set (Fin (n + 1) → ℂ)}
    (hstar : ∀ q ∈ U, ∀ s ∈ Icc (0 : ℝ) 1, firstCoordinateScale s q ∈ U)
    (hA : DifferentiableOn ℂ A U) {q : Fin (n + 1) → ℂ} (hq : q ∈ U) :
    Summable fun k => complexPicard A k q := by
  have hloc : LocallyIntegrable (complexPathCoefficient A q) volume :=
    (continuous_complexPathCoefficient hstar hA hq).locallyIntegrable
  simpa only [complexPicard_eq_l1Picard_one] using
    (summable_l1Picard hloc (t := (1 : ℝ)) zero_le_one)

/-- Compact parameter sets admit one factorial majorant for every complex Picard term. -/
theorem exists_uniform_norm_complexPicard_le
    {A : (Fin (n + 1) → ℂ) → B} {U K : Set (Fin (n + 1) → ℂ)}
    (hstar : ∀ q ∈ U, ∀ s ∈ Icc (0 : ℝ) 1, firstCoordinateScale s q ∈ U)
    (hA : DifferentiableOn ℂ A U) (hKU : K ⊆ U) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k q, q ∈ K →
      ‖complexPicard A k q‖ ≤ ‖(1 : B)‖ * (C ^ k / (k.factorial : ℝ)) := by
  let S : Set ((Fin (n + 1) → ℂ) × ℝ) := K ×ˢ Icc (0 : ℝ) 1
  have hScompact : IsCompact S := hK.prod isCompact_Icc
  have hscale : ContinuousOn
      (fun p : (Fin (n + 1) → ℂ) × ℝ => firstCoordinateScale p.2 p.1) S :=
    continuous_firstCoordinateScale_uncurry.continuousOn
  have hmem : ∀ p ∈ S, firstCoordinateScale p.2 p.1 ∈ U := by
    intro p hp
    exact hstar p.1 (hKU hp.1) p.2 hp.2
  have hAval : ContinuousOn
      (fun p : (Fin (n + 1) → ℂ) × ℝ => A (firstCoordinateScale p.2 p.1)) S :=
    hA.continuousOn.comp hscale hmem
  have hhead : Continuous
      (fun p : (Fin (n + 1) → ℂ) × ℝ => p.1 0) := by fun_prop
  have hval : ContinuousOn
      (fun p : (Fin (n + 1) → ℂ) × ℝ =>
        p.1 0 • A (firstCoordinateScale p.2 p.1)) S := by
    exact hhead.continuousOn.smul hAval
  obtain ⟨M, hM⟩ := hScompact.exists_bound_of_continuousOn hval
  let C : ℝ := max M 0
  have hC : 0 ≤ C := le_max_right _ _
  refine ⟨C, hC, ?_⟩
  intro k q hq
  have hqU : q ∈ U := hKU hq
  have hcont := continuous_complexPathCoefficient hstar hA hqU
  have hloc : LocallyIntegrable (complexPathCoefficient A q) volume := hcont.locallyIntegrable
  have hcoeff : ∀ s : ℝ, ‖complexPathCoefficient A q s‖ ≤ C := by
    intro s
    let c : ℝ := (Set.projIcc (0 : ℝ) 1 zero_le_one s : ℝ)
    have hc : c ∈ Icc (0 : ℝ) 1 := (Set.projIcc (0 : ℝ) 1 zero_le_one s).property
    exact le_trans (hM (q, c) ⟨hq, hc⟩) (le_max_left _ _)
  have hmass : positiveMass (complexPathCoefficient A q) 1 ≤ C := by
    rw [positiveMass]
    have hn : IntervalIntegrable (fun s => ‖complexPathCoefficient A q s‖) volume 0 1 :=
      (hcont.intervalIntegrable 0 1).norm
    calc
      (∫ s in (0 : ℝ)..1, ‖complexPathCoefficient A q s‖) ≤
          ∫ _s in (0 : ℝ)..1, C :=
        intervalIntegral.integral_mono_on zero_le_one hn intervalIntegrable_const
          (fun s _ => hcoeff s)
      _ = C := by simp
  rw [complexPicard_eq_l1Picard_one]
  refine le_trans (norm_l1Picard_le hloc k zero_le_one) ?_
  have hmass0 : 0 ≤ positiveMass (complexPathCoefficient A q) 1 :=
    positiveMass_nonneg zero_le_one
  have hp := pow_le_pow_left₀ hmass0 hmass k
  have hcoef : 0 ≤ ‖(1 : B)‖ / (k.factorial : ℝ) := by positivity
  calc
    ‖(1 : B)‖ * positiveMass (complexPathCoefficient A q) 1 ^ k / (k.factorial : ℝ) =
        (‖(1 : B)‖ / (k.factorial : ℝ)) *
          positiveMass (complexPathCoefficient A q) 1 ^ k := by ring
    _ ≤ (‖(1 : B)‖ / (k.factorial : ℝ)) * C ^ k :=
      mul_le_mul_of_nonneg_left hp hcoef
    _ = ‖(1 : B)‖ * (C ^ k / (k.factorial : ℝ)) := by ring

/-- Partial sums of the complex Peano--Baker evolution. -/
def complexEvolutionPartial (A : (Fin (n + 1) → ℂ) → B) (N : ℕ)
    (q : Fin (n + 1) → ℂ) : B :=
  ∑ k ∈ Finset.range N, complexPicard A k q

/-- Complex Peano--Baker evolution. -/
def complexEvolution (A : (Fin (n + 1) → ℂ) → B)
    (q : Fin (n + 1) → ℂ) : B :=
  ∑' k, complexPicard A k q

/-- At complex time one, the complex Picard sum is the ordinary Peano--Baker evolution of
the pulled-back coefficient. -/
theorem complexEvolution_eq_positiveEvolution_one
    (A : (Fin (n + 1) → ℂ) → B) (q : Fin (n + 1) → ℂ) :
    complexEvolution A q = positiveEvolution (complexPathCoefficient A q) 1 := by
  unfold complexEvolution positiveEvolution
  congr 1
  funext k
  exact complexPicard_eq_l1Picard_one A q k

/-- Holomorphic right evolution `J' = J A`, obtained by applying the left-evolution
construction in the opposite Banach algebra. -/
def rightComplexEvolution (A : (Fin (n + 1) → ℂ) → B)
    (q : Fin (n + 1) → ℂ) : B :=
  mulOppositeUnopCLM (complexEvolution ((mulOppositeOpCLM (B := B)) ∘ A) q)

/-- Global right Carathéodory evolution, transported from the opposite algebra. -/
def rightCaratheodoryEvolution (A : ℝ → B) (t : ℝ) : B :=
  mulOppositeUnopCLM
    (caratheodoryEvolution ((mulOppositeOpCLM (B := B)) ∘ A) t)

@[simp]
theorem rightCaratheodoryEvolution_zero {A : ℝ → B} (hA : Continuous A) :
    rightCaratheodoryEvolution A 0 = 1 := by
  have hAop : LocallyIntegrable ((mulOppositeOpCLM (B := B)) ∘ A) volume :=
    ((mulOppositeOpCLM (B := B)).continuous.comp hA).locallyIntegrable
  rw [rightCaratheodoryEvolution, caratheodoryEvolution_zero hAop]
  rfl

theorem continuous_rightCaratheodoryEvolution {A : ℝ → B} (hA : Continuous A) :
    Continuous (rightCaratheodoryEvolution A) := by
  have hAop : LocallyIntegrable ((mulOppositeOpCLM (B := B)) ∘ A) volume :=
    ((mulOppositeOpCLM (B := B)).continuous.comp hA).locallyIntegrable
  exact (mulOppositeUnopCLM (B := B)).continuous.comp
    (continuous_caratheodoryEvolution hAop)

/-- Volterra equation for global right evolution. -/
theorem rightCaratheodoryEvolution_integral_equation {A : ℝ → B}
    (hA : Continuous A) (t : ℝ) :
    rightCaratheodoryEvolution A t =
      1 + ∫ s in (0 : ℝ)..t, rightCaratheodoryEvolution A s * A s := by
  let Aop : ℝ → Bᵐᵒᵖ := (mulOppositeOpCLM (B := B)) ∘ A
  have hAop_cont : Continuous Aop := (mulOppositeOpCLM (B := B)).continuous.comp hA
  have hAop : LocallyIntegrable Aop volume := hAop_cont.locallyIntegrable
  let F : ℝ → Bᵐᵒᵖ := fun s => Aop s * caratheodoryEvolution Aop s
  have hFcont : Continuous F :=
    hAop_cont.mul (continuous_caratheodoryEvolution hAop)
  have hFint : IntervalIntegrable F volume 0 t := hFcont.intervalIntegrable 0 t
  have hmap := (mulOppositeUnopCLM (B := B)).intervalIntegral_comp_comm hFint
  rw [rightCaratheodoryEvolution]
  change mulOppositeUnopCLM (caratheodoryEvolution Aop t) = _
  rw [caratheodoryEvolution_integral_equation hAop]
  change mulOppositeUnopCLM (1 + ∫ s in (0 : ℝ)..t, F s) = _
  rw [map_add]
  change 1 + mulOppositeUnopCLM (∫ s in (0 : ℝ)..t, F s) = _
  rw [← hmap]
  rfl

/-- A continuous coefficient upgrades the left Carathéodory solution from an a.e. ODE to a
classical ODE. -/
theorem hasDerivAt_caratheodoryEvolution_of_continuous {A : ℝ → B}
    (hA : Continuous A) (t : ℝ) :
    HasDerivAt (caratheodoryEvolution A)
      (A t * caratheodoryEvolution A t) t := by
  have hloc : LocallyIntegrable A volume := hA.locallyIntegrable
  let F : ℝ → B := fun s => A s * caratheodoryEvolution A s
  have hF : Continuous F := hA.mul (continuous_caratheodoryEvolution hloc)
  have hprim : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, F s) (F t) t :=
    intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable 0 t)
      (hF.stronglyMeasurableAtFilter _ _) hF.continuousAt
  have heq : caratheodoryEvolution A =
      fun u => 1 + ∫ s in (0 : ℝ)..u, F s := by
    funext u
    exact caratheodoryEvolution_integral_equation hloc u
  have hevent : caratheodoryEvolution A =ᶠ[𝓝 t]
      fun u => 1 + ∫ s in (0 : ℝ)..u, F s :=
    Filter.Eventually.of_forall (congrFun heq)
  have hout := (hprim.const_add 1).congr_of_eventuallyEq hevent
  simpa only [F] using hout

/-- A continuous coefficient gives the classical right ODE `R' = R A`. -/
theorem hasDerivAt_rightCaratheodoryEvolution {A : ℝ → B}
    (hA : Continuous A) (t : ℝ) :
    HasDerivAt (rightCaratheodoryEvolution A)
      (rightCaratheodoryEvolution A t * A t) t := by
  let F : ℝ → B := fun s => rightCaratheodoryEvolution A s * A s
  have hF : Continuous F := (continuous_rightCaratheodoryEvolution hA).mul hA
  have hprim : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, F s) (F t) t :=
    intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable 0 t)
      (hF.stronglyMeasurableAtFilter _ _) hF.continuousAt
  have heq : rightCaratheodoryEvolution A =
      fun u => 1 + ∫ s in (0 : ℝ)..u, F s := by
    funext u
    exact rightCaratheodoryEvolution_integral_equation hA u
  have hevent : rightCaratheodoryEvolution A =ᶠ[𝓝 t]
      fun u => 1 + ∫ s in (0 : ℝ)..u, F s :=
    Filter.Eventually.of_forall (congrFun heq)
  have hout := (hprim.const_add 1).congr_of_eventuallyEq hevent
  simpa only [F] using hout

/-- Right evolution has an explicit right inverse, the left evolution of the negative
coefficient. -/
theorem rightCaratheodoryEvolution_mul_negativeEvolution {A : ℝ → B}
    (hA : Continuous A) (t : ℝ) :
    rightCaratheodoryEvolution A t *
        caratheodoryEvolution (fun s => -A s) t = 1 := by
  let R : ℝ → B := rightCaratheodoryEvolution A
  let K : ℝ → B := caratheodoryEvolution (fun s => -A s)
  have hneg : Continuous (fun s => -A s) := hA.neg
  have hzero : ∀ s : ℝ, HasDerivAt (fun u => R u * K u) 0 s := by
    intro s
    have hR := hasDerivAt_rightCaratheodoryEvolution hA s
    have hK := hasDerivAt_caratheodoryEvolution_of_continuous hneg s
    convert hR.mul hK using 1
    · rfl
    · noncomm_ring
  have hdiff : Differentiable ℝ (fun u => R u * K u) :=
    fun s => (hzero s).differentiableAt
  have hfderiv : ∀ s : ℝ, fderiv ℝ (fun u => R u * K u) s = 0 := by
    intro s
    rw [(hzero s).hasFDerivAt.fderiv]
    exact ContinuousLinearMap.toSpanSingleton_zero ℝ
  have hconst := is_const_of_fderiv_eq_zero hdiff hfderiv t 0
  change rightCaratheodoryEvolution A t *
      caratheodoryEvolution (fun s => -A s) t = 1
  calc
    rightCaratheodoryEvolution A t *
        caratheodoryEvolution (fun s => -A s) t = R 0 * K 0 := hconst
    _ = 1 := by
      dsimp only [R, K]
      rw [rightCaratheodoryEvolution_zero hA,
        caratheodoryEvolution_zero hneg.locallyIntegrable]
      simp

/-- In a directly finite Banach algebra (in particular, finite square matrices), every right
evolution value is a unit. -/
theorem isUnit_rightCaratheodoryEvolution [IsDedekindFiniteMonoid B]
    {A : ℝ → B} (hA : Continuous A) (t : ℝ) :
    IsUnit (rightCaratheodoryEvolution A t) := by
  rw [isUnit_iff_exists_inv]
  exact ⟨caratheodoryEvolution (fun s => -A s) t,
    rightCaratheodoryEvolution_mul_negativeEvolution hA t⟩

/-- Complex and real right evolutions agree at endpoint one. -/
theorem rightComplexEvolution_eq_rightCaratheodoryEvolution_one
    {A : (Fin (n + 1) → ℂ) → B} {U : Set (Fin (n + 1) → ℂ)}
    (hstar : ∀ q ∈ U, ∀ s ∈ Icc (0 : ℝ) 1, firstCoordinateScale s q ∈ U)
    (hA : DifferentiableOn ℂ A U) {q : Fin (n + 1) → ℂ} (hq : q ∈ U) :
    rightComplexEvolution A q =
      rightCaratheodoryEvolution (complexPathCoefficient A q) 1 := by
  let Aop : (Fin (n + 1) → ℂ) → Bᵐᵒᵖ := (mulOppositeOpCLM (B := B)) ∘ A
  have hcoeff : complexPathCoefficient Aop q =
      (mulOppositeOpCLM (B := B)) ∘ complexPathCoefficient A q := by
    funext s
    rfl
  have hcont := continuous_complexPathCoefficient hstar hA hq
  have hoploc : LocallyIntegrable
      ((mulOppositeOpCLM (B := B)) ∘ complexPathCoefficient A q) volume :=
    ((mulOppositeOpCLM (B := B)).continuous.comp hcont).locallyIntegrable
  rw [rightComplexEvolution, complexEvolution_eq_positiveEvolution_one]
  rw [rightCaratheodoryEvolution, caratheodoryEvolution_of_nonneg zero_le_one]
  rw [hcoeff]
  rfl

theorem tendstoLocallyUniformlyOn_complexEvolutionPartial
    {A : (Fin (n + 1) → ℂ) → B} {U : Set (Fin (n + 1) → ℂ)}
    (hU : IsOpen U)
    (hstar : ∀ q ∈ U, ∀ s ∈ Icc (0 : ℝ) 1, firstCoordinateScale s q ∈ U)
    (hA : DifferentiableOn ℂ A U) :
    TendstoLocallyUniformlyOn (complexEvolutionPartial A) (complexEvolution A) atTop U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  obtain ⟨C, hC, hbound⟩ := exists_uniform_norm_complexPicard_le hstar hA hKU hK
  have hmajor : Summable fun k : ℕ => ‖(1 : B)‖ * (C ^ k / (k.factorial : ℝ)) :=
    (Real.summable_pow_div_factorial C).mul_left ‖(1 : B)‖
  have huniform := tendstoUniformlyOn_tsum
    (u := fun k : ℕ => ‖(1 : B)‖ * (C ^ k / (k.factorial : ℝ)))
    (f := fun k : ℕ => fun q => complexPicard A k q) hmajor hbound
  intro v hv
  exact tendsto_finset_range.eventually (huniform v hv)

theorem differentiableOn_complexEvolutionPartial
    {A : (Fin (n + 1) → ℂ) → B} {U : Set (Fin (n + 1) → ℂ)}
    (hU : IsOpen U)
    (hstar : ∀ q ∈ U, ∀ s ∈ Icc (0 : ℝ) 1, firstCoordinateScale s q ∈ U)
    (hA : DifferentiableOn ℂ A U) :
    ∀ N, DifferentiableOn ℂ (complexEvolutionPartial A N) U
  | 0 => by
      have hzero : DifferentiableOn ℂ
          (fun _ : Fin (n + 1) → ℂ => (0 : B)) U := differentiableOn_const 0
      have heq : complexEvolutionPartial A 0 = fun _ : Fin (n + 1) → ℂ => (0 : B) := by
        funext q
        simp [complexEvolutionPartial]
      rw [heq]
      exact hzero
  | N + 1 => by
      have heq : complexEvolutionPartial A (N + 1) =
          complexEvolutionPartial A N + complexPicard A N := by
        funext q
        rw [Pi.add_apply]
        simp [complexEvolutionPartial, Finset.sum_range_succ]
      rw [heq]
      exact (differentiableOn_complexEvolutionPartial hU hstar hA N).add
        (differentiableOn_complexPicard hU hstar hA N)

/-- The complex Peano--Baker evolution is holomorphic on every first-coordinate star domain. -/
theorem analyticOnNhd_complexEvolution
    {A : (Fin (n + 1) → ℂ) → B} {U : Set (Fin (n + 1) → ℂ)}
    (hU : IsOpen U)
    (hstar : ∀ q ∈ U, ∀ s ∈ Icc (0 : ℝ) 1, firstCoordinateScale s q ∈ U)
    (hA : DifferentiableOn ℂ A U) :
    AnalyticOnNhd ℂ (complexEvolution A) U := by
  apply analyticOnNhd_of_tendstoLocallyUniformlyOn hU
  · exact differentiableOn_complexEvolutionPartial hU hstar hA
  · exact tendstoLocallyUniformlyOn_complexEvolutionPartial hU hstar hA

/-- Right Peano--Baker evolution is holomorphic on a first-coordinate star domain. -/
theorem analyticOnNhd_rightComplexEvolution
    {A : (Fin (n + 1) → ℂ) → B} {U : Set (Fin (n + 1) → ℂ)}
    (hU : IsOpen U)
    (hstar : ∀ q ∈ U, ∀ s ∈ Icc (0 : ℝ) 1, firstCoordinateScale s q ∈ U)
    (hA : DifferentiableOn ℂ A U) :
    AnalyticOnNhd ℂ (rightComplexEvolution A) U := by
  have hAop : DifferentiableOn ℂ ((mulOppositeOpCLM (B := B)) ∘ A) U :=
    (mulOppositeOpCLM (B := B)).differentiable.comp_differentiableOn hA
  have hevol : AnalyticOnNhd ℂ
      (complexEvolution ((mulOppositeOpCLM (B := B)) ∘ A)) U :=
    analyticOnNhd_complexEvolution hU hstar hAop
  have hunop : AnalyticOnNhd ℂ (mulOppositeUnopCLM (B := B)) univ :=
    (mulOppositeUnopCLM (B := B)).analyticOnNhd univ
  change AnalyticOnNhd ℂ
    ((mulOppositeUnopCLM (B := B)) ∘
      complexEvolution ((mulOppositeOpCLM (B := B)) ∘ A)) U
  exact hunop.comp hevol (fun _ _ => mem_univ _)

/-- Homogeneous right-Volterra uniqueness on a compact forward interval. -/
theorem eq_zero_of_continuous_right_volterra_on_Icc
    {A D : ℝ → B} (hA : Continuous A) (hD : Continuous D)
    {T : ℝ} (hT : 0 ≤ T)
    (hvolterra : ∀ t ∈ Icc (0 : ℝ) T,
      D t = ∫ s in (0 : ℝ)..t, D s * A s) :
    ∀ t ∈ Icc (0 : ℝ) T, D t = 0 := by
  let Aop : ℝ → Bᵐᵒᵖ := (mulOppositeOpCLM (B := B)) ∘ A
  let Dop : ℝ → Bᵐᵒᵖ := (mulOppositeOpCLM (B := B)) ∘ D
  have hAop_cont : Continuous Aop := (mulOppositeOpCLM (B := B)).continuous.comp hA
  have hAop : LocallyIntegrable Aop volume := hAop_cont.locallyIntegrable
  have hDop : Continuous Dop := (mulOppositeOpCLM (B := B)).continuous.comp hD
  have hleft : ∀ t ∈ Icc (0 : ℝ) T,
      Dop t = ∫ s in (0 : ℝ)..t, Aop s * Dop s := by
    intro t ht
    let F : ℝ → B := fun s => D s * A s
    have hF : Continuous F := hD.mul hA
    have hFint : IntervalIntegrable F volume 0 t := hF.intervalIntegrable 0 t
    have hmap := (mulOppositeOpCLM (B := B)).intervalIntegral_comp_comm hFint
    change mulOppositeOpCLM (D t) = _
    rw [hvolterra t ht]
    change mulOppositeOpCLM (∫ s in (0 : ℝ)..t, F s) = _
    rw [← hmap]
    rfl
  have hz := eq_zero_of_continuous_volterra_on_Icc hAop hDop hT hleft
  intro t ht
  have hzt := hz t ht
  change mulOppositeOpCLM (D t) = 0 at hzt
  have hu := congrArg MulOpposite.unop hzt
  simpa [mulOppositeOpCLM] using hu

end ComplexPicard

end
end GaloisForLFunctions.HTGeometry
