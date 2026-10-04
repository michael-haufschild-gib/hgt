import GaloisForLFunctions.RHTower.ChiRamanujanGlobalSourceNeighborhoods
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

/-!
# All-order global growth of the actual BAG sources

Local Banach-valued Cauchy estimates and the actual source neighborhoods give
polynomial growth of every joint complex derivative. Scalar restriction and
isometric frequency pullback give the same bounds for the literal real sources,
including damping derivatives, uniformly on the closed strip.
-/

noncomputable section
open Set Filter Metric
open scoped Topology BigOperators ContDiff
namespace RHTower.BAGTrace

/-- Local Banach-valued version of the corpus's scalar entire-function Cauchy bound. -/
private theorem norm_fderiv_le_of_analytic_ball
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {x : E} {R M : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall x R))
    (hb : ∀ y ∈ closedBall x R, ‖f y‖ ≤ M) : ‖fderiv ℂ f x‖ ≤ M/R := by
  have hx : x ∈ closedBall x R := mem_closedBall_self hR.le
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb x hx)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  by_cases hv : v=0
  · simp [hv]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let r := R/‖v‖
  have hr : 0 < r := div_pos hR hvpos
  let g : ℂ → E := fun s => x+s • v
  have hg : Differentiable ℂ g := by dsimp [g]; fun_prop
  have hgmap : MapsTo g (closedBall 0 r) (closedBall x R) := by
    intro z hz
    have hn : ‖z‖ ≤ r := by simpa using hz
    have hm := mul_le_mul_of_nonneg_right hn hvpos.le
    have he : r*‖v‖=R := div_mul_cancel₀ _ hvpos.ne'
    simpa only [g,mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,he] using hm
  have hfg : DifferentiableOn ℂ (f ∘ g) (closedBall 0 r) :=
    hf.differentiableOn.comp hg.differentiableOn hgmap
  have h1 : HasDerivAt g v 0 := by
    simpa [g] using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
  have hderiv : HasDerivAt (f ∘ g) (fderiv ℂ f x v) 0 := by
    have h : HasFDerivAt f (fderiv ℂ f x) (g 0) := by
      simpa only [g,zero_smul,add_zero] using (hf x hx).differentiableAt.hasFDerivAt
    exact h.comp_hasDerivAt 0 h1
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    (hfg.diffContOnCl_ball (subset_refl _))
    (fun z hz => hb (g z) (hgmap (sphere_subset_closedBall hz)))
  rw [hderiv.deriv] at hc
  exact hc.trans_eq (by dsimp [r]; field_simp)

/-- Cauchy control for every joint derivative; constants depend only on the order. -/
private theorem exists_iteratedFDeriv_ball_constant (n : ℕ) :
    ∃ K > 0, ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
      [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
      {f : E → F} {x : E} {R M : ℝ}, 0 < R →
      AnalyticOnNhd ℂ f (closedBall x R) →
      (∀ y ∈ closedBall x R, ‖f y‖ ≤ M) →
      ‖iteratedFDeriv ℂ n f x‖ ≤ K*M/R^n := by
  induction n with
  | zero =>
    refine ⟨1,zero_lt_one,?_⟩
    intro E F _ _ _ _ _ f x R M hR hf hb
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one,one_mul,div_one] using
      hb x (mem_closedBall_self hR.le)
  | succ n ih =>
    obtain ⟨K,hK,hbound⟩ := ih
    refine ⟨K*2^(n+1),by positivity,?_⟩
    intro E F _ _ _ _ _ f x R M hR hf hb
    have hR2 : 0 < R/2 := by positivity
    have hsub : closedBall x (R/2) ⊆ closedBall x R := closedBall_subset_closedBall (by linarith)
    have hball (y : E) (hy : y ∈ closedBall x (R/2)) :
        closedBall y (R/2) ⊆ closedBall x R := by
      apply closedBall_subset_closedBall'
      have hh : dist y x ≤ R/2 := hy
      linarith
    have hb' : ∀ y ∈ closedBall x (R/2), ‖iteratedFDeriv ℂ n f y‖ ≤ K*M/(R/2)^n := by
      intro y hy
      exact hbound hR2 (hf.mono (hball y hy)) (fun z hz => hb z (hball y hy hz))
    have hh := norm_fderiv_le_of_analytic_ball hR2 ((hf.iteratedFDeriv n).mono hsub) hb'
    rw [norm_fderiv_iteratedFDeriv] at hh
    exact hh.trans_eq (by rw [div_pow,pow_succ]; field_simp; ring)

/-- Every joint complex derivative of the literal cubic source has uniform polynomial growth. -/
theorem exists_regularCubicSource_derivative_polynomial_bound (n : ℕ) :
    ∃ C > 0, ∀ σ ∈ Icc (1 : ℝ) 2, ∀ u v : ℝ,
      ‖iteratedFDeriv ℂ n (fun w : Fin 3 → ℂ => regularCubicSource (w 0) (w 1) (w 2))
        ![σ,(u : ℂ)*Complex.I,(v : ℂ)*Complex.I]‖ ≤ C*(1+|u|+|v|)^(54+9*n) := by
  obtain ⟨d,hd,M,hM,hballs⟩ := exists_regularCubicSource_polynomial_balls
  obtain ⟨K,hK,hCauchy⟩ := exists_iteratedFDeriv_ball_constant n
  have hd0 : 0 < d := hd.1
  let C := K*M/d^n
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro σ hσ u v
  let T := 1+|u|+|v|
  have hT : 0 < T := by dsimp [T]; positivity
  have hR : 0 < d/T^9 := by positivity
  have ha := analyticOnNhd_regularCubicSource.mono
    (fun w hw => (hballs σ hσ u v w hw).1)
  have hh := hCauchy hR ha (fun w hw => (hballs σ hσ u v w hw).2)
  have halg (X Y Z W : ℝ) : X*(Y*W^54)/(Z/W^9)^n = (X*Y/Z^n)*W^(54+9*n) := by
    simp only [div_pow,pow_add,pow_mul]
    field_simp
  exact hh.trans_eq (halg K M d T)

/-- Every joint complex derivative of the literal axis source has uniform polynomial growth. -/
theorem exists_regularAxisSource_derivative_polynomial_bound (n : ℕ) :
    ∃ C > 0, ∀ σ ∈ Icc (1 : ℝ) 2, ∀ u : ℝ,
      ‖iteratedFDeriv ℂ n (fun w : Fin 2 → ℂ => regularAxisSource (w 0) (w 1))
        ![σ,(u : ℂ)*Complex.I]‖ ≤ C*(1+|u|)^(18+9*n) := by
  obtain ⟨d,hd,M,hM,hballs⟩ := exists_regularAxisSource_polynomial_balls
  obtain ⟨K,hK,hCauchy⟩ := exists_iteratedFDeriv_ball_constant n
  have hd0 : 0 < d := hd.1
  let C := K*M/d^n
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro σ hσ u
  let T := 1+|u|
  have hT : 0 < T := by dsimp [T]; positivity
  have hR : 0 < d/T^9 := by positivity
  have ha := analyticOnNhd_regularAxisSource.mono
    (fun w hw => (hballs σ hσ u w hw).1)
  have hh := hCauchy hR ha (fun w hw => (hballs σ hσ u w hw).2)
  have halg (X Y Z W : ℝ) : X*(Y*W^18)/(Z/W^9)^n = (X*Y/Z^n)*W^(18+9*n) := by
    simp only [div_pow,pow_add,pow_mul]
    field_simp
  exact hh.trans_eq (halg K M d T)

private theorem norm_iteratedFDeriv_real_pullback
    {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (g : D →ₗᵢ[ℝ] E) {f : E → ℂ} {x : D} (hf : AnalyticAt ℂ f (g x)) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (f ∘ g) x‖ ≤ ‖iteratedFDeriv ℂ n f (g x)‖ := by
  have hc : ContDiffAt ℂ (n : ℕ∞ω) f (g x) := hf.contDiffAt
  have hr : ContDiffAt ℝ (n : ℕ∞ω) f (g x) := hc.restrict_scalars ℝ
  obtain ⟨U,hUopen,hxU,hU⟩ := (show ContDiffWithinAt ℝ (n : ℕ∞ω) f univ (g x) from hr).contDiffOn' le_rfl (by simp)
  have hUr : ContDiffOn ℝ (n : ℕ∞ω) f U := by simpa using hU
  have hpre : IsOpen (g ⁻¹' U) := hUopen.preimage g.continuous
  have hcomp : ContDiffAt ℝ (n : ℕ∞ω) (f ∘ g) x := hr.comp x g.contDiff.contDiffAt
  have he := g.toContinuousLinearMap.iteratedFDerivWithin_comp_right hUr
    hUopen.uniqueDiffOn hpre.uniqueDiffOn hxU (i := n) le_rfl
  change iteratedFDerivWithin ℝ n (f ∘ g) (g ⁻¹' U) x =
    (iteratedFDerivWithin ℝ n f U (g x)).compContinuousLinearMap (fun _ => g.toContinuousLinearMap) at he
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hpre.uniqueDiffOn hcomp hxU,
    iteratedFDerivWithin_eq_iteratedFDeriv hUopen.uniqueDiffOn hr hxU] at he
  have hrestriction := hc.restrictScalars_iteratedFDeriv (𝕜 := ℝ)
  rw [← hrestriction] at he
  rw [he]
  exact ((iteratedFDeriv ℂ n f (g x)).restrictScalars ℝ).norm_compContinuous_linearIsometry_le
    (fun _ => g)

private def realFrequencyIsometry (m : ℕ) : (Fin m → ℝ) →ₗᵢ[ℝ] (Fin m → ℂ) where
  toFun w i := if i.val=0 then (w i : ℂ) else (w i : ℂ)*Complex.I
  map_add' a b := by ext i; split_ifs with hi <;> simp [hi,add_mul]
  map_smul' a b := by ext i; split_ifs with hi <;> simp [hi,smul_eq_mul,Complex.real_smul,mul_assoc]
  norm_map' w := by
    have he (i : Fin m) : ‖if i.val=0 then (w i : ℂ) else (w i : ℂ)*Complex.I‖=‖w i‖ := by
      split_ifs <;> simp
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      exact (he i).le.trans (norm_le_pi_norm w i)
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      rw [← he i]
      exact norm_le_pi_norm (fun j : Fin m =>
        if j.val=0 then (w j : ℂ) else (w j : ℂ)*Complex.I) i

/-- The actual real-frequency cubic source has polynomial bounds for every joint derivative,
including damping derivatives, uniformly up to damping one. -/
theorem exists_realCubicSource_derivative_polynomial_bound (n : ℕ) :
    ∃ C > 0, ∀ w : Fin 3 → ℝ, w 0 ∈ Icc (1 : ℝ) 2 →
      ‖iteratedFDeriv ℝ n (fun x : Fin 3 → ℝ => realCubicSource (x 0) (x 1) (x 2)) w‖ ≤
        C*(1+|w 1|+|w 2|)^(54+9*n) := by
  obtain ⟨C,hC,hbound⟩ := exists_regularCubicSource_derivative_polynomial_bound n
  refine ⟨C,hC,?_⟩
  intro w hw
  let g := realFrequencyIsometry 3
  let f : (Fin 3 → ℂ) → ℂ := fun z => regularCubicSource (z 0) (z 1) (z 2)
  have hg : g w = ![(w 0 : ℂ),(w 1 : ℂ)*Complex.I,(w 2 : ℂ)*Complex.I] := by
    ext i
    fin_cases i <;> simp [g,realFrequencyIsometry]
  have hmem : g w ∈ cubicRegularDomain := by
    rw [hg]
    exact closed_frequency_mem_cubicRegularDomain (by simpa using hw.1) (by simp) (by simp)
  have hh := norm_iteratedFDeriv_real_pullback g
    (analyticOnNhd_regularCubicSource (g w) hmem) n
  have heq : f ∘ g = fun x : Fin 3 → ℝ => realCubicSource (x 0) (x 1) (x 2) := by
    funext x
    simp [f,g,realFrequencyIsometry,realCubicSource]
  change ‖iteratedFDeriv ℝ n (f ∘ g) w‖ ≤ ‖iteratedFDeriv ℂ n f (g w)‖ at hh
  rw [heq,hg] at hh
  exact hh.trans (hbound (w 0) hw (w 1) (w 2))

/-- The literal real-frequency axis source has the corresponding all-order bound. -/
theorem exists_realAxisSource_derivative_polynomial_bound (n : ℕ) :
    ∃ C > 0, ∀ w : Fin 2 → ℝ, w 0 ∈ Icc (1 : ℝ) 2 →
      ‖iteratedFDeriv ℝ n (fun x : Fin 2 → ℝ => realAxisSource (x 0) (x 1)) w‖ ≤
        C*(1+|w 1|)^(18+9*n) := by
  obtain ⟨C,hC,hbound⟩ := exists_regularAxisSource_derivative_polynomial_bound n
  refine ⟨C,hC,?_⟩
  intro w hw
  let g := realFrequencyIsometry 2
  let f : (Fin 2 → ℂ) → ℂ := fun z => regularAxisSource (z 0) (z 1)
  have hg : g w = ![(w 0 : ℂ),(w 1 : ℂ)*Complex.I] := by
    ext i
    fin_cases i <;> simp [g,realFrequencyIsometry]
  have hmem : g w ∈ axisCoordinateTube := by
    rw [hg]
    change 7/8 < (w 0 : ℂ).re ∧ |((w 1 : ℂ)*Complex.I).re| < 1/16
    constructor
    · simpa using (by linarith [hw.1] : (7/8 : ℝ) < w 0)
    · norm_num
  have hh := norm_iteratedFDeriv_real_pullback g
    (analyticOnNhd_regularAxisSource (g w) hmem) n
  have heq : f ∘ g = fun x : Fin 2 → ℝ => realAxisSource (x 0) (x 1) := by
    funext x
    simp [f,g,realFrequencyIsometry,realAxisSource]
  change ‖iteratedFDeriv ℝ n (f ∘ g) w‖ ≤ ‖iteratedFDeriv ℂ n f (g w)‖ at hh
  rw [heq,hg] at hh
  exact hh.trans (hbound (w 0) hw (w 1))

end RHTower.BAGTrace
