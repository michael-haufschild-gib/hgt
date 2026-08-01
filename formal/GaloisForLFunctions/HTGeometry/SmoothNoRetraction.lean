import GaloisForLFunctions.HTGeometry.DeterminantPolynomialIntegral
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# No continuously differentiable retraction of a ball onto its boundary

A `C¹` map of the closed unit ball into the unit sphere cannot fix the sphere pointwise.  The proof
is the volume argument: the affine homotopy `H t x = x + t (ρ x - x)` from the identity to the
retraction is injective with positive Jacobian for small `t`, and it carries the closed ball onto
itself, so the integral of its Jacobian determinant over the ball equals the volume of the ball.
That integral is a polynomial in `t`, hence constant, so the same value appears at `t = 1`.  But at
`t = 1` the map is the retraction, whose differential is singular at every interior point because
its values lie on a sphere — so the integral vanishes, and the ball would have volume zero.

This is the analytic core of degree theory in the form the phase-carrier dimension bound needs: it
yields Brouwer's fixed point theorem and, through it, the Poincaré–Miranda theorem.
-/

open MeasureTheory Metric Set Filter

namespace GaloisForLFunctions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A map of the closed ball into the unit sphere has singular derivative at interior points. -/
theorem det_fderiv_eq_zero_of_mapsTo_sphere {ρ : E → E} {x : E}
    (hdiffx : DifferentiableAt ℝ ρ x)
    (hsphere : ∀ y ∈ closedBall (0 : E) 1, ‖ρ y‖ = 1) (hx : x ∈ ball (0 : E) 1) :
    LinearMap.det ((fderiv ℝ ρ x : E →ₗ[ℝ] E)) = 0 := by
  set A := fderiv ℝ ρ x with hA
  have hball : ball (0 : E) 1 ∈ nhds x := isOpen_ball.mem_nhds hx
  have hconst : (fun y => (inner ℝ (ρ y) (ρ y) : ℝ)) =ᶠ[nhds x] fun _ => (1 : ℝ) := by
    filter_upwards [hball] with y hy
    have h1 : ‖ρ y‖ = 1 := hsphere y (ball_subset_closedBall hy)
    rw [real_inner_self_eq_norm_sq, h1]
    norm_num
  have hdiff : HasFDerivAt ρ A x := hdiffx.hasFDerivAt
  have hinner := hdiff.inner ℝ hdiff
  have hzero : HasFDerivAt (fun y => (inner ℝ (ρ y) (ρ y) : ℝ)) (0 : E →L[ℝ] ℝ) x := by
    rw [hconst.hasFDerivAt_iff]
    exact hasFDerivAt_const _ _
  have heq := hinner.unique hzero
  have hperp : ∀ v : E, (inner ℝ (ρ x) (A v) : ℝ) = 0 := by
    intro v
    have hv := congrArg (fun L : E →L[ℝ] ℝ => L v) heq
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.prod_apply, zero_apply, fderivInnerCLM_apply] at hv
    have hsym : (inner ℝ (A v) (ρ x) : ℝ) = inner ℝ (ρ x) (A v) := real_inner_comm _ _
    linarith
  by_contra hdet
  have hker : LinearMap.ker (A : E →ₗ[ℝ] E) = ⊥ := by
    by_contra h
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
  have hinj : Function.Injective (A : E →ₗ[ℝ] E) := LinearMap.ker_eq_bot.mp hker
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective.mp hinj) (ρ x)
  have hAv : A v = ρ x := hv
  have h0 : (inner ℝ (ρ x) (ρ x) : ℝ) = 0 := by
    have hp := hperp v
    rwa [hAv] at hp
  rw [real_inner_self_eq_norm_sq, hsphere x (ball_subset_closedBall hx)] at h0
  norm_num at h0

section Main

variable [MeasurableSpace E] [BorelSpace E]

/-- **No smooth retraction of the closed unit ball onto its boundary sphere.** -/
theorem no_contDiff_retraction_closedBall (μ : Measure E) [μ.IsAddHaarMeasure] {ρ : E → E}
    {U : Set E} (hU : IsOpen U) (hBU : closedBall (0 : E) 1 ⊆ U) (hρ : ContDiffOn ℝ 1 ρ U)
    (hsphere : ∀ x ∈ closedBall (0 : E) 1, ‖ρ x‖ = 1)
    (hfix : ∀ x, ‖x‖ = 1 → ρ x = x) : False := by
  classical
  rcases subsingleton_or_nontrivial E with hsub | hnt
  · have h0 : ‖ρ (0 : E)‖ = 1 := hsphere 0 (mem_closedBall_self zero_le_one)
    have hz : ρ (0 : E) = 0 := Subsingleton.elim _ _
    rw [hz, norm_zero] at h0
    norm_num at h0
  set B : Set E := closedBall (0 : E) 1 with hBdef
  have hBcompact : IsCompact B := isCompact_closedBall _ _
  -- the difference map and its derivative
  set g : E → E := fun x => ρ x - x with hgdef
  have hg : ContDiffOn ℝ 1 g U := hρ.sub contDiffOn_id
  have hgdiff : ∀ x ∈ U, DifferentiableAt ℝ g x := fun x hx =>
    (hg.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  have hgd : ∀ x ∈ U, HasFDerivAt g (fderiv ℝ g x) x := fun x hx => (hgdiff x hx).hasFDerivAt
  set A : E → (E →L[ℝ] E) := fun x => fderiv ℝ g x with hAdef
  have hAcont : ContinuousOn A U := hg.continuousOn_fderiv_of_isOpen hU le_rfl
  set H : ℝ → E → E := fun t x => x + t • g x with hHdef
  have hHderiv : ∀ (t : ℝ), ∀ x ∈ U,
      HasFDerivAt (H t) (ContinuousLinearMap.id ℝ E + t • A x) x := by
    intro t x hx
    exact (hasFDerivAt_id x).add ((hgd x hx).const_smul t)
  -- matrix representation
  set b := Module.finBasis ℝ E with hbdef
  set M : E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun x => LinearMap.toMatrix b b ((A x : E →ₗ[ℝ] E)) with hMdef
  have hMlin : Continuous fun L : E →L[ℝ] E => LinearMap.toMatrix b b (L : E →ₗ[ℝ] E) := by
    refine continuous_matrix fun i j => ?_
    have h1 : Continuous fun L : E →L[ℝ] E => L (b j) := continuous_id.clm_apply continuous_const
    have h2 : Continuous fun y : E => b.equivFun y i :=
      (continuous_apply i).comp (LinearMap.continuous_of_finiteDimensional
        (b.equivFun : E →ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ)))
    have heq : (fun L : E →L[ℝ] E => LinearMap.toMatrix b b (L : E →ₗ[ℝ] E) i j)
        = fun L : E →L[ℝ] E => b.equivFun (L (b j)) i := by
      funext L
      simp [LinearMap.toMatrix_apply, Module.Basis.equivFun_apply]
    rw [heq]
    exact h2.comp h1
  have hMcont : ContinuousOn M B := hMlin.comp_continuousOn (hAcont.mono hBU)
  have hdetM : ∀ (t : ℝ) (x : E),
      LinearMap.det ((ContinuousLinearMap.id ℝ E + t • A x : E →L[ℝ] E) : E →ₗ[ℝ] E)
        = (1 + t • M x).det := by
    intro t x
    rw [← LinearMap.det_toMatrix b]
    congr 1
    rw [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul, map_add,
      map_smul, hMdef]
    congr 1
    exact LinearMap.toMatrix_id b
  -- uniform derivative bound on the ball
  obtain ⟨C₀, hC₀⟩ := hBcompact.exists_bound_of_continuousOn (hAcont.mono hBU)
  set C : ℝ := max C₀ 1 with hCdef
  have hC1 : (1:ℝ) ≤ C := le_max_right _ _
  have hCpos : (0:ℝ) < C := lt_of_lt_of_le zero_lt_one hC1
  have hCbound : ∀ x ∈ B, ‖A x‖ ≤ C := fun x hx => le_trans (hC₀ x hx) (le_max_left _ _)
  have hlip : LipschitzOnWith (Real.toNNReal C) g B :=
    (convex_closedBall (0:E) 1).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x hx => hgdiff x (hBU hx))
      (fun x hx => by
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal C hCpos.le]
        exact hCbound x hx)
  have hlip' : ∀ x ∈ B, ∀ y ∈ B, ‖g x - g y‖ ≤ C * ‖x - y‖ := by
    intro x hx y hy
    have h := hlip.dist_le_mul x hx y hy
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal C hCpos.le] at h
    exact h
  set ε : ℝ := 1 / (2 * C) with hεdef
  have hεpos : 0 < ε := by positivity
  have hεhalf : ε ≤ 1 / 2 := by
    rw [hεdef]
    have h2C : (2:ℝ) ≤ 2 * C := by linarith
    exact one_div_le_one_div_of_le (by norm_num) h2C
  have hεlt : ε < 1 := lt_of_le_of_lt hεhalf (by norm_num)
  have hcontH : ∀ t : ℝ, ContinuousOn (H t) U := fun t =>
    continuousOn_id.add ((hg.continuousOn).const_smul t)
  -- the key volume identity for small parameters
  have key : ∀ t : ℝ, 0 ≤ t → t ≤ ε →
      ∫ x in B, (1 + t • M x).det ∂μ = (μ B).toReal := by
    intro t ht0 htε
    have htC : t * C < 1 := by
      have : t * C ≤ ε * C := by nlinarith
      have hεC : ε * C = 1 / 2 := by
        rw [hεdef]; field_simp
      linarith [this, hεC]
    have ht1 : t ≤ 1 := le_trans htε (le_of_lt hεlt)
    -- injectivity
    have hinj : Set.InjOn (H t) B := by
      intro x hx y hy hxy
      have hsub : x - y = t • (g y - g x) := by
        have hz : (x - y) - (t • g y - t • g x) = 0 := by
          have h := hxy
          rw [hHdef] at h
          simp only at h
          rw [← sub_eq_zero] at h
          rw [← h]; abel
        rw [smul_sub]
        exact sub_eq_zero.mp hz
      have hnorm : ‖x - y‖ ≤ t * C * ‖x - y‖ := by
        have hgl : ‖g y - g x‖ ≤ C * ‖x - y‖ := by
          have h := hlip' y hy x hx
          rwa [norm_sub_rev y x] at h
        have h1 : ‖x - y‖ = t * ‖g y - g x‖ := by
          rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
        calc ‖x - y‖ = t * ‖g y - g x‖ := h1
          _ ≤ t * (C * ‖x - y‖) := mul_le_mul_of_nonneg_left hgl ht0
          _ = t * C * ‖x - y‖ := by ring
      have hz : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
      exact sub_eq_zero.mp (norm_eq_zero.mp hz)
    -- invertibility of the differential
    have hinvert : ∀ (s : ℝ), 0 ≤ s → s * C < 1 → ∀ x ∈ B,
        LinearMap.ker ((ContinuousLinearMap.id ℝ E + s • A x : E →L[ℝ] E) : E →ₗ[ℝ] E) = ⊥ := by
      intro s hs0 hsC x hx
      rw [LinearMap.ker_eq_bot']
      intro v hv
      have hv' : v + s • (A x) v = 0 := hv
      have h1 : ‖v‖ = ‖s • (A x) v‖ := by
        have hveq : v = -(s • (A x) v) := by
          rw [eq_neg_iff_add_eq_zero]; exact hv'
        conv_lhs => rw [hveq]
        rw [norm_neg]
      have h2 : ‖s • (A x) v‖ ≤ s * C * ‖v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
        calc s * ‖(A x) v‖ ≤ s * (‖A x‖ * ‖v‖) :=
              mul_le_mul_of_nonneg_left ((A x).le_opNorm v) hs0
          _ ≤ s * (C * ‖v‖) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right (hCbound x hx) (norm_nonneg v)) hs0
          _ = s * C * ‖v‖ := by ring
      have h3 : ‖v‖ ≤ s * C * ‖v‖ := by
        calc ‖v‖ = ‖s • (A x) v‖ := h1
          _ ≤ s * C * ‖v‖ := h2
      have : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
      exact norm_eq_zero.mp this
    have hdetne : ∀ (s : ℝ), 0 ≤ s → s * C < 1 → ∀ x ∈ B, (1 + s • M x).det ≠ 0 := by
      intro s hs0 hsC x hx h
      rw [← hdetM s x] at h
      exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h) (hinvert s hs0 hsC x hx)
    have hdetpos : ∀ x ∈ B, 0 < (1 + t • M x).det := by
      intro x hx
      by_contra hle
      push Not at hle
      have hdcont : ContinuousOn (fun s : ℝ => (1 + s • M x).det) (Icc 0 t) :=
        (Continuous.matrix_det (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
      have hd0 : (1 + (0:ℝ) • M x).det = 1 := by simp
      have hmem : (0:ℝ) ∈ Icc ((1 + t • M x).det) ((1 + (0:ℝ) • M x).det) := by
        constructor
        · exact hle
        · rw [hd0]; norm_num
      obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' ht0 hdcont hmem
      have hsC : s * C < 1 := by
        have : s ≤ t := hs.2
        nlinarith
      exact hdetne s hs.1 hsC x hx hs0
    -- the homotopy maps the ball into itself
    have hmaps : ∀ x ∈ B, H t x ∈ B := by
      intro x hx
      have hxn : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
      have hrn : ‖ρ x‖ = 1 := hsphere x hx
      have hrw : H t x = (1 - t) • x + t • ρ x := by
        rw [hHdef]
        simp only [hgdef]
        rw [smul_sub, sub_smul, one_smul]
        abel
      rw [mem_closedBall_zero_iff, hrw]
      calc ‖(1 - t) • x + t • ρ x‖ ≤ ‖(1 - t) • x‖ + ‖t • ρ x‖ := norm_add_le _ _
        _ = (1 - t) * ‖x‖ + t * ‖ρ x‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t), abs_of_nonneg ht0]
        _ ≤ (1 - t) * 1 + t * 1 := by
            rw [hrn]
            nlinarith
        _ = 1 := by ring
    -- the homotopy is open on the interior
    have hopen : IsOpen (H t '' (ball (0 : E) 1)) := by
      rw [isOpen_iff_mem_nhds]
      rintro y ⟨x, hxball, rfl⟩
      have hxU : x ∈ U := hBU (ball_subset_closedBall hxball)
      have hstrict : HasStrictFDerivAt (H t) (ContinuousLinearMap.id ℝ E + t • A x) x := by
        have hcda : ContDiffAt ℝ 1 (H t) x := by
          have hgat : ContDiffAt ℝ 1 g x := hg.contDiffAt (hU.mem_nhds hxU)
          exact contDiffAt_id.add (hgat.const_smul t)
        have h := hcda.hasStrictFDerivAt one_ne_zero
        rwa [(hHderiv t x hxU).fderiv] at h
      have hsurj : Function.Surjective (ContinuousLinearMap.id ℝ E + t • A x) := by
        have hker := hinvert t ht0 htC x (ball_subset_closedBall hxball)
        have hinjL : Function.Injective
            ((ContinuousLinearMap.id ℝ E + t • A x : E →L[ℝ] E) : E →ₗ[ℝ] E) :=
          LinearMap.ker_eq_bot.mp hker
        exact LinearMap.injective_iff_surjective.mp hinjL
      have hmap := hstrict.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hsurj)
      rw [← hmap]
      exact Filter.image_mem_map (isOpen_ball.mem_nhds hxball)
    have himageclosed : IsClosed (H t '' B) :=
      (hBcompact.image_of_continuousOn ((hcontH t).mono hBU)).isClosed
    have hballsub : ball (0 : E) 1 ⊆ H t '' B := by
      have hpre : IsPreconnected (ball (0 : E) 1) := (convex_ball (0 : E) 1).isPreconnected
      have hcover : ball (0 : E) 1 ⊆ (H t '' ball (0 : E) 1) ∪ (H t '' B)ᶜ := by
        intro y hy
        by_cases hmem : y ∈ H t '' B
        · left
          obtain ⟨x, hxB, hxy⟩ := hmem
          rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hxB) with hlt | heq
          · exact ⟨x, mem_ball_zero_iff.mpr hlt, hxy⟩
          · exfalso
            have hHx : H t x = x := by
              rw [hHdef]
              simp only [hgdef, hfix x heq]
              simp
            rw [hHx] at hxy
            rw [← hxy, mem_ball_zero_iff, heq] at hy
            exact lt_irrefl 1 hy
        · exact Or.inr hmem
      have hdisj : Disjoint (H t '' ball (0 : E) 1) ((H t '' B)ᶜ) := by
        rw [disjoint_compl_right_iff_subset]
        exact Set.image_mono ball_subset_closedBall
      have hne : (ball (0 : E) 1 ∩ (H t '' ball (0 : E) 1)).Nonempty := by
        refine ⟨H t 0, ?_, ⟨0, mem_ball_self one_pos, rfl⟩⟩
        have h0 : ‖ρ (0 : E)‖ = 1 := hsphere 0 (mem_closedBall_self zero_le_one)
        have hval : H t 0 = t • ρ (0 : E) := by
          rw [hHdef]
          simp [hgdef]
        rw [mem_ball_zero_iff, hval, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, h0, mul_one]
        exact lt_of_le_of_lt htε hεlt
      have hsub := hpre.subset_left_of_subset_union hopen himageclosed.isOpen_compl hdisj
        hcover hne
      exact hsub.trans (Set.image_mono ball_subset_closedBall)
    have hmeas : μ (H t '' B) = μ B := by
      refine le_antisymm (measure_mono ?_) ?_
      · rintro y ⟨x, hxB, rfl⟩
        exact hmaps x hxB
      · have hsub' : B ⊆ ball (0 : E) 1 ∪ sphere (0 : E) 1 := by
          intro x hx
          rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hx) with h | h
          · exact Or.inl (mem_ball_zero_iff.mpr h)
          · exact Or.inr (mem_sphere_zero_iff_norm.mpr h)
        calc μ B ≤ μ (ball (0 : E) 1 ∪ sphere (0 : E) 1) := measure_mono hsub'
          _ ≤ μ (ball (0 : E) 1) + μ (sphere (0 : E) 1) := measure_union_le _ _
          _ = μ (ball (0 : E) 1) := by
              rw [Measure.addHaar_sphere_of_ne_zero μ 0 one_ne_zero, add_zero]
          _ ≤ μ (H t '' B) := measure_mono hballsub
    -- change of variables
    have hcov : ∫⁻ x in B, ENNReal.ofReal |(1 + t • M x).det| ∂μ = μ (H t '' B) := by
      have h := lintegral_abs_det_fderiv_eq_addHaar_image μ measurableSet_closedBall
        (fun x hx => (hHderiv t x (hBU hx)).hasFDerivWithinAt) hinj
      rw [← h]
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [ContinuousLinearMap.det]
      rw [hdetM t x]
    have hintcont : ContinuousOn (fun x => (1 + t • M x).det) B :=
      (Continuous.matrix_det continuous_id).comp_continuousOn
        (continuousOn_const.add (hMcont.const_smul t))
    have hint : IntegrableOn (fun x => (1 + t • M x).det) B μ :=
      hintcont.integrableOn_compact hBcompact
    have hnonneg : 0 ≤ᵐ[μ.restrict B] fun x => (1 + t • M x).det :=
      ae_restrict_of_forall_mem measurableSet_closedBall fun x hx => (hdetpos x hx).le
    have habs : ∫⁻ x in B, ENNReal.ofReal |(1 + t • M x).det| ∂μ
        = ∫⁻ x in B, ENNReal.ofReal ((1 + t • M x).det) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_of_forall_mem measurableSet_closedBall
        fun x hx => hdetpos x hx] with x hx
      rw [abs_of_pos hx]
    have hofReal : ENNReal.ofReal (∫ x in B, (1 + t • M x).det ∂μ)
        = ∫⁻ x in B, ENNReal.ofReal ((1 + t • M x).det) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hint hnonneg
    have hIpos : 0 ≤ ∫ x in B, (1 + t • M x).det ∂μ := integral_nonneg_of_ae hnonneg
    have hfinal : ENNReal.ofReal (∫ x in B, (1 + t • M x).det ∂μ) = μ B := by
      rw [hofReal, ← habs, hcov, hmeas]
    calc ∫ x in B, (1 + t • M x).det ∂μ
        = (ENNReal.ofReal (∫ x in B, (1 + t • M x).det ∂μ)).toReal :=
          (ENNReal.toReal_ofReal hIpos).symm
      _ = (μ B).toReal := by rw [hfinal]
  -- the integrated determinant is a polynomial, constant on an interval, hence constant
  obtain ⟨Q, hQ⟩ := exists_polynomial_setIntegral_det_one_add_smul (μ := μ) hBcompact hMcont
  have hQconst : Q = Polynomial.C (μ B).toReal := by
    have hroot : Set.Icc (0 : ℝ) ε ⊆ {x | (Q - Polynomial.C (μ B).toReal).IsRoot x} := by
      intro s hs
      simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C]
      rw [← hQ s, key s hs.1 hs.2, sub_self]
    have hinf : {x | (Q - Polynomial.C (μ B).toReal).IsRoot x}.Infinite :=
      Set.Infinite.mono hroot (Set.Icc_infinite hεpos)
    have hz := Polynomial.eq_zero_of_infinite_isRoot _ hinf
    exact sub_eq_zero.mp hz
  have hQ1 : ∫ x in B, (1 + (1 : ℝ) • M x).det ∂μ = (μ B).toReal := by
    rw [hQ 1, hQconst, Polynomial.eval_C]
  have hH1 : H 1 = ρ := by
    funext x
    rw [hHdef]
    simp [hgdef]
  have hzero : ∀ x ∈ ball (0 : E) 1, (1 + (1 : ℝ) • M x).det = 0 := by
    intro x hx
    rw [← hdetM 1 x]
    have hxU : x ∈ U := hBU (ball_subset_closedBall hx)
    have hfd : fderiv ℝ ρ x = ContinuousLinearMap.id ℝ E + (1 : ℝ) • A x := by
      rw [← hH1]
      exact ((hHderiv 1 x hxU).fderiv)
    rw [← hfd]
    exact det_fderiv_eq_zero_of_mapsTo_sphere
      ((hρ.contDiffAt (hU.mem_nhds hxU)).differentiableAt one_ne_zero) hsphere hx
  have haeeq : B =ᵐ[μ] ball (0 : E) 1 := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · refine measure_mono_null ?_ (Measure.addHaar_sphere_of_ne_zero μ 0 one_ne_zero)
      intro x hx
      have h1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx.1
      have h2 : ¬ ‖x‖ < 1 := fun h => hx.2 (mem_ball_zero_iff.mpr h)
      exact mem_sphere_zero_iff_norm.mpr (le_antisymm h1 (not_lt.mp h2))
    · have hempty : ball (0 : E) 1 \ B = ∅ := Set.sdiff_eq_empty.mpr ball_subset_closedBall
      rw [hempty, measure_empty]
  have hzeroint : ∫ x in B, (1 + (1 : ℝ) • M x).det ∂μ = 0 := by
    rw [setIntegral_congr_set haeeq,
      setIntegral_congr_fun measurableSet_ball (fun x hx => hzero x hx)]
    simp
  rw [hzeroint] at hQ1
  have hpos : 0 < (μ B).toReal :=
    ENNReal.toReal_pos (Metric.measure_closedBall_pos μ 0 one_pos).ne'
      hBcompact.measure_lt_top.ne
  rw [← hQ1] at hpos
  exact lt_irrefl 0 hpos

end Main

end GaloisForLFunctions
