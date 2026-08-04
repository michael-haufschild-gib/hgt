import GaloisForLFunctions.RHTower.ProlateJointEigen
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# A joint eigenfunction of the band operator and the prolate equation

The commuting theorem makes the prolate Sturm–Liouville action an operator on the `lambda`-eigenspace of
the band operator.  That eigenspace is *finite dimensional* — a compact operator acts on it as
`lambda · id`, so its closed balls are compact and Riesz's theorem applies — and the prolate action is
symmetric there, because the Sturm–Liouville flux `(1-y²) psi'` vanishes at both endpoints.  A symmetric
operator on a finite-dimensional inner-product space has an eigenvector, so:

**every band eigenvalue carries an eigenfunction that also solves the prolate differential equation** —
with no simplicity hypothesis anywhere.

That is the bridge the corpus's prolate-ODE layer needs: the conserved Wronskian, the one-turning-point
variation mechanism and the Hermite rescaling identity are statements about solutions of
`P_c psi = chi psi`, and they now apply to eigenfunctions of the actual concentration operator.
-/

noncomputable section

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set intervalIntegral

open _root_.RHTower

/-! ## Riesz: a compact scalar operator forces finite dimension -/

/-- If multiplication by a nonzero scalar is a compact operator, the space is finite dimensional. -/
theorem finiteDimensional_of_isCompactOperator_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {lam : ℝ} (hlam : lam ≠ 0)
    (h : IsCompactOperator fun x : E => lam • x) : FiniteDimensional ℝ E := by
  obtain ⟨K, hK, hmem⟩ := h
  rw [Metric.mem_nhds_iff] at hmem
  obtain ⟨δ, hδpos, hball⟩ := hmem
  have habs : 0 < |lam| := abs_pos.mpr hlam
  refine FiniteDimensional.of_isCompact_closedBall₀ (𝕜 := ℝ) (r := |lam| * (δ / 2))
    (by positivity) ?_
  refine hK.of_isClosed_subset Metric.isClosed_closedBall ?_
  intro x hx
  have hxnorm : ‖x‖ ≤ |lam| * (δ / 2) := by
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    exact hx
  have hyball : lam⁻¹ • x ∈ Metric.ball (0 : E) δ := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv]
    have h1 : |lam|⁻¹ * ‖x‖ ≤ |lam|⁻¹ * (|lam| * (δ / 2)) :=
      mul_le_mul_of_nonneg_left hxnorm (by positivity)
    have h2 : |lam|⁻¹ * (|lam| * (δ / 2)) = δ / 2 := by
      field_simp
    rw [h2] at h1
    linarith
  have hmemK := hball hyball
  have hxK : lam • (lam⁻¹ • x) ∈ K := hmemK
  rw [smul_smul, mul_inv_cancel₀ hlam, one_smul] at hxK
  exact hxK

/-! ## The band eigenspace -/

/-- The operator whose kernel is the `lambda`-eigenspace of the band operator. -/
def bandEigenCLM (c lam : ℝ) : RealIntervalL2 (-1 : ℝ) 1 →L[ℝ] RealIntervalL2 (-1 : ℝ) 1 :=
  bandOperatorL2 c - lam • ContinuousLinearMap.id ℝ (RealIntervalL2 (-1 : ℝ) 1)

/-- The `lambda`-eigenspace of the band operator. -/
def bandEigenspace (c lam : ℝ) : Submodule ℝ (RealIntervalL2 (-1 : ℝ) 1) :=
  LinearMap.ker ((bandEigenCLM c lam : RealIntervalL2 (-1 : ℝ) 1 →L[ℝ] RealIntervalL2 (-1 : ℝ) 1) :
    RealIntervalL2 (-1 : ℝ) 1 →ₗ[ℝ] RealIntervalL2 (-1 : ℝ) 1)

theorem mem_bandEigenspace_iff {c lam : ℝ} {f : RealIntervalL2 (-1 : ℝ) 1} :
    f ∈ bandEigenspace c lam ↔ bandOperatorL2 c f = lam • f := by
  rw [bandEigenspace, LinearMap.mem_ker]
  show (bandEigenCLM c lam) f = 0 ↔ _
  rw [bandEigenCLM]
  simp [sub_eq_zero]

theorem completeSpace_bandEigenspace (c lam : ℝ) : CompleteSpace (bandEigenspace c lam) := by
  have hclosed : IsClosed ((bandEigenspace c lam : Submodule ℝ (RealIntervalL2 (-1 : ℝ) 1)) :
      Set (RealIntervalL2 (-1 : ℝ) 1)) := (bandEigenCLM c lam).isClosed_ker
  exact hclosed.completeSpace_coe

/-- **The band eigenspaces are finite dimensional.**  On the eigenspace the compact band operator acts
as `lambda · id`, so Riesz's theorem applies. -/
theorem finiteDimensional_bandEigenspace {c lam : ℝ} (hlam : lam ≠ 0) :
    FiniteDimensional ℝ (bandEigenspace c lam) := by
  haveI := completeSpace_bandEigenspace c lam
  have hV : ∀ v ∈ bandEigenspace c lam,
      ((bandOperatorL2 c : RealIntervalL2 (-1 : ℝ) 1 →L[ℝ] RealIntervalL2 (-1 : ℝ) 1) :
        RealIntervalL2 (-1 : ℝ) 1 →ₗ[ℝ] RealIntervalL2 (-1 : ℝ) 1) v ∈ bandEigenspace c lam := by
    intro v hv
    have hval : bandOperatorL2 c v = lam • v := mem_bandEigenspace_iff.mp hv
    show bandOperatorL2 c v ∈ bandEigenspace c lam
    rw [hval]
    exact Submodule.smul_mem _ _ hv
  have hcomp := (isCompactOperator_bandOperatorL2 c).restrict' hV
  refine finiteDimensional_of_isCompactOperator_smul hlam ?_
  have hfun : (fun x : bandEigenspace c lam => lam • x)
      = fun x : bandEigenspace c lam =>
        ((((bandOperatorL2 c : RealIntervalL2 (-1 : ℝ) 1 →L[ℝ] RealIntervalL2 (-1 : ℝ) 1) :
          RealIntervalL2 (-1 : ℝ) 1 →ₗ[ℝ] RealIntervalL2 (-1 : ℝ) 1).restrict hV) x) := by
    funext x
    refine Subtype.ext ?_
    have hval : bandOperatorL2 c (x : RealIntervalL2 (-1 : ℝ) 1) = lam • (x : RealIntervalL2 (-1 : ℝ) 1) :=
      mem_bandEigenspace_iff.mp x.2
    simpa using hval.symm
  rw [hfun]
  exact hcomp

/-! ## Linearity of the smooth representative -/

theorem integrable_sincKernel_mul (c x : ℝ) (f : RealIntervalL2 (-1 : ℝ) 1) :
    Integrable (fun y : ClosedInterval (-1 : ℝ) 1 => sincKernelSmooth c x (y : ℝ) * (f y : ℝ))
      (volume : Measure (ClosedInterval (-1 : ℝ) 1)) := by
  have hf : Integrable (f : ClosedInterval (-1 : ℝ) 1 → ℝ)
      (volume : Measure (ClosedInterval (-1 : ℝ) 1)) := integrable_of_realIntervalL2 f
  have hcont : Continuous fun y : ClosedInterval (-1 : ℝ) 1 => sincKernelSmooth c x (y : ℝ) := by
    have h : Continuous fun y : ClosedInterval (-1 : ℝ) 1 => x - (y : ℝ) := by fun_prop
    simpa [sincKernelSmooth, Function.comp_def] using (contDiff_sincSmooth c).continuous.comp h
  refine hf.bdd_mul (c := |c| / Real.pi) hcont.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun y => ?_
  rw [Real.norm_eq_abs]
  exact abs_sincSmooth_le c (x - (y : ℝ))

theorem eigenExtension_add (c lam : ℝ) (f g : RealIntervalL2 (-1 : ℝ) 1) (x : ℝ) :
    eigenExtension c lam (f + g) x = eigenExtension c lam f x + eigenExtension c lam g x := by
  have hsum : (∫ y : ClosedInterval (-1 : ℝ) 1,
      sincKernelSmooth c x (y : ℝ) * ((f + g) y : ℝ) ∂volume)
      = (∫ y : ClosedInterval (-1 : ℝ) 1, sincKernelSmooth c x (y : ℝ) * (f y : ℝ) ∂volume)
        + ∫ y : ClosedInterval (-1 : ℝ) 1, sincKernelSmooth c x (y : ℝ) * (g y : ℝ) ∂volume := by
    rw [← MeasureTheory.integral_add (integrable_sincKernel_mul c x f)
      (integrable_sincKernel_mul c x g)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add f g] with y hy
    rw [hy]
    simp only [Pi.add_apply]
    ring
  rw [eigenExtension, eigenExtension, eigenExtension, hsum]
  ring

theorem eigenExtension_smul (c lam r : ℝ) (f : RealIntervalL2 (-1 : ℝ) 1) (x : ℝ) :
    eigenExtension c lam (r • f) x = r * eigenExtension c lam f x := by
  have hsmul : (∫ y : ClosedInterval (-1 : ℝ) 1,
      sincKernelSmooth c x (y : ℝ) * ((r • f) y : ℝ) ∂volume)
      = r * ∫ y : ClosedInterval (-1 : ℝ) 1, sincKernelSmooth c x (y : ℝ) * (f y : ℝ) ∂volume := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul r f] with y hy
    rw [hy]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [eigenExtension, eigenExtension, hsmul]
  ring

/-! ## The prolate action on smooth functions -/

theorem contDiff_prolateSLAction {c : ℝ} {Φ : ℝ → ℝ}
    (h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (prolateSLAction c Φ) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv Φ) := (contDiff_infty_iff_deriv.mp h).2
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (deriv Φ)) :=
    (contDiff_infty_iff_deriv.mp h1).2
  have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : ℝ => (1 - x ^ 2) * deriv (deriv Φ) x :=
    (contDiff_const.sub (contDiff_id.pow 2)).mul h2
  have hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : ℝ => 2 * x * deriv Φ x :=
    (contDiff_const.mul contDiff_id).mul h1
  have hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : ℝ => c ^ 2 * x ^ 2 * Φ x :=
    (contDiff_const.mul (contDiff_id.pow 2)).mul h
  exact (hA.sub hB).sub hC

theorem prolateSLAction_add {c : ℝ} {Φ Ψ : ℝ → ℝ} (h1 : Differentiable ℝ Φ)
    (h2 : Differentiable ℝ (deriv Φ)) (k1 : Differentiable ℝ Ψ) (k2 : Differentiable ℝ (deriv Ψ))
    (x : ℝ) :
    prolateSLAction c (fun y => Φ y + Ψ y) x = prolateSLAction c Φ x + prolateSLAction c Ψ x := by
  have hd1 : (deriv fun y => Φ y + Ψ y) = fun y => deriv Φ y + deriv Ψ y := by
    funext y
    exact deriv_add (h1 y) (k1 y)
  have hd2 : (deriv fun y => deriv Φ y + deriv Ψ y)
      = fun y => deriv (deriv Φ) y + deriv (deriv Ψ) y := by
    funext y
    exact deriv_add (h2 y) (k2 y)
  rw [prolateSLAction, prolateSLAction, prolateSLAction]
  simp only [hd1, hd2]
  ring

/-! ## The band class is linear on continuous test functions -/

theorem bandClass_add {Φ Ψ : ℝ → ℝ} (hΦ : Continuous Φ) (hΨ : Continuous Ψ)
    (hsum : Continuous fun x => Φ x + Ψ x) :
    bandClass (fun x => Φ x + Ψ x) hsum = bandClass Φ hΦ + bandClass Ψ hΨ := by
  rw [bandClass, bandClass, bandClass, ← map_add]
  congr 1

theorem bandClass_smul {Φ : ℝ → ℝ} (hΦ : Continuous Φ) (r : ℝ)
    (hsmul : Continuous fun x => r * Φ x) :
    bandClass (fun x => r * Φ x) hsmul = r • bandClass Φ hΦ := by
  rw [bandClass, bandClass, ← map_smul]
  congr 1

/-- Two continuous test functions with the same band class agree on the band. -/
theorem eqOn_of_bandClass_eq {Φ Ψ : ℝ → ℝ} (hΦ : Continuous Φ) (hΨ : Continuous Ψ)
    (h : bandClass Φ hΦ = bandClass Ψ hΨ) : ∀ x ∈ Icc (-1 : ℝ) 1, Φ x = Ψ x := by
  -- the difference has vanishing band energy
  have hdiff : Continuous fun x => Φ x - Ψ x := hΦ.sub hΨ
  have hsum : Continuous fun x => Φ x + (fun y => -Ψ y) x := by fun_prop
  have hneg : Continuous fun y => -Ψ y := hΨ.neg
  have hclass : bandClass (fun x => Φ x - Ψ x) hdiff = 0 := by
    have hrw : (fun x => Φ x - Ψ x) = fun x => Φ x + (fun y => -Ψ y) x := by
      funext x
      ring
    have hsub : bandClass (fun x => Φ x + (fun y => -Ψ y) x) hsum
        = bandClass Φ hΦ + bandClass (fun y => -Ψ y) hneg := bandClass_add hΦ hneg hsum
    have hnegclass : bandClass (fun y => -Ψ y) hneg = -bandClass Ψ hΨ := by
      have h1 : (fun y => -Ψ y) = fun y => (-1 : ℝ) * Ψ y := by
        funext y
        ring
      have h2 : Continuous fun y => (-1 : ℝ) * Ψ y := by fun_prop
      have h3 : bandClass (fun y => (-1 : ℝ) * Ψ y) h2 = (-1 : ℝ) • bandClass Ψ hΨ :=
        bandClass_smul hΨ (-1) h2
      have h4 : bandClass (fun y => -Ψ y) hneg = bandClass (fun y => (-1 : ℝ) * Ψ y) h2 := by
        congr 1
      rw [h4, h3]
      simp
    have : bandClass (fun x => Φ x - Ψ x) hdiff
        = bandClass Φ hΦ + bandClass (fun y => -Ψ y) hneg := by
      rw [show bandClass (fun x => Φ x - Ψ x) hdiff
          = bandClass (fun x => Φ x + (fun y => -Ψ y) x) hsum from by congr 1]
      exact hsub
    rw [this, hnegclass, h]
    simp
  have henergy : (∫ x in (-1 : ℝ)..1, (Φ x - Ψ x) ^ 2) = 0 := by
    have h1 := norm_sq_bandClass (fun x => Φ x - Ψ x) hdiff
    rw [hclass, norm_zero] at h1
    simpa using h1.symm
  -- a nonnegative continuous integrand with vanishing integral vanishes on the open band
  have hae : (fun x : ℝ => (Φ x - Ψ x) ^ 2) =ᵐ[volume.restrict (Ioc (-1 : ℝ) 1)] 0 := by
    have hint : IntegrableOn (fun x : ℝ => (Φ x - Ψ x) ^ 2) (Ioc (-1 : ℝ) 1) volume :=
      ((hdiff.pow 2).continuousOn).integrableOn_compact isCompact_Icc |>.mono_set
        Ioc_subset_Icc_self
    have h0 : (∫ x in Ioc (-1 : ℝ) 1, (Φ x - Ψ x) ^ 2) = 0 := by
      rw [← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact henergy
    exact (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hint).mp h0
  -- hence on the open band, and by continuity on the closed band
  have hIoo : ∀ x ∈ Ioo (-1 : ℝ) 1, Φ x = Ψ x := by
    intro x hx
    by_contra hne
    have hpos : 0 < (Φ x - Ψ x) ^ 2 := by
      have : Φ x - Ψ x ≠ 0 := sub_ne_zero.mpr hne
      positivity
    -- the set where the square is positive is open and null
    have hopen : IsOpen {y : ℝ | y ∈ Ioo (-1 : ℝ) 1 ∧ 0 < (Φ y - Ψ y) ^ 2} := by
      have hc : Continuous fun y : ℝ => (Φ y - Ψ y) ^ 2 := hdiff.pow 2
      exact isOpen_Ioo.inter (isOpen_lt continuous_const hc)
    have hmem : x ∈ {y : ℝ | y ∈ Ioo (-1 : ℝ) 1 ∧ 0 < (Φ y - Ψ y) ^ 2} := ⟨hx, hpos⟩
    have hnull : volume {y : ℝ | y ∈ Ioo (-1 : ℝ) 1 ∧ 0 < (Φ y - Ψ y) ^ 2} = 0 := by
      have hsub : {y : ℝ | y ∈ Ioo (-1 : ℝ) 1 ∧ 0 < (Φ y - Ψ y) ^ 2}
          ⊆ {y : ℝ | ¬ (fun x : ℝ => (Φ x - Ψ x) ^ 2) y = (0 : ℝ → ℝ) y} ∩ Ioc (-1 : ℝ) 1 := by
        intro y hy
        refine ⟨?_, Ioo_subset_Ioc_self hy.1⟩
        simp only [Set.mem_setOf_eq, Pi.zero_apply]
        exact ne_of_gt hy.2
      have hnull0 : volume ({y : ℝ | ¬ (fun x : ℝ => (Φ x - Ψ x) ^ 2) y = (0 : ℝ → ℝ) y}
          ∩ Ioc (-1 : ℝ) 1) = 0 := by
        have := MeasureTheory.ae_iff.mp hae
        rwa [Measure.restrict_apply₀'] at this
        exact measurableSet_Ioc.nullMeasurableSet
      exact measure_mono_null hsub hnull0
    have hpos' : 0 < volume {y : ℝ | y ∈ Ioo (-1 : ℝ) 1 ∧ 0 < (Φ y - Ψ y) ^ 2} :=
      hopen.measure_pos volume ⟨x, hmem⟩
    rw [hnull] at hpos'
    exact absurd hpos' (lt_irrefl 0)
  intro x hx
  have hclosure : Icc (-1 : ℝ) 1 = closure (Ioo (-1 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
  rw [hclosure] at hx
  exact (Set.EqOn.closure (fun y hy => hIoo y hy) hΦ hΨ) hx

/-! ## The prolate action as a symmetric operator on the eigenspace -/

theorem bandClass_congr {Φ Ψ : ℝ → ℝ} (hΦ : Continuous Φ) (hΨ : Continuous Ψ) (h : Φ = Ψ) :
    bandClass Φ hΦ = bandClass Ψ hΨ := by
  subst h
  rfl

theorem bandClass_zero (h : Continuous fun _ : ℝ => (0 : ℝ)) :
    bandClass (fun _ : ℝ => (0 : ℝ)) h = 0 := by
  have h0 : bandClass (fun x : ℝ => (0 : ℝ) * (0 : ℝ)) (by fun_prop)
      = (0 : ℝ) • bandClass (fun _ : ℝ => (0 : ℝ)) h := bandClass_smul h 0 (by fun_prop)
  have hfun : (fun x : ℝ => (0 : ℝ) * (0 : ℝ)) = fun _ : ℝ => (0 : ℝ) := by
    funext x
    ring
  rw [bandClass_congr _ h hfun] at h0
  simpa using h0

/-- The smooth representative of a band eigenvector. -/
def eigenRep (c lam : ℝ) (f : bandEigenspace c lam) : ℝ → ℝ :=
  eigenExtension c lam (f : RealIntervalL2 (-1 : ℝ) 1)

theorem continuous_eigenRep (c lam : ℝ) (f : bandEigenspace c lam) :
    Continuous (eigenRep c lam f) := continuous_eigenExtension c lam _

theorem contDiff_eigenRep {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0) (f : bandEigenspace c lam) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (eigenRep c lam f) :=
  contDiff_eigenExtension hc hlam (mem_bandEigenspace_iff.mp f.2)

theorem bandTransform_eigenRep {c lam : ℝ} (hlam : lam ≠ 0) (f : bandEigenspace c lam) (x : ℝ) :
    bandTransform c (eigenRep c lam f) x = lam * eigenRep c lam f x :=
  bandTransform_eigenExtension hlam (mem_bandEigenspace_iff.mp f.2) x

theorem bandClass_eigenRep {c lam : ℝ} (hlam : lam ≠ 0) (f : bandEigenspace c lam) :
    bandClass (eigenRep c lam f) (continuous_eigenRep c lam f)
      = (f : RealIntervalL2 (-1 : ℝ) 1) :=
  bandClass_eigenExtension hlam (mem_bandEigenspace_iff.mp f.2)

theorem differentiable_eigenRep {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    (f : bandEigenspace c lam) : Differentiable ℝ (eigenRep c lam f) :=
  (contDiff_infty_iff_deriv.mp (contDiff_eigenRep hc hlam f)).1

theorem differentiable_deriv_eigenRep {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    (f : bandEigenspace c lam) : Differentiable ℝ (deriv (eigenRep c lam f)) :=
  (contDiff_infty_iff_deriv.mp ((contDiff_infty_iff_deriv.mp (contDiff_eigenRep hc hlam f)).2)).1

theorem continuous_deriv2_eigenRep {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    (f : bandEigenspace c lam) : Continuous (deriv (deriv (eigenRep c lam f))) :=
  ((contDiff_infty_iff_deriv.mp
    ((contDiff_infty_iff_deriv.mp (contDiff_eigenRep hc hlam f)).2)).2).continuous

theorem continuous_prolateSLAction_eigenRep {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    (f : bandEigenspace c lam) : Continuous (prolateSLAction c (eigenRep c lam f)) :=
  (contDiff_prolateSLAction (contDiff_eigenRep hc hlam f)).continuous

/-- The prolate action of a band eigenfunction is again a band eigenfunction. -/
theorem prolate_bandClass_mem {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    (f : bandEigenspace c lam) :
    bandClass (prolateSLAction c (eigenRep c lam f))
        ((contDiff_prolateSLAction (contDiff_eigenRep hc hlam f)).continuous)
      ∈ bandEigenspace c lam := by
  have hbt : ∀ x, bandTransform c (prolateSLAction c (eigenRep c lam f)) x
      = lam * prolateSLAction c (eigenRep c lam f) x :=
    bandTransform_prolateSLAction (contDiff_eigenRep hc hlam f) (bandTransform_eigenRep hlam f)
  have hfun : bandTransform c (prolateSLAction c (eigenRep c lam f))
      = fun x => lam * prolateSLAction c (eigenRep c lam f) x := funext hbt
  have hmulcont : Continuous fun x => lam * prolateSLAction c (eigenRep c lam f) x :=
    continuous_const.mul (continuous_prolateSLAction_eigenRep hc hlam f)
  rw [mem_bandEigenspace_iff, bandOperatorL2_bandClass,
    bandClass_congr (continuous_bandTransform c
      (continuous_prolateSLAction_eigenRep hc hlam f)) hmulcont hfun,
    bandClass_smul (continuous_prolateSLAction_eigenRep hc hlam f) lam hmulcont]

/-- **The prolate action as an operator on the band eigenspace.** -/
def prolateOnEigenspace {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0) :
    bandEigenspace c lam →ₗ[ℝ] bandEigenspace c lam where
  toFun f := ⟨bandClass (prolateSLAction c (eigenRep c lam f))
      ((contDiff_prolateSLAction (contDiff_eigenRep hc hlam f)).continuous),
    prolate_bandClass_mem hc hlam f⟩
  map_add' f g := by
    refine Subtype.ext ?_
    have hrep : eigenRep c lam (f + g)
        = fun x => eigenRep c lam f x + eigenRep c lam g x := by
      funext x
      exact eigenExtension_add c lam _ _ x
    have hP : prolateSLAction c (eigenRep c lam (f + g))
        = fun x => prolateSLAction c (eigenRep c lam f) x
            + prolateSLAction c (eigenRep c lam g) x := by
      rw [hrep]
      funext x
      exact prolateSLAction_add (differentiable_eigenRep hc hlam f)
        (differentiable_deriv_eigenRep hc hlam f) (differentiable_eigenRep hc hlam g)
        (differentiable_deriv_eigenRep hc hlam g) x
    show bandClass (prolateSLAction c (eigenRep c lam (f + g))) _
        = bandClass (prolateSLAction c (eigenRep c lam f)) _
          + bandClass (prolateSLAction c (eigenRep c lam g)) _
    rw [bandClass_congr _ ((continuous_prolateSLAction_eigenRep hc hlam f).add
      (continuous_prolateSLAction_eigenRep hc hlam g)) hP]
    exact bandClass_add _ _ _
  map_smul' r f := by
    refine Subtype.ext ?_
    have hrep : eigenRep c lam (r • f) = fun x => r * eigenRep c lam f x := by
      funext x
      exact eigenExtension_smul c lam r _ x
    have hP : prolateSLAction c (eigenRep c lam (r • f))
        = fun x => r * prolateSLAction c (eigenRep c lam f) x := by
      rw [hrep]
      funext x
      exact prolateSLAction_const_mul r (differentiable_eigenRep hc hlam f)
        (differentiable_deriv_eigenRep hc hlam f) x
    show bandClass (prolateSLAction c (eigenRep c lam (r • f))) _
        = r • bandClass (prolateSLAction c (eigenRep c lam f)) _
    rw [bandClass_congr _ (continuous_const.mul
      (continuous_prolateSLAction_eigenRep hc hlam f)) hP]
    exact bandClass_smul _ _ _

/-- **The prolate action is symmetric on the band eigenspace.**  The Sturm–Liouville flux vanishes at
both endpoints, so no boundary condition is needed. -/
theorem isSymmetric_prolateOnEigenspace {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0) :
    (prolateOnEigenspace hc hlam).IsSymmetric := by
  intro f g
  have hval : ∀ h : bandEigenspace c lam,
      ((prolateOnEigenspace hc hlam h : bandEigenspace c lam) : RealIntervalL2 (-1 : ℝ) 1)
        = bandClass (prolateSLAction c (eigenRep c lam h))
            ((contDiff_prolateSLAction (contDiff_eigenRep hc hlam h)).continuous) := fun _ => rfl
  show (inner ℝ ((prolateOnEigenspace hc hlam f : bandEigenspace c lam) :
      RealIntervalL2 (-1 : ℝ) 1) ((g : bandEigenspace c lam) : RealIntervalL2 (-1 : ℝ) 1) : ℝ)
      = (inner ℝ ((f : bandEigenspace c lam) : RealIntervalL2 (-1 : ℝ) 1)
        ((prolateOnEigenspace hc hlam g : bandEigenspace c lam) : RealIntervalL2 (-1 : ℝ) 1) : ℝ)
  rw [hval f, hval g, ← bandClass_eigenRep hlam f, ← bandClass_eigenRep hlam g,
    inner_bandClass_eq, inner_bandClass_eq]
  have hsymm := _root_.RHTower.prolateSLAction_band_symmetric
    (differentiable_eigenRep hc hlam f) (differentiable_deriv_eigenRep hc hlam f)
    (continuous_deriv2_eigenRep hc hlam f) (differentiable_eigenRep hc hlam g)
    (differentiable_deriv_eigenRep hc hlam g) (continuous_deriv2_eigenRep hc hlam g) c
  have hleft : (∫ x in (-1 : ℝ)..1,
      prolateSLAction c (eigenRep c lam f) x * eigenRep c lam g x)
      = ∫ x in (-1 : ℝ)..1, eigenRep c lam g x * prolateSLAction c (eigenRep c lam f) x := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  rw [hleft, hsymm]

/-! ## The joint eigenfunction -/

/-- **Every band eigenvalue carries a joint eigenfunction.**  The prolate action is a symmetric operator
on the finite-dimensional band eigenspace, so it has an eigenvector there: a band eigenfunction that also
solves the prolate differential equation on the band. -/
theorem exists_joint_prolate_band_eigen {c lam : ℝ} (hc : 0 < c) (hlam : lam ≠ 0)
    {ψ₀ : RealIntervalL2 (-1 : ℝ) 1} (hψ₀ : bandOperatorL2 c ψ₀ = lam • ψ₀) (hne : ψ₀ ≠ 0) :
    ∃ (Φ : ℝ → ℝ) (χ : ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧ Φ ≠ 0
      ∧ (∀ x, bandTransform c Φ x = lam * Φ x)
      ∧ (∀ x ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ x = χ * Φ x) := by
  haveI hfd : FiniteDimensional ℝ (bandEigenspace c lam) := finiteDimensional_bandEigenspace hlam
  haveI hnt : Nontrivial (bandEigenspace c lam) := by
    refine nontrivial_of_ne ⟨ψ₀, mem_bandEigenspace_iff.mpr hψ₀⟩ 0 ?_
    intro h
    exact hne (congrArg Subtype.val h)
  have hsym := isSymmetric_prolateOnEigenspace hc hlam
  obtain ⟨χ, hχ⟩ : ∃ χ : ℝ, Module.End.HasEigenvalue (prolateOnEigenspace hc hlam) χ :=
    ⟨_, hsym.hasEigenvalue_iSup_of_finiteDimensional⟩
  obtain ⟨v, hmem, hvne⟩ := hχ.exists_hasEigenvector
  have hveq : prolateOnEigenspace hc hlam v = χ • v := Module.End.mem_eigenspace_iff.mp hmem
  refine ⟨eigenRep c lam v, χ, contDiff_eigenRep hc hlam v, ?_, bandTransform_eigenRep hlam v, ?_⟩
  · -- the representative is nonzero because its band class is `v`
    intro h0
    have hclass := bandClass_eigenRep hlam v
    have hzero : bandClass (eigenRep c lam v) (continuous_eigenRep c lam v) = 0 := by
      have hstep : bandClass (eigenRep c lam v) (continuous_eigenRep c lam v)
          = bandClass (fun _ : ℝ => (0 : ℝ)) continuous_const :=
        bandClass_congr _ _ h0
      rw [hstep]
      exact bandClass_zero _
    have hv0 : (v : RealIntervalL2 (-1 : ℝ) 1) = 0 := by
      rw [← hclass]
      exact hzero
    exact hvne (Subtype.ext hv0)
  · -- the eigenrelation of the symmetric operator is the prolate equation on the band
    have hmulcont : Continuous fun x => χ * eigenRep c lam v x :=
      continuous_const.mul (continuous_eigenRep c lam v)
    have hcoe : bandClass (prolateSLAction c (eigenRep c lam v))
        (continuous_prolateSLAction_eigenRep hc hlam v)
        = χ • (v : RealIntervalL2 (-1 : ℝ) 1) :=
      congrArg (fun w : bandEigenspace c lam => (w : RealIntervalL2 (-1 : ℝ) 1)) hveq
    have hsmul : χ • (v : RealIntervalL2 (-1 : ℝ) 1)
        = bandClass (fun x => χ * eigenRep c lam v x) hmulcont := by
      rw [← bandClass_eigenRep hlam v,
        bandClass_smul (continuous_eigenRep c lam v) χ hmulcont]
    rw [hsmul] at hcoe
    exact eqOn_of_bandClass_eq _ _ hcoe

end GaloisForLFunctions.RHTower

end
