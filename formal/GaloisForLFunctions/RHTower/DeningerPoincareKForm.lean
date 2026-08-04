import GaloisForLFunctions.RHTower.DeningerPoincareOneForm
import GaloisForLFunctions.RHTower.DeningerContractionIdentity

/-!
# The Poincaré lemma in every degree

A closed holomorphic form on a finite-dimensional complex vector space is exact, with the primitive
given by contracting against the base point along the segment to the origin.  The derivative of the
integrand splits into the contraction of the form itself and the contraction of its derivative;
antisymmetrizing turns the first into a multiple of the form and, by the contraction identity for
closed forms, the second into the derivative at the base point.  Together they are the derivative
in the segment parameter of the scaled form, so the integral telescopes.

* `deningerHomotopyKernel` : the integrand of the homotopy operator.
* `deningerHomotopyKDeriv` : its derivative in the base point.
* `deningerAlternatize_homotopyKDeriv` : antisymmetrizing the derivative of the integrand.
-/

namespace RHTower

open ContinuousAlternatingMap

section HomotopyKernel

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The integrand of the homotopy operator: the form at the scaled point, contracted against the
base point, weighted by the power of the segment parameter. -/
noncomputable def deningerHomotopyKernel (ω : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (t : ℝ) (y : E) :
    E [⋀^Fin n]→L[ℂ] ℂ :=
  ((t : ℂ) ^ n) • (ContinuousAlternatingMap.curryLeft (ω (deningerScale t y)) y)

/-- The derivative in the base point of the integrand of the homotopy operator. -/
noncomputable def deningerHomotopyKDeriv (ω : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (x : E) (t : ℝ) :
    E →L[ℂ] (E [⋀^Fin n]→L[ℂ] ℂ) :=
  ((t : ℂ) ^ n) • (ContinuousAlternatingMap.curryLeft (ω (deningerScale t x)) +
    (t : ℂ) • ((deningerContractCLM x).comp (fderiv ℂ ω (deningerScale t x))))

/-- The flipped contraction of a derivative, evaluated. -/
theorem deningerFlip_contract_eq {ω : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ} (x : E) (t : ℝ) :
    (((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℂ) (E := E) (F := ℂ)
        (n := n)).toContinuousLinearMap.comp
      ((fderiv ℂ ω (deningerScale t x)).comp (deningerScale t))).flip x) =
      (t : ℂ) • ((deningerContractCLM x).comp (fderiv ℂ ω (deningerScale t x))) := by
  refine ContinuousLinearMap.ext fun u => ?_
  show ContinuousAlternatingMap.curryLeft
      ((fderiv ℂ ω (deningerScale t x)) ((t : ℂ) • u)) x =
    (t : ℂ) • (deningerContractCLM x ((fderiv ℂ ω (deningerScale t x)) u))
  rw [map_smul]
  ext v
  show ((t : ℂ) • (fderiv ℂ ω (deningerScale t x)) u) (Fin.cons x v) =
    (t : ℂ) • ((fderiv ℂ ω (deningerScale t x)) u) (Fin.cons x v)
  rfl

/-- The integrand of the homotopy operator is differentiable in the base point. -/
theorem deningerHomotopyKernel_hasFDerivAt {ω : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ}
    (hdiff : Differentiable ℂ ω) (x : E) (t : ℝ) :
    HasFDerivAt (deningerHomotopyKernel ω t) (deningerHomotopyKDeriv ω x t) x := by
  have hω : HasFDerivAt ω (fderiv ℂ ω (deningerScale t x)) (deningerScale t x) :=
    (hdiff (deningerScale t x)).hasFDerivAt
  have hscale : HasFDerivAt (fun y : E => deningerScale t y) (deningerScale t) x :=
    (deningerScale t).hasFDerivAt
  have hcomp : HasFDerivAt (fun y : E => ω (deningerScale t y))
      ((fderiv ℂ ω (deningerScale t x)).comp (deningerScale t)) x := hω.comp x hscale
  have hcurry : HasFDerivAt (fun y : E => ContinuousAlternatingMap.curryLeft (ω (deningerScale t y)))
      ((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℂ) (E := E) (F := ℂ)
        (n := n)).toContinuousLinearMap.comp
        ((fderiv ℂ ω (deningerScale t x)).comp (deningerScale t))) x :=
    HasFDerivAt.comp (g := ⇑(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℂ) (E := E) (F := ℂ)
      (n := n)).toContinuousLinearMap) x
      ((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℂ) (E := E) (F := ℂ)
        (n := n)).toContinuousLinearMap.hasFDerivAt) hcomp
  have happ := hcurry.clm_apply (hasFDerivAt_id x)
  simp only [id_eq] at happ
  rw [ContinuousLinearMap.comp_id, deningerFlip_contract_eq] at happ
  exact happ.const_smul ((t : ℂ) ^ n)

end HomotopyKernel

section AlternatizeIdentity

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Antisymmetrizing the derivative of the integrand** of the homotopy operator: the contraction
of the form contributes a multiple of the form, and the contraction of its derivative contributes
the derivative at the base point. -/
theorem deningerAlternatize_homotopyKDeriv {ω : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ}
    (hclosed : ∀ y : E, extDeriv ω y = 0) (x : E) (t : ℝ) :
    alternatizeUncurryFin (deningerHomotopyKDeriv ω x t) =
      ((n + 1 : ℕ) • ((t : ℂ) ^ n • ω (deningerScale t x))) +
        ((t : ℂ) ^ (n + 1)) • ((fderiv ℂ ω (deningerScale t x)) x) := by
  rw [deningerHomotopyKDeriv, alternatizeUncurryFin_smul, alternatizeUncurryFin_add,
    alternatizeUncurryFin_curryLeft, alternatizeUncurryFin_smul]
  have hB : alternatizeUncurryFin (fderiv ℂ ω (deningerScale t x)) = 0 := hclosed _
  rw [deningerAlternatize_contract _ hB]
  rw [smul_add, smul_comm ((t : ℂ) ^ n) (n + 1 : ℕ), smul_smul, ← pow_succ]

end AlternatizeIdentity

section HomotopyOperator

open MeasureTheory

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
theorem deningerContractCLM_norm_le (x : E) :
    ‖deningerContractCLM (n := n) (E := E) x‖ ≤ ‖x‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x) fun A => ?_
  show ‖ContinuousAlternatingMap.curryLeft A x‖ ≤ ‖x‖ * ‖A‖
  calc ‖ContinuousAlternatingMap.curryLeft A x‖
      ≤ ‖ContinuousAlternatingMap.curryLeft A‖ * ‖x‖ :=
        (ContinuousAlternatingMap.curryLeft A).le_opNorm x
    _ = ‖A‖ * ‖x‖ := by rw [ContinuousAlternatingMap.norm_curryLeft]
    _ = ‖x‖ * ‖A‖ := mul_comm _ _

/-- **The homotopy operator in degree `n`**: the integral of the contracted form along the segment
to the origin. -/
noncomputable def deningerHomotopyOperator (ω : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (x : E) :
    E [⋀^Fin n]→L[ℂ] ℂ :=
  ∫ t in (0 : ℝ)..1, deningerHomotopyKernel ω t x

omit [FiniteDimensional ℂ E] in
theorem deningerHomotopyKernel_continuous {ω : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ}
    (hcont : Continuous ω) (x : E) :
    Continuous fun t : ℝ => deningerHomotopyKernel ω t x := by
  have hscale : Continuous fun t : ℝ => deningerScale t x := by
    show Continuous fun t : ℝ => (t : ℂ) • x
    fun_prop
  have h1 : Continuous fun t : ℝ => ω (deningerScale t x) := hcont.comp hscale
  have h2 : Continuous fun t : ℝ => deningerContractCLM (n := n) x (ω (deningerScale t x)) :=
    (deningerContractCLM (n := n) x).continuous.comp h1
  have h3 : Continuous fun t : ℝ => ((t : ℂ) ^ n) := by fun_prop
  exact h3.smul h2

omit [FiniteDimensional ℂ E] in
theorem deningerHomotopyKDeriv_continuous {ω : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ}
    (hcont : Continuous ω) (hcont' : Continuous (fderiv ℂ ω)) (x : E) :
    Continuous fun t : ℝ => deningerHomotopyKDeriv ω x t := by
  have hscale : Continuous fun t : ℝ => deningerScale t x := by
    show Continuous fun t : ℝ => (t : ℂ) • x
    fun_prop
  have h1 : Continuous fun t : ℝ =>
      ContinuousAlternatingMap.curryLeft (ω (deningerScale t x)) :=
    ((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℂ) (E := E) (F := ℂ)
      (n := n)).toContinuousLinearMap).continuous.comp (hcont.comp hscale)
  have h2 : Continuous fun t : ℝ => (fderiv ℂ ω (deningerScale t x)) := hcont'.comp hscale
  have h3 : Continuous fun t : ℝ =>
      (deningerContractCLM (n := n) x).comp (fderiv ℂ ω (deningerScale t x)) :=
    isBoundedBilinearMap_comp.continuous.comp (continuous_const.prodMk h2)
  have h4 : Continuous fun t : ℝ => ((t : ℂ) ^ n) := by fun_prop
  have h5 : Continuous fun t : ℝ => (t : ℂ) := by fun_prop
  exact h4.smul (h1.add (h5.smul h3))

/-- **The homotopy operator differentiates to the derivative of its integrand.** -/
theorem deningerHomotopyOperator_hasFDerivAt {ω : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ}
    (hdiff : Differentiable ℂ ω) (hcont' : Continuous (fderiv ℂ ω)) (w₀ : E) :
    HasFDerivAt (deningerHomotopyOperator ω)
      (∫ t in (0 : ℝ)..1, deningerHomotopyKDeriv ω w₀ t) w₀ := by
  have hcont : Continuous ω := hdiff.continuous
  have hKne : ((fun p : ℝ × E => (p.1 : ℂ) • p.2) ''
      (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall w₀ 1)).Nonempty :=
    ⟨(0 : ℂ) • w₀, ⟨(0, w₀), ⟨⟨le_refl 0, zero_le_one⟩, Metric.mem_closedBall_self zero_le_one⟩,
      by norm_num⟩⟩
  have hnorm1 : Continuous fun x : E => ‖ω x‖ := by
    have h : Continuous fun A : E [⋀^Fin (n + 1)]→L[ℂ] ℂ => ‖A‖ := by
      exact continuous_norm (E := E [⋀^Fin (n + 1)]→L[ℂ] ℂ)
    exact h.comp hcont
  have hnorm2 : Continuous fun x : E => ‖fderiv ℂ ω x‖ := by
    have h : Continuous fun A : E →L[ℂ] (E [⋀^Fin (n + 1)]→L[ℂ] ℂ) => ‖A‖ := by
      exact continuous_norm (E := E →L[ℂ] (E [⋀^Fin (n + 1)]→L[ℂ] ℂ))
    exact h.comp hcont'
  obtain ⟨p₁, -, hp₁⟩ := IsCompact.exists_isMaxOn (deningerScale_image_isCompact w₀) hKne
    (f := fun x => ‖ω x‖) (Continuous.continuousOn hnorm1)
  obtain ⟨p₂, -, hp₂⟩ := IsCompact.exists_isMaxOn (deningerScale_image_isCompact w₀) hKne
    (f := fun x => ‖fderiv ℂ ω x‖) (Continuous.continuousOn hnorm2)
  set C₁ : ℝ := ‖ω p₁‖ with hC₁def
  set C₂ : ℝ := ‖fderiv ℂ ω p₂‖ with hC₂def
  set B : ℝ := C₁ + (‖w₀‖ + 1) * C₂ with hBdef
  have hC₁nonneg : 0 ≤ C₁ := by
    rw [hC₁def]
    exact norm_nonneg _
  have hC₂nonneg : 0 ≤ C₂ := by
    rw [hC₂def]
    exact ContinuousLinearMap.opNorm_nonneg _
  have hBnonneg : 0 ≤ B := by
    have : 0 ≤ (‖w₀‖ + 1) * C₂ := mul_nonneg (by positivity) hC₂nonneg
    linarith
  have hbound : ∀ t : ℝ, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ Metric.ball w₀ 1,
      ‖deningerHomotopyKDeriv ω x t‖ ≤ B := by
    intro t ht x hx
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact ⟨le_of_lt ht.1, ht.2⟩
    have hxc : x ∈ Metric.closedBall w₀ 1 := Metric.ball_subset_closedBall hx
    have hmem := deningerScale_mem_image ht01 hxc
    have hxn : ‖x‖ ≤ ‖w₀‖ + 1 := by
      have hd : ‖x - w₀‖ ≤ 1 := by
        rw [← dist_eq_norm]
        exact Metric.mem_closedBall.1 hxc
      calc ‖x‖ ≤ ‖w₀‖ + ‖x - w₀‖ := by
            have := norm_add_le w₀ (x - w₀)
            simpa using this
        _ ≤ ‖w₀‖ + 1 := by linarith
    have htn : ‖(t : ℂ)‖ ≤ 1 := by
      simp [abs_of_nonneg ht01.1, ht01.2]
    have htpow : ‖((t : ℂ) ^ n)‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) htn
    have hω : ‖ω (deningerScale t x)‖ ≤ C₁ := hp₁ hmem
    have hω' : ‖fderiv ℂ ω (deningerScale t x)‖ ≤ C₂ := hp₂ hmem
    have hterm1 : ‖ContinuousAlternatingMap.curryLeft (ω (deningerScale t x))‖ ≤ C₁ := by
      rw [ContinuousAlternatingMap.norm_curryLeft]
      exact hω
    have hcomp : ‖(deningerContractCLM x).comp (fderiv ℂ ω (deningerScale t x))‖ ≤
        (‖w₀‖ + 1) * C₂ := by
      refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
      exact mul_le_mul (le_trans (deningerContractCLM_norm_le x) hxn) hω'
        (ContinuousLinearMap.opNorm_nonneg _) (by positivity : (0:ℝ) ≤ ‖w₀‖ + 1)
    have hterm2 : ‖(t : ℂ) • ((deningerContractCLM x).comp
        (fderiv ℂ ω (deningerScale t x)))‖ ≤ (‖w₀‖ + 1) * C₂ := by
      refine le_trans (ContinuousLinearMap.opNorm_smul_le _ _) ?_
      calc ‖(t : ℂ)‖ * ‖(deningerContractCLM x).comp (fderiv ℂ ω (deningerScale t x))‖
          ≤ 1 * ((‖w₀‖ + 1) * C₂) :=
            mul_le_mul htn hcomp (ContinuousLinearMap.opNorm_nonneg _) zero_le_one
        _ = (‖w₀‖ + 1) * C₂ := one_mul _
    have hsum : ‖ContinuousAlternatingMap.curryLeft (ω (deningerScale t x)) +
        (t : ℂ) • ((deningerContractCLM x).comp (fderiv ℂ ω (deningerScale t x)))‖ ≤ B := by
      rw [hBdef]
      exact le_trans (ContinuousLinearMap.opNorm_add_le _ _) (add_le_add hterm1 hterm2)
    rw [deningerHomotopyKDeriv]
    refine le_trans (ContinuousLinearMap.opNorm_smul_le _ _) ?_
    calc ‖((t : ℂ) ^ n)‖ * ‖ContinuousAlternatingMap.curryLeft (ω (deningerScale t x)) +
          (t : ℂ) • ((deningerContractCLM x).comp (fderiv ℂ ω (deningerScale t x)))‖
        ≤ 1 * B := mul_le_mul htpow hsum (ContinuousLinearMap.opNorm_nonneg _) zero_le_one
      _ = B := one_mul _
  haveI : TopologicalSpace.PseudoMetrizableSpace (E →L[ℂ] (E [⋀^Fin n]→L[ℂ] ℂ)) :=
    ⟨⟨PseudoMetricSpace.toUniformSpace, rfl, by
      exact EMetric.instIsCountablyGeneratedUniformity
        (α := E →L[ℂ] (E [⋀^Fin n]→L[ℂ] ℂ))⟩⟩
  refine _root_.intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun (x : E) (t : ℝ) => deningerHomotopyKernel ω t x)
    (F' := fun (x : E) (t : ℝ) => deningerHomotopyKDeriv ω x t)
    (bound := fun _ : ℝ => B)
    (Metric.ball_mem_nhds w₀ one_pos)
    (Filter.Eventually.of_forall fun x =>
      (deningerHomotopyKernel_continuous hcont x).aestronglyMeasurable)
    ((deningerHomotopyKernel_continuous hcont w₀).intervalIntegrable 0 1)
    ((deningerHomotopyKDeriv_continuous hcont hcont' w₀).aestronglyMeasurable)
    (Filter.Eventually.of_forall hbound)
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall fun t _ x _ => deningerHomotopyKernel_hasFDerivAt hdiff x t)

/-- A natural-number multiple in a complex vector space is the multiple by the cast scalar. -/
theorem deningerNsmul_eq_cast_smul {M : Type*} [AddCommGroup M] [Module ℂ M] (k : ℕ) (m : M) :
    (k : ℕ) • m = ((k : ℂ)) • m := (Nat.cast_smul_eq_nsmul ℂ k m).symm

/-- Pulling a continuous linear map out of an interval integral of a continuous function. -/
theorem deningerIntegral_comp_comm {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace X] [CompleteSpace Y]
    (L : X →L[ℂ] Y) (f : ℝ → X) (hf : Continuous f) :
    L (∫ t in (0 : ℝ)..1, f t) = ∫ t in (0 : ℝ)..1, L (f t) := by
  rw [_root_.intervalIntegral.integral_of_le zero_le_one,
    _root_.intervalIntegral.integral_of_le zero_le_one]
  exact (ContinuousLinearMap.integral_comp_comm L
    ((hf.intervalIntegrable 0 1).1)).symm

/-- **The Poincaré lemma in degree `n + 1`**: a closed holomorphic form on a finite-dimensional
complex vector space is the exterior derivative of the homotopy operator applied to it. -/
theorem deningerExtDeriv_homotopyOperator {ω : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ}
    (hdiff : Differentiable ℂ ω) (hcont' : Continuous (fderiv ℂ ω))
    (hclosed : ∀ y : E, extDeriv ω y = 0) (x : E) : extDeriv (deningerHomotopyOperator ω) x = ω x := by
  have hcont : Continuous ω := hdiff.continuous
  have hDcont : Continuous fun t : ℝ => deningerHomotopyKDeriv ω x t :=
    deningerHomotopyKDeriv_continuous hcont hcont' x
  -- the exterior derivative of the homotopy operator is the integral of the alternatized derivative
  rw [extDeriv, (deningerHomotopyOperator_hasFDerivAt hdiff hcont' x).fderiv]
  have hcomm : alternatizeUncurryFin (∫ t in (0 : ℝ)..1, deningerHomotopyKDeriv ω x t) =
      ∫ t in (0 : ℝ)..1, alternatizeUncurryFin (deningerHomotopyKDeriv ω x t) :=
    deningerIntegral_comp_comm (alternatizeUncurryFinCLM ℂ E ℂ (n := n))
      (fun t => deningerHomotopyKDeriv ω x t) hDcont
  rw [hcomm]
  -- the alternatized derivative is a total derivative in the segment parameter
  have hcast : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ((s : ℂ) ^ (n + 1)) • ω (deningerScale s x))
      (alternatizeUncurryFin (deningerHomotopyKDeriv ω x t)) t := by
    intro t
    have hpow : HasDerivAt (fun s : ℝ => ((s : ℂ) ^ (n + 1)))
        (((n : ℂ) + 1) * (t : ℂ) ^ n) t := by
      have h := (deningerRealCast_hasDerivAt t).pow (n + 1)
      rw [mul_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at h
      exact h
    have hcurve : HasDerivAt (fun s : ℝ => (s : ℂ) • x) x t := by
      have h := (deningerRealCast_hasDerivAt t).smul_const x
      rw [one_smul] at h
      exact h
    have hωt : HasDerivAt (fun s : ℝ => ω (deningerScale s x))
        ((fderiv ℂ ω (deningerScale t x)) x) t := by
      have hfd := (hdiff (deningerScale t x)).hasFDerivAt
      exact (hfd.restrictScalars ℝ).comp_hasDerivAt t hcurve
    have h := hpow.smul hωt
    rw [deningerAlternatize_homotopyKDeriv hclosed x t]
    have hmatch : ((t : ℂ) ^ (n + 1)) • ((fderiv ℂ ω (deningerScale t x)) x) +
        (((n : ℂ) + 1) * (t : ℂ) ^ n) • ω (deningerScale t x) =
        ((n + 1 : ℕ) • ((t : ℂ) ^ n • ω (deningerScale t x))) +
          ((t : ℂ) ^ (n + 1)) • ((fderiv ℂ ω (deningerScale t x)) x) := by
      have hswap : (((n : ℂ) + 1) * (t : ℂ) ^ n) • ω (deningerScale t x) =
          (n + 1 : ℕ) • ((t : ℂ) ^ n • ω (deningerScale t x)) := by
        calc (((n : ℂ) + 1) * (t : ℂ) ^ n) • ω (deningerScale t x)
            = (((n + 1 : ℕ) : ℂ)) • ((t : ℂ) ^ n • ω (deningerScale t x)) := by
              rw [smul_smul]
              norm_cast
          _ = (n + 1 : ℕ) • ((t : ℂ) ^ n • ω (deningerScale t x)) := by
              rw [deningerNsmul_eq_cast_smul]
      rw [hswap]
      exact add_comm _ _
    rw [hmatch] at h
    exact h
  have hcontint : Continuous fun t : ℝ =>
      alternatizeUncurryFin (deningerHomotopyKDeriv ω x t) :=
    (alternatizeUncurryFinCLM ℂ E ℂ (n := n)).continuous.comp hDcont
  rw [_root_.intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hcast t)
    (hcontint.intervalIntegrable 0 1)]
  have h1 : ((1 : ℝ) : ℂ) ^ (n + 1) • ω (deningerScale 1 x) = ω x := by
    have hs : deningerScale (1 : ℝ) x = x := by
      show ((1 : ℝ) : ℂ) • x = x
      norm_num
    rw [hs]
    norm_num
  have h0 : ((0 : ℝ) : ℂ) ^ (n + 1) • ω (deningerScale 0 x) = 0 := by
    rw [Complex.ofReal_zero, zero_pow (Nat.succ_ne_zero n)]
    ext v
    simp
  rw [h1, h0, sub_zero]

end HomotopyOperator

end RHTower
