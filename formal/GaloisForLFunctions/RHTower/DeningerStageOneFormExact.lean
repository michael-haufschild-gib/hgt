import GaloisForLFunctions.RHTower.DeningerClosedOneForm
import GaloisForLFunctions.RHTower.DeningerExpCover
import GaloisForLFunctions.RHTower.DeningerFormPullback

/-!
# Closed one-forms on a character stage

A closed holomorphic one-form on a character stage differs from a combination of the logarithmic
differentials by an exact form.  The form is pulled back along the exponential covering, where the
Poincaré lemma produces a primitive; the increments of that primitive over the periods of the
covering are constants, and subtracting the linear function with those coefficients makes the
primitive periodic, hence a function on the stage.

* `deningerExpPullback` : the pullback of a stage one-form along the exponential covering.
* `deningerExpPullback_closed` : the pullback of a closed form is closed.
* `deningerExpPullback_periodic` : the pullback is periodic in each coordinate.
-/

namespace RHTower

open Complex

section ExpPullback

variable {r : ℕ}

/-- The pullback of a stage one-form along the exponential covering. -/
noncomputable def deningerExpPullback (ω : DeningerStageForm r 1) :
    (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin 1]→L[ℂ] ℂ :=
  deningerPullbackForm (deningerExpMap r) ω

theorem deningerExpMap_fderiv (w : Fin r → ℂ) :
    fderiv ℂ (deningerExpMap r) w = deningerExpDeriv w :=
  (deningerExpMap_hasFDerivAt w).fderiv

theorem deningerExpMap_analyticOnNhd : AnalyticOnNhd ℂ (deningerExpMap r) Set.univ :=
  fun w _ => deningerExpMap_analyticAt w

/-- The pullback of a holomorphic stage form along the covering is holomorphic. -/
theorem deningerExpPullback_analytic {ω : DeningerStageForm r 1}
    (hω : DeningerIsHolomorphicForm ω) :
    AnalyticOnNhd ℂ (deningerExpPullback ω) Set.univ := by
  intro w _
  refine deningerPullbackForm_analyticAt (hω _ (deningerExpMap_mem w))
    (deningerExpMap_analyticAt w) ?_
  exact (deningerExpMap_analyticOnNhd.fderiv_of_isOpen isOpen_univ) w (Set.mem_univ w)

/-- **The pullback of a closed form along the covering is closed.** -/
theorem deningerExpPullback_closed {ω : DeningerStageForm r 1}
    (hω : DeningerIsHolomorphicForm ω)
    (hclosed : ∀ z ∈ deningerStageTorus r, extDeriv ω z = 0) (w : Fin r → ℂ) :
    extDeriv (deningerExpPullback ω) w = 0 := by
  rw [deningerExpPullback, deningerPullbackForm_extDeriv
    (hω _ (deningerExpMap_mem w)).differentiableAt (deningerExpMap_analyticAt w).contDiffAt]
  show ((extDeriv ω) (deningerExpMap r w)).compContinuousLinearMap
    (fderiv ℂ (deningerExpMap r) w) = 0
  rw [hclosed _ (deningerExpMap_mem w)]
  ext v
  rfl

/-- The derivative of the covering is periodic in each coordinate. -/
theorem deningerExpDeriv_periodic (j : Fin r) (w : Fin r → ℂ) :
    deningerExpDeriv (w + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) =
      deningerExpDeriv w := by
  refine ContinuousLinearMap.ext fun u => ?_
  funext l
  show Complex.exp ((w + (2 * Real.pi * Complex.I) •
    (Pi.single j (1 : ℂ) : Fin r → ℂ)) l) * u l = Complex.exp (w l) * u l
  rw [show Complex.exp ((w + (2 * Real.pi * Complex.I) •
    (Pi.single j (1 : ℂ) : Fin r → ℂ)) l) = Complex.exp (w l) from
      congrFun (deningerExpMap_periodic j w) l]

/-- **The pullback along the covering is periodic in each coordinate.** -/
theorem deningerExpPullback_periodic (ω : DeningerStageForm r 1) (j : Fin r) (w : Fin r → ℂ) :
    deningerExpPullback ω (w + (2 * Real.pi * Complex.I) •
        (Pi.single j (1 : ℂ) : Fin r → ℂ)) = deningerExpPullback ω w := by
  show (ω (deningerExpMap r (w + (2 * Real.pi * Complex.I) •
      (Pi.single j (1 : ℂ) : Fin r → ℂ)))).compContinuousLinearMap
        (fderiv ℂ (deningerExpMap r) (w + (2 * Real.pi * Complex.I) •
          (Pi.single j (1 : ℂ) : Fin r → ℂ))) =
    (ω (deningerExpMap r w)).compContinuousLinearMap (fderiv ℂ (deningerExpMap r) w)
  rw [deningerExpMap_periodic j w, deningerExpMap_fderiv, deningerExpMap_fderiv,
    deningerExpDeriv_periodic]

end ExpPullback

section Periods

variable {r : ℕ}

/-- **The increments of a primitive over the periods of the covering are constants.** -/
theorem deningerPeriod_const {F : (Fin r → ℂ) → ℂ}
    {η : (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin 1]→L[ℂ] ℂ}
    (hF : ∀ w, HasFDerivAt F (deningerFormFunctional η w) w)
    (hper : ∀ (j : Fin r) (w : Fin r → ℂ),
      η (w + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) = η w)
    (j : Fin r) (w : Fin r → ℂ) :
    F (w + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) - F w =
      F ((2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) - F 0 := by
  set K : Fin r → ℂ := (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ) with hK
  have hshift : ∀ w : Fin r → ℂ, HasFDerivAt (fun y : Fin r → ℂ => F (y + K))
      (deningerFormFunctional η (w + K)) w := by
    intro w
    have hid : HasFDerivAt (fun y : Fin r → ℂ => y + K)
        (ContinuousLinearMap.id ℂ (Fin r → ℂ)) w := (hasFDerivAt_id w).add_const K
    have h := (hF (w + K)).comp w hid
    rw [ContinuousLinearMap.comp_id] at h
    exact h
  have hzero : ∀ w : Fin r → ℂ,
      HasFDerivAt (fun y : Fin r → ℂ => F (y + K) - F y)
        (0 : (Fin r → ℂ) →L[ℂ] ℂ) w := by
    intro w
    have h := (hshift w).sub (hF w)
    have hηeq : deningerFormFunctional η (w + K) = deningerFormFunctional η w := by
      rw [hK]
      simp only [deningerFormFunctional]
      rw [hper j w]
    rw [hηeq, sub_self] at h
    exact h
  have hconst := is_const_of_fderiv_eq_zero (f := fun y : Fin r → ℂ => F (y + K) - F y)
    (fun w => (hzero w).differentiableAt) (fun w => (hzero w).fderiv) w 0
  rw [zero_add] at hconst
  exact hconst

/-- The period coefficients of a primitive. -/
noncomputable def deningerPeriodCoeff (F : (Fin r → ℂ) → ℂ) (j : Fin r) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    (F ((2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) - F 0)

/-- The primitive corrected by the linear function of its periods. -/
noncomputable def deningerCorrectedPrimitive (F : (Fin r → ℂ) → ℂ) (w : Fin r → ℂ) : ℂ :=
  F w - ∑ j, deningerPeriodCoeff F j * w j

/-- **The corrected primitive is periodic in every coordinate**, hence descends to the stage. -/
theorem deningerCorrectedPrimitive_periodic {F : (Fin r → ℂ) → ℂ}
    {η : (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin 1]→L[ℂ] ℂ}
    (hF : ∀ w, HasFDerivAt F (deningerFormFunctional η w) w)
    (hper : ∀ (j : Fin r) (w : Fin r → ℂ),
      η (w + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) = η w)
    (j : Fin r) (w : Fin r → ℂ) :
    deningerCorrectedPrimitive F
        (w + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) =
      deningerCorrectedPrimitive F w := by
  have htwopi : (2 * Real.pi * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hsum : ∑ l, deningerPeriodCoeff F l *
      ((w + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) l) =
      (∑ l, deningerPeriodCoeff F l * w l) +
        deningerPeriodCoeff F j * (2 * Real.pi * Complex.I) := by
    have hterm : ∀ l : Fin r, deningerPeriodCoeff F l *
        ((w + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) l) =
        deningerPeriodCoeff F l * w l +
          deningerPeriodCoeff F l * ((2 * Real.pi * Complex.I) *
            (Pi.single j (1 : ℂ) : Fin r → ℂ) l) := by
      intro l
      show deningerPeriodCoeff F l * (w l + (2 * Real.pi * Complex.I) *
        (Pi.single j (1 : ℂ) : Fin r → ℂ) l) = _
      ring
    rw [Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, mul_one]
    · intro l _ hl
      rw [Pi.single_eq_of_ne hl, mul_zero, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hcoeff : deningerPeriodCoeff F j * (2 * Real.pi * Complex.I) =
      F ((2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) - F 0 := by
    rw [deningerPeriodCoeff]
    field_simp
  have hFshift := deningerPeriod_const hF hper j w
  show F (w + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) -
      ∑ l, deningerPeriodCoeff F l *
        ((w + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) l) =
    F w - ∑ l, deningerPeriodCoeff F l * w l
  rw [hsum, hcoeff]
  have hF' : F (w + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) =
      F w + (F ((2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) - F 0) := by
    rw [← hFshift]
    ring
  rw [hF']
  ring

end Periods

section Descent

variable {r : ℕ}

/-- The local branch of the logarithm at a point of the stage. -/
noncomputable def deningerLogBranch (z₀ z : Fin r → ℂ) : Fin r → ℂ :=
  fun j => Complex.log (z₀ j) + Complex.log (z j / z₀ j)

theorem deningerLogBranch_exp {z₀ : Fin r → ℂ} (hz₀ : z₀ ∈ deningerStageTorus r)
    {z : Fin r → ℂ} (hz : ∀ j, z j ≠ 0) :
    deningerExpMap r (deningerLogBranch z₀ z) = z := by
  funext j
  show Complex.exp (Complex.log (z₀ j) + Complex.log (z j / z₀ j)) = z j
  rw [Complex.exp_add, Complex.exp_log (hz₀ j), Complex.exp_log (div_ne_zero (hz j) (hz₀ j)),
    mul_comm, div_mul_eq_mul_div, mul_div_assoc, div_self (hz₀ j), mul_one]

/-- The derivative of the local branch: the inverse of the derivative of the covering. -/
noncomputable def deningerLogBranchDeriv (z₀ : Fin r → ℂ) : (Fin r → ℂ) →L[ℂ] (Fin r → ℂ) :=
  ContinuousLinearMap.pi fun j =>
    (z₀ j)⁻¹ • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j)

@[simp]
theorem deningerLogBranchDeriv_apply (z₀ u : Fin r → ℂ) (j : Fin r) :
    deningerLogBranchDeriv z₀ u j = (z₀ j)⁻¹ * u j := rfl

theorem deningerLogBranch_hasFDerivAt {z₀ : Fin r → ℂ} (hz₀ : z₀ ∈ deningerStageTorus r) :
    HasFDerivAt (deningerLogBranch z₀) (deningerLogBranchDeriv z₀) z₀ := by
  refine hasFDerivAt_pi.2 fun j => ?_
  have hone : (1 : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    norm_num
  have hproj : HasFDerivAt (fun y : Fin r → ℂ => y j)
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j) z₀ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j).hasFDerivAt
  have hdiv : HasFDerivAt (fun y : Fin r → ℂ => y j / z₀ j)
      ((z₀ j)⁻¹ • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j)) z₀ := by
    have hfun : (fun y : Fin r → ℂ => y j / z₀ j) =
        ⇑((z₀ j)⁻¹ • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j)) := by
      funext y
      show y j / z₀ j = (z₀ j)⁻¹ * y j
      rw [div_eq_inv_mul]
    rw [hfun]
    exact ((z₀ j)⁻¹ •
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j)).hasFDerivAt
  have hz : z₀ j / z₀ j = 1 := div_self (hz₀ j)
  have hlog : HasDerivAt Complex.log (z₀ j / z₀ j)⁻¹ (z₀ j / z₀ j) := by
    rw [hz]
    exact Complex.hasDerivAt_log hone
  have hcomp : HasFDerivAt (fun y : Fin r → ℂ => Complex.log (y j / z₀ j))
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) ((z₀ j / z₀ j)⁻¹)).comp
        ((z₀ j)⁻¹ • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j))) z₀ :=
    HasFDerivAt.comp (g := Complex.log) z₀ (hlog.hasFDerivAt) hdiv
  have hfinal : HasFDerivAt (fun y : Fin r → ℂ => Complex.log (y j / z₀ j))
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j).comp
        (deningerLogBranchDeriv z₀)) z₀ := by
    refine hcomp.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun u => ?_
    show ((z₀ j)⁻¹ * u j) • (z₀ j / z₀ j)⁻¹ = (z₀ j)⁻¹ * u j
    rw [hz, inv_one, smul_eq_mul, mul_one]
  exact hfinal.const_add _

/-- The functional of a combination of logarithmic differentials. -/
noncomputable def deningerDlogCombFunctional (c : Fin r → ℂ) (z : Fin r → ℂ) :
    (Fin r → ℂ) →L[ℂ] ℂ :=
  ∑ j, (c j * (z j)⁻¹) • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j)

theorem deningerDlogCombFunctional_apply (c z u : Fin r → ℂ) :
    deningerDlogCombFunctional c z u = ∑ j, c j * (z j)⁻¹ * u j := by
  rw [deningerDlogCombFunctional, sum_apply]
  exact Finset.sum_congr rfl fun j _ => rfl

/-- **A closed holomorphic one-form on a character stage is a combination of the logarithmic
differentials plus an exact form.**  This is the surjectivity half of `L ⊗ ℂ ≅ H^(1 : ℕ)` in every
dimension. -/
theorem deningerStage_closed_one_form_exact {ω : DeningerStageForm r 1}
    (hω : DeningerIsHolomorphicForm ω)
    (hclosed : ∀ z ∈ deningerStageTorus r, extDeriv ω z = 0) :
    ∃ (c : Fin r → ℂ) (h : (Fin r → ℂ) → ℂ), ∀ z ∈ deningerStageTorus r,
      HasFDerivAt h (deningerFormFunctional ω z - deningerDlogCombFunctional c z) z := by
  classical
  obtain ⟨F, hF, -⟩ := deningerExists_primitive_of_closed (deningerExpPullback_analytic hω)
    (deningerExpPullback_closed hω hclosed)
  set c : Fin r → ℂ := deningerPeriodCoeff F with hc
  set Cc : (Fin r → ℂ) →L[ℂ] ℂ :=
    ∑ j, c j • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j) with hCc
  have hlin : ∀ w : Fin r → ℂ,
      HasFDerivAt (fun y : Fin r → ℂ => ∑ j, c j * y j) Cc w := by
    intro w
    have hfun : (fun y : Fin r → ℂ => ∑ j, c j * y j) = ⇑Cc := by
      funext y
      rw [hCc, sum_apply]
      exact (Finset.sum_congr rfl fun j _ => rfl).symm
    rw [hfun]
    exact Cc.hasFDerivAt
  have hGderiv : ∀ w : Fin r → ℂ, HasFDerivAt (deningerCorrectedPrimitive F)
      (deningerFormFunctional (deningerExpPullback ω) w - Cc) w := by
    intro w
    exact (hF w).sub (hlin w)
  have hGper := deningerCorrectedPrimitive_periodic hF (deningerExpPullback_periodic ω)
  refine ⟨c, fun z => deningerCorrectedPrimitive F (fun j => Complex.log (z j)),
    fun z₀ hz₀ => ?_⟩
  -- the local branch and the eventual equality
  have hbranch := deningerLogBranch_hasFDerivAt hz₀
  have hcomp : HasFDerivAt
      (fun z : Fin r → ℂ => deningerCorrectedPrimitive F (deningerLogBranch z₀ z))
      ((deningerFormFunctional (deningerExpPullback ω) (deningerLogBranch z₀ z₀) - Cc).comp
        (deningerLogBranchDeriv z₀)) z₀ :=
    (hGderiv (deningerLogBranch z₀ z₀)).comp z₀ hbranch
  have hev : ∀ᶠ z in nhds z₀,
      deningerCorrectedPrimitive F (fun j => Complex.log (z j)) =
        deningerCorrectedPrimitive F (deningerLogBranch z₀ z) := by
    have hopen : ∀ᶠ z in nhds z₀, z ∈ deningerStageTorus r :=
      (deningerStageTorus_isOpen r).mem_nhds hz₀
    filter_upwards [hopen] with z hz
    refine deningerPeriodic_descent hGper ?_
    rw [deningerLogBranch_exp hz₀ hz]
    funext j
    exact Complex.exp_log (hz j)
  refine (hcomp.congr_of_eventuallyEq hev).congr_fderiv ?_
  -- identify the derivative
  refine ContinuousLinearMap.ext fun u => ?_
  have hexpL : deningerExpMap r (deningerLogBranch z₀ z₀) = z₀ :=
    deningerLogBranch_exp hz₀ hz₀
  have hcancel : deningerExpDeriv (deningerLogBranch z₀ z₀) (deningerLogBranchDeriv z₀ u) = u := by
    funext j
    show Complex.exp (deningerLogBranch z₀ z₀ j) * ((z₀ j)⁻¹ * u j) = u j
    have hj : Complex.exp (deningerLogBranch z₀ z₀ j) = z₀ j := congrFun hexpL j
    rw [hj, ← mul_assoc, mul_inv_cancel₀ (hz₀ j), one_mul]
  show (deningerFormFunctional (deningerExpPullback ω) (deningerLogBranch z₀ z₀) - Cc)
      (deningerLogBranchDeriv z₀ u) =
    deningerFormFunctional ω z₀ u - deningerDlogCombFunctional c z₀ u
  rw [sub_apply]
  congr 1
  · show (deningerExpPullback ω (deningerLogBranch z₀ z₀))
        (fun _ => deningerLogBranchDeriv z₀ u) = ω z₀ (fun _ => u)
    show (ω (deningerExpMap r (deningerLogBranch z₀ z₀)))
        (fun _ => fderiv ℂ (deningerExpMap r) (deningerLogBranch z₀ z₀)
          (deningerLogBranchDeriv z₀ u)) = ω z₀ (fun _ => u)
    rw [deningerExpMap_fderiv, hcancel, hexpL]
  · rw [hCc, sum_apply, deningerDlogCombFunctional_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    show c j * ((z₀ j)⁻¹ * u j) = c j * (z₀ j)⁻¹ * u j
    ring

end Descent

end RHTower
