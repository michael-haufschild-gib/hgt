import GaloisForLFunctions.RHTower.JointAncestryCompletedThetaMellinLanding
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.ResiduePromotionAnomaly

/-!
# JAS completed-theta all-grade closed Mellin chain

The actual reflection-renormalized completed theta source survives every valuation/Rees grade in
one fixed maximal singular-Mellin graph. For

\`v_r(x) = exp(r x) Phi(x)\`,

this module proves \`v_r in L2\`, exact closed-operator ladder \`M_exp v_r = v_(r+1)\`, nonvanishing
at every grade, and linear independence of the complete countable grade family in \`L2(R)\`.
Thus every finite grade packet retains full compound rank after genuine \`L2\` quotienting.

This closes the valuation-depth and finite-compound-retention half of the JAS completion burden.
It does not construct the still-missing prime-support-synchronized \`C(PrimeTorus)\` sewing and
makes no RH assumption.
-/

open Complex Real MeasureTheory Set Polynomial
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

theorem jointAncestry_thetaCuspFullSource_expWeight_memLp (r : ℕ) :
    MemLp (fun x : ℝ => ((Real.exp ((r : ℝ) * x) * thetaCuspFullSource x : ℝ) : ℂ))
      2 volume :=
  thetaCuspFullSource_expWeight_memLp r

def jointAncestryCompletedThetaGradeL2 (r : ℕ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (jointAncestry_thetaCuspFullSource_expWeight_memLp r).toLp
    (fun x : ℝ =>
      ((Real.exp ((r : ℝ) * x) * thetaCuspFullSource x : ℝ) : ℂ))

theorem jointAncestryCompletedThetaGradeL2_coeFn (r : ℕ) :
    (jointAncestryCompletedThetaGradeL2 r : ℝ → ℂ) =ᵐ[volume]
      fun x : ℝ =>
        ((Real.exp ((r : ℝ) * x) * thetaCuspFullSource x : ℝ) : ℂ) :=
  MemLp.coeFn_toLp (jointAncestry_thetaCuspFullSource_expWeight_memLp r)

/-- Grade zero is exactly the previously constructed completed-theta JAS vector, not a new
abstract representative. -/
theorem jointAncestryCompletedThetaGradeL2_zero :
    jointAncestryCompletedThetaGradeL2 0 =
      jointAncestryCompletedThetaSourceL2 := by
  apply Lp.ext
  filter_upwards [jointAncestryCompletedThetaGradeL2_coeFn 0,
    jointAncestryCompletedThetaSourceL2_coeFn] with x hgrade hsource
  rw [hgrade, hsource]
  norm_num

def jointAncestryCompletedThetaGradeDomain (r : ℕ) :
    jointAncestrySingularMellinOperator.domain :=
  ⟨jointAncestryCompletedThetaGradeL2 r, by
    change MemLp (fun x : ℝ => (Real.exp x : ℂ) *
      (jointAncestryCompletedThetaGradeL2 r : ℝ → ℂ) x) 2 volume
    refine (memLp_congr_ae ?_).mpr
      (jointAncestry_thetaCuspFullSource_expWeight_memLp (r + 1))
    filter_upwards [jointAncestryCompletedThetaGradeL2_coeFn r] with x hx
    rw [hx]
    norm_cast
    rw [← mul_assoc, ← Real.exp_add]
    congr 1
    push_cast
    ring⟩

/-- Grade-zero domain point is exactly the existing completed-theta maximal-domain landing. -/
theorem jointAncestryCompletedThetaGradeDomain_zero :
    jointAncestryCompletedThetaGradeDomain 0 =
      jointAncestryCompletedThetaSourceDomain := by
  apply Subtype.ext
  exact jointAncestryCompletedThetaGradeL2_zero

theorem jointAncestrySingularMellinOperator_completedThetaGrade
    (r : ℕ) :
    jointAncestrySingularMellinOperator
        (jointAncestryCompletedThetaGradeDomain r) =
      jointAncestryCompletedThetaGradeL2 (r + 1) := by
  apply Lp.ext
  have hop := maximalRealL2Mul_apply_ae volume Real.exp
    (jointAncestryCompletedThetaGradeDomain r)
  change (jointAncestrySingularMellinOperator
      (jointAncestryCompletedThetaGradeDomain r) : ℝ → ℂ) =ᵐ[volume]
    fun x => (Real.exp x : ℂ) *
      ((jointAncestryCompletedThetaGradeDomain r :
        Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x at hop
  have hdomain :
      ((jointAncestryCompletedThetaGradeDomain r :
        Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
        fun x : ℝ =>
          ((Real.exp ((r : ℝ) * x) * thetaCuspFullSource x : ℝ) : ℂ) :=
    jointAncestryCompletedThetaGradeL2_coeFn r
  filter_upwards [hop,
    hdomain,
    jointAncestryCompletedThetaGradeL2_coeFn (r + 1)] with x hx hr hs
  rw [hx, hr, hs]
  norm_cast
  rw [← mul_assoc, ← Real.exp_add]
  congr 1
  push_cast
  ring

private theorem jointAncestryAllGrade_eq_at_of_ae_eq_of_continuousAt
    {E : Type*} [NormedAddCommGroup E] {f g : ℝ → E} {x : ℝ}
    (hae : f =ᵐ[(volume : Measure ℝ)] g)
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    f x = g x := by
  by_contra hne
  have hnorm : ContinuousAt (fun y => ‖f y - g y‖) x := (hf.sub hg).norm
  have hxpos : 0 < ‖f x - g x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hev : {y | 0 < ‖f y - g y‖} ∈ nhds x :=
    hnorm.eventually (Ioi_mem_nhds hxpos)
  rcases mem_nhds_iff.mp hev with ⟨s, hs, hsopen, hxs⟩
  have hsub : s ⊆ {y | f y ≠ g y} := by
    intro y hy heq
    exact (norm_pos_iff.mp (hs hy)) (sub_eq_zero.mpr heq)
  have hnull : (volume : Measure ℝ) {y | f y ≠ g y} = 0 := hae
  have hsnull : (volume : Measure ℝ) s = 0 := measure_mono_null hsub hnull
  exact (hsopen.measure_ne_zero (volume : Measure ℝ) ⟨x, hxs⟩) hsnull

private theorem jointAncestryAllGrade_continuous_thetaCuspFullSource :
    Continuous thetaCuspFullSource := by
  rw [show thetaCuspFullSource = fun x =>
      thetaCuspTailDerivative 2 x - (1 / 4 : ℝ) * thetaCuspTailDerivative 0 x by
    funext x
    exact thetaCuspFullSource_eq_tail_second_sub x]
  exact (differentiable_thetaCuspTailDerivative 2).continuous.sub
    (continuous_const.mul (differentiable_thetaCuspTailDerivative 0).continuous)

theorem jointAncestryCompletedThetaGradeL2_ne_zero (r : ℕ) :
    jointAncestryCompletedThetaGradeL2 r ≠ 0 := by
  intro hzero
  have hae : (fun x : ℝ =>
      ((Real.exp ((r : ℝ) * x) * thetaCuspFullSource x : ℝ) : ℂ)) =ᵐ[volume]
      fun _ => 0 := by
    have hgrade := jointAncestryCompletedThetaGradeL2_coeFn r
    rw [hzero] at hgrade
    filter_upwards [hgrade, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx hz
    exact hx.symm.trans hz
  have hcont : Continuous (fun x : ℝ =>
      ((Real.exp ((r : ℝ) * x) * thetaCuspFullSource x : ℝ) : ℂ)) := by
    exact Complex.continuous_ofReal.comp
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        jointAncestryAllGrade_continuous_thetaCuspFullSource)
  have hat := jointAncestryAllGrade_eq_at_of_ae_eq_of_continuousAt (x := (1 : ℝ)) hae
    hcont.continuousAt continuousAt_const
  have hpos : 0 < Real.exp ((r : ℝ) * 1) * thetaCuspFullSource 1 :=
    mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_of_pos (by norm_num))
  norm_cast at hat
  exact (ne_of_gt hpos) (by simpa using hat)

def jointAncestryCompletedThetaGradeRaw (r : ℕ) (x : ℝ) : ℂ :=
  (Real.exp x : ℂ) ^ r * (thetaCuspFullSource x : ℂ)

theorem jointAncestryCompletedThetaGradeL2_coeFn_raw (r : ℕ) :
    (jointAncestryCompletedThetaGradeL2 r : ℝ → ℂ) =ᵐ[volume]
      jointAncestryCompletedThetaGradeRaw r := by
  filter_upwards [jointAncestryCompletedThetaGradeL2_coeFn r] with x hx
  rw [hx]
  unfold jointAncestryCompletedThetaGradeRaw
  norm_cast
  rw [← Real.exp_nat_mul]

theorem linearIndependent_jointAncestryCompletedThetaGradeRaw :
    LinearIndependent ℂ jointAncestryCompletedThetaGradeRaw := by
  let g : ℕ → ℂ := fun n =>
    (Real.exp (((n + 1 : ℕ) : ℝ)) : ℂ)
  have hg : Function.Injective g := by
    intro m n hmn
    have hreal : Real.exp (((m + 1 : ℕ) : ℝ)) =
        Real.exp (((n + 1 : ℕ) : ℝ)) :=
      Complex.ofReal_injective hmn
    have hcast : ((m + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) :=
      Real.exp_injective hreal
    have hnat : m + 1 = n + 1 := by exact_mod_cast hcast
    omega
  have hinf : {w : ℂ | ∃ x : ℝ,
      (Real.exp x : ℂ) = w ∧ (thetaCuspFullSource x : ℂ) ≠ 0}.Infinite := by
    refine (Set.infinite_range_of_injective hg).mono ?_
    rintro w ⟨n, rfl⟩
    refine ⟨((n + 1 : ℕ) : ℝ), rfl, ?_⟩
    exact Complex.ofReal_ne_zero.mpr
      (thetaCuspFullSource_pos_of_pos (by positivity)).ne'
  change LinearIndependent ℂ (fun j : ℕ =>
    (fun x : ℝ => (Real.exp x : ℂ) ^ j *
      (thetaCuspFullSource x : ℂ)))
  exact HTGeometry.ConstraintRelativity.linearIndependent_coordinatePowers
    (fun x : ℝ => (Real.exp x : ℂ))
    (fun x : ℝ => (thetaCuspFullSource x : ℂ)) hinf

theorem coeFn_finset_sum_smul_jointAncestryCompletedThetaGradeL2
    (s : Finset ℕ) (c : ℕ → ℂ) :
    (((∑ j ∈ s, c j • jointAncestryCompletedThetaGradeL2 j :
        Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∑ j ∈ s, c j * jointAncestryCompletedThetaGradeRaw j x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact (Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)).trans
        (Filter.Eventually.of_forall fun _ => rfl)
  | @insert j s hj ih =>
      filter_upwards [Lp.coeFn_add
          (c j • jointAncestryCompletedThetaGradeL2 j)
          (∑ k ∈ s, c k • jointAncestryCompletedThetaGradeL2 k),
        Lp.coeFn_smul (c j) (jointAncestryCompletedThetaGradeL2 j),
        jointAncestryCompletedThetaGradeL2_coeFn_raw j, ih] with
          x hadd hsmul hgrade hsum
      rw [Finset.sum_insert hj, hadd, Pi.add_apply, hsmul, Pi.smul_apply,
        smul_eq_mul, hgrade, hsum, Finset.sum_insert hj]

theorem linearIndependent_jointAncestryCompletedThetaGradeL2 :
    LinearIndependent ℂ jointAncestryCompletedThetaGradeL2 := by
  classical
  rw [linearIndependent_iff']
  intro s c hsum i hi
  have hzeroCoe :
      (((∑ j ∈ s, c j • jointAncestryCompletedThetaGradeL2 j :
          Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume]
        fun _ => 0 := by
    rw [hsum]
    exact Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)
  have hrawAE : (fun x : ℝ =>
      ∑ j ∈ s, c j * jointAncestryCompletedThetaGradeRaw j x) =ᵐ[volume]
        fun _ => 0 :=
    (coeFn_finset_sum_smul_jointAncestryCompletedThetaGradeL2 s c).symm.trans
      hzeroCoe
  have hraw : (fun x : ℝ =>
      ∑ j ∈ s, c j * jointAncestryCompletedThetaGradeRaw j x) = 0 := by
    funext x
    apply jointAncestryAllGrade_eq_at_of_ae_eq_of_continuousAt (x := x) hrawAE
    · exact (continuous_finsetSum s fun j _ =>
        continuous_const.mul
          (((Complex.continuous_ofReal.comp Real.continuous_exp).pow j).mul
            (Complex.continuous_ofReal.comp jointAncestryAllGrade_continuous_thetaCuspFullSource))).continuousAt
    · exact continuousAt_const
  have hraw' : ∑ j ∈ s, c j • jointAncestryCompletedThetaGradeRaw j = 0 := by
    funext x
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      using congrFun hraw x
  have hLI := linearIndependent_jointAncestryCompletedThetaGradeRaw
  rw [linearIndependent_iff'] at hLI
  exact hLI s c hraw' i hi

theorem linearIndependent_jointAncestryCompletedThetaGradeL2_fin (N : ℕ) :
    LinearIndependent ℂ (fun i : Fin N =>
      jointAncestryCompletedThetaGradeL2 (i : ℕ)) :=
  linearIndependent_jointAncestryCompletedThetaGradeL2.comp
    (fun i : Fin N => (i : ℕ)) Fin.val_injective

end

end RHTower
