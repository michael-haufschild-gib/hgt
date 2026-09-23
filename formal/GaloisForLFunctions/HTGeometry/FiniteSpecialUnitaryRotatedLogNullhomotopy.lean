import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryLocalLogNullhomotopy

/-!
# Rotated logarithm nullhomotopies in finite special-unitary groups

A scalar phase moves the branch cut of the principal unitary logarithm.  After subtracting the
scalar logarithm, exponentiation recovers the original unitary.  On a based special-unitary loop
contained in one rotated chart, determinant one and continuity force the shifted logarithmic trace
to vanish.  Radial scaling then gives an explicit endpoint-fixed nullhomotopy inside `SU(n)`.
-/

open Matrix Complex
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {iota : Type*} [Fintype iota] [DecidableEq iota]

noncomputable local instance finiteSpecialUnitaryRotatedLogNullhomotopyInst1 : CStarAlgebra (Matrix iota iota ℂ) :=
  CStarAlgebra.mk

/-- Scalar self-adjoint matrix with real value `beta`. -/
def scalarSelfAdjointMatrix (beta : ℝ) :
    selfAdjoint (Matrix iota iota ℂ) :=
  beta • (1 : selfAdjoint (Matrix iota iota ℂ))

/-- Scalar phase as a unitary matrix. -/
def scalarPhaseUnitaryMatrix (beta : ℝ) :
    Matrix.unitaryGroup iota ℂ :=
  selfAdjoint.expUnitary (scalarSelfAdjointMatrix beta)

theorem scalarPhaseUnitaryMatrix_coe (beta : ℝ) :
    (scalarPhaseUnitaryMatrix (iota := iota) beta : Matrix iota iota ℂ) =
      Complex.exp (Complex.I * beta) • (1 : Matrix iota iota ℂ) := by
  rw [scalarPhaseUnitaryMatrix, selfAdjoint.expUnitary_coe]
  have hscalar : Complex.I •
      (scalarSelfAdjointMatrix (iota := iota) beta : Matrix iota iota ℂ) =
      (Complex.I * beta : ℂ) • (1 : Matrix iota iota ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [scalarSelfAdjointMatrix]
    · simp [scalarSelfAdjointMatrix, hij]
  rw [hscalar]
  rw [show ((Complex.I * beta : ℂ) • (1 : Matrix iota iota ℂ)) =
      Matrix.diagonal (fun _ : iota ↦ Complex.I * beta) by
        ext i j
        by_cases hij : i = j
        · subst j
          simp
        · simp [hij]]
  rw [Matrix.exp_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp
    exact (congrFun Complex.exp_eq_exp_ℂ _).symm
  · simp [hij]

@[simp] theorem scalarPhaseUnitaryMatrix_zero :
    scalarPhaseUnitaryMatrix (iota := iota) 0 = 1 := by
  ext
  simp [scalarPhaseUnitaryMatrix_coe]

@[simp] theorem scalarPhaseUnitaryMatrix_neg_mul (beta : ℝ) :
    scalarPhaseUnitaryMatrix (iota := iota) (-beta) *
        scalarPhaseUnitaryMatrix beta = 1 := by
  ext j k
  simp [scalarPhaseUnitaryMatrix_coe, Complex.exp_neg]

@[simp] theorem scalarPhaseUnitaryMatrix_mul_neg (beta : ℝ) :
    scalarPhaseUnitaryMatrix (iota := iota) beta *
        scalarPhaseUnitaryMatrix (-beta) = 1 := by
  ext j k
  simp [scalarPhaseUnitaryMatrix_coe, Complex.exp_neg]

/-- Left rotation of a unitary by a central scalar phase. -/
def scalarRotateUnitary (beta : ℝ) (U : Matrix.unitaryGroup iota ℂ) :
    Matrix.unitaryGroup iota ℂ :=
  scalarPhaseUnitaryMatrix beta * U

variable [Nonempty iota]

@[simp] theorem norm_scalarSelfAdjointMatrix (beta : ℝ) :
    ‖scalarSelfAdjointMatrix (iota := iota) beta‖ = |beta| := by
  change ‖beta • (1 : selfAdjoint (Matrix iota iota ℂ))‖ = |beta|
  rw [norm_smul]
  have hone : ‖(1 : selfAdjoint (Matrix iota iota ℂ))‖ = 1 := by
    change ‖(1 : Matrix iota iota ℂ)‖ = 1
    exact norm_one
  rw [hone, Real.norm_eq_abs, mul_one]

omit [Nonempty iota] in
@[simp] theorem scalarSelfAdjointMatrix_neg (beta : ℝ) :
    scalarSelfAdjointMatrix (iota := iota) (-beta) =
      -scalarSelfAdjointMatrix beta := by
  simp [scalarSelfAdjointMatrix]

omit [Nonempty iota] in
theorem scalarPhaseUnitaryMatrix_commute (beta : ℝ)
    (U : Matrix.unitaryGroup iota ℂ) :
    Commute (scalarPhaseUnitaryMatrix (iota := iota) beta) U := by
  apply Subtype.coe_injective
  change ((scalarPhaseUnitaryMatrix (iota := iota) beta : Matrix iota iota ℂ) * U) =
    U * (scalarPhaseUnitaryMatrix (iota := iota) beta : Matrix iota iota ℂ)
  rw [scalarPhaseUnitaryMatrix_coe]
  simp

/-- Principal logarithm in a scalar-rotated chart, shifted back by the scalar logarithm. -/
def rotatedArgSelfAdjoint (beta : ℝ) (U : Matrix.unitaryGroup iota ℂ) :
    selfAdjoint (Matrix iota iota ℂ) :=
  Unitary.argSelfAdjoint (scalarRotateUnitary beta U) -
    scalarSelfAdjointMatrix beta

@[simp] theorem rotatedArgSelfAdjoint_one (beta : ℝ) (hbeta : |beta| < Real.pi) :
    rotatedArgSelfAdjoint (iota := iota) beta 1 = 0 := by
  have harg : Unitary.argSelfAdjoint
      (scalarPhaseUnitaryMatrix (iota := iota) beta) =
        scalarSelfAdjointMatrix beta := by
    apply argSelfAdjoint_expUnitary
    rw [norm_scalarSelfAdjointMatrix]
    exact hbeta
  simp [rotatedArgSelfAdjoint, scalarRotateUnitary, harg]

omit [Nonempty iota] in
theorem expUnitary_rotatedArgSelfAdjoint (beta : ℝ)
    (U : Matrix.unitaryGroup iota ℂ)
    (hU : ‖((scalarRotateUnitary beta U : Matrix iota iota ℂ) - 1)‖ < 2) :
    selfAdjoint.expUnitary (rotatedArgSelfAdjoint beta U) = U := by
  let A : selfAdjoint (Matrix iota iota ℂ) :=
    Unitary.argSelfAdjoint (scalarRotateUnitary beta U)
  let B : selfAdjoint (Matrix iota iota ℂ) :=
    scalarSelfAdjointMatrix beta
  have hB : (B : Matrix iota iota ℂ) = (beta : ℂ) • 1 := by
    ext j k
    by_cases hjk : j = k
    · subst k
      simp [B, scalarSelfAdjointMatrix]
    · simp [B, scalarSelfAdjointMatrix, hjk]
  have hAB : Commute (A : Matrix iota iota ℂ) (-(B : Matrix iota iota ℂ)) := by
    rw [hB]
    exact ((Commute.one_right (A : Matrix iota iota ℂ)).smul_right (beta : ℂ)).neg_right
  have hIAB : Commute
      (Complex.I • (A : Matrix iota iota ℂ))
      (Complex.I • (-(B : Matrix iota iota ℂ))) :=
    (hAB.smul_left Complex.I).smul_right Complex.I
  apply Subtype.ext
  change NormedSpace.exp
      (Complex.I • ((A - B : selfAdjoint (Matrix iota iota ℂ)) :
        Matrix iota iota ℂ)) = (U : Matrix iota iota ℂ)
  rw [show Complex.I • ((A - B : selfAdjoint (Matrix iota iota ℂ)) :
      Matrix iota iota ℂ) =
      Complex.I • (A : Matrix iota iota ℂ) +
        Complex.I • (-(B : Matrix iota iota ℂ)) by
          simp [sub_eq_add_neg]]
  have hradius : (NormedSpace.expSeries ℂ (Matrix iota iota ℂ)).radius = ⊤ :=
    NormedSpace.expSeries_radius_eq_top ℂ (Matrix iota iota ℂ)
  rw [NormedSpace.exp_add_of_commute_of_mem_ball hIAB
    (hradius.symm ▸ edist_lt_top _ _) (hradius.symm ▸ edist_lt_top _ _)]
  rw [show NormedSpace.exp (Complex.I • (A : Matrix iota iota ℂ)) =
      (selfAdjoint.expUnitary A : Matrix iota iota ℂ) by
        exact (selfAdjoint.expUnitary_coe A).symm]
  rw [show NormedSpace.exp (Complex.I • (-(B : Matrix iota iota ℂ))) =
      (selfAdjoint.expUnitary (-B) : Matrix iota iota ℂ) by
        exact (selfAdjoint.expUnitary_coe (-B)).symm]
  rw [show selfAdjoint.expUnitary A = scalarRotateUnitary beta U by
    exact expUnitary_argSelfAdjoint hU]
  rw [show selfAdjoint.expUnitary (-B) = scalarPhaseUnitaryMatrix (-beta) by
    simp [B, scalarPhaseUnitaryMatrix]]
  have hgroup : scalarRotateUnitary beta U * scalarPhaseUnitaryMatrix (-beta) = U := by
    simp only [scalarRotateUnitary]
    calc
      (scalarPhaseUnitaryMatrix beta * U) * scalarPhaseUnitaryMatrix (-beta) =
          scalarPhaseUnitaryMatrix beta *
            (scalarPhaseUnitaryMatrix (-beta) * U) := by
              rw [mul_assoc, (scalarPhaseUnitaryMatrix_commute (-beta) U).eq]
      _ = (scalarPhaseUnitaryMatrix beta * scalarPhaseUnitaryMatrix (-beta)) * U := by
        rw [mul_assoc]
      _ = U := by rw [scalarPhaseUnitaryMatrix_mul_neg, one_mul]
  exact congrArg Subtype.val hgroup

omit [Nonempty iota] in
theorem continuous_scalarRotateUnitary (beta : ℝ) :
    Continuous (scalarRotateUnitary (iota := iota) beta) := by
  exact continuous_const.mul continuous_id

omit [Nonempty iota] in
theorem continuous_rotatedArgSelfAdjoint_of
    {X : Type*} [TopologicalSpace X]
    (beta : ℝ) (u : X → Matrix.unitaryGroup iota ℂ)
    (hu : Continuous u)
    (hchart : ∀ x, ‖((scalarRotateUnitary beta (u x) : Matrix iota iota ℂ) - 1)‖ < 2) :
    Continuous (fun x ↦ rotatedArgSelfAdjoint beta (u x)) := by
  have hrotate : Continuous (fun x ↦ scalarRotateUnitary beta (u x)) :=
    (continuous_scalarRotateUnitary beta).comp hu
  have harg : Continuous (fun x ↦ Unitary.argSelfAdjoint
      (scalarRotateUnitary beta (u x))) := by
    apply Unitary.continuousOn_argSelfAdjoint.comp_continuous hrotate
    intro x
    simpa [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] using hchart x
  exact harg.sub continuous_const

theorem rotatedLogTrace_eq_zero_of_specialUnitaryPath
    (beta : ℝ) (hbeta : |beta| < Real.pi)
    (p : Path (1 : Matrix.specialUnitaryGroup iota ℂ) 1)
    (hp : ∀ t, ‖((scalarRotateUnitary beta (localSpecialUnitaryToUnitary (p t)) :
      Matrix iota iota ℂ) - 1)‖ < 2) :
    ∀ t, Matrix.trace
      (rotatedArgSelfAdjoint beta (localSpecialUnitaryToUnitary (p t)) :
        Matrix iota iota ℂ) = 0 := by
  let u : unitInterval → Matrix.unitaryGroup iota ℂ :=
    fun t ↦ localSpecialUnitaryToUnitary (p t)
  have hu : Continuous u := continuous_localSpecialUnitaryToUnitary.comp p.continuous
  have hlog : Continuous (fun t ↦ rotatedArgSelfAdjoint beta (u t)) :=
    continuous_rotatedArgSelfAdjoint_of beta u hu (by simpa only [u] using hp)
  let f : unitInterval → ℝ := fun t ↦
    (Matrix.trace (rotatedArgSelfAdjoint beta (u t) : Matrix iota iota ℂ)).re
  have hf : Continuous f := by
    unfold f
    apply Complex.continuous_re.comp
    unfold Matrix.trace
    apply continuous_finsetSum
    intro j hj
    exact (continuous_apply j).comp ((continuous_apply j).comp
      (continuous_subtype_val.comp hlog))
  have hzero : f 0 = 0 := by
    have hu0 : u 0 = 1 := by
      apply Subtype.ext
      simp [u, localSpecialUnitaryToUnitary]
    simp only [f]
    rw [hu0, rotatedArgSelfAdjoint_one beta hbeta]
    simp
  have hdisc : ∀ t, ∃ n : ℤ, f t = (n : ℝ) * (2 * Real.pi) := by
    intro t
    let H : selfAdjoint (Matrix iota iota ℂ) :=
      rotatedArgSelfAdjoint beta (u t)
    have hHerm : (H : Matrix iota iota ℂ).IsHermitian := H.2
    have him : (Matrix.trace (H : Matrix iota iota ℂ)).im = 0 := by
      rw [isHermitian_trace_eq_sum_eigenvalues hHerm]
      simp
    have hdet : ((u t : Matrix iota iota ℂ).det) = 1 := by
      exact (Matrix.mem_specialUnitaryGroup_iff.mp (p t).2).2
    have hexpOne : Complex.exp
        (Complex.I * Matrix.trace (H : Matrix iota iota ℂ)) = 1 := by
      rw [← det_expUnitary_eq_exp_I_mul_trace H]
      rw [show selfAdjoint.expUnitary H = u t from
        expUnitary_rotatedArgSelfAdjoint beta (u t) (by simpa only [u] using hp t)]
      exact hdet
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexpOne
    refine ⟨n, ?_⟩
    have hnim := congrArg Complex.im hn
    change (Matrix.trace (H : Matrix iota iota ℂ)).re =
      (n : ℝ) * (2 * Real.pi)
    simpa [him] using hnim
  have hreal : ∀ t, f t = 0 :=
    continuous_eq_zero_of_eq_int_mul 0 f hf hzero (2 * Real.pi)
      (mul_pos (by norm_num) Real.pi_pos) hdisc
  intro t
  let H : selfAdjoint (Matrix iota iota ℂ) :=
    rotatedArgSelfAdjoint beta (u t)
  have hHerm : (H : Matrix iota iota ℂ).IsHermitian := H.2
  have him : (Matrix.trace (H : Matrix iota iota ℂ)).im = 0 := by
    rw [isHermitian_trace_eq_sum_eigenvalues hHerm]
    simp
  change Matrix.trace (H : Matrix iota iota ℂ) = 0
  apply Complex.ext
  · simpa [f, H, u] using hreal t
  · exact him

/-- Endpoint-fixed contraction of a based special-unitary loop in one rotated log chart. -/
def finiteSpecialUnitaryRotatedLogHomotopy
    (beta : ℝ) (hbeta : |beta| < Real.pi)
    (p : Path (1 : Matrix.specialUnitaryGroup iota ℂ) 1)
    (hp : ∀ t, ‖((scalarRotateUnitary beta (localSpecialUnitaryToUnitary (p t)) :
      Matrix iota iota ℂ) - 1)‖ < 2) :
    p.Homotopy (Path.refl 1) := by
  have htrace := rotatedLogTrace_eq_zero_of_specialUnitaryPath beta hbeta p hp
  let u : unitInterval → Matrix.unitaryGroup iota ℂ :=
    fun t ↦ localSpecialUnitaryToUnitary (p t)
  have hu : Continuous u := continuous_localSpecialUnitaryToUnitary.comp p.continuous
  have hlog : Continuous (fun t ↦ rotatedArgSelfAdjoint beta (u t)) :=
    continuous_rotatedArgSelfAdjoint_of beta u hu (by simpa only [u] using hp)
  let Hmap : C(unitInterval × unitInterval,
      Matrix.specialUnitaryGroup iota ℂ) :=
    ⟨fun st ↦
      ⟨selfAdjoint.expUnitary
          ((1 - (st.1 : ℝ)) • rotatedArgSelfAdjoint beta (u st.2)), by
        rw [Matrix.mem_specialUnitaryGroup_iff]
        constructor
        · exact (selfAdjoint.expUnitary _).2
        · rw [det_expUnitary_eq_exp_I_mul_trace]
          have hz : Matrix.trace
              (((1 - (st.1 : ℝ)) • rotatedArgSelfAdjoint beta (u st.2) :
                selfAdjoint (Matrix iota iota ℂ)) : Matrix iota iota ℂ) = 0 := by
            have ht : Matrix.trace
                (rotatedArgSelfAdjoint beta (u st.2) : Matrix iota iota ℂ) = 0 := by
              simpa only [u] using htrace st.2
            rw [selfAdjoint.val_smul, Matrix.trace_smul]
            rw [ht, smul_zero]
          rw [hz]
          simp⟩, by
      apply continuous_induced_rng.2
      change Continuous (fun st : unitInterval × unitInterval ↦
        (selfAdjoint.expUnitary
          ((1 - (st.1 : ℝ)) • rotatedArgSelfAdjoint beta (u st.2)) :
            Matrix iota iota ℂ))
      apply continuous_subtype_val.comp
      apply selfAdjoint.continuous_expUnitary.comp
      exact (by fun_prop : Continuous (fun st : unitInterval × unitInterval ↦
        (1 - (st.1 : ℝ)))).smul (hlog.comp continuous_snd)⟩
  refine
    { toContinuousMap := Hmap
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · intro t
    apply Subtype.ext
    dsimp [Hmap]
    simp only [sub_zero, one_smul]
    change (selfAdjoint.expUnitary (rotatedArgSelfAdjoint beta (u t)) :
      Matrix iota iota ℂ) = (u t : Matrix iota iota ℂ)
    exact congrArg Subtype.val
      (expUnitary_rotatedArgSelfAdjoint beta (u t) (by simpa only [u] using hp t))
  · intro t
    apply Subtype.ext
    simp [Hmap]
  · intro t x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · apply Subtype.ext
      have hu0 : u 0 = 1 := by
        apply Subtype.ext
        simp [u, localSpecialUnitaryToUnitary]
      simp [Hmap, hu0, rotatedArgSelfAdjoint_one beta hbeta]
    · apply Subtype.ext
      have hu1 : u 1 = 1 := by
        apply Subtype.ext
        simp [u, localSpecialUnitaryToUnitary]
      simp [Hmap, hu1, rotatedArgSelfAdjoint_one beta hbeta]

theorem finiteSpecialUnitaryRotatedLog_nullhomotopic
    (beta : ℝ) (hbeta : |beta| < Real.pi)
    (p : Path (1 : Matrix.specialUnitaryGroup iota ℂ) 1)
    (hp : ∀ t, ‖((scalarRotateUnitary beta (localSpecialUnitaryToUnitary (p t)) :
      Matrix iota iota ℂ) - 1)‖ < 2) :
    p.Homotopic (Path.refl 1) :=
  ⟨finiteSpecialUnitaryRotatedLogHomotopy beta hbeta p hp⟩

end

end GaloisForLFunctions.HTGeometry
