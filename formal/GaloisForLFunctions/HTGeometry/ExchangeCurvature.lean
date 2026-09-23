import GaloisForLFunctions.HTGeometry.FriedrichsAngle

/-!
# Exchange curvature is independent of joint exactness

The **exchange curvature** of two observers is the commutator `Ω = [P_U, P_V]` of their
exactification projectors.  It records order dependence of sequential exactification and is
independent of the incidence datum `U ⊓ V`:

* `exchangeCurvature_incidence_independent` : all four combinations of vanishing or nonvanishing
  curvature with trivial or nontrivial joint sector occur, already in finite dimension;
* `norm_exchangeCurvature_planeLines` : for two lines at angle `θ` in the plane the curvature norm
  is `|sin θ cos θ|`, while `friedrichsCosine_planeLines` computes the Friedrichs cosine as
  `|cos θ|`.  The angles `θ` and `π/2 − θ` have equal curvature norms and, unless `θ = π/4`,
  different uncertainty constants `1 − |cos θ|`.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The **exchange curvature** `[P_U, P_V]` of two observer sectors. -/
noncomputable def exchangeCurvature (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : H →L[𝕜] H :=
  U.starProjection ∘L V.starProjection - V.starProjection ∘L U.starProjection

/-- The exchange curvature of two lines spanned by unit vectors. -/
theorem exchangeCurvature_line_apply {p q : H} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (w : H) :
    exchangeCurvature (𝕜 ∙ p) (𝕜 ∙ q) w
      = ⟪q, w⟫_𝕜 • (⟪p, q⟫_𝕜 • p) - ⟪p, w⟫_𝕜 • (⟪q, p⟫_𝕜 • q) := by
  rw [exchangeCurvature]
  simp only [sub_apply, ContinuousLinearMap.comp_apply]
  rw [Submodule.starProjection_unit_singleton 𝕜 hq w,
    Submodule.starProjection_unit_singleton 𝕜 hp w,
    map_smul, map_smul,
    Submodule.starProjection_unit_singleton 𝕜 hp q,
    Submodule.starProjection_unit_singleton 𝕜 hq p]

/-- Orthogonal lines have vanishing exchange curvature. -/
theorem exchangeCurvature_line_eq_zero {p q : H} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : ⟪p, q⟫_𝕜 = 0) :
    exchangeCurvature (𝕜 ∙ p) (𝕜 ∙ q) = 0 := by
  ext w
  have hqp : ⟪q, p⟫_𝕜 = 0 := by rw [← inner_conj_symm, hpq, map_zero]
  rw [exchangeCurvature_line_apply hp hq w, hpq, hqp]
  simp

section RealLines

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Two nonorthogonal, nonparallel lines have nonvanishing exchange curvature. -/
theorem exchangeCurvature_line_ne_zero {p q : E} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hc : ⟪p, q⟫_ℝ ≠ 0) (hpar : ⟪p, q⟫_ℝ • p ≠ q) :
    exchangeCurvature (ℝ ∙ p) (ℝ ∙ q) ≠ 0 := by
  intro hzero
  have happ : exchangeCurvature (ℝ ∙ p) (ℝ ∙ q) p
      = ⟪p, q⟫_ℝ • (⟪p, q⟫_ℝ • p - q) := by
    have h1 : ⟪p, p⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hp]; norm_num
    rw [exchangeCurvature_line_apply hp hq p, real_inner_comm q p, h1, one_smul, smul_sub]
  rw [hzero] at happ
  have : (⟪p, q⟫_ℝ • (⟪p, q⟫_ℝ • p - q)) = 0 := happ.symm
  exact (smul_ne_zero hc (sub_ne_zero.mpr hpar)) this

end RealLines

/-! ## The planar model -/

/-- The unit vector of the plane at angle `θ`. -/
noncomputable def planeUnit (θ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![Real.cos θ, Real.sin θ]

@[simp] theorem planeUnit_apply_zero (θ : ℝ) : planeUnit θ 0 = Real.cos θ := rfl

@[simp] theorem planeUnit_apply_one (θ : ℝ) : planeUnit θ 1 = Real.sin θ := rfl

theorem norm_planeUnit (θ : ℝ) : ‖planeUnit θ‖ = 1 := by
  have hsq : ‖planeUnit θ‖ ^ (2 : ℕ) = 1 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, planeUnit_apply_zero, planeUnit_apply_one,
      Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, Real.cos_sq_add_sin_sq]
  have hnn : 0 ≤ ‖planeUnit θ‖ := norm_nonneg _
  nlinarith

theorem inner_planeUnit_left (θ : ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    ⟪planeUnit θ, w⟫_ℝ = Real.cos θ * w 0 + Real.sin θ * w 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [planeUnit_apply_zero, planeUnit_apply_one, RCLike.inner_apply,
    starRingEnd_apply, star_trivial]
  ring

theorem inner_planeUnit (α β : ℝ) :
    ⟪planeUnit α, planeUnit β⟫_ℝ = Real.cos (α - β) := by
  rw [inner_planeUnit_left, planeUnit_apply_zero, planeUnit_apply_one, Real.cos_sub]

theorem inner_planeUnit_zero (θ : ℝ) : ⟪planeUnit 0, planeUnit θ⟫_ℝ = Real.cos θ := by
  rw [inner_planeUnit, zero_sub, Real.cos_neg]

theorem exchangeCurvature_planeUnit_apply (θ : ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    exchangeCurvature (ℝ ∙ planeUnit 0) (ℝ ∙ planeUnit θ) w
      = (Real.cos θ * Real.sin θ) •
          (WithLp.toLp 2 ![w 1, -w 0] : EuclideanSpace ℝ (Fin 2)) := by
  have hp : ‖planeUnit 0‖ = 1 := norm_planeUnit 0
  have hq : ‖planeUnit θ‖ = 1 := norm_planeUnit θ
  have hpq : ⟪planeUnit 0, planeUnit θ⟫_ℝ = Real.cos θ := inner_planeUnit_zero θ
  have hqp : ⟪planeUnit θ, planeUnit 0⟫_ℝ = Real.cos θ := by
    rw [inner_planeUnit, sub_zero]
  have hpw : ⟪planeUnit 0, w⟫_ℝ = w 0 := by
    rw [inner_planeUnit_left]
    simp
  have hqw : ⟪planeUnit θ, w⟫_ℝ = Real.cos θ * w 0 + Real.sin θ * w 1 :=
    inner_planeUnit_left θ w
  rw [exchangeCurvature_line_apply hp hq w, hpq, hqp, hpw, hqw]
  ext i
  fin_cases i <;> simp [planeUnit] <;> ring

theorem norm_toLp_swap (w : EuclideanSpace ℝ (Fin 2)) :
    ‖(WithLp.toLp 2 ![w 1, -w 0] : EuclideanSpace ℝ (Fin 2))‖ = ‖w‖ := by
  have hsq : ‖(WithLp.toLp 2 ![w 1, -w 0] : EuclideanSpace ℝ (Fin 2))‖ ^ (2 : ℕ) = ‖w‖ ^ (2 : ℕ) := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs, sq_abs, neg_sq]
    ring
  have h1 : (0 : ℝ) ≤ ‖(WithLp.toLp 2 ![w 1, -w 0] : EuclideanSpace ℝ (Fin 2))‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
  nlinarith

/-- **The planar exchange curvature norm.**  Two lines at angle `θ` have commutator norm
`|sin θ cos θ|`. -/
theorem norm_exchangeCurvature_planeLines (θ : ℝ) :
    ‖exchangeCurvature (ℝ ∙ planeUnit 0) (ℝ ∙ planeUnit θ)‖ = |Real.sin θ * Real.cos θ| := by
  have hpoint : ∀ w : EuclideanSpace ℝ (Fin 2),
      ‖exchangeCurvature (ℝ ∙ planeUnit 0) (ℝ ∙ planeUnit θ) w‖
        = |Real.sin θ * Real.cos θ| * ‖w‖ := by
    intro w
    rw [exchangeCurvature_planeUnit_apply, norm_smul, norm_toLp_swap, Real.norm_eq_abs,
      mul_comm (Real.cos θ) (Real.sin θ)]
  refine le_antisymm ?_ ?_
  · exact ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _) fun w => le_of_eq (hpoint w)
  · have hle := (exchangeCurvature (ℝ ∙ planeUnit 0) (ℝ ∙ planeUnit θ)).le_opNorm (planeUnit 0)
    rw [hpoint (planeUnit 0), norm_planeUnit, mul_one, mul_one] at hle
    exact hle

/-- Two planar lines at a nonzero angle meet only in the origin. -/
theorem planeLines_inf_eq_bot {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    (ℝ ∙ planeUnit 0) ⊓ (ℝ ∙ planeUnit θ) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx.1
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hx.2
  have h1 : x 1 = 0 := by
    rw [← ha]
    show a * (planeUnit 0) 1 = 0
    simp
  have h1' : x 1 = b * Real.sin θ := by
    rw [← hb]
    show b * (planeUnit θ) 1 = b * Real.sin θ
    simp
  have hb0 : b = 0 := by
    rw [h1] at h1'
    exact (mul_eq_zero.mp h1'.symm).resolve_right hs
  rw [← hb, hb0, zero_smul]

/-- The Friedrichs cosine of two distinct planar lines is `|cos θ|`. -/
theorem friedrichsCosine_planeLines {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    friedrichsCosine (ℝ ∙ planeUnit 0) (ℝ ∙ planeUnit θ) = |Real.cos θ| := by
  have hp : ‖planeUnit 0‖ = 1 := norm_planeUnit 0
  have hq : ‖planeUnit θ‖ = 1 := norm_planeUnit θ
  have hbot : (ℝ ∙ planeUnit 0) ⊓ (ℝ ∙ planeUnit θ) = ⊥ := planeLines_inf_eq_bot hs
  have htop : ((ℝ ∙ planeUnit 0) ⊓ (ℝ ∙ planeUnit θ))ᗮ = (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 2))) := by
    rw [hbot, Submodule.bot_orthogonal_eq_top]
  have hsetval : friedrichsCosineSet (ℝ ∙ planeUnit 0) (ℝ ∙ planeUnit θ) = {|Real.cos θ|} := by
    ext r
    constructor
    · rintro ⟨u, hu, v, hv, hun, hvn, rfl⟩
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hu.1
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hv.1
      have hanorm : |a| = 1 := by
        have := hun
        rw [← ha, norm_smul, Real.norm_eq_abs, hp, mul_one] at this
        exact this
      have hbnorm : |b| = 1 := by
        have := hvn
        rw [← hb, norm_smul, Real.norm_eq_abs, hq, mul_one] at this
        exact this
      have hinner : ⟪u, v⟫_ℝ = a * b * Real.cos θ := by
        rw [← ha, ← hb, real_inner_smul_left, real_inner_smul_right, inner_planeUnit_zero]
        ring
      simp only [Set.mem_singleton_iff]
      rw [hinner, Real.norm_eq_abs, abs_mul, abs_mul, hanorm, hbnorm, one_mul, one_mul]
    · intro hr
      simp only [Set.mem_singleton_iff] at hr
      subst hr
      refine ⟨planeUnit 0, ⟨Submodule.mem_span_singleton_self _, by rw [htop]; trivial⟩,
        planeUnit θ, ⟨Submodule.mem_span_singleton_self _, by rw [htop]; trivial⟩, hp, hq, ?_⟩
      rw [inner_planeUnit_zero, Real.norm_eq_abs]
  rw [friedrichsCosine, hsetval, csSup_singleton]

/-! ## Independence of curvature and incidence -/

/-- The exchange curvature of the orthogonal complements is the same operator. -/
theorem exchangeCurvature_orthogonal (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    exchangeCurvature Uᗮ Vᗮ = exchangeCurvature U V := by
  rw [exchangeCurvature, exchangeCurvature, Submodule.starProjection_orthogonal,
    Submodule.starProjection_orthogonal]
  ext w
  simp only [sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, map_sub]
  abel

/-- The unit vector of three-space at angle `θ` in the first coordinate plane. -/
noncomputable def spaceUnit (θ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![Real.cos θ, Real.sin θ, 0]

@[simp] theorem spaceUnit_apply_zero (θ : ℝ) : spaceUnit θ 0 = Real.cos θ := rfl

@[simp] theorem spaceUnit_apply_one (θ : ℝ) : spaceUnit θ 1 = Real.sin θ := rfl

@[simp] theorem spaceUnit_apply_two (θ : ℝ) : spaceUnit θ 2 = 0 := rfl

theorem norm_spaceUnit (θ : ℝ) : ‖spaceUnit θ‖ = 1 := by
  have hsq : ‖spaceUnit θ‖ ^ (2 : ℕ) = 1 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three, spaceUnit_apply_zero, spaceUnit_apply_one,
      spaceUnit_apply_two, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
      sq_abs, Real.cos_sq_add_sin_sq]
    norm_num
  have hnn : 0 ≤ ‖spaceUnit θ‖ := norm_nonneg _
  nlinarith

theorem inner_spaceUnit_left (θ : ℝ) (w : EuclideanSpace ℝ (Fin 3)) :
    ⟪spaceUnit θ, w⟫_ℝ = Real.cos θ * w 0 + Real.sin θ * w 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp only [spaceUnit_apply_zero, spaceUnit_apply_one, spaceUnit_apply_two, RCLike.inner_apply,
    starRingEnd_apply, star_trivial]
  ring

theorem inner_spaceUnit_zero (θ : ℝ) : ⟪spaceUnit 0, spaceUnit θ⟫_ℝ = Real.cos θ := by
  rw [inner_spaceUnit_left, spaceUnit_apply_zero, spaceUnit_apply_one]
  simp

/-- The third coordinate direction. -/
noncomputable def spaceVertical : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![0, 0, 1]

theorem spaceVertical_ne_zero : spaceVertical ≠ 0 := by
  intro h
  have h2 : spaceVertical 2 = (0 : EuclideanSpace ℝ (Fin 3)) 2 := by rw [h]
  have hval : spaceVertical 2 = (1 : ℝ) := rfl
  rw [hval] at h2
  simp at h2

theorem inner_spaceUnit_spaceVertical (θ : ℝ) : ⟪spaceUnit θ, spaceVertical⟫_ℝ = 0 := by
  rw [inner_spaceUnit_left]
  have h0 : spaceVertical 0 = (0 : ℝ) := rfl
  have h1 : spaceVertical 1 = (0 : ℝ) := rfl
  rw [h0, h1]
  ring

/-! ## All four curvature/incidence combinations -/

theorem sin_pi_div_four_ne_zero : Real.sin (Real.pi / 4) ≠ 0 := by
  rw [Real.sin_pi_div_four]
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  positivity

theorem cos_pi_div_four_ne_zero : Real.cos (Real.pi / 4) ≠ 0 := by
  rw [Real.cos_pi_div_four]
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  positivity

theorem exists_zeroCurvature_nontrivialIncidence :
    ∃ U V : Submodule ℝ (EuclideanSpace ℝ (Fin 2)),
      exchangeCurvature U V = 0 ∧ U ⊓ V ≠ ⊥ := by
  refine ⟨ℝ ∙ planeUnit 0, ℝ ∙ planeUnit 0, by rw [exchangeCurvature, sub_self], ?_⟩
  rw [inf_idem]
  intro h
  have hmem : planeUnit 0 ∈ (ℝ ∙ planeUnit 0 : Submodule ℝ (EuclideanSpace ℝ (Fin 2))) :=
    Submodule.mem_span_singleton_self _
  rw [h, Submodule.mem_bot] at hmem
  have hn := norm_planeUnit 0
  rw [hmem, norm_zero] at hn
  norm_num at hn

theorem exists_zeroCurvature_trivialIncidence :
    ∃ U V : Submodule ℝ (EuclideanSpace ℝ (Fin 2)),
      exchangeCurvature U V = 0 ∧ U ⊓ V = ⊥ := by
  refine ⟨ℝ ∙ planeUnit 0, ℝ ∙ planeUnit (Real.pi / 2), ?_, ?_⟩
  · refine exchangeCurvature_line_eq_zero (norm_planeUnit 0) (norm_planeUnit _) ?_
    rw [inner_planeUnit_zero, Real.cos_pi_div_two]
  · refine planeLines_inf_eq_bot ?_
    rw [Real.sin_pi_div_two]
    norm_num

theorem exists_nonzeroCurvature_trivialIncidence :
    ∃ U V : Submodule ℝ (EuclideanSpace ℝ (Fin 2)),
      exchangeCurvature U V ≠ 0 ∧ U ⊓ V = ⊥ := by
  refine ⟨ℝ ∙ planeUnit 0, ℝ ∙ planeUnit (Real.pi / 4), ?_,
    planeLines_inf_eq_bot sin_pi_div_four_ne_zero⟩
  refine exchangeCurvature_line_ne_zero (norm_planeUnit 0) (norm_planeUnit _) ?_ ?_
  · rw [inner_planeUnit_zero]
    exact cos_pi_div_four_ne_zero
  · intro h
    have hcoord := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) h
    have hl : (⟪planeUnit 0, planeUnit (Real.pi / 4)⟫_ℝ • planeUnit 0) 1 = 0 := by
      show ⟪planeUnit 0, planeUnit (Real.pi / 4)⟫_ℝ * (planeUnit 0) 1 = 0
      simp
    have hr : (planeUnit (Real.pi / 4)) 1 = Real.sin (Real.pi / 4) := rfl
    rw [hl, hr] at hcoord
    exact sin_pi_div_four_ne_zero hcoord.symm

theorem exists_nonzeroCurvature_nontrivialIncidence :
    ∃ U V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      exchangeCurvature U V ≠ 0 ∧ U ⊓ V ≠ ⊥ := by
  refine ⟨(ℝ ∙ spaceUnit 0)ᗮ, (ℝ ∙ spaceUnit (Real.pi / 4))ᗮ, ?_, ?_⟩
  · rw [exchangeCurvature_orthogonal]
    refine exchangeCurvature_line_ne_zero (norm_spaceUnit 0) (norm_spaceUnit _) ?_ ?_
    · rw [inner_spaceUnit_zero]
      exact cos_pi_div_four_ne_zero
    · intro h
      have hcoord := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 1) h
      have hl : (⟪spaceUnit 0, spaceUnit (Real.pi / 4)⟫_ℝ • spaceUnit 0) 1 = 0 := by
        show ⟪spaceUnit 0, spaceUnit (Real.pi / 4)⟫_ℝ * (spaceUnit 0) 1 = 0
        simp
      have hr : (spaceUnit (Real.pi / 4)) 1 = Real.sin (Real.pi / 4) := rfl
      rw [hl, hr] at hcoord
      exact sin_pi_div_four_ne_zero hcoord.symm
  · intro h
    have hmem : spaceVertical ∈ (ℝ ∙ spaceUnit 0)ᗮ ⊓ (ℝ ∙ spaceUnit (Real.pi / 4))ᗮ :=
      ⟨Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (inner_spaceUnit_spaceVertical 0),
        Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
          (inner_spaceUnit_spaceVertical _)⟩
    rw [h, Submodule.mem_bot] at hmem
    exact spaceVertical_ne_zero hmem

/-- **Curvature and incidence are independent.**  All four combinations of vanishing or
nonvanishing exchange curvature with trivial or nontrivial joint sector occur, already in finite
dimension. -/
theorem exchangeCurvature_incidence_independent :
    (∃ U V : Submodule ℝ (EuclideanSpace ℝ (Fin 2)),
        exchangeCurvature U V = 0 ∧ U ⊓ V ≠ ⊥) ∧
      (∃ U V : Submodule ℝ (EuclideanSpace ℝ (Fin 2)),
        exchangeCurvature U V = 0 ∧ U ⊓ V = ⊥) ∧
      (∃ U V : Submodule ℝ (EuclideanSpace ℝ (Fin 2)),
        exchangeCurvature U V ≠ 0 ∧ U ⊓ V = ⊥) ∧
      (∃ U V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
        exchangeCurvature U V ≠ 0 ∧ U ⊓ V ≠ ⊥) :=
  ⟨exists_zeroCurvature_nontrivialIncidence, exists_zeroCurvature_trivialIncidence,
    exists_nonzeroCurvature_trivialIncidence, exists_nonzeroCurvature_nontrivialIncidence⟩

end GaloisForLFunctions.HTGeometry
