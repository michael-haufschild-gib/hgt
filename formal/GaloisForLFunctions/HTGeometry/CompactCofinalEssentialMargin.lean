import GaloisForLFunctions.HTGeometry.ConstitutiveCompactCofinalFusion

/-!
# Essential margin of compact--cofinal formation

Rectangular distance to compact operators, its exact scalar law, and the quantitative obstruction
forced by a compact reporter jointly bounded below with a cofinal reporter.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section CompactIdealDistance

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Operator-norm distance from a rectangular bounded operator to compact operators. -/
def compactIdealDistance (T : E →L[ℂ] F) : ℝ :=
  sInf {r : ℝ | ∃ K : E →L[ℂ] F, IsCompactOperator K ∧ ‖T - K‖ = r}

theorem compactIdealDistance_set_nonempty (T : E →L[ℂ] F) :
    {r : ℝ | ∃ K : E →L[ℂ] F, IsCompactOperator K ∧ ‖T - K‖ = r}.Nonempty :=
  ⟨‖T‖, 0, isCompactOperator_zero, by rw [sub_zero]⟩

theorem compactIdealDistance_set_bddBelow (T : E →L[ℂ] F) :
    BddBelow {r : ℝ | ∃ K : E →L[ℂ] F, IsCompactOperator K ∧ ‖T - K‖ = r} := by
  refine ⟨0, ?_⟩
  rintro r ⟨K, _, rfl⟩
  positivity

/-- Every compact perturbation bounds rectangular compact-ideal distance from above. -/
theorem compactIdealDistance_le (T K : E →L[ℂ] F) (hK : IsCompactOperator K) :
    compactIdealDistance T ≤ ‖T - K‖ :=
  csInf_le (compactIdealDistance_set_bddBelow T) ⟨K, hK, rfl⟩

/-- A uniform lower bound against compact perturbations bounds compact-ideal distance. -/
theorem le_compactIdealDistance (T : E →L[ℂ] F) (c : ℝ)
    (h : ∀ K : E →L[ℂ] F, IsCompactOperator K → c ≤ ‖T - K‖) :
    c ≤ compactIdealDistance T := by
  refine le_csInf (compactIdealDistance_set_nonempty T) ?_
  rintro r ⟨K, hK, rfl⟩
  exact h K hK

theorem compactIdealDistance_nonneg (T : E →L[ℂ] F) :
    0 ≤ compactIdealDistance T :=
  le_compactIdealDistance T 0 fun _ _ => norm_nonneg _

theorem compactIdealDistance_zero : compactIdealDistance (0 : E →L[ℂ] F) = 0 :=
  le_antisymm (by
    simpa using compactIdealDistance_le (0 : E →L[ℂ] F) 0 isCompactOperator_zero)
    (compactIdealDistance_nonneg 0)

theorem compactIdealDistance_eq_zero_of_isCompactOperator
    (T : E →L[ℂ] F) (hT : IsCompactOperator T) : compactIdealDistance T = 0 :=
  le_antisymm (by simpa using compactIdealDistance_le T T hT)
    (compactIdealDistance_nonneg T)

theorem compactIdealDistance_smul_le (c : ℂ) (T : E →L[ℂ] F) :
    compactIdealDistance (c • T) ≤ ‖c‖ * compactIdealDistance T := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul, compactIdealDistance_zero, norm_zero, zero_mul]
  · have hc0 : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc
    apply le_of_forall_pos_le_add
    intro ε hε
    have hlt : compactIdealDistance T < compactIdealDistance T + ε / ‖c‖ :=
      lt_add_of_pos_right _ (div_pos hε hc0)
    obtain ⟨r, hrmem, hr⟩ := (csInf_lt_iff (compactIdealDistance_set_bddBelow T)
      (compactIdealDistance_set_nonempty T)).mp hlt
    obtain ⟨K, hK, rfl⟩ := hrmem
    calc
      compactIdealDistance (c • T) ≤ ‖c • T - c • K‖ :=
        compactIdealDistance_le _ _ (hK.smul c)
      _ = ‖c‖ * ‖T - K‖ := by rw [← smul_sub, norm_smul]
      _ ≤ ‖c‖ * (compactIdealDistance T + ε / ‖c‖) :=
        mul_le_mul_of_nonneg_left hr.le hc0.le
      _ = ‖c‖ * compactIdealDistance T + ε := by field_simp

/-- Compact-ideal distance scales exactly under scalar multiplication. -/
theorem compactIdealDistance_smul (c : ℂ) (T : E →L[ℂ] F) :
    compactIdealDistance (c • T) = ‖c‖ * compactIdealDistance T := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul, compactIdealDistance_zero, norm_zero, zero_mul]
  · refine le_antisymm (compactIdealDistance_smul_le c T) ?_
    have h := compactIdealDistance_smul_le c⁻¹ (c • T)
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul, norm_inv] at h
    have hc0 : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc
    calc
      ‖c‖ * compactIdealDistance T ≤
          ‖c‖ * (‖c‖⁻¹ * compactIdealDistance (c • T)) :=
        mul_le_mul_of_nonneg_left h hc0.le
      _ = compactIdealDistance (c • T) := by field_simp

/-- Compactness of a nonzero scalar multiple is equivalent to compactness of the operator. -/
theorem isCompactOperator_smul_iff_of_ne_zero
    (T : E →L[ℂ] F) {c : ℂ} (hc : c ≠ 0) :
    IsCompactOperator (c • T) ↔ IsCompactOperator T := by
  constructor
  · intro h
    have hinv := h.smul c⁻¹
    have heq : c⁻¹ • (c • T) = T := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [← heq]
    exact hinv
  · intro h
    exact h.smul c

end CompactIdealDistance

section RectangularUnitaryTransport

variable {E E' F F' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F']

/-- Two-sided unitary transport of a rectangular bounded operator. -/
def rectangularUnitaryPush (u : E ≃ₗᵢ[ℂ] E') (v : F ≃ₗᵢ[ℂ] F')
    (T : E →L[ℂ] F) : E' →L[ℂ] F' :=
  (v : F →L[ℂ] F') ∘L T ∘L (u.symm : E' →L[ℂ] E)

@[simp] theorem rectangularUnitaryPush_apply
    (u : E ≃ₗᵢ[ℂ] E') (v : F ≃ₗᵢ[ℂ] F') (T : E →L[ℂ] F) (x : E') :
    rectangularUnitaryPush u v T x = v (T (u.symm x)) := rfl

@[simp] theorem rectangularUnitaryPush_sub
    (u : E ≃ₗᵢ[ℂ] E') (v : F ≃ₗᵢ[ℂ] F') (S T : E →L[ℂ] F) :
    rectangularUnitaryPush u v (S - T) =
      rectangularUnitaryPush u v S - rectangularUnitaryPush u v T := by
  ext x
  simp [rectangularUnitaryPush]

theorem norm_rectangularUnitaryPush_le
    (u : E ≃ₗᵢ[ℂ] E') (v : F ≃ₗᵢ[ℂ] F') (T : E →L[ℂ] F) :
    ‖rectangularUnitaryPush u v T‖ ≤ ‖T‖ := by
  apply (rectangularUnitaryPush u v T).opNorm_le_bound T.opNorm_nonneg
  intro x
  calc
    ‖rectangularUnitaryPush u v T x‖ = ‖T (u.symm x)‖ := v.norm_map _
    _ ≤ ‖T‖ * ‖u.symm x‖ := T.le_opNorm (u.symm x)
    _ = ‖T‖ * ‖x‖ := by rw [u.symm.norm_map]

@[simp] theorem rectangularUnitaryPush_symm
    (u : E ≃ₗᵢ[ℂ] E') (v : F ≃ₗᵢ[ℂ] F') (T : E →L[ℂ] F) :
    rectangularUnitaryPush u.symm v.symm (rectangularUnitaryPush u v T) = T := by
  ext x
  simp [rectangularUnitaryPush]

theorem norm_rectangularUnitaryPush
    (u : E ≃ₗᵢ[ℂ] E') (v : F ≃ₗᵢ[ℂ] F') (T : E →L[ℂ] F) :
    ‖rectangularUnitaryPush u v T‖ = ‖T‖ := by
  apply le_antisymm (norm_rectangularUnitaryPush_le u v T)
  have h := norm_rectangularUnitaryPush_le u.symm v.symm
    (rectangularUnitaryPush u v T)
  rwa [rectangularUnitaryPush_symm] at h

theorem IsCompactOperator.rectangularUnitaryPush
    (u : E ≃ₗᵢ[ℂ] E') (v : F ≃ₗᵢ[ℂ] F')
    (T : E →L[ℂ] F) (hT : IsCompactOperator T) :
    IsCompactOperator (rectangularUnitaryPush u v T) := by
  have h := (hT.comp_clm (u.symm : E' →L[ℂ] E)).clm_comp (v : F →L[ℂ] F')
  simpa [rectangularUnitaryPush, Function.comp_def] using! h

theorem compactIdealDistance_rectangularUnitaryPush_le
    (u : E ≃ₗᵢ[ℂ] E') (v : F ≃ₗᵢ[ℂ] F') (T : E →L[ℂ] F) :
    compactIdealDistance (rectangularUnitaryPush u v T) ≤ compactIdealDistance T := by
  apply csInf_le_csInf (compactIdealDistance_set_bddBelow (rectangularUnitaryPush u v T))
    (compactIdealDistance_set_nonempty T)
  rintro r ⟨K, hK, rfl⟩
  exact ⟨rectangularUnitaryPush u v K,
    IsCompactOperator.rectangularUnitaryPush u v K hK,
    by rw [← rectangularUnitaryPush_sub, norm_rectangularUnitaryPush]⟩

/-- Compact-ideal distance is invariant under independent source and target unitaries. -/
theorem compactIdealDistance_rectangularUnitaryPush
    (u : E ≃ₗᵢ[ℂ] E') (v : F ≃ₗᵢ[ℂ] F') (T : E →L[ℂ] F) :
    compactIdealDistance (rectangularUnitaryPush u v T) = compactIdealDistance T := by
  refine le_antisymm (compactIdealDistance_rectangularUnitaryPush_le u v T) ?_
  conv_lhs => rw [← rectangularUnitaryPush_symm u v T]
  exact compactIdealDistance_rectangularUnitaryPush_le u.symm v.symm
    (rectangularUnitaryPush u v T)

theorem isCompactOperator_rectangularUnitaryPush_iff
    (u : E ≃ₗᵢ[ℂ] E') (v : F ≃ₗᵢ[ℂ] F') (T : E →L[ℂ] F) :
    IsCompactOperator (rectangularUnitaryPush u v T) ↔ IsCompactOperator T := by
  constructor
  · intro h
    have hback := IsCompactOperator.rectangularUnitaryPush u.symm v.symm
      (rectangularUnitaryPush u v T) h
    simpa using hback
  · exact IsCompactOperator.rectangularUnitaryPush u v T

end RectangularUnitaryTransport

section CompactCofinalMargin

variable {H Y Z : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]

/-- Infimum response on the unit sphere for a two-reporter packet. -/
def jointMinimumModulus (A : H →L[ℂ] Y) (R : H →L[ℂ] Z) : ℝ :=
  sInf {r : ℝ | ∃ x : H, ‖x‖ = 1 ∧ ‖(A.prod R) x‖ = r}

omit [CompleteSpace H] [CompleteSpace Y] [CompleteSpace Z] in
theorem norm_prod_rectangularUnitaryPush
    {H' Y' Z' : Type*}
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [NormedAddCommGroup Y'] [InnerProductSpace ℂ Y']
    [NormedAddCommGroup Z'] [InnerProductSpace ℂ Z']
    (u : H ≃ₗᵢ[ℂ] H') (v : Y ≃ₗᵢ[ℂ] Y') (w : Z ≃ₗᵢ[ℂ] Z')
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z) (x : H') :
    ‖((rectangularUnitaryPush u v A).prod (rectangularUnitaryPush u w R)) x‖ =
      ‖(A.prod R) (u.symm x)‖ := by
  simp [ContinuousLinearMap.prod_apply, Prod.norm_def]

omit [CompleteSpace H] [CompleteSpace Y] [CompleteSpace Z] in
/-- The minimum joint response is invariant under independent unitary changes of all three
coordinates. -/
theorem jointMinimumModulus_rectangularUnitaryPush
    {H' Y' Z' : Type*}
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [NormedAddCommGroup Y'] [InnerProductSpace ℂ Y']
    [NormedAddCommGroup Z'] [InnerProductSpace ℂ Z']
    (u : H ≃ₗᵢ[ℂ] H') (v : Y ≃ₗᵢ[ℂ] Y') (w : Z ≃ₗᵢ[ℂ] Z')
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z) :
    jointMinimumModulus (rectangularUnitaryPush u v A) (rectangularUnitaryPush u w R) =
      jointMinimumModulus A R := by
  unfold jointMinimumModulus
  congr 1
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨u.symm x, ?_, ?_⟩
    · simpa using hx
    · exact (norm_prod_rectangularUnitaryPush u v w A R x).symm
  · rintro ⟨x, hx, rfl⟩
    refine ⟨u x, ?_, ?_⟩
    · simpa using hx
    · simp [ContinuousLinearMap.prod_apply, Prod.norm_def]

omit [CompleteSpace H] [CompleteSpace Y] [CompleteSpace Z] in
/-- Joint bounded-below formation is invariant under independent unitary coordinate changes. -/
theorem isJointlyBoundedBelow_rectangularUnitaryPush_iff
    {H' Y' Z' : Type*}
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [NormedAddCommGroup Y'] [InnerProductSpace ℂ Y']
    [NormedAddCommGroup Z'] [InnerProductSpace ℂ Z']
    (u : H ≃ₗᵢ[ℂ] H') (v : Y ≃ₗᵢ[ℂ] Y') (w : Z ≃ₗᵢ[ℂ] Z')
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z) :
    IsJointlyBoundedBelow (rectangularUnitaryPush u v A) (rectangularUnitaryPush u w R) ↔
      IsJointlyBoundedBelow A R := by
  constructor
  · rintro ⟨c, hc, hbound⟩
    refine ⟨c, hc, ?_⟩
    intro x
    have h := hbound (u x)
    simpa [norm_prod_rectangularUnitaryPush] using h
  · rintro ⟨c, hc, hbound⟩
    refine ⟨c, hc, ?_⟩
    intro x
    have h := hbound (u.symm x)
    simpa [norm_prod_rectangularUnitaryPush] using h

omit [CompleteSpace H] [CompleteSpace Y] [CompleteSpace Z] in
/-- A product of compact rectangular operators is compact. -/
theorem isCompactOperator_clmProd (A : H →L[ℂ] Y) (R : H →L[ℂ] Z)
    (hA : IsCompactOperator A) (hR : IsCompactOperator R) :
    IsCompactOperator (A.prod R) := by
  have hA' := hA.clm_comp (ContinuousLinearMap.inl ℂ Y Z)
  have hR' := hR.clm_comp (ContinuousLinearMap.inr ℂ Y Z)
  have heq : A.prod R =
      (ContinuousLinearMap.inl ℂ Y Z) ∘L A + (ContinuousLinearMap.inr ℂ Y Z) ∘L R := by
    ext x <;> simp
  rw [heq]
  exact hA'.add hR'

omit [CompleteSpace Y] [CompleteSpace Z] in
/-- Two compact reporters cannot be jointly bounded below on an infinite-dimensional source. -/
theorem not_isJointlyBoundedBelow_of_compact
    (hH : ¬ FiniteDimensional ℂ H)
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z)
    (hA : IsCompactOperator A) (hR : IsCompactOperator R) :
    ¬ IsJointlyBoundedBelow A R := by
  intro hjoint
  obtain ⟨c, hc, hbound⟩ := hjoint
  have hpair : IsCompactOperator (A.prod R) := isCompactOperator_clmProd A R hA hR
  have hfinite : FiniteDimensional ℂ (⊤ : Submodule ℂ H) :=
    finiteDimensional_of_isCompactOperator_of_bounded_below hpair ⊤
      isClosed_univ hc
      (fun x _ => hbound x)
  letI := hfinite
  exact hH (Module.Finite.equiv Submodule.topEquiv)

omit [CompleteSpace Y] [CompleteSpace Z] in
/-- `(CST.15)--(CST.16)`: every compact perturbation of the cofinal reporter remains at least the
joint lower-bound margin away. -/
theorem jointLowerBound_le_norm_cofinal_sub_compact
    (hH : ¬ FiniteDimensional ℂ H)
    (A : H →L[ℂ] Y) (R K : H →L[ℂ] Z)
    (hA : IsCompactOperator A) (hK : IsCompactOperator K)
    {c : ℝ} (_hc : 0 < c)
    (hbound : ∀ x : H, c * ‖x‖ ≤ ‖(A.prod R) x‖) :
    c ≤ ‖R - K‖ := by
  by_contra hnot
  have hd : ‖R - K‖ < c := lt_of_not_ge hnot
  let b : ℝ := c - ‖R - K‖
  have hb : 0 < b := sub_pos.mpr hd
  have hpair : IsCompactOperator (A.prod K) := isCompactOperator_clmProd A K hA hK
  have hpairBound : ∀ x : H, b * ‖x‖ ≤ ‖(A.prod K) x‖ := by
    intro x
    have hdiff : ‖(A.prod R) x - (A.prod K) x‖ ≤ ‖R - K‖ * ‖x‖ := by
      calc
        ‖(A.prod R) x - (A.prod K) x‖ = ‖(R - K) x‖ := by
          simp [ContinuousLinearMap.prod_apply, Prod.norm_def]
        _ ≤ ‖R - K‖ * ‖x‖ := (R - K).le_opNorm x
    have htri : ‖(A.prod R) x‖ ≤ ‖(A.prod K) x‖ + ‖R - K‖ * ‖x‖ :=
      (norm_le_norm_add_norm_sub' ((A.prod R) x) ((A.prod K) x)).trans
        (add_le_add_right hdiff _)
    have hbound' : c * ‖x‖ ≤ max ‖A x‖ ‖R x‖ := by
      simpa [ContinuousLinearMap.prod_apply, Prod.norm_def] using hbound x
    have htri' : max ‖A x‖ ‖R x‖ ≤
        max ‖A x‖ ‖K x‖ + ‖R - K‖ * ‖x‖ := by
      simpa [ContinuousLinearMap.prod_apply, Prod.norm_def] using htri
    dsimp [b]
    change (c - ‖R - K‖) * ‖x‖ ≤ max ‖A x‖ ‖K x‖
    linarith
  have hfinite : FiniteDimensional ℂ (⊤ : Submodule ℂ H) :=
    finiteDimensional_of_isCompactOperator_of_bounded_below hpair ⊤
      isClosed_univ hb
      (fun x _ => hpairBound x)
  letI := hfinite
  exact hH (Module.Finite.equiv Submodule.topEquiv)

omit [CompleteSpace Y] [CompleteSpace Z] in
/-- `(CST.16)`: every admitted joint margin is a lower bound for rectangular essential norm. -/
theorem jointLowerBound_le_compactIdealDistance
    (hH : ¬ FiniteDimensional ℂ H)
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z)
    (hA : IsCompactOperator A) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x : H, c * ‖x‖ ≤ ‖(A.prod R) x‖) :
    c ≤ compactIdealDistance R := by
  exact le_compactIdealDistance R c fun K hK =>
    jointLowerBound_le_norm_cofinal_sub_compact hH A R K hA hK hc hbound

omit [CompleteSpace Y] [CompleteSpace Z] in
/-- Joint compact--cofinal observability forces a strictly positive essential margin. -/
theorem exists_pos_le_compactIdealDistance_of_compact_jointlyBoundedBelow
    (hH : ¬ FiniteDimensional ℂ H)
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z)
    (hA : IsCompactOperator A) (hjoint : IsJointlyBoundedBelow A R) :
    ∃ c : ℝ, 0 < c ∧ c ≤ compactIdealDistance R := by
  obtain ⟨c, hc, hbound⟩ := hjoint
  exact ⟨c, hc, jointLowerBound_le_compactIdealDistance hH A R hA hc hbound⟩

omit [CompleteSpace Y] [CompleteSpace Z] in
/-- The cofinal carrier cannot be compact on an infinite-dimensional jointly observed source. -/
theorem cofinal_not_isCompactOperator_of_compact_jointlyBoundedBelow
    (hH : ¬ FiniteDimensional ℂ H)
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z)
    (hA : IsCompactOperator A) (hjoint : IsJointlyBoundedBelow A R) :
    ¬ IsCompactOperator R := by
  exact fun hR => not_isJointlyBoundedBelow_of_compact hH A R hA hR hjoint

omit [CompleteSpace Y] [CompleteSpace Z] in
/-- `(CST.18)`: the scalar defect is compact exactly at the zero scalar. -/
theorem cofinalDefect_isCompactOperator_iff
    (hH : ¬ FiniteDimensional ℂ H)
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z)
    (hA : IsCompactOperator A) (hjoint : IsJointlyBoundedBelow A R) (delta : ℂ) :
    IsCompactOperator (delta • R) ↔ delta = 0 := by
  constructor
  · intro hdelta
    by_contra hne
    exact cofinal_not_isCompactOperator_of_compact_jointlyBoundedBelow hH A R hA hjoint
      ((isCompactOperator_smul_iff_of_ne_zero R hne).mp hdelta)
  · rintro rfl
    rw [zero_smul]
    exact isCompactOperator_zero

omit [CompleteSpace H] [CompleteSpace Z] in
/-- `(CST.19)`: exact Calkin-distance response of the scalar defect. -/
theorem cofinalDefect_compactIdealDistance
    (R : H →L[ℂ] Z) (delta : ℂ) :
    compactIdealDistance (delta • R) = ‖delta‖ * compactIdealDistance R :=
  compactIdealDistance_smul delta R

omit [CompleteSpace H] [CompleteSpace Y] [CompleteSpace Z] in
/-- `(CST.20)`: retaining the structural carrier preserves every joint lower margin, regardless
of the scalar defect coordinate. -/
theorem carrierDefectPacket_boundedBelow
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z)
    {c : ℝ} (_hc : 0 < c)
    (hbound : ∀ x : H, c * ‖x‖ ≤ ‖(A.prod R) x‖) (delta : ℂ) :
    ∀ x : H, c * ‖x‖ ≤ ‖carrierDefectPacket A R delta x‖ := by
  intro x
  refine (hbound x).trans ?_
  simp only [carrierDefectPacket, ContinuousLinearMap.prod_apply, Prod.norm_def]
  exact le_max_left _ _

omit [CompleteSpace Y] [CompleteSpace Z] in
/-- With no retained carrier, the packet is jointly bounded below exactly away from the unique
zero-defect parameter. -/
theorem soleDefect_jointlyBoundedBelow_iff
    (hH : ¬ FiniteDimensional ℂ H)
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z)
    (hA : IsCompactOperator A) (hjoint : IsJointlyBoundedBelow A R) (delta : ℂ) :
    IsJointlyBoundedBelow A (delta • R) ↔ delta ≠ 0 := by
  constructor
  · intro hdelta hzero
    subst delta
    apply not_isJointlyBoundedBelow_of_compact hH A (0 • R) hA
      (by
        rw [zero_smul]
        exact isCompactOperator_zero)
    simpa using hdelta
  · intro hdelta
    obtain ⟨c, hc, hbound⟩ := hjoint
    let m : ℝ := min 1 ‖delta‖
    have hnormdelta : 0 < ‖delta‖ := norm_pos_iff.mpr hdelta
    have hm : 0 < m := lt_min one_pos hnormdelta
    refine ⟨m * c, mul_pos hm hc, ?_⟩
    intro x
    have hscale :
        m * max ‖A x‖ ‖R x‖ ≤ max ‖A x‖ (‖delta‖ * ‖R x‖) := by
      rcases le_total ‖A x‖ ‖R x‖ with har | hra
      · rw [max_eq_right har]
        exact (mul_le_mul_of_nonneg_right (min_le_right 1 ‖delta‖) (norm_nonneg _)).trans
          (le_max_right _ _)
      · rw [max_eq_left hra]
        exact (mul_le_of_le_one_left (norm_nonneg _) (min_le_left 1 ‖delta‖)).trans
          (le_max_left _ _)
    calc
      (m * c) * ‖x‖ = m * (c * ‖x‖) := by ring
      _ ≤ m * ‖(A.prod R) x‖ := mul_le_mul_of_nonneg_left (hbound x) hm.le
      _ ≤ ‖(A.prod (delta • R)) x‖ := by
        simpa [ContinuousLinearMap.prod_apply, Prod.norm_def, norm_smul] using hscale

end CompactCofinalMargin

end

end GaloisForLFunctions.HTGeometry
