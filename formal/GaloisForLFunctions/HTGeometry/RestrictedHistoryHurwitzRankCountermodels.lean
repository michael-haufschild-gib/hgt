import GaloisForLFunctions.HTGeometry.HurwitzMonodromyClosureLawstackResonanceRankLaw

/-!
# Equal-monodromy rank-one Hurwitz countermodel

The existing `(2,4)` and `(3/2,4/3)` declarations give the two rank-two sides of
Countertheorem 4.1.  This module supplies its exact `(2,2)` comparison: closure dimension and
resonance-lattice rank are both one, while the two equal Hurwitz functions have differential rank
exactly one (the pair is dependent and either singleton is independent).
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

noncomputable def hurwitzTwoTwoTorusPoint : HurwitzTorus (Fin 2) := fun _ =>
  Units.mk0 2 (by norm_num)

@[simp]
theorem hurwitzTwoTwoTorusPoint_character (u : HurwitzCharacterLattice (Fin 2)) :
    (hurwitzTorusCharacter hurwitzTwoTwoTorusPoint u : ℂ) =
      (2 : ℂ) ^ (u 0 + u 1) := by
  unfold hurwitzTorusCharacter hurwitzTorusCharacterHom hurwitzTwoTwoTorusPoint
  change (∏ i : Fin 2, (((Units.mk0 2 (by norm_num)) ^ u i : ℂˣ) : ℂ)) = _
  simp only [Fin.prod_univ_two]
  norm_num
  rw [← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0)]

def hurwitzTwoTwoRelation : HurwitzCharacterLattice (Fin 2) →ₗ[ℤ] ℤ where
  toFun u := u 0 + u 1
  map_add' u v := by simp; ring
  map_smul' z u := by simp; ring

theorem hurwitzTwoTwo_character_eq_one_iff
    (u : HurwitzCharacterLattice (Fin 2)) :
    hurwitzTorusCharacter hurwitzTwoTwoTorusPoint u = 1 ↔
      hurwitzTwoTwoRelation u = 0 := by
  rw [← Units.val_inj, hurwitzTwoTwoTorusPoint_character]
  change (2 : ℂ) ^ (u 0 + u 1) = 1 ↔ _
  constructor
  · intro h
    have hr : (2 : ℝ) ^ (u 0 + u 1) = 1 := by
      apply Complex.ofReal_injective
      rw [Complex.ofReal_zpow]
      norm_num
      exact h
    change u 0 + u 1 = 0
    exact (zpow_eq_one_iff_right₀ (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (2 : ℝ) ≠ 1)).mp hr
  · intro h
    change u 0 + u 1 = 0 at h
    rw [h]
    simp

theorem hurwitzTwoTwo_resonanceLattice_eq_ker :
    hurwitzResonanceLattice hurwitzTwoTwoTorusPoint =
      LinearMap.ker hurwitzTwoTwoRelation := by
  ext u
  rw [mem_hurwitzResonanceLattice_iff,
    hurwitzTwoTwo_character_eq_one_iff, LinearMap.mem_ker]

theorem hurwitzTwoTwoRelation_surjective :
    Function.Surjective hurwitzTwoTwoRelation := by
  intro z
  refine ⟨fun i => if i = 0 then z else 0, ?_⟩
  simp [hurwitzTwoTwoRelation]

theorem hurwitzTwoTwo_resonanceRank :
    hurwitzResonanceRank hurwitzTwoTwoTorusPoint = 1 := by
  rw [hurwitzResonanceRank, hurwitzTwoTwo_resonanceLattice_eq_ker]
  have hquot :=
    (LinearMap.quotKerEquivOfSurjective hurwitzTwoTwoRelation
      hurwitzTwoTwoRelation_surjective).finrank_eq
  have hsum := (LinearMap.ker hurwitzTwoTwoRelation).finrank_quotient_add_finrank
  have hdom : Module.finrank ℤ (HurwitzCharacterLattice (Fin 2)) = 2 := by
    exact Module.finrank_fintype_fun_eq_card (R := ℤ) (η := Fin 2)
  have hcod : Module.finrank ℤ ℤ = 1 := Module.finrank_self ℤ
  rw [hquot, hdom, hcod] at hsum
  omega

theorem hurwitzTwoTwo_monodromyClosureDimension :
    hurwitzMonodromyClosureDimension hurwitzTwoTwoTorusPoint = 1 := by
  have hsum :=
    hurwitzMonodromyClosureDimension_add_resonanceRank hurwitzTwoTwoTorusPoint
  rw [hurwitzTwoTwo_resonanceRank] at hsum
  norm_num at hsum ⊢
  omega

noncomputable def hurwitzTwoTwoExponents : Fin 2 → ℂ := fun _ =>
  hurwitzPositiveMonodromyExponent 2

theorem hurwitzTwoTwoExponents_gt_one :
    ∀ i, 1 < (hurwitzTwoTwoExponents i).re := by
  intro i
  simp [hurwitzTwoTwoExponents]

theorem hurwitzTwoTwoExponents_nonintegral :
    ∀ i, ∀ m : ℤ, hurwitzTwoTwoExponents i ≠ (m : ℂ) := by
  intro i m h
  have him := congrArg Complex.im h
  simp only [hurwitzTwoTwoExponents, hurwitzPositiveMonodromyExponent_im,
    Complex.intCast_im] at him
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hne : Real.log 2 / (2 * Real.pi) ≠ 0 := by positivity
  exact hne him

theorem hurwitzTwoTwoExponents_monoScalar (i : Fin 2) :
    HurwitzOrbit.monoScalar (hurwitzTwoTwoExponents i) = 2 := by
  simp [hurwitzTwoTwoExponents,
    monoScalar_hurwitzPositiveMonodromyExponent (by norm_num : (0 : ℝ) < 2)]

theorem hurwitzTwoTwoExponents_not_differentialIndependent :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    ¬ DifferentialIndependent (RatFunc ℂ)
      (fun i => HurwitzJointLadder.hzetaUpperEndMero (hurwitzTwoTwoExponents i)
        (hurwitzTwoTwoExponents_gt_one i)) := by
  rw [HurwitzJointLadder.hurwitz_intrinsic_residue_differentialMatroid_law
    hurwitzTwoTwoExponents hurwitzTwoTwoExponents_gt_one
      hurwitzTwoTwoExponents_nonintegral]
  intro hinj
  have hmono : HurwitzOrbit.monoScalar (hurwitzTwoTwoExponents (0 : Fin 2)) =
      HurwitzOrbit.monoScalar (hurwitzTwoTwoExponents (1 : Fin 2)) := by
    rw [hurwitzTwoTwoExponents_monoScalar, hurwitzTwoTwoExponents_monoScalar]
  have h := hinj hmono
  norm_num at h

theorem hurwitzTwoTwoExponents_each_differentialIndependent (i : Fin 2) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (fun _ : Fin 1 => HurwitzJointLadder.hzetaUpperEndMero (hurwitzTwoTwoExponents i)
        (hurwitzTwoTwoExponents_gt_one i)) := by
  let s : Fin 1 → ℂ := fun _ => hurwitzTwoTwoExponents i
  have hs : ∀ j, 1 < (s j).re := fun _ => hurwitzTwoTwoExponents_gt_one i
  have hnon : ∀ j, ∀ m : ℤ, s j ≠ (m : ℂ) :=
    fun _ => hurwitzTwoTwoExponents_nonintegral i
  rw [HurwitzJointLadder.hurwitz_intrinsic_residue_differentialMatroid_law s hs hnon]
  exact fun _ _ _ => Subsingleton.elim _ _

/-- Exact rank-one certificate: pair dependent, each singleton independent. -/
theorem hurwitzTwoTwoExponents_differentialRank_one :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    (¬ DifferentialIndependent (RatFunc ℂ)
      (fun i => HurwitzJointLadder.hzetaUpperEndMero (hurwitzTwoTwoExponents i)
        (hurwitzTwoTwoExponents_gt_one i))) ∧
    (∀ i, DifferentialIndependent (RatFunc ℂ)
      (fun _ : Fin 1 => HurwitzJointLadder.hzetaUpperEndMero (hurwitzTwoTwoExponents i)
        (hurwitzTwoTwoExponents_gt_one i))) := by
  exact ⟨hurwitzTwoTwoExponents_not_differentialIndependent,
    hurwitzTwoTwoExponents_each_differentialIndependent⟩

end

end GaloisForLFunctions.HTGeometry
