import GaloisForLFunctions.OrderSixMetaplecticTheory.TheCompositeHeckeTraceIsAThetaSquareMultipleNearTheCusp
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheHeckeTraceAtAPrimaryPrimeIsInvariantUnderTheModularGroup

/-!
# The composite Hecke trace is invariant under the modular group

For `Θ` of multiplier `κ` on `Γ(3)` and invariant under `SL₂(ℤ)`, the trace `Tr_mF_Θ` (`m = pq`) is invariant
under `SL₂(ℤ)` (`PrimaryPair.heckeTrace_rational`): conjugation by `S` and by `T^n`, `n = N(p)N(q)`, preserves
`Γ_m = Γ_p ∩ Γ_q`; `A_mS = SA_m⁻¹`; `A_mT^n = T^{mn}A_m` and `A_m⁻¹T^n = T^{p̄q̄}A_m⁻¹` with
`mn ≡ p̄q̄ ≡ 1` mod `3`.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

theorem conjLevel_mem_iff_tPow (n : ℤ) (hn : P.p ∣ (n : O)) (γ : levelThree) :
    conjLevel (tPowO n) γ ∈ P.heckeGroup ↔ γ ∈ P.heckeGroup := by
  set n' : O := (n : O)
  have hinv : (((tPowO n)⁻¹ : SL(2, O)) : Matrix (Fin 2) (Fin 2) O) = !![1, -n'; 0, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, coe_tPowO]
    simp [Matrix.adjugate_fin_two, n']
  have h01 : ((tPowO n)⁻¹ * (γ : SL(2, O)) * tPowO n) 0 1 = (γ : SL(2, O)) 0 1 +
      n' * ((γ : SL(2, O)) 0 0 - n' * (γ : SL(2, O)) 1 0 - (γ : SL(2, O)) 1 1) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hinv, coe_tPowO]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, n']
    ring
  have h10 : ((tPowO n)⁻¹ * (γ : SL(2, O)) * tPowO n) 1 0 = (γ : SL(2, O)) 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hinv, coe_tPowO]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  rw [mem_heckeGroup, mem_heckeGroup, conjLevel_coe, h01, h10, dvd_add_left (hn.mul_right _)]

theorem dilation_transO (t : O) :
    P.dilation * integralComplexMatrix (transO t) = integralComplexMatrix (transO (P.p * t)) * P.dilation := by
  have hP := P.ringComplex_ne_zero
  have hr := P.root_sq
  have hr0 := P.root_ne_zero
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.dilation, complexDiagonal, integralComplexMatrix, transO,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.map]
  rw [← hr]
  field_simp

theorem contraction_transO (t : O) :
    P.contraction * integralComplexMatrix (transO (P.p * t)) = integralComplexMatrix (transO t) * P.contraction := by
  have hP := P.ringComplex_ne_zero
  have hr := P.root_sq
  have hr0 := P.root_ne_zero
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.contraction, complexDiagonal, integralComplexMatrix, transO,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.map]
  rw [← hr]
  field_simp

end PrimaryPrime

theorem tPowO_eq_transO (n : ℤ) : tPowO n = PrimaryPrime.transO (n : O) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [coe_tPowO]
  fin_cases i <;> fin_cases j <;> simp [PrimaryPrime.transO]

namespace PrimaryPair

variable (R : PrimaryPair)

/-! ### Conjugation permutes the cosets -/

theorem conjCoset_rel (g : SL(2, O)) (hA : ∀ γ : levelThree, conjLevel g γ ∈ R.heckeGroup ↔ γ ∈ R.heckeGroup)
    (a b : levelThree) : (QuotientGroup.leftRel R.heckeGroup) a b ↔
      (QuotientGroup.leftRel R.heckeGroup) ((conjLevel g).toEquiv a) ((conjLevel g).toEquiv b) := by
  rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
  show a⁻¹ * b ∈ R.heckeGroup ↔ (conjLevel g a)⁻¹ * conjLevel g b ∈ R.heckeGroup
  rw [← map_inv, ← map_mul, hA]

/-- Conjugation permutes the cosets of `Γ_m`. -/
def conjCoset (g : SL(2, O)) (hA : ∀ γ : levelThree, conjLevel g γ ∈ R.heckeGroup ↔ γ ∈ R.heckeGroup) :
    (levelThree ⧸ R.heckeGroup) ≃ (levelThree ⧸ R.heckeGroup) :=
  Quotient.congr (conjLevel g).toEquiv (R.conjCoset_rel g hA)

theorem conjCoset_mk (g : SL(2, O)) (hA : ∀ γ : levelThree, conjLevel g γ ∈ R.heckeGroup ↔ γ ∈ R.heckeGroup)
    (γ : levelThree) : R.conjCoset g hA (γ : levelThree ⧸ R.heckeGroup) = ((conjLevel g γ : levelThree) : _) := by
  unfold conjCoset
  exact Quotient.congr_mk _ _ γ

/-- **Conjugation invariance of the composite trace.** -/
theorem heckeTrace_conj (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (g : SL(2, O)) (hA : ∀ γ : levelThree, conjLevel g γ ∈ R.heckeGroup ↔ γ ∈ R.heckeGroup)
    (hκ : ∀ γ : levelThree, complexCharacter (conjLevel g γ) = complexCharacter γ)
    (hF : ∀ w, R.heckeCorrelation Θ (integralComplexMatrix g • w) = R.heckeCorrelation Θ w)
    (w : HyperbolicSpace) :
    R.heckeTrace Θ (integralComplexMatrix g • w) = R.heckeTrace Θ w := by
  have hFΘ : ∀ δ ∈ R.heckeGroup, ∀ x, R.heckeCorrelation Θ (complexMatrix δ • x) =
      kubotaSquare δ * R.heckeCorrelation Θ x := fun δ hδ x => by
    rw [kubotaSquare_apply]
    exact R.heckeCorrelation_automorphy Θ hΘ δ hδ x
  have hF' : ∀ y, R.heckeCorrelation Θ ((integralComplexMatrix g)⁻¹ • y) = R.heckeCorrelation Θ y := by
    intro y
    rw [← hF, ← mul_smul, mul_inv_cancel, one_smul]
  unfold heckeTrace cosetTrace
  refine Fintype.sum_equiv (R.conjCoset g hA) _ _ fun q => ?_
  have hq : (((R.conjCoset g hA q).out : levelThree) : levelThree ⧸ R.heckeGroup) =
      ((conjLevel g q.out : levelThree) : _) := by
    rw [QuotientGroup.out_eq']
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    exact R.conjCoset_mk g hA q.out
  rw [cosetTerm_congr hFΘ w hq]
  unfold cosetTerm
  rw [kubotaSquare_apply, kubotaSquare_apply, hκ]
  have hmat : complexMatrix (conjLevel g q.out)⁻¹ =
      (integralComplexMatrix g)⁻¹ * complexMatrix q.out⁻¹ * integralComplexMatrix g := by
    rw [map_inv, map_inv, complexMatrix_eq, complexMatrix_eq, conjLevel_coe, map_mul, map_mul, map_inv]
    group
  rw [hmat, mul_smul, mul_smul, hF']

/-! ### The generators -/

theorem conjLevel_mem_iff_S (γ : levelThree) : conjLevel sO γ ∈ R.heckeGroup ↔ γ ∈ R.heckeGroup := by
  rw [heckeGroup, Subgroup.mem_inf, Subgroup.mem_inf, R.P.conjLevel_mem_iff_S, R.Q.conjLevel_mem_iff_S]

/-- `N(p)N(q)` as an integer. -/
def normInt : ℤ := R.P.normInt * R.Q.normInt

theorem conjLevel_mem_iff_Tn (γ : levelThree) :
    conjLevel (tPowO R.normInt) γ ∈ R.heckeGroup ↔ γ ∈ R.heckeGroup := by
  rw [heckeGroup, Subgroup.mem_inf, Subgroup.mem_inf,
    R.P.conjLevel_mem_iff_tPow _ (by rw [normInt]; push_cast; exact R.P.p_dvd_normInt.mul_right _),
    R.Q.conjLevel_mem_iff_tPow _ (by rw [normInt]; push_cast; exact R.Q.p_dvd_normInt.mul_left _)]

theorem dilation_S : R.dilation * integralComplexMatrix sO = integralComplexMatrix sO * R.contraction := by
  rw [dilation, contraction, mul_assoc, R.Q.dilation_S, ← mul_assoc, R.P.dilation_S, mul_assoc, R.con_con]

theorem contraction_S : R.contraction * integralComplexMatrix sO = integralComplexMatrix sO * R.dilation := by
  rw [dilation, contraction, mul_assoc, R.Q.contraction_S, ← mul_assoc, R.P.contraction_S, mul_assoc, R.dil_dil]

theorem dilation_Tn :
    R.dilation * integralComplexMatrix (tPowO R.normInt) =
      integralComplexMatrix (PrimaryPrime.transO (R.P.p * (R.Q.p * R.normInt))) * R.dilation := by
  rw [dilation, tPowO_eq_transO, mul_assoc, R.Q.dilation_transO, ← mul_assoc, R.P.dilation_transO, mul_assoc]

theorem contraction_Tn :
    R.contraction * integralComplexMatrix (tPowO R.normInt) =
      integralComplexMatrix (PrimaryPrime.transO (conjO R.P.p * conjO R.Q.p)) * R.contraction := by
  have hn : ((R.normInt : ℤ) : O) = R.P.p * (R.Q.p * (conjO R.P.p * conjO R.Q.p)) := by
    rw [normInt]; push_cast; rw [← R.P.p_mul_conj, ← R.Q.p_mul_conj]; ring
  rw [contraction, R.con_con, tPowO_eq_transO, hn, mul_assoc, R.P.contraction_transO, ← mul_assoc,
    R.Q.contraction_transO, mul_assoc]

theorem three_dvd_normInt_sub_one : (3 : O) ∣ (R.normInt : O) - 1 := by
  obtain ⟨u, hu⟩ := R.P.three_dvd_normInt_sub_one
  obtain ⟨w', hw⟩ := R.Q.three_dvd_normInt_sub_one
  exact ⟨u * R.Q.normInt + w', by rw [normInt]; push_cast; linear_combination (R.Q.normInt : O) * hu + hw⟩

section Rational

variable (Θ : HyperbolicSpace → ℂ)
  (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
  (hΘr : ∀ (r : SL(2, ℤ)) (w : HyperbolicSpace), Θ (integralComplexMatrix (rationalEmbedding r) • w) = Θ w)
include hΘ hΘr

theorem heckeTrace_S (w : HyperbolicSpace) :
    R.heckeTrace Θ (integralComplexMatrix sO • w) = R.heckeTrace Θ w := by
  refine R.heckeTrace_conj Θ hΘ sO R.conjLevel_mem_iff_S (complexCharacter_conjLevel_rational _) (fun y => ?_) w
  rw [heckeCorrelation, heckeCorrelation, ← mul_smul, R.dilation_S, mul_smul, ← mul_smul R.contraction,
    R.contraction_S, mul_smul, sO, hΘr, hΘr, mul_comm]

theorem heckeTrace_Tn (w : HyperbolicSpace) :
    R.heckeTrace Θ (integralComplexMatrix (tPowO R.normInt) • w) = R.heckeTrace Θ w := by
  refine R.heckeTrace_conj Θ hΘ (tPowO R.normInt) R.conjLevel_mem_iff_Tn
    (complexCharacter_conjLevel_rational _) (fun y => ?_) w
  have h1 : (3 : O) ∣ R.P.p * (R.Q.p * R.normInt) - 1 := by
    obtain ⟨u, hu⟩ := R.three_dvd_m_sub_one
    obtain ⟨w', hw⟩ := R.three_dvd_normInt_sub_one
    exact ⟨u * R.normInt + w', by linear_combination (R.normInt : O) * hu + hw⟩
  have h2 : (3 : O) ∣ conjO R.P.p * conjO R.Q.p - 1 := by
    obtain ⟨u, hu⟩ := R.P.three_dvd_conj_sub_one
    obtain ⟨w', hw⟩ := R.Q.three_dvd_conj_sub_one
    exact ⟨u * conjO R.Q.p + w', by linear_combination conjO R.Q.p * hu + hw⟩
  rw [heckeCorrelation, heckeCorrelation, ← mul_smul, R.dilation_Tn, mul_smul, ← mul_smul R.contraction,
    R.contraction_Tn, mul_smul, PrimaryPrime.theta_transO Θ hΘ hΘr _ h1, PrimaryPrime.theta_transO Θ hΘ hΘr _ h2]

omit hΘr in
theorem heckeTrace_tPow_level (n : ℤ) (hn : (3 : O) ∣ (n : O)) (w : HyperbolicSpace) :
    R.heckeTrace Θ (integralComplexMatrix (tPowO n) • w) = R.heckeTrace Θ w := by
  let τ : levelThree := ⟨tPowO n, levelThree_of_entries _ (by
    intro i j
    rw [coe_tPowO]
    fin_cases i <;> fin_cases j <;> simp [hn])⟩
  have h := R.heckeTrace_automorphy Θ hΘ τ w
  have hκ : complexCharacter τ = 1 := by
    change ringComplex (value τ) = 1
    rw [value_zero_lower_left _ (by change (tPowO n : Matrix (Fin 2) (Fin 2) O) 1 0 = 0; rw [coe_tPowO]; simp),
      map_one]
  rw [hκ, one_pow, one_mul] at h
  exact h

/-- **The composite Hecke trace is invariant under `SL₂(ℤ)`.** -/
theorem heckeTrace_rational (r : SL(2, ℤ)) (w : HyperbolicSpace) :
    R.heckeTrace Θ (integralComplexMatrix (rationalEmbedding r) • w) = R.heckeTrace Θ w := by
  have hr : r ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]
    exact Subgroup.mem_top r
  have hT : rationalEmbedding ModularGroup.T = tPowO R.normInt * tPowO (1 - R.normInt) := by
    rw [tPowO, tPowO, ← map_mul, ← zpow_add]
    norm_num
  have h3 : (3 : O) ∣ ((1 - R.normInt : ℤ) : O) := by
    obtain ⟨u, hu⟩ := R.three_dvd_normInt_sub_one
    exact ⟨-u, by push_cast; linear_combination -hu⟩
  induction hr using Subgroup.closure_induction generalizing w with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact R.heckeTrace_S Θ hΘ hΘr w
    · rw [hT, map_mul, mul_smul, R.heckeTrace_Tn Θ hΘ hΘr, R.heckeTrace_tPow_level Θ hΘ _ h3]
  | one => rw [map_one, map_one, one_smul]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, mul_smul, hx, hy]
  | inv x _ hx =>
    rw [← hx (integralComplexMatrix (rationalEmbedding x⁻¹) • w), ← mul_smul, ← map_mul, ← map_mul, mul_inv_cancel,
      map_one, map_one, one_smul]

end Rational

end PrimaryPair

end GaloisForLFunctions.OrderSixMetaplecticTheory
