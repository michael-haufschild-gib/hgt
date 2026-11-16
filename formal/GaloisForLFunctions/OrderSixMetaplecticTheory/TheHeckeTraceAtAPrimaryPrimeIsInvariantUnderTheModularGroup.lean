import GaloisForLFunctions.OrderSixMetaplecticTheory.TheTwistedCosetsOfTheHeckeTraceReadTheDilateCorrelation

/-!
# The Hecke trace at a primary prime is invariant under the modular group

For `Θ` of multiplier `κ` on `Γ(3)` and invariant under `SL₂(ℤ)` (as `θ_s` is), the Hecke trace
`Tr_pF_Θ` is invariant under `SL₂(ℤ)` (`heckeTrace_rational`). Conjugation by `S` and by `T^n`, `n = pp̄ = N(p)`,
preserves `Γ_p` and so permutes its cosets (`heckeTrace_conj`), and

* `A_pS = SA_p⁻¹`: `S` exchanges the two Hecke points;
* `A_pT^n = T^{pn}A_p`, `A_p⁻¹T^n = T^{p̄}A_p⁻¹`, with `pn ≡ p̄ ≡ 1 mod 3`, so both translations are `T` times an element
  of `Γ(3)` with trivial multiplier.

Since `n ≡ 1 mod 3`, `T = T^n·T^{1−n}` with `T^{1−n} ∈ Γ(3)`, and `S, T` generate `SL₂(ℤ)`.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### Conjugation permutes the cosets -/

theorem mem_heckeGroup (γ : levelThree) :
    γ ∈ P.heckeGroup ↔ P.p ∣ (γ : SL(2, O)) 0 1 ∧ P.p ∣ (γ : SL(2, O)) 1 0 := Iff.rfl

theorem conjCoset_rel (g : SL(2, O)) (hA : ∀ γ : levelThree, conjLevel g γ ∈ P.heckeGroup ↔ γ ∈ P.heckeGroup)
    (a b : levelThree) : (QuotientGroup.leftRel P.heckeGroup) a b ↔
      (QuotientGroup.leftRel P.heckeGroup) ((conjLevel g).toEquiv a) ((conjLevel g).toEquiv b) := by
  rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
  show a⁻¹ * b ∈ P.heckeGroup ↔ (conjLevel g a)⁻¹ * conjLevel g b ∈ P.heckeGroup
  rw [← map_inv, ← map_mul, hA]

/-- Conjugation permutes the cosets of `Γ_p`. -/
def conjCoset (g : SL(2, O)) (hA : ∀ γ : levelThree, conjLevel g γ ∈ P.heckeGroup ↔ γ ∈ P.heckeGroup) :
    (levelThree ⧸ P.heckeGroup) ≃ (levelThree ⧸ P.heckeGroup) :=
  Quotient.congr (conjLevel g).toEquiv (P.conjCoset_rel g hA)

theorem conjCoset_mk (g : SL(2, O)) (hA : ∀ γ : levelThree, conjLevel g γ ∈ P.heckeGroup ↔ γ ∈ P.heckeGroup)
    (γ : levelThree) : P.conjCoset g hA (γ : levelThree ⧸ P.heckeGroup) = ((conjLevel g γ : levelThree) : _) := by
  unfold conjCoset
  exact Quotient.congr_mk _ _ γ

/-- **Conjugation invariance of the trace.** -/
theorem heckeTrace_conj (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (g : SL(2, O)) (hA : ∀ γ : levelThree, conjLevel g γ ∈ P.heckeGroup ↔ γ ∈ P.heckeGroup)
    (hκ : ∀ γ : levelThree, complexCharacter (conjLevel g γ) = complexCharacter γ)
    (hF : ∀ w, P.heckeCorrelation Θ (integralComplexMatrix g • w) = P.heckeCorrelation Θ w)
    (w : HyperbolicSpace) :
    P.heckeTrace Θ (integralComplexMatrix g • w) = P.heckeTrace Θ w := by
  have hFΘ : ∀ δ ∈ P.heckeGroup, ∀ x, P.heckeCorrelation Θ (complexMatrix δ • x) =
      kubotaSquare δ * P.heckeCorrelation Θ x := fun δ hδ x => by
    rw [kubotaSquare_apply]
    exact P.heckeCorrelation_automorphy Θ hΘ δ hδ x
  have hF' : ∀ y, P.heckeCorrelation Θ ((integralComplexMatrix g)⁻¹ • y) = P.heckeCorrelation Θ y := by
    intro y
    rw [← hF, ← mul_smul, mul_inv_cancel, one_smul]
  unfold heckeTrace cosetTrace
  refine Fintype.sum_equiv (P.conjCoset g hA) _ _ fun q => ?_
  have hq : (((P.conjCoset g hA q).out : levelThree) : levelThree ⧸ P.heckeGroup) =
      ((conjLevel g q.out : levelThree) : _) := by
    rw [QuotientGroup.out_eq']
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    exact P.conjCoset_mk g hA q.out
  rw [cosetTerm_congr hFΘ w hq]
  unfold cosetTerm
  rw [kubotaSquare_apply, kubotaSquare_apply, hκ]
  have hmat : complexMatrix (conjLevel g q.out)⁻¹ =
      (integralComplexMatrix g)⁻¹ * complexMatrix q.out⁻¹ * integralComplexMatrix g := by
    rw [map_inv, map_inv, complexMatrix_eq, complexMatrix_eq, conjLevel_coe, map_mul, map_mul, map_inv]
    group
  rw [hmat, mul_smul, mul_smul, hF']

/-! ### The generator `S` -/

theorem conjLevel_mem_iff_S (γ : levelThree) : conjLevel sO γ ∈ P.heckeGroup ↔ γ ∈ P.heckeGroup := by
  have hinv : ((sO⁻¹ : SL(2, O)) : Matrix (Fin 2) (Fin 2) O) = !![0, 1; -1, 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, coe_sO]
    simp [Matrix.adjugate_fin_two]
  have h01 : (sO⁻¹ * (γ : SL(2, O)) * sO) 0 1 = -(γ : SL(2, O)) 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hinv, coe_sO]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have h10 : (sO⁻¹ * (γ : SL(2, O)) * sO) 1 0 = -(γ : SL(2, O)) 0 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hinv, coe_sO]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  rw [mem_heckeGroup, mem_heckeGroup, conjLevel_coe, h01, h10, dvd_neg, dvd_neg]
  exact and_comm

theorem dilation_S : P.dilation * integralComplexMatrix sO = integralComplexMatrix sO * P.contraction := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.dilation, PrimaryPrime.contraction, complexDiagonal, integralComplexMatrix, coe_sO,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.map]

theorem contraction_S : P.contraction * integralComplexMatrix sO = integralComplexMatrix sO * P.dilation := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.dilation, PrimaryPrime.contraction, complexDiagonal, integralComplexMatrix, coe_sO,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.map]

/-! ### The generator `T^{N(p)}` -/

theorem exists_norm : ∃ n : ℤ, P.p * conjO P.p = (n : O) := by
  obtain ⟨a, b, hab⟩ := Coordinates.exists_coordinates P.p
  refine ⟨a ^ 2 - a * b + b ^ 2, ?_⟩
  rw [hab]
  simp only [map_add, map_mul, map_intCast, conjO_omega]
  have h3 : omega ^ 3 = 1 := omega_primitive.pow_eq_one
  push_cast
  linear_combination (a * b : O) * omega_sq_add + (b : O) ^ 2 * h3

/-- `N(p) = pp̄` as an integer. -/
def normInt : ℤ := P.exists_norm.choose

theorem p_mul_conj : P.p * conjO P.p = (P.normInt : O) := P.exists_norm.choose_spec

theorem three_dvd_conj_sub_one : (3 : O) ∣ conjO P.p - 1 := three_dvd_primary_sub_one _ (conjO_primary P.primary)

theorem three_dvd_normInt_sub_one : (3 : O) ∣ (P.normInt : O) - 1 := by
  obtain ⟨u, hu⟩ := P.three_dvd_sub_one
  obtain ⟨w, hw⟩ := P.three_dvd_conj_sub_one
  exact ⟨u * conjO P.p + w, by rw [← P.p_mul_conj]; linear_combination conjO P.p * hu + hw⟩

theorem p_dvd_normInt : P.p ∣ (P.normInt : O) := ⟨conjO P.p, P.p_mul_conj.symm⟩

theorem conjLevel_mem_iff_Tn (γ : levelThree) :
    conjLevel (tPowO P.normInt) γ ∈ P.heckeGroup ↔ γ ∈ P.heckeGroup := by
  set n : O := (P.normInt : O)
  have hinv : (((tPowO P.normInt)⁻¹ : SL(2, O)) : Matrix (Fin 2) (Fin 2) O) = !![1, -n; 0, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, coe_tPowO]
    simp [Matrix.adjugate_fin_two, n]
  have h01 : ((tPowO P.normInt)⁻¹ * (γ : SL(2, O)) * tPowO P.normInt) 0 1 = (γ : SL(2, O)) 0 1 +
      n * ((γ : SL(2, O)) 0 0 - n * (γ : SL(2, O)) 1 0 - (γ : SL(2, O)) 1 1) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hinv, coe_tPowO]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, n]
    ring
  have h10 : ((tPowO P.normInt)⁻¹ * (γ : SL(2, O)) * tPowO P.normInt) 1 0 = (γ : SL(2, O)) 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hinv, coe_tPowO]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  rw [mem_heckeGroup, mem_heckeGroup, conjLevel_coe, h01, h10, dvd_add_left (P.p_dvd_normInt.mul_right _)]

/-- `[[1, t], [0, 1]]` in `SL₂(O)`. -/
def transO (t : O) : SL(2, O) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩

theorem dilation_Tn :
    P.dilation * integralComplexMatrix (tPowO P.normInt) =
      integralComplexMatrix (transO (P.p * P.normInt)) * P.dilation := by
  have hP := P.ringComplex_ne_zero
  have hr := P.root_sq
  have hr0 := P.root_ne_zero
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.dilation, complexDiagonal, integralComplexMatrix, coe_tPowO, transO,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.map]
  rw [← hr]
  field_simp

theorem contraction_Tn :
    P.contraction * integralComplexMatrix (tPowO P.normInt) =
      integralComplexMatrix (transO (conjO P.p)) * P.contraction := by
  have hP := P.ringComplex_ne_zero
  have hr := P.root_sq
  have hr0 := P.root_ne_zero
  have hn := congrArg ringComplex P.p_mul_conj
  rw [map_mul, map_intCast] at hn
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.contraction, complexDiagonal, integralComplexMatrix, coe_tPowO, transO,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.map]
  rw [← hn, ← hr]
  field_simp

section Rational

variable (Θ : HyperbolicSpace → ℂ)
  (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
  (hΘr : ∀ (r : SL(2, ℤ)) (w : HyperbolicSpace), Θ (integralComplexMatrix (rationalEmbedding r) • w) = Θ w)
include hΘ hΘr

/-- `Θ` is invariant under `[[1, t], [0, 1]]` for `t ≡ 1 mod 3`. -/
theorem theta_transO (t : O) (ht : (3 : O) ∣ t - 1) (x : HyperbolicSpace) :
    Θ (integralComplexMatrix (transO t) • x) = Θ x := by
  obtain ⟨k, hk⟩ := ht
  have hm : transO t = rationalEmbedding ModularGroup.T * (transThree k : SL(2, O)) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [transO, transThree, rationalEmbedding, ModularGroup.coe_T, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.mul_apply, Fin.sum_univ_two]
    all_goals linear_combination hk
  rw [hm, map_mul, mul_smul, hΘr]
  change Θ (complexMatrix (transThree k) • x) = Θ x
  rw [hΘ, complexCharacter_transThree, one_mul]

theorem heckeTrace_S (w : HyperbolicSpace) :
    P.heckeTrace Θ (integralComplexMatrix sO • w) = P.heckeTrace Θ w := by
  refine P.heckeTrace_conj Θ hΘ sO P.conjLevel_mem_iff_S (complexCharacter_conjLevel_rational _) (fun y => ?_) w
  rw [heckeCorrelation, heckeCorrelation, ← mul_smul, P.dilation_S, mul_smul, ← mul_smul P.contraction,
    P.contraction_S, mul_smul, sO, hΘr, hΘr, mul_comm]

theorem heckeTrace_Tn (w : HyperbolicSpace) :
    P.heckeTrace Θ (integralComplexMatrix (tPowO P.normInt) • w) = P.heckeTrace Θ w := by
  refine P.heckeTrace_conj Θ hΘ (tPowO P.normInt) P.conjLevel_mem_iff_Tn
    (complexCharacter_conjLevel_rational _) (fun y => ?_) w
  have h1 : (3 : O) ∣ P.p * P.normInt - 1 := by
    obtain ⟨u, hu⟩ := P.three_dvd_sub_one
    obtain ⟨w', hw⟩ := P.three_dvd_normInt_sub_one
    exact ⟨u * P.normInt + w', by linear_combination (P.normInt : O) * hu + hw⟩
  rw [heckeCorrelation, heckeCorrelation, ← mul_smul, P.dilation_Tn, mul_smul, ← mul_smul P.contraction,
    P.contraction_Tn, mul_smul, theta_transO Θ hΘ hΘr _ h1, theta_transO Θ hΘ hΘr _ P.three_dvd_conj_sub_one]

omit hΘr in
theorem heckeTrace_tPow_level (m : ℤ) (hm : (3 : O) ∣ (m : O)) (w : HyperbolicSpace) :
    P.heckeTrace Θ (integralComplexMatrix (tPowO m) • w) = P.heckeTrace Θ w := by
  let τ : levelThree := ⟨tPowO m, levelThree_of_entries _ (by
    intro i j
    rw [coe_tPowO]
    fin_cases i <;> fin_cases j <;> simp [hm])⟩
  have h := P.heckeTrace_automorphy Θ hΘ τ w
  have hκ : complexCharacter τ = 1 := by
    change ringComplex (value τ) = 1
    rw [value_zero_lower_left _ (by change (tPowO m : Matrix (Fin 2) (Fin 2) O) 1 0 = 0; rw [coe_tPowO]; simp),
      map_one]
  rw [hκ, one_pow, one_mul] at h
  exact h

/-- **The Hecke trace at `p` is invariant under `SL₂(ℤ)`.** -/
theorem heckeTrace_rational (r : SL(2, ℤ)) (w : HyperbolicSpace) :
    P.heckeTrace Θ (integralComplexMatrix (rationalEmbedding r) • w) = P.heckeTrace Θ w := by
  have hr : r ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]
    exact Subgroup.mem_top r
  have hT : rationalEmbedding ModularGroup.T = tPowO P.normInt * tPowO (1 - P.normInt) := by
    rw [tPowO, tPowO, ← map_mul, ← zpow_add]
    norm_num
  have h3 : (3 : O) ∣ ((1 - P.normInt : ℤ) : O) := by
    obtain ⟨u, hu⟩ := P.three_dvd_normInt_sub_one
    exact ⟨-u, by push_cast; linear_combination -hu⟩
  induction hr using Subgroup.closure_induction generalizing w with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact P.heckeTrace_S Θ hΘ hΘr w
    · rw [hT, map_mul, mul_smul, P.heckeTrace_Tn Θ hΘ hΘr, P.heckeTrace_tPow_level Θ hΘ _ h3]
  | one => rw [map_one, map_one, one_smul]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, mul_smul, hx, hy]
  | inv x _ hx =>
    rw [← hx (integralComplexMatrix (rationalEmbedding x⁻¹) • w), ← mul_smul, ← map_mul, ← map_mul, mul_inv_cancel,
      map_one, map_one, one_smul]

end Rational

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
