import GaloisForLFunctions.OrderSixMetaplecticTheory.TheHeckeAtFourTraceReadsTheCubicTwistAtTwo

/-!
# The Hecke-at-four trace is invariant under the modular group

Let `Θ` have multiplier `κ` on `Γ(3)` and be invariant under `SL₂(ℤ)` (the projected theta function and its
linear cusp subtraction are). Then the trace `Tr F_Θ` is invariant under `SL₂(ℤ)`
(`heckeFourTrace_rational`), hence transforms by `ρ²` under the rational extension `Γ(3)·SL₂(ℤ)`
(`heckeFourTrace_rationalExtension`): all four rational cusps of `Γ(3)` see the same trace.

Mechanism. Conjugation by `g ∈ SL₂(O)` normalizing `Γ_A`, fixing `κ` and fixing `F_Θ` permutes the cosets of
`Γ_A` and fixes the trace (`heckeFourTrace_conj`). `S` and `T² = [[1, 2], [0, 1]]` qualify: `AS = SA⁻¹`,
`AT² = T⁴A`, `A⁻¹T² = TA⁻¹`, and both preserve the parity of `b` and `c`. `T³ ∈ Γ(3)` has `κ = 1`, and
`T = T³ T⁻²`; `S` and `T` generate `SL₂(ℤ)`.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicJacobi MetaplecticMobiusDescent.CubicEisenstein SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

instance levelThree_normal : levelThree.Normal := by
  unfold levelThree
  infer_instance

/-- Conjugation `γ ↦ g⁻¹γg` as an automorphism of `Γ(3)`. -/
def conjLevel (g : SL(2, O)) : levelThree ≃* levelThree := MulAut.conjNormal g⁻¹

theorem conjLevel_coe (g : SL(2, O)) (γ : levelThree) : ((conjLevel g γ : levelThree) : SL(2, O)) = g⁻¹ * γ * g := by
  rw [conjLevel, MulAut.conjNormal_apply, inv_inv]

theorem complexMatrix_eq (x : levelThree) : complexMatrix x = integralComplexMatrix (x : SL(2, O)) := rfl

theorem mem_fourCorrelationGroup (γ : levelThree) :
    γ ∈ fourCorrelationGroup ↔ (2 : O) ∣ (γ : SL(2, O)) 0 1 ∧ (2 : O) ∣ (γ : SL(2, O)) 1 0 := Iff.rfl

theorem conjCoset_rel (g : SL(2, O)) (hA : ∀ γ : levelThree, conjLevel g γ ∈ fourCorrelationGroup ↔ γ ∈ fourCorrelationGroup)
    (a b : levelThree) : (QuotientGroup.leftRel fourCorrelationGroup) a b ↔
      (QuotientGroup.leftRel fourCorrelationGroup) ((conjLevel g).toEquiv a) ((conjLevel g).toEquiv b) := by
  rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
  show a⁻¹ * b ∈ fourCorrelationGroup ↔ (conjLevel g a)⁻¹ * conjLevel g b ∈ fourCorrelationGroup
  rw [← map_inv, ← map_mul, hA]

/-- Conjugation permutes the cosets of `Γ_A`. -/
def conjCoset (g : SL(2, O)) (hA : ∀ γ : levelThree, conjLevel g γ ∈ fourCorrelationGroup ↔ γ ∈ fourCorrelationGroup) :
    (levelThree ⧸ fourCorrelationGroup) ≃ (levelThree ⧸ fourCorrelationGroup) :=
  Quotient.congr (conjLevel g).toEquiv (conjCoset_rel g hA)

theorem conjCoset_mk (g : SL(2, O)) (hA : ∀ γ : levelThree, conjLevel g γ ∈ fourCorrelationGroup ↔ γ ∈ fourCorrelationGroup)
    (γ : levelThree) : conjCoset g hA (γ : levelThree ⧸ fourCorrelationGroup) = ((conjLevel g γ : levelThree) : _) := by
  unfold conjCoset
  exact Quotient.congr_mk _ _ γ

/-- **Conjugation invariance of the trace.** -/
theorem heckeFourTrace_conj (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (g : SL(2, O)) (hA : ∀ γ : levelThree, conjLevel g γ ∈ fourCorrelationGroup ↔ γ ∈ fourCorrelationGroup)
    (hκ : ∀ γ : levelThree, complexCharacter (conjLevel g γ) = complexCharacter γ)
    (hF : ∀ w, heckeFourCorrelation Θ (integralComplexMatrix g • w) = heckeFourCorrelation Θ w)
    (w : HyperbolicSpace) :
    heckeFourTrace Θ (integralComplexMatrix g • w) = heckeFourTrace Θ w := by
  have hFΘ : ∀ δ ∈ fourCorrelationGroup, ∀ x, heckeFourCorrelation Θ (complexMatrix δ • x) =
      kubotaSquare δ * heckeFourCorrelation Θ x := fun δ hδ x => by
    rw [kubotaSquare_apply]
    exact heckeFourCorrelation_automorphy Θ hΘ δ hδ x
  have hF' : ∀ y, heckeFourCorrelation Θ ((integralComplexMatrix g)⁻¹ • y) = heckeFourCorrelation Θ y := by
    intro y
    rw [← hF, ← mul_smul, mul_inv_cancel, one_smul]
  unfold heckeFourTrace cosetTrace
  refine Fintype.sum_equiv (conjCoset g hA) _ _ fun q => ?_
  have hq : (((conjCoset g hA q).out : levelThree) : levelThree ⧸ fourCorrelationGroup) =
      ((conjLevel g q.out : levelThree) : _) := by
    rw [QuotientGroup.out_eq']
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    exact conjCoset_mk g hA q.out
  rw [cosetTerm_congr hFΘ w hq]
  unfold cosetTerm
  rw [kubotaSquare_apply, kubotaSquare_apply, hκ]
  have hmat : complexMatrix (conjLevel g q.out)⁻¹ =
      (integralComplexMatrix g)⁻¹ * complexMatrix q.out⁻¹ * integralComplexMatrix g := by
    rw [map_inv, map_inv, complexMatrix_eq, complexMatrix_eq, conjLevel_coe, map_mul, map_mul, map_inv]
    group
  rw [hmat, mul_smul, mul_smul, hF']

/-! ### The generators -/

/-- `S = [[0, −1], [1, 0]]` in `SL₂(O)`. -/
def sO : SL(2, O) := rationalEmbedding ModularGroup.S

/-- `T^n = [[1, n], [0, 1]]` in `SL₂(O)`. -/
def tPowO (n : ℤ) : SL(2, O) := rationalEmbedding (ModularGroup.T ^ n)

theorem coe_sO : (sO : Matrix (Fin 2) (Fin 2) O) = !![0, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sO, rationalEmbedding, ModularGroup.S]

theorem coe_tPowO (n : ℤ) : (tPowO n : Matrix (Fin 2) (Fin 2) O) = !![1, (n : O); 0, 1] := by
  rw [tPowO, rationalEmbedding, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    ModularGroup.coe_T_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The character of the rational extension restricted to `Γ(3)` is `κ` and is trivial on `SL₂(ℤ)`;
so conjugation by a rational matrix fixes `κ`. -/
theorem complexCharacter_conjLevel_rational (r : SL(2, ℤ)) (γ : levelThree) :
    complexCharacter (conjLevel (rationalEmbedding r) γ) = complexCharacter γ := by
  have hr := extendedComplexCharacter_rational r
  rw [← extendedComplexCharacter_restrict, ← extendedComplexCharacter_restrict]
  have he : (⟨((conjLevel (rationalEmbedding r) γ : levelThree) : SL(2, O)),
      levelThree_le_rationalExtension (conjLevel (rationalEmbedding r) γ).2⟩ : rationalExtension) =
      (⟨rationalEmbedding r, rational_mem_rationalExtension r⟩)⁻¹ *
        ⟨(γ : SL(2, O)), levelThree_le_rationalExtension γ.2⟩ *
          ⟨rationalEmbedding r, rational_mem_rationalExtension r⟩ := by
    ext1
    simp [conjLevel_coe]
  rw [he, map_mul, map_mul, map_inv, hr, inv_one, one_mul, mul_one]

theorem two_dvd_add_two_mul (x k : O) : (2 : O) ∣ x + 2 * k ↔ (2 : O) ∣ x :=
  dvd_add_left (dvd_mul_right 2 k)

theorem conjLevel_mem_iff_S (γ : levelThree) : conjLevel sO γ ∈ fourCorrelationGroup ↔ γ ∈ fourCorrelationGroup := by
  have hinv : ((sO⁻¹ : SL(2, O)) : Matrix (Fin 2) (Fin 2) O) = !![0, 1; -1, 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, coe_sO]
    simp [Matrix.adjugate_fin_two]
  have h01 : (sO⁻¹ * (γ : SL(2, O)) * sO) 0 1 = -(γ : SL(2, O)) 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hinv, coe_sO]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have h10 : (sO⁻¹ * (γ : SL(2, O)) * sO) 1 0 = -(γ : SL(2, O)) 0 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hinv, coe_sO]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  rw [mem_fourCorrelationGroup, mem_fourCorrelationGroup, conjLevel_coe, h01, h10, dvd_neg, dvd_neg]
  exact and_comm

theorem conjLevel_mem_iff_T2 (γ : levelThree) :
    conjLevel (tPowO 2) γ ∈ fourCorrelationGroup ↔ γ ∈ fourCorrelationGroup := by
  have hinv : (((tPowO 2)⁻¹ : SL(2, O)) : Matrix (Fin 2) (Fin 2) O) = !![1, -2; 0, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, coe_tPowO]
    simp [Matrix.adjugate_fin_two]
  have h01 : ((tPowO 2)⁻¹ * (γ : SL(2, O)) * tPowO 2) 0 1 = (γ : SL(2, O)) 0 1 +
      2 * ((γ : SL(2, O)) 0 0 - 2 * (γ : SL(2, O)) 1 0 - (γ : SL(2, O)) 1 1) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hinv, coe_tPowO]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    ring
  have h10 : ((tPowO 2)⁻¹ * (γ : SL(2, O)) * tPowO 2) 1 0 = (γ : SL(2, O)) 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hinv, coe_tPowO]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  rw [mem_fourCorrelationGroup, mem_fourCorrelationGroup, conjLevel_coe, h01, h10, two_dvd_add_two_mul]

/-- `A S = S A⁻¹` and `A⁻¹ S = S A`. -/
theorem fourDilation_S : fourDilation * integralComplexMatrix sO = integralComplexMatrix sO * fourContraction := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fourDilation, fourContraction, complexDiagonal, integralComplexMatrix, coe_sO,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.map]

theorem fourContraction_S : fourContraction * integralComplexMatrix sO = integralComplexMatrix sO * fourDilation := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fourDilation, fourContraction, complexDiagonal, integralComplexMatrix, coe_sO,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.map]

/-- `A T² = T⁴ A` and `A⁻¹ T² = T A⁻¹`. -/
theorem fourDilation_T2 :
    fourDilation * integralComplexMatrix (tPowO 2) = integralComplexMatrix (tPowO 4) * fourDilation := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fourDilation, complexDiagonal, integralComplexMatrix, coe_tPowO,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.map, map_ofNat]
  all_goals (try simp only [sqrtTwo_inv]); ring

theorem fourContraction_T2 :
    fourContraction * integralComplexMatrix (tPowO 2) = integralComplexMatrix (tPowO 1) * fourContraction := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fourContraction, complexDiagonal, integralComplexMatrix, coe_tPowO,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.map, map_ofNat]
  all_goals (try simp only [sqrtTwo_inv]); ring


/-! ### Invariance under `SL₂(ℤ)` -/

theorem rationalEmbedding_T : rationalEmbedding ModularGroup.T = tPowO 3 * (tPowO 2)⁻¹ := by
  rw [tPowO, tPowO, ← map_inv, ← map_mul, ← zpow_neg, ← zpow_add]
  norm_num

/-- `T³ ∈ Γ(3)`. -/
def tThreeLevel : levelThree :=
  ⟨tPowO 3, levelThree_of_entries _ (by
    intro i j
    rw [coe_tPowO]
    fin_cases i <;> fin_cases j <;> simp)⟩

section Rational

variable (Θ : HyperbolicSpace → ℂ)
  (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
  (hΘr : ∀ (r : SL(2, ℤ)) (w : HyperbolicSpace), Θ (integralComplexMatrix (rationalEmbedding r) • w) = Θ w)
include hΘ hΘr

theorem heckeFourTrace_S (w : HyperbolicSpace) :
    heckeFourTrace Θ (integralComplexMatrix sO • w) = heckeFourTrace Θ w := by
  refine heckeFourTrace_conj Θ hΘ sO conjLevel_mem_iff_S (complexCharacter_conjLevel_rational _) (fun y => ?_) w
  rw [heckeFourCorrelation, heckeFourCorrelation, ← mul_smul, fourDilation_S, mul_smul, ← mul_smul fourContraction,
    fourContraction_S, mul_smul, sO, hΘr, hΘr, mul_comm]

theorem heckeFourTrace_T2 (w : HyperbolicSpace) :
    heckeFourTrace Θ (integralComplexMatrix (tPowO 2) • w) = heckeFourTrace Θ w := by
  refine heckeFourTrace_conj Θ hΘ (tPowO 2) conjLevel_mem_iff_T2 (complexCharacter_conjLevel_rational _)
    (fun y => ?_) w
  rw [heckeFourCorrelation, heckeFourCorrelation, ← mul_smul, fourDilation_T2, mul_smul, ← mul_smul fourContraction,
    fourContraction_T2, mul_smul, tPowO, tPowO, hΘr, hΘr]

omit hΘr in
theorem heckeFourTrace_T3 (w : HyperbolicSpace) :
    heckeFourTrace Θ (integralComplexMatrix (tPowO 3) • w) = heckeFourTrace Θ w := by
  have h := heckeFourTrace_automorphy Θ hΘ tThreeLevel w
  have hκ : complexCharacter tThreeLevel = 1 := by
    change ringComplex (value tThreeLevel) = 1
    rw [value_zero_lower_left _ (by change (tPowO 3 : Matrix (Fin 2) (Fin 2) O) 1 0 = 0; rw [coe_tPowO]; simp),
      map_one]
  rw [hκ, one_pow, one_mul] at h
  exact h

/-- **The Hecke-at-four trace is invariant under `SL₂(ℤ)`.** -/
theorem heckeFourTrace_rational (r : SL(2, ℤ)) (w : HyperbolicSpace) :
    heckeFourTrace Θ (integralComplexMatrix (rationalEmbedding r) • w) = heckeFourTrace Θ w := by
  have hr : r ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]
    exact Subgroup.mem_top r
  induction hr using Subgroup.closure_induction generalizing w with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact heckeFourTrace_S Θ hΘ hΘr w
    · rw [rationalEmbedding_T, map_mul, mul_smul, heckeFourTrace_T3 Θ hΘ]
      rw [← heckeFourTrace_T2 Θ hΘ hΘr (integralComplexMatrix (tPowO 2)⁻¹ • w), ← mul_smul, ← map_mul,
        mul_inv_cancel, map_one, one_smul]
  | one => rw [map_one, map_one, one_smul]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, mul_smul, hx, hy]
  | inv x _ hx =>
    rw [← hx (integralComplexMatrix (rationalEmbedding x⁻¹) • w), ← mul_smul, ← map_mul, ← map_mul, mul_inv_cancel,
      map_one, map_one, one_smul]

end Rational

end GaloisForLFunctions.OrderSixMetaplecticTheory
