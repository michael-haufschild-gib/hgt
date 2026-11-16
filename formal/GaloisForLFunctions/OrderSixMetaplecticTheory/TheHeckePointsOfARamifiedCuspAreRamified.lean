import GaloisForLFunctions.OrderSixMetaplecticTheory.TheHeckeAtFourTraceIsInvariantUnderTheModularGroup
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheThetaFunctionHasALinearCuspSubtraction

/-!
# The Hecke points of a ramified cusp are ramified

The cusps of `Γ(3)` fall into the rational class and two ramified classes (MMD's `three_cusp_decomposition`). The
class of a matrix `N` is detected by the **column determinant modulo the ramified prime**
`D(N) = a₁c₂ − a₂c₁ ∈ ℤ/3` of the coordinates `a = a₁ + a₂ω`, `c = c₁ + c₂ω` of its first column (`colRes`):
`D` vanishes on the rational class (`colRes_rational`: `Γ(3)` acts trivially modulo `3` and `SL₂(ℤ)` columns have
no `ω`-coordinate), so `D(N) ≠ 0` forces a ramified class (`class_ne_zero_of_colRes`), where `θ_s` decays
exponentially (`sourceTheta_ramified_decay`).

The Hecke matrices `√2 A = diag(2, 1)` and `√2 A⁻¹ = diag(1, 2)` multiply `D` by `2`, and every determinant-two
integral matrix factors as `N' U` with `N' ∈ SL₂(O)` and `U` upper triangular, `U₀₀ = g` a divisor of `2`
(`exists_column_factor`; `D` of the column scales by the norm of `g`). Hence (`sourceTheta_hecke_ramified`): if
`D(M) ≠ 0` then `θ_s(A^{±1} M x)` decays exponentially in the height of `x`: the Hecke points of a ramified point
are ramified, at a height between `v/2` and `2v`.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicJacobi MetaplecticMobiusDescent.CubicEisenstein SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-! ### The column determinant modulo the ramified prime -/

/-- `D(x, y) = x₁y₂ − x₂y₁` for the coordinates of `x, y` modulo `3`. -/
def colRes (x y : O) : ZMod 3 :=
  (cuspResidue x).1 * (cuspResidue y).2 - (cuspResidue x).2 * (cuspResidue y).1

/-- The norm of `u` modulo `3`. -/
def normRes (u : O) : ZMod 3 := (cuspResidue u).1 ^ 2 - (cuspResidue u).1 * (cuspResidue u).2 + (cuspResidue u).2 ^ 2

theorem colRes_mul_left (u x y : O) : colRes (u * x) (u * y) = normRes u * colRes x y := by
  simp only [colRes, normRes, cuspResidue_mul, cuspResidueMul]
  ring

theorem colRes_int_comb (m n m' n' : ℤ) (x y : O) :
    colRes ((m : O) * x + (n : O) * y) ((m' : O) * x + (n' : O) * y) = ((m * n' - n * m' : ℤ) : ZMod 3) * colRes x y := by
  simp only [colRes, cuspResidue_add, cuspResidue_intCast_mul]
  push_cast
  ring

theorem cuspResidue_congr {x y : O} (h : (3 : O) ∣ x - y) : cuspResidue x = cuspResidue y := by
  obtain ⟨w, hw⟩ := h
  have hx : x = y + ((3 : ℤ) : O) * w := by push_cast; linear_combination hw
  rw [hx, cuspResidue_add, cuspResidue_intCast_mul]
  have h3 : ((3 : ℤ) : ZMod 3) = 0 := by decide
  rw [h3, zero_mul, zero_mul, add_zero, add_zero]

theorem colRes_two_left (x y : O) : colRes (2 * x) y = 2 * colRes x y := by
  have h := colRes_int_comb 2 0 0 1 x y
  simp only [Int.cast_ofNat, Int.cast_zero, zero_mul, add_zero, Int.cast_one, one_mul, zero_add] at h
  rw [h]
  norm_num

theorem colRes_two_right (x y : O) : colRes x (2 * y) = 2 * colRes x y := by
  have h := colRes_int_comb 1 0 0 2 x y
  simp only [Int.cast_one, one_mul, Int.cast_zero, zero_mul, add_zero, Int.cast_ofNat, zero_add] at h
  rw [h]
  norm_num

/-- `D` vanishes on the rational class. -/
theorem colRes_rational (G : rationalExtension) (T : SL(2, O)) (hT : T 1 0 = 0) :
    colRes (((G : SL(2, O)) * T) 0 0) (((G : SL(2, O)) * T) 1 0) = 0 := by
  obtain ⟨n, r, hG⟩ := G.2
  have hcol : ∀ i : Fin 2, ((G : SL(2, O)) * T) i 0 = T 0 0 * (G : SL(2, O)) i 0 := by
    intro i
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hT, mul_comm]
  have hres : ∀ i : Fin 2, cuspResidue ((G : SL(2, O)) i 0) = (((r i 0 : ℤ) : ZMod 3), 0) := by
    intro i
    rw [← cuspResidue_intCast]
    apply cuspResidue_congr
    rw [← hG]
    have h00 : (3 : O) ∣ (n : SL(2, O)) 0 0 - 1 := by simpa using levelThree_entry n 0 0
    have h01 : (3 : O) ∣ (n : SL(2, O)) 0 1 := by simpa using levelThree_entry n 0 1
    have h10 : (3 : O) ∣ (n : SL(2, O)) 1 0 := by simpa using levelThree_entry n 1 0
    have h11 : (3 : O) ∣ (n : SL(2, O)) 1 1 - 1 := by simpa using levelThree_entry n 1 1
    have hsum : ((n : SL(2, O)) * rationalEmbedding r) i 0 =
        (n : SL(2, O)) i 0 * (r 0 0 : O) + (n : SL(2, O)) i 1 * (r 1 0 : O) := by
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, rationalEmbedding]
    rw [hsum]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]
      obtain ⟨a, ha⟩ := h00
      obtain ⟨b, hb⟩ := h01
      exact ⟨a * (r 0 0 : O) + b * (r 1 0 : O), by linear_combination (r 0 0 : O) * ha + (r 1 0 : O) * hb⟩
    · simp only [Fin.mk_one, Fin.isValue]
      obtain ⟨a, ha⟩ := h10
      obtain ⟨b, hb⟩ := h11
      exact ⟨a * (r 0 0 : O) + b * (r 1 0 : O), by linear_combination (r 0 0 : O) * ha + (r 1 0 : O) * hb⟩
  rw [hcol 0, hcol 1, colRes_mul_left, colRes, hres 0, hres 1]
  ring

/-- `D(N) ≠ 0` forces a ramified cusp class. -/
theorem class_ne_zero_of_colRes (N : SL(2, O)) (h : colRes (N 0 0) (N 1 0) ≠ 0) (G : rationalExtension)
    (j : Fin 3) (T : SL(2, O)) (hT : T 1 0 = 0) (hdec : N = (G : SL(2, O)) * cuspRepresentative j * T) : j ≠ 0 := by
  rintro rfl
  have hc1 : cuspRepresentative 0 = 1 := by
    ext i k
    fin_cases i <;> fin_cases k <;> simp [cuspRepresentative, cuspParameter, lowerCuspMatrix]
  rw [hc1, mul_one] at hdec
  rw [hdec] at h
  exact h (colRes_rational G T hT)

/-- **`θ_s` decays exponentially at every matrix of nonzero column determinant.** -/
theorem sourceTheta_ramified_decay (a : ℝ) (ha : 0 < a) :
    ∃ C β : ℝ, 0 ≤ C ∧ 0 < β ∧ ∀ (N : SL(2, O)), colRes (N 0 0) (N 1 0) ≠ 0 →
      ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
        ‖sourceTheta (integralComplexMatrix N • upperPoint z v hv)‖ ≤ C * Real.exp (-β * v) := by
  obtain ⟨C₂, hC₂, hr₂⟩ := ramifiedSource_exponential_decay false a ha
  obtain ⟨C₃, hC₃, hr₃⟩ := ramifiedSource_exponential_decay true a ha
  refine ⟨C₂ + C₃, residualBesselDecayRate / 3, by positivity,
    by have := residualBesselDecayRate_pos; positivity, fun N hN z v hv hav => ?_⟩
  obtain ⟨G, j, T, hT, -, hu1, hdec⟩ := three_cusp_decomposition N
  have hj := class_ne_zero_of_colRes N hN G j T hT hdec
  obtain ⟨z', v', hv', hp⟩ := upperPoint_surjective (integralComplexMatrix T • upperPoint z v hv)
  have hvv : v' = v := by
    have h := height_upperTriangular T hT hu1 z v hv
    rw [← hp, hyperbolicHeight_upperPoint] at h
    exact h
  subst hvv
  have hθG := cubicSourceResidualFunction_automorphy G
    (integralComplexMatrix (cuspRepresentative j) • upperPoint z' v' hv')
  have hG1 := norm_extendedComplexCharacter G
  rw [hdec, map_mul, map_mul, mul_smul, mul_smul, ← hp]
  change ‖cubicSourceResidualFunction _‖ ≤ _
  rw [hθG, norm_mul, hG1, one_mul]
  fin_cases j
  · exact absurd rfl hj
  · have h := hr₂ v' hv' hav z'
    have hroot : ((ramifiedCuspRoot false : Oˣ) : O) = cuspParameter 1 := by
      simp [ramifiedCuspRoot, cuspOmegaUnit_val, cuspParameter]
    rw [ramifiedSourceFunction, hroot] at h
    refine h.trans ?_
    nlinarith [Real.exp_pos (-(residualBesselDecayRate / 3) * v')]
  · have h := hr₃ v' hv' hav z'
    have hroot : ((ramifiedCuspRoot true : Oˣ) : O) = cuspParameter 2 := by
      simp [ramifiedCuspRoot, cuspOmegaUnit_val, cuspParameter]
    rw [ramifiedSourceFunction, hroot] at h
    refine h.trans ?_
    nlinarith [Real.exp_pos (-(residualBesselDecayRate / 3) * v')]


/-! ### Hecke points of determinant two -/

/-- A nonzero column `(p, q)` over the principal ideal domain `O` is `g · (p', q')` with `(p', q')` unimodular. -/
theorem exists_column_factor (p q : O) (h : ¬(p = 0 ∧ q = 0)) :
    ∃ g p' q' a b : O, g ≠ 0 ∧ p = g * p' ∧ q = g * q' ∧ a * p' + b * q' = 1 := by
  set I : Ideal O := Ideal.span {p, q}
  set g := Submodule.IsPrincipal.generator I
  have hI : I = Ideal.span {g} := (Submodule.IsPrincipal.span_singleton_generator I).symm
  have hp : p ∈ Ideal.span {g} := hI ▸ Ideal.subset_span (by simp)
  have hq : q ∈ Ideal.span {g} := hI ▸ Ideal.subset_span (by simp)
  obtain ⟨p', hp'⟩ := Ideal.mem_span_singleton'.mp hp
  obtain ⟨q', hq'⟩ := Ideal.mem_span_singleton'.mp hq
  have hg : g ∈ I := Submodule.IsPrincipal.generator_mem I
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hg
  have hg0 : g ≠ 0 := by
    intro h0
    apply h
    rw [h0, mul_zero] at hp' hq'
    exact ⟨hp'.symm, hq'.symm⟩
  refine ⟨g, p', q', a, b, hg0, by rw [← hp', mul_comm], by rw [← hq', mul_comm], ?_⟩
  apply mul_left_cancel₀ hg0
  calc g * (a * p' + b * q') = a * (p' * g) + b * (q' * g) := by ring
    _ = g * 1 := by rw [hp', hq', hab, mul_one]

theorem colRes_ne_zero_of_factor {p q g p' q' : O} (hp : p = g * p') (hq : q = g * q') (h : colRes p q ≠ 0) :
    colRes p' q' ≠ 0 := by
  intro h0
  apply h
  rw [hp, hq, colRes_mul_left, h0, mul_zero]

/-- The unimodular completion `[[p', −b], [q', a]]`. -/
def columnCompletion (p' q' a b : O) (hab : a * p' + b * q' = 1) : SL(2, O) :=
  ⟨!![p', -b; q', a], by rw [Matrix.det_fin_two_of]; linear_combination hab⟩

theorem height_upper_triangular_complex (U : SL(2, ℂ)) (hU : U 1 0 = 0) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    hyperbolicHeight (U • upperPoint z v hv) = v * ‖U 0 0‖ ^ 2 := by
  have hdet : U 0 0 * U 1 1 = 1 := by
    have h := U.property
    rw [Matrix.det_fin_two, hU, mul_zero, sub_zero] at h
    exact h
  have h11 : U 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one hdet
  rw [hyperbolicHeight_action_upperPoint, hU, zero_mul, zero_add, norm_zero]
  have hn : ‖U 0 0‖ * ‖U 1 1‖ = 1 := by rw [← norm_mul, hdet, norm_one]
  have hn1 : ‖U 1 1‖ ≠ 0 := norm_ne_zero_iff.mpr h11
  field_simp
  nlinarith [hn]

/-- The Hecke point `A M x` of an integral matrix: `A M = N' U` with `N' ∈ SL₂(O)` of first column `(2M₀₀, M₁₀)/g`
and `U` upper triangular, `|U₀₀|² = |g|²/2`. -/
theorem fourDilation_factor (M : SL(2, O)) :
    ∃ (N' : SL(2, O)) (g : O), g ≠ 0 ∧ 2 * M 0 0 = g * N' 0 0 ∧ M 1 0 = g * N' 1 0 ∧
      ∃ U : SL(2, ℂ), U 1 0 = 0 ∧ ‖U 0 0‖ ^ 2 = ‖ringComplex g‖ ^ 2 / 2 ∧
        fourDilation * integralComplexMatrix M = integralComplexMatrix N' * U := by
  have hM : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact M.det_coe
  have hnz : ¬(2 * M 0 0 = 0 ∧ M 1 0 = 0) := by
    rintro ⟨h1, h2⟩
    have h0 : M 0 0 = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h two_ne_zero
      · exact h
    rw [h0, h2] at hM
    simp at hM
  obtain ⟨g, p', q', a, b, hg, hp, hq, hab⟩ := exists_column_factor _ _ hnz
  refine ⟨columnCompletion p' q' a b hab, g, hg, by simp [columnCompletion, hp], by simp [columnCompletion, hq], ?_⟩
  set N' := columnCompletion p' q' a b hab
  refine ⟨(integralComplexMatrix N')⁻¹ * (fourDilation * integralComplexMatrix M), ?_, ?_, by group⟩
  · have hinv : ((integralComplexMatrix N')⁻¹ : SL(2, ℂ)) = integralComplexMatrix N'⁻¹ := (map_inv _ _).symm
    rw [hinv]
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, integralComplexMatrix,
      Matrix.SpecialLinearGroup.SL2_inv_expl, N', columnCompletion, fourDilation, complexDiagonal, Matrix.vecMul,
      dotProduct, Matrix.map_apply]
    have hp' := congrArg ringComplex hp
    have hq' := congrArg ringComplex hq
    simp only [map_mul, map_ofNat] at hp' hq'
    simp only [sqrtTwo_inv]
    linear_combination (-(sqrtTwo / 2)) * ringComplex q' * hp' + (sqrtTwo / 2) * ringComplex p' * hq'
  · have hinv : ((integralComplexMatrix N')⁻¹ : SL(2, ℂ)) = integralComplexMatrix N'⁻¹ := (map_inv _ _).symm
    rw [hinv]
    have h00 : (integralComplexMatrix N'⁻¹ * (fourDilation * integralComplexMatrix M)) 0 0 = ringComplex g / sqrtTwo := by
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, integralComplexMatrix,
        Matrix.SpecialLinearGroup.SL2_inv_expl, N', columnCompletion, fourDilation, complexDiagonal, Matrix.vecMul,
      dotProduct, Matrix.map_apply]
      have hp' := congrArg ringComplex hp
      have hq' := congrArg ringComplex hq
      have hab' := congrArg ringComplex hab
      simp only [map_mul, map_ofNat, map_add, map_one] at hp' hq' hab'
      simp only [sqrtTwo_inv]
      rw [show ringComplex g / sqrtTwo = ringComplex g * (sqrtTwo / 2) by rw [div_eq_mul_inv, sqrtTwo_inv]]
      linear_combination (sqrtTwo / 2) * ringComplex a * hp' + (sqrtTwo / 2) * ringComplex b * hq' +
        (sqrtTwo / 2) * ringComplex g * hab'
    rw [h00, norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]


/-- The Hecke point `A⁻¹ M x`: `A⁻¹ M = N' U` with `N'` of first column `(M₀₀, 2M₁₀)/g`. -/
theorem fourContraction_factor (M : SL(2, O)) :
    ∃ (N' : SL(2, O)) (g : O), g ≠ 0 ∧ M 0 0 = g * N' 0 0 ∧ 2 * M 1 0 = g * N' 1 0 ∧
      ∃ U : SL(2, ℂ), U 1 0 = 0 ∧ ‖U 0 0‖ ^ 2 = ‖ringComplex g‖ ^ 2 / 2 ∧
        fourContraction * integralComplexMatrix M = integralComplexMatrix N' * U := by
  have hM : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact M.det_coe
  have hnz : ¬(M 0 0 = 0 ∧ 2 * M 1 0 = 0) := by
    rintro ⟨h1, h2⟩
    have h0 : M 1 0 = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h two_ne_zero
      · exact h
    rw [h1, h0] at hM
    simp at hM
  obtain ⟨g, p', q', a, b, hg, hp, hq, hab⟩ := exists_column_factor _ _ hnz
  refine ⟨columnCompletion p' q' a b hab, g, hg, by simp [columnCompletion, hp], by simp [columnCompletion, hq], ?_⟩
  set N' := columnCompletion p' q' a b hab
  refine ⟨(integralComplexMatrix N')⁻¹ * (fourContraction * integralComplexMatrix M), ?_, ?_, by group⟩
  · have hinv : ((integralComplexMatrix N')⁻¹ : SL(2, ℂ)) = integralComplexMatrix N'⁻¹ := (map_inv _ _).symm
    rw [hinv]
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, integralComplexMatrix,
      Matrix.SpecialLinearGroup.SL2_inv_expl, N', columnCompletion, fourContraction, complexDiagonal, Matrix.vecMul,
      dotProduct, Matrix.map_apply]
    have hp' := congrArg ringComplex hp
    have hq' := congrArg ringComplex hq
    simp only [map_mul, map_ofNat] at hp' hq'
    simp only [sqrtTwo_inv]
    linear_combination (-(sqrtTwo / 2)) * ringComplex q' * hp' + (sqrtTwo / 2) * ringComplex p' * hq'
  · have hinv : ((integralComplexMatrix N')⁻¹ : SL(2, ℂ)) = integralComplexMatrix N'⁻¹ := (map_inv _ _).symm
    rw [hinv]
    have h00 : (integralComplexMatrix N'⁻¹ * (fourContraction * integralComplexMatrix M)) 0 0 =
        ringComplex g / sqrtTwo := by
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, integralComplexMatrix,
        Matrix.SpecialLinearGroup.SL2_inv_expl, N', columnCompletion, fourContraction, complexDiagonal, Matrix.vecMul,
        dotProduct, Matrix.map_apply]
      have hp' := congrArg ringComplex hp
      have hq' := congrArg ringComplex hq
      have hab' := congrArg ringComplex hab
      simp only [map_mul, map_ofNat, map_add, map_one] at hp' hq' hab'
      simp only [sqrtTwo_inv]
      rw [show ringComplex g / sqrtTwo = ringComplex g * (sqrtTwo / 2) by rw [div_eq_mul_inv, sqrtTwo_inv]]
      linear_combination (sqrtTwo / 2) * ringComplex a * hp' + (sqrtTwo / 2) * ringComplex b * hq' +
        (sqrtTwo / 2) * ringComplex g * hab'
    rw [h00, norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- A divisor of `2` has squared absolute value at most `4`. -/
theorem norm_sq_le_four_of_mul {g k : O} (h : g * k = 2) : ‖ringComplex g‖ ^ 2 ≤ 4 := by
  have hk : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact two_ne_zero h.symm
  have hk1 : 1 ≤ ‖ringComplex k‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact one_le_normSq_embedding k hk
  have hn : ‖ringComplex g‖ ^ 2 * ‖ringComplex k‖ ^ 2 = 4 := by
    rw [← mul_pow, ← norm_mul, ← map_mul, h, map_ofNat, Complex.norm_ofNat]
    norm_num
  nlinarith [sq_nonneg ‖ringComplex g‖]

theorem one_le_norm_sq_ringComplex {g : O} (hg : g ≠ 0) : 1 ≤ ‖ringComplex g‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  exact one_le_normSq_embedding g hg

/-- **The Hecke points of a ramified point are ramified.** If `D(M) ≠ 0`, then `θ_s(A^{±1} M x)` decays
exponentially in the height `v` of `x`. -/
theorem sourceTheta_hecke_ramified (a : ℝ) (ha : 0 < a) :
    ∃ C β : ℝ, 0 ≤ C ∧ 0 < β ∧ ∀ (M : SL(2, O)), colRes (M 0 0) (M 1 0) ≠ 0 →
      ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
        ‖sourceTheta (fourDilation • integralComplexMatrix M • upperPoint z v hv)‖ ≤ C * Real.exp (-(β / 2) * v) ∧
        ‖sourceTheta (fourContraction • integralComplexMatrix M • upperPoint z v hv)‖ ≤
          C * Real.exp (-(β / 2) * v) := by
  obtain ⟨C, β, hC, hβ, hdec⟩ := sourceTheta_ramified_decay (a / 2) (by positivity)
  refine ⟨C, β, hC, hβ, fun M hM z v hv hav => ⟨?_, ?_⟩⟩
  · obtain ⟨N', g, hg, hp, hq, U, hU10, hU00, hfac⟩ := fourDilation_factor M
    have hk : g * (N' 0 0 * M 1 1 - 2 * M 0 1 * N' 1 0) = 2 := by
      have hM : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact M.det_coe
      linear_combination (M 1 1) * hp.symm - 2 * M 0 1 * hq.symm + 2 * hM
    have hg4 := norm_sq_le_four_of_mul hk
    have hg1 := one_le_norm_sq_ringComplex hg
    obtain ⟨z', v', hv', hpt⟩ := upperPoint_surjective (U • upperPoint z v hv)
    have hvv : v' = v * (‖ringComplex g‖ ^ 2 / 2) := by
      have h := height_upper_triangular_complex U hU10 z v hv
      rw [← hpt, hyperbolicHeight_upperPoint, hU00] at h
      exact h
    have hcol : colRes (N' 0 0) (N' 1 0) ≠ 0 := by
      refine colRes_ne_zero_of_factor hp hq ?_
      rw [colRes_two_left]
      exact mul_ne_zero (by decide) hM
    rw [← mul_smul, hfac, mul_smul, ← hpt]
    have hav' : a / 2 ≤ v' := by rw [hvv]; nlinarith
    refine (hdec N' hcol z' v' hv' hav').trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
    rw [hvv]
    nlinarith [mul_nonneg (mul_nonneg hβ.le hv.le) (sub_nonneg.mpr hg1)]
  · obtain ⟨N', g, hg, hp, hq, U, hU10, hU00, hfac⟩ := fourContraction_factor M
    have hk : g * (2 * N' 0 0 * M 1 1 - M 0 1 * N' 1 0) = 2 := by
      have hM : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact M.det_coe
      linear_combination 2 * (M 1 1) * hp.symm - M 0 1 * hq.symm + 2 * hM
    have hg4 := norm_sq_le_four_of_mul hk
    have hg1 := one_le_norm_sq_ringComplex hg
    obtain ⟨z', v', hv', hpt⟩ := upperPoint_surjective (U • upperPoint z v hv)
    have hvv : v' = v * (‖ringComplex g‖ ^ 2 / 2) := by
      have h := height_upper_triangular_complex U hU10 z v hv
      rw [← hpt, hyperbolicHeight_upperPoint, hU00] at h
      exact h
    have hcol : colRes (N' 0 0) (N' 1 0) ≠ 0 := by
      refine colRes_ne_zero_of_factor hp hq ?_
      rw [colRes_two_right]
      exact mul_ne_zero (by decide) hM
    rw [← mul_smul, hfac, mul_smul, ← hpt]
    have hav' : a / 2 ≤ v' := by rw [hvv]; nlinarith
    refine (hdec N' hcol z' v' hv' hav').trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
    rw [hvv]
    nlinarith [mul_nonneg (mul_nonneg hβ.le hv.le) (sub_nonneg.mpr hg1)]

end GaloisForLFunctions.OrderSixMetaplecticTheory
