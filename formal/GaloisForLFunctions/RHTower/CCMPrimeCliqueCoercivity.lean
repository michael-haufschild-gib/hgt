import GaloisForLFunctions.RHTower.ThetaFinitePrimeDiagonalControl
import GaloisForLFunctions.RHTower.CCMFinitePrimeCliques
import GaloisForLFunctions.RHTower.FiniteCollectiveDiagonalGap
import GaloisForLFunctions.RHTower.CCMRealGramComplexEnergy

/-!
# Positive full Weil forms on prime-packet spaces of every finite dimension

The diagonal reserve now dominates all adverse interference. The sources,
their actual physical mass, every coupling sign, and the uniform normalized
gap are constructed internally. The collective correction is retained.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators SchwartzMap

namespace RHTower

theorem ccmWeilRealPolar_neg_right (a : SuzukiPositiveAperture) (u v : CCMArchimedeanFormDomain a) :
    ccmWeilRealPolar a u (-v) = -ccmWeilRealPolar a u v := by
  rw [ccmWeilRealPolar_symm, ccmWeilRealPolar_neg_left, ccmWeilRealPolar_symm a v u]

open ThetaSourceWard

theorem exists_cofinal_ccmPrimeClique_coercivity :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ N n : ℕ,
      ∃ (p : Fin n → ℕ) (r mu : ℝ) (a : SuzukiPositiveAperture)
        (u : CCMComplexSmoothInteriorSource a) (v : Fin n → CCMComplexSmoothInteriorSource a),
        0 < r ∧ 0 < mu ∧
        (∀ i, N ≤ p i ∧ Nat.Prime (p i)) ∧
        (∀ i j, i < j → 2 * p i < p j) ∧
        Function.support u = Metric.ball 0 r ∧
        (∀ i, Function.support (v i) = Metric.ball (Real.log (p i)) r) ∧
        let f := ccmWeilPrimeCliqueFamily u.toCCMFormVector (fun i => (v i).toCCMFormVector)
        (∀ i, ‖ccmArchimedeanFormEmbedding a (f i)‖ ^ 2 = mu) ∧
        (∀ i j, i ≠ j → 0 < ccmWeilRealPolar a (f i) (f j)) ∧
        (∀ i j, (ccmRestrictedWeilForm a (f i) (f j)).im = 0) ∧
        (∀ x : Option (Fin n) → ℝ,
          (kappa * mu) * (∑ i, x i ^ 2) +
            finiteSignedCliqueCorrection (fun i j => ccmWeilRealPolar a (f i) (f j)) x ≤
          ccmRestrictedWeilSourceQuadratic a (∑ i, (x i : ℂ) • f i)) := by
  classical
  obtain ⟨C, hC, hfamily⟩ := exists_cofinal_thetaFinitePrime_diagonal_control
  refine ⟨C / 2, half_pos hC, fun N n => ?_⟩
  obtain ⟨p, r, hr, hp, hpair, hdiag, hhub, hleaf⟩ := hfamily N n
  let phi := thetaTranslatedBumpGround r hr 0
  let psi := fun i : Fin n => thetaTranslatedBumpGround r hr (Real.log (p i))
  let mu := thetaGroundNormSq (thetaComplexify phi)
  let eta : ℝ := C / (2 * (n + 1 : ℝ))
  have hmu : 0 < mu := thetaTranslatedBumpGround_mass_pos r hr 0
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hpc := compact_thetaTranslatedBumpGround r hr 0
  have hqc (i : Fin n) := compact_thetaTranslatedBumpGround r hr (Real.log (p i))
  obtain ⟨A, hA, hbound⟩ := (hpc.union (isCompact_iUnion hqc)).isBounded.exists_pos_norm_lt
  let a : SuzukiPositiveAperture := ⟨A, hA⟩
  have hs : tsupport phi ∪ (⋃ i, tsupport (psi i)) ⊆ Ioo (-a.1) a.1 := by
    intro x hx
    exact abs_lt.mp (by simpa only [Real.norm_eq_abs] using hbound x hx)
  have hps : tsupport phi ⊆ Ioo (-a.1) a.1 := fun _ hx => hs (Or.inl hx)
  have hqs (i : Fin n) : tsupport (psi i) ⊆ Ioo (-a.1) a.1 :=
    fun _ hx => hs (Or.inr (mem_iUnion.mpr ⟨i, hx⟩))
  let u := ccmThetaSourceOfCompactRealProfile a phi hpc hps
  let v := fun i => ccmThetaSourceOfCompactRealProfile a (psi i) (hqc i) (hqs i)
  let f := ccmWeilPrimeCliqueFamily u.toCCMFormVector (fun i => (v i).toCCMFormVector)
  let M := fun i j => ccmWeilRealPolar a (f i) (f j)
  have hh (i : Fin n) : ccmWeilRealPolar a u.toCCMFormVector (v i).toCCMFormVector < 0 ∧
      |ccmWeilRealPolar a u.toCCMFormVector (v i).toCCMFormVector| ≤ eta * mu := by
    rw [ccmWeilRealPolar_compactReal_eq]
    exact hhub i
  have hl (i j : Fin n) (hij : i < j) :
      0 < ccmWeilRealPolar a (v i).toCCMFormVector (v j).toCCMFormVector ∧
      |ccmWeilRealPolar a (v i).toCCMFormVector (v j).toCCMFormVector| ≤ eta * mu := by
    rw [ccmWeilRealPolar_compactReal_eq]
    exact hleaf i j hij
  have hmasses (i : Option (Fin n)) : ‖ccmArchimedeanFormEmbedding a (f i)‖ ^ 2 = mu := by
    cases i with
    | none =>
      change ‖ccmArchimedeanFormEmbedding a (-u.toCCMFormVector)‖ ^ 2 = mu
      rw [map_neg, norm_neg]
      exact (thetaGroundNormSq_compactReal_eq_physical a phi hpc hps).symm
    | some i =>
      change ‖ccmArchimedeanFormEmbedding a (v i).toCCMFormVector‖ ^ 2 = mu
      rw [← thetaGroundNormSq_compactReal_eq_physical]
      exact thetaTranslatedBumpGround_mass r hr (Real.log (p i))
  have hdiagonal (i : Option (Fin n)) : C * mu ≤ M i i := by
    cases i with
    | none =>
      change C * mu ≤ ccmWeilRealPolar a (-u.toCCMFormVector) (-u.toCCMFormVector)
      rw [ccmWeilRealPolar_neg_left, ccmWeilRealPolar_neg_right, neg_neg,
        ccmWeilRealPolar_self, ccmCompactRealProfileEnergy_eq]
      exact hdiag 0
    | some i =>
      change C * mu ≤ ccmWeilRealPolar a (v i).toCCMFormVector (v i).toCCMFormVector
      rw [ccmWeilRealPolar_self, ccmCompactRealProfileEnergy_eq]
      exact hdiag (Real.log (p i))
  have hinteraction (i j : Option (Fin n)) (hij : i ≠ j) :
      0 < M i j ∧ |M i j| ≤ eta * mu := by
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j =>
        change 0 < ccmWeilRealPolar a (-u.toCCMFormVector) (v j).toCCMFormVector ∧ _
        simp only [M, f, ccmWeilPrimeCliqueFamily, ccmWeilRealPolar_neg_left, abs_neg]
        exact ⟨neg_pos.mpr (hh j).1, (hh j).2⟩
    | some i =>
      cases j with
      | none =>
        change 0 < ccmWeilRealPolar a (v i).toCCMFormVector (-u.toCCMFormVector) ∧ _
        simp only [M, f, ccmWeilPrimeCliqueFamily, ccmWeilRealPolar_neg_right, abs_neg]
        rw [ccmWeilRealPolar_symm a (v i).toCCMFormVector u.toCCMFormVector]
        exact ⟨neg_pos.mpr (hh i).1, (hh i).2⟩
      | some j =>
        change 0 < ccmWeilRealPolar a (v i).toCCMFormVector (v j).toCCMFormVector ∧ _
        rcases lt_trichotomy i j with h | rfl | h
        · exact hl i j h
        · exact False.elim (hij rfl)
        · simp only [M, f, ccmWeilPrimeCliqueFamily]
          rw [ccmWeilRealPolar_symm a (v i).toCCMFormVector (v j).toCCMFormVector]
          exact hl j i h
  have hureal (x : ℝ) : (u x).im = 0 := by
    simp [u, ccmThetaSourceOfCompactRealProfile_apply]
  have hvreal (i : Fin n) (x : ℝ) : (v i x).im = 0 := by
    simp [v, ccmThetaSourceOfCompactRealProfile_apply]
  have hgram (i j : Option (Fin n)) : (ccmRestrictedWeilForm a (f i) (f j)).im = 0 := by
    cases i with
    | none =>
      cases j with
      | none =>
        change (ccmRestrictedWeilForm a (-u.toCCMFormVector) (-u.toCCMFormVector)).im = 0
        rw [ccmRestrictedWeilForm_neg_left, ccmRestrictedWeilForm_neg_right, neg_neg]
        exact ccmRestrictedWeilForm_real_source_im_zero a u u hureal hureal
      | some j =>
        change (ccmRestrictedWeilForm a (-u.toCCMFormVector) (v j).toCCMFormVector).im = 0
        rw [ccmRestrictedWeilForm_neg_left, Complex.neg_im,
          ccmRestrictedWeilForm_real_source_im_zero a u (v j) hureal (hvreal j), neg_zero]
    | some i =>
      cases j with
      | none =>
        change (ccmRestrictedWeilForm a (v i).toCCMFormVector (-u.toCCMFormVector)).im = 0
        rw [ccmRestrictedWeilForm_neg_right, Complex.neg_im,
          ccmRestrictedWeilForm_real_source_im_zero a (v i) u (hvreal i) hureal, neg_zero]
      | some j =>
        exact ccmRestrictedWeilForm_real_source_im_zero a (v i) (v j) (hvreal i) (hvreal j)
  have hcoefficient : C * mu - (Fintype.card (Option (Fin n)) : ℝ) * (eta * mu) = (C / 2) * mu := by
    simp only [Fintype.card_option, Fintype.card_fin, Nat.cast_add, Nat.cast_one, eta]
    field_simp
    ring
  refine ⟨p, r, mu, a, u, v, hr, hmu, hp, hpair, ?_, ?_, hmasses,
    (fun i j hij => (hinteraction i j hij).1), hgram, ?_⟩
  · rw [support_ccmThetaSourceOfCompactRealProfile]
    exact support_thetaTranslatedBumpGround r hr 0
  · intro i
    rw [support_ccmThetaSourceOfCompactRealProfile]
    exact support_thetaTranslatedBumpGround r hr (Real.log (p i))
  · intro x
    have h := finiteSignedClique_uniform_gap M
      (fun i j => ccmWeilRealPolar_symm a (f i) (f j)) (C * mu) (eta * mu)
      (mul_pos heta hmu).le hdiagonal (fun i j hij => (hinteraction i j hij).2) x
    rwa [hcoefficient, ← ccmRestrictedWeilSourceQuadratic_real_sum] at h

end RHTower
