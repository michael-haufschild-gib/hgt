import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.OnePrimeDefectReserveCoversEveryRatioThroughTouching
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.NegativeWeilPacketsHaveExponentialConductorCutoffs

/-!
# Explicit conductor confinement through touching

The exact prime-defect counterterm and the boundary-source rate retain a
fixed positive defect fraction at every horizon at least two. Exponential
confinement therefore needs no asymptotic waiting horizon on `(0,1]`.
-/

noncomputable section
open MeasureTheory Finset
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory
  ArithmeticLorentzianGeometry ArithmeticElectrostatics SelectiveMultiscaleArithmeticPositivity

/-- The literal boundary correction has an explicit logarithmic form rate. -/
theorem exists_fullWeilNonRatioMatrix_explicit_form_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ D : ℝ, 0 < D ∧ ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ N : ℕ, 2 ≤ N →
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        |⟪Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) x, x⟫| ≤
          (D * Real.log (N + 1 : ℕ) / N) * ‖x‖ ^ 2 := by
  obtain ⟨D, hD, hbound⟩ := exists_uniform_nonRatio_budget hφ hsupp hM
  refine ⟨D, hD, fun c hc0 hc1 N hN x => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hw : 0 < c / (N : ℝ) := div_pos hc0 (by exact_mod_cast hN1)
  have hG : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw hM
  rw [fullWeilNonRatioMatrix_inner_eq hφ hsupp hM hc0 hN1 x, abs_div, abs_of_pos hG]
  simpa only [sum_primeHorizonExtension_sq] using
    hbound c hc0 hc1 N hN (primeHorizonExtension x)

private theorem hermitian_action_le_of_quadratic_bound {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℝ} (hA : A.IsHermitian) {ε : ℝ} (hε : 0 ≤ ε)
    (hform : ∀ x : EuclideanSpace ℝ I, |⟪Matrix.toEuclideanLin A x, x⟫| ≤ ε * ‖x‖ ^ 2)
    (x : EuclideanSpace ℝ I) : ‖Matrix.toEuclideanLin A x‖ ≤ ε * ‖x‖ := by
  have happ (i : I) : Matrix.toEuclideanLin A (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    ext j
    exact congrFun (hA.mulVec_eigenvectorBasis i) j
  have heig (i : I) : |hA.eigenvalues i| ≤ ε := by
    have hi : ⟪hA.eigenvectorBasis i, hA.eigenvectorBasis i⟫ = (1 : ℝ) := by
      simpa only [ite_true] using (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i i
    have hn : ‖hA.eigenvectorBasis i‖ ^ 2 = (1 : ℝ) := by
      rwa [real_inner_self_eq_norm_sq] at hi
    simpa only [happ, real_inner_smul_left, hi, hn, mul_one] using hform (hA.eigenvectorBasis i)
  have hinner (i : I) : ⟪Matrix.toEuclideanLin A x, hA.eigenvectorBasis i⟫ =
      hA.eigenvalues i * ⟪x, hA.eigenvectorBasis i⟫ := by
    rw [(Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) x (hA.eigenvectorBasis i),
      happ, real_inner_smul_right]
  have hs : ‖Matrix.toEuclideanLin A x‖ ^ 2 ≤ ε ^ 2 * ‖x‖ ^ 2 := by
    rw [← hA.eigenvectorBasis.sum_sq_inner_left (Matrix.toEuclideanLin A x),
      ← hA.eigenvectorBasis.sum_sq_inner_left x, mul_sum]
    apply sum_le_sum
    intro i hi
    rw [hinner, mul_pow]
    have hb := mul_self_le_mul_self (abs_nonneg (hA.eigenvalues i)) (heig i)
    rw [← sq, sq_abs, ← sq] at hb
    exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  have hprod : 0 ≤ ε * ‖x‖ := mul_nonneg hε (norm_nonneg x)
  nlinarith only [hs, hprod, norm_nonneg (Matrix.toEuclideanLin A x)]

/-- The complete boundary correction retains its stated rate in operator action. -/
theorem exists_fullWeilNonRatioMatrix_explicit_action_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ D : ℝ, 0 < D ∧ ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ N : ℕ, 2 ≤ N →
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        ‖Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) x‖ ≤
          (D * Real.log (N + 1 : ℕ) / N) * ‖x‖ := by
  obtain ⟨D, hD, hform⟩ := exists_fullWeilNonRatioMatrix_explicit_form_bound hφ hsupp hM
  refine ⟨D, hD, fun c hc0 hc1 N hN x => ?_⟩
  exact hermitian_action_le_of_quadratic_bound (fullWeilNonRatioMatrix_isHermitian φ c N)
    (div_nonneg (mul_nonneg hD.le (Real.log_natCast_nonneg _)) (Nat.cast_nonneg N))
    (hform c hc0 hc1 N hN) x

/-- A fixed mass cost retains half the strict charge deficit at every `N≥2`. -/
theorem exists_completeWeil_primeDefect_reserve_explicit_through_touching {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ a : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ c : ℝ, 0 < c → c ≤ 1 →
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        a * ‖x‖ ^ 2 + ((1 - completeWeilPoleShift φ 1) / 2) *
          poleDefect N (primeHorizonExtension x) ≤ completeWeilEnergy φ c N x := by
  let q := completeWeilPoleShift φ 1
  have hq0 : 0 ≤ q := completeWeilPoleShift_nonneg φ zero_le_one
  have hq1 : q < 1 := completeWeilPoleShift_lt_width hφ.continuous hsupp hM zero_lt_one
  let lam : ℝ := 2 / (1 - q)
  have hlam : 0 < lam := div_pos (by norm_num) (sub_pos.mpr hq1)
  have hK : 0 ≤ (1 + lam) * psiConstant + 15 := by
    have hp := psiConstant_pos.le
    positivity
  obtain ⟨C, hC, hcrossBound⟩ := exists_uniform_fullWeilCrossError_at_touching hφ hsupp hM
  let P := |atomPoleMomentErrorConstant φ|
  obtain ⟨D, hD, hNR⟩ := exists_fullWeilNonRatioMatrix_explicit_form_bound hφ hsupp hM
  let a := completeWeilSelfFinitePart φ 1 - Real.eulerMascheroniConstant -
    (Real.log 4 + 4) - Real.exp (1 / 2) / 2 -
    q * ((1 + lam) * psiConstant + 15) - 4 * C - 2 * P - D
  refine ⟨a, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  intro c hc0 hc1 x
  let α := completeWeilPoleShift φ c
  have hα0 : 0 ≤ α := completeWeilPoleShift_nonneg φ hc0.le
  have hαq : α ≤ q := by
    have he : α = c * q := by dsimp only [α, q, completeWeilPoleShift]; ring
    rw [he]
    exact (mul_le_mul_of_nonneg_right hc1 hq0).trans_eq (one_mul q)
  have hcoef : α * (1 + 1 / lam) ≤ (1 + q) / 2 := by
    calc
      _ ≤ q * (1 + 1 / lam) := mul_le_mul_of_nonneg_right hαq (by positivity)
      _ = q * (1 + (1 - q) / 2) := by dsimp only [lam]; rw [one_div_div]
      _ ≤ _ := by nlinarith only [sq_nonneg (1 - q)]
  have hcSq : c ^ 2 ≤ 1 := by
    simpa only [← pow_two, one_pow] using mul_le_mul hc1 hc1 hc0.le zero_le_one
  have hselfFloor : completeWeilSelfFinitePart φ 1 ≤ completeWeilSelfFinitePart φ c := by
    unfold completeWeilSelfFinitePart
    apply add_le_add ?_ le_rfl
    simp only [mul_one]
    apply Real.log_le_log (by positivity)
    exact one_div_le_one_div_of_le (by positivity)
      (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hc1 (show 0 ≤ 2 * Real.pi by positivity))
  have hP : 2 * atomPoleMomentErrorConstant φ * c ^ 2 ≤ 2 * P := by
    calc
      _ ≤ (2 * P) * c ^ 2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)) (sq_nonneg c)
      _ ≤ 2 * P := (mul_le_mul_of_nonneg_left hcSq (by dsimp only [P]; positivity)).trans_eq (mul_one _)
  have hp := atomicWeilForm_add_full_poleDefect_le N (primeHorizonExtension x)
  rw [sum_primeHorizonExtension_sq, atomicWeilForm_primeHorizonExtension] at hp
  have hcenter := fullWeilCenterMatrix_inner_ge hα0 hlam hN1 x
  have hcenterCost := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hαq hK) (sq_nonneg ‖x‖)
  have hcross := (abs_le.mp (hcrossBound c hc0 hc1 N hN1 x)).2
  have hcrossCost := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcSq (by positivity : 0 ≤ 4 * C)) (sq_nonneg ‖x‖)
  have hpole := (abs_le.mp
    (abs_fullWeilPoleErrorMatrix_inner_le_at_touching hφ hsupp hM hc0 hc1 hN1 x)).1
  have hpoleCost := mul_le_mul_of_nonneg_right hP (sq_nonneg ‖x‖)
  have hself := (abs_le.mp
    (abs_completeWeilSelfError_le_at_touching hφ hsupp hM hc0 hc1 hN1)).1
  have hw : c / (N : ℝ) ≤ 1 := (div_le_one (by exact_mod_cast hN1)).mpr
    (hc1.trans (by exact_mod_cast hN1))
  have hwidth := mul_le_mul_of_nonneg_left hw
    (show 0 ≤ Real.exp (1 / 2) / 2 by positivity)
  have hselfLower : -Real.exp (1 / 2) / 2 ≤ completeWeilSelfError φ c N := by
    linarith only [hself, hwidth]
  have hselfCost := mul_le_mul_of_nonneg_right hselfLower (sq_nonneg ‖x‖)
  have hfloorCost := mul_le_mul_of_nonneg_right hselfFloor (sq_nonneg ‖x‖)
  have hdefect := mul_le_mul_of_nonneg_right hcoef
    (poleDefect_nonneg N (primeHorizonExtension x))
  have hlog : Real.log (N + 1 : ℕ) ≤ (N : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (N + 1 : ℕ) by positivity)
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using h
  have hrate : D * Real.log (N + 1 : ℕ) / N ≤ D := by
    rw [div_le_iff₀ (show (0 : ℝ) < N by exact_mod_cast hN1)]
    exact mul_le_mul_of_nonneg_left hlog hD.le
  have hnonRatio := (abs_le.mp (hNR c hc0 hc1 N hN x)).2
  have hnonRatioCost := mul_le_mul_of_nonneg_right hrate (sq_nonneg ‖x‖)
  rw [completeWeilEnergy_eq_decomposition_at_touching hφ hsupp hM hc0 hc1 hN1]
  dsimp only [a]
  unfold renormalizedPrimeEnergy
  linarith only [hp, hcenter, hcenterCost, hcross, hcrossCost, hpole, hpoleCost,
    hselfCost, hfloorCost, hdefect, hnonRatio, hnonRatioCost]

/-- One conductor cutoff covers every nonpositive unit packet throughout `(0,1]`,
starting at the stated horizon two. -/
theorem exists_negative_completeWeil_conductor_cutoff_explicit_through_touching
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {η : ℝ} (hη : 0 < η) :
    ∃ C D : ℝ, ∃ R : ℕ, 0 ≤ C ∧ 0 < D ∧
      (R : ℝ) ≤ Real.exp (D * (C + 1)) ∧
      ∀ N : ℕ, 2 ≤ N → ∀ c : ℝ, 0 < c → c ≤ 1 →
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N), ‖x‖ = 1 →
        completeWeilEnergy φ c N x ≤ 0 → ∃ b : ℕ → ℝ,
          (∑ n ∈ Icc 1 N,
            (primeHorizonExtension x n -
              ∑ m ∈ Icc 1 R, b m * ramanujanPoleProfile m n) ^ 2) ≤ η := by
  obtain ⟨a, hreserve⟩ :=
    exists_completeWeil_primeDefect_reserve_explicit_through_touching hφ hsupp hM
  let d := (1 - completeWeilPoleShift φ 1) / 2
  have hd : 0 < d := div_pos
    (sub_pos.mpr (completeWeilPoleShift_lt_width hφ.continuous hsupp hM zero_lt_one))
    zero_lt_two
  obtain ⟨D, hD, hconf⟩ := exists_exponential_conductor_cutoff_of_poleDefect_le hη
  obtain ⟨R, hR, hcut⟩ := hconf (max 0 (-a / d)) (le_max_left _ _)
  refine ⟨max 0 (-a / d), D, R, le_max_left _ _, hD, hR,
    fun N hN c hc0 hc1 x hx he => ?_⟩
  apply hcut N (primeHorizonExtension x)
  · rw [sum_primeHorizonExtension_sq, hx, one_pow]
  · have h := hreserve N hN c hc0 hc1 x
    rw [hx, one_pow, mul_one] at h
    apply le_trans ?_ (le_max_right 0 (-a / d))
    apply (le_div_iff₀ hd).mpr
    change poleDefect N (primeHorizonExtension x) *
      ((1 - completeWeilPoleShift φ 1) / 2) ≤ -a
    linarith only [h, he]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_completeWeil_primeDefect_reserve_explicit_through_touching
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_negative_completeWeil_conductor_cutoff_explicit_through_touching
