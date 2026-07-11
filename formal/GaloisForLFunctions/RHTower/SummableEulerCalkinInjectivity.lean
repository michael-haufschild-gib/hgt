import GaloisForLFunctions.RHTower.FiniteEulerCalkinIndependence

/-!
# Summable Euler Calkin injectivity

The finite scaled-shell separation theorem extends to every nonzero absolutely summable family at
strictly increasing scales. Consequently no nonzero operator-norm convergent additive series of
positive Euler metric corners becomes compact. The result is proved on ambient `L²(ℝ)`, restricted
to the actual even Sonin carrier, and transported to the concrete archimedean
Hardy--Titchmarsh line.

This theorem concerns `ℓ¹` additive renormalizations. It does not cover conditionally summed Euler
series, multiplicative phase-ratio products, or regulator-dependent all-place limits.
-/

noncomputable section

open MeasureTheory Set
open Filter Topology
open scoped InnerProduct InnerProductSpace

namespace RHTower

theorem norm_dilationSum_le_two (r : ℝ) (hr : 1 < r) :
    ‖dilationSum r hr‖ ≤ 2 := by
  apply (dilationSum r hr).opNorm_le_bound (by norm_num)
  intro f
  rw [dilationSum_apply]
  calc
    ‖dilation r (zero_lt_one.trans hr) f +
        dilation r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) f‖
        ≤ ‖dilation r (zero_lt_one.trans hr) f‖ +
          ‖dilation r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) f‖ := norm_add_le _ _
    _ = 2 * ‖f‖ := by
      rw [(dilation r (zero_lt_one.trans hr)).norm_map,
        (dilation r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))).norm_map]
      ring

theorem summable_smul_dilationSum
    (r : ℕ → ℝ) (hr : ∀ j, 1 < r j) (c : ℕ → ℂ)
    (hc : Summable fun j => ‖c j‖) :
    Summable fun j => c j • dilationSum (r j) (hr j) := by
  apply Summable.of_norm_bounded (Summable.mul_left 2 hc)
  intro j
  calc
    ‖c j • dilationSum (r j) (hr j)‖
        ≤ ‖c j‖ * ‖dilationSum (r j) (hr j)‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖c j‖ * 2 := mul_le_mul_of_nonneg_left
      (norm_dilationSum_le_two (r j) (hr j)) (norm_nonneg _)
    _ = 2 * ‖c j‖ := by ring

/-- The operator-norm convergent symmetric-dilation series. -/
def summableDilationCombination
    (r : ℕ → ℝ) (hr : ∀ j, 1 < r j) (c : ℕ → ℂ) :
    SoninL2 →L[ℂ] SoninL2 :=
  ∑' j, c j • dilationSum (r j) (hr j)

theorem exists_strictMono_separatingShellUpper
    {a : ℝ} (r : ℕ → ℝ) (hr : ∀ j, 1 < r j) (hmono : StrictMono r)
    (k : ℕ) (ha : 0 < a) :
    ∃ b : ℝ, a < b ∧ b ≤ r k * a ∧
      ∀ j, k < j → b * r k < a * r j := by
  have hk0 : 0 < r k := zero_lt_one.trans (hr k)
  have hnext : r k < r (k + 1) := hmono (Nat.lt_succ_self k)
  let u : ℝ := min (r k * a) (a * r (k + 1) / r k)
  have hau : a < u := by
    rw [lt_min_iff]
    constructor
    · nlinarith [hr k]
    · rw [lt_div_iff₀ hk0]
      nlinarith
  let b : ℝ := (a + u) / 2
  have hab : a < b := by dsimp [b]; linarith
  have hbu : b < u := by dsimp [b]; linarith
  refine ⟨b, hab, hbu.le.trans (min_le_left _ _), ?_⟩
  intro j hkj
  have hsucc : k + 1 ≤ j := Nat.succ_le_iff.mpr hkj
  have hscale : r (k + 1) ≤ r j := hmono.monotone hsucc
  have hub : u ≤ a * r (k + 1) / r k := min_le_right _ _
  have hbnext : b * r k < a * r (k + 1) := by
    rw [← lt_div_iff₀ hk0]
    exact hbu.trans_le hub
  nlinarith

set_option maxHeartbeats 4000000 in
theorem scaledEvenShellCutoff_summableDilationCombination_apply
    {a b : ℝ} (r : ℕ → ℝ) (hr : ∀ j, 1 < r j)
    (hmono : StrictMono r) (c : ℕ → ℂ) (hc : Summable fun j => ‖c j‖)
    (k : ℕ) (hk : c k ≠ 0) (hmin : ∀ j, j < k → c j = 0)
    (ha : 0 < a) (hab : a < b) (hba : b ≤ r k * a)
    (hsep : ∀ j, k < j → b * r k < a * r j) (m : ℕ) :
    scaledEvenShellCutoff (r k) a b
        (summableDilationCombination r hr c (evenShellVector a b ha hab m)) =
      c k • dilation (r k) (zero_lt_one.trans (hr k))
        (evenShellVector a b ha hab m) := by
  let g := evenShellVector a b ha hab m
  let A := scaledEvenShellCutoff (r k) a b
  have hterms := summable_smul_dilationSum r hr c hc
  have heval : Summable fun j => (c j • dilationSum (r j) (hr j)) g :=
    (ContinuousLinearMap.apply ℂ SoninL2 g).summable hterms
  calc
    A (summableDilationCombination r hr c g) =
        A (∑' j, (c j • dilationSum (r j) (hr j)) g) := by
      rw [summableDilationCombination,
        (ContinuousLinearMap.apply ℂ SoninL2 g).map_tsum hterms]
    _ = ∑' j, A ((c j • dilationSum (r j) (hr j)) g) := by
      rw [A.map_tsum heval]
    _ = A ((c k • dilationSum (r k) (hr k)) g) := by
      rw [tsum_eq_single k]
      intro j hj
      by_cases hjk : j < k
      · simp [hmin j hjk]
      · have hkj : k < j := lt_of_le_of_ne (Nat.le_of_not_gt hjk) hj.symm
        have hk0 : 0 < r k := zero_lt_one.trans (hr k)
        have hj0 : 0 < r j := zero_lt_one.trans (hr j)
        rw [ContinuousLinearMap.smul_apply, dilationSum_apply, map_smul, map_add,
          scaledEvenShellCutoff_offtarget_inward hk0 hj0 ha hab (hsep j hkj) m,
          scaledEvenShellCutoff_outward hk0 (hr j) ha hab hba m]
        simp
    _ = c k • dilation (r k) (zero_lt_one.trans (hr k)) g := by
      have hk0 : 0 < r k := zero_lt_one.trans (hr k)
      rw [ContinuousLinearMap.smul_apply, dilationSum_apply, map_smul, map_add,
        scaledEvenShellCutoff_target_inward hk0 ha hab m,
        scaledEvenShellCutoff_outward hk0 (hr k) ha hab hba m]
      simp

/-- **Summable Calkin injectivity.** Every nonzero absolutely summable combination of an increasing
family of dilation corners remains noncompact. -/
theorem summableDilationCorners_calkinInjective
    {a : ℝ} (r : ℕ → ℝ) (hr : ∀ j, 1 < r j) (hmono : StrictMono r)
    (c : ℕ → ℂ) (hc : Summable fun j => ‖c j‖) (ha : 0 < a)
    (hne : ∃ j, c j ≠ 0) :
    ¬ IsCompactOperator
      (crossBoundary (centralSoninProjection a)
        (summableDilationCombination r hr c) : SoninL2 →L[ℂ] SoninL2) := by
  let k := Nat.find hne
  have hk : c k ≠ 0 := Nat.find_spec hne
  have hmin : ∀ j, j < k → c j = 0 := by
    intro j hj
    by_contra hcj
    exact (not_le_of_gt hj) (Nat.find_min' hne hcj)
  obtain ⟨b, hab, hba, hsep⟩ :=
    exists_strictMono_separatingShellUpper r hr hmono k ha
  apply centralSoninCorner_not_isCompactOperator_of_scaledShell_norm
    ha hab (zero_lt_one.trans (hr k)) hba (norm_pos_iff.mpr hk)
    (summableDilationCombination r hr c)
  intro m
  rw [scaledEvenShellCutoff_summableDilationCombination_apply
    r hr hmono c hc k hk hmin ha hab hba hsep m]
  rw [norm_smul, (dilation (r k) (zero_lt_one.trans (hr k))).norm_map,
    (evenShellVector_orthonormal a b ha hab).norm_eq_one m, mul_one]

theorem norm_evenDilationSum_le_two (r : ℝ) (hr : 1 < r) :
    ‖evenDilationSum r hr‖ ≤ 2 := by
  apply (evenDilationSum r hr).opNorm_le_bound (by norm_num)
  intro f
  change ‖dilationSum r hr (f : SoninL2)‖ ≤ 2 * ‖(f : SoninL2)‖
  exact (dilationSum r hr).le_opNorm f |>.trans
    (mul_le_mul_of_nonneg_right (norm_dilationSum_le_two r hr) (norm_nonneg _))

theorem summable_smul_evenDilationSum
    (r : ℕ → ℝ) (hr : ∀ j, 1 < r j) (c : ℕ → ℂ)
    (hc : Summable fun j => ‖c j‖) :
    Summable fun j => c j • evenDilationSum (r j) (hr j) := by
  apply Summable.of_norm_bounded (Summable.mul_left 2 hc)
  intro j
  calc
    ‖c j • evenDilationSum (r j) (hr j)‖
        ≤ ‖c j‖ * ‖evenDilationSum (r j) (hr j)‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖c j‖ * 2 := mul_le_mul_of_nonneg_left
      (norm_evenDilationSum_le_two (r j) (hr j)) (norm_nonneg _)
    _ = 2 * ‖c j‖ := by ring

/-- The operator-norm convergent symmetric-dilation series on the actual even carrier. -/
def summableEvenDilationCombination
    (r : ℕ → ℝ) (hr : ∀ j, 1 < r j) (c : ℕ → ℂ) :
    evenSubspace →L[ℂ] evenSubspace :=
  ∑' j, c j • evenDilationSum (r j) (hr j)

theorem summableEvenDilationCombination_coe_apply
    (r : ℕ → ℝ) (hr : ∀ j, 1 < r j) (c : ℕ → ℂ)
    (hc : Summable fun j => ‖c j‖) (f : evenSubspace) :
    ((summableEvenDilationCombination r hr c f : evenSubspace) : SoninL2) =
      summableDilationCombination r hr c f := by
  have heven := summable_smul_evenDilationSum r hr c hc
  have hamb := summable_smul_dilationSum r hr c hc
  change (evenSubspace.subtype : evenSubspace →ₗ[ℂ] SoninL2)
      ((∑' j, c j • evenDilationSum (r j) (hr j)) f) =
    (∑' j, c j • dilationSum (r j) (hr j)) (f : SoninL2)
  rw [(ContinuousLinearMap.apply ℂ evenSubspace f).map_tsum heven,
    (ContinuousLinearMap.apply ℂ SoninL2 (f : SoninL2)).map_tsum hamb]
  rw [(evenSubspace.subtypeL).map_tsum
    ((ContinuousLinearMap.apply ℂ evenSubspace f).summable heven)]
  apply tsum_congr
  intro j
  simp

/-- The lower corner of the summable dilation series on the actual even Sonin carrier. -/
def summableEvenDilationCorner
    (a : ℝ) (r : ℕ → ℝ) (hr : ∀ j, 1 < r j) (c : ℕ → ℂ) :
    evenSubspace →L[ℂ] evenSubspace :=
  crossBoundary (evenCentralSoninProjection a)
    (summableEvenDilationCombination r hr c)

set_option maxHeartbeats 2400000 in
/-- Summable Calkin injectivity persists on the actual even Sonin carrier. -/
theorem summableEvenDilationCorner_not_isCompactOperator
    {a : ℝ} (r : ℕ → ℝ) (hr : ∀ j, 1 < r j) (hmono : StrictMono r)
    (c : ℕ → ℂ) (hc : Summable fun j => ‖c j‖) (ha : 0 < a)
    (hne : ∃ j, c j ≠ 0) :
    ¬ IsCompactOperator (summableEvenDilationCorner a r hr c) := by
  let W : SoninL2 →L[ℂ] SoninL2 := summableDilationCombination r hr c
  let E : SoninL2 →L[ℂ] SoninL2 := evenProjection
  let WEven : SoninL2 →L[ℂ] SoninL2 := W ∘L E
  let k := Nat.find hne
  have hk : c k ≠ 0 := Nat.find_spec hne
  have hmin : ∀ j, j < k → c j = 0 := by
    intro j hj
    by_contra hcj
    exact (not_le_of_gt hj) (Nat.find_min' hne hcj)
  obtain ⟨b, hab, hba, hsep⟩ :=
    exists_strictMono_separatingShellUpper r hr hmono k ha
  have hnon : ¬ IsCompactOperator
      (crossBoundary (centralSoninProjection a) WEven : SoninL2 →L[ℂ] SoninL2) := by
    apply centralSoninCorner_not_isCompactOperator_of_scaledShell_norm
      ha hab (zero_lt_one.trans (hr k)) hba (norm_pos_iff.mpr hk) WEven
    intro m
    have heven : evenProjection (evenShellVector a b ha hab m) =
        evenShellVector a b ha hab m := by
      rw [evenProjection_apply, l2Reflection_evenShellVector a b ha hab m]
      module
    simpa [WEven, W, E, heven] using
      congrArg norm (scaledEvenShellCutoff_summableDilationCombination_apply
        r hr hmono c hc k hk hmin ha hab hba hsep m)
  intro hcompact
  have hextCompact : IsCompactOperator
      (evenSubspace.subtypeL ∘L summableEvenDilationCorner a r hr c ∘L
        evenProjectionToEven : SoninL2 →L[ℂ] SoninL2) := by
    exact (hcompact.comp_clm evenProjectionToEven).clm_comp evenSubspace.subtypeL
  apply hnon
  have heq :
      (evenSubspace.subtypeL ∘L summableEvenDilationCorner a r hr c ∘L
        evenProjectionToEven : SoninL2 →L[ℂ] SoninL2) =
      (crossBoundary (centralSoninProjection a) WEven : SoninL2 →L[ℂ] SoninL2) := by
    apply ContinuousLinearMap.ext
    intro f
    have hQE : centralSoninProjection a (E f) =
        E (centralSoninProjection a f) := by
      simpa [E] using
        DFunLike.congr_fun (centralSoninProjection_evenProjection_commute a) f
    change ((summableEvenDilationCorner a r hr c (evenProjectionToEven f) :
        evenSubspace) : SoninL2) = _
    simp only [summableEvenDilationCorner, crossBoundary,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.sub_apply]
    rw [summableEvenDilationCombination_coe_apply r hr c hc]
    rw [summableEvenDilationCombination_coe_apply r hr c hc]
    change W (centralSoninProjection a (E f)) -
        centralSoninProjection a (W (centralSoninProjection a (E f))) =
      W (E (centralSoninProjection a f)) -
        centralSoninProjection a (W (E (centralSoninProjection a f)))
    rw [hQE]
  rw [← heq]
  exact hextCompact

/-- The summable positive-Euler metric corner series, after its constant parts vanish at the
boundary. -/
def summableEvenPositiveEulerCorner
    (a : ℝ) (r : ℕ → ℝ) (hr : ∀ j, 1 < r j) (c : ℕ → ℂ) :
    evenSubspace →L[ℂ] evenSubspace :=
  summableEvenDilationCorner a r hr
    (fun j => c j * (-((Real.sqrt (r j) : ℂ)⁻¹)))

theorem summable_norm_eulerScaled
    (r : ℕ → ℝ) (hr : ∀ j, 1 < r j) (c : ℕ → ℂ)
    (hc : Summable fun j => ‖c j‖) :
    Summable fun j => ‖c j * (-((Real.sqrt (r j) : ℂ)⁻¹))‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hc
  intro j
  rw [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.2 (zero_lt_one.trans (hr j)))]
  have hsqrt : 1 ≤ Real.sqrt (r j) :=
    Real.one_le_sqrt.mpr (by linarith [hr j])
  have hinv : (Real.sqrt (r j))⁻¹ ≤ 1 :=
    (inv_le_one₀ (Real.sqrt_pos.2 (zero_lt_one.trans (hr j)))).mpr hsqrt
  nlinarith [norm_nonneg (c j)]

/-- Every nonzero absolutely summable positive-Euler metric series has a noncompact lower corner on
the actual even carrier. -/
theorem summableEvenPositiveEulerCorner_not_isCompactOperator
    {a : ℝ} (r : ℕ → ℝ) (hr : ∀ j, 1 < r j) (hmono : StrictMono r)
    (c : ℕ → ℂ) (hc : Summable fun j => ‖c j‖) (ha : 0 < a)
    (hne : ∃ j, c j ≠ 0) :
    ¬ IsCompactOperator (summableEvenPositiveEulerCorner a r hr c) := by
  apply summableEvenDilationCorner_not_isCompactOperator r hr hmono
    (fun j => c j * (-((Real.sqrt (r j) : ℂ)⁻¹)))
    (summable_norm_eulerScaled r hr c hc) ha
  obtain ⟨j, hcj⟩ := hne
  refine ⟨j, mul_ne_zero hcj ?_⟩
  simp [Real.sqrt_ne_zero'.mpr (zero_lt_one.trans (hr j))]

/-- The summable positive Euler corner series on the concrete archimedean Hardy--Titchmarsh line. -/
def summableArchimedeanPositiveEulerCorner
    (a : ℝ) (r : ℕ → ℝ) (hr : ∀ j, 1 < r j) (c : ℕ → ℂ) :
    ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2 :=
  unitaryPush archimedeanDualHardyTitchmarshUnitary
    (summableEvenPositiveEulerCorner a r hr c)

/-- **Infinite source theorem.** Every nonzero absolutely summable positive-Euler metric series at
strictly increasing scales has a noncompact lower corner on the concrete Hardy--Titchmarsh line. -/
theorem summableArchimedeanPositiveEulerCorner_not_isCompactOperator
    {a : ℝ} (r : ℕ → ℝ) (hr : ∀ j, 1 < r j) (hmono : StrictMono r)
    (c : ℕ → ℂ) (hc : Summable fun j => ‖c j‖) (ha : 0 < a)
    (hne : ∃ j, c j ≠ 0) :
    ¬ IsCompactOperator (summableArchimedeanPositiveEulerCorner a r hr c) := by
  rw [summableArchimedeanPositiveEulerCorner]
  intro hcompact
  apply summableEvenPositiveEulerCorner_not_isCompactOperator
    r hr hmono c hc ha hne
  have hpull := (hcompact.comp_clm
    (archimedeanDualHardyTitchmarshUnitary :
      evenSubspace →L[ℂ] ArchimedeanWeightedL2)).clm_comp
    (archimedeanDualHardyTitchmarshUnitary.symm :
      ArchimedeanWeightedL2 →L[ℂ] evenSubspace)
  simpa [unitaryPush, Function.comp_def] using hpull

end RHTower
