import GaloisForLFunctions.RHTower.ProlateSmallApertureFullIndexedModeFlag

open MeasureTheory Filter Topology Set Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry
open _root_.RHTower

theorem complexUnitBandValue_eq_c_mul_fullSingular_sq
    {c : ℝ} (hc : 0 < c) (k : ℕ) :
    complexUnitBandValue c k =
      (c / (2 * Real.pi)) * indexedFullSlepianSingularValue c k ^ (2 : ℕ) := by
  have h := rectApproxNumber_apertureMomentSynthesis_sq_eq_scaled_bandValue hc k
  field_simp [hc.ne', Real.pi_ne_zero] at h ⊢
  nlinarith

/-- Every full indexed fixed-unit Slepian eigenvalue has exact small-aperture
birth order `c^(2k+1)`. -/
theorem exists_pos_eventually_complexUnitBandValue_twoSided (k : ℕ) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
        A * c ^ (2 * k + 1) ≤ complexUnitBandValue c k ∧
          complexUnitBandValue c k ≤ B * c ^ (2 * k + 1) := by
  obtain ⟨C, D, hC, hD, hbounds⟩ :=
    exists_pos_eventually_rectApproxNumber_full_twoSided k
  let A : ℝ := C ^ (2 : ℕ) / (2 * Real.pi)
  let B : ℝ := D ^ (2 : ℕ) / (2 * Real.pi)
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨A, B, hA, hB, ?_⟩
  have hmono : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_mono 0 (by intro c hc; exact ne_of_gt hc)
  filter_upwards [hmono hbounds, self_mem_nhdsWithin]
    with c hcBounds hc
  have hcAbs : |c| = c := abs_of_pos hc
  rw [hcAbs] at hcBounds
  let s : ℝ := indexedFullSlepianSingularValue c k
  have hs0 : 0 ≤ s := rectApproxNumber_nonneg _ _
  have hlowSq : (C * c ^ k) ^ (2 : ℕ) ≤ s ^ (2 : ℕ) :=
    pow_le_pow_left₀ (mul_nonneg hC.le (pow_nonneg hc.le _)) hcBounds.1 2
  have huppSq : s ^ (2 : ℕ) ≤ (D * c ^ k) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hs0 hcBounds.2 2
  have hpow : c ^ (2 * k + 1) = c * (c ^ k) ^ (2 : ℕ) := by
    calc
      c ^ (2 * k + 1) = c ^ (1 + k * 2) := by congr 1; omega
      _ = c ^ (1 : ℕ) * c ^ (k * 2) := pow_add _ _ _
      _ = c * (c ^ k) ^ (2 : ℕ) := by rw [pow_one, pow_mul]
  rw [complexUnitBandValue_eq_c_mul_fullSingular_sq hc k]
  change A * c ^ (2 * k + 1) ≤ (c / (2 * Real.pi)) * s ^ (2 : ℕ) ∧
    (c / (2 * Real.pi)) * s ^ (2 : ℕ) ≤ B * c ^ (2 * k + 1)
  constructor
  · calc
      A * c ^ (2 * k + 1) =
          (c / (2 * Real.pi)) * (C * c ^ k) ^ (2 : ℕ) := by
        dsimp [A]
        rw [hpow]
        field_simp [Real.pi_ne_zero]
      _ ≤ (c / (2 * Real.pi)) * s ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hlowSq
          (div_nonneg hc.le (mul_nonneg (by norm_num) Real.pi_pos.le))
  · calc
      (c / (2 * Real.pi)) * s ^ (2 : ℕ) ≤
          (c / (2 * Real.pi)) * (D * c ^ k) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left huppSq
          (div_nonneg hc.le (mul_nonneg (by norm_num) Real.pi_pos.le))
      _ = B * c ^ (2 * k + 1) := by
        dsimp [B]
        rw [hpow]
        field_simp [Real.pi_ne_zero]

/-- Every even-block value occurs in the full fixed-unit spectrum. -/
theorem exists_complexUnitBandValue_eq_evenValue
    {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ∃ k : ℕ, complexUnitBandValue c k = complexUnitBandEvenValue c n := by
  let S := complexUnitBandEvenBlock c
  let z : complexUnitBandEvenSubspace := ContinuousLinearMap.sgVec S n
  have hzNorm : ‖z‖ = 1 := indexedEvenSlepianInputMode_norm hc n
  have hzNe : z ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hzNorm
    norm_num at hzNorm
  have hzEigBlock : S z =
      (complexUnitBandEvenValue c n : ℂ) • z := by
    exact indexedEvenSlepianInputMode_eigen hc n
  have hzEigFull : complexBandOperatorL2 c (z : ComplexUnitIntervalL2) =
      (complexUnitBandEvenValue c n : ℂ) • (z : ComplexUnitIntervalL2) := by
    have h := congrArg
      (fun w : complexUnitBandEvenSubspace => (w : ComplexUnitIntervalL2))
      hzEigBlock
    rwa [coe_complexUnitBandEvenBlock_apply] at h
  have hzNeFull : (z : ComplexUnitIntervalL2) ≠ 0 := by
    intro hz0
    exact hzNe (Subtype.ext hz0)
  have hvalNe : (complexUnitBandEvenValue c n : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (complexUnitBandEvenValue_pos_of_pos hc n)
  obtain ⟨k, hk⟩ := ContinuousLinearMap.exists_sgVal_eq_of_eigenvalue
    (isCompactOperator_complexBandOperatorL2 c)
    (complexBandOperatorL2_isPositive hc).isSymmetric hzNeFull hzEigFull hvalNe
  refine ⟨k, ?_⟩
  rw [complexUnitBandValue_eq_sgVal hc]
  exact Complex.ofReal_injective hk

/-- A positive birth law dominates every law two powers later on the positive
small-aperture germ. -/
theorem eventually_lt_of_birth_order_succ_two
    {f g : ℝ → ℝ} {p : ℕ} {A B : ℝ}
    (hA : 0 < A) (_hB : 0 < B)
    (hf : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ), A * c ^ p ≤ f c)
    (hg : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ), g c ≤ B * c ^ (p + 2)) :
    ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ), g c < f c := by
  let L := 𝓝[>] (0 : ℝ)
  have hsq : Tendsto (fun c : ℝ => B * c ^ (2 : ℕ)) L (nhds 0) := by
    have h0 : Tendsto (fun c : ℝ => c ^ (2 : ℕ)) L (nhds 0) := by
      simpa [L] using
        (continuousAt_pow (0 : ℝ) 2).tendsto.mono_left
          (show L ≤ 𝓝 (0 : ℝ) from inf_le_left)
    simpa using tendsto_const_nhds.mul h0
  have hsmall : ∀ᶠ c : ℝ in L, B * c ^ (2 : ℕ) < A :=
    (tendsto_order.1 hsq).2 A hA
  filter_upwards [hf, hg, hsmall, self_mem_nhdsWithin]
    with c hflow hgup hsmall hc
  have hpow : c ^ (p + 2) = c ^ p * c ^ (2 : ℕ) := pow_add c p 2
  calc
    g c ≤ B * c ^ (p + 2) := hgup
    _ = c ^ p * (B * c ^ (2 : ℕ)) := by rw [hpow]; ring
    _ < c ^ p * A :=
      mul_lt_mul_of_pos_left hsmall (pow_pos hc p)
    _ = A * c ^ p := by ring
    _ ≤ f c := hflow

theorem eventually_full_next_lt_evenValue (n : ℕ) :
    ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      complexUnitBandValue c (2 * n + 1) < complexUnitBandEvenValue c n := by
  obtain ⟨Ae, _Be, hAe, _hBe, he⟩ :=
    exists_pos_eventually_complexUnitBandEvenValue_twoSided n
  obtain ⟨_Af, Bf, _hAf, hBf, hf⟩ :=
    exists_pos_eventually_complexUnitBandValue_twoSided (2 * n + 1)
  have helower : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      Ae * c ^ (4 * n + 1) ≤ complexUnitBandEvenValue c n :=
    he.mono fun _ hc => hc.1
  have hfupper : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      complexUnitBandValue c (2 * n + 1) ≤
        Bf * c ^ ((4 * n + 1) + 2) := by
    filter_upwards [hf] with c hc
    simpa only [show 2 * (2 * n + 1) + 1 = (4 * n + 1) + 2 by omega]
      using hc.2
  exact eventually_lt_of_birth_order_succ_two hAe hBf helower hfupper

theorem eventually_evenValue_lt_full_previous
    {n : ℕ} (hn : 0 < n) :
    ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      complexUnitBandEvenValue c n < complexUnitBandValue c (2 * n - 1) := by
  obtain ⟨_Ae, Be, _hAe, hBe, he⟩ :=
    exists_pos_eventually_complexUnitBandEvenValue_twoSided n
  obtain ⟨Af, _Bf, hAf, _hBf, hf⟩ :=
    exists_pos_eventually_complexUnitBandValue_twoSided (2 * n - 1)
  have hflower : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      Af * c ^ (4 * n - 1) ≤ complexUnitBandValue c (2 * n - 1) := by
    filter_upwards [hf] with c hc
    simpa only [show 2 * (2 * n - 1) + 1 = 4 * n - 1 by omega]
      using hc.1
  have heupper : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      complexUnitBandEvenValue c n ≤ Be * c ^ ((4 * n - 1) + 2) := by
    filter_upwards [he] with c hc
    simpa only [show (4 * n - 1) + 2 = 4 * n + 1 by omega]
      using hc.2
  exact eventually_lt_of_birth_order_succ_two hAf hBe hflower heupper

/-- Small-aperture parity rank law: the `n`th even Slepian value is exactly the
`2n`th value of the full fixed-unit spectrum.  This is an index theorem, not a
subsequence relabelling: adjacent sharp birth orders exclude every other rank. -/
theorem eventually_complexUnitBandValue_two_mul_eq_evenValue (n : ℕ) :
    ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      complexUnitBandValue c (2 * n) = complexUnitBandEvenValue c n := by
  have hnext := eventually_full_next_lt_evenValue n
  rcases eq_or_lt_of_le (Nat.zero_le n) with hn0 | hnpos
  · subst n
    filter_upwards [hnext, self_mem_nhdsWithin] with c hnext hc
    obtain ⟨k, hk⟩ := exists_complexUnitBandValue_eq_evenValue hc 0
    have hk0 : k = 0 := by
      by_contra hkne
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hkne
      have hmono : complexUnitBandValue c k ≤ complexUnitBandValue c 1 := by
        exact approxNumber_antitone (complexBandOperatorL2 c) hk1
      have : complexUnitBandValue c k < complexUnitBandEvenValue c 0 :=
        lt_of_le_of_lt hmono (by simpa using hnext)
      linarith
    simpa [hk0] using hk
  · have hprev := eventually_evenValue_lt_full_previous hnpos
    filter_upwards [hnext, hprev, self_mem_nhdsWithin]
      with c hnext hprev hc
    obtain ⟨k, hk⟩ := exists_complexUnitBandValue_eq_evenValue hc n
    have hkEq : k = 2 * n := by
      by_contra hkne
      rcases lt_or_gt_of_ne hkne with hklt | hkgt
      · have hkle : k ≤ 2 * n - 1 := by omega
        have hmono : complexUnitBandValue c (2 * n - 1) ≤
            complexUnitBandValue c k := by
          exact approxNumber_antitone (complexBandOperatorL2 c) hkle
        have : complexUnitBandEvenValue c n < complexUnitBandValue c k :=
          lt_of_lt_of_le hprev hmono
        linarith
      · have hge : 2 * n + 1 ≤ k := by omega
        have hmono : complexUnitBandValue c k ≤
            complexUnitBandValue c (2 * n + 1) := by
          exact approxNumber_antitone (complexBandOperatorL2 c) hge
        have : complexUnitBandValue c k < complexUnitBandEvenValue c n :=
          lt_of_le_of_lt hmono hnext
        linarith
    simpa [hkEq] using hk

theorem exists_unit_phase_evenOutput_eq_fullOutput
    {c : ℝ} (hc : 0 < c) (n : ℕ)
    (hvalue : complexUnitBandValue c (2 * n) =
      complexUnitBandEvenValue c n)
    (hsfull : 0 < indexedFullSlepianSingularValue c (2 * n)) :
    ∃ z : ℂ, ‖z‖ = 1 ∧
      indexedEvenSlepianOutputMode c n =
        z • indexedFullSlepianOutputMode c (2 * n) ∧
      indexedEvenMomentAlignmentCoeff c n =
        z * indexedFullMomentAlignmentCoeff c (2 * n) := by
  let xf := indexedFullSlepianInputMode c (2 * n)
  let xe : ComplexUnitIntervalL2 :=
    ((indexedEvenSlepianInputMode c n : complexUnitBandEvenSubspace) :
      ComplexUnitIntervalL2)
  have hxfNorm : ‖xf‖ = 1 :=
    indexedFullSlepianInputMode_norm_of_singularValue_pos hc hsfull
  have hxeNorm : ‖xe‖ = 1 := by
    exact indexedEvenSlepianInputMode_norm hc n
  have hxfNe : xf ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hxfNorm
    norm_num at hxfNorm
  have hxeNe : xe ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hxeNorm
    norm_num at hxeNorm
  have hxfEig : complexBandOperatorL2 c xf =
      (complexUnitBandEvenValue c n : ℂ) • xf := by
    rw [← hvalue]
    exact indexedFullSlepianInputMode_eigen hc (2 * n)
  have hxeEig : complexBandOperatorL2 c xe =
      (complexUnitBandEvenValue c n : ℂ) • xe := by
    have hblock := indexedEvenSlepianInputMode_eigen hc n
    have h := congrArg
      (fun w : complexUnitBandEvenSubspace => (w : ComplexUnitIntervalL2)) hblock
    change complexBandOperatorL2 c
        ((indexedEvenSlepianInputMode c n : complexUnitBandEvenSubspace) :
          ComplexUnitIntervalL2) =
      (complexUnitBandEvenValue c n : ℂ) •
        ((indexedEvenSlepianInputMode c n : complexUnitBandEvenSubspace) :
          ComplexUnitIntervalL2)
    calc
      complexBandOperatorL2 c
          ((indexedEvenSlepianInputMode c n : complexUnitBandEvenSubspace) :
            ComplexUnitIntervalL2) =
        (((complexUnitBandEvenValue c n : ℂ) •
          indexedEvenSlepianInputMode c n : complexUnitBandEvenSubspace) :
            ComplexUnitIntervalL2) := by
          simpa only [coe_complexUnitBandEvenBlock_apply] using h
      _ = _ := rfl
  have hvalNe : complexUnitBandEvenValue c n ≠ 0 :=
    ne_of_gt (complexUnitBandEvenValue_pos_of_pos hc n)
  obtain ⟨z, hz⟩ := complexBandOperatorL2_eigenvectors_proportional
    hc hvalNe hxfNe hxfEig hxeEig
  have hzNorm : ‖z‖ = 1 := by
    have hnorm := congrArg norm hz
    rw [norm_smul, hxfNorm, mul_one, hxeNorm] at hnorm
    exact hnorm.symm
  have hsEq : indexedFullSlepianSingularValue c (2 * n) =
      indexedEvenSlepianSingularValue c n := by
    have hfull :=
      rectApproxNumber_apertureMomentSynthesis_sq_eq_scaled_bandValue hc (2 * n)
    have heven := rectApproxNumber_complexEven_sq_eq_scaled_evenValue hc n
    change indexedEvenSlepianSingularValue c n ^ (2 : ℕ) =
      (2 * Real.pi / c) * complexUnitBandEvenValue c n at heven
    have hseven := indexedEvenSlepianSingularValue_pos hc n
    rw [hvalue] at hfull
    nlinarith
  have hsyn : complexEvenApertureMomentSynthesis c
        (indexedEvenSlepianInputMode c n) =
      apertureMomentFourierSynthesis 0 c xe := by
    rfl
  have hy : indexedEvenSlepianOutputMode c n =
      z • indexedFullSlepianOutputMode c (2 * n) := by
    rw [indexedEvenSlepianOutputMode, indexedFullSlepianOutputMode, hsyn,
      ← hsEq]
    change ((indexedFullSlepianSingularValue c (2 * n) : ℂ)⁻¹ •
        apertureMomentFourierSynthesis 0 c xe) = _
    rw [hz, map_smul, smul_smul, smul_smul]
    congr 1
    ring
  have hcoeff : indexedEvenMomentAlignmentCoeff c n =
      z * indexedFullMomentAlignmentCoeff c (2 * n) := by
    rw [indexedEvenMomentAlignmentCoeff, indexedFullMomentAlignmentCoeff,
      ← hsEq]
    change (((c ^ (2 * n) /
        indexedFullSlepianSingularValue c (2 * n) : ℝ) : ℂ) *
          inner ℂ (physicalComplexMonomialL2 (2 * n)) xe) = _
    rw [hz, inner_smul_right]
    ring
  exact ⟨z, hzNorm, hy, hcoeff⟩

theorem eventually_norm_even_projective_eq_full (n : ℕ) :
    ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      ‖indexedEvenSlepianOutputMode c n -
        indexedEvenMomentAlignmentCoeff c n • apertureMomentFlagVector (2 * n)‖ =
      ‖indexedFullSlepianOutputMode c (2 * n) -
        indexedFullMomentAlignmentCoeff c (2 * n) •
          apertureMomentFlagVector (2 * n)‖ := by
  have hvalue := eventually_complexUnitBandValue_two_mul_eq_evenValue n
  have hsfull := eventually_indexedFullSlepianSingularValue_pos (2 * n)
  filter_upwards [hvalue, hsfull, self_mem_nhdsWithin]
    with c hvalue hsfull hc
  obtain ⟨z, hzNorm, hy, hcoeff⟩ :=
    exists_unit_phase_evenOutput_eq_fullOutput hc n hvalue hsfull
  rw [hy, hcoeff, mul_smul, ← smul_sub, norm_smul, hzNorm, one_mul]

/-- **Actual even all-rung small-aperture eigenline identification.** The
canonical `n`th even Slepian output mode converges projectively to the exact
degree-`2n` orthogonal moment line, with no subsequence or branch permutation. -/
theorem indexedEvenSlepianOutputMode_projective_flag (n : ℕ) :
    Tendsto (fun c : ℝ =>
      ‖indexedEvenSlepianOutputMode c n -
        indexedEvenMomentAlignmentCoeff c n • apertureMomentFlagVector (2 * n)‖)
      (𝓝[>] (0 : ℝ)) (nhds 0) := by
  have heq := eventually_norm_even_projective_eq_full n
  exact (indexedFullSlepianOutputMode_projective_flag (2 * n)).1.congr'
    (heq.mono fun _ h => h.symm)

/-- The actual even indexed alignment never collapses: its norm converges to
the inverse norm of the degree-`2n` moment residual. -/
theorem tendsto_norm_indexedEvenMomentAlignmentCoeff (n : ℕ) :
    Tendsto (fun c : ℝ => ‖indexedEvenMomentAlignmentCoeff c n‖)
      (𝓝[>] (0 : ℝ)) (nhds ‖apertureMomentFlagVector (2 * n)‖⁻¹) := by
  exact tendsto_norm_indexedFullMomentAlignmentCoeff_of_projective (2 * n)
    (indexedFullSlepianOutputMode_projective_flag (2 * n)).1 |>.congr' (by
      filter_upwards [eventually_complexUnitBandValue_two_mul_eq_evenValue n,
        eventually_indexedFullSlepianSingularValue_pos (2 * n),
        self_mem_nhdsWithin] with c hvalue hsfull hc
      obtain ⟨z, hzNorm, _hy, hcoeff⟩ :=
        exists_unit_phase_evenOutput_eq_fullOutput hc n hvalue hsfull
      rw [hcoeff, norm_mul, hzNorm, one_mul])

end GaloisForLFunctions.RHTower
