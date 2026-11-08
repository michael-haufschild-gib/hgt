import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheLocalGammaGramIsTheAutocorrelationMatrix

/-!
# An exact resonance at overlap two

Two adjacent copies of any profile produce an alternating translate sum with
only two endpoint packets. The local Gamma Gram law transfers this cancellation
to neighboring integer atoms. For the doubled tilted spline, no positive
logarithmic Gamma reserve can hold uniformly in the coefficient square mass.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory Filter Topology Set Finset

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticIncidencePositivity
  RenormalizedArithmeticPotentialTheory.CompletedShell _root_.RHTower

/-- Two adjacent half-width copies of a profile. -/
def twoCopyProfile (ψ : ℝ → ℝ) (u : ℝ) : ℝ := ψ (2 * u) + ψ (2 * u - 1)

theorem contDiff_twoCopyProfile {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) :
    ContDiff ℝ 2 (twoCopyProfile ψ) :=
  (hψ.comp (contDiff_const.mul contDiff_id)).add
    (hψ.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))

theorem twoCopyProfile_eq_zero {ψ : ℝ → ℝ}
    (hs : ∀ u, u ∉ Set.Icc 0 1 → ψ u = 0) {u : ℝ} (hu : u ∉ Set.Icc 0 1) :
    twoCopyProfile ψ u = 0 := by
  have h1 : 2 * u ∉ Set.Icc (0 : ℝ) 1 := fun h => hu ⟨by linarith [h.1], by linarith [h.2]⟩
  have h2 : 2 * u - 1 ∉ Set.Icc (0 : ℝ) 1 := fun h => hu ⟨by linarith [h.1], by linarith [h.2]⟩
  rw [twoCopyProfile, hs _ h1, hs _ h2, add_zero]

/-- Alternating neighboring translates cancel throughout the interior. -/
theorem alternating_twoCopyProfile (ψ : ℝ → ℝ) (m : ℕ) (u : ℝ) :
    localProfileComb (twoCopyProfile ψ) 2 m (fun j => (-1) ^ j) (fun j => (j : ℝ)) u =
      ψ u - (-1) ^ m * ψ (u - m) := by
  induction m with
  | zero => simp only [localProfileComb, range_zero, sum_empty, pow_zero, Nat.cast_zero,
      sub_zero, one_mul, sub_self]
  | succ m ih =>
      have hstep : localProfileComb (twoCopyProfile ψ) 2 (m + 1)
          (fun j => (-1) ^ j) (fun j => (j : ℝ)) u =
          localProfileComb (twoCopyProfile ψ) 2 m (fun j => (-1) ^ j)
            (fun j => (j : ℝ)) u + (-1) ^ m * twoCopyProfile ψ ((u - m) / 2) := by
        simp only [localProfileComb, Finset.sum_range_succ]
      rw [hstep, ih, twoCopyProfile,
        show 2 * ((u - (m : ℝ)) / 2) = u - m by ring, pow_succ]
      push_cast
      rw [show u - ((m : ℝ) + 1) = u - m - 1 by ring]
      ring

/-- The square mass consists of the two endpoint packets, regardless of length. -/
theorem alternating_twoCopyProfile_square_mass {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hs : ∀ u, u ∉ Set.Icc 0 1 → ψ u = 0) {m : ℕ} (hm : 1 ≤ m) :
    (∫ u, localProfileComb (twoCopyProfile ψ) 2 m (fun j => (-1) ^ j)
      (fun j => (j : ℝ)) u ^ 2) = 2 * ∫ u, ψ u ^ 2 := by
  have hψc : HasCompactSupport ψ := HasCompactSupport.intro isCompact_Icc hs
  have hbase : ContCompact ψ := ⟨hψ.continuous, hψc⟩
  have hshift : ContCompact (fun u => ψ (u - (m : ℝ))) := by
    simpa only [sub_eq_add_neg] using hbase.translate (-(m : ℝ))
  have hscaled := hshift.const_mul_nice ((-1 : ℝ) ^ m)
  have hcross : testPairing ψ (fun u => ψ (u - (m : ℝ))) = 0 := by
    change shellAutocorr ψ (-(m : ℝ)) = 0
    rw [shellAutocorr_neg]
    exact shellAutocorr_eq_zero_of_one_le hψ hs (by exact_mod_cast hm)
  have hself : testPairing (fun u => ψ (u - (m : ℝ)))
      (fun u => ψ (u - (m : ℝ))) = testPairing ψ ψ :=
    integral_sub_right_eq_self (fun u => ψ u * ψ u) (m : ℝ)
  have hsign : ((-1 : ℝ) ^ m) * (-1) ^ m = 1 := by
    rw [← pow_add, show m + m = 2 * m by omega, pow_mul]
    norm_num
  simp_rw [alternating_twoCopyProfile]
  simp only [pow_two]
  change testPairing (fun u => ψ u - (-1) ^ m * ψ (u - (m : ℝ)))
    (fun u => ψ u - (-1) ^ m * ψ (u - (m : ℝ))) = _
  rw [testPairing_sub_left hbase hscaled (hbase.sub_nice hscaled),
    testPairing_sub_right hbase hbase hscaled,
    testPairing_sub_right hscaled hbase hscaled,
    testPairing_const_mul_right, testPairing_const_mul_left,
    testPairing_const_mul_left, testPairing_const_mul_right,
    testPairing_comm (fun u => ψ (u - (m : ℝ))) ψ, hcross, hself]
  simp only [mul_zero, sub_zero, ← mul_assoc, hsign, one_mul]
  simp only [testPairing, ← pow_two]
  ring

theorem integral_sq_twoCopyProfile {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hs : ∀ u, u ∉ Set.Icc 0 1 → ψ u = 0) :
    (∫ u, twoCopyProfile ψ u ^ 2) = ∫ u, ψ u ^ 2 := by
  have h := alternating_twoCopyProfile_square_mass hψ hs (m := 1) le_rfl
  simp only [localProfileComb, range_one, sum_singleton, pow_zero, Nat.cast_zero,
    sub_zero, one_mul] at h
  rw [Measure.integral_comp_div (fun u => twoCopyProfile ψ u ^ 2) 2] at h
  norm_num only [abs_of_pos (show (0 : ℝ) < 2 by norm_num), smul_eq_mul] at h
  linarith only [h]

private theorem scaledTranslate_nice {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hs : ∀ u, u ∉ Set.Icc 0 1 → ψ u = 0) (a : ℝ) :
    ContCompact (fun u => ψ (2 * u + a)) := by
  refine ⟨hψ.comp ((continuous_const.mul continuous_id).add continuous_const),
    HasCompactSupport.intro (K := Set.Icc (-a / 2) ((1 - a) / 2)) isCompact_Icc ?_⟩
  intro u hu
  apply hs
  intro hm
  exact hu ⟨by linarith only [hm.1], by linarith only [hm.2]⟩

private theorem scaledTranslate_pairing (ψ : ℝ → ℝ) (a b : ℝ) :
    testPairing (fun u => ψ (2 * u + a)) (fun u => ψ (2 * u + b)) =
      (1 / 2) * shellAutocorr ψ (b - a) := by
  have h := Measure.integral_comp_mul_left (fun v => ψ (v + a) * ψ (v + b)) (2 : ℝ)
  norm_num only [inv_pos, abs_of_pos (show (0 : ℝ) < 2⁻¹ by norm_num), smul_eq_mul,
    inv_eq_one_div] at h
  change (∫ u, ψ (2 * u + a) * ψ (2 * u + b)) = _
  rw [h]
  have hp := testPairing_translate_pair ψ a b
  change (∫ u, ψ (u + a) * ψ (u + b)) = shellAutocorr ψ (b - a) at hp
  rw [hp]

/-- Doubling the profile convolves its autocorrelation with the three-point
kernel `(1,2,1)`, followed by dilation. -/
theorem shellAutocorr_twoCopyProfile {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hs : ∀ u, u ∉ Set.Icc 0 1 → ψ u = 0) (t : ℝ) :
    shellAutocorr (twoCopyProfile ψ) t =
      (1 / 2) * (2 * shellAutocorr ψ (2 * t) +
        shellAutocorr ψ (2 * t - 1) + shellAutocorr ψ (2 * t + 1)) := by
  have h0 := scaledTranslate_nice hψ hs 0
  have hm := scaledTranslate_nice hψ hs (-1)
  have ht := scaledTranslate_nice hψ hs (2 * t)
  have htm := scaledTranslate_nice hψ hs (2 * t - 1)
  have he : shellAutocorr (twoCopyProfile ψ) t =
      testPairing (fun u => ψ (2 * u + 0) + ψ (2 * u + -1))
        (fun u => ψ (2 * u + 2 * t) + ψ (2 * u + (2 * t - 1))) := by
    unfold shellAutocorr _root_.RHTower.ArchimedeanAnomaly.autocorr testPairing twoCopyProfile
    congr 1
    funext u
    simp only [add_zero, mul_add, sub_eq_add_neg, add_assoc]
  rw [he, testPairing_add_left h0 hm (ht.add_nice htm),
    testPairing_add_right h0 ht htm, testPairing_add_right hm ht htm,
    scaledTranslate_pairing, scaledTranslate_pairing, scaledTranslate_pairing,
    scaledTranslate_pairing]
  rw [sub_zero, sub_zero, sub_neg_eq_add,
    show 2 * t - 1 - -1 = 2 * t by ring]
  ring

/-- At half-integer lags the doubled profile has exactly the nearest-neighbor
Gram kernel. Alternating signs turn this kernel into the discrete Laplacian. -/
theorem twoCopyProfile_local_gram_kernel {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hs : ∀ u, u ∉ Set.Icc 0 1 → ψ u = 0) (k : ℤ) :
    2 * shellAutocorr (twoCopyProfile ψ) ((k : ℝ) / 2) =
      (if k = 0 then 2 else if |k| = 1 then 1 else 0) * ∫ u, ψ u ^ 2 := by
  have hφ := contDiff_twoCopyProfile hψ
  have hφs : ∀ u, u ∉ Set.Icc 0 1 → twoCopyProfile ψ u = 0 :=
    fun _ hu => twoCopyProfile_eq_zero hs hu
  have hhalf : 2 * shellAutocorr (twoCopyProfile ψ) (1 / 2) = ∫ u, ψ u ^ 2 := by
    rw [shellAutocorr_twoCopyProfile hψ.continuous hs]
    norm_num only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, sub_self,
      show (1 : ℝ) + 1 = 2 by norm_num]
    rw [shellAutocorr_eq_zero_of_one_le hψ hs le_rfl,
      shellAutocorr_eq_zero_of_one_le hψ hs (by norm_num : (1 : ℝ) ≤ 2),
      shellAutocorr_zero]
    ring
  by_cases hk : k = 0
  · subst k
    rw [if_pos rfl]
    norm_num only [Int.cast_zero, zero_div]
    rw [shellAutocorr_zero, integral_sq_twoCopyProfile hψ hs]
  by_cases hp : k = 1
  · subst k
    norm_num only [Int.cast_one, show (1 : ℤ) ≠ 0 by omega, if_false, abs_one, if_true, one_mul]
    exact hhalf
  by_cases hn : k = -1
  · subst k
    norm_num only [Int.cast_neg, Int.cast_one, show (-1 : ℤ) ≠ 0 by omega,
      if_false, abs_neg, abs_one, if_true, one_mul]
    rw [shellAutocorr_neg]
    exact hhalf
  have habs : (2 : ℤ) ≤ |k| := by
    rcases le_total 0 k with h | h
    · rw [abs_of_nonneg h]
      omega
    · rw [abs_of_nonpos h]
      omega
  have hlag : 1 ≤ |(k : ℝ) / 2| := by
    have hr : (2 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast habs
    rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    linarith only [hr]
  rw [shellAutocorr_eq_zero_of_one_le_abs hφ hφs hlag, mul_zero,
    if_neg hk, if_neg (by omega), zero_mul]

/-- Every fixed alternating integer block has the same leading Gamma energy. -/
theorem tendsto_alternating_twoCopyProfile_archForm {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hs : ∀ u, u ∉ Set.Icc 0 1 → ψ u = 0)
    {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun N : ℕ => ((N : ℝ) + m) / Real.log ((N : ℝ) + m) *
      archForm (localIntegerBlock (twoCopyProfile ψ) 2 m (fun j => (-1) ^ j) N)) atTop
      (𝓝 (2 * ∫ u, ψ u ^ 2)) := by
  have hφ := contDiff_twoCopyProfile hψ
  have hφs : ∀ u, u ∉ Set.Icc 0 1 → twoCopyProfile ψ u = 0 := fun _ hu => twoCopyProfile_eq_zero hs hu
  have h := tendsto_localIntegerBlock_archForm hφ hφs (by norm_num : (0 : ℝ) < 2)
    m (fun j => (-1) ^ j)
  rw [← integral_sq_localProfileComb hφ.continuous hφs (by norm_num : (0 : ℝ) < 2),
    alternating_twoCopyProfile_square_mass hψ hs hm] at h
  exact h

/-- Coefficients placed at the literal integers `N,...,N+m-1`. -/
def localBlockCoefficients (m N : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ range m, if n = N + j then x j else 0

theorem localBlockCoefficients_at {m j : ℕ} (N : ℕ) (x : ℕ → ℝ) (hj : j ∈ range m) :
    localBlockCoefficients m N x (N + j) = x j := by
  rw [localBlockCoefficients, sum_eq_single_of_mem j hj]
  · rw [if_pos rfl]
  · intro i _ hij
    rw [if_neg (by omega)]

theorem sum_localBlockCoefficients_mul {N : ℕ} (hN : 1 ≤ N) (m : ℕ)
    (x f : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 (N + m), localBlockCoefficients m N x n * f n) =
      ∑ j ∈ range m, x j * f (N + j) := by
  simp_rw [localBlockCoefficients, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  have hmem : N + j ∈ Finset.Icc 1 (N + m) := by
    simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢
    omega
  rw [sum_eq_single_of_mem (N + j) hmem]
  · rw [if_pos rfl]
  · intro n _ hn
    rw [if_neg hn, zero_mul]

theorem sum_sq_localBlockCoefficients {N : ℕ} (hN : 1 ≤ N) (m : ℕ) (x : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 (N + m), localBlockCoefficients m N x n ^ 2) =
      ∑ j ∈ range m, x j ^ 2 := by
  simp only [pow_two]
  rw [sum_localBlockCoefficients_mul hN]
  apply sum_congr rfl
  intro j hj
  rw [localBlockCoefficients_at N x hj]

/-- The local block is exactly a translated test on the integer horizon. -/
theorem localIntegerBlock_eq_atomicTest {N : ℕ} (hN : 1 ≤ N) (φ : ℝ → ℝ)
    {c : ℝ} (hc : 0 < c) (m : ℕ) (x : ℕ → ℝ) (u : ℝ) :
    localIntegerBlock φ c m x N u =
      atomicTest (N + m) (localBlockCoefficients m N x)
        (atomDilate φ (c / (N + m : ℕ))) (u + Real.log N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hHr : 0 < (N : ℝ) + m := add_pos_of_pos_of_nonneg hNr (Nat.cast_nonneg m)
  rw [atomicTest, sum_localBlockCoefficients_mul hN]
  change (∑ j ∈ range m, x j * φ ((((N : ℝ) + m) * u - localIntegerCenter m N j) / c)) = _
  apply sum_congr rfl
  intro j _
  have hjr : 0 < (N : ℝ) + j := add_pos_of_pos_of_nonneg hNr (Nat.cast_nonneg j)
  have hlog : Real.log ((N : ℝ) + j) - Real.log N = Real.log (1 + (j : ℝ) / N) := by
    rw [← Real.log_div hjr.ne' hNr.ne']
    congr 1
    field_simp
  congr 1
  unfold atomDilate
  congr 1
  dsimp only [localIntegerCenter]
  push_cast
  rw [show u + Real.log (N : ℝ) - Real.log ((N : ℝ) + j) =
    u - (Real.log ((N : ℝ) + j) - Real.log N) by ring, hlog]
  field_simp

/-- A common translation changes only the Fourier phase, leaving Gamma energy fixed. -/
theorem archForm_comp_add (f : ℝ → ℝ) (v : ℝ) :
    archForm (fun u => f (u + v)) = archForm f := by
  unfold archForm
  congr 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro t
  have he : (fun u => (f (u + v) : ℂ)) =
      ArithmeticCastelnuovoSeveri.translate (-v) (fun u => (f u : ℂ)) := by
    funext u
    simp only [ArithmeticCastelnuovoSeveri.translate, sub_neg_eq_add]
  rw [he]
  dsimp only
  rw [ArithmeticCastelnuovoSeveri.paperFT_translate, norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero,
    zero_add, one_mul, Real.exp_zero]

theorem archForm_localIntegerBlock_eq_atomicTest {N : ℕ} (hN : 1 ≤ N) (φ : ℝ → ℝ)
    {c : ℝ} (hc : 0 < c) (m : ℕ) (x : ℕ → ℝ) :
    archForm (localIntegerBlock φ c m x N) =
      archForm (atomicTest (N + m) (localBlockCoefficients m N x)
        (atomDilate φ (c / (N + m : ℕ)))) := by
  have he := funext (localIntegerBlock_eq_atomicTest hN φ hc m x)
  rw [he, archForm_comp_add]

private theorem sum_alternating_sq (m : ℕ) :
    (∑ j ∈ range m, ((-1 : ℝ) ^ j) ^ 2) = (m : ℝ) := by
  have h (j : ℕ) : ((-1 : ℝ) ^ j) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
    norm_num
  simp only [h, sum_const, card_range, nsmul_eq_mul, mul_one]

/-- Two adjacent copies prevent every positive uniform logarithmic Gamma
reserve, already at the fixed overlap two and at the top of the horizon. -/
theorem twoCopyProfile_has_no_uniform_log_gamma_reserve {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hs : ∀ u, u ∉ Set.Icc 0 1 → ψ u = 0) :
    ¬ ∃ a b : ℝ, 0 < a ∧ ∀ᶠ H : ℕ in atTop, ∀ x : ℕ → ℝ,
      ((a * Real.log H - b) / H) * (∑ n ∈ Finset.Icc 1 H, x n ^ 2) ≤
        archForm (atomicTest H x (atomDilate (twoCopyProfile ψ) (2 / H))) := by
  rintro ⟨a, b, ha, hbound⟩
  obtain ⟨m, hm⟩ := exists_nat_gt (max ((2 * ∫ u, ψ u ^ 2) / a) 0)
  have hm0 : (0 : ℝ) < m := (le_max_right _ _).trans_lt hm
  have hm1 : 1 ≤ m := by
    have hmNat : 0 < m := by exact_mod_cast hm0
    omega
  have hmA : 2 * (∫ u, ψ u ^ 2) < a * m := by
    have h := (div_lt_iff₀ ha).mp ((le_max_left _ _).trans_lt hm)
    simpa only [mul_comm] using h
  have hr : Tendsto (fun N : ℕ => (N : ℝ) + m) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hH : Tendsto (fun N : ℕ => N + m) atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop k] with N hN
    omega
  have hleft : Tendsto (fun N : ℕ => (a - b / Real.log ((N : ℝ) + m)) * m)
      atTop (𝓝 (a * m)) := by
    simpa only [Function.comp_apply, sub_zero] using
      ((tendsto_const_nhds (x := a)).sub ((tendsto_const_nhds (x := b)).div_atTop
        (Real.tendsto_log_atTop.comp hr))).mul (tendsto_const_nhds (x := (m : ℝ)))
  have hright := tendsto_alternating_twoCopyProfile_archForm hψ hs hm1
  have hle : ∀ᶠ N : ℕ in atTop,
      (a - b / Real.log ((N : ℝ) + m)) * m ≤
        ((N : ℝ) + m) / Real.log ((N : ℝ) + m) *
          archForm (localIntegerBlock (twoCopyProfile ψ) 2 m (fun j => (-1) ^ j) N) := by
    filter_upwards [hH.eventually hbound, eventually_ge_atTop 2] with N hB hN
    have hN1 : 1 ≤ N := by omega
    have hHr : 1 < (N : ℝ) + m := by
      have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
      linarith only [hNr, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hlog : 0 < Real.log ((N : ℝ) + m) := Real.log_pos hHr
    have hB' := hB (localBlockCoefficients m N (fun j => (-1) ^ j))
    rw [sum_sq_localBlockCoefficients hN1, sum_alternating_sq,
      ← archForm_localIntegerBlock_eq_atomicTest hN1 (twoCopyProfile ψ)
        (by norm_num : (0 : ℝ) < 2)] at hB'
    simp only [Nat.cast_add] at hB'
    calc
      _ = (((N : ℝ) + m) / Real.log ((N : ℝ) + m)) *
          (((a * Real.log ((N : ℝ) + m) - b) / ((N : ℝ) + m)) * m) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hB' (div_nonneg (by positivity) hlog.le)
  have hcontra := le_of_tendsto_of_tendsto hleft hright hle
  exact (not_le_of_gt hmA) hcontra

/-- An explicit nonzero smooth profile for which a logarithmic reserve fails. -/
def resonantTiltedSpline : ℝ → ℝ := twoCopyProfile tiltedUnitSpline

theorem resonantTiltedSpline_certificate :
    ContDiff ℝ 2 resonantTiltedSpline ∧
    (∀ u, u ∉ Set.Icc 0 1 → resonantTiltedSpline u = 0) ∧
    (0 < ∫ u, resonantTiltedSpline u ^ 2) ∧
    ¬ ∃ a b : ℝ, 0 < a ∧ ∀ᶠ H : ℕ in atTop, ∀ x : ℕ → ℝ,
      ((a * Real.log H - b) / H) * (∑ n ∈ Finset.Icc 1 H, x n ^ 2) ≤
        archForm (atomicTest H x (atomDilate resonantTiltedSpline (2 / H))) := by
  refine ⟨contDiff_twoCopyProfile contDiff_tiltedUnitSpline,
    fun _ hu => twoCopyProfile_eq_zero tiltedUnitSpline_eq_zero hu, ?_,
    twoCopyProfile_has_no_uniform_log_gamma_reserve contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero⟩
  change 0 < ∫ u, twoCopyProfile tiltedUnitSpline u ^ 2
  rw [integral_sq_twoCopyProfile contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero]
  exact integral_tiltedUnitSpline_sq_pos

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.alternating_twoCopyProfile_square_mass
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.twoCopyProfile_local_gram_kernel
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_alternating_twoCopyProfile_archForm
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.resonantTiltedSpline_certificate
