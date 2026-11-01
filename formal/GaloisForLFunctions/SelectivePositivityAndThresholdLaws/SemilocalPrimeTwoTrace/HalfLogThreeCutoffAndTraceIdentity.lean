import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace.PrimeValuationShellLogTrace
import GaloisForLFunctions.RHTower.WeilPrimeFreeFamily
import GaloisForLFunctions.RHTower.PoleVanishingWeilTraceCertificate
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanSoninCutoffTraceFormula
import GaloisForLFunctions.HTGeometry.FramePurificationPartialTrace

/-!
# Closed-Endpoint Prime Cutoff Laws at `½ log 2` and `½ log 3`, and the `{∞, 2}` Trace Identity

For an aperture `a > 0`, a logarithmic shift `h ≥ 2a` translates the open core `(-a, a)` off
`[-a, a]` and meets `[-a, a]` at most at the single boundary point `-a` of Lebesgue measure zero.
Hence the compressed symmetric log-translation operator vanishes identically on the closed boundary
`2a ≤ h` (`ccmApertureCompression_symmetricLogTranslation_eq_zero_of_two_mul_le`).

This upgrades the strict small-aperture prime vanishing law to closed endpoints and isolates the
exact arithmetic content of the window `(0, ½ log 3]`:

1. **Closed `½ log 2` prime-free law:** for all `a ≤ ½ log 2` (including `halfLogTwoAperture`,
   where `n = 2` enters `Finset.Icc 2 ⌊e^{2a}⌋`), `ccmFinitePrimeOperator a = 0`, so
   `primeFreeFamily` coincides identically with the literal restricted Weil family through `½ log 2`.
2. **Closed `½ log 3` single-prime law:** for all `a ≤ ½ log 3` (including `halfLogThreeAperture`,
   where `n = 3` enters `Finset.Icc 2 ⌊e^{2a}⌋` with `ccmPrimeTransportOperator _ 3 = 0`),
   `ccmFinitePrimeOperator a = (log 2) • ccmPrimeTransportOperator a 2`.
3. **Aperture-compatible `{∞, p}` semilocal remainder family (`primeSingleSemilocalFamily p`):**
   retaining only the positive powers `p^m` (`m ≥ 1`) of a single prime `p` defines a genuine
   `CCMRemainderFamily`, and at `p = 2` its bounded remainder, quadratic form, and ground energy
   equal the literal all-prime restricted Weil remainder, quadratic form, and ground energy on the
   entire closed window `0 < a ≤ ½ log 3`.
4. **Exact `{∞, 2}` operator-trace identity through `½ log 3`:** combining the positive local
   `2`-adic valuation-shell operator `K_2(1) = primeTwoLogOperator 1` (`opTrace(K_2(1)) = log 2`)
   with rank-one aperture traces rewrites `ccmRestrictedWeilSourceQuadratic a u` for every
   `a ≤ ½ log 3` as the archimedean phase integral plus polar trace minus the Euler-weighted trace
   product at the prime `2`.
-/

noncomputable section

open MeasureTheory Set Filter Topology BigOperators
open scoped ENNReal InnerProductSpace
open _root_.RHTower _root_.RHTower.WeilDeletion GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace

/-- The aperture `a = ½ log 3`, i.e. multiplicative support `[3^{-1/2}, 3^{1/2}]`. -/
def halfLogThreeAperture : SuzukiPositiveAperture :=
  ⟨Real.log 3 / 2, by have := Real.log_pos (by norm_num : (1 : ℝ) < 3); positivity⟩

@[simp] theorem halfLogTwoAperture_val : halfLogTwoAperture.1 = Real.log 2 / 2 := rfl

@[simp] theorem halfLogThreeAperture_val : halfLogThreeAperture.1 = Real.log 3 / 2 := rfl

theorem halfLogTwoAperture_lt_halfLogThreeAperture :
    halfLogTwoAperture.1 < halfLogThreeAperture.1 := by
  rw [halfLogTwoAperture_val, halfLogThreeAperture_val]
  have hlt : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-! ## Closed-endpoint vanishing of compressed logarithmic translations -/

/-- A logarithmic shift `h ≥ 2a` has zero matrix elements on `suzukiApertureHilbert a`, including at
the exact boundary `h = 2a` where `[-a, a]` and `[-a - h, a - h]` meet only at `-a`. -/
theorem inner_logTranslationCLM_eq_zero_of_two_mul_le
    (a : SuzukiPositiveAperture) (f g : suzukiApertureHilbert a)
    {h : ℝ} (hh : 2 * a.1 ≤ h) :
    inner ℂ (logTranslationCLM h f.1) g.1 = 0 := by
  rw [MeasureTheory.L2.inner_def]
  have hfixG : indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1) g.1 = g.1 :=
    indicatorCutoff_suzukiApertureHilbert a g
  have hfixGAE :
      (indicatorCutoff (centralInterval a.1)
        (measurableSet_centralInterval a.1) g.1 : ℝ → ℂ) =ᵐ[volume] g.1 := by
    rw [hfixG]
  have hcutGAE := indicatorCutoff_ae (centralInterval a.1)
    (measurableSet_centralInterval a.1) g.1
  have hfixF : indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1) f.1 = f.1 :=
    indicatorCutoff_suzukiApertureHilbert a f
  have hfixFAE :
      (indicatorCutoff (centralInterval a.1)
        (measurableSet_centralInterval a.1) f.1 : ℝ → ℂ) =ᵐ[volume] f.1 := by
    rw [hfixF]
  have hcutFAE := indicatorCutoff_ae (centralInterval a.1)
    (measurableSet_centralInterval a.1) f.1
  have hfixFShift := hfixFAE.comp_tendsto
    (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae
  have hcutFShift := hcutFAE.comp_tendsto
    (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae
  have htrans := logTranslationCLM_ae h f.1
  have hne : ∀ᵐ x : ℝ, x ≠ -a.1 := ae_iff.mpr (by simp)
  calc
    (∫ x : ℝ, inner ℂ (logTranslationCLM h f.1 x) (g.1 x)) =
        ∫ _x : ℝ, (0 : ℂ) := by
      apply integral_congr_ae
      filter_upwards [hfixGAE, hcutGAE, hfixFShift, hcutFShift, htrans, hne] with
          x hfixgx hcutgx hfixfxh hcutfxh htransx hnex
      have hfixfxh' : indicatorCutoff (centralInterval a.1)
          (measurableSet_centralInterval a.1) f.1 (x + h) = f.1 (x + h) := by
        simpa [MellinL2.realTranslationEquiv, Function.comp_apply] using hfixfxh
      have hcutfxh' : indicatorCutoff (centralInterval a.1)
          (measurableSet_centralInterval a.1) f.1 (x + h) =
            (centralInterval a.1).indicator (fun y => f.1 y) (x + h) := by
        simpa [MellinL2.realTranslationEquiv, Function.comp_apply] using hcutfxh
      rw [htransx]
      by_cases hx : x ∈ centralInterval a.1
      · have hxgt : -a.1 < x := lt_of_le_of_ne hx.1 hnex.symm
        have hxh : x + h ∉ centralInterval a.1 := by
          intro hmem
          rw [centralInterval, Set.mem_Icc] at hmem
          linarith [hmem.2]
        have hzero : f.1 (x + h) = 0 := by
          rw [hcutfxh', Set.indicator_of_notMem hxh] at hfixfxh'
          exact hfixfxh'.symm
        rw [hzero]
        simp
      · have hzero : g.1 x = 0 := by
          rw [hcutgx, Set.indicator_of_notMem hx] at hfixgx
          exact hfixgx.symm
        rw [hzero]
        simp
    _ = 0 := by simp

theorem inner_neg_logTranslationCLM_eq_zero_of_two_mul_le
    (a : SuzukiPositiveAperture) (f g : suzukiApertureHilbert a)
    {h : ℝ} (hh : 2 * a.1 ≤ h) :
    inner ℂ (logTranslationCLM (-h) f.1) g.1 = 0 := by
  rw [inner_logTranslationCLM (-h)]
  simp only [neg_neg]
  exact inner_eq_zero_symm.mpr (inner_logTranslationCLM_eq_zero_of_two_mul_le a g f hh)

theorem clm_smul_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (c : ℂ) : c • (0 : H →L[ℂ] H) = 0 := by
  ext x
  change c • (0 : H) = 0
  exact smul_zero c

theorem clm_smul_comp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (c : ℂ) (A B : H →L[ℂ] H) : (c • A) ∘L B = c • (A ∘L B) := by
  ext x
  rfl

/-- Compressed symmetric log-translation vanishes identically whenever `2a ≤ h`. -/
theorem ccmApertureCompression_symmetricLogTranslation_eq_zero_of_two_mul_le
    (a : SuzukiPositiveAperture) {h : ℝ} (hh : 2 * a.1 ≤ h) :
    ccmApertureCompression a (ccmSymmetricLogTranslation h) = 0 := by
  refine ContinuousLinearMap.ext fun f => ext_inner_right ℂ fun g => ?_
  rw [zero_apply, inner_zero_left, inner_ccmApertureCompression,
    ccmSymmetricLogTranslation, add_apply, inner_add_left,
    inner_logTranslationCLM_eq_zero_of_two_mul_le a f g hh,
    inner_neg_logTranslationCLM_eq_zero_of_two_mul_le a f g hh, add_zero]

/-- The prime-transport operator `T_a(n)` vanishes identically whenever `2a ≤ log n`. -/
theorem ccmPrimeTransportOperator_eq_zero_of_two_mul_le_log
    (a : SuzukiPositiveAperture) {n : ℕ} (hn : 2 * a.1 ≤ Real.log n) :
    ccmPrimeTransportOperator a n = 0 := by
  rw [ccmPrimeTransportOperator,
    ccmApertureCompression_symmetricLogTranslation_eq_zero_of_two_mul_le a hn, clm_smul_zero]

@[simp] theorem ccmPrimeTransportOperator_halfLogTwo_two :
    ccmPrimeTransportOperator halfLogTwoAperture 2 = 0 :=
  ccmPrimeTransportOperator_eq_zero_of_two_mul_le_log halfLogTwoAperture (by
    rw [halfLogTwoAperture_val, Nat.cast_ofNat]; linarith)

@[simp] theorem ccmPrimeTransportOperator_halfLogThree_three :
    ccmPrimeTransportOperator halfLogThreeAperture 3 = 0 :=
  ccmPrimeTransportOperator_eq_zero_of_two_mul_le_log halfLogThreeAperture (by
    rw [halfLogThreeAperture_val, Nat.cast_ofNat]; linarith)

/-! ## Closed-endpoint prime cutoff laws at `½ log 2` and `½ log 3` -/

theorem ccmRemainderFamily_Q_eq_literal_of_B_eq (F : CCMRemainderFamily)
    (a : SuzukiPositiveAperture) (he : F.B a = ccmRestrictedWeilBoundedRemainder a)
    (u : CCMArchimedeanFormDomain a) :
    F.Q a u = ccmRestrictedWeilSourceQuadratic a u := by
  rw [CCMRemainderFamily.Q_eq_form_re, he, ← ccmRestrictedWeilForm_self_re_eq_source]
  rfl

theorem ccmRemainderFamily_energy_eq_literal_of_B_eq (F : CCMRemainderFamily)
    (a : SuzukiPositiveAperture) (he : F.B a = ccmRestrictedWeilBoundedRemainder a) :
    F.energy a = ccmRestrictedWeilGroundEnergy a := by
  unfold CCMRemainderFamily.energy ccmRestrictedWeilGroundEnergy ccmRestrictedWeilCovariance
  change ‖boundedPerturbedFormCovariance (ccmArchimedeanFormToAperture a) (F.B a)
      (F.selfAdjoint a)‖⁻¹ - boundedPerturbedFormShift (F.B a) =
    ‖boundedPerturbedFormCovariance (ccmArchimedeanFormToAperture a)
      (ccmRestrictedWeilBoundedRemainder a)
      (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)‖⁻¹ -
      boundedPerturbedFormShift (ccmRestrictedWeilBoundedRemainder a)
  rw [boundedPerturbedFormCovariance_congr (ccmArchimedeanFormToAperture a) he (F.selfAdjoint a)
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a), he]

/-- **Closed `½ log 2` prime vanishing law:** `ccmFinitePrimeOperator a = 0` for all `a ≤ ½ log 2`,
including the endpoint `a = ½ log 2` where `n = 2` enters `Finset.Icc 2 ⌊e^{2a}⌋`. -/
theorem ccmFinitePrimeOperator_eq_zero_of_le_halfLogTwo {a : SuzukiPositiveAperture}
    (ha : a.1 ≤ Real.log 2 / 2) :
    ccmFinitePrimeOperator a = 0 := by
  unfold ccmFinitePrimeOperator
  refine Finset.sum_eq_zero fun n hn => ?_
  have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
  rw [ccmPrimeTransportOperator_eq_zero_of_two_mul_le_log a (by linarith), clm_smul_zero]

theorem ccmPrimeFreeRemainder_eq_literal_of_le_halfLogTwo {a : SuzukiPositiveAperture}
    (ha : a.1 ≤ Real.log 2 / 2) :
    ccmPrimeFreeRemainder a = ccmRestrictedWeilBoundedRemainder a := by
  rw [ccmPrimeFreeRemainder, ccmFinitePrimeOperator_eq_zero_of_le_halfLogTwo ha, add_zero]

theorem primeFreeFamily_Q_eq_literal_of_le_halfLogTwo {a : SuzukiPositiveAperture}
    (ha : a.1 ≤ Real.log 2 / 2) (u : CCMArchimedeanFormDomain a) :
    primeFreeFamily.Q a u = ccmRestrictedWeilSourceQuadratic a u :=
  ccmRemainderFamily_Q_eq_literal_of_B_eq primeFreeFamily a
    (ccmPrimeFreeRemainder_eq_literal_of_le_halfLogTwo ha) u

theorem primeFreeFamily_energy_eq_literal_of_le_halfLogTwo {a : SuzukiPositiveAperture}
    (ha : a.1 ≤ Real.log 2 / 2) :
    primeFreeFamily.energy a = ccmRestrictedWeilGroundEnergy a :=
  ccmRemainderFamily_energy_eq_literal_of_B_eq primeFreeFamily a
    (ccmPrimeFreeRemainder_eq_literal_of_le_halfLogTwo ha)

theorem primeFreeFamily_energy_halfLogTwo :
    primeFreeFamily.energy halfLogTwoAperture =
      ccmRestrictedWeilGroundEnergy halfLogTwoAperture :=
  primeFreeFamily_energy_eq_literal_of_le_halfLogTwo le_rfl

/-- **Uniform closed `½ log 3` single-prime law:** on the entire closed window `0 < a ≤ ½ log 3`,
the finite prime operator reduces to the single prime-`2` term `(log 2) • T_a(2)` (both sides
vanishing when `a ≤ ½ log 2`, and `T_a(3) = 0` killing `n = 3` at `a = ½ log 3`). -/
theorem ccmFinitePrimeOperator_eq_primeTwo_of_le_halfLogThree {a : SuzukiPositiveAperture}
    (ha : a.1 ≤ Real.log 3 / 2) :
    ccmFinitePrimeOperator a = (Real.log 2 : ℂ) • ccmPrimeTransportOperator a 2 := by
  rcases le_or_gt a.1 (Real.log 2 / 2) with ha2 | ha2
  · have h2 : 2 * a.1 ≤ Real.log (2 : ℕ) := by rw [Nat.cast_ofNat]; linarith
    rw [ccmFinitePrimeOperator_eq_zero_of_le_halfLogTwo ha2,
      ccmPrimeTransportOperator_eq_zero_of_two_mul_le_log a h2, clm_smul_zero]
  · unfold ccmFinitePrimeOperator
    have hexp2 : (2 : ℝ) < Real.exp (2 * a.1) :=
      calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
        _ < Real.exp (2 * a.1) := Real.exp_lt_exp.mpr (by linarith)
    have hexp3 : Real.exp (2 * a.1) ≤ ((3 : ℕ) : ℝ) :=
      calc Real.exp (2 * a.1) ≤ Real.exp (Real.log 3) := Real.exp_le_exp.mpr (by linarith)
        _ = (3 : ℝ) := Real.exp_log (by norm_num)
        _ = ((3 : ℕ) : ℝ) := by norm_num
    have hfl2 : 2 ≤ Nat.floor (Real.exp (2 * a.1)) := Nat.le_floor hexp2.le
    have hfl3 : Nat.floor (Real.exp (2 * a.1)) ≤ 3 :=
      calc Nat.floor (Real.exp (2 * a.1)) ≤ Nat.floor ((3 : ℕ) : ℝ) := Nat.floor_mono hexp3
        _ = 3 := Nat.floor_natCast 3
    rw [Finset.sum_eq_single 2]
    · rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, Nat.cast_ofNat]
    · intro n hn hne2
      obtain ⟨hn2, hnu⟩ := Finset.mem_Icc.mp hn
      have hn3 : n = 3 := by omega
      subst hn3
      have h3 : 2 * a.1 ≤ Real.log (3 : ℕ) := by rw [Nat.cast_ofNat]; linarith
      rw [ccmPrimeTransportOperator_eq_zero_of_two_mul_le_log a h3, clm_smul_zero]
    · intro hnot
      exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hfl2⟩) hnot

/-- Rewriting the finite prime operator on `0 < a ≤ ½ log 3` in terms of the positive local
`2`-adic operator trace `opTrace (primeTwoLogOperator 1)` and the unsquared Euler coefficient. -/
theorem ccmFinitePrimeOperator_eq_primeTwoLogTrace_of_le_halfLogThree {a : SuzukiPositiveAperture}
    (ha : a.1 ≤ Real.log 3 / 2) :
    ccmFinitePrimeOperator a =
      (soninSemilocalLogPrimePowerCoefficient (twoPrime, 0) *
        ContinuousLinearMap.opTrace (primeTwoLogOperator 1)) •
        ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log 2)) := by
  have htr := soninEulerCoeff_mul_opTrace_primeTwoLogOperator 0
  simp only [zero_add, pow_one, Nat.cast_ofNat] at htr
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two] at htr
  have hcoef : (Real.log 2 : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) =
      soninSemilocalLogPrimePowerCoefficient (twoPrime, 0) *
        ContinuousLinearMap.opTrace (primeTwoLogOperator 1) := by
    rw [htr]
    push_cast
    ring
  rw [ccmFinitePrimeOperator_eq_primeTwo_of_le_halfLogThree ha, ccmPrimeTransportOperator,
    Nat.cast_ofNat]
  refine ContinuousLinearMap.ext fun f => ?_
  change (Real.log 2 : ℂ) • (((1 / Real.sqrt 2 : ℝ) : ℂ) •
      ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log 2)) f) =
    (soninSemilocalLogPrimePowerCoefficient (twoPrime, 0) *
      ContinuousLinearMap.opTrace (primeTwoLogOperator 1)) •
      ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log 2)) f
  rw [smul_smul, hcoef]

/-! ## The single-prime `{∞, p}` semilocal remainder family -/

/-- Sum of visible prime-power transport blocks `p^m` (`1 ≤ m ≤ ⌊e^{2a}⌋`) of a single prime `p`. -/
def ccmPrimePowerOperator (p : ℕ) (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ∑ m ∈ Finset.Icc 1 (Nat.floor (Real.exp (2 * a.1))),
    ccmVisiblePrimeBlock a (p ^ m)

theorem ccmPrimePowerOperator_isSelfAdjoint (p : ℕ) (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (ccmPrimePowerOperator p a) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  unfold ccmPrimePowerOperator
  generalize Finset.Icc 1 (Nat.floor (Real.exp (2 * a.1))) = s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert m s hm ih =>
      rw [Finset.sum_insert hm, ContinuousLinearMap.adjoint.map_add, ih,
        ContinuousLinearMap.isSelfAdjoint_iff'.mp (ccmVisiblePrimeBlock_isSelfAdjoint a (p ^ m))]

theorem ccmPrimePowerOperator_diagonal_eq_of_val_eq (p : ℕ) {a b : SuzukiPositiveAperture}
    (hab : a.1 ≤ b.1) {u : CCMArchimedeanFormDomain a} {v : CCMArchimedeanFormDomain b}
    (hvu : v.1 = u.1) :
    (inner ℂ (ccmPrimePowerOperator p b (ccmArchimedeanFormToAperture b v))
        (ccmArchimedeanFormToAperture b v)).re =
      (inner ℂ (ccmPrimePowerOperator p a (ccmArchimedeanFormToAperture a u))
        (ccmArchimedeanFormToAperture a u)).re := by
  set fa := ccmArchimedeanFormToAperture a u
  set fb := ccmArchimedeanFormToAperture b v
  have hsub : Finset.Icc 1 (Nat.floor (Real.exp (2 * a.1))) ⊆
      Finset.Icc 1 (Nat.floor (Real.exp (2 * b.1))) := by
    intro m hm
    rw [Finset.mem_Icc] at hm ⊢
    exact ⟨hm.1, hm.2.trans (Nat.floor_mono (Real.exp_le_exp.mpr (by linarith)))⟩
  have hexpand : ∑ m ∈ Finset.Icc 1 (Nat.floor (Real.exp (2 * a.1))),
        (inner ℂ (ccmVisiblePrimeBlock a (p ^ m) fa) fa).re =
      ∑ m ∈ Finset.Icc 1 (Nat.floor (Real.exp (2 * b.1))),
        (inner ℂ (ccmVisiblePrimeBlock a (p ^ m) fa) fa).re := by
    refine Finset.sum_subset hsub fun m hmb hma => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hmb).1
    have hmgt : Nat.floor (Real.exp (2 * a.1)) < m := by
      by_contra hle
      exact hma (Finset.mem_Icc.mpr ⟨hm1, Nat.le_of_not_gt hle⟩)
    have hnotMem : p ^ m ∉ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))) := by
      intro hmem
      obtain ⟨hp2, hpmle⟩ := Finset.mem_Icc.mp hmem
      have hp_ge2 : 2 ≤ p := by
        match p with
        | 0 => rw [zero_pow (by omega)] at hp2; omega
        | 1 => rw [one_pow] at hp2; omega
        | p' + 2 => omega
      have hmlt : m < p ^ m := lt_of_lt_of_le m.lt_two_pow_self (Nat.pow_le_pow_left hp_ge2 m)
      omega
    rw [ccmVisiblePrimeBlock_of_invisible a hnotMem]
    simp
  have hsum_re : ∀ (c : SuzukiPositiveAperture) (f : suzukiApertureHilbert c),
      (inner ℂ (ccmPrimePowerOperator p c f) f).re =
        ∑ m ∈ Finset.Icc 1 (Nat.floor (Real.exp (2 * c.1))),
          (inner ℂ (ccmVisiblePrimeBlock c (p ^ m) f) f).re := by
    intro c f
    unfold ccmPrimePowerOperator
    generalize Finset.Icc 1 (Nat.floor (Real.exp (2 * c.1))) = s
    induction s using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty, zero_apply, inner_zero_left, Complex.zero_re]
    | @insert m s hm ih =>
        rw [Finset.sum_insert hm, Finset.sum_insert hm, add_apply, inner_add_left,
          Complex.add_re, ih]
  rw [hsum_re b fb, hsum_re a fa, hexpand]
  refine Finset.sum_congr rfl fun m _ => ?_
  exact deleted_diagonal_eq_of_val_eq (p ^ m) hab hvu

/-- Bounded remainder of the `{∞, p}` single-prime semilocal restricted Weil form. -/
def ccmPrimeSingleSemilocalRemainder (p : ℕ) (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ccmPrimeFreeRemainder a - ccmPrimePowerOperator p a

theorem ccmPrimeSingleSemilocalRemainder_isSelfAdjoint (p : ℕ) (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (ccmPrimeSingleSemilocalRemainder p a) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', ccmPrimeSingleSemilocalRemainder,
    ContinuousLinearMap.adjoint.map_sub,
    ContinuousLinearMap.isSelfAdjoint_iff'.mp (ccmPrimeFreeRemainder_isSelfAdjoint a),
    ContinuousLinearMap.isSelfAdjoint_iff'.mp (ccmPrimePowerOperator_isSelfAdjoint p a)]

/-- The `{∞, p}` single-prime semilocal remainders form a genuine aperture-compatible family, with
continuous antitone ground energy `a ↦ (primeSingleSemilocalFamily p).energy a`. -/
def primeSingleSemilocalFamily (p : ℕ) : CCMRemainderFamily where
  B a := ccmPrimeSingleSemilocalRemainder p a
  selfAdjoint a := ccmPrimeSingleSemilocalRemainder_isSelfAdjoint p a
  compat := by
    intro a b hab u v hvu
    unfold ccmPrimeSingleSemilocalRemainder
    rw [sub_apply, sub_apply, inner_sub_left,
      inner_sub_left, Complex.sub_re, Complex.sub_re,
      primeFree_diagonal_eq_of_val_eq hab hvu,
      ccmPrimePowerOperator_diagonal_eq_of_val_eq p hab hvu]

/-- Throughout `0 < a ≤ ½ log 3`, the prime-`2` power operator equals `ccmFinitePrimeOperator a`
(since `2^2 = 4 > 3 ≥ ⌊e^{2a}⌋` and `T_a(3) = 0` at `a = ½ log 3`). -/
theorem ccmPrimePowerOperator_two_eq_finitePrime_of_le_halfLogThree {a : SuzukiPositiveAperture}
    (ha : a.1 ≤ Real.log 3 / 2) :
    ccmPrimePowerOperator 2 a = ccmFinitePrimeOperator a := by
  rw [ccmFinitePrimeOperator_eq_primeTwo_of_le_halfLogThree ha]
  have hexp3 : Real.exp (2 * a.1) ≤ ((3 : ℕ) : ℝ) :=
    calc Real.exp (2 * a.1) ≤ Real.exp (Real.log 3) := Real.exp_le_exp.mpr (by linarith)
      _ = (3 : ℝ) := Real.exp_log (by norm_num)
      _ = ((3 : ℕ) : ℝ) := by norm_num
  have hfl3 : Nat.floor (Real.exp (2 * a.1)) ≤ 3 :=
    calc Nat.floor (Real.exp (2 * a.1)) ≤ Nat.floor ((3 : ℕ) : ℝ) := Nat.floor_mono hexp3
      _ = 3 := Nat.floor_natCast 3
  rcases le_or_gt a.1 (Real.log 2 / 2) with ha2 | ha2
  · have h2 : 2 * a.1 ≤ Real.log (2 : ℕ) := by rw [Nat.cast_ofNat]; linarith
    rw [ccmPrimeTransportOperator_eq_zero_of_two_mul_le_log a h2, clm_smul_zero]
    unfold ccmPrimePowerOperator
    refine Finset.sum_eq_zero fun m hm => ?_
    unfold ccmVisiblePrimeBlock
    split_ifs with hmem
    · have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hpow : (2 : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
        exact_mod_cast (show 2 ≤ 2 ^ m from
          le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm1))
      have hlog : Real.log 2 ≤ Real.log ((2 ^ m : ℕ) : ℝ) :=
        Real.log_le_log (by norm_num) hpow
      rw [ccmPrimeTransportOperator_eq_zero_of_two_mul_le_log a (by linarith), clm_smul_zero]
    · rfl
  · have hexp2 : (2 : ℝ) < Real.exp (2 * a.1) :=
      calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
        _ < Real.exp (2 * a.1) := Real.exp_lt_exp.mpr (by linarith)
    have hfl2 : 2 ≤ Nat.floor (Real.exp (2 * a.1)) := Nat.le_floor hexp2.le
    unfold ccmPrimePowerOperator
    rw [Finset.sum_eq_single 1]
    · unfold ccmVisiblePrimeBlock
      rw [pow_one, if_pos (Finset.mem_Icc.mpr ⟨le_rfl, hfl2⟩),
        ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, Nat.cast_ofNat]
    · intro m hm hne1
      have hm2 : 2 ≤ m := by
        have hm1 := (Finset.mem_Icc.mp hm).1
        omega
      have hpow4 : 4 ≤ 2 ^ m :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
      have hnotMem : 2 ^ m ∉ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))) := by
        intro hmem
        have := (Finset.mem_Icc.mp hmem).2
        omega
      exact ccmVisiblePrimeBlock_of_invisible a hnotMem
    · intro hnot
      exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩) hnot

/-- On the entire closed window `0 < a ≤ ½ log 3`, the `{∞, 2}` semilocal remainder equals the
literal all-prime restricted Weil remainder. -/
theorem ccmPrimeSingleSemilocalRemainder_two_eq_literal_of_le_halfLogThree
    {a : SuzukiPositiveAperture} (ha : a.1 ≤ Real.log 3 / 2) :
    (primeSingleSemilocalFamily 2).B a = ccmRestrictedWeilBoundedRemainder a := by
  change ccmPrimeFreeRemainder a - ccmPrimePowerOperator 2 a = _
  rw [ccmPrimeFreeRemainder, ccmPrimePowerOperator_two_eq_finitePrime_of_le_halfLogThree ha,
    add_sub_cancel_right]

theorem primeSingleSemilocalFamily_two_Q_eq_literal_of_le_halfLogThree
    {a : SuzukiPositiveAperture} (ha : a.1 ≤ Real.log 3 / 2) (u : CCMArchimedeanFormDomain a) :
    (primeSingleSemilocalFamily 2).Q a u = ccmRestrictedWeilSourceQuadratic a u :=
  ccmRemainderFamily_Q_eq_literal_of_B_eq (primeSingleSemilocalFamily 2) a
    (ccmPrimeSingleSemilocalRemainder_two_eq_literal_of_le_halfLogThree ha) u

theorem primeSingleSemilocalFamily_two_energy_eq_literal_of_le_halfLogThree
    {a : SuzukiPositiveAperture} (ha : a.1 ≤ Real.log 3 / 2) :
    (primeSingleSemilocalFamily 2).energy a = ccmRestrictedWeilGroundEnergy a :=
  ccmRemainderFamily_energy_eq_literal_of_B_eq (primeSingleSemilocalFamily 2) a
    (ccmPrimeSingleSemilocalRemainder_two_eq_literal_of_le_halfLogThree ha)

theorem primeSingleSemilocalFamily_two_energy_halfLogThree :
    (primeSingleSemilocalFamily 2).energy halfLogThreeAperture =
      ccmRestrictedWeilGroundEnergy halfLogThreeAperture :=
  primeSingleSemilocalFamily_two_energy_eq_literal_of_le_halfLogThree le_rfl

/-! ## Exact `{∞, 2}` operator-trace identity through `½ log 3` -/

theorem opTrace_comp_rankOne_self_of_isSelfAdjoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {R : H →L[ℂ] H} (hR : IsSelfAdjoint R) (f : H) :
    ContinuousLinearMap.opTrace (R ∘L InnerProductSpace.rankOne ℂ f f) = inner ℂ (R f) f := by
  rw [opTrace_comp_rankOne]
  exact (hR.isSymmetric f f).symm

/-- **Exact `{∞, 2}` operator-trace identity through `½ log 3`.**
For every aperture `0 < a ≤ ½ log 3` and every form vector `u : CCMArchimedeanFormDomain a` with
aperture image `f = ccmArchimedeanFormToAperture a u`, the literal restricted Weil quadratic form
equals the archimedean phase integral plus the polar rank-one trace minus the product of the
unsquared Euler coefficient, the trace of the positive `2`-adic shell operator
`primeTwoLogOperator 1`, and the compressed prime-`2` log-shift trace. -/
theorem ccmRestrictedWeilSourceQuadratic_eq_semilocalPrimeTwoTrace_of_le_halfLogThree
    {a : SuzukiPositiveAperture} (ha : a.1 ≤ Real.log 3 / 2) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilSourceQuadratic a u =
      archPart a u +
        (ContinuousLinearMap.opTrace (ccmPolarOperator a ∘L
          InnerProductSpace.rankOne ℂ (ccmArchimedeanFormToAperture a u)
            (ccmArchimedeanFormToAperture a u))).re -
        (soninSemilocalLogPrimePowerCoefficient (twoPrime, 0) *
          ContinuousLinearMap.opTrace (primeTwoLogOperator 1) *
          ContinuousLinearMap.opTrace
            (ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log 2)) ∘L
              InnerProductSpace.rankOne ℂ (ccmArchimedeanFormToAperture a u)
                (ccmArchimedeanFormToAperture a u))).re := by
  set f := ccmArchimedeanFormToAperture a u
  have hQ : primeFreeFamily.Q a u = ccmRestrictedWeilSourceQuadratic a u +
      (inner ℂ (ccmFinitePrimeOperator a f) f).re := by
    rw [CCMRemainderFamily.Q_eq_form_re, ← ccmRestrictedWeilForm_self_re_eq_source]
    show (inner ℂ u u + inner ℂ (ccmRestrictedWeilBoundedRemainder a f +
      ccmFinitePrimeOperator a f) f).re = _
    rw [inner_add_left, ← add_assoc, Complex.add_re]
    rfl
  have hpol : polarPart a u =
      (ContinuousLinearMap.opTrace (ccmPolarOperator a ∘L
        InnerProductSpace.rankOne ℂ f f)).re := by
    rw [opTrace_comp_rankOne_self_of_isSelfAdjoint (ccmPolarOperator_isSelfAdjoint a) f,
      inner_ccmPolarOperator]
    rfl
  set c : ℂ := soninSemilocalLogPrimePowerCoefficient (twoPrime, 0) *
      ContinuousLinearMap.opTrace (primeTwoLogOperator 1)
  set S : suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
      ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log 2))
  have hpr1 : inner ℂ (ccmFinitePrimeOperator a f) f =
      ContinuousLinearMap.opTrace (ccmFinitePrimeOperator a ∘L InnerProductSpace.rankOne ℂ f f) :=
    (opTrace_comp_rankOne_self_of_isSelfAdjoint (ccmFinitePrimeOperator_isSelfAdjoint a) f).symm
  have hpr2 : ContinuousLinearMap.opTrace
      (ccmFinitePrimeOperator a ∘L InnerProductSpace.rankOne ℂ f f) =
      ContinuousLinearMap.opTrace ((c • S) ∘L InnerProductSpace.rankOne ℂ f f) :=
    congrArg (fun T : suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a =>
      ContinuousLinearMap.opTrace (T ∘L InnerProductSpace.rankOne ℂ f f))
      (ccmFinitePrimeOperator_eq_primeTwoLogTrace_of_le_halfLogThree ha)
  have hpr3 : ContinuousLinearMap.opTrace ((c • S) ∘L InnerProductSpace.rankOne ℂ f f) =
      c * ContinuousLinearMap.opTrace (S ∘L InnerProductSpace.rankOne ℂ f f) := by
    have hcomp : (c • S) ∘L InnerProductSpace.rankOne ℂ f f =
        c • (S ∘L InnerProductSpace.rankOne ℂ f f) :=
      clm_smul_comp c S (InnerProductSpace.rankOne ℂ f f)
    exact (congrArg ContinuousLinearMap.opTrace hcomp).trans
      (RHTower.opTrace_smul c (S ∘L InnerProductSpace.rankOne ℂ f f))
  have hpr : inner ℂ (ccmFinitePrimeOperator a f) f =
      c * ContinuousLinearMap.opTrace (S ∘L InnerProductSpace.rankOne ℂ f f) :=
    hpr1.trans (hpr2.trans hpr3)
  linarith [primeFreeFamily_Q_eq a u, hQ, hpol, congrArg Complex.re hpr]

/-- Combined `{∞, 2}` trace-identity package: pairs the Connes–Consani archimedean Sonin cutoff
trace formula `-W_∞(g★ ⋆ g) = Tr(ϑ(g)(1 - P₁ - P̂₁)ϑ(g)†)` with the positive `2`-adic logarithmic
trace operator `K_2(m)` (`Tr(K_2(m)) = m log 2`) and the exact closed-window `{∞, 2}` restricted
Weil trace identity through `½ log 3`. -/
theorem archimedean_and_primeTwo_trace_identity_through_halfLogThree :
    (∀ g : CCMCompactSchwartzLogTest,
      -ccmArchimedeanWeilDistribution (ccmSoninGramTest g) =
        ContinuousLinearMap.opTrace
          (ccmIntegratedScaling (ccmSchwartzLogKernel g.toSchwartzMap) ∘L
            (1 - evenIndicatorCutoff 1 - evenFourierCutoff 1) ∘L
            ContinuousLinearMap.adjoint
              (ccmIntegratedScaling (ccmSchwartzLogKernel g.toSchwartzMap)))) ∧
    (∀ m : ℕ, ContinuousLinearMap.IsPositive (primeTwoLogOperator m) ∧
      ContinuousLinearMap.IsTraceClass (primeTwoLogOperator m) ∧
      ContinuousLinearMap.opTrace (primeTwoLogOperator m) = (m : ℂ) * (Real.log 2 : ℂ)) ∧
    (∀ (a : SuzukiPositiveAperture), a.1 ≤ Real.log 3 / 2 →
      ∀ u : CCMArchimedeanFormDomain a,
        ccmRestrictedWeilSourceQuadratic a u =
          archPart a u +
            (ContinuousLinearMap.opTrace (ccmPolarOperator a ∘L
              InnerProductSpace.rankOne ℂ (ccmArchimedeanFormToAperture a u)
                (ccmArchimedeanFormToAperture a u))).re -
            (soninSemilocalLogPrimePowerCoefficient (twoPrime, 0) *
              ContinuousLinearMap.opTrace (primeTwoLogOperator 1) *
              ContinuousLinearMap.opTrace
                (ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log 2)) ∘L
                  InnerProductSpace.rankOne ℂ (ccmArchimedeanFormToAperture a u)
                    (ccmArchimedeanFormToAperture a u))).re) :=
  ⟨neg_ccmArchimedeanWeilDistribution_ccmSoninGramTest,
    fun m => ⟨primeTwoLogOperator_isPositive m, primeTwoLogOperator_isTraceClass m,
      opTrace_primeTwoLogOperator m⟩,
    fun _ ha u => ccmRestrictedWeilSourceQuadratic_eq_semilocalPrimeTwoTrace_of_le_halfLogThree ha u⟩

end GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace

end
