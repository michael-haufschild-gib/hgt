import GaloisForLFunctions.RHTower.FieldOnePadicRamifiedTateEquation258
import GaloisForLFunctions.RHTower.FieldOnePadicBruhatFourierSelfMap

/-!
# Absolute convergence of ramified critical Tate integrals

Every p-adic Bruhat--Schwartz test has support bounded below in valuation.
At the critical exponent its multiplicative Mellin integrand is dominated on
the remaining shells by a one-sided geometric series with ratio
`1 / sqrt(p)`.  This file proves that argument on the literal decomposition
`ℚ_pˣ ≃ ℤ × ℤ_pˣ`, for both a character and its inverse.

The resulting integrability theorems are unconditional for every Bruhat test;
they justify all later linearity and projection arguments for equation (2.258).
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set
open scoped BigOperators NNReal ENNReal

variable (p : ℕ) [Fact p.Prime]

def fieldOneIntTailEquiv (K : ℤ) : ℕ ≃ {k : ℤ // K ≤ k} where
  toFun n := ⟨K + n, by omega⟩
  invFun k := (k.1 - K).toNat
  left_inv n := by simp
  right_inv k := by
    apply Subtype.ext
    change K + (((k.1 - K).toNat : ℕ) : ℤ) = k.1
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr k.2)]
    ring

theorem fieldOne_summable_int_geometric_tail
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (K : ℤ) :
    Summable (fun k : ℤ => if K ≤ k then r ^ (k - K).toNat else 0) := by
  let f : ℤ → ℝ := fun k => r ^ (k - K).toNat
  have hgeo : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_norm_lt_one (by
      simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)
  have hsub : Summable (f ∘ ((↑) : {k : ℤ // K ≤ k} → ℤ)) := by
    rw [← (fieldOneIntTailEquiv K).summable_iff]
    convert hgeo using 1
    funext n
    simp [f, fieldOneIntTailEquiv]
  have hind : Summable ((Set.Ici K).indicator f) :=
    summable_subtype_iff_indicator.mp hsub
  convert hind using 1
  funext k
  by_cases hk : K ≤ k <;> simp [f, Set.indicator, hk]

theorem fieldOnePadicDenominatorStage_coordinates_iff
    (N : ℕ) (k : ℤ) (u : ℤ_[p]ˣ) :
    ((((fieldOnePadicValuationUnitContinuousMulEquiv p)
        (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p])) ∈
        fieldOnePadicDenominatorStage p N ↔
      -(N : ℤ) ≤ k := by
  change ‖(p : ℚ_[p]) ^ N *
    (((fieldOnePadicValuationUnitContinuousMulEquiv p)
      (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1 ↔ _
  rw [Padic.norm_le_one_iff_val_nonneg]
  have hp0 : (p : ℚ_[p]) ^ N ≠ 0 :=
    pow_ne_zero N (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
  have hx0 : (((fieldOnePadicValuationUnitContinuousMulEquiv p)
      (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p]) ≠ 0 :=
    Units.ne_zero _
  rw [Padic.valuation_mul hp0 hx0, Padic.valuation_pow,
    Padic.valuation_p]
  have hval : Padic.valuation
      ((((fieldOnePadicValuationUnitContinuousMulEquiv p)
        (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p])) = k :=
    fieldOnePadic_valuation_forward p (Multiplicative.ofAdd k, u)
  rw [hval]
  simp only [mul_one]
  omega

theorem norm_fieldOnePadicRamifiedCriticalCharacter
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (ρ : Circle) (a : ℚ_[p]ˣ) :
    ‖fieldOnePadicRamifiedCriticalCharacter p n χ ρ a‖ = 1 := by
  unfold fieldOnePadicRamifiedCriticalCharacter
  rw [norm_mul, norm_zpow, Circle.norm_coe, one_zpow, one_mul]
  exact DirichletCharacter.unit_norm_eq_one χ.1 _

theorem continuous_fieldOnePadicRamifiedCriticalCharacter
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (ρ : Circle) :
    Continuous (fieldOnePadicRamifiedCriticalCharacter p n χ ρ) := by
  have hval : Continuous (fun a : ℚ_[p]ˣ => Padic.valuation (a : ℚ_[p])) := by
    exact (continuous_of_discreteTopology : Continuous
      (fun z : Multiplicative ℤ => z.toAdd)).comp
        (continuous_fieldOnePadic_valuation p)
  have hrad : Continuous (fun a : ℚ_[p]ˣ =>
      (ρ : ℂ) ^ Padic.valuation (a : ℚ_[p])) :=
    (continuous_of_discreteTopology : Continuous
      (fun k : ℤ => (ρ : ℂ) ^ k)).comp hval
  have hang : Continuous (fun a : ℚ_[p]ˣ =>
      χ.1 (fieldOnePadicUnitReduction p n
        (fieldOnePadicAngularUnit p a))) :=
    (continuous_of_discreteTopology : Continuous
      (fun r : (ZMod (p ^ n))ˣ => χ.1 r)).comp
        ((fieldOnePadicUnitReduction_continuous p n).comp
          (continuous_fieldOnePadicAngularUnit p))
  exact hrad.mul hang

theorem continuous_fieldOnePadicCriticalHalfDensity :
    Continuous (fieldOnePadicCriticalHalfDensity p) := by
  have hval : Continuous (fun a : ℚ_[p]ˣ => Padic.valuation (a : ℚ_[p])) := by
    exact (continuous_of_discreteTopology : Continuous
      (fun z : Multiplicative ℤ => z.toAdd)).comp
        (continuous_fieldOnePadic_valuation p)
  exact (continuous_of_discreteTopology : Continuous
    (fun k : ℤ => (Real.sqrt (p : ℝ) : ℂ) ^ (-k))).comp hval

theorem continuous_fieldOnePadicCriticalTateIntegrand
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (ρ : Circle) (f : compactlySupportedLocallyConstant ℚ_[p]) :
    Continuous (fieldOnePadicCriticalTateIntegrand p n χ ρ f) := by
  exact ((f.1.continuous.comp Units.continuous_val).mul
    (continuous_fieldOnePadicRamifiedCriticalCharacter p n χ ρ)).mul
      (continuous_fieldOnePadicCriticalHalfDensity p)

theorem continuous_fieldOnePadicDualCriticalTateIntegrand
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (ρ : Circle) (f : compactlySupportedLocallyConstant ℚ_[p]) :
    Continuous (fieldOnePadicDualCriticalTateIntegrand p n χ ρ f) := by
  have hne : ∀ a : ℚ_[p]ˣ,
      fieldOnePadicRamifiedCriticalCharacter p n χ ρ a ≠ 0 := by
    intro a hzero
    have hnorm := norm_fieldOnePadicRamifiedCriticalCharacter p n χ ρ a
    rw [hzero, norm_zero] at hnorm
    exact zero_ne_one hnorm
  exact ((f.1.continuous.comp Units.continuous_val).mul
    ((continuous_fieldOnePadicRamifiedCriticalCharacter p n χ ρ).inv₀ hne)).mul
      (continuous_fieldOnePadicCriticalHalfDensity p)

theorem norm_fieldOnePadicCriticalHalfDensity_coordinates
    (k : ℤ) (u : ℤ_[p]ˣ) :
    ‖fieldOnePadicCriticalHalfDensity p
        (fieldOnePadicValuationUnitContinuousMulEquiv p
          (Multiplicative.ofAdd k, u))‖ =
      (Real.sqrt (p : ℝ)) ^ (-k) := by
  rw [fieldOnePadicCriticalHalfDensity_coordinates, norm_zpow,
    Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (Real.sqrt_pos.2 (by
    exact_mod_cast (Fact.out : Nat.Prime p).pos))]

theorem fieldOneReal_sqrt_zpow_tail
    (K k : ℤ) (hk : K ≤ k) :
    (Real.sqrt (p : ℝ)) ^ (-k) =
      (Real.sqrt (p : ℝ)) ^ (-K) *
        ((Real.sqrt (p : ℝ))⁻¹) ^ (k - K).toNat := by
  let s := Real.sqrt (p : ℝ)
  have hs : 0 < s := Real.sqrt_pos.2 (by
    exact_mod_cast (Fact.out : Nat.Prime p).pos)
  have hd : (((k - K).toNat : ℕ) : ℤ) = k - K :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hk)
  calc
    s ^ (-k) = s ^ (-K + -(k - K)) := by congr 1; omega
    _ = s ^ (-K) * s ^ (-(k - K)) :=
      zpow_add₀ hs.ne' (-K) (-(k - K))
    _ = s ^ (-K) * s ^ (-(((k - K).toNat : ℕ) : ℤ)) := by rw [hd]
    _ = s ^ (-K) * (s⁻¹) ^ (k - K).toNat := by
      congr 1
      calc
        s ^ (-(((k - K).toNat : ℕ) : ℤ)) =
            (s ^ (((k - K).toNat : ℕ) : ℤ))⁻¹ := zpow_neg _ _
        _ = (s ^ (k - K).toNat)⁻¹ := by rw [zpow_natCast]
        _ = (s⁻¹) ^ (k - K).toNat := by rw [inv_pow]

theorem fieldOnePadicBruhat_coordinates_eq_zero_of_lt_neg_supportDepth
    (f : compactlySupportedLocallyConstant ℚ_[p]) (N : ℕ)
    (hsupport : tsupport (f.1 : ℚ_[p] → ℂ) ⊆
      fieldOnePadicDenominatorStage p N)
    (k : ℤ) (u : ℤ_[p]ˣ) (hk : k < -(N : ℤ)) :
    f.1 (((fieldOnePadicValuationUnitContinuousMulEquiv p)
      (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p]) = 0 := by
  by_contra hne
  have hts : ((((fieldOnePadicValuationUnitContinuousMulEquiv p)
      (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p])) ∈
      tsupport (f.1 : ℚ_[p] → ℂ) := subset_tsupport _ hne
  have hstage := hsupport hts
  have hkbound := (fieldOnePadicDenominatorStage_coordinates_iff p N k u).mp hstage
  omega

private theorem integrable_fieldOnePadicCriticalTateIntegrand_of_supportDepth
    (n N : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (ρ : Circle) (f : compactlySupportedLocallyConstant ℚ_[p])
    (hsupport : tsupport (f.1 : ℚ_[p] → ℂ) ⊆
      fieldOnePadicDenominatorStage p N) :
    Integrable (fieldOnePadicCriticalTateIntegrand p n χ ρ f)
      (fieldOnePadicMultiplicativeHaar p) := by
  let e := fieldOnePadicValuationUnitContinuousMulEquiv p
  let μu := fieldOnePadicUnitNormalizedHaar p
  let F : Multiplicative ℤ × ℤ_[p]ˣ → ℂ := fun z =>
    fieldOnePadicCriticalTateIntegrand p n χ ρ f (e z)
  have hFcont : Continuous F :=
    (continuous_fieldOnePadicCriticalTateIntegrand p n χ ρ f).comp e.continuous
  have hFmeas : AEStronglyMeasurable F
      (Measure.count.prod μu) := hFcont.aestronglyMeasurable
  obtain ⟨C, hC⟩ := f.1.continuous.bounded_above_of_compact_support f.2
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (f.1 0)) (hC 0)
  let K : ℤ := -(N : ℤ)
  let s : ℝ := Real.sqrt (p : ℝ)
  let r : ℝ := s⁻¹
  let D : ℝ := C * s ^ (-K)
  have hs : 1 < s := by
    have hp1 : (1 : ℝ) < p := by
      exact_mod_cast (Fact.out : Nat.Prime p).one_lt
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ p by positivity),
      Real.sqrt_nonneg (p : ℝ)]
  have hs0 : 0 < s := zero_lt_one.trans hs
  have hr0 : 0 ≤ r := inv_nonneg.mpr hs0.le
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hs
  have hD0 : 0 ≤ D := mul_nonneg hC0 (zpow_nonneg hs0.le _)
  have hMsumZ : Summable (fun k : ℤ =>
      if K ≤ k then D * r ^ (k - K).toNat else 0) := by
    have h := (fieldOne_summable_int_geometric_tail r hr0 hr1 K).mul_left D
    apply h.congr
    intro k
    by_cases hk : K ≤ k <;> simp [hk]
  let M : Multiplicative ℤ → ℝ := fun k =>
    if K ≤ k.toAdd then D * r ^ (k.toAdd - K).toNat else 0
  have hMsum : Summable M := by
    rw [← Multiplicative.ofAdd.summable_iff]
    convert hMsumZ using 1
    funext k
    simp only [Function.comp_apply, M]
    change (if K ≤ k then D * r ^ (k - K).toNat else 0) = _
    rfl
  have hMint : Integrable M Measure.count := by
    rw [integrable_count_iff]
    have hnorm : (fun k => ‖M k‖) = M := by
      funext k
      by_cases hk : K ≤ k.toAdd
      · rw [show M k = D * r ^ (k.toAdd - K).toNat by simp [M, hk]]
        exact Real.norm_of_nonneg (mul_nonneg hD0 (pow_nonneg hr0 _))
      · simp [M, hk]
    rw [hnorm]
    exact hMsum
  have hFint : Integrable F (Measure.count.prod μu) := by
    refine (integrable_prod_iff hFmeas).mpr ⟨?_, ?_⟩
    · filter_upwards with k
      exact (hFcont.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · apply hMint.mono'
      · exact (continuous_of_discreteTopology : Continuous
          (fun k : Multiplicative ℤ =>
            ∫ u, ‖F (k, u)‖ ∂μu)).aestronglyMeasurable
      · filter_upwards with k
        by_cases hk : K ≤ k.toAdd
        · have hslice : Integrable (fun u => ‖F (k, u)‖) μu :=
            ((hFcont.comp (continuous_const.prodMk continuous_id)).norm).integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _)
          calc
            ‖∫ u, ‖F (k, u)‖ ∂μu‖ = ∫ u, ‖F (k, u)‖ ∂μu := by
              rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
            _ ≤ ∫ _u : ℤ_[p]ˣ, C * s ^ (-k.toAdd) ∂μu := by
              apply integral_mono hslice (integrable_const _)
              intro u
              have hkrep := Multiplicative.ofAdd.apply_symm_apply k
              have heq : e (k, u) = e (Multiplicative.ofAdd k.toAdd, u) :=
                congrArg e (Prod.ext hkrep.symm rfl)
              dsimp only [F]
              unfold fieldOnePadicCriticalTateIntegrand
              rw [heq]
              rw [norm_mul, norm_mul,
                norm_fieldOnePadicRamifiedCriticalCharacter,
                mul_one, norm_fieldOnePadicCriticalHalfDensity_coordinates]
              exact mul_le_mul_of_nonneg_right (hC _) (zpow_nonneg hs0.le _)
            _ = C * s ^ (-k.toAdd) := by
              rw [integral_const, Measure.real,
                fieldOnePadicUnitNormalizedHaar_univ]
              simp
            _ = M k := by
              rw [fieldOneReal_sqrt_zpow_tail p K k.toAdd hk]
              simp only [M, if_pos hk, D, r]
              ring
        · have hklt : k.toAdd < -(N : ℤ) := by simpa [K] using lt_of_not_ge hk
          have hzero : (fun u => ‖F (k, u)‖) = 0 := by
            funext u
            have hkrep := Multiplicative.ofAdd.apply_symm_apply k
            have heq : e (k, u) = e (Multiplicative.ofAdd k.toAdd, u) :=
              congrArg e (Prod.ext hkrep.symm rfl)
            dsimp only [F]
            unfold fieldOnePadicCriticalTateIntegrand
            rw [heq]
            rw [fieldOnePadicBruhat_coordinates_eq_zero_of_lt_neg_supportDepth
              p f N hsupport k.toAdd u hklt]
            simp
          rw [hzero]
          simp [M, hk]
  change Integrable (fieldOnePadicCriticalTateIntegrand p n χ ρ f)
    (Measure.map e (fieldOnePadicValuationUnitProductHaar p))
  apply (integrable_map_equiv e.toHomeomorph.toMeasurableEquiv _).mpr
  change Integrable F (fieldOnePadicValuationUnitProductHaar p)
  simpa [fieldOnePadicValuationUnitProductHaar] using hFint

theorem integrable_fieldOnePadicCriticalTateIntegrand
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (ρ : Circle) (f : compactlySupportedLocallyConstant ℚ_[p]) :
    Integrable (fieldOnePadicCriticalTateIntegrand p n χ ρ f)
      (fieldOnePadicMultiplicativeHaar p) := by
  obtain ⟨N, _L, hsupport, _hperiod⟩ :=
    fieldOnePadicBruhat_exists_finiteLevel p f
  exact integrable_fieldOnePadicCriticalTateIntegrand_of_supportDepth
    p n N χ ρ f hsupport

theorem integrable_fieldOnePadicDualCriticalTateIntegrand
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (ρ : Circle) (f : compactlySupportedLocallyConstant ℚ_[p]) :
    Integrable (fieldOnePadicDualCriticalTateIntegrand p n χ ρ f)
      (fieldOnePadicMultiplicativeHaar p) := by
  have hpoint : (fun a => fieldOnePadicDualCriticalTateIntegrand p n χ ρ f a) =
      fun a => fieldOnePadicCriticalTateIntegrand p n χ ρ f a *
        ((fieldOnePadicRamifiedCriticalCharacter p n χ ρ a)⁻¹) ^ 2 := by
    funext a
    unfold fieldOnePadicDualCriticalTateIntegrand
    unfold fieldOnePadicCriticalTateIntegrand
    have hne : fieldOnePadicRamifiedCriticalCharacter p n χ ρ a ≠ 0 := by
      intro hzero
      have hnorm := norm_fieldOnePadicRamifiedCriticalCharacter p n χ ρ a
      rw [hzero, norm_zero] at hnorm
      exact zero_ne_one hnorm
    field_simp
  have hbase := integrable_fieldOnePadicCriticalTateIntegrand p n χ ρ f
  change Integrable (fun a =>
    fieldOnePadicDualCriticalTateIntegrand p n χ ρ f a)
    (fieldOnePadicMultiplicativeHaar p)
  rw [hpoint]
  apply hbase.mul_bdd (c := 1)
  · exact ((continuous_fieldOnePadicRamifiedCriticalCharacter p n χ ρ).inv₀
      (fun a hzero => by
        have hnorm := norm_fieldOnePadicRamifiedCriticalCharacter p n χ ρ a
        rw [hzero, norm_zero] at hnorm
        exact zero_ne_one hnorm)).pow 2 |>.aestronglyMeasurable
  · filter_upwards with a
    rw [norm_pow, norm_inv,
      norm_fieldOnePadicRamifiedCriticalCharacter]
    norm_num

end
end GaloisForLFunctions.RHTower
