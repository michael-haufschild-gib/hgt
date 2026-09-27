import GaloisForLFunctions.RHTower.XiGaussianMultiplierNullFamily
import GaloisForLFunctions.RHTower.XiGaussianPolarAnnihilator

/-!
# Native Xi energy has no positive spectral interval floor

The square integral over a nondegenerate nonpositive real spectral interval
is positive definite on polynomials. Nevertheless every nonzero polynomial
principal ideal contains tests with interval energy at least one and native
energy arbitrarily small, uniformly throughout a fixed positive heat half-line.
This includes exact polar cancellation. The complete source and every mixed
term with the native unit ball are controlled at the same cutoff.

The interval Gram is an auxiliary positive form, not the actual Xi Hankel form.
The result rules out a finite domination constant for this proposed source of
positive energy; it asserts neither an actual negative Xi witness nor RH.
-/

open Complex Polynomial MeasureTheory Filter Topology
open scoped BigOperators Real
noncomputable section
namespace RHTower

/-- The full square integral retains every coefficient cross term. -/
def xiSpectralIntervalEnergy (a b : ℝ) (P : Polynomial ℝ) : ℝ :=
  ∫ x in Set.Icc a b, (P.eval x) ^ 2

theorem xiSpectralIntervalEnergy_C_mul (a b c : ℝ) (P : Polynomial ℝ) :
    xiSpectralIntervalEnergy a b (Polynomial.C c * P) =
      c ^ 2 * xiSpectralIntervalEnergy a b P := by
  simp only [xiSpectralIntervalEnergy, Polynomial.eval_mul, Polynomial.eval_C,
    mul_pow, integral_const_mul]

/-- Any nonzero polynomial has positive interval energy. -/
theorem xiSpectralIntervalEnergy_pos (a : ℝ) (b : Set.Ioi a)
    (P : {P : Polynomial ℝ // P ≠ 0}) :
    0 < xiSpectralIntervalEnergy a b P := by
  have hi : IntegrableOn (fun x : ℝ => (P.1.eval x) ^ 2) (Set.Icc a b) volume :=
    (P.1.continuous.pow 2).integrableOn_Icc
  rw [xiSpectralIntervalEnergy,
    setIntegral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall fun x => sq_nonneg (P.1.eval x)) hi]
  let U := Set.Ioo a (b : ℝ) ∩ {x : ℝ | P.1.eval x ≠ 0}
  have hopen : IsOpen U := isOpen_Ioo.inter (isOpen_ne.preimage P.1.continuous)
  have hne : U.Nonempty := by
    by_contra h
    have hsub : Set.Ioo a (b : ℝ) ⊆ {x : ℝ | P.1.IsRoot x} := by
      intro x hx
      by_contra hpx
      exact h ⟨x, hx, hpx⟩
    exact P.property (Polynomial.eq_zero_of_infinite_isRoot P.1
      ((Set.Ioo_infinite b.property).mono hsub))
  have hsub : U ⊆ Function.support (fun x : ℝ => (P.1.eval x) ^ 2) ∩ Set.Icc a b := by
    intro x hx
    exact ⟨pow_ne_zero 2 hx.2, hx.1.1.le, hx.1.2.le⟩
  exact (hopen.measure_pos volume hne).trans_le (measure_mono hsub)

/-- The actual divisor product increases this auxiliary Gram on a nonpositive
interval. The inequality concerns the full polynomial, not separate monomials. -/
theorem xiSpectralIntervalEnergy_le_mul_annihilator
    (a : ℝ) (b : Set.Iic (0 : ℝ)) (B : Polynomial ℝ) (F : Finset XiZeroCopy) :
    xiSpectralIntervalEnergy a b B ≤
      xiSpectralIntervalEnergy a b (B * xiGaussianAnnihilator F) := by
  apply setIntegral_mono_on (B.continuous.pow 2).integrableOn_Icc
    ((B * xiGaussianAnnihilator F).continuous.pow 2).integrableOn_Icc measurableSet_Icc
  intro x hx
  change (B.eval x) ^ 2 ≤ ((B * xiGaussianAnnihilator F).eval x) ^ 2
  have hA := one_le_xiGaussianAnnihilator_eval_nonpos F ⟨x, hx.2.trans b.property⟩
  have hA2 : 1 ≤ ((xiGaussianAnnihilator F).eval x) ^ 2 := by nlinarith
  simpa only [Polynomial.eval_mul, mul_pow, mul_one] using
    mul_le_mul_of_nonneg_left hA2 (sq_nonneg (B.eval x))

/-- Even after any fixed algebraic constraints, interval-normalized tests can
have arbitrarily small native energy and complete source at every later time.
The mixed term is preserved explicitly and is uniform over all polynomial orders. -/
theorem exists_xiGaussian_principalIdeal_interval_large_source_small
    (a : ℝ) (b : {b : ℝ // a < b ∧ b ≤ 0})
    (B : {B : Polynomial ℝ // B ≠ 0})
    (t₀ : {t : ℝ // 0 < t}) (ε : {ε : ℝ // 0 < ε}) :
    ∃ Q : Polynomial ℝ, B.1 ∣ Q ∧ 1 ≤ xiSpectralIntervalEnergy a b Q ∧
      ∀ s : Set.Ici (t₀ : ℝ),
        let t := xiGaussianHeatAfter t₀ s
        xiGaussianNativeEnergy Q t < (ε : ℝ) ∧
        |xiGaussianCompletedSourceResidual Q t| < π * (ε : ℝ) ∧
        ∀ P : {P : Polynomial ℝ // xiGaussianNativeEnergy P t₀ ≤ 1},
          |xiGaussianCompletedSourceResidual (P.1 + Q) t -
            xiGaussianCompletedSourceResidual P.1 t -
            xiGaussianCompletedSourceResidual Q t| < (ε : ℝ) := by
  let m := xiSpectralIntervalEnergy a b B
  have hm : 0 < m := xiSpectralIntervalEnergy_pos a ⟨b, b.property.1⟩ B
  let D := Polynomial.C ((Real.sqrt m)⁻¹) * B.1
  have hD : xiSpectralIntervalEnergy a b D = 1 := by
    rw [xiSpectralIntervalEnergy_C_mul, inv_pow, Real.sq_sqrt hm.le]
    exact inv_mul_cancel₀ hm.ne'
  obtain ⟨F, hF, hmix⟩ := ((eventually_xiGaussian_mul_annihilator_heatHalfLine_small D t₀ ε).and
    (eventually_xiGaussian_mul_annihilator_mixed_source_small D t₀ ε)).exists
  refine ⟨D * xiGaussianAnnihilator F, ?_, ?_, fun s => ⟨(hF s).1, (hF s).2, hmix s⟩⟩
  · exact dvd_mul_of_dvd_left (dvd_mul_left B.1 (Polynomial.C ((Real.sqrt m)⁻¹))) _
  · rw [← hD]
    exact xiSpectralIntervalEnergy_le_mul_annihilator a ⟨b, b.property.2⟩ D F

/-- No finite native-energy domination constant exists, even on an arbitrary
nonzero principal ideal. This is a fixed-time, all-orders obstruction. -/
theorem not_xiGaussian_principalIdeal_spectralInterval_dominated
    (a : ℝ) (b : {b : ℝ // a < b ∧ b ≤ 0})
    (B : {B : Polynomial ℝ // B ≠ 0}) (t : {t : ℝ // 0 < t}) :
    ¬ ∃ C : ℝ, ∀ P : {P : Polynomial ℝ // B.1 ∣ P},
      xiSpectralIntervalEnergy a b P ≤ C * xiGaussianNativeEnergy P t := by
  rintro ⟨C, hC⟩
  have hlim : Tendsto (fun F : Finset XiZeroCopy =>
      C * xiGaussianNativeEnergy (B.1 * xiGaussianAnnihilator F) t) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_xiGaussianNativeEnergy_mul_annihilator_zero B.1 t).const_mul C
  have hbad : xiSpectralIntervalEnergy a b B ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall fun F =>
      (xiSpectralIntervalEnergy_le_mul_annihilator a ⟨b, b.property.2⟩ B F).trans
        (hC ⟨B.1 * xiGaussianAnnihilator F, dvd_mul_right _ _⟩))
  exact (not_le_of_gt (xiSpectralIntervalEnergy_pos a ⟨b, b.property.1⟩ B)) hbad

/-- Replacing the native energy by the absolute value of the complete signed
prime--Gamma source cannot supply the missing interval Gram floor either. -/
theorem not_xiGaussian_principalIdeal_spectralInterval_source_dominated
    (a : ℝ) (b : {b : ℝ // a < b ∧ b ≤ 0})
    (B : {B : Polynomial ℝ // B ≠ 0}) (t : {t : ℝ // 0 < t}) :
    ¬ ∃ C : ℝ, ∀ P : {P : Polynomial ℝ // B.1 ∣ P},
      xiSpectralIntervalEnergy a b P ≤ C * |xiGaussianCompletedSourceResidual P t| := by
  rintro ⟨C, hC⟩
  apply not_xiGaussian_principalIdeal_spectralInterval_dominated a b B t
  refine ⟨|C| * π, fun P => (hC P).trans ?_⟩
  calc
    _ ≤ |C| * |xiGaussianCompletedSourceResidual P t| :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg _)
    _ ≤ |C| * (π * xiGaussianNativeEnergy P t) :=
      mul_le_mul_of_nonneg_left (abs_xiGaussianCompletedSourceResidual_le_energy P t)
        (abs_nonneg C)
    _ = _ := (mul_assoc _ _ _).symm

/-- Exact pole cancellation does not repair the continuum Gram bound. The
full source and all its mixed interactions are small on one heat half-line. -/
theorem exists_xiGaussian_poleFree_interval_large_source_small
    (t₀ : {t : ℝ // 0 < t}) (ε : {ε : ℝ // 0 < ε}) :
    ∃ Q : Polynomial ℝ, Q.eval (-(1 / 4 : ℝ)) = 0 ∧
      1 ≤ xiSpectralIntervalEnergy (-1) 0 Q ∧
      ∀ s : Set.Ici (t₀ : ℝ),
        let t := xiGaussianHeatAfter t₀ s
        xiGaussianNativeEnergy Q t < (ε : ℝ) ∧
        |xiGaussianCompletedSourceResidual Q t| < π * (ε : ℝ) ∧
        ∀ P : {P : Polynomial ℝ // xiGaussianNativeEnergy P t₀ ≤ 1},
          |xiGaussianCompletedSourceResidual (P.1 + Q) t -
            xiGaussianCompletedSourceResidual P.1 t -
            xiGaussianCompletedSourceResidual Q t| < (ε : ℝ) := by
  obtain ⟨Q, ⟨R, hR⟩, hQ, hsmall⟩ :=
    exists_xiGaussian_principalIdeal_interval_large_source_small (-1)
      ⟨0, neg_one_lt_zero, le_rfl⟩
      ⟨Polynomial.X + Polynomial.C (1 / 4 : ℝ), Polynomial.X_add_C_ne_zero _⟩ t₀ ε
  refine ⟨Q, ?_, hQ, hsmall⟩
  rw [hR]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, neg_add_cancel, zero_mul]

end RHTower
