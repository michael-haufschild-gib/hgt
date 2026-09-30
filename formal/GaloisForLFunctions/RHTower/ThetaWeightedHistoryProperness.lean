import GaloisForLFunctions.RHTower.ThetaRealShiftHistory
import GaloisForLFunctions.RHTower.HedenmalmThetaDerivativeHistoryFourier

/-!
# Proper derivative history throughout the positive theta-weight range

The complementary exponent `2-q` supplies the actual bounded Fourier
evaluation on `L²(k^(-q) dx)`. Density-unitary cancellation identifies it
with the literal integral. Hardy's real Xi divisor annihilates the entire
closed derivative history, while a phase-twisted source has positive mass.
-/

open MeasureTheory Set Filter Topology Complex

namespace RHTower

open HedenmalmThetaSource GaloisForLFunctions.HTGeometry

noncomputable section

attribute [local instance 2000] Real.measurableSpace
attribute [local instance 2000] NormedSpace.complexToReal

/-- The everywhere-positive density unitary of the literal theta carrier. -/
def thetaPowerDensityUnitary (q : ℝ) :
    Lp ℂ 2 (thetaPowerWeightedMeasure q) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  weightedDensityUnitary (μ := (volume : Measure ℝ)) (fun x => thetaCuspFullSource x ^ (-q))
    (contDiff_thetaCuspFullSource.continuous.rpow_const
      fun x => Or.inl (thetaCuspFullSource_pos_all x).ne').measurable
    (fun x => Real.rpow_pos_of_pos (thetaCuspFullSource_pos_all x) _)

theorem thetaPowerDensityUnitary_coe (q : ℝ)
    (f : Lp ℂ 2 (thetaPowerWeightedMeasure q)) :
    (thetaPowerDensityUnitary q f : ℝ → ℂ) =ᵐ[volume]
      fun x => (Real.sqrt (thetaCuspFullSource x ^ (-q)) : ℂ) * f x :=
  densityMul_ae _
    (contDiff_thetaCuspFullSource.continuous.rpow_const
      fun x => Or.inl (thetaCuspFullSource_pos_all x).ne').measurable
    (fun x => Real.rpow_pos_of_pos (thetaCuspFullSource_pos_all x) _) f

theorem thetaPowerWeightedMeasure_ae_eq (q : ℝ) {β : Type*} {f g : ℝ → β} :
    f =ᵐ[thetaPowerWeightedMeasure q] g ↔ f =ᵐ[volume] g :=
  withDensity_realDensity_ae_eq
    (contDiff_thetaCuspFullSource.continuous.rpow_const
      fun x => Or.inl (thetaCuspFullSource_pos_all x).ne').measurable
    (fun x => Real.rpow_pos_of_pos (thetaCuspFullSource_pos_all x) _)

/-- Complementary weighted admission proves the reciprocal-density moment. -/
theorem integrable_thetaSource_rpow_of_lt_two (q : ℝ) (hq : 0 < q) (hq2 : q < 2) :
    Integrable (fun x => thetaCuspFullSource x ^ q) := by
  have hm := thetaWeightedDerivative_memLp (2-q) (by linarith) (by linarith) 0
  simp only [iteratedDeriv_zero] at hm
  have h := (memLp_ofReal_thetaPowerWeightedMeasure_iff (2-q)
    contDiff_thetaCuspFullSource.continuous).mp hm
  convert h using 1
  funext x
  dsimp only [thetaPowerWeightedEnergy]
  rw [← Real.rpow_natCast, ← Real.rpow_add (thetaCuspFullSource_pos_all x)]
  congr 1
  norm_num

/-- Every real Fourier phase twist of the source is genuinely admitted. -/
theorem thetaRealFourierTest_memLp (q : ℝ) (hq : 0 < q) (hq2 : q < 2) (t : ℝ) :
    MemLp (fun x : ℝ => (thetaCuspFullSource x : ℂ) *
      Complex.exp (-(Complex.I * (t : ℂ) * (x : ℂ)))) 2
      (thetaPowerWeightedMeasure q) := by
  have hm := thetaWeightedDerivative_memLp q hq hq2 0
  simp only [iteratedDeriv_zero] at hm
  have hc := contDiff_thetaCuspFullSource.continuous
  apply hm.congr_norm
  · exact (by fun_prop : Continuous (fun x : ℝ => (thetaCuspFullSource x : ℂ) *
      Complex.exp (-(Complex.I * (t : ℂ) * (x : ℂ))))).aestronglyMeasurable
  · filter_upwards with x
    simp [Complex.norm_exp]

def thetaWeightedRealFourierTest (q : ℝ) (hq : 0 < q) (hq2 : q < 2) (t : ℝ) :
    Lp ℂ 2 (thetaPowerWeightedMeasure q) :=
  (thetaRealFourierTest_memLp q hq hq2 t).toLp _

theorem thetaWeightedRealFourierTest_coe (q : ℝ) (hq : 0 < q) (hq2 : q < 2) (t : ℝ) :
    (thetaWeightedRealFourierTest q hq hq2 t : ℝ → ℂ) =ᵐ[volume]
      fun x => (thetaCuspFullSource x : ℂ) *
        Complex.exp (-(Complex.I * (t : ℂ) * (x : ℂ))) :=
  (thetaPowerWeightedMeasure_ae_eq q).mp
    (thetaRealFourierTest_memLp q hq hq2 t).coeFn_toLp

private theorem complementary_sqrt_weights {k : ℝ} (hk : 0 < k) (q : ℝ) :
    Real.sqrt (k ^ (-(2-q))) * k * Real.sqrt (k ^ (-q)) = 1 := by
  calc
    _ = (Real.sqrt (k ^ (-(2-q))) * Real.sqrt (k ^ (-q))) * k := by ring
    _ = Real.sqrt (k ^ (-(2-q)) * k ^ (-q)) * k := by
      rw [Real.sqrt_mul (Real.rpow_nonneg hk.le _)]
    _ = Real.sqrt (k ^ (-2 : ℝ)) * k := by
      rw [← Real.rpow_add hk, show -(2-q) + -q = (-2 : ℝ) by ring]
    _ = 1 := by
      rw [Real.rpow_neg hk.le, show (2 : ℝ) = (2 : ℕ) by norm_num,
        Real.rpow_natCast, Real.sqrt_inv, Real.sqrt_sq hk.le, inv_mul_cancel₀ hk.ne']

/-- Literal real Fourier evaluation, constructed from the complementary carrier. -/
def thetaWeightedRealFourierFunctional (q : ℝ) (hq : 0 < q) (hq2 : q < 2) (t : ℝ) :
    Lp ℂ 2 (thetaPowerWeightedMeasure q) →L[ℂ] ℂ :=
  (innerSL ℂ (thetaPowerDensityUnitary (2-q)
    (thetaWeightedRealFourierTest (2-q) (by linarith) (by linarith) t))).comp
    (thetaPowerDensityUnitary q).toContinuousLinearEquiv.toContinuousLinearMap

private theorem thetaWeightedRealFourier_inner_integrand
    (q : ℝ) (hq : 0 < q) (hq2 : q < 2) (t : ℝ)
    (f : Lp ℂ 2 (thetaPowerWeightedMeasure q)) :
    (fun x => inner ℂ
      (thetaPowerDensityUnitary (2-q)
        (thetaWeightedRealFourierTest (2-q) (by linarith) (by linarith) t) x)
      (thetaPowerDensityUnitary q f x)) =ᵐ[volume]
      fun x => f x * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) := by
  filter_upwards [thetaPowerDensityUnitary_coe q f,
    thetaPowerDensityUnitary_coe (2-q)
      (thetaWeightedRealFourierTest (2-q) (by linarith) (by linarith) t),
    thetaWeightedRealFourierTest_coe (2-q) (by linarith) (by linarith) t]
    with x hf hu ht
  rw [hf, hu, ht]
  change (Real.sqrt (thetaCuspFullSource x ^ (-q)) : ℂ) * f x *
    (starRingEnd ℂ) ((Real.sqrt (thetaCuspFullSource x ^ (-(2-q))) : ℂ) *
      ((thetaCuspFullSource x : ℂ) *
        Complex.exp (-(Complex.I * (t : ℂ) * (x : ℂ))))) = _
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  have hc : (starRingEnd ℂ) (-(Complex.I * (t : ℂ) * (x : ℂ))) =
      Complex.I * (t : ℂ) * (x : ℂ) := by simp
  rw [hc]
  have hw : (Real.sqrt (thetaCuspFullSource x ^ (-(2-q))) : ℂ) *
      (thetaCuspFullSource x : ℂ) *
      (Real.sqrt (thetaCuspFullSource x ^ (-q)) : ℂ) = 1 := by
    exact_mod_cast complementary_sqrt_weights (thetaCuspFullSource_pos_all x) q
  calc
    _ = ((Real.sqrt (thetaCuspFullSource x ^ (-(2-q))) : ℂ) *
      (thetaCuspFullSource x : ℂ) *
      (Real.sqrt (thetaCuspFullSource x ^ (-q)) : ℂ)) *
      (f x * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) := by ring
    _ = _ := by rw [hw, one_mul]

theorem integrable_thetaWeightedRealFourierIntegrand
    (q : ℝ) (hq : 0 < q) (hq2 : q < 2) (t : ℝ)
    (f : Lp ℂ 2 (thetaPowerWeightedMeasure q)) :
    Integrable (fun x => f x * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) :=
  (L2.integrable_inner
    (thetaPowerDensityUnitary (2-q)
      (thetaWeightedRealFourierTest (2-q) (by linarith) (by linarith) t))
    (thetaPowerDensityUnitary q f)).congr
      (thetaWeightedRealFourier_inner_integrand q hq hq2 t f)

theorem thetaWeightedRealFourierFunctional_apply
    (q : ℝ) (hq : 0 < q) (hq2 : q < 2) (t : ℝ)
    (f : Lp ℂ 2 (thetaPowerWeightedMeasure q)) :
    thetaWeightedRealFourierFunctional q hq hq2 t f =
      ∫ x : ℝ, f x * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) := by
  change inner ℂ
    (thetaPowerDensityUnitary (2-q)
      (thetaWeightedRealFourierTest (2-q) (by linarith) (by linarith) t))
    (thetaPowerDensityUnitary q f) = _
  rw [L2.inner_def]
  exact integral_congr_ae (thetaWeightedRealFourier_inner_integrand q hq hq2 t f)

theorem norm_thetaWeightedRealFourierIntegral_le
    (q : ℝ) (hq : 0 < q) (hq2 : q < 2) (t : ℝ)
    (f : Lp ℂ 2 (thetaPowerWeightedMeasure q)) :
    ‖∫ x : ℝ, f x * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))‖ ≤
      ‖thetaWeightedRealFourierFunctional q hq hq2 t‖ * ‖f‖ := by
  rw [← thetaWeightedRealFourierFunctional_apply q hq hq2 t f]
  exact (thetaWeightedRealFourierFunctional q hq hq2 t).le_opNorm f

theorem thetaWeightedRealFourierFunctional_test
    (q : ℝ) (hq : 0 < q) (hq2 : q < 2) (t : ℝ) :
    thetaWeightedRealFourierFunctional q hq hq2 t
      (thetaWeightedRealFourierTest q hq hq2 t) = (thetaSource.mass : ℂ) := by
  rw [thetaWeightedRealFourierFunctional_apply]
  calc
    _ = ∫ x : ℝ, (thetaCuspFullSource x : ℂ) := by
      apply integral_congr_ae
      filter_upwards [thetaWeightedRealFourierTest_coe q hq hq2 t] with x hx
      rw [hx, mul_assoc, ← Complex.exp_add, neg_add_cancel,
        Complex.exp_zero, mul_one]
    _ = (thetaSource.mass : ℂ) := by rw [integral_complex_ofReal]; rfl

theorem thetaWeightedRealFourierFunctional_ne_zero
    (q : ℝ) (hq : 0 < q) (hq2 : q < 2) (t : ℝ) :
    thetaWeightedRealFourierFunctional q hq hq2 t ≠ 0 := by
  intro hzero
  have h := thetaWeightedRealFourierFunctional_test q hq hq2 t
  rw [hzero] at h
  change (0 : ℂ) = (thetaSource.mass : ℂ) at h
  exact (by exact_mod_cast thetaSource.mass_ne_zero : (thetaSource.mass : ℂ) ≠ 0) h.symm

theorem thetaWeightedRealFourierFunctional_derivative
    (q : ℝ) (hq : 0 < q) (hq2 : q < 2) (t : ℝ) (n : ℕ) :
    thetaWeightedRealFourierFunctional q hq hq2 t (thetaWeightedDerivativeVector q n) =
      (-Complex.I * (t : ℂ)) ^ n * XiC (t : ℂ) := by
  rw [thetaWeightedRealFourierFunctional_apply]
  apply (integral_congr_ae ?_).trans (thetaSourceDerivativeFourierIntegral (t : ℂ) n)
  filter_upwards [(thetaPowerWeightedMeasure_ae_eq q).mp
    (thetaWeightedDerivativeVector_coe q hq hq2 n)] with x hx
  rw [hx]

theorem thetaWeightedDerivativeHistory_le_ker_realFourierFunctional
    (q : ℝ) (hq : 0 < q) (hq2 : q < 2) {t : ℝ} (ht : XiC (t : ℂ) = 0) :
    thetaWeightedDerivativeHistory q ≤ (thetaWeightedRealFourierFunctional q hq hq2 t).ker := by
  apply (Submodule.span ℂ (range (thetaWeightedDerivativeVector q))).topologicalClosure_minimal
    (Submodule.span_le.mpr ?_) (thetaWeightedRealFourierFunctional q hq hq2 t).isClosed_ker
  rintro _ ⟨n, rfl⟩
  change thetaWeightedRealFourierFunctional q hq hq2 t (thetaWeightedDerivativeVector q n) = 0
  rw [thetaWeightedRealFourierFunctional_derivative, ht, mul_zero]

theorem thetaWeightedRealFourierFunctional_history
    (q : ℝ) (hq : 0 < q) (hq2 : q < 2) {t : ℝ} (ht : XiC (t : ℂ) = 0)
    {f : Lp ℂ 2 (thetaPowerWeightedMeasure q)} (hf : f ∈ thetaWeightedDerivativeHistory q) :
    thetaWeightedRealFourierFunctional q hq hq2 t f = 0 :=
  thetaWeightedDerivativeHistory_le_ker_realFourierFunctional q hq hq2 ht hf

/-- Every positive theta weight below two has a proper actual derivative history. -/
theorem thetaWeightedDerivativeHistory_ne_top (q : ℝ) (hq : 0 < q) (hq2 : q < 2) :
    thetaWeightedDerivativeHistory q ≠ ⊤ := by
  intro htop
  obtain ⟨t, _, htzero⟩ := exists_Xi_zero_gt 0
  have ht : XiC (t : ℂ) = 0 := by rw [XiC_ofReal, htzero]; simp
  apply thetaWeightedRealFourierFunctional_ne_zero q hq hq2 t
  apply ContinuousLinearMap.ext
  intro f
  exact thetaWeightedRealFourierFunctional_history q hq hq2 ht (by rw [htop]; trivial)

end

end RHTower
