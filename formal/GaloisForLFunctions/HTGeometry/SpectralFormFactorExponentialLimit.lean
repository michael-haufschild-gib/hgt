import GaloisForLFunctions.HTGeometry.SpectralFormFactorMoments
import GaloisForLFunctions.HTGeometry.MethodOfMomentsReal
import GaloisForLFunctions.HTGeometry.FiniteSpectralHaarRecurrenceLaw

/-!
# The exponential limit of the spectral form factor

Under product Haar measure the normalized spectral form factor of a finite level set is a squared
character sum, so its moments are exactly the sums of squared multinomial coefficients: every
character with a nonzero index integrates to zero, and only the diagonal pairs of multiplicity
vectors survive.

Those moment constants converge to the factorials, which are the moments of the unit-mean
exponential law, and they never exceed the factorials, so the whole family carries one
factorial-geometric moment bound.  The method of moments therefore identifies the weak limit as the
unit-mean exponential law.
-/

open Filter MeasureTheory ProbabilityTheory Topology UnitAddTorus

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section HaarMoments

private theorem fourier_one_pow (x : AddCircle (1 : ℝ)) (k : ℕ) :
    (fourier 1 x) ^ k = fourier (k : ℤ) x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih]
      have hcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
      rw [hcast, fourier_add]

theorem prod_mFourier_single_pow {D : ℕ} (p : Fin D → ℕ) (z : UnitAddTorus (Fin D)) :
    ∏ j : Fin D, (mFourier (Pi.single j (1 : ℤ)) z) ^ (p j) =
      mFourier (fun j => (p j : ℤ)) z := by
  have h1 : ∀ j : Fin D, mFourier (Pi.single j (1 : ℤ)) z = fourier 1 (z j) :=
    fun j => mFourier_single z j
  simp_rw [h1, fourier_one_pow]
  rfl

/-- The uniform phase sum on the product torus. -/
def torusPhaseSum (D : ℕ) (z : UnitAddTorus (Fin D)) : ℂ :=
  ∑ j : Fin D, mFourier (Pi.single j (1 : ℤ)) z

theorem torusPhaseSum_pow (D m : ℕ) (z : UnitAddTorus (Fin D)) :
    torusPhaseSum D z ^ m =
      ∑ p ∈ (Finset.univ : Finset (Fin D)).piAntidiag m,
        (Nat.multinomial Finset.univ p : ℂ) * mFourier (fun j => (p j : ℤ)) z := by
  rw [torusPhaseSum, Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [prod_mFourier_single_pow]

theorem continuous_torusPhaseSum (D : ℕ) : Continuous (torusPhaseSum D) := by
  refine continuous_finsetSum _ fun j _ => ?_
  exact (mFourier (Pi.single j (1 : ℤ))).continuous

/-- The normalized spectral form factor of a level set of prescribed size. -/
def torusSFF (D : ℕ) (z : UnitAddTorus (Fin D)) : ℝ := ‖torusPhaseSum D z‖ ^ 2 / D

theorem torusSFF_nonneg (D : ℕ) (z : UnitAddTorus (Fin D)) : 0 ≤ torusSFF D z := by
  rw [torusSFF]
  positivity

theorem continuous_torusSFF (D : ℕ) : Continuous (torusSFF D) :=
  ((continuous_torusPhaseSum D).norm.pow 2).div_const _

private theorem integrable_of_continuous {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : X → E} (hf : Continuous f) :
    Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem ofReal_norm_sq (w : ℂ) : ((‖w‖ : ℝ) : ℂ) ^ 2 = w * (starRingEnd ℂ) w := by
  rw [Complex.mul_conj]
  norm_cast
  rw [Complex.normSq_eq_norm_sq]

/-- **Haar moments of the normalized spectral form factor.**  Every moment is the sum of squared
multinomial coefficients divided by the dimension raised to the replica order. -/
theorem integral_torusSFF_pow (D m : ℕ) :
    ∫ z : UnitAddTorus (Fin D), torusSFF D z ^ m
        ∂(finiteTorusHaarProbabilityMeasure (Fin D) :
          Measure (UnitAddTorus (Fin D))) = sffMoment D m := by
  classical
  set ν : Measure (UnitAddTorus (Fin D)) :=
    (finiteTorusHaarProbabilityMeasure (Fin D) : Measure (UnitAddTorus (Fin D))) with hν
  have hprob : IsProbabilityMeasure ν := by
    rw [hν]
    exact (finiteTorusHaarProbabilityMeasure (Fin D)).prop
  have hpoint : ∀ z : UnitAddTorus (Fin D), ((torusSFF D z ^ m : ℝ) : ℂ) =
      ∑ p ∈ (Finset.univ : Finset (Fin D)).piAntidiag m,
        ∑ q ∈ (Finset.univ : Finset (Fin D)).piAntidiag m,
          ((Nat.multinomial Finset.univ p : ℂ) * (Nat.multinomial Finset.univ q : ℂ) /
            (D : ℂ) ^ m) *
            mFourier ((fun j => (p j : ℤ)) + fun j => -(q j : ℤ)) z := by
    intro z
    have hA : ((torusSFF D z : ℝ) : ℂ) =
        torusPhaseSum D z * (starRingEnd ℂ) (torusPhaseSum D z) / (D : ℂ) := by
      rw [torusSFF]
      push_cast
      rw [ofReal_norm_sq]
    rw [show ((torusSFF D z ^ m : ℝ) : ℂ) = ((torusSFF D z : ℝ) : ℂ) ^ m by push_cast; ring, hA,
      div_pow, mul_pow, ← map_pow, torusPhaseSum_pow, map_sum]
    rw [Finset.sum_mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul, Complex.conj_natCast, ← mFourier_neg]
    have hneg : (-(fun j => (q j : ℤ)) : Fin D → ℤ) = fun j => -(q j : ℤ) := rfl
    rw [hneg, mFourier_add]
    ring
  have hintUnit : ∀ (n : Fin D → ℤ) (c : ℂ), Integrable (fun z => c * mFourier n z) ν :=
    fun n c => (integrable_of_continuous ((mFourier n).continuous)).const_mul c
  have hinner : ∀ p : Fin D → ℕ, Integrable (fun z : UnitAddTorus (Fin D) =>
      ∑ q ∈ (Finset.univ : Finset (Fin D)).piAntidiag m,
        ((Nat.multinomial Finset.univ p : ℂ) * (Nat.multinomial Finset.univ q : ℂ) /
          (D : ℂ) ^ m) * mFourier ((fun j => (p j : ℤ)) + fun j => -(q j : ℤ)) z) ν := by
    intro p
    exact integrable_finsetSum _ fun q _ => hintUnit _ _
  have hcomplex : ∫ z : UnitAddTorus (Fin D), ((torusSFF D z ^ m : ℝ) : ℂ) ∂ν =
      ((sffMoment D m : ℝ) : ℂ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
      integral_finsetSum _ fun p _ => hinner p]
    rw [sffMoment, replicaPairCount]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [integral_finsetSum _ fun q _ => hintUnit _ _]
    rw [Finset.sum_eq_single p]
    · rw [integral_const_mul]
      have hzero : ((fun j => (p j : ℤ)) + fun j => -(p j : ℤ)) = (0 : Fin D → ℤ) := by
        funext j
        simp
      rw [hzero, finiteTorusHaarProbabilityMeasure_mFourier_integral, if_pos rfl, mul_one]
      ring
    · intro q _ hqp
      rw [integral_const_mul]
      have hne : ((fun j => (p j : ℤ)) + fun j => -(q j : ℤ)) ≠ (0 : Fin D → ℤ) := by
        intro hzero
        refine hqp ?_
        funext j
        have hj := congrFun hzero j
        simp only [Pi.add_apply, Pi.zero_apply] at hj
        omega
      rw [finiteTorusHaarProbabilityMeasure_mFourier_integral, if_neg hne, mul_zero]
    · intro hp'
      exact absurd hp hp'
  refine Complex.ofReal_inj.mp ?_
  calc ((∫ z : UnitAddTorus (Fin D), torusSFF D z ^ m ∂ν : ℝ) : ℂ)
      = ∫ z : UnitAddTorus (Fin D), ((torusSFF D z ^ m : ℝ) : ℂ) ∂ν :=
        (integral_ofReal (𝕜 := ℂ)).symm
    _ = ((sffMoment D m : ℝ) : ℂ) := hcomplex

end HaarMoments

section SFFLaw

/-- The Haar law of the normalized spectral form factor. -/
def sffLaw (D : ℕ) : ProbabilityMeasure ℝ :=
  ⟨Measure.map (torusSFF D)
      (finiteTorusHaarProbabilityMeasure (Fin D) : Measure (UnitAddTorus (Fin D))),
    Measure.isProbabilityMeasure_map (continuous_torusSFF D).measurable.aemeasurable⟩

theorem integral_sffLaw_pow (D m : ℕ) :
    ∫ x : ℝ, x ^ m ∂((sffLaw D : ProbabilityMeasure ℝ) : Measure ℝ) = sffMoment D m := by
  rw [show ((sffLaw D : ProbabilityMeasure ℝ) : Measure ℝ) =
      Measure.map (torusSFF D)
        (finiteTorusHaarProbabilityMeasure (Fin D) : Measure (UnitAddTorus (Fin D))) from rfl,
    integral_map (f := fun y : ℝ => y ^ m) (continuous_torusSFF D).measurable.aemeasurable
      ((measurable_id.pow_const m).aestronglyMeasurable)]
  exact integral_torusSFF_pow D m

theorem hasFactorialMomentBound_sffLaw (D : ℕ) :
    HasFactorialMomentBound ((sffLaw D : ProbabilityMeasure ℝ) : Measure ℝ) 1 := by
  intro n
  have hmap : ((sffLaw D : ProbabilityMeasure ℝ) : Measure ℝ) =
      Measure.map (torusSFF D)
        (finiteTorusHaarProbabilityMeasure (Fin D) : Measure (UnitAddTorus (Fin D))) := rfl
  rw [hmap, lintegral_map (f := fun y : ℝ => ENNReal.ofReal (|y| ^ n))
    (ENNReal.measurable_ofReal.comp (measurable_id.abs.pow_const n))
    (continuous_torusSFF D).measurable]
  have habs : ∀ z : UnitAddTorus (Fin D),
      ENNReal.ofReal (|torusSFF D z| ^ n) = ENNReal.ofReal (torusSFF D z ^ n) := by
    intro z
    rw [abs_of_nonneg (torusSFF_nonneg D z)]
  simp_rw [habs]
  have hint : Integrable (fun z : UnitAddTorus (Fin D) => torusSFF D z ^ n)
      ((finiteTorusHaarProbabilityMeasure (Fin D) : Measure (UnitAddTorus (Fin D)))) :=
    integrable_of_continuous ((continuous_torusSFF D).pow n)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun z => pow_nonneg (torusSFF_nonneg D z) n)]
  rw [integral_torusSFF_pow]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [one_pow, mul_one]
  exact sffMoment_le' D n

end SFFLaw

section ExponentialLaw

theorem exponentialPDF_one_eq (x : ℝ) :
    exponentialPDF 1 x = ENNReal.ofReal (Set.indicator (Set.Ici (0 : ℝ))
      (fun y : ℝ => Real.exp (-y)) x) := by
  rw [exponentialPDF_eq]
  congr 1
  by_cases hx : (0 : ℝ) ≤ x
  · rw [if_pos hx, Set.indicator_of_mem (Set.mem_Ici.mpr hx)]
    norm_num
  · rw [if_neg hx, Set.indicator_of_notMem (fun h => hx (Set.mem_Ici.mp h))]

theorem measurable_exponentialPDF_one : Measurable (exponentialPDF 1) := by
  have h : exponentialPDF 1 = fun x : ℝ => ENNReal.ofReal (Set.indicator (Set.Ici (0 : ℝ))
      (fun y : ℝ => Real.exp (-y)) x) := funext exponentialPDF_one_eq
  rw [h]
  refine ENNReal.measurable_ofReal.comp ?_
  exact (Real.measurable_exp.comp measurable_neg).indicator measurableSet_Ici

theorem exponentialPDF_one_lt_top (x : ℝ) : exponentialPDF 1 x < ⊤ := by
  rw [exponentialPDF_one_eq]
  exact ENNReal.ofReal_lt_top

theorem toReal_exponentialPDF_one (x : ℝ) :
    (exponentialPDF 1 x).toReal =
      Set.indicator (Set.Ici (0 : ℝ)) (fun y : ℝ => Real.exp (-y)) x := by
  rw [exponentialPDF_one_eq, ENNReal.toReal_ofReal]
  by_cases hx : (0 : ℝ) ≤ x
  · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hx)]
    exact (Real.exp_pos _).le
  · rw [Set.indicator_of_notMem (fun h => hx (Set.mem_Ici.mp h))]

theorem integrableOn_exp_neg_mul_pow (n : ℕ) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ n) (Set.Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (n : ℝ) + 1) (by positivity)
  refine (integrableOn_congr_fun ?_ measurableSet_Ioi).mp h
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  simp [show ((n : ℝ) + 1 - 1) = (n : ℝ) by ring, Real.rpow_natCast]

theorem integral_exp_neg_mul_pow (n : ℕ) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-x) * x ^ n = (Nat.factorial n : ℝ) := by
  have h := Real.Gamma_eq_integral (s := (n : ℝ) + 1) (by positivity)
  rw [Real.Gamma_nat_eq_factorial] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  simp [show ((n : ℝ) + 1 - 1) = (n : ℝ) by ring, Real.rpow_natCast]

/-- The unit-mean exponential law. -/
def unitExpLaw : ProbabilityMeasure ℝ :=
  ⟨expMeasure 1, isProbabilityMeasure_expMeasure one_pos⟩

theorem integral_unitExpLaw_pow (n : ℕ) :
    ∫ x : ℝ, x ^ n ∂((unitExpLaw : ProbabilityMeasure ℝ) : Measure ℝ) =
      (Nat.factorial n : ℝ) := by
  have hpdf : ((unitExpLaw : ProbabilityMeasure ℝ) : Measure ℝ) =
      (volume : Measure ℝ).withDensity (exponentialPDF 1) := rfl
  rw [hpdf, integral_withDensity_eq_integral_toReal_smul measurable_exponentialPDF_one
    (Filter.Eventually.of_forall exponentialPDF_one_lt_top)]
  have hval : ∀ x : ℝ, (exponentialPDF 1 x).toReal • x ^ n =
      Set.indicator (Set.Ici (0 : ℝ)) (fun y : ℝ => Real.exp (-y) * y ^ n) x := by
    intro x
    rw [toReal_exponentialPDF_one, smul_eq_mul]
    by_cases hx : (0 : ℝ) ≤ x
    · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hx), Set.indicator_of_mem (Set.mem_Ici.mpr hx)]
    · rw [Set.indicator_of_notMem (fun h => hx (Set.mem_Ici.mp h)),
        Set.indicator_of_notMem (fun h => hx (Set.mem_Ici.mp h)), zero_mul]
  simp_rw [hval]
  rw [integral_indicator measurableSet_Ici,
    ← Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))]
  exact integral_exp_neg_mul_pow n

theorem hasFactorialMomentBound_unitExpLaw :
    HasFactorialMomentBound ((unitExpLaw : ProbabilityMeasure ℝ) : Measure ℝ) 1 := by
  intro n
  have hpdf : ((unitExpLaw : ProbabilityMeasure ℝ) : Measure ℝ) =
      (volume : Measure ℝ).withDensity (exponentialPDF 1) := rfl
  rw [hpdf, lintegral_withDensity_eq_lintegral_mul _ measurable_exponentialPDF_one
    (g := fun y : ℝ => ENNReal.ofReal (|y| ^ n))
    (ENNReal.measurable_ofReal.comp (measurable_id.abs.pow_const n))]
  have hval : ∀ x : ℝ, (exponentialPDF 1 * fun y : ℝ => ENNReal.ofReal (|y| ^ n)) x =
      ENNReal.ofReal (Set.indicator (Set.Ici (0 : ℝ))
        (fun y : ℝ => Real.exp (-y) * y ^ n) x) := by
    intro x
    show exponentialPDF 1 x * ENNReal.ofReal (|x| ^ n) = _
    rw [exponentialPDF_one_eq]
    by_cases hx : (0 : ℝ) ≤ x
    · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hx), Set.indicator_of_mem (Set.mem_Ici.mpr hx),
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, abs_of_nonneg hx]
    · rw [Set.indicator_of_notMem (fun h => hx (Set.mem_Ici.mp h)),
        Set.indicator_of_notMem (fun h => hx (Set.mem_Ici.mp h))]
      simp
  simp_rw [hval]
  rw [← ofReal_integral_eq_lintegral_ofReal, integral_indicator measurableSet_Ici,
    ← Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ))), integral_exp_neg_mul_pow]
  · rw [one_pow, mul_one]
  · rw [integrable_indicator_iff measurableSet_Ici]
    exact (integrableOn_exp_neg_mul_pow n).congr_set_ae
      (Ioi_ae_eq_Ici (a := (0 : ℝ))).symm
  · refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : (0 : ℝ) ≤ x
    · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hx)]
      have hxn : (0 : ℝ) ≤ x ^ n := pow_nonneg hx n
      positivity
    · rw [Set.indicator_of_notMem (fun h => hx (Set.mem_Ici.mp h))]
      exact le_rfl

end ExponentialLaw

section ExponentialLimit

/-- **The spectral form factor converges to the unit-mean exponential law.**  The Haar laws of the
normalized spectral form factor converge weakly, as the dimension grows, to the unit-mean
exponential law. -/
theorem tendsto_sffLaw_unitExpLaw :
    Tendsto (fun D : ℕ => sffLaw D) atTop (𝓝 unitExpLaw) := by
  refine tendsto_of_tendsto_moments (M := 1) one_pos
    (fun D => hasFactorialMomentBound_sffLaw D) hasFactorialMomentBound_unitExpLaw ?_
  intro n
  have hleft : (fun D : ℕ => ∫ x : ℝ, x ^ n ∂((sffLaw D : ProbabilityMeasure ℝ) : Measure ℝ)) =
      fun D : ℕ => sffMoment D n := funext fun D => integral_sffLaw_pow D n
  rw [hleft, integral_unitExpLaw_pow n]
  exact tendsto_sffMoment n

end ExponentialLimit

end

end GaloisForLFunctions.HTGeometry
