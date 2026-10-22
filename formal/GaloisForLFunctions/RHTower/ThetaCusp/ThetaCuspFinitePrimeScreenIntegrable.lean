import GaloisForLFunctions.RHTower.HermiteTruncationTailAsymptotic
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimePositiveScreen

/-!
# Exponential integrability of finite-prime theta screens

The selected finite-prime source has arbitrary exponential moments on the positive ray.  Its
one-sided smooth screen has compactly supported reflection there; even reflection therefore
produces an everywhere-positive source with arbitrary two-sided exponential moments.
-/

open Filter Topology Set MeasureTheory

noncomputable section

namespace RHTower

theorem continuous_finitePrimeThetaCuspSource (N : ℕ) :
    Continuous (finitePrimeThetaCuspSource N) := by
  have hzero : finitePrimeThetaCuspSource N = finitePrimeThetaCuspDerivative 0 N := by
    simpa only [iteratedDeriv_zero] using
      iteratedDeriv_finitePrimeThetaCuspSource 0 N
  rw [hzero]
  have hder : ∀ x : ℝ, HasDerivAt (finitePrimeThetaCuspSource N)
      (finitePrimeThetaCuspDerivative 1 N x) x := by
    intro x
    rw [hzero]
    exact hasDerivAt_finitePrimeThetaCuspDerivative 0 N x
  exact continuous_iff_continuousAt.mpr fun x ↦ (hder x).continuousAt

theorem continuous_finitePrimeThetaCuspScreenCutoff (j : ℕ) :
    Continuous (finitePrimeThetaCuspScreenCutoff j) := by
  unfold finitePrimeThetaCuspScreenCutoff
  exact ccmSmoothHalflineCutoff_contDiff.continuous.comp
    (continuous_id.add continuous_const)

theorem continuous_finitePrimeThetaCuspRightScreen (j : ℕ) :
    Continuous (finitePrimeThetaCuspRightScreen j) := by
  unfold finitePrimeThetaCuspRightScreen
  exact (continuous_finitePrimeThetaCuspScreenCutoff j).mul
    (continuous_finitePrimeThetaCuspSource _)

theorem continuous_finitePrimeThetaCuspEvenScreen (j : ℕ) :
    Continuous (finitePrimeThetaCuspEvenScreen j) := by
  unfold finitePrimeThetaCuspEvenScreen
  exact ((continuous_finitePrimeThetaCuspRightScreen j).add
    ((continuous_finitePrimeThetaCuspRightScreen j).comp continuous_neg)).div_const 2

theorem finitePrimeThetaCuspRightScreen_neg_eq_zero_of_ge (j : ℕ) {x : ℝ}
    (hx : ((j + 1 : ℕ) : ℝ) ≤ x) :
    finitePrimeThetaCuspRightScreen j (-x) = 0 := by
  rw [finitePrimeThetaCuspRightScreen,
    finitePrimeThetaCuspScreenCutoff_eq_zero j (by linarith), zero_mul]

theorem integrableOn_exp_mul_finitePrimeThetaCuspSource_Ioi
    (N : ℕ) (A : ℝ) :
    IntegrableOn (fun x : ℝ ↦ Real.exp (A * x) * finitePrimeThetaCuspSource N x)
      (Ioi 0) := by
  obtain ⟨q : ℕ, hq⟩ := exists_nat_gt A
  have hq' : A < (q + 1 : ℕ) := lt_trans hq (by exact_mod_cast Nat.lt_succ_self q)
  have hbase := integrableOn_exp_mul_abs_finitePrimeThetaCuspDerivative 0 q N A hq'
  have hzero : finitePrimeThetaCuspSource N = finitePrimeThetaCuspDerivative 0 N := by
    simpa only [iteratedDeriv_zero] using
      iteratedDeriv_finitePrimeThetaCuspSource 0 N
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro x hx
  change Real.exp (A * x) * |finitePrimeThetaCuspDerivative 0 N x| =
    Real.exp (A * x) * finitePrimeThetaCuspSource N x
  rw [← congrFun hzero x,
    abs_of_pos (finitePrimeThetaCuspSource_pos_of_nonneg N hx.le)]

theorem integrableOn_exp_mul_reflectedRightScreen_Ioi
    (j : ℕ) (A : ℝ) :
    IntegrableOn (fun x : ℝ ↦
      Real.exp (A * x) * finitePrimeThetaCuspRightScreen j (-x)) (Ioi 0) := by
  let B : ℝ := ((j + 1 : ℕ) : ℝ)
  let f : ℝ → ℝ := fun x ↦
    Real.exp (A * x) * finitePrimeThetaCuspRightScreen j (-x)
  have hfcont : Continuous f := by
    dsimp [f]
    exact (by fun_prop : Continuous fun x : ℝ ↦ Real.exp (A * x)).mul
      ((continuous_finitePrimeThetaCuspRightScreen j).comp continuous_neg)
  have hcompact : IntegrableOn f (Ioc 0 B) :=
    hfcont.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hzero : IntegrableOn f (Ioi B) := by
    refine integrableOn_zero.congr_fun ?_ measurableSet_Ioi
    intro x hx
    dsimp [f, B]
    rw [finitePrimeThetaCuspRightScreen_neg_eq_zero_of_ge j hx.le, mul_zero]
  have hunion : IntegrableOn f (Ioc 0 B ∪ Ioi B) := hcompact.union hzero
  have hset : Ioc 0 B ∪ Ioi B = Ioi 0 := by
    ext x
    simp [B]
    constructor
    · intro h
      rcases h with ⟨hx, _⟩ | hx <;> linarith
    · intro hx
      by_cases hxb : x ≤ ((j + 1 : ℕ) : ℝ)
      · push_cast at hxb
        exact Or.inl ⟨hx, hxb⟩
      · push_cast at hxb
        exact Or.inr (lt_of_not_ge hxb)
  rwa [hset] at hunion

theorem integrableOn_exp_mul_finitePrimeThetaCuspEvenScreen_Ioi
    (j : ℕ) (A : ℝ) :
    IntegrableOn (fun x : ℝ ↦ Real.exp (A * x) * finitePrimeThetaCuspEvenScreen j x)
      (Ioi 0) := by
  have hright := integrableOn_exp_mul_finitePrimeThetaCuspSource_Ioi
    (finitePrimeThetaCuspPositiveScreenIndex j) A
  have href := integrableOn_exp_mul_reflectedRightScreen_Ioi j A
  have hsum : IntegrableOn (fun x : ℝ ↦
      Real.exp (A * x) * finitePrimeThetaCuspSource
          (finitePrimeThetaCuspPositiveScreenIndex j) x +
        Real.exp (A * x) * finitePrimeThetaCuspRightScreen j (-x)) (Ioi 0) :=
    Integrable.add hright href
  have hhalf : IntegrableOn (fun x : ℝ ↦ (1 / 2 : ℝ) *
      (Real.exp (A * x) * finitePrimeThetaCuspSource
          (finitePrimeThetaCuspPositiveScreenIndex j) x +
        Real.exp (A * x) * finitePrimeThetaCuspRightScreen j (-x))) (Ioi 0) :=
    Integrable.const_mul hsum (1 / 2 : ℝ)
  apply hhalf.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := hx
  have hxRight : finitePrimeThetaCuspRightScreen j x =
      finitePrimeThetaCuspSource (finitePrimeThetaCuspPositiveScreenIndex j) x := by
    rw [finitePrimeThetaCuspRightScreen,
      finitePrimeThetaCuspScreenCutoff_eq_one j (by
        have hj : (0 : ℝ) ≤ (j : ℕ) := by positivity
        linarith), one_mul]
  rw [finitePrimeThetaCuspEvenScreen, hxRight]
  ring

/-- Every absolute exponential weight of a screened even source is globally integrable. -/
theorem integrable_exp_abs_mul_finitePrimeThetaCuspEvenScreen
    (j : ℕ) (A : ℝ) :
    Integrable (fun x : ℝ ↦
      Real.exp (A * |x|) * finitePrimeThetaCuspEvenScreen j x) := by
  let f : ℝ → ℝ := fun x ↦
    Real.exp (A * |x|) * finitePrimeThetaCuspEvenScreen j x
  have hfEven : ∀ x, f (-x) = f x := by
    intro x
    simp only [f, abs_neg, finitePrimeThetaCuspEvenScreen_neg]
  have hfcont : Continuous f := by
    dsimp [f]
    exact (Real.continuous_exp.comp
      ((continuous_const.mul continuous_abs))).mul
        (continuous_finitePrimeThetaCuspEvenScreen j)
  have hpos : IntegrableOn f (Ioi 0) := by
    have h := integrableOn_exp_mul_finitePrimeThetaCuspEvenScreen_Ioi j A
    refine h.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx0 : 0 < x := hx
    simp only [f, abs_of_pos hx0]
  have hneg : IntegrableOn f (Iio 0) := by
    have hmp : MeasurePreserving (fun x : ℝ ↦ -x) volume volume :=
      Measure.measurePreserving_neg volume
    have hme : MeasurableEmbedding (fun x : ℝ ↦ -x) :=
      (Homeomorph.neg ℝ).measurableEmbedding
    have hiff := hmp.integrableOn_comp_preimage hme (f := f) (s := Ioi (0 : ℝ))
    have hpre : (fun x : ℝ ↦ -x) ⁻¹' Ioi 0 = Iio 0 := by ext x; simp
    rw [hpre] at hiff
    refine (hiff.mpr hpos).congr_fun ?_ measurableSet_Iio
    intro x hx
    exact hfEven x
  have hunion : IntegrableOn f (Iio 0 ∪ Ioi 0) := hneg.union hpos
  rw [Iio_union_Ioi] at hunion
  have hae : (Set.univ : Set ℝ) =ᵐ[volume] ({(0 : ℝ)}ᶜ : Set ℝ) :=
    (ae_eq_univ.mpr (by simp)).symm
  have huniv := hunion.congr_set_ae hae
  rwa [integrableOn_univ] at huniv

/-- Absolute values do not change the screened source, which is strictly positive. -/
theorem integrable_exp_abs_mul_abs_finitePrimeThetaCuspEvenScreen
    (j : ℕ) (A : ℝ) :
    Integrable (fun x : ℝ ↦
      Real.exp (A * |x|) * |finitePrimeThetaCuspEvenScreen j x|) := by
  refine (integrable_exp_abs_mul_finitePrimeThetaCuspEvenScreen j A).congr ?_
  filter_upwards with x
  rw [abs_of_pos (finitePrimeThetaCuspEvenScreen_pos j x)]

end RHTower
