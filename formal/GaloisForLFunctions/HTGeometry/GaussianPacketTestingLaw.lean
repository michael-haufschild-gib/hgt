import GaloisForLFunctions.HTGeometry.GaussianFormationRateRegion
import GaloisForLFunctions.HTGeometry.ConstitutiveFunctionalEquationPacketLift

/-!
# Equal-prior Bayes error of the Gaussian genesis packet

Section 4 of the formation-resource card `ULF-FRM-4`, plus the relative-entropy form of its
Theorem 2.1.

* `bayesRisk`, `bayesError`  the equal-prior optimal test error, with relabelling invariance and
  the exact neutrality of a common independent side channel (a Fubini argument, no
  Neyman--Pearson);
* `bayesRisk_gaussianReal`  the one-dimensional Gaussian testing law, proved from the Lebesgue
  densities: the optimal risk is `∫ min(φ₀, φ_c) = 2 Φ(-c/2)`;
* `bayesRisk_stdGaussian_shift`, `bayesError_stdGaussian_shift`  **`(CDS.20)`**: the optimal
  equal-prior Bayes error of the Gaussian genesis packet with signal `m` is exactly `Φ(-‖m‖/2)`,
  by reduction to one dimension along an orthonormal basis aligned with the signal;
* `bayesError_ge_of_rate`, `tendsto_stdGaussianCDF_half`  **Corollary 4.1, `(CDS.21)`**: vanishing
  capital density makes every formable one-copy observer asymptotically blind;
* `klDiv_comp_pi_le`, `jeffreys_comp_pi_le`  the relative-entropy and Jeffreys forms of the
  intensive formation law `(CDS.7)`.

Everything is unconditional.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Total error mass of the best equal-prior test of a binary experiment. -/
def bayesRisk {Ω : Type*} [MeasurableSpace Ω] (P₀ P₁ : Measure Ω) : ℝ≥0∞ :=
  ⨅ A : {s : Set Ω // MeasurableSet s}, (P₀ A.1 + P₁ A.1ᶜ)

/-- `(CDS.20)`  Equal-prior optimal Bayes error. -/
def bayesError {Ω : Type*} [MeasurableSpace Ω] (P₀ P₁ : Measure Ω) : ℝ :=
  (bayesRisk P₀ P₁).toReal / 2

theorem bayesRisk_le {Ω : Type*} [MeasurableSpace Ω] (P₀ P₁ : Measure Ω) {s : Set Ω}
    (hs : MeasurableSet s) : bayesRisk P₀ P₁ ≤ P₀ s + P₁ sᶜ :=
  iInf_le (fun A : {s : Set Ω // MeasurableSet s} => P₀ A.1 + P₁ A.1ᶜ) ⟨s, hs⟩

theorem le_bayesRisk {Ω : Type*} [MeasurableSpace Ω] (P₀ P₁ : Measure Ω) {c : ℝ≥0∞}
    (h : ∀ s : Set Ω, MeasurableSet s → c ≤ P₀ s + P₁ sᶜ) : c ≤ bayesRisk P₀ P₁ :=
  le_iInf fun A => h A.1 A.2

/-- Relabelling the observation space by a measurable equivalence does not change the risk. -/
theorem bayesRisk_map_measurableEquiv {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P₀ P₁ : Measure Ω) (e : Ω ≃ᵐ Ω') :
    bayesRisk (P₀.map e) (P₁.map e) = bayesRisk P₀ P₁ := by
  refine le_antisymm (le_bayesRisk _ _ fun s hs => ?_) (le_bayesRisk _ _ fun s hs => ?_)
  · have h1 : (P₀.map e) (e.symm ⁻¹' s) = P₀ s := by
      rw [Measure.map_apply e.measurable (e.symm.measurable hs)]
      congr 1
      ext x
      simp
    have h2 : (P₁.map e) (e.symm ⁻¹' s)ᶜ = P₁ sᶜ := by
      rw [Measure.map_apply e.measurable ((e.symm.measurable hs).compl)]
      congr 1
      ext x
      simp
    calc bayesRisk (P₀.map e) (P₁.map e)
        ≤ (P₀.map e) (e.symm ⁻¹' s) + (P₁.map e) (e.symm ⁻¹' s)ᶜ :=
          bayesRisk_le _ _ (e.symm.measurable hs)
      _ = P₀ s + P₁ sᶜ := by rw [h1, h2]
  · have h1 : P₀ (e ⁻¹' s) = (P₀.map e) s := (Measure.map_apply e.measurable hs).symm
    have h2 : P₁ (e ⁻¹' s)ᶜ = (P₁.map e) sᶜ := by
      rw [Measure.map_apply e.measurable hs.compl]
      congr 1
    calc bayesRisk P₀ P₁ ≤ P₀ (e ⁻¹' s) + P₁ (e ⁻¹' s)ᶜ :=
          bayesRisk_le _ _ (e.measurable hs)
      _ = (P₀.map e) s + (P₁.map e) sᶜ := by rw [h1, h2]

/-- **A common independent side channel is testing-neutral.** -/
theorem bayesRisk_prod_right {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (Q₀ Q₁ : Measure X) [SFinite Q₀] [SFinite Q₁] (R : Measure Y) [IsProbabilityMeasure R] :
    bayesRisk (Q₀.prod R) (Q₁.prod R) = bayesRisk Q₀ Q₁ := by
  refine le_antisymm (le_bayesRisk _ _ fun s hs => ?_) (le_bayesRisk _ _ fun s hs => ?_)
  · have hms : MeasurableSet (s ×ˢ (Set.univ : Set Y)) := hs.prod MeasurableSet.univ
    have hcompl : (s ×ˢ (Set.univ : Set Y))ᶜ = sᶜ ×ˢ (Set.univ : Set Y) := by
      ext p; simp
    calc bayesRisk (Q₀.prod R) (Q₁.prod R)
        ≤ (Q₀.prod R) (s ×ˢ Set.univ) + (Q₁.prod R) (s ×ˢ Set.univ)ᶜ := bayesRisk_le _ _ hms
      _ = Q₀ s + Q₁ sᶜ := by
          rw [hcompl, Measure.prod_prod, Measure.prod_prod, measure_univ, mul_one, mul_one]
  · have hmeas₀ : Measurable fun y => Q₀ ((fun x => (x, y)) ⁻¹' s) :=
      measurable_measure_prodMk_right hs
    have hmeas₁ : Measurable fun y => Q₁ (((fun x => (x, y)) ⁻¹' s)ᶜ) := by
      have : ∀ y, ((fun x => (x, y)) ⁻¹' s)ᶜ = (fun x => (x, y)) ⁻¹' sᶜ := fun y => rfl
      simp_rw [this]
      exact measurable_measure_prodMk_right hs.compl
    rw [Measure.prod_apply_symm hs, Measure.prod_apply_symm hs.compl,
      ← lintegral_add_left hmeas₀]
    have hconst : lintegral R (fun _ => bayesRisk Q₀ Q₁) = bayesRisk Q₀ Q₁ := by
      rw [lintegral_const, measure_univ, mul_one]
    calc bayesRisk Q₀ Q₁ = lintegral R (fun _ => bayesRisk Q₀ Q₁) := hconst.symm
      _ ≤ lintegral R (fun y => Q₀ ((fun x => (x, y)) ⁻¹' s)
            + Q₁ ((fun x => (x, y)) ⁻¹' sᶜ)) :=
          lintegral_mono fun y => bayesRisk_le _ _ (measurable_prodMk_right hs)

/-! ## The one-dimensional Gaussian testing law -/

/-- Standard Gaussian distribution function. -/
def stdGaussianCDF (u : ℝ) : ℝ := (gaussianReal 0 1).real (Set.Iic u)

theorem gaussianReal_Ioi (a : ℝ) :
    gaussianReal 0 1 (Set.Ioi a) = gaussianReal 0 1 (Set.Iio (-a)) := by
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa using gaussianReal_map_neg (μ := (0:ℝ)) (v := 1)
  have hpre : (fun x : ℝ => -x) ⁻¹' Set.Ioi a = Set.Iio (-a) := by
    ext x; simp [lt_neg]
  calc gaussianReal 0 1 (Set.Ioi a)
      = ((gaussianReal 0 1).map (fun x : ℝ => -x)) (Set.Ioi a) := by rw [hmap]
    _ = gaussianReal 0 1 ((fun x : ℝ => -x) ⁻¹' Set.Ioi a) :=
        Measure.map_apply measurable_neg measurableSet_Ioi
    _ = gaussianReal 0 1 (Set.Iio (-a)) := by rw [hpre]

theorem gaussianReal_singleton_null (m : ℝ) (a : ℝ) : gaussianReal m 1 {a} = 0 := by
  haveI := nullSingletonClass_gaussianReal (μ := m) (v := 1) one_ne_zero
  exact measure_singleton a

theorem gaussianReal_Iio_eq_Iic (m a : ℝ) :
    gaussianReal m 1 (Set.Iio a) = gaussianReal m 1 (Set.Iic a) := by
  haveI := nullSingletonClass_gaussianReal (μ := m) (v := 1) one_ne_zero
  exact measure_congr Iio_ae_eq_Iic

theorem gaussianReal_Ici_eq_Ioi (m a : ℝ) :
    gaussianReal m 1 (Set.Ici a) = gaussianReal m 1 (Set.Ioi a) := by
  haveI := nullSingletonClass_gaussianReal (μ := m) (v := 1) one_ne_zero
  exact (measure_congr Ioi_ae_eq_Ici).symm

theorem gaussianReal_shift_Iic (c a : ℝ) :
    gaussianReal c 1 (Set.Iic a) = gaussianReal 0 1 (Set.Iic (a - c)) := by
  have hmap : (gaussianReal 0 1).map (· + c) = gaussianReal c 1 := by
    simpa using gaussianReal_map_add_const (μ := (0:ℝ)) (v := 1) c
  have hpre : (fun x : ℝ => x + c) ⁻¹' Set.Iic a = Set.Iic (a - c) := by
    ext x; simp [le_sub_iff_add_le]
  rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Iic, hpre]

theorem gaussianPDF_le_iff {c : ℝ} (hc : 0 < c) (x : ℝ) :
    gaussianPDF 0 1 x ≤ gaussianPDF c 1 x ↔ c / 2 ≤ x := by
  rw [gaussianPDF, gaussianPDF, ENNReal.ofReal_le_ofReal_iff (gaussianPDFReal_nonneg _ _ _),
    gaussianPDFReal, gaussianPDFReal]
  have hpos : (0:ℝ) < (Real.sqrt (2 * Real.pi * ((1:ℝ≥0) : ℝ)))⁻¹ := by
    have : (0:ℝ) < 2 * Real.pi * ((1:ℝ≥0) : ℝ) := by
      simp only [NNReal.coe_one, mul_one]
      positivity
    exact inv_pos.mpr (Real.sqrt_pos.mpr this)
  rw [mul_le_mul_iff_of_pos_left hpos, Real.exp_le_exp]
  push_cast
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **The one-dimensional Gaussian testing law.**  The optimal equal-prior risk of the Gaussian
shift experiment of signal `c ≥ 0` is `2 Φ(-c/2)`. -/
theorem bayesRisk_gaussianReal {c : ℝ} (hc : 0 ≤ c) :
    bayesRisk (gaussianReal 0 1) (gaussianReal c 1)
      = 2 * gaussianReal 0 1 (Set.Iic (-(c / 2))) := by
  have hval : gaussianReal 0 1 (Set.Ici (c / 2)) + gaussianReal c 1 (Set.Iio (c / 2))
      = 2 * gaussianReal 0 1 (Set.Iic (-(c / 2))) := by
    rw [gaussianReal_Ici_eq_Ioi, gaussianReal_Ioi, gaussianReal_Iio_eq_Iic,
      gaussianReal_Iio_eq_Iic, gaussianReal_shift_Iic c (c / 2)]
    have hcc : c / 2 - c = -(c / 2) := by ring
    rw [hcc, two_mul]
  have hmin : ∀ x, min (gaussianPDF 0 1 x) (gaussianPDF c 1 x)
      = if c / 2 ≤ x then gaussianPDF 0 1 x else gaussianPDF c 1 x := by
    intro x
    rcases eq_or_lt_of_le hc with hc0 | hc0
    · rw [← hc0]
      simp
    · split_ifs with h
      · exact min_eq_left ((gaussianPDF_le_iff hc0 x).mpr h)
      · refine min_eq_right (le_of_not_ge fun hle => h ((gaussianPDF_le_iff hc0 x).mp hle))
  have hint : ∫⁻ x, min (gaussianPDF 0 1 x) (gaussianPDF c 1 x)
      = gaussianReal 0 1 (Set.Ici (c / 2)) + gaussianReal c 1 (Set.Iio (c / 2)) := by
    rw [← lintegral_add_compl _ measurableSet_Ici, Set.compl_Ici]
    have h1 : ∫⁻ x in Set.Ici (c / 2), min (gaussianPDF 0 1 x) (gaussianPDF c 1 x)
        = gaussianReal 0 1 (Set.Ici (c / 2)) := by
      rw [gaussianReal_apply 0 one_ne_zero]
      refine setLIntegral_congr_fun measurableSet_Ici fun x hx => ?_
      rw [hmin x, if_pos (show c / 2 ≤ x from hx)]
    have h2 : ∫⁻ x in Set.Iio (c / 2), min (gaussianPDF 0 1 x) (gaussianPDF c 1 x)
        = gaussianReal c 1 (Set.Iio (c / 2)) := by
      rw [gaussianReal_apply c one_ne_zero]
      refine setLIntegral_congr_fun measurableSet_Iio fun x hx => ?_
      rw [hmin x, if_neg (not_le.mpr (show x < c / 2 from hx))]
    rw [h1, h2]
  refine le_antisymm ?_ ?_
  · calc bayesRisk (gaussianReal 0 1) (gaussianReal c 1)
        ≤ gaussianReal 0 1 (Set.Ici (c / 2)) + gaussianReal c 1 (Set.Ici (c / 2))ᶜ :=
          bayesRisk_le _ _ measurableSet_Ici
      _ = 2 * gaussianReal 0 1 (Set.Iic (-(c / 2))) := by rw [Set.compl_Ici]; exact hval
  · rw [← hval, ← hint]
    refine le_bayesRisk _ _ fun s hs => ?_
    calc ∫⁻ x, min (gaussianPDF 0 1 x) (gaussianPDF c 1 x)
        = (∫⁻ x in s, min (gaussianPDF 0 1 x) (gaussianPDF c 1 x))
          + (∫⁻ x in sᶜ, min (gaussianPDF 0 1 x) (gaussianPDF c 1 x)) :=
          (lintegral_add_compl _ hs).symm
      _ ≤ (∫⁻ x in s, gaussianPDF 0 1 x) + (∫⁻ x in sᶜ, gaussianPDF c 1 x) :=
          add_le_add (lintegral_mono fun x => min_le_left _ _)
            (lintegral_mono fun x => min_le_right _ _)
      _ = gaussianReal 0 1 s + gaussianReal c 1 sᶜ := by
          rw [gaussianReal_apply 0 one_ne_zero, gaussianReal_apply c one_ne_zero]

/-- **`(CDS.20)` in one dimension.** -/
theorem bayesError_gaussianReal {c : ℝ} (hc : 0 ≤ c) :
    bayesError (gaussianReal 0 1) (gaussianReal c 1) = stdGaussianCDF (-(c / 2)) := by
  rw [bayesError, bayesRisk_gaussianReal hc, stdGaussianCDF, measureReal_def]
  rw [ENNReal.toReal_mul]
  simp

/-! ## The Gaussian genesis packet testing law -/

theorem bayesRisk_self {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    bayesRisk P P = 1 := by
  refine le_antisymm ?_ (le_bayesRisk _ _ fun s hs => ?_)
  · calc bayesRisk P P ≤ P Set.univ + P (Set.univ : Set Ω)ᶜ := bayesRisk_le _ _ MeasurableSet.univ
      _ = 1 := by simp
  · rw [le_iff_lt_or_eq]
    right
    have := measure_add_measure_compl (μ := P) hs
    rw [measure_univ] at this
    exact this.symm

section MultivariateTesting

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Coordinate isomorphism attached to an orthonormal basis. -/
def onbEquiv {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) : (Fin n → ℝ) ≃L[ℝ] E :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.trans
    b.repr.symm.toContinuousLinearEquiv

theorem onbEquiv_apply {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (x : Fin n → ℝ) :
    onbEquiv b x = ∑ i, x i • b i := by
  have h1 : onbEquiv b x = b.repr.symm (WithLp.toLp 2 x) := rfl
  rw [h1, ← b.sum_repr_symm]

theorem stdGaussian_eq_map_onb {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) :
    stdGaussian E = (Measure.pi fun _ : Fin n => gaussianReal 0 1).map (onbEquiv b) := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis b]
  congr 1
  funext x
  exact (onbEquiv_apply b x).symm

theorem stdGaussian_shift_eq_map_onb {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (m : E) :
    (stdGaussian E).map (fun x => x + m)
      = (Measure.pi fun i => gaussianReal ((b.repr m).ofLp i) 1).map (onbEquiv b) := by
  have hem : onbEquiv b (fun i => (b.repr m).ofLp i) = m := by
    have h1 : onbEquiv b (fun i => (b.repr m).ofLp i)
        = b.repr.symm (WithLp.toLp 2 fun i => (b.repr m).ofLp i) := rfl
    rw [h1]
    have h2 : (WithLp.toLp 2 fun i => (b.repr m).ofLp i : EuclideanSpace ℝ (Fin n)) = b.repr m :=
      rfl
    rw [h2, LinearIsometryEquiv.symm_apply_apply]
  have hpi : (Measure.pi fun _ : Fin n => gaussianReal 0 1).map
        (fun x => x + fun i => (b.repr m).ofLp i)
      = Measure.pi fun i => gaussianReal ((b.repr m).ofLp i) 1 := by
    have hfun : (fun (x : Fin n → ℝ) => x + fun i => (b.repr m).ofLp i)
        = fun (x : Fin n → ℝ) i => x i + (b.repr m).ofLp i := rfl
    rw [hfun, Measure.pi_map_pi (fun i => (measurable_add_const ((b.repr m).ofLp i)).aemeasurable)]
    congr 1
    funext i
    simpa using gaussianReal_map_add_const (μ := 0) (v := 1) ((b.repr m).ofLp i)
  rw [stdGaussian_eq_map_onb b, ← hpi, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [Function.comp_apply]
  rw [map_add, hem]

/-- **Theorem 4.1, `(CDS.20)`.**  The optimal equal-prior risk of the Gaussian genesis packet with
signal `m` is `2 Φ(-‖m‖/2)`. -/
theorem bayesRisk_stdGaussian_shift (m : E) :
    bayesRisk (stdGaussian E) ((stdGaussian E).map (fun x => x + m))
      = 2 * gaussianReal 0 1 (Set.Iic (-(‖m‖ / 2))) := by
  classical
  rcases eq_or_ne m 0 with rfl | hm
  · have hmap : (stdGaussian E).map (fun x => x + (0 : E)) = stdGaussian E := by simp
    rw [hmap, bayesRisk_self]
    have h1d := bayesRisk_gaussianReal (c := 0) le_rfl
    rw [bayesRisk_self] at h1d
    simpa using h1d
  · have hmpos : 0 < ‖m‖ := norm_pos_iff.mpr hm
    haveI : Nontrivial E := ⟨⟨m, 0, hm⟩⟩
    have hn : 0 < Module.finrank ℝ E := Module.finrank_pos
    obtain ⟨k, hk⟩ : ∃ k, Module.finrank ℝ E = k + 1 := ⟨Module.finrank ℝ E - 1, by omega⟩
    have hcard : Module.finrank ℝ E = Fintype.card (Fin (k + 1)) := by
      rw [hk, Fintype.card_fin]
    have hunit : ‖(‖m‖⁻¹ • m : E)‖ = 1 := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg m),
        inv_mul_cancel₀ hmpos.ne']
    have horth : Orthonormal ℝ (({0} : Set (Fin (k + 1))).restrict
        (fun _ : Fin (k + 1) => (‖m‖⁻¹ • m : E))) := by
      constructor
      · intro i
        simpa using hunit
      · intro i j hij
        exact absurd (Subtype.ext (by
          have hi := i.2
          have hj := j.2
          simp only [Set.mem_singleton_iff] at hi hj
          rw [hi, hj])) hij
    obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
    have hb0 : b 0 = ‖m‖⁻¹ • m := hb 0 rfl
    have hmb : m = ‖m‖ • b 0 := by
      rw [hb0, smul_smul, mul_inv_cancel₀ hmpos.ne', one_smul]
    set c : Fin (k + 1) → ℝ := fun i => (b.repr m).ofLp i with hc
    have hcval : ∀ i, c i = ⟪b i, m⟫ := by
      intro i
      show (b.repr m).ofLp i = ⟪b i, m⟫
      exact b.repr_apply_apply m i
    have hc0 : c 0 = ‖m‖ := by
      rw [hcval, hb0, real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp
    have hcne : ∀ i, i ≠ 0 → c i = 0 := by
      intro i hi
      rw [hcval, hmb, real_inner_smul_right, b.inner_eq_ite]
      simp [hi]
    -- transport to coordinates
    have hmeq : MeasurableEmbedding ((onbEquiv b : (Fin (k + 1) → ℝ) → E)) :=
      (onbEquiv b).toHomeomorph.measurableEmbedding
    have hequiv : (Fin (k + 1) → ℝ) ≃ᵐ E :=
      (onbEquiv b).toHomeomorph.toMeasurableEquiv
    have hcoe : ((onbEquiv b).toHomeomorph.toMeasurableEquiv : (Fin (k+1) → ℝ) → E)
        = (onbEquiv b : (Fin (k+1) → ℝ) → E) := rfl
    rw [stdGaussian_shift_eq_map_onb b m, stdGaussian_eq_map_onb b]
    rw [show ((onbEquiv b : (Fin (k+1) → ℝ) → E))
        = ((onbEquiv b).toHomeomorph.toMeasurableEquiv : (Fin (k+1) → ℝ) → E) from rfl]
    rw [bayesRisk_map_measurableEquiv]
    -- split the first coordinate
    have hsplit₀ := (measurePreserving_piFinSuccAbove
      (fun _ : Fin (k + 1) => gaussianReal (0 : ℝ) 1) 0).map_eq
    have hsplit₁ := (measurePreserving_piFinSuccAbove
      (fun i : Fin (k + 1) => gaussianReal (c i) 1) 0).map_eq
    rw [← bayesRisk_map_measurableEquiv _ _
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0), hsplit₀, hsplit₁]
    have hsecond : (Measure.pi fun j : Fin k => gaussianReal (c ((0 : Fin (k+1)).succAbove j)) 1)
        = Measure.pi fun _ : Fin k => gaussianReal (0 : ℝ) 1 := by
      congr 1
      funext j
      rw [hcne _ (Fin.succAbove_ne 0 j)]
    rw [hsecond, bayesRisk_prod_right, hc0]
    exact bayesRisk_gaussianReal hmpos.le

end MultivariateTesting

/-! ## Elementary properties of the Gaussian distribution function -/

theorem gaussianReal_Iic_zero : gaussianReal 0 1 (Set.Iic (0 : ℝ)) = 1 / 2 := by
  have hsym : gaussianReal 0 1 (Set.Ioi (0 : ℝ)) = gaussianReal 0 1 (Set.Iic (0 : ℝ)) := by
    rw [gaussianReal_Ioi, neg_zero, gaussianReal_Iio_eq_Iic]
  have hsum : gaussianReal 0 1 (Set.Iic (0 : ℝ)) + gaussianReal 0 1 (Set.Ioi (0 : ℝ)) = 1 := by
    have h := measure_add_measure_compl (μ := gaussianReal 0 1) (s := Set.Iic (0 : ℝ))
      measurableSet_Iic
    rw [Set.compl_Iic, measure_univ] at h
    exact h
  rw [hsym] at hsum
  have h2 : (2 : ℝ≥0∞) * gaussianReal 0 1 (Set.Iic (0 : ℝ)) = 1 := by
    rw [two_mul]; exact hsum
  have hne : gaussianReal 0 1 (Set.Iic (0 : ℝ)) ≠ ⊤ := measure_ne_top _ _
  rw [ENNReal.eq_div_iff (by norm_num) (by norm_num)]
  exact h2

theorem stdGaussianCDF_zero : stdGaussianCDF 0 = 1 / 2 := by
  rw [stdGaussianCDF, measureReal_def, gaussianReal_Iic_zero]
  simp

theorem gaussianPDF_le_one (x : ℝ) : gaussianPDF 0 1 x ≤ 1 := by
  rw [gaussianPDF, ← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [gaussianPDFReal]
  have hpi : (1:ℝ) ≤ Real.sqrt (2 * Real.pi * ((1:ℝ≥0) : ℝ)) := by
    rw [show ((1:ℝ≥0) : ℝ) = 1 from rfl, mul_one, show (1:ℝ) = Real.sqrt 1 by simp]
    refine Real.sqrt_le_sqrt ?_
    nlinarith [Real.pi_gt_three]
  have hinv : (Real.sqrt (2 * Real.pi * ((1:ℝ≥0) : ℝ)))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by linarith)]
    exact hpi
  have hexp : Real.exp (-(x - 0) ^ 2 / (2 * ((1:ℝ≥0) : ℝ))) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have : (0:ℝ) < 2 * ((1:ℝ≥0) : ℝ) := by norm_num
    apply div_nonpos_of_nonpos_of_nonneg _ this.le
    nlinarith [sq_nonneg (x - 0)]
  nlinarith [Real.exp_pos (-(x - 0) ^ 2 / (2 * ((1:ℝ≥0) : ℝ))),
    inv_nonneg.mpr (Real.sqrt_nonneg (2 * Real.pi * ((1:ℝ≥0) : ℝ)))]

theorem stdGaussianCDF_le_half {u : ℝ} (hu : u ≤ 0) : stdGaussianCDF u ≤ 1 / 2 := by
  rw [stdGaussianCDF, ← stdGaussianCDF_zero, stdGaussianCDF]
  exact measureReal_mono (Set.Iic_subset_Iic.mpr hu)

theorem half_sub_le_stdGaussianCDF {u : ℝ} (hu : u ≤ 0) : 1 / 2 + u ≤ stdGaussianCDF u := by
  have hdec : Set.Iic (0 : ℝ) = Set.Iic u ∪ Set.Ioc u 0 := (Set.Iic_union_Ioc_eq_Iic hu).symm
  have hbound : gaussianReal 0 1 (Set.Ioc u 0) ≤ ENNReal.ofReal (-u) := by
    rw [gaussianReal_apply 0 one_ne_zero]
    calc ∫⁻ x in Set.Ioc u 0, gaussianPDF 0 1 x
        ≤ ∫⁻ _ in Set.Ioc u 0, (1 : ℝ≥0∞) := lintegral_mono fun x => gaussianPDF_le_one x
      _ = volume (Set.Ioc u 0) := by simp
      _ = ENNReal.ofReal (-u) := by rw [Real.volume_Ioc]; congr 1; ring
  have hsum : gaussianReal 0 1 (Set.Iic (0:ℝ))
      ≤ gaussianReal 0 1 (Set.Iic u) + gaussianReal 0 1 (Set.Ioc u 0) := by
    rw [hdec]
    exact measure_union_le _ _
  have hfin₁ : gaussianReal 0 1 (Set.Iic u) ≠ ⊤ := measure_ne_top _ _
  have hreal : (1:ℝ) / 2 ≤ (gaussianReal 0 1 (Set.Iic u)).toReal + (-u) := by
    have h := hsum.trans (add_le_add le_rfl hbound)
    rw [gaussianReal_Iic_zero] at h
    have h' := ENNReal.toReal_mono (by finiteness) h
    rw [ENNReal.toReal_add hfin₁ (by finiteness), ENNReal.toReal_ofReal (by linarith)] at h'
    simpa using h'
  rw [stdGaussianCDF, measureReal_def]
  linarith

theorem stdGaussianCDF_mono {u v : ℝ} (h : u ≤ v) : stdGaussianCDF u ≤ stdGaussianCDF v :=
  measureReal_mono (Set.Iic_subset_Iic.mpr h)

section Conclusions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Theorem 4.1, `(CDS.20)`.**  The equal-prior optimal Bayes error of one Gaussian genesis
packet of signal `m` is exactly `Φ(-‖m‖/2) = Φ(-√Q/2)`. -/
theorem bayesError_stdGaussian_shift (m : E) :
    bayesError (stdGaussian E) ((stdGaussian E).map (fun x => x + m))
      = stdGaussianCDF (-(‖m‖ / 2)) := by
  rw [bayesError, bayesRisk_stdGaussian_shift, stdGaussianCDF, measureReal_def,
    ENNReal.toReal_mul]
  simp

/-- **`(CDS.20)` rate bound.**  Capital density caps the distinguishability of one formed copy. -/
theorem bayesError_ge_of_rate {b : ℝ} {d : ℕ} (hd : 0 < d) {m : E}
    (hm : (d : ℝ) * ‖m‖ ^ 2 ≤ b) :
    stdGaussianCDF (-(Real.sqrt (b / d) / 2))
      ≤ bayesError (stdGaussian E) ((stdGaussian E).map (fun x => x + m)) := by
  have hdpos : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hsq : ‖m‖ ^ 2 ≤ b / d := by
    rw [le_div_iff₀ hdpos, mul_comm]
    exact hm
  have hnorm : ‖m‖ ≤ Real.sqrt (b / d) := by
    rw [show ‖m‖ = Real.sqrt (‖m‖ ^ 2) from (Real.sqrt_sq (norm_nonneg m)).symm]
    exact Real.sqrt_le_sqrt hsq
  rw [bayesError_stdGaussian_shift]
  exact stdGaussianCDF_mono (by linarith)

end Conclusions

/-- **Corollary 4.1, `(CDS.21)`.**  Vanishing capital density makes every formable one-copy
observer asymptotically blind. -/
theorem tendsto_stdGaussianCDF_half {Q ρ : ℕ → ℝ} (hQ : ∀ n, 0 ≤ Q n) (hle : ∀ n, Q n ≤ ρ n)
    (hρ : Filter.Tendsto ρ Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => stdGaussianCDF (-(Real.sqrt (Q n) / 2))) Filter.atTop (nhds (1 / 2)) := by
  have hQ0 : Filter.Tendsto Q Filter.atTop (nhds 0) := squeeze_zero hQ hle hρ
  have hsqrt : Filter.Tendsto (fun n => Real.sqrt (Q n)) Filter.atTop (nhds 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hQ0
    simp only [Function.comp_def, Real.sqrt_zero] at h
    exact h
  have hlow : Filter.Tendsto (fun n => 1 / 2 + -(Real.sqrt (Q n) / 2)) Filter.atTop
      (nhds (1 / 2)) := by
    have : Filter.Tendsto (fun n => -(Real.sqrt (Q n) / 2)) Filter.atTop (nhds 0) := by
      simpa using (hsqrt.div_const 2).neg
    simpa using Filter.Tendsto.const_add (1 / 2 : ℝ) this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun n => half_sub_le_stdGaussianCDF ?_) (fun n => stdGaussianCDF_le_half ?_)
  · have := Real.sqrt_nonneg (Q n); linarith
  · have := Real.sqrt_nonneg (Q n); linarith

/-! ## The relative-entropy form of the intensive formation law -/

/-- **`(CDS.7)` for relative entropy.**  Every exact formation array pays the whole formed target
divergence out of source divergence. -/
theorem klDiv_comp_pi_le {S X : Type*} [MeasurableSpace S] [MeasurableSpace X]
    [StandardBorelSpace S] [Nonempty S] {d : ℕ}
    [StandardBorelSpace (Fin d → X)] [Nonempty X] [MeasurableEq (Fin d → X)]
    (r₀ r₁ : Measure S) [IsProbabilityMeasure r₀] [IsProbabilityMeasure r₁]
    (p₀ p₁ : Measure X) [IsProbabilityMeasure p₀] [IsProbabilityMeasure p₁]
    (κ : Kernel S (Fin d → X)) [IsMarkovKernel κ]
    (h₀ : κ ∘ₘ r₀ = Measure.pi fun _ : Fin d => p₀)
    (h₁ : κ ∘ₘ r₁ = Measure.pi fun _ : Fin d => p₁) :
    (d : ℝ≥0∞) * klDiv p₀ p₁ ≤ klDiv r₀ r₁ := by
  have h := klDiv_comp_le r₀ r₁ κ
  rw [h₀, h₁, klDiv_pi] at h
  simpa [Finset.sum_const, nsmul_eq_mul] using h

/-- **`(CDS.7)` for Jeffreys work.** -/
theorem jeffreys_comp_pi_le {S X : Type*} [MeasurableSpace S] [MeasurableSpace X]
    [StandardBorelSpace S] [Nonempty S] {d : ℕ}
    [StandardBorelSpace (Fin d → X)] [Nonempty X] [MeasurableEq (Fin d → X)]
    (r₀ r₁ : Measure S) [IsProbabilityMeasure r₀] [IsProbabilityMeasure r₁]
    (p₀ p₁ : Measure X) [IsProbabilityMeasure p₀] [IsProbabilityMeasure p₁]
    (κ : Kernel S (Fin d → X)) [IsMarkovKernel κ]
    (h₀ : κ ∘ₘ r₀ = Measure.pi fun _ : Fin d => p₀)
    (h₁ : κ ∘ₘ r₁ = Measure.pi fun _ : Fin d => p₁) :
    (d : ℝ≥0∞) * formationJeffreys p₀ p₁ ≤ formationJeffreys r₀ r₁ := by
  rw [formationJeffreys, formationJeffreys, mul_add]
  exact add_le_add (klDiv_comp_pi_le r₀ r₁ p₀ p₁ κ h₀ h₁)
    (klDiv_comp_pi_le r₁ r₀ p₁ p₀ κ h₁ h₀)

end

end GaloisForLFunctions.HTGeometry
