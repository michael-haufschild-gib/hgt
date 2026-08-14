import GaloisForLFunctions.HTGeometry.ConstitutiveTimeReversalLikelihoodCocycle
import GaloisForLFunctions.HTGeometry.ShiftLatticeThetaSeries

/-!
# Cofinal renewal information geometry

This file supplies the measure-theoretic information laws used by the cofinal-renewal cards.  The
data-processing theorem works on arbitrary measurable spaces: its proof identifies the pushed
Radon--Nikodym derivative with a conditional expectation and applies conditional Jensen to
`klFun`.  No disintegration or standard-Borel hypothesis is used.  Exponential tilting then gives
the entropy--exponential-moment inequality.  The final section records the exact horizontal /
vertical chain rule for formed packets and its zero-cost and minimum-action classifications.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Real InformationTheory Set ProbabilityTheory
open scoped ENNReal Topology

/-! ## Arbitrary-space information contraction -/

section ArbitraryDataProcessing

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Relative entropy contracts under every measurable observation, on arbitrary measurable
spaces.  This is the unrestricted data-processing law needed before any disintegration is chosen. -/
theorem klDiv_map_le_arbitrary
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (g : X → Y) (hg : Measurable g) :
    klDiv (μ.map g) (ν.map g) ≤ klDiv μ ν := by
  by_cases htop : klDiv μ ν = ⊤
  · rw [htop]
    exact le_top
  obtain ⟨hac, hllr⟩ := klDiv_ne_top_iff.mp htop
  haveI : IsProbabilityMeasure (μ.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  haveI : IsProbabilityMeasure (ν.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  have hmapac : μ.map g ≪ ν.map g := hac.map hg
  let r : X → ℝ := fun x => (μ.rnDeriv ν x).toReal
  have hr_nonneg : 0 ≤ᵐ[ν] r := by
    filter_upwards with x
    exact ENNReal.toReal_nonneg
  have hr_int : Integrable r ν := Measure.integrable_toReal_rnDeriv
  have hkl_int : Integrable (fun x => klFun (r x)) ν :=
    (integrable_klFun_rnDeriv_iff hac).2 hllr
  have hkl_nonneg : 0 ≤ᵐ[ν] fun x => klFun (r x) := by
    filter_upwards [hr_nonneg] with x hx
    exact klFun_nonneg hx
  have hr_cond_nonneg :
      0 ≤ᵐ[ν] ν[r | MeasurableSpace.comap g (inferInstance : MeasurableSpace Y)] :=
    condExp_nonneg hr_nonneg
  have hkl_cond_nonneg :
      0 ≤ᵐ[ν] ν[(fun x => klFun (r x)) |
        MeasurableSpace.comap g (inferInstance : MeasurableSpace Y)] :=
    condExp_nonneg hkl_nonneg
  have hjensen :
      (fun x => klFun (ν[r |
        MeasurableSpace.comap g (inferInstance : MeasurableSpace Y)] x)) ≤ᵐ[ν]
        ν[(fun x => klFun (r x)) |
          MeasurableSpace.comap g (inferInstance : MeasurableSpace Y)] := by
    have h := convexOn_klFun.map_condExp_le
      (s := Ici (0 : ℝ))
      (m := MeasurableSpace.comap g (inferInstance : MeasurableSpace Y)) (μ := ν) (f := r)
      hg.comap_le
      (continuous_klFun.lowerSemicontinuous.lowerSemicontinuousOn _)
      hr_nonneg isClosed_Ici hr_int hkl_int
    simpa only [Function.comp_def] using h
  have hcond_int :
      Integrable (ν[(fun x => klFun (r x)) |
        MeasurableSpace.comap g (inferInstance : MeasurableSpace Y)]) ν := integrable_condExp
  have hjensen_int :
      Integrable (fun x => klFun (ν[r |
        MeasurableSpace.comap g (inferInstance : MeasurableSpace Y)] x)) ν := by
    refine hcond_int.mono' (by fun_prop) ?_
    filter_upwards [hjensen, hr_cond_nonneg, hkl_cond_nonneg] with x hx hrx hkx
    rw [Real.norm_eq_abs, abs_of_nonneg (klFun_nonneg hrx)]
    exact hx
  have hmaprn := toReal_rnDeriv_map hac hg
  have hcomp_int :
      Integrable
        (fun x => klFun (((μ.map g).rnDeriv (ν.map g) (g x)).toReal)) ν := by
    refine hjensen_int.congr ?_
    filter_upwards [hmaprn] with x hx
    rw [hx]
  have hmapkl_int :
      Integrable (fun y => klFun (((μ.map g).rnDeriv (ν.map g) y).toReal)) (ν.map g) := by
    have hmeas :
        AEStronglyMeasurable
          (fun y => klFun (((μ.map g).rnDeriv (ν.map g) y).toReal)) (ν.map g) :=
      (measurable_klFun.comp (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable
    apply (integrable_map_measure hmeas hg.aemeasurable).2
    simpa only [Function.comp_def] using hcomp_int
  have hmapllr : Integrable (llr (μ.map g) (ν.map g)) (μ.map g) :=
    (integrable_klFun_rnDeriv_iff hmapac).1 hmapkl_int
  have hmaptop : klDiv (μ.map g) (ν.map g) ≠ ⊤ := klDiv_ne_top hmapac hmapllr
  apply (ENNReal.toReal_le_toReal hmaptop htop).mp
  rw [toReal_klDiv_eq_integral_klFun hmapac, toReal_klDiv_eq_integral_klFun hac]
  calc
    (∫ y, klFun (((μ.map g).rnDeriv (ν.map g) y).toReal) ∂(ν.map g)) =
        ∫ x, klFun (ν[r |
          MeasurableSpace.comap g (inferInstance : MeasurableSpace Y)] x) ∂ν := by
      rw [integral_map hg.aemeasurable hmapkl_int.aestronglyMeasurable]
      apply integral_congr_ae
      filter_upwards [hmaprn] with x hx
      rw [hx]
    _ ≤ ∫ x, ν[(fun z => klFun (r z)) |
      MeasurableSpace.comap g (inferInstance : MeasurableSpace Y)] x ∂ν :=
      integral_mono_ae hjensen_int hcond_int hjensen
    _ = ∫ x, klFun (r x) ∂ν := integral_condExp hg.comap_le

end ArbitraryDataProcessing

/-! ## Entropy--exponential-moment conservation -/

section EntropyMoment

variable {X : Type*} [MeasurableSpace X]

/-- The entropy--exponential-moment inequality.  The finiteness premise on `klDiv` unfolds to the
paper assumptions of absolute continuity and finite renewal action. -/
theorem integral_le_klDiv_add_log_integral_exp
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X → ℝ)
    (hfν : Integrable f ν)
    (hexp : Integrable (fun x => Real.exp (f x)) μ)
    (hfin : klDiv ν μ ≠ ⊤) :
    (∫ x, f x ∂ν) ≤ (klDiv ν μ).toReal + Real.log (∫ x, Real.exp (f x) ∂μ) := by
  obtain ⟨hac, hllr⟩ := klDiv_ne_top_iff.mp hfin
  haveI : IsProbabilityMeasure (μ.tilted f) := isProbabilityMeasure_tilted hexp
  have hactilt : ν ≪ μ.tilted f := hac.trans (absolutelyContinuous_tilted hexp)
  have hinttilt : Integrable (llr ν (μ.tilted f)) ν :=
    integrable_llr_tilted_right hac hfν hllr hexp
  have hnonneg : 0 ≤ ∫ x, llr ν (μ.tilted f) x ∂ν := by
    simpa using integral_llr_add_sub_measure_univ_nonneg hactilt hinttilt
  rw [integral_llr_tilted_right hac hfν hexp hllr] at hnonneg
  have hkl : (klDiv ν μ).toReal = ∫ x, llr ν μ x ∂ν :=
    toReal_klDiv_of_measure_eq hac (by simp)
  rw [hkl]
  linarith

/-- Finite relative entropy and a finite exponential moment force integrability of every measurable
nonnegative formation gauge.  This discharges, rather than assumes, finiteness of renewed work. -/
theorem integrable_of_klDiv_ne_top_of_integrable_exp
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hexp : Integrable (fun x => Real.exp (f x)) μ)
    (hfin : klDiv ν μ ≠ ⊤) : Integrable f ν := by
  let trunc : ℕ → X → ℝ := fun n x => min (f x) n
  have htrunc_meas (n : ℕ) : Measurable (trunc n) := hf.min measurable_const
  have htrunc_nonneg (n : ℕ) : ∀ x, 0 ≤ trunc n x := by
    intro x
    exact le_min (hf0 x) (Nat.cast_nonneg n)
  have htrunc_int_ν (n : ℕ) : Integrable (trunc n) ν := by
    refine ⟨(htrunc_meas n).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := (n : ℝ)) ?_⟩
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (htrunc_nonneg n x)]
    exact min_le_right _ _
  have hexp_trunc (n : ℕ) : Integrable (fun x => Real.exp (trunc n x)) μ := by
    refine hexp.mono (by fun_prop) ?_
    filter_upwards with x
    simp only [Real.norm_eq_abs, Real.abs_exp]
    exact Real.exp_le_exp.mpr (min_le_left _ _)
  let B : ℝ := (klDiv ν μ).toReal + Real.log (∫ x, Real.exp (f x) ∂μ)
  have htrunc_bound (n : ℕ) : (∫ x, trunc n x ∂ν) ≤ B := by
    have h := integral_le_klDiv_add_log_integral_exp μ ν (trunc n)
      (htrunc_int_ν n) (hexp_trunc n) hfin
    have hZle : (∫ x, Real.exp (trunc n x) ∂μ) ≤ ∫ x, Real.exp (f x) ∂μ := by
      apply integral_mono (hexp_trunc n) hexp
      intro x
      exact Real.exp_le_exp.mpr (min_le_left _ _)
    have hlogle := Real.log_le_log (integral_exp_pos (hexp_trunc n)) hZle
    exact h.trans (by simpa [B] using add_le_add_left hlogle (klDiv ν μ).toReal)
  have hlintegral_bound (n : ℕ) :
      (∫⁻ x, ENNReal.ofReal (trunc n x) ∂ν) ≤ ENNReal.ofReal B := by
    rw [← ofReal_integral_eq_lintegral_ofReal (htrunc_int_ν n)
      (ae_of_all _ (htrunc_nonneg n))]
    exact ENNReal.ofReal_le_ofReal (htrunc_bound n)
  have htrunc_tendsto (x : X) : Filter.Tendsto (fun n => trunc n x) Filter.atTop (𝓝 (f x)) := by
    obtain ⟨N, hN⟩ := exists_nat_ge (f x)
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    dsimp [trunc]
    rw [min_eq_left]
    exact hN.trans (by exact_mod_cast hn)
  have hofReal_tendsto (x : X) :
      Filter.Tendsto (fun n => ENNReal.ofReal (trunc n x)) Filter.atTop
        (𝓝 (ENNReal.ofReal (f x))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp (htrunc_tendsto x)
  have hfatou :
      (∫⁻ x, ENNReal.ofReal (f x) ∂ν) ≤
        Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (trunc n x) ∂ν) Filter.atTop := by
    calc
      (∫⁻ x, ENNReal.ofReal (f x) ∂ν) =
          ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (trunc n x)) Filter.atTop ∂ν := by
        apply lintegral_congr
        intro x
        rw [(hofReal_tendsto x).liminf_eq]
      _ ≤ _ := lintegral_liminf_le fun n => (htrunc_meas n).ennreal_ofReal
  have hliminf_bound :
      Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (trunc n x) ∂ν) Filter.atTop ≤
        ENNReal.ofReal B :=
    Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hlintegral_bound)
  have hltop : (∫⁻ x, ENNReal.ofReal (f x) ∂ν) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hfatou.trans hliminf_bound)
  exact (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable
    (ae_of_all _ hf0)).mp hltop

/-- Entropy controls a nonnegative formation gauge under exactly the paper assumptions: gauge
integrability under the renewed law is a conclusion of the theorem. -/
theorem integral_le_klDiv_add_log_integral_exp_of_nonneg
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hexp : Integrable (fun x => Real.exp (f x)) μ)
    (hfin : klDiv ν μ ≠ ⊤) :
    Integrable f ν ∧
      (∫ x, f x ∂ν) ≤ (klDiv ν μ).toReal + Real.log (∫ x, Real.exp (f x) ∂μ) := by
  have hfi := integrable_of_klDiv_ne_top_of_integrable_exp μ ν f hf hf0 hexp hfin
  exact ⟨hfi, integral_le_klDiv_add_log_integral_exp μ ν f hfi hexp hfin⟩

end EntropyMoment

/-! ## Disjoint aperture gauges -/

section ApertureGauge

variable {X : Type*}

/-- Formation gauge which assigns weight `phi n` on aperture `A n` and zero outside all
apertures.  Pairwise disjointness makes every pointwise series finitely supported. -/
noncomputable def apertureGauge (A : ℕ → Set X) (phi : ℕ → ℝ) (x : X) : ℝ :=
  ∑' n, (A n).indicator (fun _ => phi n) x

theorem apertureTerm_hasFiniteSupport
    (A : ℕ → Set X) (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (phi : ℕ → ℝ) (x : X) :
    (fun n => (A n).indicator (fun _ => phi n) x).HasFiniteSupport := by
  by_cases hx : ∃ n, x ∈ A n
  · obtain ⟨n, hn⟩ := hx
    refine (Set.finite_singleton n).subset ?_
    intro m hm
    simp only [Function.mem_support] at hm
    by_contra hmn
    have hAm : x ∈ A m := by
      by_contra hAm
      simp [hAm] at hm
    exact Set.disjoint_left.1 (hdisj hmn) hAm hn
  · simp only [not_exists] at hx
    simpa [hx] using
      (Function.hasFiniteSupport_zero : (fun _ : ℕ => (0 : ℝ)).HasFiniteSupport)

theorem summable_apertureTerm
    (A : ℕ → Set X) (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (phi : ℕ → ℝ) (x : X) :
    Summable (fun n => (A n).indicator (fun _ => phi n) x) :=
  summable_of_hasFiniteSupport (apertureTerm_hasFiniteSupport A hdisj phi x)

theorem apertureGauge_apply_mem
    (A : ℕ → Set X) (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (phi : ℕ → ℝ) (n : ℕ) {x : X} (hx : x ∈ A n) :
    apertureGauge A phi x = phi n := by
  rw [apertureGauge, tsum_eq_single n]
  · simp [hx]
  · intro m hmn
    have hnot : x ∉ A m := fun hm => Set.disjoint_left.1 (hdisj hmn) hm hx
    simp [hnot]

theorem apertureGauge_apply_not_mem
    (A : ℕ → Set X) (phi : ℕ → ℝ) {x : X} (hx : x ∉ ⋃ n, A n) :
    apertureGauge A phi x = 0 := by
  rw [apertureGauge]
  simp only [mem_iUnion, not_exists] at hx
  simp [hx]

theorem apertureGauge_nonneg
    (A : ℕ → Set X) (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (phi : ℕ → ℝ) (hphi : ∀ n, 0 ≤ phi n) (x : X) :
    0 ≤ apertureGauge A phi x := by
  by_cases hx : ∃ n, x ∈ A n
  · obtain ⟨n, hn⟩ := hx
    rw [apertureGauge_apply_mem A hdisj phi n hn]
    exact hphi n
  · rw [not_exists] at hx
    have hout : x ∉ ⋃ n, A n := by simpa only [mem_iUnion, not_exists]
    rw [apertureGauge_apply_not_mem A phi hout]

theorem exp_apertureGauge_eq
    (A : ℕ → Set X) (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (phi : ℕ → ℝ) (lambda : ℝ) (x : X) :
    Real.exp (lambda * apertureGauge A phi x) =
      1 + apertureGauge A (fun n => Real.exp (lambda * phi n) - 1) x := by
  by_cases hx : ∃ n, x ∈ A n
  · obtain ⟨n, hn⟩ := hx
    rw [apertureGauge_apply_mem A hdisj phi n hn,
      apertureGauge_apply_mem A hdisj (fun n => Real.exp (lambda * phi n) - 1) n hn]
    ring
  · rw [not_exists] at hx
    have hout : x ∉ ⋃ n, A n := by simpa only [mem_iUnion, not_exists]
    rw [apertureGauge_apply_not_mem A phi hout,
      apertureGauge_apply_not_mem A (fun n => Real.exp (lambda * phi n) - 1) hout]
    simp

section Measurable

variable [MeasurableSpace X]

theorem measurable_apertureGauge
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n)) (phi : ℕ → ℝ) :
    Measurable (apertureGauge A phi) := by
  exact Measurable.tsum (fun n => measurable_const.indicator (hA n))

/-- The expectation of a disjoint-aperture gauge is the exact occupation-moment series. -/
theorem integral_apertureGauge
    (mu : Measure X) (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j)) (phi : ℕ → ℝ)
    (hint : Integrable (apertureGauge A phi) mu) :
    (∫ x, apertureGauge A phi x ∂mu) = ∑' n, phi n * mu.real (A n) := by
  let U : Set X := ⋃ n, A n
  have hU : MeasurableSet U := MeasurableSet.iUnion hA
  calc
    (∫ x, apertureGauge A phi x ∂mu) =
        ∫ x, U.indicator (apertureGauge A phi) x ∂mu := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ U
      · simp [hx]
      · simp [hx, apertureGauge_apply_not_mem A phi hx]
    _ = ∫ x in U, apertureGauge A phi x ∂mu := integral_indicator hU
    _ = ∑' n, ∫ x in A n, apertureGauge A phi x ∂mu :=
      integral_iUnion hA hdisj hint.integrableOn
    _ = ∑' n, phi n * mu.real (A n) := by
      apply tsum_congr
      intro n
      calc
        (∫ x in A n, apertureGauge A phi x ∂mu) = ∫ _x in A n, phi n ∂mu := by
          apply setIntegral_congr_fun (hA n)
          intro x hx
          exact apertureGauge_apply_mem A hdisj phi n hx
        _ = phi n * mu.real (A n) := by
          rw [setIntegral_const]
          simp [mul_comm]

theorem hasSum_apertureGauge_integral
    (mu : Measure X) (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j)) (phi : ℕ → ℝ)
    (hint : Integrable (apertureGauge A phi) mu) :
    HasSum (fun n => phi n * mu.real (A n)) (∫ x, apertureGauge A phi x ∂mu) := by
  let U : Set X := ⋃ n, A n
  have hU : MeasurableSet U := MeasurableSet.iUnion hA
  have hwhole : (∫ x in U, apertureGauge A phi x ∂mu) =
      ∫ x, apertureGauge A phi x ∂mu := by
    rw [← integral_indicator hU]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ U
    · simp [hx]
    · simp [hx, apertureGauge_apply_not_mem A phi hx]
  have hsum := hasSum_integral_iUnion hA hdisj hint.integrableOn
  rw [hwhole] at hsum
  refine hsum.congr_fun ?_
  intro n
  calc
    phi n * mu.real (A n) = ∫ _x in A n, phi n ∂mu := by
      rw [setIntegral_const]
      simp [mul_comm]
    _ = ∫ x in A n, apertureGauge A phi x ∂mu := by
      symm
      apply setIntegral_congr_fun (hA n)
      intro x hx
      exact apertureGauge_apply_mem A hdisj phi n hx

theorem lintegral_apertureGauge
    (mu : Measure X) (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j)) (phi : ℕ → ℝ) :
    (∫⁻ x, ENNReal.ofReal (apertureGauge A phi x) ∂mu) =
      ∑' n, ENNReal.ofReal (phi n) * mu (A n) := by
  let U : Set X := ⋃ n, A n
  have hU : MeasurableSet U := MeasurableSet.iUnion hA
  calc
    (∫⁻ x, ENNReal.ofReal (apertureGauge A phi x) ∂mu) =
        ∫⁻ x, U.indicator (fun x => ENNReal.ofReal (apertureGauge A phi x)) x ∂mu := by
      apply lintegral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ U
      · simp [hx]
      · simp [hx, apertureGauge_apply_not_mem A phi hx]
    _ = ∫⁻ x in U, ENNReal.ofReal (apertureGauge A phi x) ∂mu :=
      lintegral_indicator hU _
    _ = ∑' n, ∫⁻ x in A n, ENNReal.ofReal (apertureGauge A phi x) ∂mu :=
      lintegral_iUnion hA hdisj _
    _ = ∑' n, ENNReal.ofReal (phi n) * mu (A n) := by
      apply tsum_congr
      intro n
      calc
        (∫⁻ x in A n, ENNReal.ofReal (apertureGauge A phi x) ∂mu) =
            ∫⁻ _x in A n, ENNReal.ofReal (phi n) ∂mu := by
          apply setLIntegral_congr_fun (hA n)
          intro x hx
          change ENNReal.ofReal (apertureGauge A phi x) = ENNReal.ofReal (phi n)
          rw [apertureGauge_apply_mem A hdisj phi n hx]
        _ = ENNReal.ofReal (phi n) * mu (A n) := setLIntegral_const (A n) _

/-- For nonnegative weights, gauge integrability is exactly summability of the aperture occupation
moment. -/
theorem integrable_apertureGauge_iff_summable
    (mu : Measure X) [IsFiniteMeasure mu]
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j)) (phi : ℕ → ℝ)
    (hphi : ∀ n, 0 ≤ phi n) :
    Integrable (apertureGauge A phi) mu ↔
      Summable (fun n => phi n * mu.real (A n)) := by
  have hmeas := measurable_apertureGauge A hA phi
  have hnonneg := apertureGauge_nonneg A hdisj phi hphi
  constructor
  · intro hint
    exact (hasSum_apertureGauge_integral mu A hA hdisj phi hint).summable
  · intro hsum
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have hnorm : (fun x => ENNReal.ofReal ‖apertureGauge A phi x‖) =
        fun x => ENNReal.ofReal (apertureGauge A phi x) := by
      funext x
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]
    rw [hnorm, lintegral_apertureGauge mu A hA hdisj phi]
    have hrewrite : (fun n => ENNReal.ofReal (phi n) * mu (A n)) =
        fun n => ENNReal.ofReal (phi n * mu.real (A n)) := by
      funext n
      rw [ENNReal.ofReal_mul (hphi n), ofReal_measureReal]
    rw [hrewrite]
    exact hsum.tsum_ofReal_lt_top

theorem integrable_exp_apertureGauge_of_summable
    (mu : Measure X) [IsFiniteMeasure mu]
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (phi : ℕ → ℝ) (hphi : ∀ n, 0 ≤ phi n)
    (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (hsum : Summable (fun n => Real.exp (lambda * phi n) * mu.real (A n))) :
    Integrable (fun x => Real.exp (lambda * apertureGauge A phi x)) mu := by
  let psi : ℕ → ℝ := fun n => Real.exp (lambda * phi n) - 1
  have hpsi : ∀ n, 0 ≤ psi n := fun n => by
    dsimp [psi]
    exact sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hlambda (hphi n)))
  have hmeasure : ∀ n, 0 ≤ mu.real (A n) := fun n => measureReal_nonneg
  have hsumPsi : Summable (fun n => psi n * mu.real (A n)) := by
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (hpsi n) (hmeasure n))
      (fun n => ?_) hsum
    exact mul_le_mul_of_nonneg_right
      (by dsimp [psi]; linarith [Real.exp_pos (lambda * phi n)]) (hmeasure n)
  have hintPsi : Integrable (apertureGauge A psi) mu :=
    (integrable_apertureGauge_iff_summable mu A hA hdisj psi hpsi).2 hsumPsi
  have hone : Integrable (fun _ : X => (1 : ℝ)) mu := integrable_const _
  have hint : Integrable (fun x => 1 + apertureGauge A psi x) mu := hone.add hintPsi
  refine hint.congr ?_
  filter_upwards with x
  exact (exp_apertureGauge_eq A hdisj phi lambda x).symm

/-- Exact partition function of a disjoint-aperture gauge, including the outside atom. -/
theorem integral_exp_apertureGauge
    (mu : Measure X) [IsFiniteMeasure mu]
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (phi : ℕ → ℝ) (lambda : ℝ)
    (hint : Integrable (fun x => Real.exp (lambda * apertureGauge A phi x)) mu) :
    (∫ x, Real.exp (lambda * apertureGauge A phi x) ∂mu) =
      mu.real ((⋃ n, A n)ᶜ) +
        ∑' n, Real.exp (lambda * phi n) * mu.real (A n) := by
  let U : Set X := ⋃ n, A n
  have hU : MeasurableSet U := MeasurableSet.iUnion hA
  have hunion :
      (∫ x in U, Real.exp (lambda * apertureGauge A phi x) ∂mu) =
        ∑' n, Real.exp (lambda * phi n) * mu.real (A n) := by
    rw [integral_iUnion hA hdisj hint.integrableOn]
    apply tsum_congr
    intro n
    calc
      (∫ x in A n, Real.exp (lambda * apertureGauge A phi x) ∂mu) =
          ∫ _x in A n, Real.exp (lambda * phi n) ∂mu := by
        apply setIntegral_congr_fun (hA n)
        intro x hx
        change Real.exp (lambda * apertureGauge A phi x) = Real.exp (lambda * phi n)
        rw [apertureGauge_apply_mem A hdisj phi n hx]
      _ = Real.exp (lambda * phi n) * mu.real (A n) := by
        rw [setIntegral_const]
        simp [mul_comm]
  have hcompl :
      (∫ x in Uᶜ, Real.exp (lambda * apertureGauge A phi x) ∂mu) = mu.real Uᶜ := by
    calc
      (∫ x in Uᶜ, Real.exp (lambda * apertureGauge A phi x) ∂mu) =
          ∫ _x in Uᶜ, 1 ∂mu := by
        apply setIntegral_congr_fun hU.compl
        intro x hx
        change Real.exp (lambda * apertureGauge A phi x) = 1
        rw [apertureGauge_apply_not_mem A phi hx]
        simp
      _ = mu.real Uᶜ := by rw [setIntegral_const]; simp
  calc
    (∫ x, Real.exp (lambda * apertureGauge A phi x) ∂mu) =
        (∫ x in U, Real.exp (lambda * apertureGauge A phi x) ∂mu) +
          ∫ x in Uᶜ, Real.exp (lambda * apertureGauge A phi x) ∂mu :=
      (integral_add_compl hU hint).symm
    _ = (∑' n, Real.exp (lambda * phi n) * mu.real (A n)) + mu.real Uᶜ := by
      rw [hunion, hcompl]
    _ = mu.real Uᶜ + ∑' n, Real.exp (lambda * phi n) * mu.real (A n) := add_comm _ _

/-- Stretched-exponential aperture evacuation gives a finite exponential formation partition at
every smaller tilt. -/
theorem summable_exp_stretchedApertureMass
    (mu : Measure X) [IsFiniteMeasure mu]
    (A : ℕ → Set X) (C beta gamma lambda : ℝ)
    (_hC : 0 < C) (hgamma : 0 < gamma) (_hlambda : 0 ≤ lambda) (hlt : lambda < beta)
    (hmass : ∀ n, mu.real (A n) ≤
      C * Real.exp (-beta * (((n + 1 : ℕ) : ℝ) ^ gamma))) :
    Summable (fun n =>
      Real.exp (lambda * (((n + 1 : ℕ) : ℝ) ^ gamma)) * mu.real (A n)) := by
  have hdelta : 0 < beta - lambda := sub_pos.mpr hlt
  have hbase : Summable (fun n : ℕ =>
      Real.exp (-((beta - lambda) * ((n : ℝ) ^ gamma)))) := by
    have h := summable_rpow_mul_exp_neg_rpow (A := 0) hdelta hgamma
    simpa using h
  have hshift : Summable (fun n : ℕ =>
      Real.exp (-((beta - lambda) * (((n + 1 : ℕ) : ℝ) ^ gamma)))) :=
    (summable_nat_add_iff 1).mpr hbase
  have hmajor : Summable (fun n : ℕ =>
      C * Real.exp (-((beta - lambda) * (((n + 1 : ℕ) : ℝ) ^ gamma)))) :=
    hshift.mul_left C
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (Real.exp_pos _).le measureReal_nonneg)
    (fun n => ?_) hmajor
  let t : ℝ := ((n + 1 : ℕ) : ℝ) ^ gamma
  calc
    Real.exp (lambda * t) * mu.real (A n) ≤
        Real.exp (lambda * t) * (C * Real.exp (-beta * t)) :=
      mul_le_mul_of_nonneg_left (hmass n) (Real.exp_pos _).le
    _ = C * Real.exp (-((beta - lambda) * t)) := by
      rw [← mul_assoc, mul_comm (Real.exp (lambda * t)) C, mul_assoc, ← Real.exp_add]
      congr 1
      ring_nf

end Measurable

end ApertureGauge

/-! ## Cofinal work-degree wall -/

/-- If a nonnegative aperture occupation has finite `gamma`-moment, while positive persistent
current is carried by work of polynomial degree `d`, then necessarily `d > gamma + 1`.

The index is written as `n + 1`, so the statement covers apertures indexed from one without a
special zero case. -/
theorem persistentCurrent_workDegree_gt_gaugeDegree_add_one
    (alpha W : ℕ → ℝ) (K c gamma d : ℝ)
    (hK : 0 < K) (hc : 0 < c)
    (halpha : ∀ n, 0 ≤ alpha n) (_hW : ∀ n, 0 ≤ W n)
    (hwork : ∀ n, W n ≤ K * ((n + 1 : ℕ) : ℝ) ^ d)
    (hcurrent : ∀ n, c ≤ alpha n * W n)
    (hmoment : Summable (fun n => ((n + 1 : ℕ) : ℝ) ^ gamma * alpha n)) :
    gamma + 1 < d := by
  have hlower (n : ℕ) :
      c / K * ((n + 1 : ℕ) : ℝ) ^ (gamma - d) ≤
        ((n + 1 : ℕ) : ℝ) ^ gamma * alpha n := by
    have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hpowd : 0 < ((n + 1 : ℕ) : ℝ) ^ d := Real.rpow_pos_of_pos hn _
    have hden : 0 < K * ((n + 1 : ℕ) : ℝ) ^ d := mul_pos hK hpowd
    have hc' : c ≤ alpha n * (K * ((n + 1 : ℕ) : ℝ) ^ d) :=
      (hcurrent n).trans (mul_le_mul_of_nonneg_left (hwork n) (halpha n))
    have halpha' : c / (K * ((n + 1 : ℕ) : ℝ) ^ d) ≤ alpha n :=
      (div_le_iff₀ hden).2 (by simpa [mul_assoc] using hc')
    calc
      c / K * ((n + 1 : ℕ) : ℝ) ^ (gamma - d) =
          ((n + 1 : ℕ) : ℝ) ^ gamma *
            (c / (K * ((n + 1 : ℕ) : ℝ) ^ d)) := by
        rw [Real.rpow_sub hn]
        field_simp
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ gamma * alpha n :=
        mul_le_mul_of_nonneg_left halpha' (Real.rpow_nonneg hn.le _)
  have hscaled : Summable (fun n => c / K * ((n + 1 : ℕ) : ℝ) ^ (gamma - d)) :=
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (div_nonneg hc.le hK.le) (by positivity))
      hlower hmoment
  have hshift : Summable (fun n => ((n + 1 : ℕ) : ℝ) ^ (gamma - d)) :=
    (summable_mul_left_iff (ne_of_gt (div_pos hc hK))).mp hscaled
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (gamma - d)) :=
    (summable_nat_add_iff 1).mp hshift
  have hexp : gamma - d < -1 := Real.summable_nat_rpow.mp hbase
  linarith

/-- Ordinary exponential evacuation has gauge degree one, so persistent polynomial work must have
degree strictly greater than two. -/
theorem persistentCurrent_workDegree_gt_two
    (alpha W : ℕ → ℝ) (K c d : ℝ)
    (hK : 0 < K) (hc : 0 < c)
    (halpha : ∀ n, 0 ≤ alpha n) (hW : ∀ n, 0 ≤ W n)
    (hwork : ∀ n, W n ≤ K * ((n + 1 : ℕ) : ℝ) ^ d)
    (hcurrent : ∀ n, c ≤ alpha n * W n)
    (hmoment : Summable (fun n => ((n + 1 : ℕ) : ℝ) * alpha n)) :
    2 < d := by
  have hmoment' : Summable (fun n => ((n + 1 : ℕ) : ℝ) ^ (1 : ℝ) * alpha n) := by
    simpa using hmoment
  have h := persistentCurrent_workDegree_gt_gaugeDegree_add_one
    alpha W K c 1 d hK hc halpha hW hwork hcurrent hmoment'
  linarith

/-! ## Global aperture renewal conservation -/

section ApertureRenewal

variable {X : Type*} [MeasurableSpace X]

/-- One finite-KL renewal controls the full occupation series of every disjoint aperture gauge
with finite exponential partition function. -/
theorem disjointAperture_entropyMoment_conservation
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (phi : ℕ → ℝ) (hphi : ∀ n, 0 ≤ phi n)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (hexp : Integrable (fun x => Real.exp (lambda * apertureGauge A phi x)) mu)
    (hfin : klDiv nu mu ≠ ⊤) :
    Integrable (apertureGauge A phi) nu ∧
      HasSum (fun n => phi n * nu.real (A n))
        (∫ x, apertureGauge A phi x ∂nu) ∧
      lambda * (∑' n, phi n * nu.real (A n)) ≤
        (klDiv nu mu).toReal +
          Real.log (∫ x, Real.exp (lambda * apertureGauge A phi x) ∂mu) := by
  have hbudget := integral_le_klDiv_add_log_integral_exp_of_nonneg mu nu
    (fun x => lambda * apertureGauge A phi x)
    (measurable_const.mul (measurable_apertureGauge A hA phi))
    (fun x => mul_nonneg hlambda.le (apertureGauge_nonneg A hdisj phi hphi x)) hexp hfin
  have hint : Integrable (apertureGauge A phi) nu := by
    have hscaled := hbudget.1.const_mul lambda⁻¹
    convert hscaled using 1
    funext x
    field_simp
  have hsum := hasSum_apertureGauge_integral nu A hA hdisj phi hint
  refine ⟨hint, hsum, ?_⟩
  have hbound :
      lambda * (∫ x, apertureGauge A phi x ∂nu) ≤
        (klDiv nu mu).toReal +
          Real.log (∫ x, Real.exp (lambda * apertureGauge A phi x) ∂mu) := by
    simpa only [integral_const_mul] using hbudget.2
  rw [← hsum.tsum_eq] at hbound
  exact hbound

/-- Stretched-exponential evacuation supplies the exact finite partition function and, for one
global finite-KL renewal, the complete `gamma`-occupation moment. -/
theorem stretchedAperture_partition_entropyMoment
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (C beta gamma lambda : ℝ)
    (hC : 0 < C) (hgamma : 0 < gamma) (hlambda : 0 < lambda) (hlt : lambda < beta)
    (hmass : ∀ n, mu.real (A n) ≤
      C * Real.exp (-beta * (((n + 1 : ℕ) : ℝ) ^ gamma)))
    (hfin : klDiv nu mu ≠ ⊤) :
    Integrable (fun x => Real.exp
      (lambda * apertureGauge A (fun n => (((n + 1 : ℕ) : ℝ) ^ gamma)) x)) mu ∧
      (∫ x, Real.exp
          (lambda * apertureGauge A (fun n => (((n + 1 : ℕ) : ℝ) ^ gamma)) x) ∂mu) =
        mu.real ((⋃ n, A n)ᶜ) +
          ∑' n, Real.exp (lambda * (((n + 1 : ℕ) : ℝ) ^ gamma)) * mu.real (A n) ∧
      (∫ x, Real.exp
          (lambda * apertureGauge A (fun n => (((n + 1 : ℕ) : ℝ) ^ gamma)) x) ∂mu) ≤
        1 + C * ∑' n,
          Real.exp (-((beta - lambda) * (((n + 1 : ℕ) : ℝ) ^ gamma))) ∧
      Integrable (apertureGauge A (fun n => (((n + 1 : ℕ) : ℝ) ^ gamma))) nu ∧
      Summable (fun n => (((n + 1 : ℕ) : ℝ) ^ gamma) * nu.real (A n)) ∧
      lambda * (∑' n, (((n + 1 : ℕ) : ℝ) ^ gamma) * nu.real (A n)) ≤
        (klDiv nu mu).toReal + Real.log
          (∫ x, Real.exp
            (lambda * apertureGauge A (fun n => (((n + 1 : ℕ) : ℝ) ^ gamma)) x) ∂mu) := by
  let phi : ℕ → ℝ := fun n => (((n + 1 : ℕ) : ℝ) ^ gamma)
  have hphi : ∀ n, 0 ≤ phi n := fun n => Real.rpow_nonneg (by positivity) _
  have hactual : Summable (fun n => Real.exp (lambda * phi n) * mu.real (A n)) :=
    summable_exp_stretchedApertureMass mu A C beta gamma lambda
      hC hgamma hlambda.le hlt hmass
  have hexp : Integrable (fun x => Real.exp (lambda * apertureGauge A phi x)) mu :=
    integrable_exp_apertureGauge_of_summable mu A hA hdisj phi hphi
      lambda hlambda.le hactual
  have hpartition := integral_exp_apertureGauge mu A hA hdisj phi lambda hexp
  have hdelta : 0 < beta - lambda := sub_pos.mpr hlt
  have hbase : Summable (fun n : ℕ =>
      Real.exp (-((beta - lambda) * ((n : ℝ) ^ gamma)))) := by
    have h := summable_rpow_mul_exp_neg_rpow (A := 0) hdelta hgamma
    simpa using h
  have hshift : Summable (fun n : ℕ =>
      Real.exp (-((beta - lambda) * (((n + 1 : ℕ) : ℝ) ^ gamma)))) :=
    (summable_nat_add_iff 1).mpr hbase
  have hmajor : Summable (fun n : ℕ =>
      C * Real.exp (-((beta - lambda) * (((n + 1 : ℕ) : ℝ) ^ gamma)))) :=
    hshift.mul_left C
  have hterm (n : ℕ) :
      Real.exp (lambda * phi n) * mu.real (A n) ≤
        C * Real.exp (-((beta - lambda) * (((n + 1 : ℕ) : ℝ) ^ gamma))) := by
    let t : ℝ := ((n + 1 : ℕ) : ℝ) ^ gamma
    calc
      Real.exp (lambda * t) * mu.real (A n) ≤
          Real.exp (lambda * t) * (C * Real.exp (-beta * t)) :=
        mul_le_mul_of_nonneg_left (hmass n) (Real.exp_pos _).le
      _ = C * Real.exp (-((beta - lambda) * t)) := by
        rw [← mul_assoc, mul_comm (Real.exp (lambda * t)) C, mul_assoc, ← Real.exp_add]
        congr 1
        ring_nf
  have hseries :
      (∑' n, Real.exp (lambda * phi n) * mu.real (A n)) ≤
        C * ∑' n, Real.exp (-((beta - lambda) * (((n + 1 : ℕ) : ℝ) ^ gamma))) := by
    calc
      (∑' n, Real.exp (lambda * phi n) * mu.real (A n)) ≤
          ∑' n, C * Real.exp
            (-((beta - lambda) * (((n + 1 : ℕ) : ℝ) ^ gamma))) :=
        Summable.tsum_le_tsum hterm hactual hmajor
      _ = C * ∑' n, Real.exp
          (-((beta - lambda) * (((n + 1 : ℕ) : ℝ) ^ gamma)) ) := tsum_mul_left
  have hpartitionBound :
      (∫ x, Real.exp (lambda * apertureGauge A phi x) ∂mu) ≤
        1 + C * ∑' n,
          Real.exp (-((beta - lambda) * (((n + 1 : ℕ) : ℝ) ^ gamma))) := by
    rw [hpartition]
    exact add_le_add measureReal_le_one hseries
  obtain ⟨hint, hmoment, hbudget⟩ := disjointAperture_entropyMoment_conservation
    mu nu A hA hdisj phi hphi lambda hlambda hexp hfin
  exact ⟨hexp, hpartition, hpartitionBound, hint, hmoment.summable, hbudget⟩

/-- Finite global renewal action plus stretched-exponential evacuation forces the sharp work wall
`d > gamma + 1`. -/
theorem stretchedAperture_persistentCurrent_workDegree_gt
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (W : ℕ → ℝ) (C beta gamma lambda K c d : ℝ)
    (hC : 0 < C) (hgamma : 0 < gamma) (hlambda : 0 < lambda) (hlt : lambda < beta)
    (hK : 0 < K) (hc : 0 < c) (hW : ∀ n, 0 ≤ W n)
    (hmass : ∀ n, mu.real (A n) ≤
      C * Real.exp (-beta * (((n + 1 : ℕ) : ℝ) ^ gamma)))
    (hwork : ∀ n, W n ≤ K * ((n + 1 : ℕ) : ℝ) ^ d)
    (hcurrent : ∀ n, c ≤ nu.real (A n) * W n)
    (hfin : klDiv nu mu ≠ ⊤) :
    gamma + 1 < d := by
  obtain ⟨_, _, _, _, hmoment, _⟩ := stretchedAperture_partition_entropyMoment
    mu nu A hA hdisj C beta gamma lambda hC hgamma hlambda hlt hmass hfin
  exact persistentCurrent_workDegree_gt_gaugeDegree_add_one
    (fun n => nu.real (A n)) W K c gamma d hK hc
    (fun _ => measureReal_nonneg) hW hwork hcurrent hmoment

/-- Ordinary exponential evacuation is the `gamma = 1` chart: constant, linear, and quadratic
persistent work are impossible at finite action. -/
theorem exponentialAperture_persistentCurrent_workDegree_gt_two
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (W : ℕ → ℝ) (C beta lambda K c d : ℝ)
    (hC : 0 < C) (hlambda : 0 < lambda) (hlt : lambda < beta)
    (hK : 0 < K) (hc : 0 < c) (hW : ∀ n, 0 ≤ W n)
    (hmass : ∀ n, mu.real (A n) ≤
      C * Real.exp (-beta * ((n + 1 : ℕ) : ℝ)))
    (hwork : ∀ n, W n ≤ K * ((n + 1 : ℕ) : ℝ) ^ d)
    (hcurrent : ∀ n, c ≤ nu.real (A n) * W n)
    (hfin : klDiv nu mu ≠ ⊤) :
    2 < d := by
  have h := stretchedAperture_persistentCurrent_workDegree_gt
    mu nu A hA hdisj W C beta 1 lambda K c d hC one_pos hlambda hlt hK hc hW
    (by simpa using hmass) hwork hcurrent hfin
  linarith

/-- Coordinate-free gauge/work duality: persistent positive current can coexist with a finite
gauge occupation moment only when `phi / W` is summable. -/
theorem persistentCurrent_gauge_div_work_summable
    (alpha W phi : ℕ → ℝ) (c : ℝ)
    (hc : 0 < c) (_halpha : ∀ n, 0 ≤ alpha n)
    (hW : ∀ n, 0 < W n) (hphi : ∀ n, 0 ≤ phi n)
    (hcurrent : ∀ n, c ≤ alpha n * W n)
    (hmoment : Summable (fun n => phi n * alpha n)) :
    Summable (fun n => phi n / W n) := by
  have hmajor : Summable (fun n => c⁻¹ * (phi n * alpha n)) := hmoment.mul_left c⁻¹
  apply Summable.of_nonneg_of_le
    (fun n => div_nonneg (hphi n) (hW n).le) (fun n => ?_) hmajor
  have hcW : c / W n ≤ alpha n := by
    rw [div_le_iff₀ (hW n)]
    simpa [mul_comm] using hcurrent n
  have hscaled : c * (phi n / W n) ≤ phi n * alpha n := by
    calc
      c * (phi n / W n) = phi n * (c / W n) := by ring
      _ ≤ phi n * alpha n := mul_le_mul_of_nonneg_left hcW (hphi n)
  rw [inv_mul_eq_div, le_div_iff₀ hc]
  simpa [mul_comm] using hscaled

/-- Work dominated by the gauge has summable total current, with the exact total-series bound. -/
theorem gaugeDominated_totalCurrent_summable
    (alpha W phi : ℕ → ℝ) (K : ℝ)
    (_hK : 0 ≤ K) (halpha : ∀ n, 0 ≤ alpha n)
    (hW : ∀ n, 0 ≤ W n) (_hphi : ∀ n, 0 ≤ phi n)
    (hwork : ∀ n, W n ≤ K * phi n)
    (hmoment : Summable (fun n => phi n * alpha n)) :
    Summable (fun n => alpha n * W n) ∧
      (∑' n, alpha n * W n) ≤ K * ∑' n, phi n * alpha n := by
  have hmajor : Summable (fun n => K * (phi n * alpha n)) := hmoment.mul_left K
  have hle (n : ℕ) : alpha n * W n ≤ K * (phi n * alpha n) := by
    calc
      alpha n * W n ≤ alpha n * (K * phi n) :=
        mul_le_mul_of_nonneg_left (hwork n) (halpha n)
      _ = K * (phi n * alpha n) := by ring
  have hsum : Summable (fun n => alpha n * W n) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (halpha n) (hW n)) hle hmajor
  refine ⟨hsum, ?_⟩
  calc
    (∑' n, alpha n * W n) ≤ ∑' n, K * (phi n * alpha n) :=
      Summable.tsum_le_tsum hle hsum hmajor
    _ = K * ∑' n, phi n * alpha n := tsum_mul_left

/-- Markov properness of a finite-action KL sublevel, stated for real aperture mass. -/
theorem disjointAperture_KLSublevel_tail_bound
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (phi : ℕ → ℝ) (hphi : ∀ n, 0 ≤ phi n)
    (lambda R M : ℝ) (hlambda : 0 < lambda) (hR : 0 < R)
    (hexp : Integrable (fun x => Real.exp (lambda * apertureGauge A phi x)) mu)
    (hfin : klDiv nu mu ≠ ⊤) (hsublevel : (klDiv nu mu).toReal ≤ M) :
    nu.real {x | R < apertureGauge A phi x} ≤
      (M + Real.log (∫ x, Real.exp (lambda * apertureGauge A phi x) ∂mu)) /
        (lambda * R) := by
  obtain ⟨hint, _, hbudget⟩ := disjointAperture_entropyMoment_conservation
    mu nu A hA hdisj phi hphi lambda hlambda hexp hfin
  let N := apertureGauge A phi
  let s : Set X := {x | R < N x}
  have hN0 : ∀ x, 0 ≤ N x := apertureGauge_nonneg A hdisj phi hphi
  have hscaledInt : Integrable (fun x => R⁻¹ * N x) nu := hint.const_mul R⁻¹
  have hmarkov : nu s ≤ ENNReal.ofReal (∫ x, R⁻¹ * N x ∂nu) := by
    apply hscaledInt.measure_le_integral (ae_of_all _ fun x => mul_nonneg (inv_nonneg.mpr hR.le) (hN0 x))
    intro x hx
    change R < N x at hx
    exact (le_inv_mul_iff₀ hR).2 (by simpa using le_of_lt hx)
  have hintegral0 : 0 ≤ ∫ x, R⁻¹ * N x ∂nu :=
    integral_nonneg fun x => mul_nonneg (inv_nonneg.mpr hR.le) (hN0 x)
  have hmarkovReal : nu.real s ≤ (∫ x, N x ∂nu) / R := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmarkov
    rw [ENNReal.toReal_ofReal hintegral0, integral_const_mul] at h
    change (nu s).toReal ≤ (∫ x, N x ∂nu) / R
    simpa [inv_mul_eq_div] using h
  have hbudget' :
      lambda * (∫ x, N x ∂nu) ≤
        M + Real.log (∫ x, Real.exp (lambda * N x) ∂mu) := by
    rw [← integral_apertureGauge nu A hA hdisj phi hint] at hbudget
    exact hbudget.trans (add_le_add hsublevel le_rfl)
  calc
    nu.real s ≤ (∫ x, N x ∂nu) / R := hmarkovReal
    _ ≤ ((M + Real.log (∫ x, Real.exp (lambda * N x) ∂mu)) / lambda) / R := by
      exact div_le_div_of_nonneg_right
        ((le_div_iff₀ hlambda).2 (by simpa [mul_comm] using hbudget')) hR.le
    _ = (M + Real.log (∫ x, Real.exp (lambda * N x) ∂mu)) / (lambda * R) := by
      field_simp

/-- Under ordinary exponential evacuation, any current whose work is at most linear has a finite
total series, quantitatively bounded by the same global KL budget. -/
theorem exponentialAperture_totalLinearCurrent_bound
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (W : ℕ → ℝ) (C beta lambda K : ℝ)
    (hC : 0 < C) (hlambda : 0 < lambda) (hlt : lambda < beta) (hK : 0 ≤ K)
    (hW0 : ∀ n, 0 ≤ W n)
    (hmass : ∀ n, mu.real (A n) ≤
      C * Real.exp (-beta * ((n + 1 : ℕ) : ℝ)))
    (hwork : ∀ n, W n ≤ K * ((n + 1 : ℕ) : ℝ))
    (hfin : klDiv nu mu ≠ ⊤) :
    Summable (fun n => nu.real (A n) * W n) ∧
      (∑' n, nu.real (A n) * W n) ≤
        (K / lambda) *
          ((klDiv nu mu).toReal + Real.log
            (∫ x, Real.exp
              (lambda * apertureGauge A (fun n => ((n + 1 : ℕ) : ℝ)) x) ∂mu)) := by
  obtain ⟨_, _, _, _, hmomentRaw, hbudgetRaw⟩ := stretchedAperture_partition_entropyMoment
    mu nu A hA hdisj C beta 1 lambda hC one_pos hlambda hlt
      (by simpa using hmass) hfin
  have hmoment : Summable (fun n => ((n + 1 : ℕ) : ℝ) * nu.real (A n)) := by
    simpa using hmomentRaw
  have hcurrent := gaugeDominated_totalCurrent_summable
    (fun n => nu.real (A n)) W (fun n => ((n + 1 : ℕ) : ℝ)) K
    hK (fun _ => measureReal_nonneg) hW0 (fun _ => by positivity) hwork hmoment
  refine ⟨hcurrent.1, hcurrent.2.trans ?_⟩
  have hbudget :
      lambda * (∑' n, ((n + 1 : ℕ) : ℝ) * nu.real (A n)) ≤
        (klDiv nu mu).toReal + Real.log
          (∫ x, Real.exp
            (lambda * apertureGauge A (fun n => ((n + 1 : ℕ) : ℝ)) x) ∂mu) := by
    simpa using hbudgetRaw
  have hmomentBound :
      (∑' n, ((n + 1 : ℕ) : ℝ) * nu.real (A n)) ≤
        ((klDiv nu mu).toReal + Real.log
          (∫ x, Real.exp
            (lambda * apertureGauge A (fun n => ((n + 1 : ℕ) : ℝ)) x) ∂mu)) / lambda :=
    (le_div_iff₀ hlambda).2 (by simpa [mul_comm] using hbudget)
  calc
    K * (∑' n, ((n + 1 : ℕ) : ℝ) * nu.real (A n)) ≤
        K * (((klDiv nu mu).toReal + Real.log
          (∫ x, Real.exp
            (lambda * apertureGauge A (fun n => ((n + 1 : ℕ) : ℝ)) x) ∂mu)) / lambda) :=
      mul_le_mul_of_nonneg_left hmomentBound hK
    _ = (K / lambda) *
        ((klDiv nu mu).toReal + Real.log
          (∫ x, Real.exp
            (lambda * apertureGauge A (fun n => ((n + 1 : ℕ) : ℝ)) x) ∂mu)) := by
      field_simp

end ApertureRenewal

/-! ## Horizontal--vertical packet action -/

section PacketAction

variable {X H : Type*} [MeasurableSpace X] [MeasurableSpace H]

/-- The observer marginal action of an arbitrary packet renewal cannot exceed its full action.
No standard-Borel assumption is needed. -/
theorem packetMarginal_klDiv_le
    (μ : Measure X) (Q : Measure (X × H))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
    (K : Kernel X H) [IsMarkovKernel K] :
    klDiv Q.fst μ ≤ klDiv Q (μ ⊗ₘ K) := by
  have h := klDiv_map_le_arbitrary Q (μ ⊗ₘ K) Prod.fst measurable_fst
  rw [← Measure.fst] at h
  have hbase : Measure.map Prod.fst (μ ⊗ₘ K) = μ := by
    rw [← Measure.fst, Measure.fst_compProd]
  rw [hbase] at h
  exact h

/-- Packet entropy controls the recovered formation gauge for an arbitrary correlated observer /
history renewal.  Finiteness of the gauge under `Q` is proved from finite packet action and the
baseline exponential moment. -/
theorem packetEntropy_controls_horizontalGauge
    (μ : Measure X) (Q : Measure (X × H))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
    (K : Kernel X H) [IsMarkovKernel K]
    (N : X → ℝ) (hN : Measurable N) (hN0 : ∀ x, 0 ≤ N x)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (hexp : Integrable (fun x => Real.exp (lambda * N x)) μ)
    (hfin : klDiv Q (μ ⊗ₘ K) ≠ ⊤) :
    Integrable (fun p : X × H => N p.1) Q ∧
      lambda * (∫ p : X × H, N p.1 ∂Q) ≤
        (klDiv Q (μ ⊗ₘ K)).toReal +
          Real.log (∫ x, Real.exp (lambda * N x) ∂μ) := by
  have hexp_packet :
      Integrable (fun p : X × H => Real.exp (lambda * N p.1)) (μ ⊗ₘ K) := by
    have hmeas : Measurable (fun p : X × H => Real.exp (lambda * N p.1)) :=
      Real.continuous_exp.measurable.comp (measurable_const.mul (hN.comp measurable_fst))
    rw [Measure.integrable_compProd_iff hmeas.aestronglyMeasurable]
    constructor
    · filter_upwards with x
      exact integrable_const _
    · convert hexp using 1
      funext x
      simp [Real.norm_eq_abs, Real.abs_exp]
  have hZ :
      (∫ p : X × H, Real.exp (lambda * N p.1) ∂(μ ⊗ₘ K)) =
        ∫ x, Real.exp (lambda * N x) ∂μ := by
    rw [Measure.integral_compProd hexp_packet]
    simp
  have hbudget := integral_le_klDiv_add_log_integral_exp_of_nonneg
    (μ ⊗ₘ K) Q (fun p : X × H => lambda * N p.1)
    (by fun_prop) (fun p => mul_nonneg hlambda.le (hN0 p.1)) hexp_packet hfin
  have hNQ : Integrable (fun p : X × H => N p.1) Q := by
    have hscaled := hbudget.1.const_mul lambda⁻¹
    convert hscaled using 1
    funext p
    field_simp
  refine ⟨hNQ, ?_⟩
  rw [← hZ]
  simpa only [integral_const_mul] using hbudget.2

/-- A recovered-coordinate gauge has the same packet and observer-marginal integrals. -/
theorem packetGauge_integral_eq_marginal
    (Q : Measure (X × H)) [IsProbabilityMeasure Q]
    (N : X → ℝ) (hN : Measurable N) :
    (∫ p : X × H, N p.1 ∂Q) = ∫ x, N x ∂Q.fst := by
  rw [Measure.fst]
  exact (integral_map measurable_fst.aemeasurable hN.aestronglyMeasurable).symm

/-- Observer-aperture mass in the marginal is exactly mass of the corresponding full-history
cylinder in the packet. -/
theorem packetFst_real_apply
    (Q : Measure (X × H)) (A : Set X) (hA : MeasurableSet A) :
    Q.fst.real A = Q.real (A ×ˢ (Set.univ : Set H)) := by
  rw [measureReal_def, measureReal_def, Measure.fst_apply hA]
  congr 2
  ext p
  simp

/-- Finite arbitrary packet action controls every disjoint observer-aperture occupation moment;
the right side is the total packet KL, not merely marginal KL. -/
theorem arbitraryPacket_disjointAperture_entropyMoment
    (mu : Measure X) [IsProbabilityMeasure mu]
    (K : Kernel X H) [IsMarkovKernel K]
    (Q : Measure (X × H)) [IsProbabilityMeasure Q]
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (phi : ℕ → ℝ) (hphi : ∀ n, 0 ≤ phi n)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (hexp : Integrable (fun x => Real.exp (lambda * apertureGauge A phi x)) mu)
    (hfin : klDiv Q (mu ⊗ₘ K) ≠ ⊤) :
    Integrable (apertureGauge A phi) Q.fst ∧
      HasSum (fun n => phi n * Q.real (A n ×ˢ (Set.univ : Set H)))
        (∫ x, apertureGauge A phi x ∂Q.fst) ∧
      lambda * (∑' n, phi n * Q.real (A n ×ˢ (Set.univ : Set H))) ≤
        (klDiv Q (mu ⊗ₘ K)).toReal +
          Real.log (∫ x, Real.exp (lambda * apertureGauge A phi x) ∂mu) := by
  have hcontract := packetMarginal_klDiv_le mu Q K
  have hfinMarg : klDiv Q.fst mu ≠ ⊤ := ne_top_of_le_ne_top hfin hcontract
  obtain ⟨hint, hsum, hbudget⟩ := disjointAperture_entropyMoment_conservation
    mu Q.fst A hA hdisj phi hphi lambda hlambda hexp hfinMarg
  have hsumPacket :
      HasSum (fun n => phi n * Q.real (A n ×ˢ (Set.univ : Set H)))
        (∫ x, apertureGauge A phi x ∂Q.fst) := by
    convert hsum using 1
    funext n
    rw [packetFst_real_apply Q (A n) (hA n)]
  refine ⟨hint, hsumPacket, ?_⟩
  have hreal := ENNReal.toReal_mono hfin hcontract
  have hbudget' := hbudget.trans (add_le_add hreal le_rfl)
  simpa only [hsum.tsum_eq, hsumPacket.tsum_eq] using hbudget'

/-- Arbitrary correlated history interventions obey the same sharp stretched-exponential work
wall as observer-only renewals. -/
theorem arbitraryPacket_stretchedAperture_workDegree_gt
    (mu : Measure X) [IsProbabilityMeasure mu]
    (K : Kernel X H) [IsMarkovKernel K]
    (Q : Measure (X × H)) [IsProbabilityMeasure Q]
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (W : ℕ → ℝ) (C beta gamma lambda Kwork c d : ℝ)
    (hC : 0 < C) (hgamma : 0 < gamma) (hlambda : 0 < lambda) (hlt : lambda < beta)
    (hKwork : 0 < Kwork) (hc : 0 < c) (hW : ∀ n, 0 ≤ W n)
    (hmass : ∀ n, mu.real (A n) ≤
      C * Real.exp (-beta * (((n + 1 : ℕ) : ℝ) ^ gamma)))
    (hwork : ∀ n, W n ≤ Kwork * ((n + 1 : ℕ) : ℝ) ^ d)
    (hcurrent : ∀ n,
      c ≤ Q.real (A n ×ˢ (Set.univ : Set H)) * W n)
    (hfin : klDiv Q (mu ⊗ₘ K) ≠ ⊤) :
    gamma + 1 < d := by
  have hcontract := packetMarginal_klDiv_le mu Q K
  have hfinMarg : klDiv Q.fst mu ≠ ⊤ := ne_top_of_le_ne_top hfin hcontract
  apply stretchedAperture_persistentCurrent_workDegree_gt
    mu Q.fst A hA hdisj W C beta gamma lambda Kwork c d
    hC hgamma hlambda hlt hKwork hc hW hmass hwork
  · intro n
    rw [packetFst_real_apply Q (A n) (hA n)]
    exact hcurrent n
  · exact hfinMarg

/-- Vertical deviation from a certified recovery kernel, expressed without choosing coordinates
or a disintegration. -/
noncomputable def packetVerticalAction
    (ν : Measure X) (L K : Kernel X H) : ℝ≥0∞ :=
  klDiv (ν ⊗ₘ L) (ν ⊗ₘ K)

/-- Exact horizontal--vertical conservation for a split packet. -/
theorem splitPacket_klDiv_eq_horizontal_add_vertical
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (L K : Kernel X H) [IsMarkovKernel L] [IsMarkovKernel K] :
    klDiv (ν ⊗ₘ L) (μ ⊗ₘ K) = klDiv ν μ + packetVerticalAction ν L K := by
  exact klDiv_compProd_eq_add ν μ L K

/-- On a standard-Borel history space, every arbitrary packet has the exact horizontal--vertical
chain rule through its canonical regular conditional kernel. -/
theorem arbitraryPacket_klDiv_eq_horizontal_add_vertical
    (μ : Measure X) [IsProbabilityMeasure μ]
    (Q : Measure (X × H)) [IsProbabilityMeasure Q]
    [StandardBorelSpace H] [Nonempty H]
    (K : Kernel X H) [IsMarkovKernel K] :
    klDiv Q (μ ⊗ₘ K) =
      klDiv Q.fst μ + packetVerticalAction Q.fst Q.condKernel K := by
  have hQ : Q.fst ⊗ₘ Q.condKernel = Q := Q.disintegrate Q.condKernel
  calc
    klDiv Q (μ ⊗ₘ K) = klDiv (Q.fst ⊗ₘ Q.condKernel) (μ ⊗ₘ K) := by
      exact congrArg (fun rho => klDiv rho (μ ⊗ₘ K)) hQ.symm
    _ = klDiv Q.fst μ + packetVerticalAction Q.fst Q.condKernel K :=
      splitPacket_klDiv_eq_horizontal_add_vertical μ Q.fst Q.condKernel K

/-- The sharpened conservation law: horizontal formation cost and vertical recovery deviation draw
from one exact packet information budget. -/
theorem splitPacket_horizontal_vertical_budget
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (L K : Kernel X H) [IsMarkovKernel L] [IsMarkovKernel K]
    (N : X → ℝ) (hN : Measurable N) (hN0 : ∀ x, 0 ≤ N x)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (hexp : Integrable (fun x => Real.exp (lambda * N x)) μ)
    (hfin : klDiv (ν ⊗ₘ L) (μ ⊗ₘ K) ≠ ⊤) :
    Integrable N ν ∧
      lambda * (∫ x, N x ∂ν) + (packetVerticalAction ν L K).toReal ≤
        (klDiv (ν ⊗ₘ L) (μ ⊗ₘ K)).toReal +
          Real.log (∫ x, Real.exp (lambda * N x) ∂μ) := by
  have hchain := splitPacket_klDiv_eq_horizontal_add_vertical μ ν L K
  have haddfin : klDiv ν μ + packetVerticalAction ν L K ≠ ⊤ := by
    rw [← hchain]
    exact hfin
  obtain ⟨hhorizontal, hvertical⟩ := ENNReal.add_ne_top.mp haddfin
  have hexp' : Integrable (fun x => Real.exp (lambda * N x)) μ := hexp
  have hobs := integral_le_klDiv_add_log_integral_exp_of_nonneg μ ν
    (fun x => lambda * N x) (by fun_prop)
    (fun x => mul_nonneg hlambda.le (hN0 x)) hexp' hhorizontal
  have hNν : Integrable N ν := by
    have hscaled := hobs.1.const_mul lambda⁻¹
    convert hscaled using 1
    funext x
    field_simp
  refine ⟨hNν, ?_⟩
  have hreal :
      (klDiv (ν ⊗ₘ L) (μ ⊗ₘ K)).toReal =
        (klDiv ν μ).toReal + (packetVerticalAction ν L K).toReal := by
    rw [hchain, ENNReal.toReal_add hhorizontal hvertical]
  rw [hreal]
  have hobs' :
      lambda * (∫ x, N x ∂ν) ≤
        (klDiv ν μ).toReal + Real.log (∫ x, Real.exp (lambda * N x) ∂μ) := by
    simpa only [integral_const_mul] using hobs.2
  linarith

/-- Standard-Borel arbitrary-packet form of the sharpened horizontal--vertical conservation
budget. -/
theorem arbitraryPacket_horizontal_vertical_budget
    (μ : Measure X) [IsProbabilityMeasure μ]
    (Q : Measure (X × H)) [IsProbabilityMeasure Q]
    [StandardBorelSpace H] [Nonempty H]
    (K : Kernel X H) [IsMarkovKernel K]
    (N : X → ℝ) (hN : Measurable N) (hN0 : ∀ x, 0 ≤ N x)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (hexp : Integrable (fun x => Real.exp (lambda * N x)) μ)
    (hfin : klDiv Q (μ ⊗ₘ K) ≠ ⊤) :
    Integrable N Q.fst ∧
      lambda * (∫ x, N x ∂Q.fst) +
          (packetVerticalAction Q.fst Q.condKernel K).toReal ≤
        (klDiv Q (μ ⊗ₘ K)).toReal +
          Real.log (∫ x, Real.exp (lambda * N x) ∂μ) := by
  have hQ : Q.fst ⊗ₘ Q.condKernel = Q := Q.disintegrate Q.condKernel
  have hkl : klDiv (Q.fst ⊗ₘ Q.condKernel) (μ ⊗ₘ K) = klDiv Q (μ ⊗ₘ K) :=
    congrArg (fun rho => klDiv rho (μ ⊗ₘ K)) hQ
  have hfinSplit : klDiv (Q.fst ⊗ₘ Q.condKernel) (μ ⊗ₘ K) ≠ ⊤ := by
    rwa [hkl]
  have hbudget := splitPacket_horizontal_vertical_budget
    μ Q.fst Q.condKernel K N hN hN0 lambda hlambda hexp hfinSplit
  rwa [hkl] at hbudget

/-- Under the paper's absolute-continuity assumption, vertical action is exactly the integral of
the fibrewise conditional divergences. -/
theorem packetVerticalAction_eq_lintegral
    (ν : Measure X) [IsProbabilityMeasure ν]
    [MeasurableSpace.CountableOrCountablyGenerated X H]
    (L K : Kernel X H) [IsMarkovKernel L] [IsMarkovKernel K]
    (hac : ν ⊗ₘ L ≪ ν ⊗ₘ K) :
    packetVerticalAction ν L K = ∫⁻ x, klDiv (L x) (K x) ∂ν := by
  exact klDiv_compProd_right ν L K hac

/-- Fibrewise form of the arbitrary-packet chain rule under the card's absolute-continuity and
standard-Borel hypotheses. -/
theorem arbitraryPacket_klDiv_eq_horizontal_add_lintegral
    (μ : Measure X) [IsProbabilityMeasure μ]
    (Q : Measure (X × H)) [IsProbabilityMeasure Q]
    [StandardBorelSpace H] [Nonempty H]
    [MeasurableSpace.CountableOrCountablyGenerated X H]
    (K : Kernel X H) [IsMarkovKernel K]
    (hac : Q ≪ μ ⊗ₘ K) :
    klDiv Q (μ ⊗ₘ K) =
      klDiv Q.fst μ + ∫⁻ x, klDiv (Q.condKernel x) (K x) ∂Q.fst := by
  have hQ : Q.fst ⊗ₘ Q.condKernel = Q := Q.disintegrate Q.condKernel
  have hac' : Q.fst ⊗ₘ Q.condKernel ≪ μ ⊗ₘ K := by rwa [hQ]
  have hacVertical : Q.fst ⊗ₘ Q.condKernel ≪ Q.fst ⊗ₘ K :=
    Measure.AbsolutelyContinuous.compProd_right hac'.kernel_of_compProd
  rw [arbitraryPacket_klDiv_eq_horizontal_add_vertical μ Q K,
    packetVerticalAction_eq_lintegral Q.fst Q.condKernel K hacVertical]

/-- Vertical action vanishes exactly for the certified recovery kernel, up to the unavoidable
`ν`-almost-everywhere identification of kernels. -/
theorem packetVerticalAction_eq_zero_iff
    (ν : Measure X) [IsProbabilityMeasure ν]
    [MeasurableSpace.CountableOrCountablyGenerated X H]
    (L K : Kernel X H) [IsMarkovKernel L] [IsMarkovKernel K] :
    packetVerticalAction ν L K = 0 ↔ L =ᵐ[ν] K := by
  rw [packetVerticalAction, klDiv_eq_zero_iff, Kernel.compProd_eq_iff]

/-- The common-recovery split packet realizes exactly the observer marginal action. -/
theorem commonRecovery_klDiv
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : Kernel X H) [IsMarkovKernel K] :
    klDiv (ν ⊗ₘ K) (μ ⊗ₘ K) = klDiv ν μ :=
  klDiv_compProd_left ν μ K

/-- Among all split packets with fixed observer marginal, common recovery uniquely minimizes full
action whenever the horizontal action is finite. -/
theorem splitPacket_minimumAction_eq_iff
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [MeasurableSpace.CountableOrCountablyGenerated X H]
    (L K : Kernel X H) [IsMarkovKernel L] [IsMarkovKernel K]
    (hfin : klDiv ν μ ≠ ⊤) :
    klDiv (ν ⊗ₘ L) (μ ⊗ₘ K) = klDiv ν μ ↔ L =ᵐ[ν] K := by
  rw [splitPacket_klDiv_eq_horizontal_add_vertical]
  constructor
  · intro h
    have hzero : packetVerticalAction ν L K = 0 := by
      have hc : klDiv ν μ + packetVerticalAction ν L K = klDiv ν μ + 0 := by
        simpa using h
      exact (ENNReal.add_right_inj hfin).mp hc
    exact (packetVerticalAction_eq_zero_iff ν L K).mp hzero
  · intro h
    rw [(packetVerticalAction_eq_zero_iff ν L K).mpr h, add_zero]

/-- Canonical common recovery is the unique least-action representative of an arbitrary packet's
observer marginal, expressed through standard-Borel disintegration. -/
theorem arbitraryPacket_minimumAction_eq_iff
    (μ : Measure X) [IsProbabilityMeasure μ]
    (Q : Measure (X × H)) [IsProbabilityMeasure Q]
    [StandardBorelSpace H] [Nonempty H]
    [MeasurableSpace.CountableOrCountablyGenerated X H]
    (K : Kernel X H) [IsMarkovKernel K]
    (hfin : klDiv Q.fst μ ≠ ⊤) :
    klDiv Q (μ ⊗ₘ K) = klDiv Q.fst μ ↔ Q.condKernel =ᵐ[Q.fst] K := by
  have hQ : Q.fst ⊗ₘ Q.condKernel = Q := Q.disintegrate Q.condKernel
  have hkl : klDiv Q (μ ⊗ₘ K) =
      klDiv (Q.fst ⊗ₘ Q.condKernel) (μ ⊗ₘ K) :=
    congrArg (fun rho => klDiv rho (μ ⊗ₘ K)) hQ.symm
  rw [hkl]
  exact splitPacket_minimumAction_eq_iff μ Q.fst Q.condKernel K hfin

end PacketAction

end GaloisForLFunctions.HTGeometry
