import GaloisForLFunctions.RHTower.CCMActualHeadExteriorCosineMeasureGauge
import GaloisForLFunctions.RHTower.SoninReferenceTailSup
import GaloisForLFunctions.RHTower.SoninScaledMeanBound
import GaloisForLFunctions.RHTower.SoninRefTailWeightedVanishing

/-!
# Dual total-mass wall for exterior cosine gauges

The exterior finite-measure gauge ideal is locally expressive, but expansion of the controlled
physical window has an unavoidable global price.  Pairing an arbitrary exterior cosine transform
with the corpus's compact Sonin profile converts support separation into the uniform Fourier-tail
majorant.  This gives an exact lower bound on combined positive/negative measure mass.

For any fixed exterior threshold `H₀ > 0` and fixed approximation error `ε < 1`, every sequence of
positive-minus-positive finite measures approximating the constant mode on expanding Sonin windows
has combined mass tending to infinity.  No atomicity or canonical packet representation is used.
-/

open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform

noncomputable section

namespace RHTower

theorem integrable_soninScaledAnnulusBump_mul_exteriorCosineJoint
    (m δ : ℝ) (hδ : 0 < δ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (Function.uncurry fun h x : ℝ =>
      soninScaledAnnulusBump m δ x * Real.cos (2 * Real.pi * h * x))
      (μ.prod volume) := by
  have hφ := integrable_soninScaledAnnulusBump m δ hδ
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) μ := integrable_const 1
  have hmajor : Integrable (fun p : ℝ × ℝ =>
      (1 : ℝ) * soninScaledAnnulusBump m δ p.2) (μ.prod volume) :=
    hone.mul_prod hφ
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      soninScaledAnnulusBump m δ p.2 * Real.cos (2 * Real.pi * p.1 * p.2))
      (μ.prod volume) := by
    apply Continuous.aestronglyMeasurable
    exact ((contDiff_soninScaledAnnulusBump m δ hδ).continuous.comp continuous_snd).mul
      (Real.continuous_cos.comp
        ((continuous_const.mul continuous_fst).mul continuous_snd))
  apply hmajor.mono' hmeas
  filter_upwards with p
  have hφ0 := soninScaledAnnulusBump_nonneg m δ p.2
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hφ0, one_mul]
  exact mul_le_of_le_one_right hφ0 (Real.abs_cos_le_one _)

theorem integrable_soninScaledAnnulusBump_mul_exteriorCosineMeasureGauge
    (m δ : ℝ) (hδ : 0 < δ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun x : ℝ =>
      soninScaledAnnulusBump m δ x * ccmActualHeadExteriorCosineMeasureGauge μ x) := by
  let K : ℝ → ℝ → ℝ := fun h x =>
    soninScaledAnnulusBump m δ x * Real.cos (2 * Real.pi * h * x)
  have hK : Integrable (Function.uncurry K) (μ.prod volume) := by
    simpa only [K] using
      integrable_soninScaledAnnulusBump_mul_exteriorCosineJoint m δ hδ μ
  exact hK.integral_prod_right.congr (Filter.Eventually.of_forall fun x => by
    change (∫ h : ℝ, K h x ∂μ) =
      soninScaledAnnulusBump m δ x *
        (∫ h : ℝ, Real.cos (2 * Real.pi * h * x) ∂μ)
    rw [← MeasureTheory.integral_const_mul])

theorem integral_soninScaledAnnulusBump_mul_exteriorCosineMeasureGauge_eq
    (m δ : ℝ) (hδ : 0 < δ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (∫ x : ℝ, soninScaledAnnulusBump m δ x *
        ccmActualHeadExteriorCosineMeasureGauge μ x) =
      ∫ h : ℝ, (∫ x : ℝ,
        soninScaledAnnulusBump m δ x * Real.cos (2 * Real.pi * h * x)) ∂μ := by
  let K : ℝ → ℝ → ℝ := fun h x =>
    soninScaledAnnulusBump m δ x * Real.cos (2 * Real.pi * h * x)
  have hK : Integrable (Function.uncurry K) (μ.prod volume) := by
    simpa only [K] using
      integrable_soninScaledAnnulusBump_mul_exteriorCosineJoint m δ hδ μ
  have hswap := MeasureTheory.integral_integral_swap hK
  calc
    (∫ x : ℝ, soninScaledAnnulusBump m δ x *
        ccmActualHeadExteriorCosineMeasureGauge μ x) =
        ∫ x : ℝ, ∫ h : ℝ, K h x ∂μ := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          unfold ccmActualHeadExteriorCosineMeasureGauge
          rw [← MeasureTheory.integral_const_mul]
    _ = ∫ h : ℝ, (∫ x : ℝ, K h x) ∂μ := by
          simpa only using hswap.symm
    _ = _ := by rfl

theorem abs_integral_soninScaledAnnulusBump_mul_cos_le_tailSup
    (m δ H₀ h : ℝ) (hδ : 0 < δ) (hH₀ : 0 ≤ H₀) (hh : H₀ ≤ h) :
    |∫ x : ℝ, soninScaledAnnulusBump m δ x *
        Real.cos (2 * Real.pi * h * x)| ≤
      4 * δ * soninRefTailSup (δ * H₀) := by
  have hh0 : 0 ≤ h := hH₀.trans hh
  have hmain := abs_integral_soninScaledAnnulusBump_mul_cos_le m δ h hδ
  have htail (v : ℝ) (hv : δ * H₀ ≤ |v|) :
      ‖𝓕 soninUnitBumpC v‖ ≤ soninRefTailSup (δ * H₀) :=
    norm_fourier_soninUnitBumpC_le_tailSup hv
  have hvpos : δ * H₀ ≤ |δ * h| := by
    rw [abs_mul, abs_of_pos hδ, abs_of_nonneg hh0]
    exact mul_le_mul_of_nonneg_left hh hδ.le
  have hvneg : δ * H₀ ≤ |δ * -h| := by
    rw [abs_mul, abs_of_pos hδ, abs_neg, abs_of_nonneg hh0]
    exact mul_le_mul_of_nonneg_left hh hδ.le
  have h₁ := htail (δ * h) hvpos
  have h₂ := htail (δ * -h) hvneg
  have h₃ := htail (δ * -(-h)) (by simpa only [neg_neg] using hvpos)
  have hS := soninRefTailSup_nonneg (δ * H₀)
  nlinarith

theorem abs_integral_soninScaledAnnulusBump_mul_exteriorCosineMeasureGauge_le
    (m δ H₀ : ℝ) (hδ : 0 < δ) (hH₀ : 0 ≤ H₀)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ h : ℝ ∂μ, H₀ ≤ h) :
    |∫ x : ℝ, soninScaledAnnulusBump m δ x *
        ccmActualHeadExteriorCosineMeasureGauge μ x| ≤
      (4 * δ * soninRefTailSup (δ * H₀)) * μ.real Set.univ := by
  rw [integral_soninScaledAnnulusBump_mul_exteriorCosineMeasureGauge_eq m δ hδ μ]
  simpa only [Real.norm_eq_abs] using
    (MeasureTheory.norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun h : ℝ => ∫ x : ℝ,
        soninScaledAnnulusBump m δ x * Real.cos (2 * Real.pi * h * x))
      (C := 4 * δ * soninRefTailSup (δ * H₀)) (by
        filter_upwards [hμ] with h hh
        simpa only [Real.norm_eq_abs] using
          abs_integral_soninScaledAnnulusBump_mul_cos_le_tailSup
            m δ H₀ h hδ hH₀ hh))

theorem abs_integral_soninScaledAnnulusBump_mul_exteriorCosineGauge_sub_le
    (m δ H₀ : ℝ) (hδ : 0 < δ) (hH₀ : 0 ≤ H₀)
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ h : ℝ ∂μ, H₀ ≤ h) (hν : ∀ᵐ h : ℝ ∂ν, H₀ ≤ h) :
    |∫ x : ℝ, soninScaledAnnulusBump m δ x *
        (ccmActualHeadExteriorCosineMeasureGauge μ x -
          ccmActualHeadExteriorCosineMeasureGauge ν x)| ≤
      (4 * δ * soninRefTailSup (δ * H₀)) *
        (μ.real Set.univ + ν.real Set.univ) := by
  have hμint :=
    integrable_soninScaledAnnulusBump_mul_exteriorCosineMeasureGauge m δ hδ μ
  have hνint :=
    integrable_soninScaledAnnulusBump_mul_exteriorCosineMeasureGauge m δ hδ ν
  rw [show (fun x : ℝ => soninScaledAnnulusBump m δ x *
      (ccmActualHeadExteriorCosineMeasureGauge μ x -
        ccmActualHeadExteriorCosineMeasureGauge ν x)) =
      fun x : ℝ =>
        soninScaledAnnulusBump m δ x * ccmActualHeadExteriorCosineMeasureGauge μ x -
        soninScaledAnnulusBump m δ x * ccmActualHeadExteriorCosineMeasureGauge ν x by
      funext x
      ring,
    integral_sub hμint hνint]
  calc
    |(∫ x : ℝ, soninScaledAnnulusBump m δ x *
        ccmActualHeadExteriorCosineMeasureGauge μ x) -
      (∫ x : ℝ, soninScaledAnnulusBump m δ x *
        ccmActualHeadExteriorCosineMeasureGauge ν x)| ≤
        |∫ x : ℝ, soninScaledAnnulusBump m δ x *
          ccmActualHeadExteriorCosineMeasureGauge μ x| +
        |∫ x : ℝ, soninScaledAnnulusBump m δ x *
          ccmActualHeadExteriorCosineMeasureGauge ν x| := abs_sub _ _
    _ ≤ (4 * δ * soninRefTailSup (δ * H₀)) * μ.real Set.univ +
        (4 * δ * soninRefTailSup (δ * H₀)) * ν.real Set.univ :=
      add_le_add
        (abs_integral_soninScaledAnnulusBump_mul_exteriorCosineMeasureGauge_le
          m δ H₀ hδ hH₀ μ hμ)
        (abs_integral_soninScaledAnnulusBump_mul_exteriorCosineMeasureGauge_le
          m δ H₀ hδ hH₀ ν hν)
    _ = _ := by ring

theorem exteriorCosineMeasureGauge_mass_lower_bound_of_constant_approximation
    (m δ H₀ ε : ℝ) (hδ : 0 < δ) (hH₀ : 0 ≤ H₀) (hε : 0 ≤ ε)
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ h : ℝ ∂μ, H₀ ≤ h) (hν : ∀ᵐ h : ℝ ∂ν, H₀ ≤ h)
    (happrox : ∀ x : ℝ, soninScaledAnnulusBump m δ x ≠ 0 →
      |1 - (ccmActualHeadExteriorCosineMeasureGauge μ x -
        ccmActualHeadExteriorCosineMeasureGauge ν x)| ≤ ε) :
    (1 - ε) * (∫ y : ℝ, soninUnitBumpData y) ≤
      2 * soninRefTailSup (δ * H₀) *
        (μ.real Set.univ + ν.real Set.univ) := by
  let φ : ℝ → ℝ := soninScaledAnnulusBump m δ
  let G : ℝ → ℝ := fun x =>
    ccmActualHeadExteriorCosineMeasureGauge μ x -
      ccmActualHeadExteriorCosineMeasureGauge ν x
  have hφ : Integrable φ := integrable_soninScaledAnnulusBump m δ hδ
  have hμint :=
    integrable_soninScaledAnnulusBump_mul_exteriorCosineMeasureGauge m δ hδ μ
  have hνint :=
    integrable_soninScaledAnnulusBump_mul_exteriorCosineMeasureGauge m δ hδ ν
  have hφG : Integrable (fun x => φ x * G x) := by
    apply (hμint.sub hνint).congr
    filter_upwards with x
    simp only [Pi.sub_apply]
    dsimp only [φ, G]
    ring
  have herrInt : Integrable (fun x => φ x * (1 - G x)) := by
    have hbase : Integrable (fun x => φ x - φ x * G x) := by
      apply (hφ.sub hφG).congr
      filter_upwards with x
      rfl
    apply hbase.congr
    filter_upwards with x
    dsimp only [φ, G]
    ring
  have hmajor : Integrable (fun x => ε * φ x) := hφ.const_mul ε
  have herr := MeasureTheory.norm_integral_le_of_norm_le
    (f := fun x => φ x * (1 - G x)) (g := fun x => ε * φ x) hmajor
    (Filter.Eventually.of_forall fun x => by
      dsimp only [φ, G]
      by_cases hx : soninScaledAnnulusBump m δ x = 0
      · simp only [hx, zero_mul, norm_zero, mul_zero]
        exact le_rfl
      · rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (soninScaledAnnulusBump_nonneg m δ x)]
        simpa only [mul_comm] using
          (mul_le_mul_of_nonneg_left (happrox x hx)
            (soninScaledAnnulusBump_nonneg m δ x)))
  have herr' : |∫ x : ℝ, φ x * (1 - G x)| ≤
      ε * ∫ x : ℝ, φ x := by
    simpa only [Real.norm_eq_abs, MeasureTheory.integral_const_mul] using herr
  have hdecomp :
      (∫ x : ℝ, φ x * (1 - G x)) + (∫ x : ℝ, φ x * G x) =
        ∫ x : ℝ, φ x := by
    rw [← integral_add herrInt hφG]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring
  have htriangle : |∫ x : ℝ, φ x| ≤
      |∫ x : ℝ, φ x * (1 - G x)| + |∫ x : ℝ, φ x * G x| := by
    rw [← hdecomp]
    exact abs_add_le _ _
  have hupper :=
    abs_integral_soninScaledAnnulusBump_mul_exteriorCosineGauge_sub_le
      m δ H₀ hδ hH₀ μ ν hμ hν
  have hmass := integral_soninUnitBumpData_pos
  have hφmass : ∫ x : ℝ, φ x =
      2 * δ * ∫ y : ℝ, soninUnitBumpData y := by
    exact integral_soninScaledAnnulusBump_eq m δ hδ
  dsimp only [φ, G] at hupper hφmass
  rw [hφmass, abs_of_pos (by positivity :
    0 < 2 * δ * ∫ y : ℝ, soninUnitBumpData y)] at htriangle
  have hS := soninRefTailSup_nonneg (δ * H₀)
  have hμmass : 0 ≤ μ.real Set.univ := measureReal_nonneg
  have hνmass : 0 ≤ ν.real Set.univ := measureReal_nonneg
  nlinarith

/-- A nonnegative vanishing factor cannot carry a fixed positive product floor without the other
factor diverging. -/
theorem tendsto_atTop_of_nonneg_vanishing_mul_lower
    {S M : ℕ → ℝ} {A : ℝ} (hA : 0 < A)
    (hS0 : ∀ n, 0 ≤ S n)
    (hS : Tendsto S atTop (𝓝 0))
    (hlower : ∀ n, A ≤ 2 * S n * M n) :
    Tendsto M atTop atTop := by
  rw [tendsto_atTop]
  intro B
  let C : ℝ := |B| + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hradius : 0 < A / (2 * C) := div_pos hA (by positivity)
  have hevent := hS.eventually (Metric.ball_mem_nhds 0 hradius)
  filter_upwards [hevent] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hS0 n)] at hn
  have hSC : 2 * S n * C < A := by
    have := (lt_div_iff₀ (by positivity : 0 < 2 * C)).mp hn
    nlinarith
  by_contra hnot
  push Not at hnot
  have hBC : B < C := by
    dsimp only [C]
    linarith [le_abs_self B]
  have hMC : M n < C := hnot.trans hBC
  have hSM : 2 * S n * M n ≤ 2 * S n * C := by
    exact mul_le_mul_of_nonneg_left hMC.le (mul_nonneg (by norm_num) (hS0 n))
  linarith [hlower n]

/-- **Universal exterior-measure mass wall.**  Fixed-error approximation of the constant mode on
expanding compact Sonin windows by arbitrary signed finite measures carried by a fixed positive
exterior half-line forces combined Jordan mass to infinity. -/
theorem tendsto_exteriorCosineMeasureGauge_mass_atTop_of_constant_approximation
    {H₀ ε : ℝ} (hH₀ : 0 < H₀) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (μ ν : ℕ → FiniteMeasure ℝ)
    (hμ : ∀ N : ℕ, ∀ᵐ h : ℝ ∂(μ N : Measure ℝ), H₀ ≤ h)
    (hν : ∀ N : ℕ, ∀ᵐ h : ℝ ∂(ν N : Measure ℝ), H₀ ≤ h)
    (happrox : ∀ N : ℕ, ∀ x : ℝ,
      soninScaledAnnulusBump 0 ((N + 1 : ℕ) : ℝ) x ≠ 0 →
        |1 - (ccmActualHeadExteriorCosineMeasureGauge (μ N : Measure ℝ) x -
          ccmActualHeadExteriorCosineMeasureGauge (ν N : Measure ℝ) x)| ≤ ε) :
    Tendsto (fun N : ℕ =>
      (μ N : Measure ℝ).real Set.univ + (ν N : Measure ℝ).real Set.univ)
      atTop atTop := by
  let S : ℕ → ℝ := fun N =>
    soninRefTailSup (((N + 1 : ℕ) : ℝ) * H₀)
  let M : ℕ → ℝ := fun N =>
    (μ N : Measure ℝ).real Set.univ + (ν N : Measure ℝ).real Set.univ
  let A : ℝ := (1 - ε) * ∫ y : ℝ, soninUnitBumpData y
  have hA : 0 < A := by
    dsimp only [A]
    exact mul_pos (sub_pos.mpr hε1) integral_soninUnitBumpData_pos
  have hS0 : ∀ N, 0 ≤ S N := fun N => by
    dsimp only [S]
    exact soninRefTailSup_nonneg _
  have hwidth : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop := by
    have hadd : Tendsto (fun N : ℕ => N + 1) atTop atTop := by
      simpa only [Nat.add_comm] using tendsto_add_atTop_nat 1
    exact tendsto_natCast_atTop_atTop.comp hadd
  have harg : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) * H₀) atTop atTop :=
    hwidth.atTop_mul_const hH₀
  have hS : Tendsto S atTop (𝓝 0) := by
    exact tendsto_soninRefTailSup_atTop.comp harg
  have hlower : ∀ N, A ≤ 2 * S N * M N := by
    intro N
    have hδ : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    simpa only [A, S, M] using
      exteriorCosineMeasureGauge_mass_lower_bound_of_constant_approximation
        0 ((N + 1 : ℕ) : ℝ) H₀ ε hδ hH₀.le hε0
        (μ N : Measure ℝ) (ν N : Measure ℝ) (hμ N) (hν N) (happrox N)
  exact tendsto_atTop_of_nonneg_vanishing_mul_lower hA hS0 hS hlower

/-- **Superpolynomial universal mass wall.**  Under the same fixed-error expanding-window
approximation, combined Jordan mass divided by any fixed power of scaled window width still tends
to infinity. -/
theorem tendsto_exteriorCosineMeasureGauge_mass_div_pow_atTop_of_constant_approximation
    {H₀ ε : ℝ} (hH₀ : 0 < H₀) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (μ ν : ℕ → FiniteMeasure ℝ)
    (hμ : ∀ N : ℕ, ∀ᵐ h : ℝ ∂(μ N : Measure ℝ), H₀ ≤ h)
    (hν : ∀ N : ℕ, ∀ᵐ h : ℝ ∂(ν N : Measure ℝ), H₀ ≤ h)
    (happrox : ∀ N : ℕ, ∀ x : ℝ,
      soninScaledAnnulusBump 0 ((N + 1 : ℕ) : ℝ) x ≠ 0 →
        |1 - (ccmActualHeadExteriorCosineMeasureGauge (μ N : Measure ℝ) x -
          ccmActualHeadExteriorCosineMeasureGauge (ν N : Measure ℝ) x)| ≤ ε)
    (p : ℕ) :
    Tendsto (fun N : ℕ =>
      ((μ N : Measure ℝ).real Set.univ + (ν N : Measure ℝ).real Set.univ) /
        ((((N + 1 : ℕ) : ℝ) * H₀) ^ p)) atTop atTop := by
  let u : ℕ → ℝ := fun N => ((N + 1 : ℕ) : ℝ) * H₀
  let S : ℕ → ℝ := fun N => u N ^ p * soninRefTailSup (u N)
  let M : ℕ → ℝ := fun N =>
    ((μ N : Measure ℝ).real Set.univ + (ν N : Measure ℝ).real Set.univ) / (u N ^ p)
  let A : ℝ := (1 - ε) * ∫ y : ℝ, soninUnitBumpData y
  have hA : 0 < A := by
    dsimp only [A]
    exact mul_pos (sub_pos.mpr hε1) integral_soninUnitBumpData_pos
  have hwidth : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop := by
    have hadd : Tendsto (fun N : ℕ => N + 1) atTop atTop := by
      simpa only [Nat.add_comm] using tendsto_add_atTop_nat 1
    exact tendsto_natCast_atTop_atTop.comp hadd
  have huTop : Tendsto u atTop atTop := by
    exact hwidth.atTop_mul_const hH₀
  have hS : Tendsto S atTop (𝓝 0) := by
    exact (tendsto_pow_mul_soninRefTailSup_atTop p).comp huTop
  have hu0 : ∀ N, 0 < u N := fun N => by
    dsimp only [u]
    positivity
  have hS0 : ∀ N, 0 ≤ S N := fun N => by
    dsimp only [S]
    exact mul_nonneg (pow_nonneg (hu0 N).le p) (soninRefTailSup_nonneg _)
  have hlower : ∀ N, A ≤ 2 * S N * M N := by
    intro N
    have hbase :=
      exteriorCosineMeasureGauge_mass_lower_bound_of_constant_approximation
        0 ((N + 1 : ℕ) : ℝ) H₀ ε (by positivity) hH₀.le hε0
        (μ N : Measure ℝ) (ν N : Measure ℝ) (hμ N) (hν N) (happrox N)
    have hupow : u N ^ p ≠ 0 := pow_ne_zero p (hu0 N).ne'
    dsimp only [A, S, M]
    change A ≤ 2 * (u N ^ p * soninRefTailSup (u N)) *
      (((μ N : Measure ℝ).real Set.univ + (ν N : Measure ℝ).real Set.univ) /
        u N ^ p)
    rw [show u N = ((N + 1 : ℕ) : ℝ) * H₀ by rfl]
    convert hbase using 1
    all_goals field_simp [hupow]
  exact tendsto_atTop_of_nonneg_vanishing_mul_lower hA hS0 hS hlower


end RHTower
