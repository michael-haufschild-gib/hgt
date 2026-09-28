import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SocleMomentGenerating

/-!
# The zeta-Gibbs law on the full absolute-convergence chamber

The abelian zeta gas `P_{σ,τ}(A) = Z(σ,τ)⁻¹ |A|^{-σ} |soc A|^{-τ}`, `Z(σ,τ) = ∏_{j≥1} ζ(jσ + τ)`,
is a probability law on the whole chamber `Θ = {σ > 0, σ + τ > 1}`, including negative socle
fugacity `τ`.  It is realized as the exponential socle tilt of the corpus law at the base point
`(σ, max τ 0)`, whose tilt normalizer is the socle moment generating function.

On `Θ` the socle moment generating function is `E_{σ,τ} e^{-zQ} = C_{σ,τ}(z)`, and fugacity
translation `V_u` is the normalized socle intervention `dP_{σ,τ+u}/dP_{σ,τ} = C_{σ,τ}(u)⁻¹ e^{-uQ}`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.AbelianZetaGas

/-- `(AZC.2)`  A point of the absolute-convergence chamber `σ > 0`, `σ + τ > 1`. -/
structure GasChamber where
  sigma : ℝ
  tau : ℝ
  sigma_pos : 0 < sigma
  firstDepth : 1 < sigma + tau

namespace GasChamber

variable (c : GasChamber)

/-- The corpus base point `(σ, max τ 0)`. -/
def base : AbelianZetaConvergentParameters where
  sigma := c.sigma
  tau := max c.tau 0
  sigma_pos := c.sigma_pos
  tau_nonneg := le_max_right _ _
  firstDepth := by linarith [le_max_left c.tau 0, c.firstDepth]

@[simp] theorem base_sigma : c.base.sigma = c.sigma := rfl

@[simp] theorem base_tau : c.base.tau = max c.tau 0 := rfl

/-- The tilt `s = τ - max τ 0 ≤ 0` leading from the base point to the chamber point. -/
def shift : ℝ := c.tau - max c.tau 0

theorem base_tau_add_shift : c.base.tau + c.shift = c.tau := by
  simp only [base_tau, shift]
  ring

theorem integrable_base_tilt :
    Integrable (fun A => Real.exp (-c.shift * socleLog A))
      (classLaw c.base.toAbelianZetaParameters) :=
  integrable_classLaw_exp_socle c.base (by
    have := c.base_tau_add_shift
    simp only [base_sigma] at *
    linarith [c.firstDepth])

/-- The tilt normalizer `M = E_{σ,τ₀} e^{-sQ}`. -/
def normalizer : ℝ :=
  ∫ A, Real.exp (-c.shift * socleLog A) ∂classLaw c.base.toAbelianZetaParameters

theorem normalizer_pos : 0 < c.normalizer :=
  integral_exp_pos c.integrable_base_tilt

/-- The tilt normalizer is the socle moment generating function at the base point. -/
theorem normalizer_eq : (c.normalizer : ℂ) = socleResponse c.sigma c.base.tau c.shift := by
  have h := integral_classLaw_cexp_socle c.base (z := (c.shift : ℂ)) (by
    have := c.base_tau_add_shift
    simp only [base_sigma, Complex.ofReal_re] at *
    linarith [c.firstDepth])
  rw [base_sigma] at h
  rw [← h, normalizer, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun A => ?_)
  simp only [Complex.ofReal_exp]
  push_cast
  ring_nf

/-- `(AZC.3)`  The zeta-Gibbs law `P_{σ,τ}` on the chamber. -/
def law : Measure AbelianZetaGroupClass :=
  (classLaw c.base.toAbelianZetaParameters).withDensity fun A =>
    ENNReal.ofReal (Real.exp (-c.shift * socleLog A) / c.normalizer)

theorem law_apply (s : Set AbelianZetaGroupClass) :
    c.law s = ∫⁻ A in s, ENNReal.ofReal (Real.exp (-c.shift * socleLog A) / c.normalizer)
      ∂classLaw c.base.toAbelianZetaParameters :=
  withDensity_apply _ trivial

instance isProbabilityMeasure_law : IsProbabilityMeasure c.law := by
  constructor
  rw [law_apply, Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal
    (c.integrable_base_tilt.div_const _)
    (Eventually.of_forall fun _ => div_nonneg (Real.exp_pos _).le c.normalizer_pos.le),
    integral_div, show (∫ A, Real.exp (-c.shift * socleLog A)
      ∂classLaw c.base.toAbelianZetaParameters) = c.normalizer from rfl,
    div_self c.normalizer_pos.ne', ENNReal.ofReal_one]

theorem integral_law {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : AbelianZetaGroupClass → E) :
    ∫ A, f A ∂c.law = ∫ A, (Real.exp (-c.shift * socleLog A) / c.normalizer) • f A
      ∂classLaw c.base.toAbelianZetaParameters := by
  rw [law, integral_withDensity_eq_integral_toReal_smul measurable_from_top
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun A => ?_)
  simp only
  rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le c.normalizer_pos.le)]

/-- `(AZC.12)`  **Socle moment generating function on the chamber.**
`E_{σ,τ} e^{-zQ} = C_{σ,τ}(z) = ∏_{j≥1} ζ(jσ + τ + z)/ζ(jσ + τ)` for `σ + τ + Re z > 1`. -/
theorem integral_law_cexp_socle {z : ℂ} (hz : 1 < c.sigma + c.tau + z.re) :
    ∫ A, Complex.exp (-z * socleLog A) ∂c.law = socleResponse c.sigma c.tau z := by
  have hbase := integral_classLaw_cexp_socle c.base (z := (c.shift : ℂ) + z) (by
    have := c.base_tau_add_shift
    simp only [base_sigma, Complex.add_re, Complex.ofReal_re] at *
    linarith)
  have hsplit : ∀ A : AbelianZetaGroupClass,
      (Real.exp (-c.shift * socleLog A) / c.normalizer) • Complex.exp (-z * socleLog A) =
        (c.normalizer : ℂ)⁻¹ * Complex.exp (-((c.shift : ℂ) + z) * socleLog A) := by
    intro A
    rw [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_exp, div_eq_inv_mul, mul_assoc,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [integral_law, integral_congr_ae (Eventually.of_forall hsplit), integral_const_mul, hbase,
    normalizer_eq]
  have hb := c.base.firstDepth
  simp only [base_sigma, base_tau] at hb
  have hL : socleLadder c.sigma ((max c.tau 0 : ℝ) : ℂ) ≠ 0 :=
    socleLadder_ne_zero_of_mem c.sigma_pos
      (by simp only [socleChamber, Set.mem_setOf_eq, Complex.ofReal_re]; linarith)
  have hLt : socleLadder c.sigma (c.tau : ℂ) ≠ 0 :=
    socleLadder_ne_zero_of_mem c.sigma_pos
      (by simp only [socleChamber, Set.mem_setOf_eq, Complex.ofReal_re]; linarith [c.firstDepth])
  have htau : ((max c.tau 0 : ℝ) : ℂ) + (c.shift : ℂ) = (c.tau : ℂ) := by
    have h := c.base_tau_add_shift
    rw [base_tau] at h
    rw [← Complex.ofReal_add, h]
  simp only [socleResponse, base_sigma, base_tau]
  rw [← add_assoc, htau]
  field_simp

/-! ## The atoms of the chamber law -/

/-- The two-observable Gibbs weight `|A|^{-σ} |soc A|^{-τ}`. -/
def weight (A : AbelianZetaGroupClass) : ℝ :=
  (A.order : ℝ) ^ (-c.sigma) * (A.socleOrder : ℝ) ^ (-c.tau)

theorem weight_pos (A : AbelianZetaGroupClass) : 0 < c.weight A := by
  have hord : (0 : ℝ) < (A.order : ℝ) := by exact_mod_cast A.order_pos
  have hsoc : (0 : ℝ) < (A.socleOrder : ℝ) := by exact_mod_cast A.socleOrder_pos
  exact mul_pos (Real.rpow_pos_of_pos hord _) (Real.rpow_pos_of_pos hsoc _)

theorem exp_socleLog_mul_socle_rpow (x y : ℝ) (A : AbelianZetaGroupClass) :
    Real.exp (-x * socleLog A) * (A.socleOrder : ℝ) ^ (-y) = (A.socleOrder : ℝ) ^ (-(y + x)) := by
  have hsoc : (0 : ℝ) < (A.socleOrder : ℝ) := by exact_mod_cast A.socleOrder_pos
  rw [socleLog, Real.rpow_def_of_pos hsoc, Real.rpow_def_of_pos hsoc, ← Real.exp_add]
  congr 1
  ring

theorem zetaPartition_base : c.base.zetaPartition = socleLadder c.sigma c.base.tau := by
  rw [AbelianZetaConvergentParameters.zetaPartition, socleLadder_eq_tprod]
  congr 1
  funext n
  congr 1
  push_cast
  rfl

theorem ofReal_toReal_classLaw_base (A : AbelianZetaGroupClass) :
    (((classLaw c.base.toAbelianZetaParameters {A}).toReal : ℝ) : ℂ) =
      (socleLadder c.sigma c.base.tau)⁻¹ *
        ((abelianZetaTwoObservableWeight c.base.toAbelianZetaParameters A : ℝ) : ℂ) := by
  have hw : 0 ≤ abelianZetaTwoObservableWeight c.base.toAbelianZetaParameters A := by
    have hord : (0 : ℝ) < (A.order : ℝ) := by exact_mod_cast A.order_pos
    have hsoc : (0 : ℝ) < (A.socleOrder : ℝ) := by exact_mod_cast A.socleOrder_pos
    exact (mul_pos (Real.rpow_pos_of_pos hord _) (Real.rpow_pos_of_pos hsoc _)).le
  rw [classLaw_singleton, c.base.classMass_eq_ennNormalizer_mul_twoObservableWeight,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hw, AbelianZetaConvergentParameters.ennNormalizer,
    ENNReal.coe_toReal]
  push_cast
  rw [c.base.coe_nnNormalizer_eq_complexNormalizer,
    c.base.complexNormalizer_eq_zetaPartition_inv, zetaPartition_base]

theorem law_singleton (A : AbelianZetaGroupClass) :
    c.law {A} = ENNReal.ofReal (Real.exp (-c.shift * socleLog A) / c.normalizer) *
      classLaw c.base.toAbelianZetaParameters {A} := by
  rw [law_apply, lintegral_singleton]

theorem law_singleton_pos (A : AbelianZetaGroupClass) : 0 < c.law {A} := by
  rw [law_singleton]
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (div_pos (Real.exp_pos _) c.normalizer_pos)).ne'
    (by rw [classLaw_singleton]; exact (classMass_pos c.base A).ne')

/-- `(AZC.3)`  **The chamber atoms.**  `P_{σ,τ}(A) · ∏_{j≥1} ζ(jσ + τ) = |A|^{-σ} |soc A|^{-τ}`. -/
theorem ofReal_toReal_law_mul_socleLadder (A : AbelianZetaGroupClass) :
    (((c.law {A}).toReal : ℝ) : ℂ) * socleLadder c.sigma c.tau = ((c.weight A : ℝ) : ℂ) := by
  have hb := c.base.firstDepth
  simp only [base_sigma, base_tau] at hb
  have hL : socleLadder c.sigma ((max c.tau 0 : ℝ) : ℂ) ≠ 0 :=
    socleLadder_ne_zero_of_mem c.sigma_pos
      (by simp only [socleChamber, Set.mem_setOf_eq, Complex.ofReal_re]; linarith)
  have htau : ((max c.tau 0 : ℝ) : ℂ) + (c.shift : ℂ) = (c.tau : ℂ) := by
    have h := c.base_tau_add_shift
    rw [base_tau] at h
    rw [← Complex.ofReal_add, h]
  have hM := c.normalizer_eq
  simp only [socleResponse, base_tau] at hM
  rw [htau] at hM
  have hMne : (c.normalizer : ℂ) ≠ 0 := by exact_mod_cast c.normalizer_pos.ne'
  rw [law_singleton, ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (div_nonneg (Real.exp_pos _).le c.normalizer_pos.le)]
  push_cast
  rw [ofReal_toReal_classLaw_base, base_tau]
  have hLt : socleLadder c.sigma (c.tau : ℂ) = (c.normalizer : ℂ) *
      socleLadder c.sigma ((max c.tau 0 : ℝ) : ℂ) := by
    rw [hM]
    field_simp
  rw [hLt, weight, abelianZetaTwoObservableWeight]
  have hw := exp_socleLog_mul_socle_rpow c.shift (max c.tau 0) A
  have hsum : max c.tau 0 + c.shift = c.tau := by
    have h := c.base_tau_add_shift
    rwa [base_tau] at h
  rw [hsum] at hw
  simp only [base_sigma, base_tau]
  rw [← hw]
  push_cast
  field_simp

/-- `(AZC.3)`  The chamber partition function `Z(σ,τ) = ∏_{j≥1} ζ(jσ + τ)`. -/
def partition : ℝ := (socleLadder c.sigma c.tau).re

theorem weight_zero : c.weight 0 = 1 := by
  simp [weight, AbelianZetaGroupClass.order, AbelianZetaGroupClass.socleOrder]

theorem ofReal_partition : (c.partition : ℂ) = socleLadder c.sigma c.tau := by
  have h := c.ofReal_toReal_law_mul_socleLadder 0
  rw [c.weight_zero, Complex.ofReal_one] at h
  have ht : ((c.law {0}).toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos (c.law_singleton_pos 0).ne'
      (measure_ne_top _ _)).ne'
  have hL : socleLadder c.sigma c.tau = (((c.law {0}).toReal)⁻¹ : ℝ) := by
    push_cast
    field_simp
    rw [mul_comm]
    exact h
  rw [partition, hL, Complex.ofReal_re]

theorem partition_pos : 0 < c.partition := by
  have h := c.ofReal_toReal_law_mul_socleLadder 0
  rw [c.weight_zero, ← c.ofReal_partition] at h
  have h' : (c.law {0}).toReal * c.partition = 1 := by exact_mod_cast h
  have ht : 0 < (c.law {0}).toReal :=
    ENNReal.toReal_pos (c.law_singleton_pos 0).ne' (measure_ne_top _ _)
  nlinarith

/-- `(AZC.3)`  **Exact chamber atoms.**  `P_{σ,τ}(A) = |A|^{-σ} |soc A|^{-τ} / Z(σ,τ)`. -/
theorem toReal_law_singleton (A : AbelianZetaGroupClass) :
    (c.law {A}).toReal = c.weight A / c.partition := by
  have h := c.ofReal_toReal_law_mul_socleLadder A
  rw [← c.ofReal_partition] at h
  have h' : (c.law {A}).toReal * c.partition = c.weight A := by exact_mod_cast h
  rw [eq_div_iff c.partition_pos.ne']
  exact h'

/-- The chamber law extends the corpus law: for `τ ≥ 0` it is the corpus zeta-Gibbs law. -/
theorem law_eq_classLaw (hτ : 0 ≤ c.tau) : c.law = classLaw c.base.toAbelianZetaParameters := by
  have hs : c.shift = 0 := by simp [shift, max_eq_left hτ]
  have hM : c.normalizer = 1 := by
    simp [normalizer, hs]
  rw [law]
  conv_rhs => rw [← withDensity_one (μ := classLaw c.base.toAbelianZetaParameters)]
  congr 1
  funext A
  simp [hs, hM]

theorem socleLog_zero : socleLog 0 = 0 := by
  simp [socleLog, AbelianZetaGroupClass.socleOrder]

/-- The socle observable is not almost surely constant under any chamber law. -/
theorem not_ae_const_socleLog : ¬ ∃ k : ℝ, ∀ᵐ A ∂c.law, socleLog A = k := by
  rintro ⟨k, hk⟩
  set p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
  set A1 : AbelianZetaGroupClass := Finsupp.single (p2, 0) 1
  have hA1 : socleLog A1 = Real.log 2 := by
    simp [socleLog, A1, AbelianZetaGroupClass.socleOrder, p2]
  have hat : ∀ A, socleLog A = k := fun A => by
    by_contra hne
    have hnull : c.law {A} = 0 := measure_mono_null (fun B hB => by
      rw [Set.mem_singleton_iff] at hB
      rw [hB]
      exact hne) (ae_iff.mp hk)
    exact (c.law_singleton_pos A).ne' hnull
  have h0 := hat 0
  have h1 := hat A1
  rw [socleLog_zero] at h0
  rw [hA1, ← h0] at h1
  exact absurd h1 (Real.log_pos one_lt_two).ne'

/-! ## Fugacity translation -/

/-- `(AZC.6)`  The fugacity translate `V_u(σ, τ) = (σ, τ + u)`. -/
def translate (u : ℝ) (hu : 1 < c.sigma + c.tau + u) : GasChamber :=
  ⟨c.sigma, c.tau + u, c.sigma_pos, by linarith⟩

theorem weight_translate (u : ℝ) (hu : 1 < c.sigma + c.tau + u) (A : AbelianZetaGroupClass) :
    (c.translate u hu).weight A = Real.exp (-u * socleLog A) * c.weight A := by
  simp only [weight, translate]
  rw [mul_left_comm, exp_socleLog_mul_socle_rpow]

/-- The response `C_{σ,τ}(u) = Z(σ, τ+u)/Z(σ,τ)` is real on real translations. -/
theorem ofReal_partition_div (u : ℝ) (hu : 1 < c.sigma + c.tau + u) :
    (((c.translate u hu).partition / c.partition : ℝ) : ℂ) = socleResponse c.sigma c.tau u := by
  rw [Complex.ofReal_div, ofReal_partition, ofReal_partition, socleResponse]
  simp only [translate]
  push_cast
  rfl

/-- `(AZC.13)`  **Exact intervention law.**  `dP_{σ,τ+u}/dP_{σ,τ} = C_{σ,τ}(u)⁻¹ e^{-uQ}`. -/
theorem translate_law (u : ℝ) (hu : 1 < c.sigma + c.tau + u) :
    (c.translate u hu).law = c.law.withDensity fun A =>
      ENNReal.ofReal (Real.exp (-u * socleLog A) /
        ((c.translate u hu).partition / c.partition)) := by
  refine Measure.ext_of_singleton fun A => ?_
  rw [withDensity_apply _ (MeasurableSet.singleton A), lintegral_singleton]
  have hpos := (c.translate u hu).partition_pos
  have hpos' := c.partition_pos
  rw [← ENNReal.ofReal_toReal (measure_ne_top (c.translate u hu).law {A}),
    ← ENNReal.ofReal_toReal (measure_ne_top c.law {A}), ← ENNReal.ofReal_mul (by positivity),
    toReal_law_singleton, toReal_law_singleton, weight_translate]
  congr 1
  field_simp

/-- `(AZC.13)`, Radon–Nikodym form. -/
theorem rnDeriv_translate_law (u : ℝ) (hu : 1 < c.sigma + c.tau + u) :
    (c.translate u hu).law.rnDeriv c.law =ᵐ[c.law] fun A =>
      ENNReal.ofReal (Real.exp (-u * socleLog A) /
        ((c.translate u hu).partition / c.partition)) := by
  rw [translate_law]
  exact Measure.rnDeriv_withDensity _ measurable_from_top

end GasChamber

end GaloisForLFunctions.HTGeometry.AbelianZetaGas
