import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheInsertionConeOfExponentiallyConvexAmplitudes
import GaloisForLFunctions.SelbergClass.MultipleStandardTwistDamping
import GaloisForLFunctions.RHTower.SatoTateMoment

/-!
# The torus walls of prime insertion

Let `a` be an amplitude on multi-indices `k : Fin n → ℕ` (for instance `a_k = f(x + Σ k_i log p_i)`), and let

`S_a(θ) = Σ_k a_k Π_i U_{k_i}(cos θ_i)`

be the torus sum of `n` prime insertions at free phases. Against the product of Sato–Tate measures the characters
`Π_i U_{k_i}` are orthonormal (`integral_torusSum_mul_chiProd`), so `S_a` has the amplitude as its Fourier coefficients. A
nonnegative `S_a` therefore pairs nonnegatively with every square of a polynomial in the characters.

* **The Hecke–Bessel inequality** (`hecke_level_one`, `sq_sum_le_hecke`). If `S_a ≥ 0` on the torus then
  `(Σ_i c_i a_{e_i})² ≤ a_0 (Σ_i c_i² (a_0 + a_{2e_i}) + Σ_{i≠j} c_i c_j a_{e_i+e_j})`.
* **The log-concavity wall** (`sum_sq_le_of_logConcave`). If `a_0 a_{e_i+e_j} ≤ ρ a_{e_i} a_{e_j}` with `ρ < 1`, then torus
  positivity forces `Σ_i a_{e_i}² ≤ a_0²/(1 − ρ)`. A log-concave amplitude leaves the torus cone at a finite prime set.
* **The size floor** (`torusSum_ge_of_geometric`). If `|a_k| ≤ a_0 Π r_i^{k_i}` then `S_a ≥ a_0 (2 − Π (1 − r_i)^{−2})`, so a
  decaying amplitude stays in the cone while `Π_i (1 − r_i)^{−2} ≤ 2`.

The two bounds locate the largest prime set `S*` of torus-uniform positivity from the ratios `f(x + log p)/f(x)` alone.
-/

open Filter Topology MeasureTheory Set
open scoped Real ENNReal

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open GaloisForLFunctions.CompletedArithmeticForms (cosSum cosSum_add_two cosSum_eq_chebyshev)

noncomputable section

/-! ### The Sato–Tate measure -/

/-- The Sato–Tate density on `(0, π)`. -/
def satoTateDensity (θ : ℝ) : ℝ := 2 / π * Real.sin θ ^ 2

theorem satoTateDensity_nonneg (θ : ℝ) : 0 ≤ satoTateDensity θ := by
  unfold satoTateDensity
  positivity

theorem measurable_satoTateDensity : Measurable satoTateDensity := by
  unfold satoTateDensity
  fun_prop

/-- The Sato–Tate measure. -/
def satoTate : Measure ℝ :=
  (volume.restrict (Ioc 0 π)).withDensity fun θ => ENNReal.ofReal (satoTateDensity θ)

theorem integral_satoTate (g : ℝ → ℝ) :
    ∫ θ, g θ ∂satoTate = ∫ θ in (0 : ℝ)..π, g θ * satoTateDensity θ := by
  rw [satoTate, integral_withDensity_eq_integral_toReal_smul₀
    measurable_satoTateDensity.ennreal_ofReal.aemeasurable
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    intervalIntegral.integral_of_le Real.pi_pos.le]
  refine integral_congr_ae (ae_of_all _ fun θ => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (satoTateDensity_nonneg θ)]
  ring

/-- Orthonormality of the characters. -/
theorem integral_cosSum_mul_cosSum (j k : ℕ) :
    ∫ θ, cosSum θ j * cosSum θ k ∂satoTate = if j = k then 1 else 0 := by
  rw [integral_satoTate]
  simp only [cosSum_eq_chebyshev, satoTateDensity]
  exact GaloisForLFunctions.satoTate_orthonormal j k

theorem cosSum_zero (θ : ℝ) : cosSum θ 0 = 1 := by simp [cosSum]

instance : IsProbabilityMeasure satoTate := by
  constructor
  have h := integral_cosSum_mul_cosSum 0 0
  simp only [cosSum_zero, mul_one, if_true, integral_const, smul_eq_mul] at h
  have hm : (satoTate univ).toReal = 1 := by
    simpa [Measure.real] using h
  have hne : satoTate univ ≠ ∞ := by
    intro htop
    rw [htop] at hm
    simp at hm
  rw [← ENNReal.ofReal_toReal hne, hm, ENNReal.ofReal_one]

theorem continuous_cosSum (k : ℕ) : Continuous fun θ => cosSum θ k := by
  unfold cosSum
  fun_prop

theorem measurable_cosSum (k : ℕ) : Measurable fun θ => cosSum θ k :=
  (continuous_cosSum k).measurable

/-! ### The characters of the torus -/

variable {n : ℕ}

/-- `Π_i U_{k_i}(cos θ_i)`. -/
def chiProd (θ : Fin n → ℝ) (k : Fin n → ℕ) : ℝ := ∏ i, cosSum (θ i) (k i)

/-- The size of a character. -/
def chiSize (k : Fin n → ℕ) : ℝ := ∏ i, ((k i : ℝ) + 1)

theorem chiSize_nonneg (k : Fin n → ℕ) : 0 ≤ chiSize k :=
  Finset.prod_nonneg fun _ _ => by positivity

theorem abs_chiProd_le (θ : Fin n → ℝ) (k : Fin n → ℕ) : |chiProd θ k| ≤ chiSize k := by
  rw [chiProd, chiSize, Finset.abs_prod]
  exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => abs_cosSum_le _ _

theorem continuous_chiProd (k : Fin n → ℕ) : Continuous fun θ : Fin n → ℝ => chiProd θ k := by
  unfold chiProd
  refine continuous_finsetProd _ fun i _ => ?_
  exact (continuous_cosSum (k i)).comp (continuous_apply i)

/-- The trace-summable amplitudes. -/
def TraceSummable (a : (Fin n → ℕ) → ℝ) : Prop := Summable fun k => |a k| * chiSize k

/-- The torus sum of an amplitude. -/
def torusSum (a : (Fin n → ℕ) → ℝ) (θ : Fin n → ℝ) : ℝ := ∑' k, a k * chiProd θ k

variable {a : (Fin n → ℕ) → ℝ}

theorem summable_term (ha : TraceSummable a) (θ : Fin n → ℝ) :
    Summable fun k => a k * chiProd θ k := by
  refine Summable.of_norm_bounded ha fun k => ?_
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (abs_chiProd_le θ k) (abs_nonneg _)

theorem continuous_torusSum (ha : TraceSummable a) : Continuous (torusSum a) := by
  refine continuous_tsum (fun k => continuous_const.mul (continuous_chiProd k)) ha fun k θ => ?_
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (abs_chiProd_le θ k) (abs_nonneg _)

theorem abs_torusSum_le (ha : TraceSummable a) (θ : Fin n → ℝ) :
    |torusSum a θ| ≤ ∑' k, |a k| * chiSize k := by
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm (summable_term ha θ).norm).trans ?_
  refine (summable_term ha θ).norm.tsum_le_tsum (fun k => ?_) ha
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (abs_chiProd_le θ k) (abs_nonneg _)

/-- The product of Sato–Tate measures. -/
def torusMeasure (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi fun _ => satoTate

instance : IsProbabilityMeasure (torusMeasure n) := by
  unfold torusMeasure
  infer_instance

/-- Orthonormality on the torus. -/
theorem integral_chiProd_mul_chiProd (k m : Fin n → ℕ) :
    ∫ θ, chiProd θ k * chiProd θ m ∂(torusMeasure n) = if k = m then 1 else 0 := by
  have e : (fun θ : Fin n → ℝ => chiProd θ k * chiProd θ m) =
      fun θ => ∏ i, (cosSum (θ i) (k i) * cosSum (θ i) (m i)) := by
    funext θ
    rw [chiProd, chiProd, Finset.prod_mul_distrib]
  rw [e, torusMeasure, integral_fintype_prod_eq_prod
    (f := fun i (t : ℝ) => cosSum t (k i) * cosSum t (m i))]
  simp only [integral_cosSum_mul_cosSum]
  by_cases h : k = m
  · subst h
    simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem integrable_of_bounded_continuous {g : (Fin n → ℝ) → ℝ} (hg : Continuous g) {C : ℝ}
    (hC : ∀ θ, |g θ| ≤ C) : Integrable g (torusMeasure n) :=
  Integrable.of_bound hg.aestronglyMeasurable C (ae_of_all _ fun θ => by
    rw [Real.norm_eq_abs]; exact hC θ)

/-- **The amplitude is the Fourier coefficient of the torus sum.** -/
theorem integral_torusSum_mul_chiProd (ha : TraceSummable a) (m : Fin n → ℕ) :
    ∫ θ, torusSum a θ * chiProd θ m ∂(torusMeasure n) = a m := by
  have hF : ∀ k, Integrable (fun θ => a k * chiProd θ k * chiProd θ m) (torusMeasure n) := fun k =>
    integrable_of_bounded_continuous (C := |a k| * chiSize k * chiSize m)
      ((continuous_const.mul (continuous_chiProd k)).mul (continuous_chiProd m)) fun θ => by
        rw [abs_mul, abs_mul]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (abs_chiProd_le θ k) (abs_nonneg _))
          (abs_chiProd_le θ m) (abs_nonneg _) (mul_nonneg (abs_nonneg _) (chiSize_nonneg k))
  have hsum : Summable fun k => ∫ θ, ‖a k * chiProd θ k * chiProd θ m‖ ∂(torusMeasure n) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _)
      (fun k => ?_) (ha.mul_right (chiSize m))
    have hb : ∀ θ, ‖a k * chiProd θ k * chiProd θ m‖ ≤ |a k| * chiSize k * chiSize m := fun θ => by
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (abs_chiProd_le θ k) (abs_nonneg _))
        (abs_chiProd_le θ m) (abs_nonneg _) (mul_nonneg (abs_nonneg _) (chiSize_nonneg k))
    calc ∫ θ, ‖a k * chiProd θ k * chiProd θ m‖ ∂(torusMeasure n)
        ≤ ∫ _ : Fin n → ℝ, |a k| * chiSize k * chiSize m ∂(torusMeasure n) :=
          integral_mono (hF k).norm (integrable_const _) hb
      _ = _ := by simp
  have hs := hasSum_integral_of_summable_integral_norm hF hsum
  have e1 : ∀ θ, ∑' k, a k * chiProd θ k * chiProd θ m = torusSum a θ * chiProd θ m := fun θ => by
    rw [torusSum, tsum_mul_right]
  simp_rw [e1] at hs
  have e2 : ∀ k, ∫ θ, a k * chiProd θ k * chiProd θ m ∂(torusMeasure n) = if k = m then a k else 0 := by
    intro k
    simp_rw [mul_assoc]
    rw [integral_const_mul, integral_chiProd_mul_chiProd]
    split_ifs <;> simp
  simp_rw [e2] at hs
  have hsingle : HasSum (fun k => if k = m then a k else 0) (a m) := by
    have := hasSum_ite_eq m (a m)
    convert this using 2 with k
    split_ifs with h
    · rw [h]
    · rfl
  exact hs.unique hsingle

/-! ### Level one -/

/-- The unit multi-index. -/
def unitIdx (i : Fin n) : Fin n → ℕ := Pi.single i 1

theorem chiProd_zero (θ : Fin n → ℝ) : chiProd θ (0 : Fin n → ℕ) = 1 := by
  simp [chiProd, cosSum_zero]

theorem chiProd_of_support {θ : Fin n → ℝ} (m : Fin n → ℕ) (s : Finset (Fin n))
    (hs : ∀ i, i ∉ s → m i = 0) : chiProd θ m = ∏ i ∈ s, cosSum (θ i) (m i) := by
  rw [chiProd]
  refine (Finset.prod_subset (Finset.subset_univ s) fun i _ hi => ?_).symm
  rw [hs i hi, cosSum_zero]

/-- `U_1(cos θ)² = U_2(cos θ) + 1`. -/
theorem cosSum_one_sq (θ : ℝ) : cosSum θ 1 * cosSum θ 1 = cosSum θ 2 + 1 := by
  have h2 := cosSum_add_two θ 0
  have h1 : cosSum θ 1 = 2 * Real.cos θ := by
    simp only [cosSum, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Real.cos_neg]
    ring
  simp only [zero_add] at h2
  rw [h2, cosSum_zero, h1]
  ring

theorem chiProd_unit (θ : Fin n → ℝ) (i : Fin n) : chiProd θ (unitIdx i) = cosSum (θ i) 1 := by
  rw [chiProd_of_support (unitIdx i) {i} (fun j hj => by
    simp only [unitIdx, Pi.single_apply, Finset.mem_singleton] at hj ⊢
    exact if_neg hj)]
  simp [unitIdx]

theorem chiProd_two_unit (θ : Fin n → ℝ) (i : Fin n) :
    chiProd θ (unitIdx i + unitIdx i) = cosSum (θ i) 2 := by
  rw [chiProd_of_support (unitIdx i + unitIdx i) {i} (fun j hj => by
    simp only [unitIdx, Pi.add_apply, Pi.single_apply, Finset.mem_singleton] at hj ⊢
    simp [hj])]
  simp [unitIdx]

theorem chiProd_unit_add_unit (θ : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) :
    chiProd θ (unitIdx i + unitIdx j) = cosSum (θ i) 1 * cosSum (θ j) 1 := by
  rw [chiProd_of_support (unitIdx i + unitIdx j) {i, j} (fun l hl => by
    simp only [unitIdx, Pi.add_apply, Pi.single_apply, Finset.mem_insert, Finset.mem_singleton,
      not_or] at hl ⊢
    simp [hl.1, hl.2]), Finset.prod_pair hij]
  simp [unitIdx, hij, hij.symm]

/-- The form of the Hecke operators at level one. -/
def heckeOne (a : (Fin n → ℕ) → ℝ) (c₀ : ℝ) (c : Fin n → ℝ) : ℝ :=
  c₀ ^ 2 * a 0 + 2 * c₀ * ∑ i, c i * a (unitIdx i) +
    ∑ i, c i ^ 2 * (a 0 + a (unitIdx i + unitIdx i)) +
      ∑ i, ∑ j ∈ Finset.univ.erase i, c i * c j * a (unitIdx i + unitIdx j)

/-- **The Hecke form at level one is nonnegative on the torus cone.** -/
theorem hecke_level_one (ha : TraceSummable a) (hpos : ∀ θ, 0 ≤ torusSum a θ) (c₀ : ℝ)
    (c : Fin n → ℝ) : 0 ≤ heckeOne a c₀ c := by
  set X : Fin n → (Fin n → ℝ) → ℝ := fun i θ => cosSum (θ i) 1 with hX
  -- the square of a linear polynomial expanded in the characters
  have hexp : ∀ θ : Fin n → ℝ, (c₀ + ∑ i, c i * X i θ) ^ 2 =
      c₀ ^ 2 * chiProd θ 0 + 2 * c₀ * ∑ i, c i * chiProd θ (unitIdx i) +
        ∑ i, c i ^ 2 * (chiProd θ 0 + chiProd θ (unitIdx i + unitIdx i)) +
          ∑ i, ∑ j ∈ Finset.univ.erase i, c i * c j * chiProd θ (unitIdx i + unitIdx j) := by
    intro θ
    have hsq : (∑ i, c i * X i θ) ^ 2 = ∑ i, ∑ j, c i * c j * (X i θ * X j θ) := by
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have hsplit : ∀ i, ∑ j, c i * c j * (X i θ * X j θ) = c i ^ 2 * (X i θ * X i θ) +
        ∑ j ∈ Finset.univ.erase i, c i * c j * (X i θ * X j θ) := by
      intro i
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      ring
    have hA : ∑ i, c i * X i θ = ∑ i, c i * chiProd θ (unitIdx i) := by
      simp only [chiProd_unit, hX]
    have hB : ∑ i, c i ^ 2 * (X i θ * X i θ) =
        ∑ i, c i ^ 2 * (1 + chiProd θ (unitIdx i + unitIdx i)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [chiProd_two_unit, hX]
      simp only
      rw [cosSum_one_sq]
      ring
    have hC : ∑ i, ∑ j ∈ Finset.univ.erase i, c i * c j * (X i θ * X j θ) =
        ∑ i, ∑ j ∈ Finset.univ.erase i, c i * c j * chiProd θ (unitIdx i + unitIdx j) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
      rw [chiProd_unit_add_unit θ (Finset.ne_of_mem_erase hj).symm]
    have hYY : (∑ i, c i * X i θ) ^ 2 = ∑ i, c i ^ 2 * (1 + chiProd θ (unitIdx i + unitIdx i)) +
        ∑ i, ∑ j ∈ Finset.univ.erase i, c i * c j * chiProd θ (unitIdx i + unitIdx j) := by
      rw [hsq, Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib, hB, hC]
    calc (c₀ + ∑ i, c i * X i θ) ^ 2
        = c₀ ^ 2 + 2 * c₀ * ∑ i, c i * X i θ + (∑ i, c i * X i θ) ^ 2 := by ring
      _ = _ := by rw [hYY, hA, chiProd_zero]; ring
  -- integrate against the torus sum
  have hSc := continuous_torusSum ha
  have hSb := abs_torusSum_le ha
  have hI : ∀ m : Fin n → ℕ, Integrable (fun θ => torusSum a θ * chiProd θ m) (torusMeasure n) := fun m =>
    integrable_of_bounded_continuous (C := (∑' k, |a k| * chiSize k) * chiSize m)
      (hSc.mul (continuous_chiProd m)) fun θ => by
        rw [abs_mul]
        exact mul_le_mul (hSb θ) (abs_chiProd_le θ m) (abs_nonneg _)
          (tsum_nonneg fun _ => mul_nonneg (abs_nonneg _) (chiSize_nonneg _))
  have hM := integral_torusSum_mul_chiProd ha
  have hval : ∫ θ, torusSum a θ * (c₀ + ∑ i, c i * X i θ) ^ 2 ∂(torusMeasure n) = heckeOne a c₀ c := by
    have e : ∀ θ, torusSum a θ * (c₀ + ∑ i, c i * X i θ) ^ 2 =
        c₀ ^ 2 * (torusSum a θ * chiProd θ 0) +
          2 * c₀ * ∑ i, c i * (torusSum a θ * chiProd θ (unitIdx i)) +
          ∑ i, c i ^ 2 * (torusSum a θ * chiProd θ 0 +
            torusSum a θ * chiProd θ (unitIdx i + unitIdx i)) +
          ∑ i, ∑ j ∈ Finset.univ.erase i, c i * c j *
            (torusSum a θ * chiProd θ (unitIdx i + unitIdx j)) := by
      intro θ
      rw [hexp θ]
      simp only [mul_add, Finset.mul_sum]
      have e1 : ∀ i, torusSum a θ * (2 * c₀ * (c i * chiProd θ (unitIdx i))) =
          2 * c₀ * (c i * (torusSum a θ * chiProd θ (unitIdx i))) := fun i => by ring
      have e2 : ∀ i, torusSum a θ * (c i ^ 2 * chiProd θ 0) =
          c i ^ 2 * (torusSum a θ * chiProd θ 0) := fun i => by ring
      have e3 : ∀ i, torusSum a θ * (c i ^ 2 * chiProd θ (unitIdx i + unitIdx i)) =
          c i ^ 2 * (torusSum a θ * chiProd θ (unitIdx i + unitIdx i)) := fun i => by ring
      have e4 : ∀ i j, torusSum a θ * (c i * c j * chiProd θ (unitIdx i + unitIdx j)) =
          c i * c j * (torusSum a θ * chiProd θ (unitIdx i + unitIdx j)) := fun i j => by ring
      simp only [e1, e2, e3, e4]
      ring
    simp_rw [e]
    have i1 : Integrable (fun θ => c₀ ^ 2 * (torusSum a θ * chiProd θ 0)) (torusMeasure n) :=
      (hI 0).const_mul (c₀ ^ 2)
    have hi2 : ∀ i, Integrable (fun θ => c i * (torusSum a θ * chiProd θ (unitIdx i)))
        (torusMeasure n) := fun i => (hI (unitIdx i)).const_mul (c i)
    have i2 : Integrable (fun θ => 2 * c₀ * ∑ i, c i * (torusSum a θ * chiProd θ (unitIdx i)))
        (torusMeasure n) := (integrable_finsetSum _ fun i _ => hi2 i).const_mul _
    have hi0 : ∀ i, Integrable (fun θ => torusSum a θ * chiProd θ 0 +
        torusSum a θ * chiProd θ (unitIdx i + unitIdx i)) (torusMeasure n) := fun i =>
      (hI 0).add (hI (unitIdx i + unitIdx i))
    have hi3 : ∀ i, Integrable (fun θ => c i ^ 2 * (torusSum a θ * chiProd θ 0 +
        torusSum a θ * chiProd θ (unitIdx i + unitIdx i))) (torusMeasure n) := fun i =>
      (hi0 i).const_mul _
    have i3 : Integrable (fun θ => ∑ i, c i ^ 2 * (torusSum a θ * chiProd θ 0 +
        torusSum a θ * chiProd θ (unitIdx i + unitIdx i))) (torusMeasure n) :=
      integrable_finsetSum _ fun i _ => hi3 i
    have hi4 : ∀ i j, Integrable (fun θ => c i * c j *
        (torusSum a θ * chiProd θ (unitIdx i + unitIdx j))) (torusMeasure n) := fun i j =>
      (hI (unitIdx i + unitIdx j)).const_mul _
    have hi5 : ∀ i, Integrable (fun θ => ∑ j ∈ Finset.univ.erase i, c i * c j *
        (torusSum a θ * chiProd θ (unitIdx i + unitIdx j))) (torusMeasure n) := fun i =>
      integrable_finsetSum _ fun j _ => hi4 i j
    have i4 : Integrable (fun θ => ∑ i, ∑ j ∈ Finset.univ.erase i, c i * c j *
        (torusSum a θ * chiProd θ (unitIdx i + unitIdx j))) (torusMeasure n) :=
      integrable_finsetSum _ fun i _ => hi5 i
    have i12 : Integrable (fun θ => c₀ ^ 2 * (torusSum a θ * chiProd θ 0) +
        2 * c₀ * ∑ i, c i * (torusSum a θ * chiProd θ (unitIdx i))) (torusMeasure n) := i1.add i2
    have i123 : Integrable (fun θ => c₀ ^ 2 * (torusSum a θ * chiProd θ 0) +
        2 * c₀ * ∑ i, c i * (torusSum a θ * chiProd θ (unitIdx i)) +
        ∑ i, c i ^ 2 * (torusSum a θ * chiProd θ 0 +
        torusSum a θ * chiProd θ (unitIdx i + unitIdx i))) (torusMeasure n) := i12.add i3
    rw [integral_add i123 i4, integral_add i12 i3, integral_add i1 i2, integral_const_mul, hM,
      integral_const_mul, integral_finsetSum _ fun i _ => hi2 i,
      integral_finsetSum _ fun i _ => hi3 i, integral_finsetSum _ fun i _ => hi5 i, heckeOne]
    have s1 : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        ∫ θ, c i * (torusSum a θ * chiProd θ (unitIdx i)) ∂(torusMeasure n) = c i * a (unitIdx i) :=
      fun i _ => by rw [integral_const_mul, hM]
    have s2 : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        ∫ θ, c i ^ 2 * (torusSum a θ * chiProd θ 0 +
          torusSum a θ * chiProd θ (unitIdx i + unitIdx i)) ∂(torusMeasure n) =
        c i ^ 2 * (a 0 + a (unitIdx i + unitIdx i)) := fun i _ => by
      rw [integral_const_mul, integral_add (hI 0) (hI _), hM, hM]
    have s3 : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        ∫ θ, ∑ j ∈ Finset.univ.erase i, c i * c j *
          (torusSum a θ * chiProd θ (unitIdx i + unitIdx j)) ∂(torusMeasure n) =
        ∑ j ∈ Finset.univ.erase i, c i * c j * a (unitIdx i + unitIdx j) := fun i _ => by
      rw [integral_finsetSum _ fun j _ => hi4 i j]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, hM]
    rw [Finset.sum_congr rfl s1, Finset.sum_congr rfl s2, Finset.sum_congr rfl s3]
  rw [← hval]
  exact integral_nonneg fun θ => mul_nonneg (hpos θ) (sq_nonneg _)

/-! ### The walls -/

/-- **The Hecke–Bessel inequality.** -/
theorem sq_sum_le_hecke (ha : TraceSummable a) (hpos : ∀ θ, 0 ≤ torusSum a θ) (h0 : 0 < a 0)
    (c : Fin n → ℝ) :
    (∑ i, c i * a (unitIdx i)) ^ 2 ≤
      a 0 * (∑ i, c i ^ 2 * (a 0 + a (unitIdx i + unitIdx i)) +
        ∑ i, ∑ j ∈ Finset.univ.erase i, c i * c j * a (unitIdx i + unitIdx j)) := by
  set B := ∑ i, c i * a (unitIdx i) with hB
  set C := ∑ i, c i ^ 2 * (a 0 + a (unitIdx i + unitIdx i)) +
    ∑ i, ∑ j ∈ Finset.univ.erase i, c i * c j * a (unitIdx i + unitIdx j) with hC
  have h := hecke_level_one ha hpos (-B / a 0) c
  have e : heckeOne a (-B / a 0) c = C - B ^ 2 / a 0 := by
    rw [heckeOne, ← hB, hC]
    field_simp
    ring
  rw [e, sub_nonneg, div_le_iff₀ h0] at h
  linarith

/-- **The log-concavity wall.** A torus-positive amplitude with `a_0 a_{e_i+e_j} ≤ ρ a_{e_i} a_{e_j}`, `ρ < 1`, satisfies
`Σ_i a_{e_i}² ≤ a_0²/(1 − ρ)`. -/
theorem sum_sq_le_of_logConcave (ha : TraceSummable a) (hpos : ∀ θ, 0 ≤ torusSum a θ) (h0 : 0 < a 0)
    (hnn : ∀ i, 0 ≤ a (unitIdx i)) {ρ : ℝ}
    (hconc : ∀ i j, a 0 * a (unitIdx i + unitIdx j) ≤ ρ * (a (unitIdx i) * a (unitIdx j))) :
    (∑ i, a (unitIdx i) ^ 2) * (1 - ρ) ≤ a 0 ^ 2 := by
  set Ssq := ∑ i, a (unitIdx i) ^ 2 with hS
  have hS0 : 0 ≤ Ssq := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h := sq_sum_le_hecke ha hpos h0 (fun i => a (unitIdx i))
  have e1 : ∑ i, a (unitIdx i) * a (unitIdx i) = Ssq := by
    simp only [hS, sq]
  rw [e1] at h
  have e2 : a 0 * (∑ i, a (unitIdx i) ^ 2 * (a 0 + a (unitIdx i + unitIdx i)) +
      ∑ i, ∑ j ∈ Finset.univ.erase i, a (unitIdx i) * a (unitIdx j) * a (unitIdx i + unitIdx j)) =
      a 0 ^ 2 * Ssq + ∑ i, ∑ j, a (unitIdx i) * a (unitIdx j) *
        (a 0 * a (unitIdx i + unitIdx j)) := by
    have hsplit : ∀ i, ∑ j, a (unitIdx i) * a (unitIdx j) * (a 0 * a (unitIdx i + unitIdx j)) =
        a (unitIdx i) ^ 2 * (a 0 * a (unitIdx i + unitIdx i)) +
          ∑ j ∈ Finset.univ.erase i, a (unitIdx i) * a (unitIdx j) *
            (a 0 * a (unitIdx i + unitIdx j)) := by
      intro i
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib, mul_add, Finset.mul_sum,
      Finset.mul_sum, hS, Finset.mul_sum]
    have e3 : ∀ i, a 0 * (a (unitIdx i) ^ 2 * (a 0 + a (unitIdx i + unitIdx i))) =
        a 0 ^ 2 * a (unitIdx i) ^ 2 + a (unitIdx i) ^ 2 * (a 0 * a (unitIdx i + unitIdx i)) :=
      fun i => by ring
    have e4 : ∀ i, a 0 * ∑ j ∈ Finset.univ.erase i, a (unitIdx i) * a (unitIdx j) *
        a (unitIdx i + unitIdx j) = ∑ j ∈ Finset.univ.erase i, a (unitIdx i) * a (unitIdx j) *
        (a 0 * a (unitIdx i + unitIdx j)) := fun i => by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [e3, e4, Finset.sum_add_distrib]
    ring
  rw [e2] at h
  have hdbl : ∑ i, ∑ j, a (unitIdx i) * a (unitIdx j) * (a 0 * a (unitIdx i + unitIdx j)) ≤
      ρ * Ssq ^ 2 := by
    have hsq : Ssq ^ 2 = ∑ i, ∑ j, a (unitIdx i) ^ 2 * a (unitIdx j) ^ 2 := by
      rw [sq, hS, Finset.sum_mul_sum]
    rw [hsq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 := mul_le_mul_of_nonneg_left (hconc i j) (mul_nonneg (hnn i) (hnn j))
    calc a (unitIdx i) * a (unitIdx j) * (a 0 * a (unitIdx i + unitIdx j))
        ≤ a (unitIdx i) * a (unitIdx j) * (ρ * (a (unitIdx i) * a (unitIdx j))) := h1
      _ = _ := by ring
  rcases hS0.eq_or_lt with hzero | hposS
  · rw [← hzero]
    simp only [zero_mul]
    positivity
  · have hfin : Ssq * Ssq ≤ a 0 ^ 2 * Ssq + ρ * Ssq ^ 2 := by
      have : Ssq ^ 2 = Ssq * Ssq := sq _
      linarith
    have hmul : Ssq * (Ssq * (1 - ρ)) ≤ Ssq * a 0 ^ 2 := by nlinarith
    exact le_of_mul_le_mul_left hmul hposS

/-- Multi-indices of length `n + 1` are pairs. -/
def consEquiv (n : ℕ) : (Fin (n + 1) → ℕ) ≃ ℕ × (Fin n → ℕ) where
  toFun k := (k 0, Fin.tail k)
  invFun x := Fin.cons x.1 x.2
  left_inv k := Fin.cons_self_tail k
  right_inv x := by simp

/-- A product of series over multi-indices. -/
theorem hasSum_pi_prod {n : ℕ} (g : Fin n → ℕ → ℝ) (s : Fin n → ℝ) (hg : ∀ i k, 0 ≤ g i k)
    (hs : ∀ i, HasSum (g i) (s i)) :
    HasSum (fun k : Fin n → ℕ => ∏ i, g i (k i)) (∏ i, s i) := by
  induction n with
  | zero =>
    haveI : Unique (Fin 0 → ℕ) := Pi.uniqueOfIsEmpty _
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact hasSum_single default fun b hb => absurd (Subsingleton.elim b default) hb
  | succ n ih =>
    have hih : HasSum (fun k : Fin n → ℕ => ∏ i : Fin n, g i.succ (k i)) (∏ i : Fin n, s i.succ) :=
      ih (fun i : Fin n => g i.succ) (fun i => s i.succ) (fun i k => hg i.succ k)
        (fun i => hs i.succ)
    have hsm := Summable.mul_of_nonneg (hs 0).summable hih.summable (fun k => hg 0 k)
        (fun k => Finset.prod_nonneg fun (i : Fin n) _ => hg i.succ _)
    have hmul := HasSum.mul (hs 0) hih hsm
    have h2 := (consEquiv n).hasSum_iff.mpr hmul
    have e1 : (fun k : Fin (n + 1) → ℕ => ∏ i, g i (k i)) =
        (fun x : ℕ × (Fin n → ℕ) => g 0 x.1 * ∏ i : Fin n, g i.succ (x.2 i)) ∘ (consEquiv n) := by
      funext k
      simp only [Function.comp_apply, Fin.prod_univ_succ, consEquiv, Equiv.coe_fn_mk, Fin.tail]
    rw [e1, Fin.prod_univ_succ]
    exact h2

/-- `Σ_k (k + 1) r^k = (1 − r)^{−2}`. -/
theorem hasSum_succ_mul_pow {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    HasSum (fun k : ℕ => ((k : ℝ) + 1) * r ^ k) (((1 - r) ^ 2)⁻¹) := by
  have hn : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg h0]
  have h2 := (hasSum_coe_mul_geometric_of_norm_lt_one hn).add (hasSum_geometric_of_lt_one h0 h1)
  have e : (fun k : ℕ => ((k : ℝ) + 1) * r ^ k) = fun b : ℕ => (b : ℝ) * r ^ b + r ^ b := by
    funext k
    ring
  have hd : 1 - r ≠ 0 := by linarith
  have eV : ((1 - r) ^ 2)⁻¹ = r / (1 - r) ^ 2 + (1 - r)⁻¹ := by
    field_simp
    ring
  rw [e, eV]
  exact h2

/-- **The size floor.** If `|a_k| ≤ a_0 Π r_i^{k_i}`, then `S_a(θ) ≥ a_0 (2 − Π (1 − r_i)^{−2})`. -/
theorem torusSum_ge_of_geometric {r : Fin n → ℝ} (hr0 : ∀ i, 0 ≤ r i)
    (hr1 : ∀ i, r i < 1) (hgeo : ∀ k, |a k| ≤ a 0 * ∏ i, r i ^ k i) (θ : Fin n → ℝ) :
    a 0 * (2 - ∏ i, ((1 - r i) ^ 2)⁻¹) ≤ torusSum a θ := by
  have hG := hasSum_pi_prod (fun i k => ((k : ℝ) + 1) * r i ^ k) (fun i => ((1 - r i) ^ 2)⁻¹)
    (fun i k => by have := hr0 i; positivity) (fun i => hasSum_succ_mul_pow (hr0 i) (hr1 i))
  set G : (Fin n → ℕ) → ℝ := fun k => ∏ i, (((k i : ℕ) : ℝ) + 1) * r i ^ k i with hGd
  set D : ℝ := ∏ i, ((1 - r i) ^ 2)⁻¹ with hD
  have hbound : ∀ k, |a k| * chiSize k ≤ a 0 * G k := fun k => by
    have e : G k = chiSize k * ∏ i, r i ^ k i := by
      simp only [hGd, chiSize, Finset.prod_mul_distrib]
    rw [e]
    calc |a k| * chiSize k ≤ (a 0 * ∏ i, r i ^ k i) * chiSize k :=
          mul_le_mul_of_nonneg_right (hgeo k) (chiSize_nonneg k)
      _ = _ := by ring
  have ha : TraceSummable a :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (chiSize_nonneg k)) hbound
      (hG.summable.mul_left _)
  have hG0 : G 0 = 1 := by simp [hGd]
  have hsum := (summable_term ha θ).hasSum
  have hh := (hG.mul_left (a 0)).add hsum
  have hnn : ∀ k, 0 ≤ a 0 * G k + a k * chiProd θ k := fun k => by
    have h1 := abs_chiProd_le θ k
    have h2 : |a k * chiProd θ k| ≤ a 0 * G k := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)).trans (hbound k)
    linarith [neg_abs_le (a k * chiProd θ k)]
  have hle := sum_le_hasSum ({0} : Finset (Fin n → ℕ)) (fun k _ => hnn k) hh
  rw [Finset.sum_singleton, hG0, chiProd_zero] at hle
  change _ ≤ a 0 * D + torusSum a θ at hle
  nlinarith

/-- A size certificate: `Π (1 − r_i)^{−2} ≤ 2` keeps the amplitude in the torus cone. -/
theorem torusSum_nonneg_of_geometric (h0 : 0 ≤ a 0) {r : Fin n → ℝ} (hr0 : ∀ i, 0 ≤ r i)
    (hr1 : ∀ i, r i < 1) (hgeo : ∀ k, |a k| ≤ a 0 * ∏ i, r i ^ k i)
    (hD : ∏ i, ((1 - r i) ^ 2)⁻¹ ≤ 2) (θ : Fin n → ℝ) : 0 ≤ torusSum a θ :=
  le_trans (mul_nonneg h0 (by linarith)) (torusSum_ge_of_geometric hr0 hr1 hgeo θ)

/-! ### Amplitudes on a set of primes -/

/-- The amplitude `a_k = f(x + Σ k_i ℓ_i)` of steps `ℓ` at the base point `x`. -/
def ampl (f : ℝ → ℝ) (ℓ : Fin n → ℝ) (x : ℝ) (k : Fin n → ℕ) : ℝ := f (x + ∑ i, (k i : ℝ) * ℓ i)

variable {x₀ κ : ℝ} {f : ℝ → ℝ}

theorem abs_ampl_le {C : ℝ} (hC : ∀ x, x₀ ≤ x → |f x| ≤ C * Real.exp (-κ * x)) {ℓ : Fin n → ℝ}
    (hℓ : ∀ i, 0 ≤ ℓ i) {x : ℝ} (hx : x₀ ≤ x) (k : Fin n → ℕ) :
    |ampl f ℓ x k| ≤ C * Real.exp (-κ * x) * ∏ i, Real.exp (-(κ * ℓ i)) ^ k i := by
  have hs : 0 ≤ ∑ i, (k i : ℝ) * ℓ i := Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hℓ i)
  have h := hC _ (show x₀ ≤ x + ∑ i, (k i : ℝ) * ℓ i by linarith)
  have e : Real.exp (-κ * (x + ∑ i, (k i : ℝ) * ℓ i)) =
      Real.exp (-κ * x) * ∏ i, Real.exp (-(κ * ℓ i)) ^ k i := by
    simp_rw [← Real.exp_nat_mul]
    rw [← Real.exp_sum, ← Real.exp_add]
    congr 1
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [ampl, mul_assoc, ← e]
  exact h

theorem traceSummable_ampl (hκ : 0 < κ) {C : ℝ} (hC : ∀ x, x₀ ≤ x → |f x| ≤ C * Real.exp (-κ * x))
    {ℓ : Fin n → ℝ} (hℓ : ∀ i, 0 < ℓ i) {x : ℝ} (hx : x₀ ≤ x) : TraceSummable (ampl f ℓ x) := by
  have hq : ∀ i, Real.exp (-(κ * ℓ i)) < 1 := fun i => exp_neg_lt_one (mul_pos hκ (hℓ i))
  have hG := hasSum_pi_prod (fun i k => ((k : ℝ) + 1) * Real.exp (-(κ * ℓ i)) ^ k)
    (fun i => ((1 - Real.exp (-(κ * ℓ i))) ^ 2)⁻¹) (fun i k => by positivity)
    (fun i => hasSum_succ_mul_pow (Real.exp_pos _).le (hq i))
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (chiSize_nonneg k))
    (fun k => ?_) (hG.summable.mul_left (C * Real.exp (-κ * x)))
  have h1 := abs_ampl_le hC (fun i => (hℓ i).le) hx k
  have e : ∏ i, (((k i : ℕ) : ℝ) + 1) * Real.exp (-(κ * ℓ i)) ^ k i =
      chiSize k * ∏ i, Real.exp (-(κ * ℓ i)) ^ k i := by
    simp only [chiSize, Finset.prod_mul_distrib]
  rw [e]
  calc |ampl f ℓ x k| * chiSize k
      ≤ (C * Real.exp (-κ * x) * ∏ i, Real.exp (-(κ * ℓ i)) ^ k i) * chiSize k :=
        mul_le_mul_of_nonneg_right h1 (chiSize_nonneg k)
    _ = _ := by ring

/-- A series over multi-indices of length `n + 1`, first index apart. -/
theorem tsum_cons {n : ℕ} {F : (Fin (n + 1) → ℕ) → ℝ} (hs : Summable F) :
    ∑' k, F k = ∑' k₀ : ℕ, ∑' m : Fin n → ℕ, F (Fin.cons k₀ m) := by
  have hs' : Summable fun c : ℕ × (Fin n → ℕ) => F (Fin.cons c.1 c.2) :=
    (consEquiv n).symm.summable_iff.mpr hs
  have heq : ∑' c : ℕ × (Fin n → ℕ), F (Fin.cons c.1 c.2) = ∑' k, F k :=
    (consEquiv n).symm.tsum_eq F
  rw [← heq]
  exact hs'.tsum_prod

theorem ampl_cons {n : ℕ} (f : ℝ → ℝ) (ℓ : Fin (n + 1) → ℝ) (x : ℝ) (k₀ : ℕ) (m : Fin n → ℕ) :
    ampl f ℓ x (Fin.cons k₀ m) = ampl f (Fin.tail ℓ) (x + k₀ * ℓ 0) m := by
  have e : ∑ i, ((Fin.cons k₀ m : Fin (n + 1) → ℕ) i : ℝ) * ℓ i =
      (k₀ : ℝ) * ℓ 0 + ∑ i : Fin n, (m i : ℝ) * Fin.tail ℓ i := by
    rw [Fin.sum_univ_succ]
    rfl
  rw [ampl, ampl, e, add_assoc]

theorem chiProd_cons {n : ℕ} (θ : Fin (n + 1) → ℝ) (k₀ : ℕ) (m : Fin n → ℕ) :
    chiProd θ (Fin.cons k₀ m) = cosSum (θ 0) k₀ * chiProd (Fin.tail θ) m := by
  rw [chiProd, Fin.prod_univ_succ]
  rfl

/-- The torus sum is the composite of the insertions, prime by prime. -/
theorem torusSum_cons (hκ : 0 < κ) {C : ℝ} (hC : ∀ x, x₀ ≤ x → |f x| ≤ C * Real.exp (-κ * x))
    {n : ℕ} {ℓ : Fin (n + 1) → ℝ} (hℓ : ∀ i, 0 < ℓ i) {x : ℝ} (hx : x₀ ≤ x) (θ : Fin (n + 1) → ℝ) :
    torusSum (ampl f ℓ x) θ = insertion (θ 0) (ℓ 0)
      (fun y => torusSum (ampl f (Fin.tail ℓ) y) (Fin.tail θ)) x := by
  rw [torusSum, tsum_cons (summable_term (traceSummable_ampl hκ hC hℓ hx) θ), insertion]
  refine tsum_congr fun k => ?_
  rw [torusSum, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [ampl_cons, chiProd_cons]
  ring

theorem IsExpConvexFrom.congr_on {g : ℝ → ℝ} (hf : IsExpConvexFrom x₀ f)
    (he : ∀ x, x₀ ≤ x → g x = f x) : IsExpConvexFrom x₀ g := by
  intro ι S t c ht
  have h := hf ι S t c ht
  have e : ∑ i ∈ S, ∑ j ∈ S, c i * (starRingEnd ℂ) (c j) * (g (x₀ + t i + t j) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, c i * (starRingEnd ℂ) (c j) * (f (x₀ + t i + t j) : ℂ) := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    rw [he _ (by linarith [ht i hi, ht j hj])]
  rwa [e]

theorem ExpDecayFrom.congr_on {g : ℝ → ℝ} (hf : ExpDecayFrom x₀ κ f)
    (he : ∀ x, x₀ ≤ x → g x = f x) : ExpDecayFrom x₀ κ g := by
  obtain ⟨C, hC0, hC⟩ := hf
  exact ⟨C, hC0, fun x hx => by rw [he x hx]; exact hC x hx⟩

/-- **The cone is torus-positive.** An exponentially convex amplitude of exponential decay has
nonnegative torus sum at every base point, for every set of steps and every phase. -/
theorem IsExpConvexFrom.torusSum (hκ : 0 < κ) (hf : IsExpConvexFrom x₀ f) (hd : ExpDecayFrom x₀ κ f)
    {n : ℕ} {ℓ : Fin n → ℝ} (hℓ : ∀ i, 0 < ℓ i) (θ : Fin n → ℝ) :
    IsExpConvexFrom x₀ (fun y => GaloisForLFunctions.ArithmeticInnerFunctionTheory.torusSum
        (ampl f ℓ y) θ) ∧
      ExpDecayFrom x₀ κ (fun y => GaloisForLFunctions.ArithmeticInnerFunctionTheory.torusSum
        (ampl f ℓ y) θ) := by
  obtain ⟨C, hC0, hC⟩ := id hd
  induction n with
  | zero =>
    have e : ∀ y, GaloisForLFunctions.ArithmeticInnerFunctionTheory.torusSum (ampl f ℓ y) θ = f y := by
      intro y
      haveI : Unique (Fin 0 → ℕ) := Pi.uniqueOfIsEmpty _
      rw [GaloisForLFunctions.ArithmeticInnerFunctionTheory.torusSum, tsum_fintype]
      simp [ampl, chiProd]
    exact ⟨hf.congr_on fun y _ => e y, hd.congr_on fun y _ => e y⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (ℓ := Fin.tail ℓ) (fun i => hℓ i.succ) (Fin.tail θ)
    have e : ∀ y, x₀ ≤ y → GaloisForLFunctions.ArithmeticInnerFunctionTheory.torusSum (ampl f ℓ y) θ =
        GaloisForLFunctions.ArithmeticInnerFunctionTheory.insertion (θ 0) (ℓ 0)
          (fun y => GaloisForLFunctions.ArithmeticInnerFunctionTheory.torusSum
          (ampl f (Fin.tail ℓ) y) (Fin.tail θ)) y := fun y hy => torusSum_cons hκ hC hℓ hy θ
    exact ⟨(IsExpConvexFrom.insertion hκ (hℓ 0) h1 h2 (θ 0)).congr_on e,
      (ExpDecayFrom.insertion hκ (hℓ 0) h2 (θ 0)).congr_on e⟩

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
