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
  refine continuous_finset_prod _ fun i _ => ?_
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
  have hs := hasSum_integral_of_summable_norm hF hsum
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
  simp [unitIdx, Pi.single_apply, hij, hij.symm]

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
    rw [add_sq, hsq, Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib, chiProd_zero]
    have hA : 2 * c₀ * ∑ i, c i * X i θ = 2 * c₀ * ∑ i, c i * chiProd θ (unitIdx i) := by
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
    rw [hB, hC]
    ring_nf
    rw [mul_comm c₀, mul_assoc] at hA
    sorry
  sorry

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
