import GaloisForLFunctions.RHTower.GaussianPolynomialTailAsymptotic
import GaloisForLFunctions.RHTower.HermiteEvenCarrier

/-!
# Sharp truncation tails for the normalized Hermite trial family

The squared aperture error of the step-four Hermite vectors is exactly a two-sided
polynomial--Gaussian tail.  Reflection reduces it to twice the one-sided tail, so the sharp
polynomial asymptotics give the exact leading constants.  This recovers the full Gaussian exponent
`exp (-2*pi*a^(2 : ℕ))` without the exponent loss incurred by a crude polynomial envelope.
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace RHTower

/-- An even integrable density has twice its right-tail mass outside a symmetric interval. -/
theorem integral_compl_Icc_eq_two_mul_integral_Ioi_of_even
    {f : ℝ → ℝ} (hf : Integrable f) (heven : ∀ x, f (-x) = f x)
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ x in (Icc (-a) a)ᶜ, f x) = 2 * ∫ x in Ioi a, f x := by
  have hsplit : (Icc (-a) a)ᶜ = Iio (-a) ∪ Ioi a := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi,
      not_and_or, not_le]
  have hdisj : Disjoint (Iio (-a)) (Ioi a) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_Iio] at hx
    simp only [Set.mem_Ioi] at hx'
    linarith
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioi hf.integrableOn hf.integrableOn]
  have hIioIic : ∫ x in Iio (-a), f x = ∫ x in Iic (-a), f x :=
    setIntegral_congr_set Iio_ae_eq_Iic
  have hrefl : ∫ x in Iic (-a), f x = ∫ x in Ioi a, f x := by
    rw [← integral_comp_neg_Ioi a f]
    exact setIntegral_congr_fun measurableSet_Ioi fun x _ => heven x
  rw [hIioIic, hrefl]
  ring

/-- Pointwise squared norm of a self-dual Hermite function in polynomial--Gaussian form. -/
theorem norm_sq_hermiteSchwartz_eq_polyGaussian (n : ℕ) (x : ℝ) :
    ‖GaloisForLFunctions.hermiteSchwartz n x‖ ^ (2 : ℕ) =
      (GaloisForLFunctions.hermitePoly n).eval x ^ (2 : ℕ) *
        Real.exp (-(2 * Real.pi * x ^ (2 : ℕ))) := by
  rw [GaloisForLFunctions.hermiteSchwartz_apply, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, GaloisForLFunctions.gaussReal]
  rw [mul_pow]
  congr 1
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- Squared Hermite functions of even index are even and integrable. -/
theorem integrable_even_norm_sq_hermiteSchwartz (k : ℕ) :
    Integrable (fun x : ℝ => ‖GaloisForLFunctions.hermiteSchwartz (2 * k) x‖ ^ (2 : ℕ)) := by
  have h := integrable_norm_sq (hermiteL2 (2 * k))
  exact h.congr ((hermiteL2_coeFn (2 * k)).fun_comp fun z : ℂ => ‖z‖ ^ (2 : ℕ))

theorem even_norm_sq_hermiteSchwartz (k : ℕ) (x : ℝ) :
    ‖GaloisForLFunctions.hermiteSchwartz (2 * k) (-x)‖ ^ (2 : ℕ) =
      ‖GaloisForLFunctions.hermiteSchwartz (2 * k) x‖ ^ (2 : ℕ) := by
  rw [GaloisForLFunctions.hermiteSchwartz_even]

/-- Exact two-sided tail representation of an unnormalized step-four Hermite truncation error. -/
theorem norm_sq_hermiteEven_sub_cut_eq_two_tail (j : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    ‖hermiteEven j - evenIndicatorCutoff a (hermiteEven j)‖ ^ (2 : ℕ) =
      2 * ∫ x in Ioi a,
        (GaloisForLFunctions.hermitePoly (4 * j)).eval x ^ (2 : ℕ) *
          Real.exp (-(2 * Real.pi * x ^ (2 : ℕ))) := by
  rw [norm_sq_sub_cut_eq a (hermiteEven j)]
  have hae :
      (∫ x in (centralInterval a)ᶜ, ‖((hermiteEven j : SoninL2) : ℝ → ℂ) x‖ ^ (2 : ℕ)) =
        ∫ x in (centralInterval a)ᶜ,
          ‖GaloisForLFunctions.hermiteSchwartz (4 * j) x‖ ^ (2 : ℕ) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (hermiteL2_coeFn (4 * j))] with x hx
    rw [coe_hermiteEven, hx]
  rw [hae]
  have htwo := integral_compl_Icc_eq_two_mul_integral_Ioi_of_even
    (integrable_even_norm_sq_hermiteSchwartz (2 * j))
    (even_norm_sq_hermiteSchwartz (2 * j)) ha
  have htwo' :
      (∫ x in (Icc (-a) a)ᶜ,
        ‖GaloisForLFunctions.hermiteSchwartz (4 * j) x‖ ^ (2 : ℕ)) =
          2 * ∫ x in Ioi a,
            ‖GaloisForLFunctions.hermiteSchwartz (4 * j) x‖ ^ (2 : ℕ) := by
    simpa only [show 2 * (2 * j) = 4 * j by ring] using htwo
  rw [show centralInterval a = Icc (-a) a from rfl, htwo']
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  exact norm_sq_hermiteSchwartz_eq_polyGaussian (4 * j) x

/-- Exact leading tail of every positive step-four Hermite truncation error. -/
theorem tendsto_norm_sq_hermiteEven_sub_cut_div_leading
    (j : ℕ) (hj : 0 < j) :
    Tendsto
      (fun a : ℝ =>
        ‖hermiteEven j - evenIndicatorCutoff a (hermiteEven j)‖ ^ (2 : ℕ) /
          (a ^ (8 * j - 1) * Real.exp (-(2 * Real.pi * a ^ (2 : ℕ)))))
      atTop (nhds (2 ^ (8 * j) / (2 * Real.pi))) := by
  have h := tendsto_hermitePolySqTail_div_leading (4 * j) (by omega)
  have h2 := h.const_mul 2
  have h3 : Tendsto
      (fun a : ℝ =>
        ‖hermiteEven j - evenIndicatorCutoff a (hermiteEven j)‖ ^ (2 : ℕ) /
          (a ^ (8 * j - 1) * Real.exp (-(2 * Real.pi * a ^ (2 : ℕ)))))
      atTop (nhds (2 * (2 ^ (2 * (4 * j)) / (4 * Real.pi)))) := by
    apply h2.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    rw [norm_sq_hermiteEven_sub_cut_eq_two_tail j ha]
    rw [show 2 * (4 * j) - 1 = 8 * j - 1 by omega]
    ring
  convert h3 using 1 <;> ring

/-- Exact leading tail of the ground Hermite truncation error. -/
theorem tendsto_norm_sq_hermiteEven_zero_sub_cut_div_leading :
    Tendsto
      (fun a : ℝ =>
        ‖hermiteEven 0 - evenIndicatorCutoff a (hermiteEven 0)‖ ^ (2 : ℕ) /
          (a⁻¹ * Real.exp (-(2 * Real.pi * a ^ (2 : ℕ)))))
      atTop (nhds (1 / (2 * Real.pi))) := by
  have h := tendsto_gaussianTail_div_leading (b := 2 * Real.pi) (by positivity)
  have h2 := h.const_mul 2
  have h3 : Tendsto
      (fun a : ℝ =>
        ‖hermiteEven 0 - evenIndicatorCutoff a (hermiteEven 0)‖ ^ (2 : ℕ) /
          (a⁻¹ * Real.exp (-(2 * Real.pi * a ^ (2 : ℕ)))))
      atTop (nhds (2 * (1 / (2 * (2 * Real.pi))))) := by
    apply h2.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    rw [norm_sq_hermiteEven_sub_cut_eq_two_tail 0 ha]
    simp only [Nat.mul_zero, GaloisForLFunctions.hermitePoly_zero,
      Polynomial.eval_one, one_pow]
    ring
  convert h3 using 1 <;> ring

/-- Exact leading tail of every normalized positive step-four Hermite vector. -/
theorem tendsto_norm_sq_hermiteEvenUnit_sub_cut_div_leading
    (j : ℕ) (hj : 0 < j) :
    Tendsto
      (fun a : ℝ =>
        ‖hermiteEvenUnit j - evenIndicatorCutoff a (hermiteEvenUnit j)‖ ^ (2 : ℕ) /
          (a ^ (8 * j - 1) * Real.exp (-(2 * Real.pi * a ^ (2 : ℕ)))))
      atTop (nhds (2 ^ (8 * j) / (2 * Real.pi * ‖hermiteEven j‖ ^ (2 : ℕ)))) := by
  have h := (tendsto_norm_sq_hermiteEven_sub_cut_div_leading j hj).div_const
    (‖hermiteEven j‖ ^ (2 : ℕ))
  have hne : ‖hermiteEven j‖ ^ (2 : ℕ) ≠ 0 := pow_ne_zero _
    (norm_ne_zero_iff.mpr (hermiteEven_ne_zero j))
  have h' : Tendsto
      (fun a : ℝ =>
        ‖hermiteEvenUnit j - evenIndicatorCutoff a (hermiteEvenUnit j)‖ ^ (2 : ℕ) /
          (a ^ (8 * j - 1) * Real.exp (-(2 * Real.pi * a ^ (2 : ℕ)))))
      atTop (nhds ((2 ^ (8 * j) / (2 * Real.pi)) / ‖hermiteEven j‖ ^ (2 : ℕ))) := by
    apply h.congr'
    filter_upwards with a
    rw [norm_sq_hermiteEvenUnit_sub_cut]
    field_simp [hne]
  convert h' using 1
  field_simp [hne, Real.pi_ne_zero]

/-- Exact leading tail of the normalized ground Hermite vector. -/
theorem tendsto_norm_sq_hermiteEvenUnit_zero_sub_cut_div_leading :
    Tendsto
      (fun a : ℝ =>
        ‖hermiteEvenUnit 0 - evenIndicatorCutoff a (hermiteEvenUnit 0)‖ ^ (2 : ℕ) /
          (a⁻¹ * Real.exp (-(2 * Real.pi * a ^ (2 : ℕ)))))
      atTop (nhds (1 / (2 * Real.pi * ‖hermiteEven 0‖ ^ (2 : ℕ)))) := by
  have h := tendsto_norm_sq_hermiteEven_zero_sub_cut_div_leading.div_const
    (‖hermiteEven 0‖ ^ (2 : ℕ))
  have hne : ‖hermiteEven 0‖ ^ (2 : ℕ) ≠ 0 := pow_ne_zero _
    (norm_ne_zero_iff.mpr (hermiteEven_ne_zero 0))
  have h' : Tendsto
      (fun a : ℝ =>
        ‖hermiteEvenUnit 0 - evenIndicatorCutoff a (hermiteEvenUnit 0)‖ ^ (2 : ℕ) /
          (a⁻¹ * Real.exp (-(2 * Real.pi * a ^ (2 : ℕ)))))
      atTop (nhds ((1 / (2 * Real.pi)) / ‖hermiteEven 0‖ ^ (2 : ℕ))) := by
    apply h.congr'
    filter_upwards with a
    rw [norm_sq_hermiteEvenUnit_sub_cut]
    field_simp [hne]
  convert h' using 1
  field_simp [hne, Real.pi_ne_zero]

/-! ## Uniform finite-depth envelope -/

/-- The sharp polynomial--Gaussian scale for the `j`-th step-four Hermite tail.  The ground
vector has degree zero and therefore carries the reciprocal-power scale; every positive index has
degree `8*j` after squaring. -/
def hermiteStepFourTailScale (j : ℕ) (a : ℝ) : ℝ :=
  if j = 0 then a⁻¹ * Real.exp (-(2 * Real.pi * a ^ (2 : ℕ)))
  else a ^ (8 * j - 1) * Real.exp (-(2 * Real.pi * a ^ (2 : ℕ)))

/-- Exact leading constant belonging to `hermiteStepFourTailScale`. -/
def hermiteStepFourTailConstant (j : ℕ) : ℝ :=
  if j = 0 then 1 / (2 * Real.pi * ‖hermiteEven 0‖ ^ (2 : ℕ))
  else 2 ^ (8 * j) / (2 * Real.pi * ‖hermiteEven j‖ ^ (2 : ℕ))

theorem hermiteStepFourTailScale_pos (j : ℕ) {a : ℝ} (ha : 0 < a) :
    0 < hermiteStepFourTailScale j a := by
  rw [hermiteStepFourTailScale]
  split <;> positivity

theorem hermiteStepFourTailConstant_pos (j : ℕ) :
    0 < hermiteStepFourTailConstant j := by
  rw [hermiteStepFourTailConstant]
  split
  · have hnorm : 0 < ‖hermiteEven 0‖ ^ (2 : ℕ) :=
      sq_pos_of_pos (norm_pos_iff.mpr (hermiteEven_ne_zero 0))
    positivity
  · have hnorm : 0 < ‖hermiteEven j‖ ^ (2 : ℕ) :=
      sq_pos_of_pos (norm_pos_iff.mpr (hermiteEven_ne_zero j))
    positivity

/-- At aperture at least one, the sharp tail scales increase with the Hermite index. -/
theorem hermiteStepFourTailScale_mono {j n : ℕ} {a : ℝ} (ha : 1 ≤ a) (hjn : j ≤ n) :
    hermiteStepFourTailScale j a ≤ hermiteStepFourTailScale n a := by
  by_cases hj : j = 0
  · subst j
    by_cases hn : n = 0
    · subst n
      exact le_rfl
    · simp only [hermiteStepFourTailScale, if_pos, if_neg hn]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact (inv_le_one_of_one_le₀ ha).trans (one_le_pow₀ ha)
  · have hn : n ≠ 0 := by omega
    simp only [hermiteStepFourTailScale, if_neg hj, if_neg hn]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    exact pow_le_pow_right₀ ha (by omega)

/-- Unified exact normalized-tail law, including the exceptional ground scale. -/
theorem tendsto_norm_sq_hermiteEvenUnit_sub_cut_div_tailScale (j : ℕ) :
    Tendsto
      (fun a : ℝ =>
        ‖hermiteEvenUnit j - evenIndicatorCutoff a (hermiteEvenUnit j)‖ ^ (2 : ℕ) /
          hermiteStepFourTailScale j a)
      atTop (nhds (hermiteStepFourTailConstant j)) := by
  by_cases hj : j = 0
  · subst j
    simpa [hermiteStepFourTailScale, hermiteStepFourTailConstant] using
      tendsto_norm_sq_hermiteEvenUnit_zero_sub_cut_div_leading
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
    simpa [hermiteStepFourTailScale, hermiteStepFourTailConstant, hj] using
      tendsto_norm_sq_hermiteEvenUnit_sub_cut_div_leading j hjpos

/-- Every normalized Hermite tail is eventually bounded by one unit above its exact leading
constant. -/
theorem eventually_norm_sq_hermiteEvenUnit_sub_cut_le_tailScale (j : ℕ) :
    ∀ᶠ a : ℝ in atTop,
      ‖hermiteEvenUnit j - evenIndicatorCutoff a (hermiteEvenUnit j)‖ ^ (2 : ℕ) ≤
        (hermiteStepFourTailConstant j + 1) * hermiteStepFourTailScale j a := by
  have hratio :=
    (tendsto_order.1 (tendsto_norm_sq_hermiteEvenUnit_sub_cut_div_tailScale j)).2
      (hermiteStepFourTailConstant j + 1) (lt_add_one (hermiteStepFourTailConstant j))
  filter_upwards [hratio, eventually_gt_atTop (0 : ℝ)] with a ha' ha
  exact (div_le_iff₀ (hermiteStepFourTailScale_pos j ha)).mp ha'.le

/-- The complete `(n+1)`-dimensional Hermite trial defect has the sharp largest-index
polynomial--Gaussian envelope.  This finite aggregation loses neither Gaussian exponent nor an
aperture-dependent constant. -/
theorem eventually_hermiteTrialDefect_le_tailScale (n : ℕ) :
    ∀ᶠ a : ℝ in atTop,
      hermiteTrialDefect a n ≤
        (∑ k : Fin (n + 1),
          5 * (hermiteStepFourTailConstant (k : ℕ) + 1)) *
            hermiteStepFourTailScale n a := by
  have hall : ∀ᶠ a : ℝ in atTop, ∀ k : Fin (n + 1),
      ‖hermiteEvenUnit (k : ℕ) - evenIndicatorCutoff a (hermiteEvenUnit (k : ℕ))‖ ^ (2 : ℕ) ≤
        (hermiteStepFourTailConstant (k : ℕ) + 1) *
          hermiteStepFourTailScale (k : ℕ) a := by
    simpa only [Finset.mem_univ, forall_const] using
      (Finset.eventually_all (Finset.univ : Finset (Fin (n + 1)))).2
        (fun k _ => eventually_norm_sq_hermiteEvenUnit_sub_cut_le_tailScale (k : ℕ))
  filter_upwards [hall, eventually_ge_atTop (1 : ℝ)] with a hall ha
  rw [hermiteTrialDefect]
  calc
    ∑ k : Fin (n + 1),
        5 * ‖hermiteEvenUnit (k : ℕ) -
          evenIndicatorCutoff a (hermiteEvenUnit (k : ℕ))‖ ^ (2 : ℕ)
      ≤ ∑ k : Fin (n + 1),
          5 * ((hermiteStepFourTailConstant (k : ℕ) + 1) *
            hermiteStepFourTailScale n a) := by
            apply Finset.sum_le_sum
            intro k _
            have hmono := hermiteStepFourTailScale_mono ha (Nat.le_of_lt_succ k.isLt)
            have hc : 0 ≤ hermiteStepFourTailConstant (k : ℕ) + 1 := by
              have := hermiteStepFourTailConstant_pos (k : ℕ)
              positivity
            calc
              5 * ‖hermiteEvenUnit (k : ℕ) -
                    evenIndicatorCutoff a (hermiteEvenUnit (k : ℕ))‖ ^ (2 : ℕ)
                ≤ 5 * ((hermiteStepFourTailConstant (k : ℕ) + 1) *
                    hermiteStepFourTailScale (k : ℕ) a) := by
                      gcongr
                      exact hall k
              _ ≤ 5 * ((hermiteStepFourTailConstant (k : ℕ) + 1) *
                    hermiteStepFourTailScale n a) := by
                      gcongr
    _ = (∑ k : Fin (n + 1),
          5 * (hermiteStepFourTailConstant (k : ℕ) + 1)) *
            hermiteStepFourTailScale n a := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring

end RHTower

end
