import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.PhaseExtraction.SexticFilterEnergy

/-!
# Unique minimum-energy target filters

Every six-phase weight suppressing the constant and direct modes and retaining
the inverse mode has three free Fourier coefficients. Geometric cancellation
fixes one linear functional of these coefficients. Orthogonal projection onto
that affine hyperplane gives the unique minimum and an exact excess-energy law.
-/

noncomputable section
open Complex Finset
open scoped Classical ComplexConjugate InnerProductSpace
namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

/-- The positive Gram scalar for cancelling the geometric row with three modes. -/
def targetGram (Y : ℂ) : ℝ := 1 + ‖Y‖ ^ 2 + ‖Y‖ ^ 4

theorem targetGram_pos (Y : ℂ) : 0 < targetGram Y := by
  unfold targetGram
  positivity

/-- The normal to the geometric-cancellation constraint in coefficient space. -/
def targetNormal (Y : ℂ) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 ![conj (Y ^ 2), conj Y, 1]

/-- The coefficients of least energy with geometric response `−Y³`. -/
def minimumTargetTail (Y : ℂ) : EuclideanSpace ℂ (Fin 3) :=
  (-Y ^ 3 / (targetGram Y : ℂ)) • targetNormal Y

/-- The squared normal length is the positive Gram scalar. -/
theorem norm_targetNormal_sq (Y : ℂ) : ‖targetNormal Y‖ ^ 2 = targetGram Y := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [targetNormal, targetGram, Fin.sum_univ_succ, norm_pow]
  ring

/-- The inner product with the normal is the literal geometric constraint. -/
theorem inner_targetNormal (Y : ℂ) (v : EuclideanSpace ℂ (Fin 3)) :
    ⟪targetNormal Y, v⟫_ℂ = Y ^ 2 * v 0 + Y * v 1 + v 2 := by
  rw [PiLp.inner_apply]
  simp [targetNormal, Fin.sum_univ_succ, RCLike.inner_apply]
  ring

/-- The minimizing tail satisfies the cancellation equation for every `Y`. -/
theorem minimumTargetTail_constraint (Y : ℂ) :
    ⟪targetNormal Y, minimumTargetTail Y⟫_ℂ = -Y ^ 3 := by
  have hself : ⟪targetNormal Y, targetNormal Y⟫_ℂ = (targetGram Y : ℂ) := by
    rw [inner_targetNormal]
    change Y ^ 2 * conj (Y ^ 2) + Y * conj Y + 1 = (targetGram Y : ℂ)
    simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow]
    unfold targetGram
    push_cast
    ring
  rw [minimumTargetTail, inner_smul_right, hself]
  exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (targetGram_pos Y).ne')

/-- The minimum tail energy is `‖Y‖⁶/(1+‖Y‖²+‖Y‖⁴)`. -/
theorem norm_minimumTargetTail_sq (Y : ℂ) :
    ‖minimumTargetTail Y‖ ^ 2 = ‖Y‖ ^ 6 / targetGram Y := by
  rw [minimumTargetTail, norm_smul, mul_pow, norm_targetNormal_sq,
    norm_div, norm_neg, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (targetGram_pos Y).le]
  field_simp [(targetGram_pos Y).ne']

/-- Exact excess energy above the minimizing tail, including the equality case. -/
theorem targetTail_energy_decomposition (Y : ℂ) (v : EuclideanSpace ℂ (Fin 3))
    (hv : ⟪targetNormal Y, v⟫_ℂ = -Y ^ 3) :
    ‖v‖ ^ 2 = ‖Y‖ ^ 6 / targetGram Y + ‖v - minimumTargetTail Y‖ ^ 2 := by
  have ho : ⟪minimumTargetTail Y, v - minimumTargetTail Y⟫_ℂ = 0 := by
    rw [minimumTargetTail, inner_smul_left]
    have he : ⟪targetNormal Y, v - minimumTargetTail Y⟫_ℂ = 0 := by
      rw [inner_sub_right, hv, minimumTargetTail_constraint, sub_self]
    change conj (-Y ^ 3 / (targetGram Y : ℂ)) *
      ⟪targetNormal Y, v - minimumTargetTail Y⟫_ℂ = 0
    rw [he, mul_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (minimumTargetTail Y) (v - minimumTargetTail Y) ho
  have he : minimumTargetTail Y + (v - minimumTargetTail Y) = v := by abel
  rw [he] at h
  simpa only [← pow_two, norm_minimumTargetTail_sq] using h

/-- Every admissible tail has at least the explicit minimum energy. -/
theorem minimumTargetTail_energy_le (Y : ℂ) (v : EuclideanSpace ℂ (Fin 3))
    (hv : ⟪targetNormal Y, v⟫_ℂ = -Y ^ 3) :
    ‖Y‖ ^ 6 / targetGram Y ≤ ‖v‖ ^ 2 := by
  rw [targetTail_energy_decomposition Y v hv]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Equality in the minimum-energy bound fixes all three coefficients. -/
theorem minimumTargetTail_unique (Y : ℂ) (v : EuclideanSpace ℂ (Fin 3))
    (hv : ⟪targetNormal Y, v⟫_ℂ = -Y ^ 3) :
    ‖v‖ ^ 2 = ‖Y‖ ^ 6 / targetGram Y ↔ v = minimumTargetTail Y := by
  rw [targetTail_energy_decomposition Y v hv]
  simp only [add_eq_left, sq_eq_zero_iff, norm_eq_zero, sub_eq_zero]

/-- The four modes that remain after suppressing constants and the direct row mode. -/
def fourModeCoefficients (c : ℂ) (v : EuclideanSpace ℂ (Fin 3)) : Fin 6 → ℂ :=
  ![0, c, v 0, v 1, v 2, 0]

/-- A phase weight with one target coefficient and three cancellation coefficients. -/
def fourModeWeight (c : ℂ) (v : EuclideanSpace ℂ (Fin 3)) (ρ : ℂ) : ℂ :=
  c * ρ + v 0 * ρ ^ 2 + v 1 * ρ ^ 3 + v 2 * ρ ^ 4

/-- Polynomial and coordinate descriptions agree pointwise. -/
theorem sexticPolynomial_fourMode (c : ℂ) (v : EuclideanSpace ℂ (Fin 3)) (ρ : ℂ) :
    sexticPolynomial (fourModeCoefficients c v) ρ = fourModeWeight c v ρ := by
  simp [sexticPolynomial, fourModeCoefficients, fourModeWeight, Fin.sum_univ_succ]
  ring

/-- Coefficient energy splits into the target mode and the three free modes. -/
theorem fourModeCoefficients_energy (c : ℂ) (v : EuclideanSpace ℂ (Fin 3)) :
    ∑ j : Fin 6, ‖fourModeCoefficients c v j‖ ^ 2 = ‖c‖ ^ 2 + ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [fourModeCoefficients, Fin.sum_univ_succ]

/-- Exact phase energy for the four remaining Fourier modes. -/
theorem fourModeWeight_energy {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6)
    (c : ℂ) (v : EuclideanSpace ℂ (Fin 3)) :
    ∑ i : Fin 6, ‖fourModeWeight c v (ζ ^ i.val)‖ ^ 2 =
      6 * (‖c‖ ^ 2 + ‖v‖ ^ 2) := by
  simpa only [sexticPolynomial_fourMode, fourModeCoefficients_energy] using
    sexticPolynomial_energy hζ (fourModeCoefficients c v)

/-- Differences retain their literal Fourier coefficients. -/
theorem fourModeWeight_sub (c d : ℂ) (v u : EuclideanSpace ℂ (Fin 3)) (ρ : ℂ) :
    fourModeWeight c v ρ - fourModeWeight d u ρ =
      fourModeWeight (c - d) (v - u) ρ := by
  simp only [fourModeWeight, PiLp.sub_apply]
  ring

/-- The minimizing homogeneous filter, defined at every complex value of `Y`. -/
def minimumTargetWeight (Y ρ : ℂ) : ℂ := fourModeWeight 1 (minimumTargetTail Y) ρ

/-- Its exact mean-square cost includes the excess required for geometric cancellation. -/
theorem minimumTargetWeight_energy {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6) (Y : ℂ) :
    ∑ i : Fin 6, ‖minimumTargetWeight Y (ζ ^ i.val)‖ ^ 2 =
      6 * (1 + ‖Y‖ ^ 6 / targetGram Y) := by
  simpa only [minimumTargetWeight, norm_one, one_pow, norm_minimumTargetTail_sq] using
    fourModeWeight_energy hζ (1 : ℂ) (minimumTargetTail Y)

/-- The three free coefficients of any observed phase weight. -/
def phaseTargetTail (ζ : ℂ) (w : Fin 6 → ℂ) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 ![sexticCoefficients ζ w 2, sexticCoefficients ζ w 3,
    sexticCoefficients ζ w 4]

/-- Every normalized weight suppressing the constant and direct modes has the
four-mode form; no restriction on its remaining values is imposed. -/
theorem phaseWeight_eq_fourMode {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6) (w : Fin 6 → ℂ)
    (h0 : sexticCoefficients ζ w 0 = 0) (h1 : sexticCoefficients ζ w 1 = 1)
    (h5 : sexticCoefficients ζ w 5 = 0) (i : Fin 6) :
    w i = fourModeWeight 1 (phaseTargetTail ζ w) (ζ ^ i.val) := by
  rw [← sexticPolynomial_coefficients hζ w i]
  simp [sexticPolynomial, Fin.sum_univ_succ, h0, h1, h5,
    fourModeWeight, phaseTargetTail]
  ring

/-- The geometric observation sees one explicit affine constraint on the three
free coefficients. -/
theorem fourModeWeight_geometric {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6)
    (Y : ℂ) (hY : Y ^ 6 ≠ 1) (v : EuclideanSpace ℂ (Fin 3)) :
    sexticReadout (fun i => fourModeWeight 1 v (ζ ^ i.val))
      (fun i => ζ ^ i.val * Y * (1 - ζ ^ i.val * Y)⁻¹) =
        Y ^ 2 * (Y ^ 3 + ⟪targetNormal Y, v⟫_ℂ) / (1 - Y ^ 6) := by
  rw [sexticReadout_geometric hζ _ Y hY]
  have hc (j : Fin 6) :
      sexticCoefficients ζ (fun i => fourModeWeight 1 v (ζ ^ i.val)) j =
        fourModeCoefficients 1 v j := by
    simpa only [sexticPolynomial_fourMode] using
      sexticCoefficients_polynomial hζ (fourModeCoefficients 1 v) j
  simp [hc, fourModeCoefficients, inner_targetNormal]
  ring

/-- Away from `Y=0`, geometric cancellation is precisely the normal equation. -/
theorem fourModeWeight_geometric_zero_iff {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6)
    (Y : ℂ) (hY : Y ^ 6 ≠ 1) (hY0 : Y ≠ 0) (v : EuclideanSpace ℂ (Fin 3)) :
    sexticReadout (fun i => fourModeWeight 1 v (ζ ^ i.val))
      (fun i => ζ ^ i.val * Y * (1 - ζ ^ i.val * Y)⁻¹) = 0 ↔
        ⟪targetNormal Y, v⟫_ℂ = -Y ^ 3 := by
  rw [fourModeWeight_geometric hζ Y hY v]
  have hd : 1 - Y ^ 6 ≠ 0 := sub_ne_zero.mpr (Ne.symm hY)
  rw [div_eq_iff hd, zero_mul, mul_eq_zero]
  simp only [pow_ne_zero _ hY0, false_or, add_eq_zero_iff_eq_neg]
  constructor <;> intro h <;> linear_combination h

/-- The minimizing filter passes all geometric-cancellation tests. -/
theorem minimumTargetWeight_geometric {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6)
    (Y : ℂ) (hY : Y ^ 6 ≠ 1) :
    sexticReadout (fun i => minimumTargetWeight Y (ζ ^ i.val))
      (fun i => ζ ^ i.val * Y * (1 - ζ ^ i.val * Y)⁻¹) = 0 := by
  change sexticReadout (fun i => fourModeWeight 1 (minimumTargetTail Y) (ζ ^ i.val))
    (fun i => ζ ^ i.val * Y * (1 - ζ ^ i.val * Y)⁻¹) = 0
  rw [fourModeWeight_geometric hζ Y hY,
    minimumTargetTail_constraint, add_neg_cancel, mul_zero, zero_div]

/-- Geometric cancellation has the same exact excess-energy law at `Y=0`,
where the minimizing tail is zero and the cancellation test is automatic. -/
theorem targetTail_energy_of_geometric_zero {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6)
    (Y : ℂ) (hY : Y ^ 6 ≠ 1) (v : EuclideanSpace ℂ (Fin 3))
    (hv : sexticReadout (fun i => fourModeWeight 1 v (ζ ^ i.val))
      (fun i => ζ ^ i.val * Y * (1 - ζ ^ i.val * Y)⁻¹) = 0) :
    ‖v‖ ^ 2 = ‖Y‖ ^ 6 / targetGram Y + ‖v - minimumTargetTail Y‖ ^ 2 := by
  by_cases hY0 : Y = 0
  · subst Y
    simp [minimumTargetTail]
  · exact targetTail_energy_decomposition Y v
      ((fourModeWeight_geometric_zero_iff hζ Y hY hY0 v).mp hv)

/-- All normalized homogeneous target filters obey an exact excess-energy
identity. Its residual records every departure from the unique minimizer. -/
theorem targetWeight_energy_decomposition {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6)
    (Y : ℂ) (hY : Y ^ 6 ≠ 1) (w : Fin 6 → ℂ)
    (h0 : sexticCoefficients ζ w 0 = 0) (h1 : sexticCoefficients ζ w 1 = 1)
    (h5 : sexticCoefficients ζ w 5 = 0)
    (hg : sexticReadout w (fun i => ζ ^ i.val * Y * (1 - ζ ^ i.val * Y)⁻¹) = 0) :
    ∑ i : Fin 6, ‖w i‖ ^ 2 = 6 * (1 + ‖Y‖ ^ 6 / targetGram Y) +
      ∑ i : Fin 6, ‖w i - minimumTargetWeight Y (ζ ^ i.val)‖ ^ 2 := by
  let v := phaseTargetTail ζ w
  have hr : w = fun i => fourModeWeight 1 v (ζ ^ i.val) :=
    funext (phaseWeight_eq_fourMode hζ w h0 h1 h5)
  have hv := targetTail_energy_of_geometric_zero hζ Y hY v (by simpa only [hr] using hg)
  have hd : (∑ i : Fin 6, ‖w i - minimumTargetWeight Y (ζ ^ i.val)‖ ^ 2) =
      6 * ‖v - minimumTargetTail Y‖ ^ 2 := by
    rw [hr]
    simp_rw [minimumTargetWeight, fourModeWeight_sub, sub_self]
    rw [fourModeWeight_energy hζ]
    norm_num
  rw [hd, hr, fourModeWeight_energy hζ, hv]
  norm_num
  ring

/-- Minimum mean-square cost among every six-phase weight passing the target
normalization and the constant, direct-mode and geometric cancellation tests. -/
theorem minimumTargetWeight_optimal {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6)
    (Y : ℂ) (hY : Y ^ 6 ≠ 1) (w : Fin 6 → ℂ)
    (h0 : sexticCoefficients ζ w 0 = 0) (h1 : sexticCoefficients ζ w 1 = 1)
    (h5 : sexticCoefficients ζ w 5 = 0)
    (hg : sexticReadout w (fun i => ζ ^ i.val * Y * (1 - ζ ^ i.val * Y)⁻¹) = 0) :
    6 * (1 + ‖Y‖ ^ 6 / targetGram Y) ≤ ∑ i : Fin 6, ‖w i‖ ^ 2 := by
  rw [targetWeight_energy_decomposition hζ Y hY w h0 h1 h5 hg]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Equality fixes the actual phase weights, not merely their energy. -/
theorem minimumTargetWeight_unique {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6)
    (Y : ℂ) (hY : Y ^ 6 ≠ 1) (w : Fin 6 → ℂ)
    (h0 : sexticCoefficients ζ w 0 = 0) (h1 : sexticCoefficients ζ w 1 = 1)
    (h5 : sexticCoefficients ζ w 5 = 0)
    (hg : sexticReadout w (fun i => ζ ^ i.val * Y * (1 - ζ ^ i.val * Y)⁻¹) = 0) :
    (∑ i : Fin 6, ‖w i‖ ^ 2) = 6 * (1 + ‖Y‖ ^ 6 / targetGram Y) ↔
      w = fun i => minimumTargetWeight Y (ζ ^ i.val) := by
  constructor
  · intro he
    have hd := targetWeight_energy_decomposition hζ Y hY w h0 h1 h5 hg
    have hs : (∑ i : Fin 6, ‖w i - minimumTargetWeight Y (ζ ^ i.val)‖ ^ 2) = 0 := by
      linarith only [he, hd]
    funext i
    have hi := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin 6))) =>
        sq_nonneg ‖w j - minimumTargetWeight Y (ζ ^ j.val)‖)
      (Finset.mem_univ i)
    rw [hs] at hi
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp
      (le_antisymm hi (sq_nonneg _))))
  · intro he
    rw [he, minimumTargetWeight_energy hζ]

/-- The minimizing construction satisfies every extraction test. -/
theorem minimumTargetWeight_admissible {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6)
    (Y : ℂ) (hY : Y ^ 6 ≠ 1) :
    sexticCoefficients ζ (fun i => minimumTargetWeight Y (ζ ^ i.val)) 0 = 0 ∧
    sexticCoefficients ζ (fun i => minimumTargetWeight Y (ζ ^ i.val)) 1 = 1 ∧
    sexticCoefficients ζ (fun i => minimumTargetWeight Y (ζ ^ i.val)) 5 = 0 ∧
    sexticReadout (fun i => minimumTargetWeight Y (ζ ^ i.val))
      (fun i => ζ ^ i.val * Y * (1 - ζ ^ i.val * Y)⁻¹) = 0 := by
  have hc (j : Fin 6) :
      sexticCoefficients ζ (fun i => minimumTargetWeight Y (ζ ^ i.val)) j =
        fourModeCoefficients 1 (minimumTargetTail Y) j := by
    simpa only [sexticPolynomial_fourMode, minimumTargetWeight] using
      sexticCoefficients_polynomial hζ (fourModeCoefficients 1 (minimumTargetTail Y)) j
  refine ⟨?_, ?_, ?_, minimumTargetWeight_geometric hζ Y hY⟩ <;>
    simp [hc, fourModeCoefficients]

/-- Nonzero geometric parameters strictly improve the two-mode filter cost. -/
theorem minimumTargetWeight_cost_lt (Y : ℂ) (hY : Y ≠ 0) :
    1 + ‖Y‖ ^ 6 / targetGram Y < 1 + ‖Y‖ ^ 2 := by
  have hn : 0 < ‖Y‖ := norm_pos_iff.mpr hY
  have hp : 0 < ‖Y‖ ^ 2 + ‖Y‖ ^ 4 := by positivity
  have hd : ‖Y‖ ^ 2 * targetGram Y - ‖Y‖ ^ 6 = ‖Y‖ ^ 2 + ‖Y‖ ^ 4 := by
    unfold targetGram
    ring
  have hh : ‖Y‖ ^ 6 / targetGram Y < ‖Y‖ ^ 2 :=
    (div_lt_iff₀ (targetGram_pos Y)).mpr (by linarith only [hp, hd])
  linarith only [hh]

/-- On the unit circle the exact minimum mean-square cost is `4/3`. -/
theorem minimumTargetWeight_cost_unit (Y : ℂ) (hY : ‖Y‖ = 1) :
    1 + ‖Y‖ ^ 6 / targetGram Y = 4 / 3 := by
  norm_num [targetGram, hY]

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
