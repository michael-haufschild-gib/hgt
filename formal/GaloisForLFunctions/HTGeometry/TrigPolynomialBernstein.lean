import GaloisForLFunctions.QuantumAlg.Primitives.GeneralizedParameterShift

/-!
# Bernstein's inequality for trigonometric polynomials

M. Riesz's interpolation formula writes the derivative of a real trigonometric polynomial of degree
`R` at the origin as a fixed weighted sum of its values at the `2R` nodes `(2μ-1)π/(2R)`.  The
weights alternate in sign, and evaluating the formula on `sin (R x)` — whose values at those nodes
are exactly the signs — computes their total mass to be `R`.  Bounding the interpolation formula
termwise therefore gives

`|ℓ'(t)| ≤ R · sup |ℓ|`,

with the constant attained by `sin (R x)`.  Translating the coefficients moves the estimate from the
origin to every point, so a degree bound on the spectrum becomes a Lipschitz bound on the function.
-/

namespace GaloisForLFunctions.HTGeometry

open QuantumAlg

/-- Half of a first-derivative node, in the form the weight uses. -/
theorem psPoint_div_two (R μ : ℕ) :
    psPoint R μ / 2 = (2 * (μ : ℝ) - 1) * Real.pi / (4 * R) := by
  unfold psPoint
  ring

/-- The sine appearing in the first-derivative weight is nonzero at an interior node. -/
theorem sin_psWeight_denom_ne_zero {R μ : ℕ} (hR : 1 ≤ R) (hμ : 1 ≤ μ) (hμR : μ ≤ 2 * R) :
    Real.sin ((2 * (μ : ℝ) - 1) * Real.pi / (4 * R)) ≠ 0 := by
  have h := sin_half_psPoint_ne R μ hR hμ hμR
  rwa [psPoint_div_two] at h

/-- **The first-derivative weights alternate in sign.**  Multiplying by `(-1)^{μ-1}` makes the
weight its own absolute value. -/
theorem abs_psWeight {R μ : ℕ} (hR : 1 ≤ R) (hμ : 1 ≤ μ) (hμR : μ ≤ 2 * R) :
    |psWeight R μ| = (-1 : ℝ) ^ (μ - 1) * psWeight R μ := by
  have hs := sin_psWeight_denom_ne_zero hR hμ hμR
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hsq : 0 < Real.sin ((2 * (μ : ℝ) - 1) * Real.pi / (4 * R)) ^ (2 : ℕ) :=
    pow_pos (abs_pos.mpr hs) 2 |>.trans_le (le_of_eq (by rw [sq_abs]))
  have hden : 0 < 4 * (R : ℝ) * Real.sin ((2 * (μ : ℝ) - 1) * Real.pi / (4 * R)) ^ (2 : ℕ) := by
    positivity
  have hsign : ((-1 : ℝ) ^ (μ - 1)) * ((-1 : ℝ) ^ (μ - 1)) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨μ - 1, rfl⟩
  unfold psWeight
  rw [abs_div, abs_of_pos hden, abs_pow, abs_neg, abs_one, one_pow, ← mul_div_assoc, hsign]

/-- **The total mass of the Riesz weights is the degree.**  Applying the interpolation formula to
`sin (R x)`, whose value at the node `x_μ` is the sign `(-1)^{μ-1}`, turns the alternating sum of
the weights into their absolute sum. -/
theorem sum_abs_psWeight (R : ℕ) (hR : 1 ≤ R) :
    ∑ μ ∈ Finset.Icc 1 (2 * R), |psWeight R μ| = (R : ℝ) := by
  classical
  set b : ℕ → ℝ := fun p => if p = R then 1 else 0 with hb
  have hcost : ∀ x : ℝ, genTrigCost (fun _ => 0) b R x = Real.sin ((R : ℝ) * x) := by
    intro x
    simp only [genTrigCost, zero_mul, zero_add]
    rw [Finset.sum_eq_single R]
    · simp [hb]
    · intro p _ hpR
      simp [hb, hpR]
    · intro hR'
      exact absurd (Finset.mem_Icc.mpr ⟨hR, le_rfl⟩) hR'
  have hrhs : ∑ p ∈ Finset.Icc 1 R, (p : ℝ) * b p = (R : ℝ) := by
    rw [Finset.sum_eq_single R]
    · simp [hb]
    · intro p _ hpR
      simp [hb, hpR]
    · intro hR'
      exact absurd (Finset.mem_Icc.mpr ⟨hR, le_rfl⟩) hR'
  have key := dirichlet_first_identity (fun _ => 0) b R hR
  rw [hrhs] at key
  rw [← key]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  obtain ⟨hμ1, hμ2⟩ := Finset.mem_Icc.mp hμ
  rw [abs_psWeight hR hμ1 hμ2, hcost, sin_R_mul_psPoint R μ hR hμ1]

/-- Cosine coefficients of the translate `x ↦ ℓ (t + x)`. -/
noncomputable def shiftCos (a b : ℕ → ℝ) (t : ℝ) : ℕ → ℝ :=
  fun p => if p = 0 then a 0 else a p * Real.cos ((p : ℝ) * t) + b p * Real.sin ((p : ℝ) * t)

/-- Sine coefficients of the translate `x ↦ ℓ (t + x)`. -/
noncomputable def shiftSin (a b : ℕ → ℝ) (t : ℝ) : ℕ → ℝ :=
  fun p => -(a p) * Real.sin ((p : ℝ) * t) + b p * Real.cos ((p : ℝ) * t)

/-- **A translate of a trigonometric polynomial is a trigonometric polynomial of the same degree.**
-/
theorem genTrigCost_shift (a b : ℕ → ℝ) (R : ℕ) (t x : ℝ) :
    genTrigCost (shiftCos a b t) (shiftSin a b t) R x = genTrigCost a b R (t + x) := by
  unfold genTrigCost shiftCos shiftSin
  rw [if_pos rfl]
  refine congrArg _ (Finset.sum_congr rfl fun p hp => ?_)
  have hp0 : p ≠ 0 := by
    have := (Finset.mem_Icc.mp hp).1
    omega
  rw [if_neg hp0]
  have hmul : (p : ℝ) * (t + x) = (p : ℝ) * t + (p : ℝ) * x := by ring
  rw [hmul, Real.cos_add, Real.sin_add]
  ring

/-- **Bernstein's inequality.**  A real trigonometric polynomial of degree at most `R` bounded by
`M` has derivative bounded by `R · M` at every point.  The constant is attained by `sin (R x)`. -/
theorem abs_deriv_genTrigCost_le {a b : ℕ → ℝ} {R : ℕ} (hR : 1 ≤ R) {M : ℝ}
    (hM : ∀ x : ℝ, |genTrigCost a b R x| ≤ M) (t : ℝ) :
    |deriv (genTrigCost a b R) t| ≤ (R : ℝ) * M := by
  classical
  set a' : ℕ → ℝ := shiftCos a b t with ha'
  set b' : ℕ → ℝ := shiftSin a b t with hb'
  have hshift : ∀ x : ℝ, genTrigCost a' b' R x = genTrigCost a b R (t + x) := fun x =>
    genTrigCost_shift a b R t x
  have hbound : ∀ x : ℝ, |genTrigCost a' b' R x| ≤ M := by
    intro x
    rw [hshift x]
    exact hM (t + x)
  have hderiv : deriv (genTrigCost a' b' R) 0 = deriv (genTrigCost a b R) t := by
    have hcomp : HasDerivAt (genTrigCost a' b' R) (deriv (genTrigCost a b R) t) 0 := by
      have hbase : HasDerivAt (genTrigCost a b R) (deriv (genTrigCost a b R) t) (t + 0) := by
        rw [add_zero]
        exact (hasDerivAt_genTrigCost a b R t).congr_deriv
          (hasDerivAt_genTrigCost a b R t).deriv.symm
      have hinner : HasDerivAt (fun x : ℝ => t + x) 1 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_add t
      have hfun : (fun x : ℝ => genTrigCost a b R (t + x)) = genTrigCost a' b' R :=
        funext fun x => (hshift x).symm
      have hc := hbase.comp 0 hinner
      simp only [Function.comp_def, mul_one] at hc
      rwa [hfun] at hc
    exact hcomp.deriv
  have hformula := GeneralizedParamShift.firstDeriv (R := R) ⟨a', b', hR⟩
  rw [hderiv] at hformula
  rw [hformula]
  calc |∑ μ ∈ Finset.Icc 1 (2 * R), genTrigCost a' b' R (psPoint R μ) * psWeight R μ|
      ≤ ∑ μ ∈ Finset.Icc 1 (2 * R), |genTrigCost a' b' R (psPoint R μ) * psWeight R μ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ μ ∈ Finset.Icc 1 (2 * R), M * |psWeight R μ| := by
        refine Finset.sum_le_sum fun μ _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hbound _) (abs_nonneg _)
    _ = M * ∑ μ ∈ Finset.Icc 1 (2 * R), |psWeight R μ| := by rw [Finset.mul_sum]
    _ = (R : ℝ) * M := by rw [sum_abs_psWeight R hR, mul_comm]

/-- **A bounded trigonometric polynomial is Lipschitz with constant `R · M`.**  This is the modulus
of continuity that a spectral degree bound alone supplies. -/
theorem abs_sub_genTrigCost_le {a b : ℕ → ℝ} {R : ℕ} (hR : 1 ≤ R) {M : ℝ}
    (hM : ∀ x : ℝ, |genTrigCost a b R x| ≤ M) (x y : ℝ) :
    |genTrigCost a b R x - genTrigCost a b R y| ≤ (R : ℝ) * M * |x - y| := by
  have hdiff : ∀ z : ℝ, DifferentiableAt ℝ (genTrigCost a b R) z := fun z =>
    (hasDerivAt_genTrigCost a b R z).differentiableAt
  have hbound : ∀ z ∈ Set.uIcc y x, ‖deriv (genTrigCost a b R) z‖ ≤ (R : ℝ) * M := by
    intro z _
    simpa [Real.norm_eq_abs] using abs_deriv_genTrigCost_le hR hM z
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := genTrigCost a b R)
    (fun z _ => hdiff z) hbound (convex_uIcc y x) (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  simpa [Real.norm_eq_abs] using this

end GaloisForLFunctions.HTGeometry
