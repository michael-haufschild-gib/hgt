import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatConvexRigidity

/-!
# Strict convexity with vanishing curvature at the minimizer

Reflecting the flat potential removes its flat half-line without removing
infinite smoothness. The resulting even potential is strictly convex,
has a unique critical point, and still has a contractive gradient whose
derivative vanishes at that point. Thus uniqueness and strict convexity
do not supply a positive curvature bound.
-/

open Set
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
noncomputable section

def evenPotential (t : ℝ) : ℝ := potential t + potential (-t)

def evenGradient (t : ℝ) : ℝ := gradient t - gradient (-t)

@[simp] theorem evenPotential_zero : evenPotential 0 = 0 := by
  simp only [evenPotential, neg_zero, potential_zero, add_zero]

@[simp] theorem evenGradient_zero : evenGradient 0 = 0 := by
  simp only [evenGradient, neg_zero, sub_self]

theorem evenPotential_neg (t : ℝ) : evenPotential (-t) = evenPotential t := by
  simp only [evenPotential, neg_neg, add_comm]

theorem evenGradient_neg (t : ℝ) : evenGradient (-t) = -evenGradient t := by
  simp only [evenGradient, neg_neg, neg_sub]

theorem evenPotential_contDiff (n : ℕ∞) : ContDiff ℝ n evenPotential :=
  (potential_contDiff n).add ((potential_contDiff n).comp contDiff_id.neg)

theorem evenGradient_contDiff (n : ℕ∞) : ContDiff ℝ n evenGradient :=
  (gradient_contDiff n).sub ((gradient_contDiff n).comp contDiff_id.neg)

theorem evenPotential_hasDerivAt (t : ℝ) :
    HasDerivAt evenPotential (evenGradient t) t := by
  have h : HasDerivAt evenPotential (gradient t + gradient (-t) * (-1)) t :=
    (potential_hasDerivAt t).add
      ((potential_hasDerivAt (-t)).comp t (hasDerivAt_id t).neg)
  simpa only [evenGradient, mul_neg_one, ← sub_eq_add_neg] using h

theorem evenGradient_hasDerivAt (t : ℝ) :
    HasDerivAt evenGradient (expNegInvGlue t + expNegInvGlue (-t)) t := by
  have h : HasDerivAt evenGradient (expNegInvGlue t - expNegInvGlue (-t) * (-1)) t :=
    (gradient_hasDerivAt t).sub
      ((gradient_hasDerivAt (-t)).comp t (hasDerivAt_id t).neg)
  simpa only [mul_neg_one, sub_neg_eq_add] using h

private theorem even_curvature_bounds (t : ℝ) :
    0 ≤ expNegInvGlue t + expNegInvGlue (-t) ∧
      expNegInvGlue t + expNegInvGlue (-t) ≤ 1 := by
  constructor
  · exact add_nonneg (curvature_bounds t).1 (curvature_bounds (-t)).1
  · rcases le_total t 0 with ht | ht
    · rw [expNegInvGlue.zero_of_nonpos ht, zero_add]
      exact (curvature_bounds (-t)).2
    · rw [expNegInvGlue.zero_of_nonpos (neg_nonpos.mpr ht), add_zero]
      exact (curvature_bounds t).2

/-- Reflection preserves the global unit contraction bound. -/
theorem evenGradient_contraction : LipschitzWith 1 evenGradient := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t => (evenGradient_hasDerivAt t).differentiableAt)
  intro t
  change ‖deriv evenGradient t‖ ≤ (1 : ℝ)
  rw [(evenGradient_hasDerivAt t).deriv, Real.norm_eq_abs,
    abs_of_nonneg (even_curvature_bounds t).1]
  exact (even_curvature_bounds t).2

/-- Opposite flat half-lines cannot identify two distinct real arguments. -/
theorem evenGradient_strictMono : StrictMono evenGradient := by
  intro x y hxy
  have h₁ := gradient_monotone hxy.le
  have h₂ := gradient_monotone (neg_le_neg hxy.le)
  by_contra hn
  have he : gradient x = gradient y := by
    change ¬ gradient x - gradient (-x) < gradient y - gradient (-y) at hn
    linarith only [h₁, h₂, le_of_not_gt hn]
  have he' : gradient (-y) = gradient (-x) := by
    change ¬ gradient x - gradient (-x) < gradient y - gradient (-y) at hn
    linarith only [h₁, h₂, le_of_not_gt hn]
  rcases (gradient_eq_iff x y).mp he with he | ⟨hx, hy⟩
  · exact hxy.ne he
  rcases (gradient_eq_iff (-y) (-x)).mp he' with he' | ⟨hy', hx'⟩
  · linarith only [hxy, he']
  · linarith only [hxy, hx, hy, hx', hy']

/-- Strict convexity survives infinite flatness at the unique minimum. -/
theorem evenPotential_strictConvex : StrictConvexOn ℝ univ evenPotential := by
  apply StrictMonoOn.strictConvexOn_of_deriv convex_univ
    (evenPotential_contDiff 0).continuous.continuousOn
  intro x _ y _ hxy
  simpa only [(evenPotential_hasDerivAt x).deriv,
    (evenPotential_hasDerivAt y).deriv] using evenGradient_strictMono hxy

theorem evenGradient_zero_iff (t : ℝ) : evenGradient t = 0 ↔ t = 0 := by
  constructor
  · intro h
    exact evenGradient_strictMono.injective (h.trans evenGradient_zero.symm)
  · rintro rfl
    exact evenGradient_zero

/-- The even potential is bounded above quadratically and vanishes only at zero. -/
theorem evenPotential_bounds (t : ℝ) :
    0 ≤ evenPotential t ∧ evenPotential t ≤ t ^ 2 / 2 := by
  refine ⟨add_nonneg (potential_bounds t).1 (potential_bounds (-t)).1, ?_⟩
  rcases le_total t 0 with ht | ht
  · rw [evenPotential, (potential_zero_iff t).mpr ht, zero_add]
    simpa only [neg_sq] using (potential_bounds (-t)).2
  · rw [evenPotential, (potential_zero_iff (-t)).mpr (neg_nonpos.mpr ht), add_zero]
    exact (potential_bounds t).2

theorem evenPotential_zero_iff (t : ℝ) : evenPotential t = 0 ↔ t = 0 := by
  constructor
  · intro h
    have hp : potential t = 0 := by
      change potential t + potential (-t) = 0 at h
      linarith only [h, (potential_bounds t).1, (potential_bounds (-t)).1]
    have hn : potential (-t) = 0 := by
      change potential t + potential (-t) = 0 at h
      linarith only [h, (potential_bounds t).1, (potential_bounds (-t)).1]
    have ht := (potential_zero_iff t).mp hp
    have ht' := (potential_zero_iff (-t)).mp hn
    linarith only [ht, ht']
  · rintro rfl
    exact evenPotential_zero

/-- Reflection turns the flat half-line loss into a loss of absolute amplitude. -/
theorem evenPotential_eq_potential_abs (t : ℝ) : evenPotential t = potential |t| := by
  rcases le_total t 0 with ht | ht
  · rw [evenPotential, (potential_zero_iff t).mpr ht, zero_add, abs_of_nonpos ht]
  · rw [evenPotential, (potential_zero_iff (-t)).mpr (neg_nonpos.mpr ht),
      add_zero, abs_of_nonneg ht]

private theorem potential_monotone : Monotone potential := by
  apply monotone_of_deriv_nonneg (fun t => (potential_hasDerivAt t).differentiableAt)
  intro t
  rw [(potential_hasDerivAt t).deriv]
  exact gradient_nonneg t

/-- Absolute jump domination implies domination of the nonlinear jump charge. -/
theorem evenPotential_le_of_abs_le {x y : ℝ} (h : |x| ≤ |y|) :
    evenPotential x ≤ evenPotential y := by
  rw [evenPotential_eq_potential_abs, evenPotential_eq_potential_abs]
  exact potential_monotone h

/-- No positive lower curvature bound exists, even at the unique minimizer. -/
theorem evenGradient_deriv_zero : deriv evenGradient 0 = 0 := by
  rw [(evenGradient_hasDerivAt 0).deriv]
  simp only [neg_zero, expNegInvGlue.zero, add_zero]

#print axioms evenPotential_strictConvex
#print axioms evenGradient_contraction
#print axioms evenGradient_zero_iff
#print axioms evenPotential_zero_iff
#print axioms evenGradient_deriv_zero
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
