import GaloisForLFunctions.HTGeometry.EntireZeroFactorization

/-!
# Continuous analytic families do not preserve pointwise multiplicity parity

The polynomial family

`F(t,z) = z^(2 : ℕ) - t^(2 : ℕ)`

is jointly continuous and every parameter slice is entire.  At `t = 0` it has a double zero at
the origin, whereas for every `t != 0` it has a simple zero at `z = t`.  Thus continuity of an
analytic family does not by itself define a pointwise even-multiplicity class.  What is stable
under a deformation avoiding zeros on a fixed contour is the total enclosed multiplicity, not the
parity of each moving zero after collisions or splittings.
-/

open Complex

namespace RHTower

noncomputable section

/-- Elementary jointly polynomial family in which one double zero splits into two simple zeros. -/
def continuousAnalyticParitySplit (t z : ℂ) : ℂ := z ^ (2 : ℕ) - t ^ (2 : ℕ)

/-- The family is jointly continuous in parameter and analytic variable. -/
theorem continuous_continuousAnalyticParitySplit :
    Continuous (fun p : ℂ × ℂ => continuousAnalyticParitySplit p.1 p.2) := by
  change Continuous (fun p : ℂ × ℂ => p.2 ^ (2 : ℕ) - p.1 ^ (2 : ℕ))
  fun_prop

/-- Every fixed-parameter member is entire. -/
theorem analyticOnNhd_continuousAnalyticParitySplit (t : ℂ) :
    AnalyticOnNhd ℂ (continuousAnalyticParitySplit t) Set.univ := by
  intro z _hz
  change AnalyticAt ℂ (fun w : ℂ => w ^ (2 : ℕ) - t ^ (2 : ℕ)) z
  fun_prop

/-- The collision member has even order two at the origin. -/
theorem analyticOrderAt_continuousAnalyticParitySplit_zero :
    analyticOrderAt (continuousAnalyticParitySplit 0) 0 = (2 : ℕ∞) := by
  change analyticOrderAt (fun z : ℂ => z ^ (2 : ℕ) - 0 ^ (2 : ℕ)) 0 = (2 : ℕ∞)
  simpa using
    (GaloisForLFunctions.HTGeometry.analyticOrderAt_sub_pow_self (0 : ℂ) 2)

/-- Away from the collision, the moving zero `z = t` is simple. -/
theorem analyticOrderAt_continuousAnalyticParitySplit_self_of_ne_zero
    {t : ℂ} (ht : t ≠ 0) :
    analyticOrderAt (continuousAnalyticParitySplit t) t = (1 : ℕ∞) := by
  have htneg : t ≠ -t := by
    intro h
    apply ht
    linear_combination (1 / 2 : ℂ) * h
  have hfun : continuousAnalyticParitySplit t =
      fun z : ℂ => (z - t) ^ (1 : ℕ) * (z - (-t)) ^ (1 : ℕ) := by
    funext z
    simp [continuousAnalyticParitySplit]
    ring
  rw [hfun]
  change analyticOrderAt
      ((fun z : ℂ => (z - t) ^ (1 : ℕ)) * (fun z : ℂ => (z - (-t)) ^ (1 : ℕ))) t =
    (1 : ℕ∞)
  rw [analyticOrderAt_mul,
    GaloisForLFunctions.HTGeometry.analyticOrderAt_sub_pow_self,
    GaloisForLFunctions.HTGeometry.analyticOrderAt_sub_pow_of_ne (-t) 1 htneg]
  · simp
  · exact GaloisForLFunctions.HTGeometry.analyticAt_sub_pow t 1 t
  · exact GaloisForLFunctions.HTGeometry.analyticAt_sub_pow (-t) 1 t

/-- Packaged countermodel to pointwise parity invariance under continuous analytic deformation. -/
theorem exists_continuous_entire_family_even_collision_with_simple_splits :
    ∃ F : ℂ → ℂ → ℂ,
      Continuous (fun p : ℂ × ℂ => F p.1 p.2) ∧
      (∀ t, AnalyticOnNhd ℂ (F t) Set.univ) ∧
      analyticOrderAt (F 0) 0 = (2 : ℕ∞) ∧
      ∀ t, t ≠ 0 → analyticOrderAt (F t) t = (1 : ℕ∞) := by
  exact ⟨continuousAnalyticParitySplit,
    continuous_continuousAnalyticParitySplit,
    analyticOnNhd_continuousAnalyticParitySplit,
    analyticOrderAt_continuousAnalyticParitySplit_zero,
    fun _ ht => analyticOrderAt_continuousAnalyticParitySplit_self_of_ne_zero ht⟩

end

end RHTower
