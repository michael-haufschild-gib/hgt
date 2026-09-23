import GaloisForLFunctions.HTGeometry.DerivSignMonotone
import GaloisForLFunctions.RHTower.ProlateOneTurningVariation
import GaloisForLFunctions.RHTower.ProlateProportionality

/-!
# Bounded variation of a prolate mode on a compact subband

The prolate eigen-equation has the Sturm form `((1−y²)ψ')' = (χ + c²y²)ψ`.  The right-hand side is
a product of a quadratic and the mode itself, so it vanishes only finitely often: the quadratic has
at most two roots, and the zeros of a nontrivial prolate mode are simple, hence isolated, hence
finite on a compact subband.  Between consecutive zeros of the right-hand side the Sturm flux is
strictly monotone, so the mode has at most one stationary point per cell.  Finitely many monotone
cells plus a sup bound give bounded variation.

The conclusion holds on every compact subinterval of the open aperture, with no asymptotic,
spectral-index, or RH input.
-/

noncomputable section

open Set

namespace RHTower

open HTGeometry

/-- The quadratic `χ + c²y²` has finitely many zeros unless it is identically zero. -/
theorem finite_zeros_prolate_quadratic {χ c : ℝ} (hcχ : χ ≠ 0 ∨ c ≠ 0) (a b : ℝ) :
    {y | y ∈ Icc a b ∧ χ + c ^ (2 : ℕ) * y ^ (2 : ℕ) = 0}.Finite := by
  rcases Set.eq_empty_or_nonempty {y | y ∈ Icc a b ∧ χ + c ^ (2 : ℕ) * y ^ (2 : ℕ) = 0} with h | ⟨y₀, hy₀⟩
  · rw [h]
    exact Set.finite_empty
  · have hc : c ≠ 0 := by
      rcases hcχ with hχ | hc
      · rintro rfl
        exact hχ (by simpa using hy₀.2)
      · exact hc
    refine Set.Finite.subset (Set.toFinite ({y₀, -y₀} : Set ℝ)) ?_
    rintro y ⟨-, hy⟩
    have hsq : (y - y₀) * (y + y₀) = 0 := by
      have hc2 : c ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hc
      have : c ^ (2 : ℕ) * (y ^ (2 : ℕ) - y₀ ^ (2 : ℕ)) = 0 := by linarith [hy, hy₀.2]
      have := (mul_eq_zero.mp this).resolve_left hc2
      linear_combination this
    rcases mul_eq_zero.mp hsq with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by simp only [Set.mem_singleton_iff]; linarith)

/-- **Bounded variation of a prolate mode.**  A nontrivial prolate mode has bounded variation on
every compact subinterval of the open aperture. -/
theorem prolate_boundedVariationOn {c χ a b : ℝ} {ψ : ℝ → ℝ}
    (hab : a ≤ b) (hlo : -1 < a) (hhi : b < 1)
    (h1 : Differentiable ℝ ψ) (h2 : Differentiable ℝ (deriv ψ))
    (he : ∀ y, prolateSLAction c ψ y = χ * ψ y)
    (hnt : ∃ z ∈ Ioo (-1 : ℝ) 1, ψ z ≠ 0) (hcχ : χ ≠ 0 ∨ c ≠ 0) :
    BoundedVariationOn ψ (Icc a b) := by
  have hIcc : Icc a b ⊆ Ioo (-1 : ℝ) 1 := fun x hx =>
    ⟨lt_of_lt_of_le hlo hx.1, lt_of_le_of_lt hx.2 hhi⟩
  have hzψ : {x | x ∈ Icc a b ∧ ψ x = 0}.Finite :=
    finite_zeros_of_deriv_ne_zero (fun x _ => h1 x)
      (fun x hx hzx => prolate_deriv_ne_zero_of_eq_zero h1 h2 he hnt (hIcc hx) hzx)
  have hmul : {x | x ∈ Icc a b ∧ (χ + c ^ (2 : ℕ) * x ^ (2 : ℕ)) * ψ x = 0}.Finite :=
    finite_zeros_mul (finite_zeros_prolate_quadratic hcχ a b) hzψ
  have hS : {x | x ∈ Ioo a b ∧ (χ + c ^ (2 : ℕ) * x ^ (2 : ℕ)) * ψ x = 0}.Finite := by
    refine hmul.subset ?_
    rintro x ⟨hx, hzx⟩
    exact ⟨Ioo_subset_Icc_self hx, hzx⟩
  have hcf : ContinuousOn ψ (Icc a b) := h1.continuous.continuousOn
  have hdf : ContinuousOn (deriv ψ) (Icc a b) := h2.continuous.continuousOn
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcf
  refine boundedVariationOn_of_finite_rhs_zeros hab hcf hdf
    (continuous_sturmFlux_prolate h2).continuousOn
    (fun x _ => deriv_sturmFlux_prolate_eq h2 he x)
    (((continuous_const.add ((continuous_const.mul (continuous_pow 2)))).mul
      h1.continuous).continuousOn)
    hS.toFinset (fun x hx => (hS.mem_toFinset.mp hx).1)
    (fun x hx hzx => hS.mem_toFinset.mpr ⟨hx, hzx⟩) B ?_
  intro x hx
  simpa [Real.norm_eq_abs] using hB x hx

end RHTower
