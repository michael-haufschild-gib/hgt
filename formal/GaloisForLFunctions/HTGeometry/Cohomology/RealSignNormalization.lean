import GaloisForLFunctions.HTGeometry.Cohomology.FiniteCocycleAveraging
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Positive normalization of finite real scalar cocycles

A finite-group cocycle with values in the nonzero real numbers can be
normalized by positive scalars to its sign cocycle. Taking logarithms of
absolute values reduces the positive part to additive cocycle averaging.
Thus the remaining obstruction has values in the two-element sign group.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.Cohomology

open RHTower

variable {G : Type*}

/-- The sign of a scalar cochain, expressed without a separate sign type. -/
def signCochain (c : G → G → ℝ) (g h : G) : ℝ := c g h / |c g h|

theorem signCochain_eq_one_or_neg_one (c : G → G → ℝ)
    (hc : ∀ g h, c g h ≠ 0) (g h : G) :
    signCochain c g h = 1 ∨ signCochain c g h = -1 := by
  by_cases hpos : 0 < c g h
  · exact Or.inl (by rw [signCochain, abs_of_pos hpos, div_self (hc g h)])
  · exact Or.inr (by
      rw [signCochain, abs_of_nonpos (le_of_not_gt hpos), div_neg, div_self (hc g h)])

variable [Group G]

/-- Taking signs preserves the scalar cocycle identity. -/
theorem signCochain_cocycle (c : G → G → ℝ)
    (hc : ∀ g h k, c g h * c (g * h) k = c h k * c g (h * k)) (g h k : G) :
    signCochain c g h * signCochain c (g * h) k =
      signCochain c h k * signCochain c g (h * k) := by
  simp only [signCochain, div_mul_div_comm, ← abs_mul]
  rw [hc]

variable [Fintype G]

/-- Scalar additive cocycles are coboundaries, by the same averaging
primitive as for arbitrary linear coefficient actions. -/
theorem finite_real_additive_cocycle (L : G → G → ℝ)
    (hL : ∀ g h k, L g h + L (g * h) k = L h k + L g (h * k)) :
    ∃ b : G → ℝ, ∀ g h, L g h = b g + b h - b (g * h) := by
  letI : DistribMulAction G ℝ :=
    { smul := fun _ x => x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_zero := fun _ => rfl
      smul_add := fun _ _ _ => rfl }
  letI : SMulCommClass G ℝ ℝ := ⟨fun _ _ _ => rfl⟩
  have hω : IsTwoCocycle L := by
    intro g h k
    change L h k + L g (h * k) = L (g * h) k + L g h
    linarith only [hL g h k]
  let b := finiteCocycleAverage (K := ℝ) L
  refine ⟨b, ?_⟩
  intro g h
  have hh := congrFun (congrFun (isTwoCocycle_eq_twoCoboundary_average (K := ℝ) hω) g) h
  change L g h = b h - b (g * h) + b g at hh
  linarith only [hh]

/-- Every finite nonzero real scalar cocycle becomes its sign cocycle
after a positive change of one-cochain. -/
theorem finite_real_cocycle_positive_normalization (c : G → G → ℝ)
    (hc0 : ∀ g h, c g h ≠ 0)
    (hc : ∀ g h k, c g h * c (g * h) k = c h k * c g (h * k)) :
    ∃ a : G → ℝ, (∀ g, 0 < a g) ∧
      ∀ g h, (a g * a h / a (g * h)) * c g h = signCochain c g h := by
  let L : G → G → ℝ := fun g h => Real.log |c g h|
  have hL : ∀ g h k, L g h + L (g * h) k = L h k + L g (h * k) := by
    intro g h k
    dsimp only [L]
    rw [← Real.log_mul (abs_ne_zero.mpr (hc0 g h)) (abs_ne_zero.mpr (hc0 (g * h) k)),
      ← Real.log_mul (abs_ne_zero.mpr (hc0 h k)) (abs_ne_zero.mpr (hc0 g (h * k))),
      ← abs_mul, ← abs_mul, hc]
  obtain ⟨b, hb⟩ := finite_real_additive_cocycle L hL
  refine ⟨fun g => Real.exp (-b g), fun g => Real.exp_pos _, ?_⟩
  intro g h
  have hexponent : -b g + -b h - -b (g * h) = -Real.log |c g h| := by
    have heq := hb g h
    dsimp only [L] at heq
    linarith only [heq]
  have hscale : Real.exp (-b g) * Real.exp (-b h) / Real.exp (-b (g * h)) =
      |c g h|⁻¹ := by
    rw [← Real.exp_add, ← Real.exp_sub, hexponent, Real.exp_neg,
      Real.exp_log (abs_pos.mpr (hc0 g h))]
  change (Real.exp (-b g) * Real.exp (-b h) / Real.exp (-b (g * h))) * c g h = _
  rw [hscale, signCochain, div_eq_mul_inv, mul_comm]

/-- Positive real cocycles are exactly positive scalar coboundaries. -/
theorem finite_positive_real_cocycle (c : G → G → ℝ)
    (hc0 : ∀ g h, 0 < c g h)
    (hc : ∀ g h k, c g h * c (g * h) k = c h k * c g (h * k)) :
    ∃ a : G → ℝ, (∀ g, 0 < a g) ∧
      ∀ g h, (a g * a h / a (g * h)) * c g h = 1 := by
  obtain ⟨a, ha, heq⟩ := finite_real_cocycle_positive_normalization c
    (fun g h => (hc0 g h).ne') hc
  refine ⟨a, ha, fun g h => ?_⟩
  rw [heq, signCochain, abs_of_pos (hc0 g h), div_self (hc0 g h).ne']

#print axioms finite_real_cocycle_positive_normalization
#print axioms finite_positive_real_cocycle
#print axioms signCochain_cocycle

end GaloisForLFunctions.HTGeometry.Cohomology
