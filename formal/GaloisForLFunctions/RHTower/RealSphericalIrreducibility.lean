import GaloisForLFunctions.RHTower.RealSphericalHarishChandra

/-!
# Irreducibility of the real spherical complementary-series module

A Harish-Chandra submodule is closed under the spherical `K`-type projections and the
`sl₂` raising and lowering operators.  For `|s| < 1`, every raising and lowering coefficient is
nonzero.  Starting from one nonzero `K`-type component therefore generates every basis vector,
which proves algebraic `(𝔤,K)`-irreducibility of the spherical principal-series model throughout
the complementary interval.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- A `(𝔤,K)`-submodule of the spherical principal-series model: closed under its `K`-type
projections and the raising/lowering operators. -/
def IsSphericalHarishChandraSubmodule (s : ℝ)
    (W : Submodule ℂ SphericalKFiniteModel) : Prop :=
  (∀ v ∈ W, ∀ m : ℤ, Finsupp.single m (v m) ∈ W) ∧
    (∀ v ∈ W, sphericalPrincipalE (s : ℂ) v ∈ W) ∧
      ∀ v ∈ W, sphericalPrincipalF (s : ℂ) v ∈ W

theorem sphericalPrincipalE_coefficient_ne_zero (s : ℝ) (hs : |s| < 1) (m : ℤ) :
    ((s : ℂ) - 1 - 2 * (m : ℂ)) / 2 ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  norm_num at hre
  have hs' := abs_lt.mp hs
  have hmleft : (-1 : ℝ) < (m : ℝ) := by linarith
  have hmright : (m : ℝ) < 0 := by linarith
  have hmleft' : (-1 : ℤ) < m := by exact_mod_cast hmleft
  have hmright' : m < 0 := by exact_mod_cast hmright
  omega

theorem sphericalPrincipalF_coefficient_ne_zero (s : ℝ) (hs : |s| < 1) (m : ℤ) :
    ((s : ℂ) - 1 + 2 * (m : ℂ)) / 2 ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  norm_num at hre
  have hs' := abs_lt.mp hs
  have hmleft : (0 : ℝ) < (m : ℝ) := by linarith
  have hmright : (m : ℝ) < 1 := by linarith
  have hmleft' : (0 : ℤ) < m := by exact_mod_cast hmleft
  have hmright' : m < 1 := by exact_mod_cast hmright
  omega

theorem sphericalHarishChandraSubmodule_single_succ
    (s : ℝ) (hs : |s| < 1) (W : Submodule ℂ SphericalKFiniteModel)
    (hW : IsSphericalHarishChandraSubmodule s W) (m : ℤ)
    (hm : Finsupp.single m 1 ∈ W) :
    Finsupp.single (m + 1) 1 ∈ W := by
  let c : ℂ := ((s : ℂ) - 1 - 2 * (m : ℂ)) / 2
  have hc : c ≠ 0 := sphericalPrincipalE_coefficient_ne_zero s hs m
  have hE : Finsupp.single (m + 1) (c * 1) ∈ W := by
    simpa [c] using hW.2.1 _ hm
  have hscaled := W.smul_mem c⁻¹ hE
  simpa only [Finsupp.smul_single, smul_eq_mul, mul_one,
    inv_mul_cancel₀ hc] using hscaled

theorem sphericalHarishChandraSubmodule_single_pred
    (s : ℝ) (hs : |s| < 1) (W : Submodule ℂ SphericalKFiniteModel)
    (hW : IsSphericalHarishChandraSubmodule s W) (m : ℤ)
    (hm : Finsupp.single m 1 ∈ W) :
    Finsupp.single (m - 1) 1 ∈ W := by
  let c : ℂ := ((s : ℂ) - 1 + 2 * (m : ℂ)) / 2
  have hc : c ≠ 0 := sphericalPrincipalF_coefficient_ne_zero s hs m
  have hF : Finsupp.single (m - 1) (c * 1) ∈ W := by
    simpa [c] using hW.2.2 _ hm
  have hscaled := W.smul_mem c⁻¹ hF
  simpa only [Finsupp.smul_single, smul_eq_mul, mul_one,
    inv_mul_cancel₀ hc] using hscaled

theorem sphericalHarishChandraSubmodule_all_single
    (s : ℝ) (hs : |s| < 1) (W : Submodule ℂ SphericalKFiniteModel)
    (hW : IsSphericalHarishChandraSubmodule s W) (m : ℤ)
    (hm : Finsupp.single m 1 ∈ W) :
    ∀ n : ℤ, Finsupp.single n 1 ∈ W := by
  intro n
  exact Int.inductionOn' n m hm
    (fun k _ hk ↦ sphericalHarishChandraSubmodule_single_succ s hs W hW k hk)
    (fun k _ hk ↦ sphericalHarishChandraSubmodule_single_pred s hs W hW k hk)

/-- The spherical Harish-Chandra model is irreducible throughout the complementary interval. -/
theorem sphericalPrincipal_irreducible_of_abs_lt_one (s : ℝ) (hs : |s| < 1) :
    ∀ W : Submodule ℂ SphericalKFiniteModel,
      IsSphericalHarishChandraSubmodule s W → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨v, hvW, hvzero⟩ := (Submodule.ne_bot_iff W).mp hbot
    obtain ⟨m, hm⟩ := Finsupp.support_nonempty_iff.mpr hvzero
    have hvm : v m ≠ 0 := Finsupp.mem_support_iff.mp hm
    have hproject : Finsupp.single m (v m) ∈ W := hW.1 v hvW m
    have hunitScaled := W.smul_mem (v m)⁻¹ hproject
    have hunit : Finsupp.single m 1 ∈ W := by
      simpa [Finsupp.smul_single, hvm] using hunitScaled
    have hall := sphericalHarishChandraSubmodule_all_single s hs W hW m hunit
    rw [Submodule.eq_top_iff']
    intro x
    induction x using Finsupp.induction_linear with
    | zero => exact W.zero_mem
    | add x y hx hy => exact W.add_mem hx hy
    | single n z =>
        have hz := W.smul_mem z (hall n)
        simpa [Finsupp.smul_single] using hz

end
end GaloisForLFunctions.RHTower
