import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.SmoothParabolicInduction

/-! If a set of coset representatives normalizes the fixed subgroup,
evaluation of a fixed vector gives invariants in the inducing
representation under the preimage of that subgroup. -/

noncomputable section

namespace Representation

variable {G H V : Type*} [Group G] [Group H] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] (f : H →* G) (ρ : Representation ℂ H V)

theorem exists_nonzero_fixed_inducing_vector (K C : Subgroup G)
    (hdecomp : ∀ g : G, ∃ h : H, ∃ c : C, g = f h * c.val)
    (hnorm : ∀ c : C, ∀ k ∈ K, c.val⁻¹ * k * c.val ∈ K)
    (u : (coind f ρ).smoothVectors) (hu : ∀ k : K, smoothInduction f ρ k.val u = u)
    (hu₀ : u ≠ 0) : ∃ v : V, v ≠ 0 ∧ ∀ h : K.comap f, ρ h.val v = v := by
  have hval : ∃ g : G, u.val.val g ≠ 0 := by
    by_contra! h
    exact hu₀ (Subtype.ext (Subtype.ext (funext h)))
  obtain ⟨g, hg⟩ := hval
  obtain ⟨h, c, rfl⟩ := hdecomp g
  rw [smoothInduction_equivariance f ρ u] at hg
  refine ⟨u.val.val c.val, fun hz => hg (by rw [hz, map_zero]), fun h => ?_⟩
  let k : K := ⟨c.val⁻¹ * f h.val * c.val, hnorm c _ h.2⟩
  have he : f h.val * c.val = c.val * k.val := by simp [k, mul_assoc]
  rw [← smoothInduction_equivariance f ρ u, he]
  exact congrArg (fun w : (coind f ρ).smoothVectors => w.val.val c.val) (hu k)

theorem smoothInduction_scalar_of_central (h : H) (hc : ∀ g : G, g * f h = f h * g)
    (a : ℂ) (hρ : ∀ w : V, ρ h w = a • w) (u : (coind f ρ).smoothVectors) :
    smoothInduction f ρ (f h) u = a • u := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change u.val.val (g * f h) = a • u.val.val g
  rw [hc, smoothInduction_equivariance f ρ u, hρ]

end Representation

#print axioms Representation.exists_nonzero_fixed_inducing_vector
