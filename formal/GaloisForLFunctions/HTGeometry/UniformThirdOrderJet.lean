import GaloisForLFunctions.HTGeometry.UniformSecondOrderJet

/-!
Uniform third-order endpoint jets.

The literal source-pole strip reaches `Re w > -4`.  Its finite source action needs
three retained endpoint coefficients and an `O(z^3)` remainder, so the existing
second-order horizon interface is insufficient.
-/

namespace GaloisForLFunctions.HTGeometry
open Set Filter Topology
noncomputable section
set_option autoImplicit false

/-- A parameter-uniform endpoint Taylor polynomial through degree two. -/
def HasUniformJet3 (S : Set ℂ) (b : ℝ) (F : ℂ → ℝ → ℂ)
    (c₀ c₁ c₂ : ℂ → ℂ) (C : ℝ) : Prop :=
  ∀ u ∈ S, ∀ z ∈ Ioc (0 : ℝ) b,
    ‖F u z - c₀ u - c₁ u * z - c₂ u * z ^ 2‖ ≤ C * z ^ 3

theorem HasUniformJet3.mono {S T : Set ℂ} {b : ℝ} {F : ℂ → ℝ → ℂ}
    {c₀ c₁ c₂ : ℂ → ℂ} {C : ℝ}
    (h : HasUniformJet3 S b F c₀ c₁ c₂ C) (hT : T ⊆ S) :
    HasUniformJet3 T b F c₀ c₁ c₂ C :=
  fun u hu => h u (hT hu)

theorem HasUniformJet3.mono_radius {S : Set ℂ} {b b' : ℝ} {F : ℂ → ℝ → ℂ}
    {c₀ c₁ c₂ : ℂ → ℂ} {C : ℝ}
    (h : HasUniformJet3 S b F c₀ c₁ c₂ C) (hb : b' ≤ b) :
    HasUniformJet3 S b' F c₀ c₁ c₂ C :=
  fun u hu z hz => h u hu z ⟨hz.1, hz.2.trans hb⟩

/-- A uniformly bounded literal third derivative supplies the degree-two endpoint
Taylor polynomial with its exact cubic remainder order. -/
theorem hasUniformJet3_of_deriv3_bound {S : Set ℂ} {b : ℝ} (hb : 0 ≤ b)
    {F : ℂ → ℝ → ℂ} {C : ℝ}
    (hsmooth : ∀ u ∈ S, ContDiffOn ℝ 3 (F u) (Icc 0 b))
    (hbound : ∀ u ∈ S, ∀ z ∈ Icc (0 : ℝ) b,
      ‖iteratedDerivWithin 3 (F u) (Icc 0 b) z‖ ≤ C) :
    HasUniformJet3 S b F (fun u => F u 0)
      (fun u => derivWithin (F u) (Icc 0 b) 0)
      (fun u => iteratedDerivWithin 2 (F u) (Icc 0 b) 0 / 2) (C / 2) := by
  intro u hu z hz
  have hz' : z ∈ Icc (0 : ℝ) b := ⟨hz.1.le, hz.2⟩
  have h := taylor_mean_remainder_bound (f := F u) (a := 0) (b := b) (C := C) (n := 2) hb
    ((hsmooth u hu).of_le (by norm_num)) hz' (hbound u hu)
  have htay : taylorWithinEval (F u) 2 (Icc 0 b) 0 z =
      F u 0 + derivWithin (F u) (Icc 0 b) 0 * z +
        (iteratedDerivWithin 2 (F u) (Icc 0 b) 0 / 2) * z ^ 2 := by
    rw [taylor_within_apply]
    simp [Finset.sum_range_succ, iteratedDerivWithin_zero, iteratedDerivWithin_one]
    ring
  rw [htay, sub_add_eq_sub_sub] at h
  norm_num [Nat.factorial] at h
  convert h using 1 <;> ring_nf

end
end GaloisForLFunctions.HTGeometry
