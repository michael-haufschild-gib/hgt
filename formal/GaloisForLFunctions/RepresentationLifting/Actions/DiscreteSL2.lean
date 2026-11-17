import GaloisForLFunctions.HTGeometry.Sl2ElementaryFactorization
import GaloisForLFunctions.HTGeometry.LoopEisenstein.SL2RootSplittings
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Triviality of finite-dimensional smooth special-linear actions

Conjugation by powers of a small coroot sends every elementary unipotent
to the identity. A homomorphism continuous at the identity with discrete
codomain must kill these elements. The existing elementary factorization
then kills the whole special linear group.

For a finite-dimensional smooth linear action, intersecting the stabilizers
of a finite basis supplies the required common identity neighborhood. Thus
every such action of `SL₂(K)` is trivial for every nontrivially normed field
`K`, with no restriction on the coefficient field. This extends the unipotent
contraction argument of *A note on finite length for GL₂*, Lemma 2.2.
-/

noncomputable section
open Filter Topology Matrix
namespace GaloisForLFunctions.RepresentationLifting.DiscreteSL2
open HTGeometry.LoopEisenstein

/-- A convergent conjugacy orbit is invisible in every continuous discrete group image. -/
theorem map_one_of_contracting_conjugates {G H : Type*} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H] [DiscreteTopology H]
    (f : G →* H) (hf : ContinuousAt f 1) (g : G) (a : ℕ → G)
    (hlim : Tendsto (fun n => a n * g * (a n)⁻¹) atTop (𝓝 1)) : f g = 1 := by
  have hl := hf.tendsto.comp hlim
  rw [map_one] at hl
  have he : ∀ᶠ j in atTop, f (a j * g * (a j)⁻¹) ∈ ({1} : Set H) :=
    hl.eventually ((isOpen_discrete _).mem_nhds (by simp))
  obtain ⟨j, hj⟩ := he.exists
  change f (a j * g * (a j)⁻¹) = 1 at hj
  simp only [map_mul, map_inv] at hj
  apply mul_left_cancel (a := f (a j))
  simpa only [mul_one] using (mul_inv_eq_one.mp hj)

variable {K : Type*} [NontriviallyNormedField K]

@[simp] theorem diagonal_inv (a : Kˣ) : (sl2Diagonal a)⁻¹ = sl2Diagonal a⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Diagonal, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

/-- The upper root contracts under a small coroot. -/
theorem diagonal_upper (a : Kˣ) (t : K) :
    sl2Diagonal a * sl2Upper t * (sl2Diagonal a)⁻¹ = sl2Upper ((a : K)^2 * t) := by
  rw [diagonal_inv]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Diagonal, sl2Upper, SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, pow_two, mul_comm, mul_left_comm, mul_assoc]

/-- The lower root contracts under the inverse small coroot. -/
theorem diagonal_lower (a : Kˣ) (t : K) :
    sl2Diagonal a⁻¹ * sl2Lower t * (sl2Diagonal a⁻¹)⁻¹ = sl2Lower ((a : K)^2 * t) := by
  rw [diagonal_inv]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Diagonal, sl2Lower, SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, pow_two, mul_comm, mul_left_comm, mul_assoc]

theorem continuous_upper : Continuous (sl2Upper : K → SpecialLinearGroup (Fin 2) K) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> fun_prop

theorem continuous_lower : Continuous (sl2Lower : K → SpecialLinearGroup (Fin 2) K) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> fun_prop

variable {H : Type*} [Group H] [TopologicalSpace H] [DiscreteTopology H]

/-- Every continuous discrete image kills both elementary root groups. -/
theorem roots_trivial (f : SpecialLinearGroup (Fin 2) K →* H) (hf : ContinuousAt f 1) :
    (∀ t : K, f (sl2Upper t) = 1) ∧ (∀ t : K, f (sl2Lower t) = 1) := by
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
  let a (j : ℕ) : Kˣ := Units.mk0 (c^j) (pow_ne_zero j (norm_pos_iff.mp hc0))
  have hlim (t : K) : Tendsto (fun j : ℕ => (c^j)^2 * t) atTop (𝓝 0) := by
    simpa only [zero_pow two_ne_zero, zero_mul] using
      ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc1).pow 2).mul_const t
  constructor
  · intro t
    apply map_one_of_contracting_conjugates f hf (sl2Upper t) (fun j => sl2Diagonal (a j))
    simp only [diagonal_upper]
    have h := continuous_upper.continuousAt.tendsto.comp (hlim t)
    simpa only [a, Units.val_mk0, sl2Upper_zero, Function.comp_def] using h
  · intro t
    apply map_one_of_contracting_conjugates f hf (sl2Lower t) (fun j => sl2Diagonal (a j)⁻¹)
    simp only [diagonal_lower]
    have h := continuous_lower.continuousAt.tendsto.comp (hlim t)
    simpa only [a, Units.val_mk0, sl2Lower_zero, Function.comp_def] using h

/-- Special linear groups over nontrivially normed fields have no nontrivial continuous discrete image. -/
theorem hom_trivial (f : SpecialLinearGroup (Fin 2) K →* H) (hf : ContinuousAt f 1)
    (g : SpecialLinearGroup (Fin 2) K) : f g = 1 := by
  obtain ⟨hu, hl⟩ := roots_trivial f hf
  obtain ⟨x, y, z, w, h⟩ := HTGeometry.exists_elementary_factorization g.val g.property
  have hg : g = sl2Upper x * sl2Lower y * sl2Upper z * sl2Lower w := Subtype.ext h
  rw [hg]
  simp only [map_mul, hu, hl, mul_one]

/-- A smooth finite-dimensional linear action has an open common stabilizer, hence is trivial. -/
theorem finiteDimensional_smooth_trivial {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V]
    (ρ : SpecialLinearGroup (Fin 2) K →* (V ≃ₗ[k] V))
    (hρ : ∀ v : V, ∀ᶠ g in 𝓝 (1 : SpecialLinearGroup (Fin 2) K), ρ g v = v)
    (g : SpecialLinearGroup (Fin 2) K) : ρ g = 1 := by
  letI : TopologicalSpace (V ≃ₗ[k] V) := ⊥
  letI : DiscreteTopology (V ≃ₗ[k] V) := ⟨rfl⟩
  let b := Module.finBasis k V
  have he : ∀ᶠ g in 𝓝 (1 : SpecialLinearGroup (Fin 2) K),
      ∀ i : Fin (Module.finrank k V), ρ g (b i) = b i :=
    Filter.eventually_all.mpr (fun i => hρ (b i))
  have hk : ∀ᶠ g in 𝓝 (1 : SpecialLinearGroup (Fin 2) K), ρ g = 1 := by
    filter_upwards [he] with g hg
    apply LinearEquiv.toLinearMap_injective
    exact b.ext (fun i => hg i)
  apply hom_trivial ρ ?_ g
  change Tendsto ρ (𝓝 1) (𝓝 (ρ 1))
  rw [map_one]
  exact tendsto_const_nhds.congr' (Filter.Eventually.mono hk (fun _ h => h.symm))

#print axioms finiteDimensional_smooth_trivial
#print axioms map_one_of_contracting_conjugates
#print axioms roots_trivial
#print axioms hom_trivial

end GaloisForLFunctions.RepresentationLifting.DiscreteSL2
