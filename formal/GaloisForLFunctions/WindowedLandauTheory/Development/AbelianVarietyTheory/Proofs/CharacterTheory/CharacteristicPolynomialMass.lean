import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobius
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Isomorphisms

/-! The distribution of a class function by characteristic polynomial. -/

open Polynomial

namespace GlobalTheory.CuspGL

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- Sum a weight over the endomorphisms with a fixed characteristic polynomial. -/
def mass (φ : Module.End F V → ℂ) (P : F[X]) : ℂ :=
  ∑ᶠ g ∈ {g : Module.End F V | LinearMap.charpoly g = P}, φ g

/-- The order of the finite general linear group, regarded as a complex scalar. -/
def glCard (F : Type) [Field F] (n : ℕ) : ℂ := (Nat.card (GL (Fin n) F) : ℂ)

theorem glCard_ne_zero_of_finite (F : Type) [Field F] [Finite F] (n : ℕ) :
    glCard F n ≠ 0 := by
  unfold glCard
  exact_mod_cast (Nat.card_pos (α := GL (Fin n) F)).ne'

/-- The characteristic-polynomial mass of the constant weight, divided by the group order. -/
def mu (P : F[X]) : ℂ :=
  mass (fun _ : Module.End F (Fin P.natDegree → F) => (1 : ℂ)) P / glCard F P.natDegree

/-- An additive polynomial weight supported on positive powers of monic irreducibles. -/
def mangoldt (s : F[X] → ℂ) (P : F[X]) : ℂ :=
  ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ Irreducible f ∧ ∃ m : ℕ, 0 < m ∧ P = f ^ m}, s f

/-- Convolution over ordered monic factorizations. -/
def conv (a b : F[X] → ℂ) (P : F[X]) : ℂ :=
  ∑ᶠ x ∈ {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P}, a x.1 * b x.2

theorem mass_comp_charpoly_eq_mul [Finite F] (s : F[X] → ℂ) (P : F[X]) :
    mass (fun g : Module.End F V => s (LinearMap.charpoly g)) P =
      s P * mass (fun _ : Module.End F V => (1 : ℂ)) P := by
  letI : Finite (Module.End F V) := Module.finite_of_finite F
  have hfin : {g : Module.End F V | LinearMap.charpoly g = P}.Finite := Set.toFinite _
  unfold mass
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  have he : LinearMap.charpoly g = P := by simpa using hg
  simp [he]

theorem mass_eq_mass_pi_of_invariant (Φ : ∀ (W : Type) [AddCommGroup W] [Module F W]
    [FiniteDimensional F W], Module.End F W → ℂ)
    (hΦ : ∀ (W W' : Type) [AddCommGroup W] [Module F W] [FiniteDimensional F W]
      [AddCommGroup W'] [Module F W'] [FiniteDimensional F W'] (e : W ≃ₗ[F] W')
      (g : Module.End F W), Φ W' (e.conj g) = Φ W g)
    (P : F[X]) (hP : P.natDegree = Module.finrank F V) :
    mass (Φ V) P = mass (Φ (Fin P.natDegree → F)) P := by
  let e : V ≃ₗ[F] (Fin P.natDegree → F) := LinearEquiv.ofFinrankEq _ _ (by simp [hP])
  unfold mass
  refine finsum_mem_eq_of_bijOn (fun g => e.conj g) ⟨?_, ?_, ?_⟩ ?_
  · intro g hg
    simpa using hg
  · intro g _ h _ hgh
    simpa using congrArg e.symm.conj hgh
  · intro h hh
    refine ⟨e.symm.conj h, ?_, by simp⟩
    simpa using hh
  · intro g _
    exact (hΦ V _ e g).symm

end GlobalTheory.CuspGL
