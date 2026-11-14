import GaloisForLFunctions.DilutionCrystallizationPincer.EisensteinCommensurability
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicCuspPeriodLattice

/-!
# Incommensurate samples determine a continuous cubic-periodic function

The full-plane density alternative for two Eisenstein lattices applies to
the actual cusp period lattice `3 ℤ[ω]`. Two continuous periodic functions
that agree on an incommensurate triangular coset agree everywhere.
No analyticity or Fourier convergence assumption is needed.
-/

noncomputable section
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

open Eisenstein Set
open DilutionCrystallizationPincer.EisensteinCommensurability
open FamilyContinuationTheory.EisensteinNorm

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]

/-- Dense mixed-lattice samples determine a continuous function with the cubic cusp periods. -/
theorem eq_of_incommensurate_samples (α c : ℂ) (hα : mixedClosure α = ⊤)
    (f g : ℂ → Y) (hf : Continuous f) (hg : Continuous g)
    (hfper : ∀ p : periodLattice, Function.Periodic f (p : ℂ))
    (hgper : ∀ p : periodLattice, Function.Periodic g (p : ℂ))
    (hsample : ∀ a : O, f (c + 3 * α * ringComplex a) = g (c + 3 * α * ringComplex a)) :
    f = g := by
  let S : Set ℂ := {z | f (c + 3 * z) = g (c + 3 * z)}
  have hc : Continuous (fun z : ℂ => c + 3 * z) :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hS : IsClosed S := isClosed_eq (hf.comp hc) (hg.comp hc)
  have hper : ∀ z ∈ S, ∀ a : O, z + ringComplex a ∈ S := by
    intro z hz a
    have heq : c + 3 * (z + ringComplex a) = (c + 3 * z) + (periodPoint a : ℂ) := by
      rw [periodPoint_val]
      ring
    change f (c + 3 * (z + ringComplex a)) = g (c + 3 * (z + ringComplex a))
    rw [heq, hfper (periodPoint a), hgper (periodPoint a)]
    exact hz
  have hcoset : ∀ a : O, (0 : ℂ) + α * ringComplex a ∈ S := by
    intro a
    change f (c + 3 * (0 + α * ringComplex a)) = g (c + 3 * (0 + α * ringComplex a))
    simpa only [zero_add, mul_assoc] using hsample a
  have hall := closed_periodic_set_eq_univ α 0 hα S hS hper hcoset
  funext z
  have hz : (z - c) / 3 ∈ S := by rw [hall]; exact mem_univ _
  change f (c + 3 * ((z - c) / 3)) = g (c + 3 * ((z - c) / 3)) at hz
  have heq : c + 3 * ((z - c) / 3) = z := by ring
  simpa only [heq] using hz

/-- A nonrepresented integral squared scale is a sufficient arithmetic sampling criterion. -/
theorem eq_of_nonnorm_samples (α c : ℂ) (n : ℕ) (hnorm : ‖α‖ ^ 2 = n)
    (hn : ¬ (normSet n).Nonempty)
    (f g : ℂ → Y) (hf : Continuous f) (hg : Continuous g)
    (hfper : ∀ p : periodLattice, Function.Periodic f (p : ℂ))
    (hgper : ∀ p : periodLattice, Function.Periodic g (p : ℂ))
    (hsample : ∀ a : O, f (c + 3 * α * ringComplex a) = g (c + 3 * α * ringComplex a)) :
    f = g :=
  eq_of_incommensurate_samples α c
    (mixedClosure_eq_top_of_norm_not_represented α n hnorm hn) f g hf hg hfper hgper hsample

/-- Sampling on a square-root-of-two triangular coset has no arithmetic side condition. -/
theorem eq_of_sqrt_two_samples (c : ℂ) (f g : ℂ → Y) (hf : Continuous f) (hg : Continuous g)
    (hfper : ∀ p : periodLattice, Function.Periodic f (p : ℂ))
    (hgper : ∀ p : periodLattice, Function.Periodic g (p : ℂ))
    (hsample : ∀ a : O,
      f (c + 3 * (Real.sqrt 2 : ℂ) * ringComplex a) =
        g (c + 3 * (Real.sqrt 2 : ℂ) * ringComplex a)) : f = g :=
  eq_of_incommensurate_samples (Real.sqrt 2 : ℂ) c mixedClosure_sqrt_two_eq_top
    f g hf hg hfper hgper hsample

/-- An extra incommensurate pair of triangular periods makes a continuous cubic-periodic function constant. -/
theorem constant_of_nonnorm_periods (α : ℂ) (n : ℕ) (hnorm : ‖α‖ ^ 2 = n)
    (hn : ¬ (normSet n).Nonempty) (f : ℂ → Y) (hf : Continuous f)
    (hfper : ∀ p : periodLattice, Function.Periodic f (p : ℂ))
    (hextra : ∀ a : O, Function.Periodic f (3 * α * ringComplex a)) :
    ∀ z : ℂ, f z = f 0 := by
  have heq := eq_of_nonnorm_samples α 0 n hnorm hn f (fun _ => f 0) hf continuous_const
    hfper (fun _ _ => rfl) (fun a => by simpa only [zero_add] using hextra a 0)
  exact fun z => congrFun heq z

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.eq_of_nonnorm_samples
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.eq_of_sqrt_two_samples
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.constant_of_nonnorm_periods
