import GaloisForLFunctions.HTGeometry.CauchyJetControllability
import GaloisForLFunctions.HTGeometry.SmallPerturbationReach
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Small mass perturbations reach every nearby Cauchy jet packet

Real Cauchy-jet controllability says that finitely supported real masses on an infinite injective
real support realize every finite complex jet packet.  Equivalently the Cauchy-jet columns span the
packet space over the reals.

A spanning family of a finite-dimensional space reaches a neighbourhood of the origin already with
arbitrarily small multiplicative perturbations of finitely many of its coefficients.  So finitely
many atoms, rescaled by factors arbitrarily close to one, move the jet packet through a whole
neighbourhood -- exactly the controllability a transversality argument consumes.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The Cauchy-jet columns span the packet space over the reals.** -/
theorem span_range_cauchyJetColumn_eq_top {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Infinite κ]
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (t : κ → ℝ) (ht : Function.Injective t) :
    Submodule.span ℝ (Set.range (cauchyJetColumn x n fun a => (t a : ℂ))) = ⊤ := by
  have hsurj := cauchyJetRealLinearCombination_surjective x hx hupper n t ht
  have hrange : LinearMap.range (cauchyJetRealLinearCombination x n t) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  rw [cauchyJetRealLinearCombination, Finsupp.range_linearCombination] at hrange
  exact hrange

/-- **Small multiplicative mass perturbations reach a neighbourhood of every Cauchy jet packet.**
Finitely many atoms suffice, and their masses need move only by factors arbitrarily close to one. -/
theorem exists_cauchyJet_expBox_reach {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Infinite κ]
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (t : κ → ℝ) (ht : Function.Injective t) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (K : ℕ) (a : Fin K → κ), Function.Injective a ∧
      {y : (Σ i, Fin (n i)) → ℂ | ∃ s : Fin K → ℝ, (∀ k, |s k| < δ) ∧
          ∑ k, (Real.exp (s k) - 1) • cauchyJetColumn x n (fun b => (t b : ℂ)) (a k) = y}
        ∈ nhds (0 : (Σ i, Fin (n i)) → ℂ) := by
  haveI : Fintype ((i : ι) × Fin (n i)) := inferInstance
  exact exists_expBox_reach_of_span_range _
    (span_range_cauchyJetColumn_eq_top x hx hupper n t ht) hδ

end

end GaloisForLFunctions.HTGeometry
