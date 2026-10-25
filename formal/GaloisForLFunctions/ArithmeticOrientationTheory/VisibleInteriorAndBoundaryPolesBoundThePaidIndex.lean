import GaloisForLFunctions.ArithmeticOrientationTheory.InteriorJetsAndBoundaryValuesCanBePrescribed
import GaloisForLFunctions.ArithmeticOrientationTheory.PaidKernelsCoverVisibleTranslatedZeroOrders
import GaloisForLFunctions.ArithmeticOrientationTheory.CriticalBoundaryPolesObstructPaidKernels

/-!
# Visible interior and boundary poles bound the paid index

Interior jets and additional values have additive quotient codimension.
For the actual paid ideal this counts visible interior multiplicities
together with distinct critical-boundary poles.
-/

noncomputable section
set_option autoImplicit false
open Finset

namespace GaloisForLFunctions.ArithmeticOrientationTheory
open WienerAlgebraAt TransHorizonIncidenceMechanics BezoutValuationIncidence

/-- Interior jet conditions and separate boundary values add their quotient codimensions. -/
theorem sum_jets_add_values_le_rank_wiener_quotient
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (s : ι → ℂ) (hs : ∀ i, 1 / 2 < (s i).re) (hsinj : Function.Injective s) (m : ι → ℕ)
    (t : β → ℂ) (ht : ∀ j, (1 / 2 : ℝ) ≤ (t j).re) (htinj : Function.Injective t)
    (hdisj : ∀ i j, s i ≠ t j) (I : Ideal (WienerAlgebraAt (1 / 2)))
    (hIjet : ∀ a ∈ I, ∀ i k, k < m i → iteratedDeriv k (LSeries (⇑a.toFn)) (s i) = 0)
    (hIval : ∀ a ∈ I, ∀ j, LSeries (⇑a.toFn) (t j) = 0) :
    (((∑ i, m i) + Fintype.card β : ℕ) : Cardinal) ≤
      Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸ I) := by
  let J := (Σ i, Fin (m i)) ⊕ β
  let χ (j : β) := WienerAlgebraAt.bohrCharacter (1 / 2) (halfPlanePoint (1 / 2) (t j) (ht j))
  let q : WienerAlgebraAt (1 / 2) →ₗ[ℂ] (J → ℂ) := LinearMap.pi
    (Sum.elim (fun u => wienerJetLinear (s u.1) (hs u.1) u.2)
      (fun j => (χ j).toLinearMap))
  have hq : Function.Surjective q := by
    intro v
    obtain ⟨a, ha, hav⟩ := exists_wiener_with_mixed_finite_data s hs hsinj m
      (fun i k => if h : k < m i then v (.inl ⟨i, ⟨k, h⟩⟩) else 0)
      t ht htinj hdisj (fun j => v (.inr j))
    refine ⟨a, funext fun u => ?_⟩
    cases u with
    | inl u => exact (ha u.1 u.2 u.2.isLt).trans (dif_pos u.2.isLt)
    | inr j =>
        exact (wienerLSeries_eq_character a (ht j)).symm.trans (hav j)
  have hker : I.restrictScalars ℂ ≤ q.ker := by
    intro a ha
    change q a = 0
    apply funext
    intro u
    cases u with
    | inl u => exact hIjet a ha u.1 u.2 u.2.isLt
    | inr j => exact (wienerLSeries_eq_character a (ht j)).symm.trans (hIval a ha j)
  let L : (WienerAlgebraAt (1 / 2) ⧸ I) →ₗ[ℂ] (J → ℂ) :=
    (I.restrictScalars ℂ).liftQ q hker
  have hL : Function.Surjective L := by
    intro v
    obtain ⟨a, rfl⟩ := hq v
    exact ⟨Submodule.Quotient.mk a, rfl⟩
  have h := rank_range_le L
  rw [LinearMap.range_eq_top.mpr hL, rank_top, rank_fun'] at h
  simpa only [J, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin] using h

/-- Visible interior pole orders and critical-boundary poles jointly bound the paid index. -/
theorem sum_visible_orders_add_boundary_card_le_paid_index
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (Z B : Finset ℂ) (hZ : ∀ ρ ∈ Z, 1 / 2 + ε < ρ.re ∧ ρ.re < 1)
    (hB : ∀ ρ ∈ B, ρ.re = 1 / 2 + ε ∧
      analyticOrderAt riemannZeta (ρ - ε) < analyticOrderAt riemannZeta ρ)
    (m : Z → ℕ) (hm : ∀ ρ : Z, (m ρ : ℕ∞) ≤ visibleTranslatedZetaOrder ε ρ) :
    (((∑ ρ : Z, m ρ) + B.card : ℕ) : Cardinal) ≤
      Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸
        paidIdeal (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε)) := by
  classical
  have hs (ρ : Z) : 1 / 2 < ((ρ : ℂ) - (ε : ℂ)).re := by
    have h := (hZ ρ ρ.property).1
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith only [h]
  have ht (ρ : B) : (1 / 2 : ℝ) ≤ ((ρ : ℂ) - (ε : ℂ)).re := by
    have h := (hB ρ ρ.property).1
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith only [h]
  have hdisj (ρ : Z) (τ : B) : (ρ : ℂ) - ε ≠ (τ : ℂ) - ε := by
    intro h
    have heq := congrArg Complex.re (sub_left_inj.mp h)
    have hρ := (hZ ρ ρ.property).1
    have hτ := (hB τ τ.property).1
    linarith only [heq, hρ, hτ]
  have h := sum_jets_add_values_le_rank_wiener_quotient
    (fun ρ : Z => (ρ : ℂ) - ε) hs (fun a b hab => Subtype.ext (sub_left_inj.mp hab)) m
    (fun ρ : B => (ρ : ℂ) - ε) ht (fun a b hab => Subtype.ext (sub_left_inj.mp hab)) hdisj
    (paidIdeal (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε))
    (fun a ha ρ k hk => paid_kernel_jets_vanish_below_visible_order hε hε2 a ha
      (hZ ρ ρ.property).1 (hZ ρ ρ.property).2 (hm ρ) k hk)
    (fun a ha ρ => by
      have hz := mem_obstructionHull_moebius_of_critical_boundary_order_loss hε hε2
        (hB ρ ρ.property).1 (hB ρ ρ.property).2 a ha
      rw [bohrEval_halfPlanePoint] at hz
      exact hz)
  simpa only [Fintype.card_coe] using h

end GaloisForLFunctions.ArithmeticOrientationTheory

#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.sum_jets_add_values_le_rank_wiener_quotient
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.sum_visible_orders_add_boundary_card_le_paid_index
end
