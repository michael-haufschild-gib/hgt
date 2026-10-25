import GaloisForLFunctions.ArithmeticOrientationTheory.FiniteWienerJetsCanBePrescribed
import GaloisForLFunctions.ArithmeticOrientationTheory.PaidKernelsCoverVisibleTranslatedZeroOrders

/-!
# Visible pole jets bound the paid index

The surjective finite jet map descends through every ideal imposing those
jets. Visible translated zero orders impose these conditions on the actual
paid ideal, with each finite multiplicity counted separately.
-/

noncomputable section
set_option autoImplicit false
open Finset

namespace GaloisForLFunctions.ArithmeticOrientationTheory
open WienerAlgebraAt TransHorizonIncidenceMechanics BezoutValuationIncidence

/-- Any Wiener ideal imposing finite interior jets has at least their total codimension. -/
theorem sum_jets_le_rank_wiener_quotient
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι → ℂ) (hs : ∀ i, 1 / 2 < (s i).re) (hinj : Function.Injective s)
    (m : ι → ℕ) (I : Ideal (WienerAlgebraAt (1 / 2)))
    (hI : ∀ a ∈ I, ∀ i k, k < m i → iteratedDeriv k (LSeries (⇑a.toFn)) (s i) = 0) :
    ((∑ i, m i : ℕ) : Cardinal) ≤ Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸ I) := by
  let J := Σ i, Fin (m i)
  let q : WienerAlgebraAt (1 / 2) →ₗ[ℂ] (J → ℂ) :=
    LinearMap.pi fun t => wienerJetLinear (s t.1) (hs t.1) t.2
  have hq : Function.Surjective q := by
    intro v
    obtain ⟨a, ha⟩ := surjective_wiener_finite_jet_evaluation s hs hinj m
      (fun i k => v ⟨i, k⟩)
    refine ⟨a, funext fun t => ?_⟩
    exact congrFun (congrFun ha t.1) t.2
  have hker : I.restrictScalars ℂ ≤ q.ker := by
    intro a ha
    change q a = 0
    exact funext fun t => hI a ha t.1 t.2 t.2.isLt
  let L : (WienerAlgebraAt (1 / 2) ⧸ I) →ₗ[ℂ] (J → ℂ) :=
    (I.restrictScalars ℂ).liftQ q hker
  have hL : Function.Surjective L := by
    intro v
    obtain ⟨a, rfl⟩ := hq v
    exact ⟨Submodule.Quotient.mk a, rfl⟩
  have h := rank_range_le L
  rw [LinearMap.range_eq_top.mpr hL, rank_top, rank_fun'] at h
  simpa only [J, Fintype.card_sigma, Fintype.card_fin] using h

/-- Uncancelled translated zero multiplicities bound the actual paid quotient index. -/
theorem sum_visible_orders_le_rank_quotient_paidIdeal_moebius
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, 1 / 2 + ε < ρ.re ∧ ρ.re < 1)
    (m : Z → ℕ) (hm : ∀ ρ : Z, (m ρ : ℕ∞) ≤ visibleTranslatedZetaOrder ε ρ) :
    ((∑ ρ : Z, m ρ : ℕ) : Cardinal) ≤
      Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸
        paidIdeal (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε)) := by
  classical
  have hs (ρ : Z) : 1 / 2 < ((ρ : ℂ) - (ε : ℂ)).re := by
    have h := (hZ ρ ρ.property).1
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith only [h]
  apply sum_jets_le_rank_wiener_quotient (fun ρ : Z => (ρ : ℂ) - ε) hs
    (fun a b hab => Subtype.ext (sub_left_inj.mp hab)) m
  intro a ha ρ k hk
  exact paid_kernel_jets_vanish_below_visible_order hε hε2 a ha
    (hZ ρ ρ.property).1 (hZ ρ ρ.property).2 (hm ρ) k hk

end GaloisForLFunctions.ArithmeticOrientationTheory

#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.sum_jets_le_rank_wiener_quotient
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.sum_visible_orders_le_rank_quotient_paidIdeal_moebius
end
