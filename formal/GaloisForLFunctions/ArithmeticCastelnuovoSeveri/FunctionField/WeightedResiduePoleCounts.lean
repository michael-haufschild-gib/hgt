import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerPoleCutoffs
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.WeightedResidueGaps
import Mathlib.Data.Fintype.Sum

/-!
# Bounded pole orders and missing residue weights

Distinct residue weights give unique coordinates for every represented
integer. Once a bound contains every gap, the bounded coordinates and
the gaps partition its initial interval. Counting this partition gives
the eventual linear dimension formula for one-point pole spaces.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis

variable {N : ℕ} (hN : 0 < N) (D : Fin N → ℕ)
    (hresidue : ∀ i j, D i % N = D j % N → i = j)
    (m : ℕ) (hgap : ∀ a : WeightedResidueGaps D, a.val ≤ m)

private def boundedPoleGapMap :
    ((Σ i : Fin N, Fin (poleDegreeCutoff N (D i) m)) ⊕ WeightedResidueGaps D) →
      Fin (m + 1)
  | Sum.inl a => ⟨N * a.2.val + D a.1,
      Nat.lt_succ_of_le ((lt_poleDegreeCutoff_iff N (D a.1) m a.2.val hN).mp a.2.isLt)⟩
  | Sum.inr a => ⟨a.val, Nat.lt_succ_of_le (hgap a)⟩

include hresidue in
private theorem boundedPoleGapMap_bijective :
    Function.Bijective (boundedPoleGapMap hN D m hgap) := by
  constructor
  · intro a b h
    have hv := congrArg Fin.val h
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        rcases a with ⟨i, k⟩
        rcases b with ⟨j, l⟩
        change N * k.val + D i = N * l.val + D j at hv
        have hmod := congrArg (fun t => t % N) hv
        simp only [Nat.mul_add_mod_self_left] at hmod
        have hij := hresidue i j hmod
        subst j
        have hkl : k = l := Fin.ext
          (Nat.eq_of_mul_eq_mul_left hN (Nat.add_right_cancel hv))
        subst l
        rfl
      | inr b => exact False.elim (b.property ⟨a.1, a.2.val, hv⟩)
    | inr a =>
      cases b with
      | inl b => exact False.elim (a.property ⟨b.1, b.2.val, hv.symm⟩)
      | inr b => exact congrArg Sum.inr (Subtype.ext hv)
  · intro a
    by_cases ha : ∃ i : Fin N, ∃ k : ℕ, N * k + D i = a.val
    · obtain ⟨i, k, hk⟩ := ha
      have hkm : k < poleDegreeCutoff N (D i) m :=
        (lt_poleDegreeCutoff_iff N (D i) m k hN).mpr
          (by rw [hk]; exact Nat.le_of_lt_succ a.isLt)
      exact ⟨Sum.inl ⟨i, ⟨k, hkm⟩⟩, Fin.ext hk⟩
    · exact ⟨Sum.inr ⟨a.val, ha⟩, rfl⟩

/-- Bounded residue coordinates and all gaps partition the initial interval after the final gap. -/
def boundedPoleGapEquiv :
    ((Σ i : Fin N, Fin (poleDegreeCutoff N (D i) m)) ⊕ WeightedResidueGaps D) ≃
      Fin (m + 1) :=
  Equiv.ofBijective (boundedPoleGapMap hN D m hgap)
    (boundedPoleGapMap_bijective hN D hresidue m hgap)

include hN hresidue hgap in
/-- Above all gaps, the number of bounded represented orders plus the gap count is the interval length. -/
theorem poleDegreeCutoff_sum_add_gaps :
    (∑ i : Fin N, poleDegreeCutoff N (D i) m) + Nat.card (WeightedResidueGaps D) = m + 1 := by
  letI : Fintype (WeightedResidueGaps D) :=
    Fintype.ofEquiv (Σ i : Fin N, Fin (D i / N)) (weightedResidueGapEquiv hN D hresidue)
  have h := Nat.card_congr (boundedPoleGapEquiv hN D hresidue m hgap)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_sigma,
    Fintype.card_fin] using h

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
