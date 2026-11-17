import GaloisForLFunctions.RepresentationLifting.Differential.CartierGapContraction
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Cartier contraction on the actual gap space

The Euler operator is invertible on missing exponents when the characteristic belongs to the retained additive spectrum.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.DividedPower
variable (p : ℕ) [Fact p.Prime]

/-- The actual coefficient subspace carried by the missing exponents. -/
def gapSpace (S : AddSubmonoid ℕ) : Submodule (ZMod p) (ℕ →₀ ZMod p) :=
  Finsupp.supported (ZMod p) (ZMod p) (S : Set ℕ)ᶜ

private theorem mem_gapSpace_iff (S : AddSubmonoid ℕ) (f : ℕ →₀ ZMod p) :
    f ∈ gapSpace p S ↔ ∀ n ∈ S, f n = 0 := by
  rw [gapSpace, Finsupp.mem_supported']
  simp only [Set.mem_compl_iff, SetLike.mem_coe, not_not]

private theorem projection_gap_zero (S : AddSubmonoid ℕ) (v : gapSpace p S) :
    spectrumProjection p S v.val = 0 := by
  classical
  apply Finsupp.ext
  intro n
  rw [spectrumProjection_apply]
  by_cases hn : n ∈ S
  · rw [if_pos hn, (mem_gapSpace_iff p S v.val).mp v.property n hn]
    rfl
  · rw [if_neg hn]
    rfl

/-- Restriction of the logarithmic Euler operator to its gap subspace. -/
def gapEuler (S : AddSubmonoid ℕ) : Module.End (ZMod p) (gapSpace p S) where
  toFun v := ⟨logarithmicEuler p v.val, (mem_gapSpace_iff p S _).mpr (by
    intro n hn
    rw [logarithmicEuler_apply, (mem_gapSpace_iff p S v.val).mp v.property n hn, mul_zero])⟩
  map_add' u v := Subtype.ext ((logarithmicEuler p).map_add u.val v.val)
  map_smul' c v := Subtype.ext ((logarithmicEuler p).map_smul c v.val)

/-- Restriction of the explicit Cartier homotopy to the same subspace. -/
def gapInverse (S : AddSubmonoid ℕ) : Module.End (ZMod p) (gapSpace p S) where
  toFun v := ⟨gapGreen p S v.val, (mem_gapSpace_iff p S _).mpr (by
    intro n hn
    rw [gapGreen_apply, if_pos hn])⟩
  map_add' u v := Subtype.ext ((gapGreen p S).map_add u.val v.val)
  map_smul' c v := Subtype.ext ((gapGreen p S).map_smul c v.val)

/-- The gap differential is an actual linear automorphism when the characteristic is retained. -/
def gapEulerEquiv (S : AddSubmonoid ℕ) (hp : p ∈ S) : gapSpace p S ≃ₗ[ZMod p] gapSpace p S where
  toLinearMap := gapEuler p S
  invFun := gapInverse p S
  left_inv v := by
    apply Subtype.ext
    have h := LinearMap.congr_fun (gapGreen_logarithmicEuler p S hp) v.val
    change gapGreen p S (logarithmicEuler p v.val) = v.val - spectrumProjection p S v.val at h
    rw [projection_gap_zero, sub_zero] at h
    exact h
  right_inv v := by
    apply Subtype.ext
    have h := LinearMap.congr_fun (logarithmicEuler_gapGreen p S hp) v.val
    change logarithmicEuler p (gapGreen p S v.val) = v.val - spectrumProjection p S v.val at h
    rw [projection_gap_zero, sub_zero] at h
    exact h

open ArithmeticEffectivityTheory.ResidueColumns

/-- The dimension of the complete gap subspace is exactly the residue-column genus. -/
theorem kunz_gapSpace_finrank (m : ℕ) [Fact (m + 1).Prime] (k : ℕ → ℕ)
    (h0 : k 0 = 0) (hK : Kunz m k) :
    Module.finrank (ZMod (m + 1)) (gapSpace (m + 1) (columnSubmonoid m k h0 hK)) = genus m k := by
  letI : Fintype ({n : ℕ | n ∉ carrier m k} : Set ℕ) := gapsFintype m k
  change Module.finrank (ZMod (m + 1))
    (Finsupp.supported (ZMod (m + 1)) (ZMod (m + 1)) {n : ℕ | n ∉ carrier m k}) = _
  rw [((Finsupp.supportedEquivFinsupp (M := ZMod (m + 1)) (R := ZMod (m + 1))
      {n : ℕ | n ∉ carrier m k}).trans
    (Finsupp.linearEquivFunOnFinite (ZMod (m + 1)) (ZMod (m + 1))
      ({n : ℕ | n ∉ carrier m k} : Set ℕ))).finrank_eq,
    Module.finrank_fintype_fun_eq_card]
  exact card_gaps m k

/-- Every prime-period column gap operator has the displayed inverse on its genus-dimensional space. -/
def kunzGapEulerEquiv (m : ℕ) [Fact (m + 1).Prime] (k : ℕ → ℕ)
    (h0 : k 0 = 0) (hK : Kunz m k) :
    gapSpace (m + 1) (columnSubmonoid m k h0 hK) ≃ₗ[ZMod (m + 1)]
      gapSpace (m + 1) (columnSubmonoid m k h0 hK) :=
  gapEulerEquiv (m + 1) _ (by
    change m + 1 ∈ carrier m k
    have h := (mem_column m k 1 0 (Nat.succ_pos m)).mpr (by omega)
    simpa only [Nat.one_mul, Nat.add_zero] using h)

#print axioms gapEulerEquiv
#print axioms kunz_gapSpace_finrank
#print axioms kunzGapEulerEquiv
end GaloisForLFunctions.RepresentationLifting.DividedPower
