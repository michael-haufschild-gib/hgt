import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobius
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.SubspaceCounts
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.GaussianWeightedSum

/-! Evaluate the invariant-subspace Möbius inverse on the identity endomorphism. -/

open Polynomial

namespace GlobalTheory.CuspGL

private noncomputable def dimensionWeight (q a : ℕ) : ℂ :=
  if a = 0 then 0 else ∏ i ∈ Finset.Ico 1 a, (1 - (q : ℂ) ^ i)

private theorem sum_dimensionWeight (F : Type) [Field F] [Finite F]
    (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Fintype (Submodule F V)] :
    ∑ W : Submodule F V, dimensionWeight (Nat.card F) (Module.finrank F W) =
      (Module.finrank F V : ℂ) := by
  classical
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have h := GlobalTheory.QBinomialSum.sum_gaussian_mul_prod (Nat.card F) (Module.finrank F V)
    (fun a => Nat.card {W : Submodule F V // Module.finrank F W = a}) hq
    (fun a ha => GlobalTheory.SubspaceNumber.card_subspaces_mul F V a ha)
  rw [← h, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.Icc 0 (Module.finrank F V))
    (g := fun W : Submodule F V => Module.finrank F W)
    (fun W _ => Finset.mem_Icc.2 ⟨Nat.zero_le _, W.finrank_le⟩)]
  have fibre (a : ℕ) : ∑ W ∈ Finset.univ.filter (fun W : Submodule F V => Module.finrank F W = a),
      dimensionWeight (Nat.card F) (Module.finrank F W) =
      (Nat.card {W : Submodule F V // Module.finrank F W = a} : ℂ) * dimensionWeight (Nat.card F) a := by
    rw [Finset.sum_congr rfl (g := fun _ => dimensionWeight (Nat.card F) a)
      (fun W hW => by rw [(Finset.mem_filter.1 hW).2]), Finset.sum_const, nsmul_eq_mul,
      Nat.card_eq_fintype_card (α := {W : Submodule F V // Module.finrank F W = a}), Fintype.card_subtype]
  simp only [fibre]
  symm
  refine Finset.sum_subset_zero_on_sdiff (Finset.Icc_subset_Icc_left (Nat.zero_le 1)) ?_ ?_
  · intro a ha
    have h₀ : a = 0 := by
      simp only [Finset.mem_sdiff, Finset.mem_Icc] at ha
      omega
    simp [h₀, dimensionWeight]
  · intro a ha
    have h₀ : a ≠ 0 := by
      simp only [Finset.mem_Icc] at ha
      omega
    simp [h₀, dimensionWeight]

private theorem psi_one_eq_dimensionWeight (F : Type) [Field F] [Finite F] (s : F[X] → ℂ)
    (hs : ∀ j : ℕ, s ((X - C 1) ^ j) = j) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V], Module.finrank F V = n →
      psi s V 1 = dimensionWeight (Nat.card F) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ hn
    classical
    letI : Finite V := Module.finite_of_finite F
    letI : Finite (Submodule F V) := Finite.of_injective _ SetLike.coe_injective
    letI : Fintype (Submodule F V) := Fintype.ofFinite _
    have hc : LinearMap.charpoly (1 : Module.End F V) = (X - C 1) ^ n := by
      rw [LinearMap.charpoly_one, hn, C_1]
    rw [psi_eq, hc, hs]
    have h₁ : ∀ W : {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, (1 : Module.End F V) x ∈ W},
        psi s W.1 ((1 : Module.End F V).restrict W.2.2) =
          dimensionWeight (Nat.card F) (Module.finrank F W.1) := by
      intro W
      have he : (1 : Module.End F V).restrict W.2.2 = (1 : Module.End F W.1) := by
        ext x
        rfl
      rw [he]
      exact ih _ (hn ▸ Submodule.finrank_lt W.2.1) _ rfl
    rw [finsum_congr h₁, finsum_eq_sum_of_fintype,
      ← Finset.sum_subtype (Finset.univ.erase (⊤ : Submodule F V)) (by intro W; simp)
        (fun W : Submodule F V => dimensionWeight (Nat.card F) (Module.finrank F W))]
    have h₂ := sum_dimensionWeight F V
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⊤ : Submodule F V)), finrank_top, hn] at h₂
    rw [← h₂]
    ring

/-- In positive dimension, the identity value is the alternating finite-field product. -/
theorem psi_one (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (s : F[X] → ℂ) (hs : ∀ j : ℕ, s ((X - C 1) ^ j) = j)
    (h : 0 < Module.finrank F V) :
    psi s V 1 = ∏ i ∈ Finset.Ico 1 (Module.finrank F V), (1 - (Nat.card F : ℂ) ^ i) := by
  rw [psi_one_eq_dimensionWeight F s hs _ V rfl, dimensionWeight, if_neg h.ne']

end GlobalTheory.CuspGL
