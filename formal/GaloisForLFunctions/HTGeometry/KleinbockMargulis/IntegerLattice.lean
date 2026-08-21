import GaloisForLFunctions.HTGeometry.KleinbockMargulis.PluckerSpan
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The lattice of integer points of a rational subspace

A rational subspace `W ⊆ ℚ^k` meets `ℤ^k` in a subgroup `intPoints W`, which is free of rank
`dim_ℚ W`: a `ℤ`-basis of it is `ℚ`-linearly independent (linear independence is insensitive to
passing to the fraction field) and spans `W` over `ℚ` (any `w ∈ W` becomes integral after
multiplication by a common denominator).

These lattices, indexed by the nonzero rational subspaces of `ℚ^k`, form the poset `L(ℤ^k)` on
which the quantitative non-divergence theorem of Kleinbock–Margulis §5 is proved.

## Main definitions and results

* `intPoints`, `latticeRank`, `latticeBasis` — the lattice, its rank and a chosen `ℤ`-basis.
* `exists_int_combination` — every integer point is an integral combination of the basis.
* `latticeBasis_linearIndependent`, `latticeBasis_span` — the basis is a `ℚ`-basis of `W`.
* `latticeRank_eq_finrank` — `rank(W ∩ ℤ^k) = dim_ℚ W`.
-/

open Matrix Finset Module
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

variable {k : ℕ}

/-! ### Integer vectors as rational vectors -/

/-- The coordinatewise inclusion `ℤ^k → ℚ^k`. -/
def intToRat (v : Fin k → ℤ) : Fin k → ℚ := fun i => (v i : ℚ)

/-- `intToRat` as a `ℤ`-linear map. -/
def intToRatₗ (k : ℕ) : (Fin k → ℤ) →ₗ[ℤ] (Fin k → ℚ) where
  toFun := intToRat
  map_add' u v := by funext i; simp [intToRat]
  map_smul' c v := by funext i; simp [intToRat]

@[simp] theorem intToRatₗ_apply (v : Fin k → ℤ) : intToRatₗ k v = intToRat v := rfl

theorem intToRat_injective : Function.Injective (intToRat (k := k)) := by
  intro u v h
  funext i
  have hi := congrFun h i
  simp only [intToRat] at hi
  exact_mod_cast hi

theorem ker_intToRatₗ : LinearMap.ker (intToRatₗ k) = ⊥ :=
  LinearMap.ker_eq_bot.mpr intToRat_injective

/-! ### The lattice of integer points -/

/-- The integer points of a rational subspace. -/
def intPoints (W : Submodule ℚ (Fin k → ℚ)) : Submodule ℤ (Fin k → ℤ) :=
  (W.restrictScalars ℤ).comap (intToRatₗ k)

@[simp] theorem mem_intPoints {W : Submodule ℚ (Fin k → ℚ)} {v : Fin k → ℤ} :
    v ∈ intPoints W ↔ intToRat v ∈ W := Iff.rfl

/-- The rank of the lattice of integer points. -/
noncomputable def latticeRank (W : Submodule ℚ (Fin k → ℚ)) : ℕ :=
  (Submodule.basisOfPid (Pi.basisFun ℤ (Fin k)) (intPoints W)).1

/-- A chosen `ℤ`-basis of the lattice of integer points. -/
noncomputable def latticeBasisSub (W : Submodule ℚ (Fin k → ℚ)) :
    Basis (Fin (latticeRank W)) ℤ (intPoints W) :=
  (Submodule.basisOfPid (Pi.basisFun ℤ (Fin k)) (intPoints W)).2

/-- The chosen basis, as a tuple of integer vectors. -/
noncomputable def latticeBasis (W : Submodule ℚ (Fin k → ℚ)) :
    Fin (latticeRank W) → (Fin k → ℤ) := fun a => ((latticeBasisSub W a : intPoints W) : Fin k → ℤ)

theorem latticeBasis_mem (W : Submodule ℚ (Fin k → ℚ)) (a : Fin (latticeRank W)) :
    latticeBasis W a ∈ intPoints W := (latticeBasisSub W a).2

/-- Every integer point of `W` is an integral combination of the chosen basis. -/
theorem exists_int_combination (W : Submodule ℚ (Fin k → ℚ)) {v : Fin k → ℤ}
    (hv : v ∈ intPoints W) :
    ∃ c : Fin (latticeRank W) → ℤ, v = fun i => ∑ a, c a * latticeBasis W a i := by
  classical
  refine ⟨fun a => (latticeBasisSub W).repr ⟨v, hv⟩ a, ?_⟩
  have hsum := (latticeBasisSub W).sum_repr ⟨v, hv⟩
  have hcoe := congrArg (fun u : intPoints W => (u : Fin k → ℤ)) hsum
  simp only [Submodule.coe_sum, SetLike.val_smul] at hcoe
  funext i
  have := congrFun hcoe i
  simpa [latticeBasis, Finset.sum_apply, smul_eq_mul] using this.symm

/-! ### The basis is a rational basis of `W` -/

theorem latticeBasis_linearIndependent (W : Submodule ℚ (Fin k → ℚ)) :
    LinearIndependent ℚ fun a => intToRat (latticeBasis W a) := by
  have hZ : LinearIndependent ℤ fun a => intToRat (latticeBasis W a) := by
    have h1 : LinearIndependent ℤ (latticeBasisSub W) := (latticeBasisSub W).linearIndependent
    have hker : LinearMap.ker ((intToRatₗ k).comp (intPoints W).subtype) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro u v huv
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        intToRatₗ_apply] at huv
      exact Subtype.ext (intToRat_injective huv)
    exact h1.map' ((intToRatₗ k).comp (intPoints W).subtype) hker
  exact (LinearIndependent.iff_fractionRing ℤ ℚ).mp hZ

/-- Multiplying by a common denominator makes a rational vector integral. -/
theorem exists_int_smul_mem (W : Submodule ℚ (Fin k → ℚ)) {w : Fin k → ℚ} (hw : w ∈ W) :
    ∃ (N : ℤ) (v : Fin k → ℤ), 0 < N ∧ intToRat v = (N : ℚ) • w ∧ v ∈ intPoints W := by
  classical
  refine ⟨∏ i, ((w i).den : ℤ), fun i => (∏ l ∈ Finset.univ.erase i, ((w l).den : ℤ)) * (w i).num,
    ?_, ?_, ?_⟩
  · refine Finset.prod_pos fun i _ => ?_
    exact_mod_cast (w i).pos
  · funext i
    simp only [intToRat, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_assoc]
    congr 1
    exact (Rat.den_mul_eq_num (w i)).symm
  · rw [mem_intPoints]
    have heq : intToRat (fun i => (∏ l ∈ Finset.univ.erase i, ((w l).den : ℤ)) * (w i).num)
        = ((∏ i, ((w i).den : ℤ) : ℤ) : ℚ) • w := by
      funext i
      simp only [intToRat, Pi.smul_apply, smul_eq_mul]
      push_cast
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_assoc]
      congr 1
      exact (Rat.den_mul_eq_num (w i)).symm
    rw [heq]
    exact W.smul_mem _ hw

theorem latticeBasis_span (W : Submodule ℚ (Fin k → ℚ)) :
    Submodule.span ℚ (Set.range fun a => intToRat (latticeBasis W a)) = W := by
  classical
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨a, rfl⟩
    exact latticeBasis_mem W a
  · intro w hw
    obtain ⟨N, v, hN, hv, hvmem⟩ := exists_int_smul_mem W hw
    obtain ⟨c, hc⟩ := exists_int_combination W hvmem
    have hNne : ((N : ℚ)) ≠ 0 := by exact_mod_cast hN.ne'
    have hw' : w = ((N : ℚ))⁻¹ • intToRat v := by
      rw [hv, smul_smul, inv_mul_cancel₀ hNne, one_smul]
    rw [hw']
    refine Submodule.smul_mem _ _ ?_
    have : intToRat v = ∑ a, ((c a : ℚ)) • intToRat (latticeBasis W a) := by
      funext i
      simp only [intToRat, hc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      rfl
    rw [this]
    exact Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/-- The rank of the lattice of integer points equals the dimension of the subspace. -/
theorem latticeRank_eq_finrank (W : Submodule ℚ (Fin k → ℚ)) :
    latticeRank W = Module.finrank ℚ W := by
  have h := finrank_span_eq_card (latticeBasis_linearIndependent W)
  rw [latticeBasis_span W] at h
  rw [h, Fintype.card_fin]

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
