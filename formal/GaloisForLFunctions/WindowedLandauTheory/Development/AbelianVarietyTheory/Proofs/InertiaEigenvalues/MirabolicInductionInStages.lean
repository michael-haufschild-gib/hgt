import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicInductionStep
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.InducedFunctionTwist

/-! Inflation and induction in stages carry the mirabolic recursion through
the smaller stabilizer while keeping its last-column character. -/

noncomputable section
open GaloisForLFunctions
open scoped Classical

namespace GlobalTheory.GLq

variable {g m : ℕ} [Fact g.Prime]

local notation "M" => mirabolicSubgroup g (m + 1)
local notation "M₀" => mirabolicSubgroup g m
local notation "K" => mirabolicInducingSubgroup g m

theorem mirabolicInducingLevi_surjective :
    Function.Surjective (mirabolicInducingLevi (g := g) (m := m)) := by
  intro x
  refine ⟨⟨mirabolicUnit x.val 0, ?_⟩, Subtype.ext (mirabolicLevi_unit x.val 0)⟩
  change mirabolicLevi (mirabolicUnit x.val 0) ∈ M₀
  rw [mirabolicLevi_unit]
  exact x.property

theorem mirabolicInduce_sum (ψ : AddChar (ZMod g) ℂ) {ι : Type} (S : Finset ι) (F : ι → M₀ → ℂ) :
    mirabolicInduce ψ (fun x => ∑ i ∈ S, F i x) = ∑ i ∈ S, mirabolicInduce ψ (F i) := by
  funext u
  unfold mirabolicInduce inducedFunction
  simp only [Finset.sum_apply, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x * u * x⁻¹ ∈ K
  · simp only [extendByZero_of_mem _ _ hx, Finset.mul_sum]
  · simp only [extendByZero_of_notMem _ _ hx, Finset.sum_const_zero]

/-- If the function on the smaller mirabolic subgroup is induced, passing
to the next rank induces from its inverse image with the last-column twist. -/
theorem mirabolicInduce_inducedFunction (ψ : AddChar (ZMod g) ℂ) (H : Subgroup M₀) (f : H → ℂ) :
    let π : K →* M₀ := mirabolicInducingLevi
    let P := H.comap π
    let e := P.equivMapOfInjective (Subgroup.subtype K) (Subgroup.subtype_injective K)
    mirabolicInduce ψ (inducedFunction H f) =
      inducedFunction (P.map (Subgroup.subtype K)) (fun x =>
        (mirabolicLastCharacter ψ (e.symm x).val : ℂ) *
          f ⟨π (e.symm x).val, (e.symm x).property⟩) := by
  dsimp only
  let π : K →* M₀ := mirabolicInducingLevi
  let P := H.comap π
  let f' (x : P) := f ⟨π x.val, x.property⟩
  let η : K →* ℂˣ := mirabolicLastCharacter ψ
  have he (x : K) :
      (η x : ℂ) * inducedFunction H f (π x) =
        inducedFunction P (fun z => (η z.val : ℂ) * f' z) x := by
    rw [inducedFunction_twist]
    rw [inducedFunction_comap π mirabolicInducingLevi_surjective H f x]
  unfold mirabolicInduce
  change inducedFunction K (fun x => (η x : ℂ) * inducedFunction H f (π x)) = _
  rw [funext he, inducedFunction_inducedFunction]

end GlobalTheory.GLq
