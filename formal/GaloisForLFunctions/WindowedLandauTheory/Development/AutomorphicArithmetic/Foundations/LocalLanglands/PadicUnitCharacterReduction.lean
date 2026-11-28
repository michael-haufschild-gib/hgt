import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PadicIntegralReduction
import Mathlib.Analysis.Complex.Basic

/-! A p-adic character trivial on the first principal units has a
unique induced character on the residue units. -/

noncomputable section

namespace GlobalTheory.GLp

variable {p : ℕ} [Fact p.Prime]

/-- Reduction of integral units to the prime residue field. -/
def padicUnitReduction : ℤ_[p]ˣ →* (ZMod p)ˣ :=
  Units.map (PadicInt.toZMod (p := p)).toMonoidHom

theorem padicUnitReduction_surjective : Function.Surjective (padicUnitReduction (p := p)) := by
  intro z
  obtain ⟨u, hu⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) z.val
  have hU : IsUnit u := by
    by_contra he
    have hm : u ∈ IsLocalRing.maximalIdeal ℤ_[p] := he
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, hu] at hm
    exact z.ne_zero hm
  refine ⟨hU.unit, Units.ext ?_⟩
  change PadicInt.toZMod hU.unit.val = z.val
  rw [IsUnit.unit_spec]
  exact hu

theorem existsUnique_padicResidueCharacter (χ : ℚ_[p]ˣ →* ℂˣ)
    (hχ : ∀ u : ℤ_[p]ˣ, padicUnitReduction u = 1 →
      χ (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u) = 1) :
    ∃! δ : (ZMod p)ˣ →* ℂˣ, ∀ u : ℤ_[p]ˣ,
      δ (padicUnitReduction u) = χ (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u) := by
  let r := padicUnitReduction (p := p)
  let c := χ.comp (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom)
  let δ := r.liftOfSurjective padicUnitReduction_surjective ⟨c, hχ⟩
  refine ⟨δ, ?_, fun ψ hψ => ?_⟩
  · exact r.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv padicUnitReduction_surjective) ⟨c, hχ⟩
  · apply MonoidHom.ext
    intro z
    obtain ⟨u, rfl⟩ := padicUnitReduction_surjective z
    exact (hψ u).trans
      (r.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv padicUnitReduction_surjective) ⟨c, hχ⟩ u).symm

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.existsUnique_padicResidueCharacter
