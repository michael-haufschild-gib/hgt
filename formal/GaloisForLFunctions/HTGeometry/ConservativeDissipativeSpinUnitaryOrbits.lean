import GaloisForLFunctions.HTGeometry.ConservativeDissipativeMixedSpin
import GaloisForLFunctions.HTGeometry.GomesHiggsOrbitClassification

/-!
# Higgs orbit classification along conservative–dissipative spin trajectories

Application of Schaffer–Exl, arXiv:2609.04530, through the corpus's exact spin flow
and Gomes's Higgs orbit classification. Normalized chart lifts admit unique SU(2)
transport. Each complete spin trajectory admits pointwise special-unitary transport
starting at the identity, and every mixed trajectory remains on one SU(2) conjugacy
orbit. These are state-dependent transports; no regularity of the chosen family is
asserted, and they do not assert a common channel acting on all initial states.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- The canonical chart lift is always a nonzero Higgs doublet. -/
theorem spinChartSpinor_ne_zero (z : ℂ) : spinChartSpinor z ≠ 0 := by
  intro h
  have hn := spinChartSpinor_normSq z
  rw [h] at hn
  simp [abelianHiggsSpinorNormSq] at hn

/-- The existing Higgs orbit classifier gives a unique SU(2) transport between any two chart spinors. -/
theorem spinChartSpinor_unique_specialUnitary (z w : ℂ) :
    ∃! U : Matrix.specialUnitaryGroup (Fin 2) ℂ,
      (U : Matrix (Fin 2) (Fin 2) ℂ).mulVec (spinChartSpinor z) = spinChartSpinor w := by
  obtain ⟨U, hU, hmap⟩ := (higgs_norm_eq_iff_specialUnitary_orbit
    (spinChartSpinor z) (spinChartSpinor w)).mp (by rw [spinChartSpinor_normSq, spinChartSpinor_normSq])
  refine ⟨⟨U, hU⟩, hmap, ?_⟩
  intro V hV
  have he := (higgs_specialUnitary_action_eq_iff V ⟨U, hU⟩ (spinChartSpinor z)).mp (hV.trans hmap.symm)
  exact he.resolve_left (spinChartSpinor_ne_zero z)

/-- Every pair of actual pure spin densities lies on one special-unitary conjugacy orbit. -/
theorem spinChartDensity_specialUnitary_orbit (z w : ℂ) :
    ∃ U : Matrix.specialUnitaryGroup (Fin 2) ℂ,
      (U : Matrix (Fin 2) (Fin 2) ℂ) * spinChartDensity z *
        (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = spinChartDensity w := by
  obtain ⟨U, hU, _⟩ := spinChartSpinor_unique_specialUnitary z w
  refine ⟨U, ?_⟩
  rw [spinChartDensity_eq_pureProjector, conj_pureProjectorMatrix, hU,
    ← spinChartDensity_eq_pureProjector]

/-- The entire spinor evolution has pointwise special-unitary transport from its initial lift. -/
theorem spinSpinorFlow_pointwise_specialUnitary (a : ℝ) (z : ℂ) :
    ∃ U : ℝ → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ t, U t ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) ∧
      (∀ t, (U t).mulVec (spinChartSpinor z) = spinSpinorFlow a z t) ∧ U 0 = 1 := by
  have hn : ∀ t : ℝ, abelianHiggsSpinorNormSq (spinChartSpinor z) =
      abelianHiggsSpinorNormSq (spinSpinorFlow a z t) := fun t =>
    (spinChartSpinor_normSq z).trans (spinSpinorFlow_higgs_vacuum a z t).1.symm
  obtain ⟨U, hU, hmap⟩ := (higgs_section_norm_eq_iff_pointwise_specialUnitary
    (fun _ : ℝ => spinChartSpinor z) (spinSpinorFlow a z)).mp hn
  refine ⟨U, hU, hmap, ?_⟩
  have hh : (U 0).mulVec (spinChartSpinor z) = spinChartSpinor z := by
    simpa only [spinSpinorFlow, spinPlaneFlow_zero] using hmap 0
  have he := ((higgs_specialUnitary_stabilizer ⟨U 0, hU 0⟩ (spinChartSpinor z)).mp hh).resolve_left
    (spinChartSpinor_ne_zero z)
  exact congrArg (fun V : Matrix.specialUnitaryGroup (Fin 2) ℂ => (V : Matrix (Fin 2) (Fin 2) ℂ)) he

/-- Every two times on a mixed spin trajectory are related by an actual special-unitary conjugation. -/
theorem spinMixedDensity_specialUnitary_orbit (a u : ℝ) (z : ℂ) (s t : ℝ) :
    ∃ U : Matrix.specialUnitaryGroup (Fin 2) ℂ,
      (U : Matrix (Fin 2) (Fin 2) ℂ) * spinMixedDensity a u z s *
        (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = spinMixedDensity a u z t := by
  obtain ⟨U, hp⟩ := spinChartDensity_specialUnitary_orbit
    (spinPlaneFlow (spinMixAmplitude a u) z s) (spinPlaneFlow (spinMixAmplitude a u) z t)
  have hU : (U : Matrix (Fin 2) (Fin 2) ℂ) * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp
      (Matrix.specialUnitaryGroup_le_unitaryGroup U.property)
  change (U : Matrix (Fin 2) (Fin 2) ℂ) * spinDensityFlow (spinMixAmplitude a u) z s *
    (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = spinDensityFlow (spinMixAmplitude a u) z t at hp
  refine ⟨U, ?_⟩
  rw [spinMixedDensity_mixture, spinMixedDensity_mixture]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hU, hp]

end
end GaloisForLFunctions.HTGeometry.SchafferExl
