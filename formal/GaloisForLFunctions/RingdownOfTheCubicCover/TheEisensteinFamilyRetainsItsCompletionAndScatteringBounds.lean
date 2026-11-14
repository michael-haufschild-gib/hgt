import GaloisForLFunctions.RingdownOfTheCubicCover.UnconditionalScatteringResonanceBounds
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheSquareOfANumberRingThroughItsIdealsHasTheIndexOfItsDedekindZetaFunction

/-!
# The primitive Eisenstein family with its full completion

For the third cyclotomic field, the character has root number `+1` and
Gamma factor `Γℝ(s + 1)`. The two poles and conductor factor remain in
the completed product. Its scattering ratio has value `-1` at the origin;
away from that removable point the completed-zeta quotient is literal.
The certified pulse decay rate is `1/16 - ε`.
-/

noncomputable section

open Complex NumberField
open GaloisForLFunctions.FamilyContinuationTheory
open GaloisForLFunctions.FamilyContinuationTheory.EisensteinNorm
open GaloisForLFunctions.HeckeLFunctions
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.RHTower.HalfWeight

namespace GaloisForLFunctions.RingdownOfTheCubicCover

/-- The archimedean factor of the actual odd character modulo three. -/
theorem gammaFactor_chi3D (s : ℂ) :
    DirichletCharacter.gammaFactor chi3D s = Complex.Gammaℝ (s + 1) := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hodd : ¬ chi3D.Even := by
    intro h
    have he : chi3D (-1) = 1 := h
    rw [chi3D_eq_legendreC, legendreC_neg_one 3 (by norm_num),
      ZMod.χ₄_nat_three_mod_four (by norm_num)] at he
    norm_num at he
  simp only [DirichletCharacter.gammaFactor, if_neg hodd]

/-- Primitivity and the exact root number of the Eisenstein character. -/
theorem chi3D_primitive_rootNumber :
    chi3D.IsPrimitive ∧ DirichletCharacter.rootNumber chi3D = 1 := by
  refine ⟨isPrimitive_chi3D, ?_⟩
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [chi3D_eq_legendreC]
  exact rootNumber_legendre 3 (by norm_num)

/-- Both Gamma factors and the conductor factor in the completed Dedekind product. -/
theorem completedBianchiZeta_eq_gamma_product {s : ℂ} (hs : 0 < s.re) :
    completedBianchiZeta s =
      (3 : ℂ) ^ (s / 2) * (Complex.Gammaℝ s * Complex.Gammaℝ (s + 1)) *
        (riemannZeta s * DirichletCharacter.LFunction chi3D s) := by
  have hs0 : s ≠ 0 := fun h => by simpa [h] using hs
  have hz : completedRiemannZeta s = riemannZeta s * Complex.Gammaℝ s := by
    rw [riemannZeta_def_of_ne_zero hs0, div_mul_cancel₀ _
      (Complex.Gammaℝ_ne_zero_of_re_pos hs)]
  rw [completedBianchiZeta, hz,
    completedLFunction_chi3D_eq_mul hs0 (gammaFactor_chi3D_ne_zero_of_re_pos hs),
    gammaFactor_chi3D]
  ring

/-- The entire normalization clears both poles, retaining its factor `1/2`. -/
theorem xiBianchi_eq_gamma_product {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    xiBianchi s = s * (s - 1) / 2 *
      ((3 : ℂ) ^ (s / 2) * (Complex.Gammaℝ s * Complex.Gammaℝ (s + 1)) *
        (riemannZeta s * DirichletCharacter.LFunction chi3D s)) := by
  have hs0 : s ≠ 0 := fun h => by simpa [h] using hs
  have hxi : xiBianchi s = s * (s - 1) / 2 * completedBianchiZeta s := by
    rw [xiBianchi, _root_.RHTower.xi_eq_half_mul hs0 hs1, completedBianchiZeta]
    ring
  rw [hxi, completedBianchiZeta_eq_gamma_product hs]

/-- The primitive trivial Hecke character, with both poles and all completion factors retained. -/
theorem thirdCyclotomic_primitive_hecke_completion
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K] :
    heckeFiniteConductor (trivialModulus K) 1 = (trivialModulus K).fin ∧
      ∀ s : ℂ, 1 < s.re →
        heckeXi (trivialModulus K) 1 s =
          s * (s - 1) * (heckeCompletionFactor (trivialModulus K) s *
            heckeGammaFactor (trivialModulus K) 1 s *
              (riemannZeta s * DirichletCharacter.LFunction chi3D s)) := by
  refine ⟨heckeFiniteConductor_trivialModulus K 1, fun s hs => ?_⟩
  rw [heckeXi_trivialModulus_one K hs, dedekindZeta_thirdCyclotomic K hs]

/-- The polar prefactor gives the continued scattering value at zero. -/
theorem bianchiScatteringPhase_zero : bianchiScatteringPhase 0 = -1 := by
  have h01 : xiBianchi 0 = xiBianchi 1 := by
    simpa only [sub_zero] using (xiBianchi_one_sub 0).symm
  have h1 : xiBianchi 1 ≠ 0 := xiBianchi_ne_zero_of_one_le_re (by norm_num)
  simp only [bianchiScatteringPhase, mul_zero, add_zero, zero_sub, h01,
    div_self h1]
  norm_num

/-- On the punctured spectral axis the scattering phase is the literal completed quotient. -/
theorem bianchiScatteringPhase_axis_eq_completedRatio {t : ℝ} (ht : t ≠ 0) :
    bianchiScatteringPhase ((t : ℂ) * I) =
      completedBianchiZeta (2 * ((t : ℂ) * I)) /
        completedBianchiZeta (1 + 2 * ((t : ℂ) * I)) := by
  symm
  apply completedBianchiZeta_div_eq_bianchiScatteringPhase
  · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) Complex.I_ne_zero
  · intro h
    have := congrArg Complex.re h
    norm_num at this
  · intro h
    have := congrArg Complex.re h
    norm_num at this
  · intro h
    have := congrArg Complex.re h
    norm_num at this
  · intro h
    have hi := congrArg Complex.im h
    norm_num at hi
    exact ht (by linarith only [hi])

/-- The actual scattering phase is unitary and has the unconditional one-sixteenth pulse rate. -/
theorem eisenstein_scattering_certificate :
    bianchiScatteringPhase 0 = -1 ∧
    (∀ t : ℝ, ‖bianchiScatteringPhase ((t : ℂ) * I)‖ = 1) ∧
    (∀ ε : ℝ, 0 < ε → ∀ h : BlackHoleRingdown.CompactPulse,
      ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
        ‖bianchiReflectedField h τ‖ ≤ C * Real.exp (-(1 / 16 - ε) * τ)) :=
  ⟨bianchiScatteringPhase_zero, norm_bianchiScatteringPhase_axis,
    fun _ hε h => bianchi_pulse_ringdown_one_sixteenth hε h⟩

#print axioms gammaFactor_chi3D
#print axioms chi3D_primitive_rootNumber
#print axioms completedBianchiZeta_eq_gamma_product
#print axioms xiBianchi_eq_gamma_product
#print axioms thirdCyclotomic_primitive_hecke_completion
#print axioms bianchiScatteringPhase_axis_eq_completedRatio
#print axioms eisenstein_scattering_certificate
#print axioms heckeLFunction_thirdCyclotomic_zero_mem_quasiRH_strip

end GaloisForLFunctions.RingdownOfTheCubicCover
