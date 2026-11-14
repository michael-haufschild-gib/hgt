import GaloisForLFunctions.RingdownOfTheCubicCover.UnconditionalScatteringResonanceBounds
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheSquareOfANumberRingThroughItsIdealsHasTheIndexOfItsDedekindZetaFunction

/-!
# The primitive Eisenstein family with its full completion

For the third cyclotomic field, `χ₋₃` has root number `+1` and
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

local notation "K₃" => CyclotomicField 3 ℚ

local instance : NeZero ((3 : ℕ) : ℚ) := ⟨by norm_num⟩
local instance : IsCyclotomicExtension {3} ℚ K₃ :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
local instance : NumberField K₃ := IsCyclotomicExtension.numberField {3} ℚ K₃

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
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
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
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have hxi : xiBianchi s = s * (s - 1) / 2 * completedBianchiZeta s := by
    rw [xiBianchi, _root_.RHTower.xi_eq_half_mul hs0 hs1, completedBianchiZeta]
    ring
  rw [hxi, completedBianchiZeta_eq_gamma_product hs]

/-- The primitive trivial Hecke character, with both poles and all completion factors retained. -/
theorem thirdCyclotomic_primitive_hecke_completion :
    heckeFiniteConductor (trivialModulus K₃) 1 = (trivialModulus K₃).fin ∧
      ∀ s : ℂ, 1 < s.re →
        heckeXi (trivialModulus K₃) 1 s =
          s * (s - 1) * (heckeCompletionFactor (trivialModulus K₃) s *
            heckeGammaFactor (trivialModulus K₃) 1 s *
              (riemannZeta s * DirichletCharacter.LFunction chi3D s)) := by
  refine ⟨heckeFiniteConductor_trivialModulus K₃ 1, fun s hs => ?_⟩
  rw [heckeXi_trivialModulus_one K₃ hs, dedekindZeta_thirdCyclotomic K₃ hs]

/-- The continued Hecke source is the actual Dedekind product, with its simple pole retained. -/
theorem thirdCyclotomic_hecke_source_and_pole :
    (∀ s : ℂ, s ≠ 1 → heckeLFunction (trivialModulus K₃) 1 s =
      riemannZeta s * DirichletCharacter.LFunction chi3D s) ∧
    meromorphicOrderAt (heckeLFunction (trivialModulus K₃) 1) 1 = (-1 : ℤ) :=
  ⟨fun _ hs => heckeLFunction_thirdCyclotomic_trivial K₃ hs,
    meromorphicOrderAt_heckeLFunction_one (trivialModulus K₃)⟩

/-- Primitive reflection retains the arithmetic Gauss/parity phase, whose modulus is one. -/
theorem thirdCyclotomic_hecke_reflection :
    ‖heckeRootNumber (trivialModulus K₃) 1‖ = 1 ∧
      ∀ s : ℂ, heckeXi (trivialModulus K₃) 1 (1 - s) =
        heckeRootNumber (trivialModulus K₃) 1 * heckeXi (trivialModulus K₃) 1 s := by
  have hprim := heckeFiniteConductor_trivialModulus K₃ 1
  refine ⟨norm_heckeRootNumber (trivialModulus K₃) 1 hprim, fun s => ?_⟩
  have hinv : (1 : HeckeCharacter (trivialModulus K₃))⁻¹ = 1 :=
    hecke_inv_eq_one_iff.mpr rfl
  simpa only [hinv] using heckeXi_one_sub (trivialModulus K₃) 1 hprim s

/-- The actual Eisenstein-field Hecke source inherits the certified strip without a cancellation premise. -/
theorem thirdCyclotomic_hecke_zero_strip {s : ℂ} (hs1 : s ≠ 1) (hs0 : 0 < s.re)
    (hz : heckeLFunction (trivialModulus K₃) 1 s = 0) :
    s.re ∈ Set.Icc (1 / 8 : ℝ) (7 / 8 : ℝ) :=
  heckeLFunction_thirdCyclotomic_zero_mem_quasiRH_strip K₃ hs1 hs0 hz

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

/-- The off-real scattering factorization retains the odd Gamma quotient and polar factor. -/
theorem bianchiScatteringPhase_eq_explicit_gamma_factors {u : ℂ} (him : u.im ≠ 0) :
    bianchiScatteringPhase u =
      ((3 : ℂ) ^ (2 * u / 2) / (3 : ℂ) ^ ((1 + 2 * u) / 2)) *
        (2 / (2 * u - 1)) * BlackHoleRingdown.scatterQ (u + 1 / 2) *
        (DirichletCharacter.LFunction chi3D (2 * u) *
          (DirichletCharacter.LFunction chi3D (1 + 2 * u))⁻¹ *
          (Complex.Gammaℝ (2 * u + 1) / Complex.Gammaℝ (2 * u + 2))) := by
  rw [bianchiScatteringPhase_eq_factors him, gammaFactor_chi3D, gammaFactor_chi3D]
  rw [show (1 + 2 * u + 1 : ℂ) = 2 * u + 2 by ring]

/-- The actual scattering phase is unitary and has the unconditional one-sixteenth pulse rate. -/
theorem eisenstein_scattering_certificate :
    bianchiScatteringPhase 0 = -1 ∧
    (∀ t : ℝ, ‖bianchiScatteringPhase ((t : ℂ) * I)‖ = 1) ∧
    (∀ ε : ℝ, 0 < ε → ∀ h : BlackHoleRingdown.CompactPulse,
      ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
        ‖bianchiReflectedField h τ‖ ≤ C * Real.exp (-(1 / 16 - ε) * τ)) := by
  refine ⟨bianchiScatteringPhase_zero, norm_bianchiScatteringPhase_axis, ?_⟩
  apply (bianchi_hecke_zeroFreeStrip_iff_pulse_ringdown K₃ (δ := 1 / 16)
    (by norm_num) (by norm_num)).mp
  intro ρ hρ1 hρ hρ0
  simpa only [show (1 : ℝ) - 2 * (1 / 16) = 7 / 8 by norm_num] using
    (thirdCyclotomic_hecke_zero_strip hρ1 hρ0 hρ).2

#print axioms gammaFactor_chi3D
#print axioms chi3D_primitive_rootNumber
#print axioms completedBianchiZeta_eq_gamma_product
#print axioms xiBianchi_eq_gamma_product
#print axioms thirdCyclotomic_primitive_hecke_completion
#print axioms thirdCyclotomic_hecke_source_and_pole
#print axioms thirdCyclotomic_hecke_reflection
#print axioms thirdCyclotomic_hecke_zero_strip
#print axioms bianchiScatteringPhase_axis_eq_completedRatio
#print axioms bianchiScatteringPhase_eq_explicit_gamma_factors
#print axioms eisenstein_scattering_certificate

end GaloisForLFunctions.RingdownOfTheCubicCover
