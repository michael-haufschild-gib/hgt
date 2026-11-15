import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheDegreeTwoCharacterOfTheCubeRootsOfTwoHasItsHodgeIndex
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.QuasiRiemannHypothesis

/-!
# The Artin function of the cube roots of two carries the seed

E6 asks which families admit a seed. The seed of MMD holds for every Hecke `L`-function of finite
order of `ℚ(ω)` on its theta-lattice continuation (`hecke_nonzero`). The splitting field of `X³ − 2`
has group `S₃`, and its degree-two Artin character `ρ` has the `L`-function of the cubic character
`χ` of `2` over `ℚ(ω)`, a ray class character modulo `6` (AGZ `cubicTwoHecke`), whose contacts are
the point counts `#{x³ = 2} − 1` (AGZ `heckeMangoldt_cubicTwoHecke`).

* **The bridge** (`idealCoeff_sixHeckeFamilyCharacter`, `LFunction_sixHeckeFamilyCharacter_eq`):
  the MMD character with the residue of `χ` on `(O/6)^×` (`sixHeckeFamilyCharacter`) has the ideal
  coefficients of `χ`, and the entire function `Ξ_χ(s)/(N^{s/2}Γ(s))` (`artinCont`) is its
  `L`-function everywhere: they agree on `Re s > 1` as sums over the nonzero ideals.
* **The seed for `ρ`** (`heckeXi_cubicTwoHecke_ne_zero`, `re_le_seven_eighths_of_mem_artinZeros`):
  the completed `L(s, ρ)` has no zero on `Re s > 7/8`. A non-abelian Artin `L`-function admits the
  seed of `ζ`.
-/

noncomputable section

open NumberField Complex Set

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

open GaloisForLFunctions.AbsoluteGeometryOfSpecZ GaloisForLFunctions.AbsoluteGeometryOfSpecZ.CubeRootsOfTwo
open MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicEisenstein HeckeLFunctions

local instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

/-- The residue character of `χ` on `O/6`, with values in `ℂ`. -/
def sixResidueMulChar : MulChar (O ⧸ Ideal.span {(6 : O)}) ℂ :=
  MulChar.ofUnitHom ((Units.map ringComplex.toMonoidHom).comp sixResidueChar)

/-- An element coprime to `6` is a unit modulo `6`. -/
theorem isUnit_mk_of_sup_eq_top {a : O} (h : Ideal.span {a} ⊔ Ideal.span {(6 : O)} = ⊤) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(6 : O)}) a) := by
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 h)
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  have hz0 : Ideal.Quotient.mk (Ideal.span {(6 : O)}) z = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hz
  refine isUnit_of_mul_eq_one _ (Ideal.Quotient.mk _ c) ?_
  rw [← map_mul, mul_comm, ← sub_eq_of_eq_add' hyz.symm, map_sub, hz0, sub_zero, map_one]

/-- On a residue `a mod 6` the character is `(π_{(a)} mod 2)`. -/
theorem sixResidueMulChar_mk (a : O) :
    sixResidueMulChar (Ideal.Quotient.mk _ a) = ringComplex (twoCubicOf a) := by
  by_cases hu : IsUnit (Ideal.Quotient.mk (Ideal.span {(6 : O)}) a)
  · have h := MulChar.ofUnitHom_coe ((Units.map ringComplex.toMonoidHom).comp sixResidueChar)
      hu.unit
    rw [IsUnit.unit_spec] at h
    rw [sixResidueMulChar, h, MonoidHom.comp_apply, Units.coe_map, coe_sixResidueChar_mk hu]
    rfl
  · rw [MulChar.map_nonunit _ hu]
    have h0 : twoCubicOf a = 0 := by
      by_contra hne
      exact hu (isUnit_mk_of_sup_eq_top ((twoCubicValue_ne_zero_iff (Ideal.span {a})).1 hne))
    rw [h0, map_zero]

theorem sixResidueMulChar_unit (u : Oˣ) :
    sixResidueMulChar (Ideal.Quotient.mk (Ideal.span {(6 : O)}) (u : O)) = 1 := by
  rw [sixResidueMulChar_mk, twoCubicOf_unit, map_one]

/-- The MMD character of the cubic character of `2`. -/
def sixHeckeFamilyCharacter : HeckeFamily.Character :=
  HeckeFamily.Character.ofResidue (Ideal.span {(6 : O)}) sixModulus.fin_ne_bot sixResidueMulChar
    sixResidueMulChar_unit

theorem sixHeckeFamilyCharacter_residue_ne_one : sixHeckeFamilyCharacter.residue ≠ 1 := by
  intro h1
  have hu := isUnit_mk_six good_one_add_three_omega.1 good_one_add_three_omega.2
  have h := sixResidueMulChar_mk (1 + 3 * omega)
  change sixHeckeFamilyCharacter.residue _ = _ at h
  rw [h1, MulChar.one_apply hu] at h
  exact twoCubicOf_one_add_three_omega_ne_one (ringComplex_injective (by rw [map_one]; exact h.symm))

/-- **The bridge on ideals**: the MMD coefficients are the values of `χ`. -/
theorem idealCoeff_sixHeckeFamilyCharacter (I : Ideal O) :
    HeckeFamily.idealCoeff sixHeckeFamilyCharacter I = heckeValue sixModulus cubicTwoHecke I := by
  rw [heckeValue_cubicTwoHecke]
  by_cases hI : I = ⊥
  · subst hI
    rw [twoCubicValue_bot, map_zero]
    exact HeckeFamily.idealCoeff_zero _
  · obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal I).principal
    have ha' : Ideal.span ({a} : Set O) = I := ha.symm
    change IdealCharacter.ofResidue (Ideal.span {(6 : O)}) sixResidueMulChar _ I = _
    rw [IdealCharacter.ofResidue_of_generator _ _ _ hI ha', sixResidueMulChar_mk, twoCubicOf, ha']

/-- On `Re s > 1` the MMD `L`-function is `L(s, χ)`. -/
theorem LFunction_sixHeckeFamilyCharacter_eq_heckeL {s : ℂ} (hs : 1 < s.re) :
    HeckeFamily.LFunction sixHeckeFamilyCharacter s = heckeL sixModulus cubicTwoHecke s := by
  rw [HeckeFamily.LFunction_eq_ideal_tsum _ hs, heckeL_eq_tsum_ideals sixModulus cubicTwoHecke hs]
  have hsupp : Function.support (HeckeFamily.idealTerm sixHeckeFamilyCharacter s) ⊆
      (nonZeroDivisors (Ideal O) : Set (Ideal O)) := by
    intro I hI
    apply mem_nonZeroDivisors_of_ne_zero
    rintro rfl
    exact hI (by simp [HeckeFamily.idealTerm])
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  refine tsum_congr fun I => ?_
  change HeckeFamily.idealCoeff sixHeckeFamilyCharacter I / (Ideal.absNorm (I : Ideal O) : ℂ) ^ s =
    heckeValue sixModulus cubicTwoHecke I * (Ideal.absNorm (I : Ideal O) : ℂ) ^ (-s)
  rw [idealCoeff_sixHeckeFamilyCharacter, cpow_neg, div_eq_mul_inv]

/-- The entire continuation of `L(s, χ)` from its completion. -/
def artinCont (s : ℂ) : ℂ :=
  (heckeGammaFactor sixModulus cubicTwoHecke s)⁻¹ * (heckeCompletionFactor sixModulus s)⁻¹ *
    heckeXi sixModulus cubicTwoHecke s

theorem differentiable_artinCont : Differentiable ℂ artinCont :=
  ((differentiable_heckeGammaFactor_inv sixModulus cubicTwoHecke).mul
    ((differentiable_heckeCompletionFactor sixModulus).inv
      (heckeCompletionFactor_ne_zero sixModulus))).mul (differentiable_heckeXi sixModulus cubicTwoHecke)

theorem artinCont_eq_heckeL {s : ℂ} (hs : 1 < s.re) : artinCont s = heckeL sixModulus cubicTwoHecke s := by
  have hΓ := heckeGammaFactor_ne_zero sixModulus cubicTwoHecke (show 0 < s.re by linarith)
  have hN := heckeCompletionFactor_ne_zero sixModulus s
  rw [artinCont, heckeXi_of_ne_one cubicTwoHecke_ne_one, heckeCompletedLFunction_eq _ _ hs]
  field_simp

/-- **The bridge**: the MMD `L`-function of `χ` is the continuation of `L(s, χ)` everywhere. -/
theorem LFunction_sixHeckeFamilyCharacter_eq (s : ℂ) :
    HeckeFamily.LFunction sixHeckeFamilyCharacter s = artinCont s := by
  have hL : Differentiable ℂ (HeckeFamily.LFunction sixHeckeFamilyCharacter) := by
    have h := HeckeFamily.continuedLattice_entire_nonprincipal sixHeckeFamilyCharacter
      sixHeckeFamilyCharacter_residue_ne_one
    exact fun z => (h z).div_const 6
  have hA : AnalyticOnNhd ℂ (HeckeFamily.LFunction sixHeckeFamilyCharacter) univ :=
    fun z _ => hL.analyticAt z
  have hB : AnalyticOnNhd ℂ artinCont univ := fun z _ => differentiable_artinCont.analyticAt z
  have hev : HeckeFamily.LFunction sixHeckeFamilyCharacter =ᶠ[nhds (2 : ℂ)] artinCont := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (1 : ℝ) < (2 : ℂ).re)] with z hz
    rw [LFunction_sixHeckeFamilyCharacter_eq_heckeL hz, artinCont_eq_heckeL hz]
  exact hA.eqOn_of_preconnected_of_eventuallyEq hB isPreconnected_univ (mem_univ 2) hev (mem_univ s)

/-- **The seed for the degree-two Artin character of `ℚ(∛2)`**: its completed `L`-function has no
zero on `Re s > 7/8`. -/
theorem heckeXi_cubicTwoHecke_ne_zero {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) :
    heckeXi sixModulus cubicTwoHecke s ≠ 0 := by
  intro h0
  have hG : artinCont s = 0 := by rw [artinCont, h0, mul_zero]
  rw [← LFunction_sixHeckeFamilyCharacter_eq] at hG
  exact ProbeFinalAssemblyUnconditional.hecke_nonzero sixHeckeFamilyCharacter s hs
    (Or.inr sixHeckeFamilyCharacter_residue_ne_one) hG

/-- Every zero of `L(s, ρ)` lies in `Re s ≤ 7/8`. -/
theorem re_le_seven_eighths_of_mem_artinZeros {ρ : ℂ} (hρ : ρ ∈ artinZeros.carrier) :
    ρ.re ≤ 7 / 8 := by
  by_contra h
  exact heckeXi_cubicTwoHecke_ne_zero (lt_of_not_ge h) hρ

#print axioms heckeXi_cubicTwoHecke_ne_zero

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
