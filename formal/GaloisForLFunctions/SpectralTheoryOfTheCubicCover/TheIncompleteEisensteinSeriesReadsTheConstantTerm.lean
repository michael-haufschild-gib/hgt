import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheCubicEisensteinSeriesUnfolds
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicCuspVolumeCoordinates
import GaloisForLFunctions.MetaplecticMobiusDescent.PrimitiveCubicEisensteinRows

/-!
# The incomplete Eisenstein series reads the constant term

The cusp stabilizer `Γ∞` of the level-three group acts on `ℍ³` by the translations
`z + jv ↦ z + b + jv`, `b ∈ 3ℤ[ω]` (`cuspSubgroup_smul_upperPoint`), and `k ↦ b(k)` is a bijection
onto the period lattice (`translationOf_injective`, `translationOf_surjective`). Hence the strip
`{w : z(w) ∈ P}` over the period parallelogram `P` meets every `Γ∞`-orbit exactly once
(`cuspStrip_unique`, `CuspDomain.strip`). In the coordinates `(v, z)` its volume is
`v^{−3} dv dz` (`cuspStrip_coordinates`).

With the unfolding of `TheCubicEisensteinSeriesUnfolds` this gives, for `F` of multiplier `κ⁻¹` with
`F · ψ(v)` integrable on the strip (`integral_mul_incompleteEisenstein_eq_constantTerm`),

`∫_{D_Γ} F(w) E(w ∣ ψ) dμ = ∫_0^∞ ψ(v) (∫_P F(z + jv) dz) v^{−3} dv`:

the incomplete Eisenstein series pairs a height profile with the constant term of `F`. For
`ψ(t) = t^s` it is the Mellin transform of the constant term
(`integral_mul_hyperbolicEisenstein_eq_constantTerm`), the first step of the Rankin–Selberg method on
the cubic cover.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical MatrixGroups ENNReal

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein

/-! ### `Γ∞` is the period lattice -/

/-- The translation `b(k)` of `k ∈ Γ∞`. -/
def translationOf (k : cuspSubgroup) : ℂ := ringComplex ((k : SL(2, O)) 0 1)

theorem cuspSubgroup_lower (k : cuspSubgroup) : (k : SL(2, O)) 1 0 = 0 := by
  obtain ⟨T, hT, hTk⟩ := Subgroup.mem_map.mp k.2
  rw [← hTk]
  exact (mem_cuspStabilizer_iff T).mp hT

theorem cuspSubgroup_matrix (k : cuspSubgroup) :
    integralComplexMatrix (k : SL(2, O)) = complexTranslation (translationOf k) :=
  levelThree_integral_eq_translation ⟨k, cuspSubgroup_le k.2⟩ (cuspSubgroup_lower k)

theorem cuspSubgroup_smul_upperPoint (k : cuspSubgroup) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    k • upperPoint z v hv = upperPoint (z + translationOf k) v hv := by
  rw [integralSubgroup_smul, cuspSubgroup_matrix, complexTranslation_action]

theorem translationOf_mem (k : cuspSubgroup) : translationOf k ∈ periodLattice := by
  obtain ⟨n, hn⟩ := levelThree_upper ⟨k, cuspSubgroup_le k.2⟩
  have hn' : (k : SL(2, O)) 0 1 = 3 * n := hn
  rw [translationOf, hn', map_mul, map_ofNat]
  exact three_embedding_mem n

theorem translationOf_injective : Function.Injective translationOf := by
  intro k₁ k₂ h
  have hm : integralComplexMatrix (k₁ : SL(2, O)) = integralComplexMatrix (k₂ : SL(2, O)) := by
    rw [cuspSubgroup_matrix, cuspSubgroup_matrix, h]
  exact Subtype.ext (integralComplexMatrix_injective hm)

/-- The translation matrix `[[1, 3n], [0, 1]]`. -/
def translationMatrix (n : O) : SL(2, O) :=
  ⟨!![1, 3 * n; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem translationMatrix_mem (n : O) : translationMatrix n ∈ levelThree := by
  apply levelThree_of_entries
  intro i j
  fin_cases i <;> fin_cases j <;> simp [translationMatrix]

theorem translationMatrix_cusp (n : O) :
    (⟨translationMatrix n, translationMatrix_mem n⟩ : levelThree) ∈ cuspStabilizer :=
  (mem_cuspStabilizer_iff _).mpr (by simp [translationMatrix])

theorem translationOf_surjective (b : ℂ) (hb : b ∈ periodLattice) :
    ∃ k : cuspSubgroup, translationOf k = b := by
  obtain ⟨n, hn⟩ := periodPoint_bijective.2 ⟨b, hb⟩
  refine ⟨toCusp ⟨translationMatrix n, translationMatrix_mem n⟩ (translationMatrix_cusp n), ?_⟩
  have hb' : 3 * ringComplex n = b := congrArg Subtype.val hn
  have h01 : (translationMatrix n) 0 1 = 3 * n := by simp [translationMatrix]
  change ringComplex ((translationMatrix n) 0 1) = b
  rw [h01, map_mul, map_ofNat, hb']

/-! ### The period strip -/

/-- The period strip `{w : z(w) ∈ P}`. -/
def cuspStripSet : Set HyperbolicSpace := {w | hyperbolicHorizontal w ∈ periodDomain}

theorem cuspStripSet_measurable : MeasurableSet cuspStripSet :=
  periodDomain_measurable.preimage hyperbolicHorizontal_continuous.measurable

/-- **The strip is a strict fundamental set of `Γ∞`.** -/
theorem cuspStrip_unique (w : HyperbolicSpace) : ∃! k : cuspSubgroup, k • w ∈ cuspStripSet := by
  obtain ⟨z, v, hv, rfl⟩ := upperPoint_surjective w
  have hmem : ∀ k : cuspSubgroup,
      k • upperPoint z v hv ∈ cuspStripSet ↔ z + translationOf k ∈ periodDomain := by
    intro k
    rw [cuspSubgroup_smul_upperPoint]
    simp only [cuspStripSet, Set.mem_setOf_eq, hyperbolicHorizontal_upperPoint]
  obtain ⟨ℓ, hℓ, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain periodBasis z
  obtain ⟨k, hk⟩ := translationOf_surjective ℓ ℓ.2
  have hz : z + translationOf k ∈ periodDomain := by
    rw [hk, add_comm]
    exact hℓ
  refine ⟨k, (hmem k).mpr hz, fun k' hk' => ?_⟩
  have h1 := (hmem k').mp hk'
  apply translationOf_injective
  have h := periodDomain_unique_translate _ _ (translationOf k' - translationOf k) h1 hz
    (sub_mem (translationOf_mem k') (translationOf_mem k)) (by ring)
  linear_combination h

/-- The period strip as a `CuspDomain`. -/
def CuspDomain.strip : CuspDomain := ⟨cuspStripSet, cuspStripSet_measurable, cuspStrip_unique⟩

/-! ### Coordinates on the strip -/

/-- The Euclidean preimage `{(x, y, v) : v > 0, x + iy ∈ P}` of the strip. -/
def stripEuclidean : Set EuclideanSpatial :=
  spatialComplexSplit ⁻¹' (Set.Ioi (0 : ℝ) ×ˢ periodDomain)

theorem stripEuclidean_measurable : MeasurableSet stripEuclidean :=
  spatialComplexSplit.measurable (measurableSet_Ioi.prod periodDomain_measurable)

theorem stripEuclidean_positive : stripEuclidean ⊆ euclideanUpperHalf := by
  intro p hp
  change 0 < p 2
  exact hp.1

theorem stripEuclidean_preimage :
    hyperbolicEuclideanCoordinates ⁻¹' stripEuclidean = cuspStripSet := by
  ext w
  change spatialComplexSplit (hyperbolicEuclideanCoordinates w) ∈ (Set.Ioi (0 : ℝ) ×ˢ periodDomain) ↔ _
  rw [spatialComplexSplit_coordinates]
  exact ⟨fun h => h.2, fun h => ⟨hyperbolicHeight_pos w, h⟩⟩

/-- **The strip in coordinates.** If `g` is integrable on the strip, then
`(v, z) ↦ g(z + jv) v^{−3}` is integrable on `(0, ∞) × P` and
`∫_{strip} g dμ = ∫_0^∞ (∫_P g(z + jv) dz) v^{−3} dv`. -/
theorem cuspStrip_coordinates (g : HyperbolicSpace → ℂ)
    (hg : IntegrableOn g cuspStripSet hyperbolicVolume) :
    IntegrableOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q) / (q.1 : ℂ) ^ 3)
        (Set.Ioi (0 : ℝ) ×ˢ periodDomain) volume ∧
      ∫ w in cuspStripSet, g w ∂hyperbolicVolume =
        ∫ v in Set.Ioi (0 : ℝ), (∫ z in periodDomain, g (cuspCoordinateLift (v, z))) / (v : ℂ) ^ 3 := by
  have hm := euclideanToHyperbolic_measurePreserving_on stripEuclidean stripEuclidean_measurable
  rw [stripEuclidean_preimage] at hm
  set h : ℝ × ℂ → ℂ := fun q => g (cuspCoordinateLift q) / (q.1 : ℂ) ^ 3 with hh
  have hcomp : ∀ p, h (spatialComplexSplit p) = g (euclideanToHyperbolic p) / (p 2 : ℂ) ^ 3 := by
    intro p
    simp only [hh, cuspCoordinateLift, spatialComplexSplit.symm_apply_apply, spatialComplexSplit_fst]
  -- integrability in coordinates
  have hE : hyperbolicEuclideanVolume.restrict stripEuclidean =
      (volume.restrict stripEuclidean).withDensity hyperbolicDensity := by
    rw [hyperbolicEuclideanVolume, restrict_withDensity stripEuclidean_measurable,
      Measure.restrict_restrict stripEuclidean_measurable,
      Set.inter_eq_left.mpr stripEuclidean_positive]
  have hI1 : Integrable (g ∘ euclideanToHyperbolic) (hyperbolicEuclideanVolume.restrict stripEuclidean) :=
    (hm.integrable_comp hg.aestronglyMeasurable).mpr hg
  rw [hE, integrable_withDensity_iff_integrable_smul' hyperbolicDensity_measurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hI1
  have hI2 : IntegrableOn (h ∘ spatialComplexSplit) stripEuclidean volume := by
    refine hI1.congr ?_
    filter_upwards [ae_restrict_mem stripEuclidean_measurable] with p hp
    have h2 : 0 < p 2 := stripEuclidean_positive hp
    rw [Function.comp_apply, Function.comp_apply, hcomp p, hyperbolicDensity,
      ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
    simp only [Complex.ofReal_inv, Complex.ofReal_pow, div_eq_mul_inv, mul_comm]
  have hI3 : IntegrableOn h (Set.Ioi (0 : ℝ) ×ˢ periodDomain) volume :=
    (spatialComplexSplit_preserves_volume.integrableOn_comp_preimage
      spatialComplexSplit.measurableEmbedding).mp hI2
  refine ⟨hI3, ?_⟩
  -- the integral
  have he : ∫ w in cuspStripSet, g w ∂hyperbolicVolume =
      ∫ p in stripEuclidean, g (euclideanToHyperbolic p) ∂hyperbolicEuclideanVolume := by
    have hh' := hg.aestronglyMeasurable
    rw [← hm.map_eq] at hh' ⊢
    exact integral_map hm.measurable.aemeasurable hh'
  rw [he, hyperbolicEuclidean_setIntegral_complex stripEuclidean stripEuclidean_measurable
    stripEuclidean_positive]
  have hsplit := spatialComplexSplit.measurableEmbedding.setIntegral_map h
    (Set.Ioi (0 : ℝ) ×ˢ periodDomain) («μ» := (volume : Measure EuclideanSpatial))
  rw [spatialComplexSplit_preserves_volume.map_eq] at hsplit
  have heq : ∫ p in stripEuclidean, g (euclideanToHyperbolic p) / (p 2 : ℂ) ^ 3 =
      ∫ q in Set.Ioi (0 : ℝ) ×ˢ periodDomain, h q := by
    rw [hsplit]
    exact setIntegral_congr_fun stripEuclidean_measurable (fun p _ => (hcomp p).symm)
  rw [heq]
  change ∫ q in Set.Ioi (0 : ℝ) ×ˢ periodDomain, h q ∂((volume : Measure ℝ).prod volume) = _
  rw [setIntegral_prod _ hI3]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  exact integral_div ((v : ℂ) ^ 3) (fun z => g (cuspCoordinateLift (v, z)))

/-! ### The constant term -/

/-- **The incomplete Eisenstein series reads the constant term.** For `F` of multiplier `κ⁻¹` with
`F · ψ(v)` integrable on the strip:
`∫_{D_Γ} F · E(·∣ψ) dμ = ∫_0^∞ ψ(v) (∫_P F(z + jv) dz) v^{−3} dv`. -/
theorem integral_mul_incompleteEisenstein_eq_constantTerm (F : HyperbolicSpace → ℂ)
    (hF : ∀ (M : levelThree) (w : HyperbolicSpace), F (complexMatrix M • w) = (complexCharacter M)⁻¹ * F w)
    (ψ : ℝ → ℂ) (hint : IntegrableOn (unfolded F ψ) cuspStripSet hyperbolicVolume) :
    ∫ w in levelSet, F w * incompleteEisenstein ψ w ∂hyperbolicVolume =
      ∫ v in Set.Ioi (0 : ℝ), ψ v * (∫ z in periodDomain, F (cuspCoordinateLift (v, z))) / (v : ℂ) ^ 3 := by
  rw [integral_mul_incompleteEisenstein CuspDomain.strip F hF ψ hint]
  change ∫ w in cuspStripSet, unfolded F ψ w ∂hyperbolicVolume = _
  rw [(cuspStrip_coordinates _ hint).2]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  have hlift : ∀ z, unfolded F ψ (cuspCoordinateLift (v, z)) = ψ v * F (cuspCoordinateLift (v, z)) := by
    intro z
    have hh : hyperbolicHeight (cuspCoordinateLift (v, z)) = v := by
      rw [cuspCoordinateLift_positive v z hv, hyperbolicHeight_upperPoint]
    rw [unfolded, hh, mul_comm]
  simp_rw [hlift, integral_const_mul]

/-- **The Mellin transform of the constant term.** For `F` of multiplier `κ⁻¹` with `F v^s`
integrable on the strip: `∫_{D_Γ} F · E(·, s) dμ = ∫_0^∞ v^{s−3} (∫_P F(z + jv) dz) dv`. -/
theorem integral_mul_hyperbolicEisenstein_eq_constantTerm (F : HyperbolicSpace → ℂ)
    (hF : ∀ (M : levelThree) (w : HyperbolicSpace), F (complexMatrix M • w) = (complexCharacter M)⁻¹ * F w)
    (s : ℂ) (hint : IntegrableOn (unfolded F (fun t => (t : ℂ) ^ s)) cuspStripSet hyperbolicVolume) :
    ∫ w in levelSet, F w * hyperbolicEisenstein s w ∂hyperbolicVolume =
      ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s * (∫ z in periodDomain, F (cuspCoordinateLift (v, z))) /
        (v : ℂ) ^ 3 := by
  simp_rw [← incompleteEisenstein_cpow]
  exact integral_mul_incompleteEisenstein_eq_constantTerm F hF _ hint

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
