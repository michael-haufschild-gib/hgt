import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.FiniteIdelicArtin

/-! The finite idelic Artin maps commute with restriction in a tower.
Choose a diagonal normalization for one modulus divisible by both
conductors and apply restriction to the Artin symbols of its ideals. -/

noncomputable section

open NumberField IsDedekindDomain FractionalIdeal GaloisForLFunctions
open GaloisForLFunctions.HeckeLFunctions
open scoped nonZeroDivisors

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay

/-- Divisibility of finite moduli bounds their local exponents. -/
theorem exponent_le_of_dvd {K : Type*} [Field K] [NumberField K]
    {m n : Modulus K} (hm : m.fin ∣ n.fin) (v : HeightOneSpectrum (𝓞 K)) :
    exponent m v ≤ exponent n v := by
  exact v.multiplicity_le_of_ideal_ge (Ideal.dvd_iff_le.mp hm) n.fin_ne_bot

private theorem idelesOneMod_le_of_dvd {K : Type*} [Field K] [NumberField K]
    {m n : Modulus K} (hm : m.fin ∣ n.fin) (hi : m.inf ⊆ n.inf) :
    idelesOneMod n ≤ idelesOneMod m := by
  intro x hx
  obtain ⟨hf, hpos⟩ := (mem_idelesOneMod n).mp hx
  exact (mem_idelesOneMod m).mpr ⟨fun v hv => unitsLevel_antitone v
    (exponent_le_of_dvd hm v) (hf v (hv.trans hm)), fun w hw => hpos w (hi hw)⟩

universe u

variable (K L M : Type u) (G Γ : Type u) [Field K] [NumberField K]
  [Field L] [NumberField L] [Field M] [NumberField M] [Algebra K L] [Algebra K M]
  [Algebra L M] [IsScalarTower K L M] [CommGroup G] [Fintype G]
  [MulSemiringAction G L] [IsGaloisGroup G K L] [CommGroup Γ] [Fintype Γ]
  [MulSemiringAction Γ M] [IsGaloisGroup Γ K M]

theorem finite_idelic_artin_restrict (m n : Modulus K)
    (φ : IdeleGroup K →* G) (ψ : IdeleGroup K →* Γ)
    (hφd : ∀ a : Kˣ, φ (diagonal K a) = 1) (hψd : ∀ a : Kˣ, ψ (diagonal K a) = 1)
    (hφu : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ m.fin → IsUnramifiedPrime K L G v)
    (hψu : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ n.fin → IsUnramifiedPrime K M Γ v)
    (hφ : ∀ x : idelesOneMod m, φ x.val = artinMap K L G (toFractionalIdeal x.val))
    (hψ : ∀ x : idelesOneMod n, ψ x.val = artinMap K M Γ (toFractionalIdeal x.val)) :
    (IsGaloisGroup.restrictHom Γ G K L M).comp ψ = φ := by
  let o : Modulus K :=
    ⟨m.fin * n.fin, by
      simpa only [Ideal.zero_eq_bot] using mul_ne_zero
        (show m.fin ≠ 0 from m.fin_ne_bot) (show n.fin ≠ 0 from n.fin_ne_bot),
      m.inf ∪ n.inf⟩
  have ho₁ : idelesOneMod o ≤ idelesOneMod m :=
    idelesOneMod_le_of_dvd (dvd_mul_right _ _) Set.subset_union_left
  have ho₂ : idelesOneMod o ≤ idelesOneMod n :=
    idelesOneMod_le_of_dvd (dvd_mul_left _ _) Set.subset_union_right
  apply MonoidHom.ext
  intro x
  obtain ⟨a, ha⟩ := exists_diagonal_mul_mem_idelesOneMod o x
  set y := diagonal K a * x
  have hmy : y ∈ idelesOneMod m := ho₁ ha
  have hny : y ∈ idelesOneMod n := ho₂ ha
  have hφy : φ y = φ x := by simp [y, hφd]
  have hψy : ψ y = ψ x := by simp [y, hψd]
  change IsGaloisGroup.restrictHom Γ G K L M (ψ x) = φ x
  rw [← hψy, ← hφy, hψ ⟨y, hny⟩, hφ ⟨y, hmy⟩]
  refine restrictHom_artinMap K L M fun v hv => ⟨hφu v ?_, hψu v ?_⟩
  · intro hm
    exact hv ((count_toFractionalIdeal v y).trans (ord_eq_zero_of_mem_idelesOneMod m hmy hm))
  · intro hn
    exact hv ((count_toFractionalIdeal v y).trans (ord_eq_zero_of_mem_idelesOneMod n hny hn))

end GlobalTheory.Reciprocity
