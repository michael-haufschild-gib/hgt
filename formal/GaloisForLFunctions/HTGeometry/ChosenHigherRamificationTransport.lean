import AlgebraicNumberTheory.Completion.ChosenLocalization
import AlgebraicNumberTheory.Completion.ExtensionIndex
import RamificationTheory.HilbertRamification.LocalizationRamificationGroups
import LocalFieldTheory.NonarchimedeanLocalField.PrincipalUnitQuotients

noncomputable section

open scoped NumberField Classical ValuativeRel NNReal
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open LocalFieldTheory

namespace HilbertRamification

variable {K L : Type}
  [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

abbrev chosenGlobalValuationRing (v₀ : HeightOneSpectrum (𝓞 K)) :=
  absoluteValueValuationSubring
    (chosenFinitePlaceExtension (L := L) v₀).1
    (finitePlaceExtension_nonarchimedean
      (K := K) (L := L) v₀ (chosenFinitePlaceExtension (L := L) v₀))

abbrev chosenLocalIntegerRing (v₀ : HeightOneSpectrum (𝓞 K)) :=
  𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀]

noncomputable local instance chosenLocalIntegerRingIsLocal
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    IsLocalRing (chosenLocalIntegerRing (K := K) (L := L) v₀) :=
  ValuationSubring.isLocalRing
    ((ValuativeRel.valuation
      (ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀)).valuationSubring)

noncomputable def chosenGlobalToLocalIntegerRing
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    chosenGlobalValuationRing (K := K) (L := L) v₀ →+*
      chosenLocalIntegerRing (K := K) (L := L) v₀ where
  toFun x := ⟨AbsoluteValue.toAlgebraicLocalization
      (HeightOneSpectrum.adicAbv K v₀)
      (chosenFinitePlaceExtension (L := L) v₀).1
      (chosenFinitePlaceExtension (L := L) v₀).2 (x : L), by
    apply (localizedCompletion_mem_integers_iff_norm_le_one
      (HeightOneSpectrum.adicAbv K v₀)
      (chosenFinitePlaceExtension (L := L) v₀)
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀) _).2
    change (AbsoluteValue.algebraicLocalizationAbsoluteValue
      (HeightOneSpectrum.adicAbv K v₀)
      (chosenFinitePlaceExtension (L := L) v₀).1
      (chosenFinitePlaceExtension (L := L) v₀).2)
        (AbsoluteValue.toAlgebraicLocalization
          (HeightOneSpectrum.adicAbv K v₀)
          (chosenFinitePlaceExtension (L := L) v₀).1
          (chosenFinitePlaceExtension (L := L) v₀).2 (x : L)) ≤ 1
    rw [AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization]
    exact (mem_absoluteValueValuationSubring_iff _ _ _).mp x.property⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem chosenGlobalToLocalIntegerRing_mem_maximalIdeal_pow
    (v₀ : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    {x : chosenGlobalValuationRing (K := K) (L := L) v₀}
    (hx : x ∈ IsLocalRing.maximalIdeal
      (chosenGlobalValuationRing (K := K) (L := L) v₀) ^ n) :
    chosenGlobalToLocalIntegerRing (K := K) (L := L) v₀ x ∈
      IsLocalRing.maximalIdeal
        𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] ^ n := by
  let f := chosenGlobalToLocalIntegerRing (K := K) (L := L) v₀
  have hmap : Ideal.map f
      (IsLocalRing.maximalIdeal
        (chosenGlobalValuationRing (K := K) (L := L) v₀)) ≤
      IsLocalRing.maximalIdeal
        𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    change f y ∈ IsLocalRing.maximalIdeal
      𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    have hyAbs : (chosenFinitePlaceExtension (L := L) v₀).1 (y : L) < 1 :=
      (absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one _ _ y).mp hy
    have hyNorm : ‖(f y :
        𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀])‖ < 1 := by
      change (AbsoluteValue.algebraicLocalizationAbsoluteValue
        (HeightOneSpectrum.adicAbv K v₀)
        (chosenFinitePlaceExtension (L := L) v₀).1
        (chosenFinitePlaceExtension (L := L) v₀).2)
          (AbsoluteValue.toAlgebraicLocalization
            (HeightOneSpectrum.adicAbv K v₀)
            (chosenFinitePlaceExtension (L := L) v₀).1
            (chosenFinitePlaceExtension (L := L) v₀).2 (y : L)) < 1
      rw [AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization]
      exact hyAbs
    apply (Valuation.Integer.not_isUnit_iff_valuation_lt_one).2
    let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀
    let zE : E := (f y : 𝒪[E])
    rw [lt_iff_not_ge]
    intro hge
    have hgeRel : (1 : E) ≤ᵥ zE :=
      (Valuation.Compatible.vle_iff_le
        (v := ValuativeRel.valuation E) (1 : E) zE).2 hge
    have hgeVal : (1 : ℝ≥0) ≤ (Valued.v : Valuation E ℝ≥0) zE :=
      by simpa using
        (Valuation.Compatible.vle_iff_le
          (v := (Valued.v : Valuation E ℝ≥0)) (1 : E) zE).1 hgeRel
    have hgeNorm : (1 : ℝ) ≤ ‖zE‖ := by exact_mod_cast hgeVal
    exact (not_le_of_gt hyNorm) hgeNorm
  have hxmap := Ideal.mem_map_of_mem f hx
  rw [Ideal.map_pow] at hxmap
  exact (pow_le_pow_left' hmap n) hxmap

noncomputable def chosenLocalIntegerRingAut
    (v₀ : HeightOneSpectrum (𝓞 K))
    (τ : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀ ≃ₐ[
      ChosenFinitePlaceBaseCompletion (K := K) v₀]
        ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀) :
    𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] ≃+*
      𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] where
  toFun x := ⟨τ (x : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀), by
    apply (localizedCompletion_mem_integers_iff_norm_le_one
      (HeightOneSpectrum.adicAbv K v₀)
      (chosenFinitePlaceExtension (L := L) v₀)
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀) _).2
    have hx := (localizedCompletion_mem_integers_iff_norm_le_one
      (HeightOneSpectrum.adicAbv K v₀)
      (chosenFinitePlaceExtension (L := L) v₀)
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀) _).1 x.property
    change (AbsoluteValue.algebraicLocalizationAbsoluteValue
      (HeightOneSpectrum.adicAbv K v₀)
      (chosenFinitePlaceExtension (L := L) v₀).1
      (chosenFinitePlaceExtension (L := L) v₀).2) (τ (x : _)) ≤ 1
    rw [algebraicLocalizationDensity_localizationAbsoluteValue_algEquiv
      (HeightOneSpectrum.adicAbv K v₀)
      (chosenFinitePlaceExtension (L := L) v₀)
      (RayClass.adicAbv_isNontrivial v₀) τ]
    exact hx⟩
  invFun x := ⟨τ.symm (x : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀), by
    apply (localizedCompletion_mem_integers_iff_norm_le_one
      (HeightOneSpectrum.adicAbv K v₀)
      (chosenFinitePlaceExtension (L := L) v₀)
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀) _).2
    have hx := (localizedCompletion_mem_integers_iff_norm_le_one
      (HeightOneSpectrum.adicAbv K v₀)
      (chosenFinitePlaceExtension (L := L) v₀)
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀) _).1 x.property
    change (AbsoluteValue.algebraicLocalizationAbsoluteValue
      (HeightOneSpectrum.adicAbv K v₀)
      (chosenFinitePlaceExtension (L := L) v₀).1
      (chosenFinitePlaceExtension (L := L) v₀).2) (τ.symm (x : _)) ≤ 1
    rw [algebraicLocalizationDensity_localizationAbsoluteValue_algEquiv
      (HeightOneSpectrum.adicAbv K v₀)
      (chosenFinitePlaceExtension (L := L) v₀)
      (RayClass.adicAbv_isNontrivial v₀) τ.symm]
    exact hx⟩
  left_inv x := by
    apply Subtype.ext
    exact τ.symm_apply_apply (x : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀)
  right_inv x := by
    apply Subtype.ext
    exact τ.apply_symm_apply (x : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul τ
      (x : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀)
      (y : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀)
  map_add' x y := by
    apply Subtype.ext
    exact map_add τ
      (x : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀)
      (y : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀)

theorem chosenLocalIntegerRingAut_mem_maximalIdeal_pow_iff
    (v₀ : HeightOneSpectrum (𝓞 K))
    (τ : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀ ≃ₐ[
      ChosenFinitePlaceBaseCompletion (K := K) v₀]
        ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀)
    (n : ℕ) (x : 𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀]) :
    chosenLocalIntegerRingAut (K := K) (L := L) v₀ τ x ∈
        IsLocalRing.maximalIdeal
          𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] ^ n ↔
      x ∈ IsLocalRing.maximalIdeal
          𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] ^ n :=
  ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff
    (chosenLocalIntegerRingAut (K := K) (L := L) v₀ τ) n x

theorem chosenGlobalToLocalIntegerRing_denseRange
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    DenseRange (chosenGlobalToLocalIntegerRing (K := K) (L := L) v₀) := by
  rw [Metric.denseRange_iff]
  intro z r hr
  let vK := HeightOneSpectrum.adicAbv K v₀
  let w := chosenFinitePlaceExtension (L := L) v₀
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀
  have heps : 0 < min r 1 := lt_min hr (by norm_num)
  obtain ⟨x, hx⟩ :=
    algebraicLocalizationDensity_localization_exists_close vK w
      (z : E) heps
  have hz : ‖(z : E)‖ ≤ 1 :=
    (localizedCompletion_mem_integers_iff_norm_le_one vK w
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v₀) _).1 z.property
  have hstrong : ‖(z : E) + -((z : E) -
      AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x)‖ ≤
      max ‖(z : E)‖ ‖-((z : E) -
        AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x)‖ :=
    IsUltrametricDist.norm_add_le_max _ _
  have hxLocal : ‖AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x‖ ≤ 1 := by
    calc
      ‖AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x‖ =
          ‖(z : E) + -((z : E) -
            AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x)‖ := by
        congr 1
        ring
      _ ≤ max ‖(z : E)‖ ‖-((z : E) -
          AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x)‖ := hstrong
      _ = max ‖(z : E)‖ ‖(z : E) -
          AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x‖ := by rw [norm_neg]
      _ ≤ 1 := max_le hz (hx.le.trans (min_le_right _ _))
  have hxGlobal : w.1 x ≤ 1 := by
    change ‖AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x‖ ≤ 1 at hxLocal
    rw [← AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization
      vK w.1 w.2 x]
    exact hxLocal
  let xA : chosenGlobalValuationRing (K := K) (L := L) v₀ :=
    ⟨x, (mem_absoluteValueValuationSubring_iff _ _ _).mpr hxGlobal⟩
  refine ⟨xA, ?_⟩
  rw [dist_eq_norm]
  change ‖(z : E) - AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x‖ < r
  exact hx.trans_le (min_le_left _ _)

set_option maxHeartbeats 800000 in
theorem chosenGlobalToLocalIntegerRing_exists_approx_mod_maximalIdeal_pow
    (v₀ : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (z : 𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀]) :
    ∃ x : chosenGlobalValuationRing (K := K) (L := L) v₀,
      z - chosenGlobalToLocalIntegerRing (K := K) (L := L) v₀ x ∈
        IsLocalRing.maximalIdeal
          𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] ^ n := by
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀
  let I := IsLocalRing.maximalIdeal
    𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] ^ n
  have hIopen : IsOpen (I : Set 𝒪[ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) v₀]) :=
    I.toAddSubgroup.isOpen_of_mem_nhds (LocalFieldTheory.maximalIdeal_pow_mem_nhds_zero E n)
  let U : Set 𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] :=
    {y | y - z ∈ I}
  have hUopen : IsOpen U := hIopen.preimage (continuous_id.sub continuous_const)
  have hUne : U.Nonempty := by
    refine ⟨z, ?_⟩
    change z - z ∈ I
    rw [sub_self]
    exact I.zero_mem
  obtain ⟨x, hx⟩ :=
    (chosenGlobalToLocalIntegerRing_denseRange (K := K) (L := L) v₀).exists_mem_open
      hUopen hUne
  refine ⟨x, ?_⟩
  have hx' : chosenGlobalToLocalIntegerRing (K := K) (L := L) v₀ x - z ∈ I := hx
  have hneg := I.neg_mem hx'
  convert hneg using 1 <;> ring

theorem displacement_mem_of_dense_ideal_approximation
    {A B : Type*} [CommRing A] [CommRing B]
    (I : Ideal B) (f : A →+* B) (τ : B ≃+* B)
    (happrox : ∀ z : B, ∃ x : A, z - f x ∈ I)
    (hstable : ∀ e : B, e ∈ I → τ e ∈ I)
    (hmain : ∀ x : A, τ (f x) - f x ∈ I)
    (z : B) : τ z - z ∈ I := by
  obtain ⟨x, hx⟩ := happrox z
  let e : B := z - f x
  have he : e ∈ I := hx
  have herror : τ e - e ∈ I := I.sub_mem (hstable e he) he
  have hdecomp : τ z - z = (τ e - e) + (τ (f x) - f x) := by
    dsimp only [e]
    rw [map_sub]
    ring
  rw [hdecomp]
  exact I.add_mem herror (hmain x)

set_option maxHeartbeats 1200000 in
theorem chosenDecompositionDisplacement_mem_local_of_global
    (v₀ : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (σ : RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup K
      (chosenGlobalValuationRing (K := K) (L := L) v₀))
    (hσ : ∀ x : chosenGlobalValuationRing (K := K) (L := L) v₀,
      σ • x - x ∈ IsLocalRing.maximalIdeal
        (chosenGlobalValuationRing (K := K) (L := L) v₀) ^ n)
    (z : 𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀]) :
    let vK := HeightOneSpectrum.adicAbv K v₀
    let w := chosenFinitePlaceExtension (L := L) v₀
    let τD := localizationRamificationGroups_valuationDecompositionGroupEquiv
      vK (RayClass.adicAbv_isNontrivial v₀) w
        (finitePlaceExtension_nonarchimedean (K := K) (L := L) v₀ w) σ
    let τ : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀ ≃ₐ[
      ChosenFinitePlaceBaseCompletion (K := K) v₀]
        ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀ := τD
    chosenLocalIntegerRingAut (K := K) (L := L) v₀ τ z - z ∈
      IsLocalRing.maximalIdeal
        𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] ^ n := by
  let vK := HeightOneSpectrum.adicAbv K v₀
  let w := chosenFinitePlaceExtension (L := L) v₀
  let hw := finitePlaceExtension_nonarchimedean (K := K) (L := L) v₀ w
  let τD := localizationRamificationGroups_valuationDecompositionGroupEquiv
    vK (RayClass.adicAbv_isNontrivial v₀) w hw σ
  let τ : ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀ ≃ₐ[
      ChosenFinitePlaceBaseCompletion (K := K) v₀]
        ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀ := τD
  let eτ := chosenLocalIntegerRingAut (K := K) (L := L) v₀ τ
  let f := chosenGlobalToLocalIntegerRing (K := K) (L := L) v₀
  let I := IsLocalRing.maximalIdeal
    𝒪[ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v₀] ^ n
  apply displacement_mem_of_dense_ideal_approximation I f eτ
  · exact chosenGlobalToLocalIntegerRing_exists_approx_mod_maximalIdeal_pow
      (K := K) (L := L) v₀ n
  · intro e he
    exact (chosenLocalIntegerRingAut_mem_maximalIdeal_pow_iff
      (K := K) (L := L) v₀ τ n e).2 he
  · intro x
    have hglobal := hσ x
    have hmainMapped : f (σ • x - x) ∈ I :=
      chosenGlobalToLocalIntegerRing_mem_maximalIdeal_pow
        (K := K) (L := L) v₀ n hglobal
    have hcomm : eτ (f x) - f x = f (σ • x - x) := by
      apply Subtype.ext
      change τ (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 (x : L)) -
          AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 (x : L) =
        AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
          (((σ : RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup K
            (chosenGlobalValuationRing (K := K) (L := L) v₀)) : L ≃ₐ[K] L)
              (x : L) - (x : L))
      rw [map_sub,
        localizationRamificationGroups_valuationDecompositionGroupEquiv_toLocalization]
    rw [hcomm]
    exact hmainMapped

end HilbertRamification
