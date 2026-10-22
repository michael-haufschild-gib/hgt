import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualTwoAdicWildBreak
import GaloisForLFunctions.HTGeometry.UniformizerPowerBasis

/-!
# Literal monogenic two-adic localization of the SST quaternion field

For every prime `P` above two, its contraction `Q` to the biquadratic field has relative
inertia degree one and relative ramification index two.  The fundamental ramification identity
then proves that `P` is the unique prime above `Q`, so the local extension is finite.  Residue
degree one supplies exact residue approximation, while the literal top radical is already known
to be a uniformizer satisfying `z² = 2b` with `b` a unit.  Consequently `{1, z}` is a basis of
the localized top integers over the localized biquadratic integers.
-/

namespace RHTower

open scoped NumberField Pointwise
open IsDiscreteValuationRing
noncomputable section

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => deningerQ8RootNumberNegOneTopField

local instance q8MonoCharZeroK2 : CharZero K2 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K2).injective
local instance q8MonoCharZeroK3 : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
noncomputable local instance q8MonoFiniteDimensionalRatK1 : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis
noncomputable local instance q8MonoFiniteDimensionalK1K2 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis
noncomputable local instance q8MonoFiniteDimensionalRatK2 : FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis
noncomputable local instance q8MonoFiniteDimensionalK2K3 : FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis
noncomputable local instance q8MonoFiniteDimensionalRatK3 : FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3
noncomputable local instance q8MonoNumberFieldK2 : NumberField K2 := NumberField.mk
noncomputable local instance q8MonoNumberFieldK3 : NumberField K3 := NumberField.mk

noncomputable def q8BiquadTwoAdicU : 𝓞 K2 :=
  ⟨algebraMap K1 K2 q8BiquadU,
    q8BiquadU_isIntegral.map (IsScalarTower.toAlgHom ℤ K1 K2)⟩

theorem q8BiquadTwoAdicU_sq : q8BiquadTwoAdicU ^ 2 = q8BiquadTwoAdicU + 1 := by
  apply Subtype.ext
  change (algebraMap K1 K2 q8BiquadU) ^ 2 = algebraMap K1 K2 q8BiquadU + 1
  rw [← map_pow, q8BiquadU_sq, map_add, map_one]

theorem q8Biquad_two_three_le_residue_natCard
    (Q : Ideal (𝓞 K2)) [Q.IsMaximal] (hQtwo : (2 : 𝓞 K2) ∈ Q) :
    3 ≤ Nat.card ((𝓞 K2) ⧸ Q) := by
  letI : Nontrivial ((𝓞 K2) ⧸ Q) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsMaximal.ne_top inferInstance)
  let ubar : (𝓞 K2) ⧸ Q := Ideal.Quotient.mk Q q8BiquadTwoAdicU
  have hrel : ubar ^ 2 = ubar + 1 :=
    congrArg (Ideal.Quotient.mk Q) q8BiquadTwoAdicU_sq
  have htwo : (2 : (𝓞 K2) ⧸ Q) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hQtwo
  have hu0 : ubar ≠ 0 := by
    intro hu
    rw [hu] at hrel
    simp at hrel
  have hu1 : ubar ≠ 1 := by
    intro hu
    rw [hu] at hrel
    norm_num at hrel
    have : (1 : (𝓞 K2) ⧸ Q) = 0 := hrel.trans htwo
    exact one_ne_zero this
  let f : Fin 3 → ((𝓞 K2) ⧸ Q)
    | 0 => 0
    | 1 => 1
    | 2 => ubar
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  simpa using Nat.card_le_card_of_injective f hf

theorem q8Literal_two_relative_inertiaDeg_eq_one
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    P.inertiaDeg (𝓞 K2) = 1 := by
  let Q : Ideal (𝓞 K2) := P.comap (algebraMap (𝓞 K2) (𝓞 K3))
  letI : Q.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := 𝓞 K2) (S := 𝓞 K3) P
  letI : P.LiesOver Q := ⟨rfl⟩
  have hQtwo : (2 : 𝓞 K2) ∈ Q := by
    change algebraMap (𝓞 K2) (𝓞 K3) 2 ∈ P
    simpa only [map_ofNat] using hPtwo
  have hPglobal : P.inertiaDeg ℤ = 2 :=
    q8Literal_two_inertiaDeg_eq_two P hPtwo
  have htower := Ideal.inertiaDeg_tower (R := ℤ) Q P
  rw [hPglobal] at htower
  have hrelPos : 0 < P.inertiaDeg (𝓞 K2) := Ideal.inertiaDeg_pos P (𝓞 K2)
  have hQPos : 0 < Q.inertiaDeg ℤ := Ideal.inertiaDeg_pos Q ℤ
  have hQle : Q.inertiaDeg ℤ ≤ 2 := by
    exact Nat.le_of_dvd (by norm_num) ⟨P.inertiaDeg (𝓞 K2), htower⟩
  have hrelLe : P.inertiaDeg (𝓞 K2) ≤ 2 := by
    exact Nat.le_of_dvd (by norm_num)
      ⟨Q.inertiaDeg ℤ, by simpa [mul_comm] using htower⟩
  have hQneOne : Q.inertiaDeg ℤ ≠ 1 := by
    intro hQone
    let p : Ideal ℤ := Ideal.span {(2 : ℤ)}
    letI : p.IsMaximal := Int.prime_two.isMaximal_span_singleton
    have hQover : Q.LiesOver p := by
      rw [Ideal.liesOver_span_iff (Ideal.IsMaximal.ne_top inferInstance) Int.prime_two]
      simpa [p] using hQtwo
    letI : Q.LiesOver p := hQover
    have hnorm : Nat.card ((𝓞 K2) ⧸ Q) = 2 ^ Q.inertiaDeg ℤ := by
      calc
        Nat.card ((𝓞 K2) ⧸ Q) = Submodule.cardQuot Q := by
          rw [Submodule.cardQuot_apply]
        _ = Ideal.absNorm Q := (Ideal.absNorm_apply Q).symm
        _ = 2 ^ (Ideal.span {(2 : ℤ)}).inertiaDeg' Q :=
          Ideal.absNorm_eq_pow_inertiaDeg' Q Nat.prime_two
        _ = 2 ^ Q.inertiaDeg ℤ := by
          rw [Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(2 : ℤ)}) Q]
    rw [hQone] at hnorm
    norm_num at hnorm
    have hthree := q8Biquad_two_three_le_residue_natCard Q hQtwo
    omega
  have hQtwo : Q.inertiaDeg ℤ = 2 := by omega
  rw [hQtwo] at htower
  omega

theorem q8Literal_two_relative_ramificationIdx_eq_two
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    P.ramificationIdx (𝓞 K2) = 2 := by
  let p : Ideal ℤ := Ideal.span {(2 : ℤ)}
  let Q : Ideal (𝓞 K2) := P.comap (algebraMap (𝓞 K2) (𝓞 K3))
  letI : Q.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := 𝓞 K2) (S := 𝓞 K3) P
  letI : P.LiesOver Q := ⟨rfl⟩
  have hQtwo : (2 : 𝓞 K2) ∈ Q := by
    change algebraMap (𝓞 K2) (𝓞 K3) 2 ∈ P
    simpa only [map_ofNat] using hPtwo
  have hQover : Q.LiesOver p := by
    rw [Ideal.liesOver_span_iff (Ideal.IsMaximal.ne_top inferInstance) Int.prime_two]
    simpa [p] using hQtwo
  have hQram : Q.ramificationIdx ℤ = 1 :=
    q8Biquad_two_isUnramifiedIn.ramificationIdx_eq_one hQover
  have htower := Ideal.ramificationIdx_tower (R := ℤ) Q P
  rw [q8Literal_two_ramificationIdx_eq_two P hPtwo, hQram] at htower
  simpa using htower.symm

theorem q8Literal_ringOfIntegers_relative_finrank_eq_two :
    Module.finrank (𝓞 K2) (𝓞 K3) = 2 := by
  have hK3K2 : Module.finrank K2 K3 = 2 := by
    exact deningerQ8RootNumberNegOneTopField_finrank_over_second
  rw [← hK3K2]
  exact (Algebra.IsAlgebraic.finrank_of_isFractionRing
    (𝓞 K2) K2 (𝓞 K3) K3).symm

theorem q8Literal_two_relative_primesOver_eq_singleton
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    let Q : Ideal (𝓞 K2) := P.comap (algebraMap (𝓞 K2) (𝓞 K3))
    Q.primesOver (𝓞 K3) = {P} := by
  classical
  let Q : Ideal (𝓞 K2) := P.comap (algebraMap (𝓞 K2) (𝓞 K3))
  letI : Q.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := 𝓞 K2) (S := 𝓞 K3) P
  letI : P.LiesOver Q := ⟨rfl⟩
  letI : Fintype (Q.primesOver (𝓞 K3)) := Fintype.ofFinite _
  let pP : Q.primesOver (𝓞 K3) := Ideal.primesOver.mk Q P
  let term : Q.primesOver (𝓞 K3) → ℕ := fun R =>
    R.1.ramificationIdx (𝓞 K2) * R.1.inertiaDeg (𝓞 K2)
  have hsum : ∑ R : Q.primesOver (𝓞 K3), term R = 2 := by
    change (∑ R : Q.primesOver (𝓞 K3),
      R.1.ramificationIdx (𝓞 K2) * R.1.inertiaDeg (𝓞 K2)) = 2
    rw [Ideal.sum_ramification_inertia_eq_finrank,
      q8Literal_ringOfIntegers_relative_finrank_eq_two]
  have htermP : term pP = 2 := by
    change P.ramificationIdx (𝓞 K2) * P.inertiaDeg (𝓞 K2) = 2
    rw [q8Literal_two_relative_ramificationIdx_eq_two P hPtwo,
      q8Literal_two_relative_inertiaDeg_eq_one P hPtwo]
  have herase : ∑ R ∈ Finset.univ.erase pP, term R = 0 := by
    have hsplit := Finset.sum_erase_add Finset.univ term (Finset.mem_univ pP)
    rw [htermP, hsum] at hsplit
    omega
  apply Set.ext
  intro R
  constructor
  · intro hR
    haveI : R.IsPrime := hR.1
    letI : R.LiesOver Q := hR.2
    let pR : Q.primesOver (𝓞 K3) := Ideal.primesOver.mk Q R
    have hpReq : pR = pP := by
      by_contra hne
      have hmem : pR ∈ Finset.univ.erase pP :=
        Finset.mem_erase.mpr ⟨hne, Finset.mem_univ pR⟩
      have hle : term pR ≤ ∑ S ∈ Finset.univ.erase pP, term S :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
      have hpos : 0 < term pR := by
        exact Nat.mul_pos (Ideal.ramificationIdx_pos R (𝓞 K2))
          (Ideal.inertiaDeg_pos R (𝓞 K2))
      rw [herase] at hle
      omega
    simpa [pR, pP] using congrArg Subtype.val hpReq
  · intro hR
    have : R = P := Set.mem_singleton_iff.mp hR
    subst R
    exact ⟨inferInstance, inferInstance⟩

theorem q8Biquad_two_local_addVal_two_eq_one
    (Q : Ideal (𝓞 K2)) [Q.IsMaximal] (hQtwo : (2 : 𝓞 K2) ∈ Q) :
    let A := Localization.AtPrime Q
    letI : IsDiscreteValuationRing A :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
        (𝓞 K2) (show Q ≠ ⊥ from by
          intro hQ
          rw [hQ, Ideal.mem_bot] at hQtwo
          norm_num at hQtwo) A
    addVal A (2 : A) = 1 := by
  let p : Ideal ℤ := Ideal.span {(2 : ℤ)}
  have hQover : Q.LiesOver p := by
    rw [Ideal.liesOver_span_iff (Ideal.IsMaximal.ne_top inferInstance) Int.prime_two]
    simpa [p] using hQtwo
  letI : Q.LiesOver p := hQover
  let A := Localization.AtPrime Q
  letI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (𝓞 K2) (show Q ≠ ⊥ from by
        intro hQ
        rw [hQ, Ideal.mem_bot] at hQtwo
        norm_num at hQtwo) A
  letI : CharZero A := charZero_of_injective_algebraMap
    (IsLocalization.injective A Q.primeCompl_le_nonZeroDivisors)
  have hram : Q.ramificationIdx ℤ = 1 :=
    q8Biquad_two_isUnramifiedIn.ramificationIdx_eq_one hQover
  have hlen : (Module.length A (A ⧸ p.map (algebraMap ℤ A))).toNat = 1 := by
    rw [← Ideal.ramificationIdx_eq p Q]
    exact hram
  have hmap : p.map (algebraMap ℤ A) = Ideal.span {(2 : A)} := by
    simp [p, Ideal.map_span]
  rw [hmap, dvr_length_quotient_span_eq_addVal (by norm_num : (2 : A) ≠ 0)] at hlen
  have hfinite : addVal A (2 : A) ≠ ⊤ := by
    rw [Ne, addVal_eq_top_iff]
    norm_num
  calc
    addVal A (2 : A) = ((addVal A (2 : A)).toNat : ℕ∞) :=
      (ENat.coe_toNat hfinite).symm
    _ = 1 := by rw [hlen]; norm_num

theorem q8Literal_two_local_residue_approximation
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    let Q : Ideal (𝓞 K2) := P.comap (algebraMap (𝓞 K2) (𝓞 K3))
    let A := Localization.AtPrime Q
    let B := Localization.AtPrime P
    letI : Algebra A B := Localization.AtPrime.algebraOfLiesOver Q P
    letI : IsDiscreteValuationRing B :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
        (𝓞 K3) (show P ≠ ⊥ from by
          intro hP
          rw [hP, Ideal.mem_bot] at hPtwo
          norm_num at hPtwo) B
    ∀ b : B, ∃ a : A, addVal B (b - algebraMap A B a) ≠ 0 := by
  let Q : Ideal (𝓞 K2) := P.comap (algebraMap (𝓞 K2) (𝓞 K3))
  letI : Q.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := 𝓞 K2) (S := 𝓞 K3) P
  letI : P.LiesOver Q := ⟨rfl⟩
  let A := Localization.AtPrime Q
  let B := Localization.AtPrime P
  letI : Algebra A B := Localization.AtPrime.algebraOfLiesOver Q P
  letI : IsDiscreteValuationRing B :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (𝓞 K3) (show P ≠ ⊥ from by
        intro hP
        rw [hP, Ideal.mem_bot] at hPtwo
        norm_num at hPtwo) B
  have hfinrank : Module.finrank Q.ResidueField P.ResidueField = 1 := by
    rw [← Ideal.inertiaDeg_eq Q P]
    exact q8Literal_two_relative_inertiaDeg_eq_one P hPtwo
  have hresSurj : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) :=
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfinrank).2
  change ∀ x : B, ∃ a : A, addVal B (x - algebraMap A B a) ≠ 0
  intro x
  obtain ⟨r, hr⟩ := hresSurj (IsLocalRing.residue B x)
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := A) r
  refine ⟨a, ?_⟩
  intro hzero
  have hu : IsUnit (x - algebraMap A B a) := addVal_eq_zero_iff.mp hzero
  have hreszero : IsLocalRing.residue B (x - algebraMap A B a) = 0 := by
    rw [map_sub, ← IsLocalRing.ResidueField.algebraMap_residue, hr, sub_self]
  have hmem : x - algebraMap A B a ∈ IsLocalRing.maximalIdeal B :=
    (IsLocalRing.residue_eq_zero_iff _).mp hreszero
  exact (IsLocalRing.notMem_maximalIdeal.mpr hu) hmem

noncomputable def q8Literal_two_local_uniformizerPowBasis
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    let Q : Ideal (𝓞 K2) := P.comap (algebraMap (𝓞 K2) (𝓞 K3))
    let A := Localization.AtPrime Q
    let B := Localization.AtPrime P
    letI : Algebra A B := Localization.AtPrime.algebraOfLiesOver Q P
    letI : Module.Finite A B := Localization.finite_of_primesOver_eq_singleton
      (q8Literal_two_relative_primesOver_eq_singleton P hPtwo)
    Module.Basis (Fin 2) A B := by
  let Q : Ideal (𝓞 K2) := P.comap (algebraMap (𝓞 K2) (𝓞 K3))
  letI : Q.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := 𝓞 K2) (S := 𝓞 K3) P
  letI : P.LiesOver Q := ⟨rfl⟩
  have hQtwo : (2 : 𝓞 K2) ∈ Q := by
    change algebraMap (𝓞 K2) (𝓞 K3) 2 ∈ P
    simpa only [map_ofNat] using hPtwo
  let A := Localization.AtPrime Q
  let B := Localization.AtPrime P
  letI : Algebra A B := Localization.AtPrime.algebraOfLiesOver Q P
  letI : Module.Finite A B := Localization.finite_of_primesOver_eq_singleton
    (q8Literal_two_relative_primesOver_eq_singleton P hPtwo)
  letI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (𝓞 K2) (show Q ≠ ⊥ from by
        intro hQ
        rw [hQ, Ideal.mem_bot] at hQtwo
        norm_num at hQtwo) A
  letI : IsDiscreteValuationRing B :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (𝓞 K3) (show P ≠ ⊥ from by
        intro hP
        rw [hP, Ideal.mem_bot] at hPtwo
        norm_num at hPtwo) B
  let z : B := algebraMap (𝓞 K3) B q8LiteralTwoAdicZ
  have hpiVal : addVal A (2 : A) = 1 :=
    q8Biquad_two_local_addVal_two_eq_one Q hQtwo
  have hpi : Irreducible (2 : A) :=
    GaloisForLFunctions.HTGeometry.irreducible_of_addVal_eq_one hpiVal
  have hram : addVal B (algebraMap A B (2 : A)) = (2 : ℕ∞) := by
    simpa only [map_ofNat] using q8Literal_two_local_addVal_two_eq_two P hPtwo
  have hzVal : addVal B z = 1 :=
    q8Literal_two_local_addVal_topRadical_eq_one P hPtwo
  have hres : ∀ b : B, ∃ a : A, addVal B (b - algebraMap A B a) ≠ 0 :=
    q8Literal_two_local_residue_approximation P hPtwo
  have hdvd : algebraMap A B (2 : A) ∣ z ^ 2 := by
    let f : 𝓞 K3 →+* B := algebraMap (𝓞 K3) B
    refine ⟨f q8LiteralTwoAdicUnitCoefficient, ?_⟩
    rw [map_ofNat]
    change z ^ 2 = (2 : B) * f q8LiteralTwoAdicUnitCoefficient
    dsimp [z, q8LiteralTwoAdicUnitCoefficient]
    rw [← map_ofNat f 2]
    simpa only [map_pow, map_mul, map_add, map_ofNat, mul_assoc] using
      congrArg f q8LiteralTwoAdicZ_sq
  exact GaloisForLFunctions.HTGeometry.uniformizerPowBasis
    hpi 2 hram hzVal hres hdvd

theorem q8Literal_two_local_exists_linearCoordinates
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    let Q : Ideal (𝓞 K2) := P.comap (algebraMap (𝓞 K2) (𝓞 K3))
    let A := Localization.AtPrime Q
    let B := Localization.AtPrime P
    letI : Algebra A B := Localization.AtPrime.algebraOfLiesOver Q P
    letI : Module.Finite A B := Localization.finite_of_primesOver_eq_singleton
      (q8Literal_two_relative_primesOver_eq_singleton P hPtwo)
    ∀ y : B, ∃ a₀ a₁ : A,
      y = algebraMap A B a₀ + algebraMap A B a₁ *
        algebraMap (𝓞 K3) B q8LiteralTwoAdicZ := by
  let Q : Ideal (𝓞 K2) := P.comap (algebraMap (𝓞 K2) (𝓞 K3))
  letI : Q.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := 𝓞 K2) (S := 𝓞 K3) P
  letI : P.LiesOver Q := ⟨rfl⟩
  let A := Localization.AtPrime Q
  let B := Localization.AtPrime P
  letI : Algebra A B := Localization.AtPrime.algebraOfLiesOver Q P
  letI : Module.Finite A B := Localization.finite_of_primesOver_eq_singleton
    (q8Literal_two_relative_primesOver_eq_singleton P hPtwo)
  let b : Module.Basis (Fin 2) A B :=
    q8Literal_two_local_uniformizerPowBasis P hPtwo
  change ∀ y : B, ∃ a₀ a₁ : A,
    y = algebraMap A B a₀ + algebraMap A B a₁ *
      algebraMap (𝓞 K3) B q8LiteralTwoAdicZ
  intro y
  refine ⟨b.repr y 0, b.repr y 1, ?_⟩
  have hy := b.sum_repr y
  rw [Fin.sum_univ_two] at hy
  simpa [b, q8Literal_two_local_uniformizerPowBasis,
    GaloisForLFunctions.HTGeometry.uniformizerPowBasis, Module.Basis.coe_mk,
    Algebra.smul_def] using hy.symm

end
end RHTower
