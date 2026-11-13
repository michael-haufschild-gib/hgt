/-
Partitions and forcing ideals adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.ExceptionalProfilesAndHeckeSlots

/-!
# Partitions and forcing ideals

Forcing and moving ideals, supported powers of unequal moduli, partition normalizers and
divided frequencies; the norm ledger of the second saving.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentUnequal
open CenteredMomentCorrelation CenteredMomentCommonSupport

section Domain
variable {A : Type*} [CommRing A] [IsDomain A]

theorem divisor_congruence (v t k : A) (hv : v ≠ 0)
    (x : Residue (v * t)) (y : Residue v) :
    scaledResidue (v * t) v ((v * t) * v) rfl x -
      scaledResidue v (v * t) ((v * t) * v) (mul_comm _ _) y =
      Ideal.Quotient.mk _ (v * k) ↔
      x = scaledResidue v t (v * t) rfl y + Ideal.Quotient.mk _ k := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_congruence, scaledResidue_mk, ← map_add, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  change (v * t) * v ∣ v * x - (v * t) * y - v * k ↔ v * t ∣ x - (t * y + k)
  rw [show (v * t) * v = v * (v * t) by ring,
    show v * x - (v * t) * y - v * k = v * (x - (t * y + k)) by ring]
  exact mul_dvd_mul_iff_left hv

theorem fullCorrelation_divisor (v t k : A) (hv : v ≠ 0)
    [Fintype (Residue (v * t))] [Fintype (Residue v)]
    (χu : MulChar (Residue (v * t)) ℂ) (χv : MulChar (Residue v) ℂ) :
    fullModulusCorrelation (v * t) v χu χv (v * k) =
      ∑ y : Residue v, χu (scaledResidue v t (v * t) rfl y + Ideal.Quotient.mk _ k) *
        star (χv y) := by
  unfold fullModulusCorrelation fullCorrelation
  simp_rw [divisor_congruence v t k hv]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem fullCorrelation_divisor_constant (v t k : A) (hv : v ≠ 0)
    [Fintype (Residue (v * t))] [Fintype (Residue v)]
    (χu : MulChar (Residue (v * t)) ℂ) (χv : MulChar (Residue v) ℂ)
    (hχ : ∀ y : Residue v,
      χu (scaledResidue v t (v * t) rfl y + Ideal.Quotient.mk _ k) = χu (Ideal.Quotient.mk _ k)) :
    fullModulusCorrelation (v * t) v χu χv (v * k) =
      χu (Ideal.Quotient.mk _ k) * star (∑ y : Residue v, χv y) := by
  rw [fullCorrelation_divisor v t k hv χu χv]
  simp_rw [hχ]
  rw [← Finset.mul_sum, star_sum]

omit [IsDomain A] in
theorem divisor_lift_constant (p v t k : A) (hpt : p ∣ t)
    (χu : MulChar (Residue (v * t)) ℂ) (χ : MulChar (Residue p) ℂ)
    (hχ : ∀ x : A, χu (Ideal.Quotient.mk _ x) = χ (Ideal.Quotient.mk _ x)) :
    ∀ y : Residue v, χu (scaledResidue v t (v * t) rfl y + Ideal.Quotient.mk _ k) =
      χu (Ideal.Quotient.mk _ k) := by
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_mk, ← map_add, hχ, hχ, map_add, map_mul]
  have ht : Ideal.Quotient.mk (Ideal.span {p}) t = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hpt)
  rw [ht, zero_mul, zero_add]

omit [IsDomain A] in
theorem lifted_character_sum_zero (p v : A) (hpv : p ∣ v)
    [Fintype (Residue p)] [Fintype (Residue v)]
    (χv : MulChar (Residue v) ℂ) (χ : MulChar (Residue p) ℂ) (hχ : χ ≠ 1)
    (hlift : ∀ x : A, χv (Ideal.Quotient.mk _ x) = χ (Ideal.Quotient.mk _ x)) :
    (∑ y : Residue v, χv y) = 0 := by
  let π : Residue v →+* Residue p :=
    Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr hpv)
  have hπ : Function.Surjective π := Ideal.Quotient.factor_surjective _
  have he (y : Residue v) : χv y = χ (π y) := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact hlift y
  simp_rw [he]
  rw [sum_reduction π hπ χ, MulChar.sum_eq_zero_of_ne_one hχ, mul_zero]

theorem fullCorrelation_divisor_eq_zero (p v t k : A) (hv : v ≠ 0)
    (hpv : p ∣ v) (hpt : p ∣ t)
    [Fintype (Residue p)] [Fintype (Residue (v * t))] [Fintype (Residue v)]
    (χu : MulChar (Residue (v * t)) ℂ) (χv : MulChar (Residue v) ℂ)
    (ψu ψv : MulChar (Residue p) ℂ) (hψv : ψv ≠ 1)
    (hu : ∀ x : A, χu (Ideal.Quotient.mk _ x) = ψu (Ideal.Quotient.mk _ x))
    (hv' : ∀ x : A, χv (Ideal.Quotient.mk _ x) = ψv (Ideal.Quotient.mk _ x)) :
    fullModulusCorrelation (v * t) v χu χv (v * k) = 0 := by
  rw [fullCorrelation_divisor_constant v t k hv χu χv
    (divisor_lift_constant p v t k hpt χu ψu hu),
    lifted_character_sum_zero p v hpv χv ψv hψv hv', star_zero, mul_zero]

end Domain
section Eisenstein
open Eisenstein  CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentSupportedCorrelation CenteredMomentCanonical CompletedGauss

local notation "O" => Eisenstein.O

theorem supported_power (p : O) (hp : Supported (Ideal.span {p})) (i : ℕ) :
    Supported (Ideal.span {p ^ i}) := by
  rw [← Ideal.span_singleton_pow]
  exact supported_pow hp i

theorem supported_power_character_mk (p : O) [ (Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    {i : ℕ} (hi : 1 ≤ i) (x : O) :
    supportedModulusCharacter (p ^ i) (supported_power p hp i) (Ideal.Quotient.mk _ x) =
      (complexSexticChar (Ideal.span {p}) hg ^ i) (Ideal.Quotient.mk _ x) := by
  rw [supportedModulusCharacter_mk, ← Ideal.span_singleton_pow, map_pow,
    idealRowHom_prime x (Ideal.span {p}) hg, MulChar.pow_apply' _ (by omega)]

theorem supported_product_power_character_mk (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    {j d : ℕ} (hj : 1 ≤ j) (x : O) :
    supportedModulusCharacter (p ^ j * p ^ d)
      (supported_mul_elements _ _ (supported_power p hp j) (supported_power p hp d))
      (Ideal.Quotient.mk _ x) =
      (complexSexticChar (Ideal.span {p}) hg ^ (j + d)) (Ideal.Quotient.mk _ x) := by
  rw [supportedModulusCharacter_mk, ← pow_add, ← Ideal.span_singleton_pow, map_pow,
    idealRowHom_prime x (Ideal.span {p}) hg, MulChar.pow_apply' _ (by omega)]

theorem unequal_prime_power_zero_of_not_six (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    {j d : ℕ} (hj : 1 ≤ j) (hd : 1 ≤ d) (hj6 : ¬ 6 ∣ j) (k : O) :
    actualCorrelation (p ^ j * p ^ d) (p ^ j)
      (supported_mul_elements _ _ (supported_power p hp j) (supported_power p hp d))
      (supported_power p hp j) (p ^ j * k) = 0 := by
  have hp0 := supported_element_ne_zero p hp
  let := finiteEisensteinQuotientOfNonzero hp0
  let : Fintype (Residue p) := Fintype.ofFinite _
  let := finiteEisensteinQuotientOfNonzero (pow_ne_zero j hp0)
  let : Fintype (Residue (p ^ j)) := Fintype.ofFinite _
  let := finiteEisensteinQuotientOfNonzero (mul_ne_zero (pow_ne_zero j hp0) (pow_ne_zero d hp0))
  let : Fintype (Residue (p ^ j * p ^ d)) := Fintype.ofFinite _
  have hχ : complexSexticChar (Ideal.span {p}) hg ^ j ≠ 1 := by
    intro h
    apply hj6
    rw [← complexSexticChar_order_six (Ideal.span {p}) hg hchar]
    exact orderOf_dvd_of_pow_eq_one h
  exact fullCorrelation_divisor_eq_zero p (p ^ j) (p ^ d) k (pow_ne_zero j hp0)
    (dvd_pow_self p (by omega)) (dvd_pow_self p (by omega))
    (supportedModulusCharacter _ _ ) (supportedModulusCharacter _ _)
    (complexSexticChar (Ideal.span {p}) hg ^ (j + d)) (complexSexticChar (Ideal.span {p}) hg ^ j)
    hχ (supported_product_power_character_mk p hp hg hj)
    (supported_power_character_mk p hp hg hj)

theorem unequal_prime_power_factor (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    {j d : ℕ} (hj : 1 ≤ j) (hd : 1 ≤ d) (k : O) :
    actualCorrelation (p ^ j * p ^ d) (p ^ j)
      (supported_mul_elements _ _ (supported_power p hp j) (supported_power p hp d))
      (supported_power p hp j) (p ^ j * k) =
      (complexSexticChar (Ideal.span {p}) hg ^ (j + d)) (Ideal.Quotient.mk _ k) *
        star (∑' y : Residue (p ^ j), supportedModulusCharacter (p ^ j)
          (supported_power p hp j) y) := by
  have hp0 := supported_element_ne_zero p hp
  let := finiteEisensteinQuotientOfNonzero (pow_ne_zero j hp0)
  let : Fintype (Residue (p ^ j)) := Fintype.ofFinite _
  let := finiteEisensteinQuotientOfNonzero (mul_ne_zero (pow_ne_zero j hp0) (pow_ne_zero d hp0))
  let : Fintype (Residue (p ^ j * p ^ d)) := Fintype.ofFinite _
  have h := fullCorrelation_divisor_constant (p ^ j) (p ^ d) k (pow_ne_zero j hp0)
    (supportedModulusCharacter _ (supported_mul_elements _ _ (supported_power p hp j) (supported_power p hp d)))
    (supportedModulusCharacter _ (supported_power p hp j))
    (divisor_lift_constant p (p ^ j) (p ^ d) k (dvd_pow_self p (by omega))
      _ (complexSexticChar (Ideal.span {p}) hg ^ (j + d))
      (supported_product_power_character_mk p hp hg hj))
  rw [supported_product_power_character_mk p hp hg hj k] at h
  simpa only [actualCorrelation, supportedCorrelation, tsum_fintype] using h

theorem unequal_prime_power_zero_of_nonunit (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    {j d : ℕ} (hj : 1 ≤ j) (hd : 1 ≤ d) (k : O) (hk : p ∣ k) :
    actualCorrelation (p ^ j * p ^ d) (p ^ j)
      (supported_mul_elements _ _ (supported_power p hp j) (supported_power p hp d))
      (supported_power p hp j) (p ^ j * k) = 0 := by
  rw [unequal_prime_power_factor p hp hg hj hd k]
  have hk0 : Ideal.Quotient.mk (Ideal.span {p}) k = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hk)
  rw [hk0, MulChar.map_zero, zero_mul]

theorem unequal_prime_power_norm_le (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    {j d : ℕ} (hj : 1 ≤ j) (hd : 1 ≤ d) (k : O) :
    ‖actualCorrelation (p ^ j * p ^ d) (p ^ j)
      (supported_mul_elements _ _ (supported_power p hp j) (supported_power p hp d))
      (supported_power p hp j) (p ^ j * k)‖ ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ j := by
  have hp0 := supported_element_ne_zero p hp
  let := finiteEisensteinQuotientOfNonzero hp0
  let : Fintype (Residue p) := Fintype.ofFinite _
  let := finiteEisensteinQuotientOfNonzero (pow_ne_zero j hp0)
  let : Fintype (Residue (p ^ j)) := Fintype.ofFinite _
  rw [unequal_prime_power_factor p hp hg hj hd k, norm_mul, norm_star, tsum_fintype]
  calc
    _ ≤ ‖∑ y : Residue (p ^ j), supportedModulusCharacter (p ^ j)
        (supported_power p hp j) y‖ := mul_le_of_le_one_left (norm_nonneg _)
      (FiniteRayExpansion.norm_char_le_one _ _)
    _ ≤ ∑ y : Residue (p ^ j), ‖supportedModulusCharacter (p ^ j)
        (supported_power p hp j) y‖ := norm_sum_le _ _
    _ ≤ ∑ _y : Residue (p ^ j), (1 : ℝ) := Finset.sum_le_sum
      (fun y _ => FiniteRayExpansion.norm_char_le_one _ _)
    _ = _ := by
      rw [← Nat.cast_pow, ← map_pow Ideal.absNorm,
        Ideal.span_singleton_pow]
      simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

theorem unequal_prime_power_support (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    {j d : ℕ} (hj : 1 ≤ j) (hd : 1 ≤ d) (h : O)
    (hne : actualCorrelation (p ^ j * p ^ d) (p ^ j)
      (supported_mul_elements _ _ (supported_power p hp j) (supported_power p hp d))
      (supported_power p hp j) h ≠ 0) :
    ∃ k : O, h = p ^ j * k ∧ 6 ∣ j ∧ ¬ p ∣ k := by
  have hp0 := supported_element_ne_zero p hp
  let := finiteEisensteinQuotientOfNonzero (pow_ne_zero j hp0)
  let : Fintype (Residue (p ^ j)) := Fintype.ofFinite _
  let := finiteEisensteinQuotientOfNonzero (mul_ne_zero (pow_ne_zero j hp0) (pow_ne_zero d hp0))
  let : Fintype (Residue (p ^ j * p ^ d)) := Fintype.ofFinite _
  have hdiv : p ^ j ∣ h := by
    by_contra hn
    exact hne (fullModulusCorrelation_eq_zero_of_common_not_dvd _ _ (p ^ j) h
      (supportedModulusCharacter _ _) (supportedModulusCharacter _ _)
      (dvd_mul_right _ _) dvd_rfl hn)
  obtain ⟨k, rfl⟩ := hdiv
  refine ⟨k, rfl, ?_, ?_⟩
  · by_contra hj6
    exact hne (unequal_prime_power_zero_of_not_six p hp hg hchar hj hd hj6 k)
  · intro hk
    exact hne (unequal_prime_power_zero_of_nonunit p hp hg hj hd k hk)

end Eisenstein

end CenteredMomentUnequal

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentLocal
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentUnequal

section Domain
variable {A : Type*} [CommRing A] [IsDomain A]

omit [IsDomain A] in
theorem scaledResidue_one (q : A) (x : Residue q) :
    scaledResidue q 1 q (mul_one q).symm x = x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [scaledResidue_mk, one_mul]

theorem fullCorrelation_equal_divided (q k : A) (hq : q ≠ 0)
    [Fintype (Residue q)] (χ : MulChar (Residue q) ℂ) :
    fullModulusCorrelation q q χ χ (q * k) =
      fullCorrelation (fun x : Residue q => x) (fun y : Residue q => y) χ χ
        (Ideal.Quotient.mk _ k) := by
  have hs (x y : Residue q) :
      scaledResidue q q (q * q) rfl x - scaledResidue q q (q * q) (mul_comm _ _) y =
        Ideal.Quotient.mk _ (q * k) ↔ x - y = Ideal.Quotient.mk _ k := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [scaledResidue_congruence, ← map_sub, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    rw [show q * x - q * y - q * k = q * (x - y - k) by ring]
    exact mul_dvd_mul_iff_left hq
  unfold fullModulusCorrelation fullCorrelation
  simp_rw [hs]

end Domain

open Eisenstein  CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentSupportedCorrelation CenteredMomentCanonical CompletedGauss
open CenteredMomentFourier

local notation "O" => Eisenstein.O

theorem powerReduction_multiplicity (p : O) (_hp : p ≠ 0) {i : ℕ} (hi : 1 ≤ i)
    [Fintype (Residue p)] [Fintype (Residue (p ^ i))] :
    reductionMultiplicity (frequencyReduction p (p ^ i) (dvd_pow_self p (by omega))) =
      Ideal.absNorm (Ideal.span {p}) ^ (i - 1) := by
  have hcard (a : O) [Fintype (Residue a)] :
      Fintype.card (Residue a) = Ideal.absNorm (Ideal.span {a}) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  apply reductionMultiplicity_eq_pow _ (Ideal.Quotient.factor_surjective _) (c := i)
  · rw [← hcard p]
    exact Fintype.card_pos
  · exact hi
  · rw [hcard, ← Ideal.span_singleton_pow, map_pow]
  · exact hcard p

theorem equal_prime_power_formula (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    {i : ℕ} (hi : 1 ≤ i) (k : O) :
    actualCorrelation (p ^ i) (p ^ i) (supported_power p hp i) (supported_power p hp i)
      (p ^ i * k) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (i - 1) *
        (if p ∣ k then (Ideal.absNorm (Ideal.span {p}) : ℂ) - 1
         else if 6 ∣ i then (Ideal.absNorm (Ideal.span {p}) : ℂ) - 2 else -1) := by
  have hp0 := supported_element_ne_zero p hp
  let := finiteEisensteinQuotientOfNonzero hp0
  let : Fintype (Residue p) := Fintype.ofFinite _
  let := finiteEisensteinQuotientOfNonzero (pow_ne_zero i hp0)
  let : Fintype (Residue (p ^ i)) := Fintype.ofFinite _
  let : Field (Residue p) := Ideal.Quotient.field (Ideal.span {p})
  let π := frequencyReduction p (p ^ i) (dvd_pow_self p (by omega))
  let χ := complexSexticChar (Ideal.span {p}) hg ^ i
  have hπ : Function.Surjective π := Ideal.Quotient.factor_surjective _
  have hχ (x : Residue (p ^ i)) :
      supportedModulusCharacter (p ^ i) (supported_power p hp i) x = χ (π x) := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact supported_power_character_mk p hp hg hi x
  have hred := fullCorrelation_reduction_unit_right π hπ
    (1 : (Residue (p ^ i))ˣ) 1 (Ideal.Quotient.mk _ k) χ χ
  simp only [Units.val_one, map_one, one_mul] at hred
  have hpow : χ = 1 ↔ 6 ∣ i := by
    dsimp only [χ]
    rw [← orderOf_dvd_iff_pow_eq_one, complexSexticChar_order_six (Ideal.span {p}) hg hchar]
  have hk : Ideal.Quotient.mk (Ideal.span {p}) k = 0 ↔ p ∣ k := by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have hcard : Fintype.card (Residue p) = Ideal.absNorm (Ideal.span {p}) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  change fullModulusCorrelation _ _ _ _ _ = _
  rw [fullCorrelation_equal_divided _ _ (pow_ne_zero i hp0)]
  have hχfun : (supportedModulusCharacter (p ^ i) (supported_power p hp i) :
      Residue (p ^ i) → ℂ) = (fun x => χ (π x)) := funext hχ
  rw [hχfun, hred]
  have he : fullCorrelation (fun x : Residue p => x) (fun x => x) χ χ
      (π (Ideal.Quotient.mk _ k)) = localCorrelation χ 1 1 (Ideal.Quotient.mk _ k) := by
    simp only [localCorrelation, one_mul, π, frequencyReduction_mk]
  rw [he]
  rw [localCorrelation_units χ one_ne_zero one_ne_zero, div_self one_ne_zero, map_one, one_mul,
    hcard]
  simp only [hk, hpow]
  have hm : (reductionMultiplicity π : ℂ) = (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (i - 1) := by
    rw [powerReduction_multiplicity p hp0 hi, Nat.cast_pow]
  rw [hm]

theorem equal_prime_power_unit_norm (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    {i : ℕ} (hi : 1 ≤ i) (hi6 : ¬ 6 ∣ i) (k : O) (hk : ¬ p ∣ k) :
    ‖actualCorrelation (p ^ i) (p ^ i) (supported_power p hp i) (supported_power p hp i)
      (p ^ i * k)‖ = (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (i - 1) := by
  rw [equal_prime_power_formula p hp hg hchar hi k, if_neg hk, if_neg hi6]
  simp

theorem equal_prime_power_norm_le (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    {i : ℕ} (hi : 1 ≤ i) (k : O) :
    ‖actualCorrelation (p ^ i) (p ^ i) (supported_power p hp i) (supported_power p hp i)
      (p ^ i * k)‖ ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ i := by
  have hp0 := supported_element_ne_zero p hp
  let := finiteEisensteinQuotientOfNonzero hp0
  let : Fintype (Residue p) := Fintype.ofFinite _
  have hcard : Fintype.card (Residue p) = Ideal.absNorm (Ideal.span {p}) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hN : (2 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast (show 2 ≤ Ideal.absNorm (Ideal.span {p}) from by
      rw [← hcard]
      exact Fintype.one_lt_card)
  have hsub (a : ℝ) (ha : 0 ≤ a) (haN : a ≤ Ideal.absNorm (Ideal.span {p})) :
      ‖(Ideal.absNorm (Ideal.span {p}) : ℂ) - (a : ℂ)‖ ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
    have he : (Ideal.absNorm (Ideal.span {p}) : ℂ) - (a : ℂ) =
        ((Ideal.absNorm (Ideal.span {p}) : ℝ) - a : ℝ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr haN)]
    linarith
  rw [equal_prime_power_formula p hp hg hchar hi k, norm_mul, norm_pow]
  have hnorm : ‖(Ideal.absNorm (Ideal.span {p}) : ℂ)‖ = (Ideal.absNorm (Ideal.span {p}) : ℝ) := by simp
  rw [hnorm]
  have hb : ‖(if p ∣ k then (Ideal.absNorm (Ideal.span {p}) : ℂ) - 1
      else if 6 ∣ i then (Ideal.absNorm (Ideal.span {p}) : ℂ) - 2 else -1)‖ ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
    split_ifs
    · simpa using hsub 1 (by norm_num) (by linarith)
    · simpa using hsub 2 (by norm_num) hN
    · simpa using (show (1 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}) by linarith)
  calc
    _ ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (i - 1) * Ideal.absNorm (Ideal.span {p}) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [← pow_succ, Nat.sub_add_cancel hi]

end CenteredMomentLocal

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentHeterogeneousCRT
open CenteredMomentCorrelation

theorem fullCorrelation_heterogeneous_pi {ι : Type*} [Fintype ι]
    {X Y R : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    [∀ i, CommRing (R i)]
    (left : ∀ i, X i → R i) (right : ∀ i, Y i → R i)
    (f : ∀ i, X i → ℂ) (g : ∀ i, Y i → ℂ) (k : ∀ i, R i) :
    fullCorrelation (fun (x : ∀ i, X i) i => left i (x i)) (fun (y : ∀ i, Y i) i => right i (y i))
        (fun x => ∏ i, f i (x i)) (fun y => ∏ i, g i (y i)) k =
      ∏ i, fullCorrelation (left i) (right i) (f i) (g i) (k i) := by
  have hterm (x : ∀ i, X i) (y : ∀ i, Y i) :
      (if (fun i => left i (x i)) - (fun i => right i (y i)) = k
       then (∏ i, f i (x i)) * star (∏ i, g i (y i)) else 0) =
      ∏ i, if left i (x i) - right i (y i) = k i then f i (x i) * star (g i (y i)) else 0 := by
    by_cases h : ∀ i, left i (x i) - right i (y i) = k i
    · have he : (fun i => left i (x i)) - (fun i => right i (y i)) = k := funext h
      simp only [he, ite_true, h, star_prod, Finset.prod_mul_distrib]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      have he : (fun i => left i (x i)) - (fun i => right i (y i)) ≠ k :=
        fun h => hi (congrFun h i)
      rw [if_neg he]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [hi, ite_false]
  simp only [fullCorrelation]
  simp_rw [hterm]
  calc
    _ = ∑ x : ∀ i, X i, ∏ i, ∑ y : Y i,
        if left i (x i) - right i y = k i then f i (x i) * star (g i y) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Fintype.prod_sum (fun i (y : Y i) =>
        if left i (x i) - right i y = k i then f i (x i) * star (g i y) else (0 : ℂ))).symm
    _ = _ := (Fintype.prod_sum (fun i (x : X i) => ∑ y : Y i,
      if left i x - right i y = k i then f i x * star (g i y) else (0 : ℂ))).symm

theorem fullCorrelation_three_equiv {ι X Y R : Type*} [Fintype ι]
    [Fintype X] [Fintype Y] [CommRing R]
    {Xi Yi Ri : ι → Type*} [∀ i, Fintype (Xi i)] [∀ i, Fintype (Yi i)]
    [∀ i, CommRing (Ri i)]
    (eX : X ≃ ∀ i, Xi i) (eY : Y ≃ ∀ i, Yi i) (eR : R ≃+* ∀ i, Ri i)
    (left : X → R) (right : Y → R)
    (li : ∀ i, Xi i → Ri i) (ri : ∀ i, Yi i → Ri i)
    (hl : ∀ x i, eR (left x) i = li i (eX x i))
    (hr : ∀ y i, eR (right y) i = ri i (eY y i))
    (f : ∀ i, Xi i → ℂ) (g : ∀ i, Yi i → ℂ) (k : R) :
    fullCorrelation left right (fun x => ∏ i, f i (eX x i))
      (fun y => ∏ i, g i (eY y i)) k =
      ∏ i, fullCorrelation (li i) (ri i) (f i) (g i) (eR k i) := by
  rw [← fullCorrelation_heterogeneous_pi li ri f g (eR k)]
  unfold fullCorrelation
  apply Fintype.sum_equiv eX
  intro x
  apply Fintype.sum_equiv eY
  intro y
  have he : left x - right y = k ↔
      (fun i => li i (eX x i)) - (fun i => ri i (eY y i)) = eR k := by
    rw [← eR.injective.eq_iff, map_sub]
    have hleft : eR (left x) = fun i => li i (eX x i) := funext (hl x)
    have hright : eR (right y) = fun i => ri i (eY y i) := funext (hr y)
    rw [hleft, hright]
  simp only [he]

end CenteredMomentHeterogeneousCRT

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentProductCRT
open CenteredMomentCorrelation CenteredMomentCommonSupport
open CenteredMomentHeterogeneousCRT
variable {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]

def productCRT (a : ι → A)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i}))) :
    Residue (∏ i, a i) ≃+* ∀ i, Residue (a i) :=
  (Ideal.quotEquivOfEq (Ideal.prod_span_singleton Finset.univ a).symm).trans
    (IdealGaussCRT.quotientProdEquivPi (fun i => Ideal.span {a i}) hcop)

omit [DecidableEq ι] in
@[simp] theorem productCRT_mk (a : ι → A)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i})))
    (x : A) (i : ι) :
    productCRT a hcop (Ideal.Quotient.mk _ x) i = Ideal.Quotient.mk _ x := by
  simp only [productCRT, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    IdealGaussCRT.quotientProdEquivPi_mk]

def jointCRT (a b : ι → A)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i}))) :
    Residue ((∏ i, a i) * ∏ i, b i) ≃+* ∀ i, Residue (a i * b i) :=
  (Ideal.quotEquivOfEq (congrArg (fun x : A => Ideal.span {x})
    (Finset.prod_mul_distrib (s := Finset.univ) (f := a) (g := b)).symm)).trans
      (productCRT (fun i => a i * b i) hcop)

omit [DecidableEq ι] in
@[simp] theorem jointCRT_mk (a b : ι → A)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    (x : A) (i : ι) :
    jointCRT a b hcop (Ideal.Quotient.mk _ x) i = Ideal.Quotient.mk _ x := by
  simp only [jointCRT, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, productCRT_mk]

def cuspPrimeCofactor (a : ι → A) (i : ι) : A := ∏ j ∈ Finset.univ.erase i, a j

theorem factor_mul_cuspPrimeCofactor (a : ι → A) (i : ι) : a i * cuspPrimeCofactor a i = ∏ j, a j :=
  Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)

theorem left_crt_component (a b : ι → A)
    (ha : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i})))
    (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    (x : Residue (∏ i, a i)) (i : ι) :
    jointCRT a b hab
      (scaledResidue (∏ i, a i) (∏ i, b i) ((∏ i, a i) * ∏ i, b i) rfl x) i =
      scaledResidue (a i) (b i) (a i * b i) rfl
        (Ideal.Quotient.mk _ (cuspPrimeCofactor b i) * productCRT a ha x i) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [scaledResidue_mk, jointCRT_mk, productCRT_mk, ← map_mul, scaledResidue_mk]
  congr 1
  rw [← factor_mul_cuspPrimeCofactor b i]
  ring

theorem right_crt_component (a b : ι → A)
    (hb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {b i})))
    (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    (y : Residue (∏ i, b i)) (i : ι) :
    jointCRT a b hab
      (scaledResidue (∏ i, b i) (∏ i, a i) ((∏ i, a i) * ∏ i, b i) (mul_comm _ _) y) i =
      scaledResidue (b i) (a i) (a i * b i) (mul_comm _ _)
        (Ideal.Quotient.mk _ (cuspPrimeCofactor a i) * productCRT b hb y i) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_mk, jointCRT_mk, productCRT_mk, ← map_mul, scaledResidue_mk]
  congr 1
  rw [← factor_mul_cuspPrimeCofactor a i]
  ring

theorem fullModulusCorrelation_product (a b : ι → A)
    (ha : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i})))
    (hb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {b i})))
    (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    [Fintype (Residue (∏ i, a i))] [Fintype (Residue (∏ i, b i))]
    [∀ i, Fintype (Residue (a i))] [∀ i, Fintype (Residue (b i))]
    (χ : ∀ i, MulChar (Residue (a i)) ℂ) (ψ : ∀ i, MulChar (Residue (b i)) ℂ) (h : A) :
    fullModulusCorrelation (∏ i, a i) (∏ i, b i)
      (crtCharacter (productCRT a ha) χ) (crtCharacter (productCRT b hb) ψ) h =
      ∏ i, fullCorrelation
        (fun x => scaledResidue (a i) (b i) (a i * b i) rfl
          (Ideal.Quotient.mk _ (cuspPrimeCofactor b i) * x))
        (fun y => scaledResidue (b i) (a i) (a i * b i) (mul_comm _ _)
          (Ideal.Quotient.mk _ (cuspPrimeCofactor a i) * y))
        (χ i) (ψ i) (Ideal.Quotient.mk _ h) := by
  have hcrt := fullCorrelation_three_equiv (productCRT a ha).toEquiv (productCRT b hb).toEquiv
    (jointCRT a b hab)
    (scaledResidue (∏ i, a i) (∏ i, b i) ((∏ i, a i) * ∏ i, b i) rfl)
    (scaledResidue (∏ i, b i) (∏ i, a i) ((∏ i, a i) * ∏ i, b i) (mul_comm _ _))
    (fun i x => scaledResidue (a i) (b i) (a i * b i) rfl
      (Ideal.Quotient.mk _ (cuspPrimeCofactor b i) * x))
    (fun i y => scaledResidue (b i) (a i) (a i * b i) (mul_comm _ _)
      (Ideal.Quotient.mk _ (cuspPrimeCofactor a i) * y))
    (left_crt_component a b ha hab) (right_crt_component a b hb hab)
    (fun i => χ i) (fun i => ψ i) (Ideal.Quotient.mk _ h)
  simpa only [fullModulusCorrelation, fullCorrelation, crtCharacter_apply, jointCRT_mk,
    RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe] using hcrt

theorem cross_cuspPrimeCofactor_coprime (a b : ι → A)
    (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    (i : ι) : IsCoprime (a i) (cuspPrimeCofactor b i) := by
  unfold cuspPrimeCofactor
  apply IsCoprime.prod_right
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hij := (Ideal.isCoprime_span_singleton_iff _ _).mp (hab hji.symm)
  exact (IsCoprime.mul_right_iff.mp (IsCoprime.mul_left_iff.mp hij).1).2

theorem local_cuspPrimeCofactor_norm (a b : ι → A)
    (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    [∀ i, Fintype (Residue (a i))] [∀ i, Fintype (Residue (b i))]
    (χ : ∀ i, MulChar (Residue (a i)) ℂ) (ψ : ∀ i, MulChar (Residue (b i)) ℂ)
    (h : A) (i : ι) :
    ‖fullCorrelation
        (fun x => scaledResidue (a i) (b i) (a i * b i) rfl
          (Ideal.Quotient.mk _ (cuspPrimeCofactor b i) * x))
        (fun y => scaledResidue (b i) (a i) (a i * b i) (mul_comm _ _)
          (Ideal.Quotient.mk _ (cuspPrimeCofactor a i) * y))
        (χ i) (ψ i) (Ideal.Quotient.mk _ h)‖ =
      ‖fullModulusCorrelation (a i) (b i) (χ i) (ψ i) h‖ := by
  obtain ⟨u, hu⟩ := isUnit_residue_of_coprime (a i) (cuspPrimeCofactor b i)
    (cross_cuspPrimeCofactor_coprime a b hab i)
  have hba : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {b i * a i})) := by
    simpa only [mul_comm] using hab
  obtain ⟨v, hv⟩ := isUnit_residue_of_coprime (b i) (cuspPrimeCofactor a i)
    (cross_cuspPrimeCofactor_coprime b a hba i)
  rw [← hu, ← hv, fullCorrelation_unit_change, norm_mul, norm_mul, norm_star,
    FiniteRayExpansion.norm_char_unit, FiniteRayExpansion.norm_char_unit, one_mul, one_mul]
  rfl

theorem fullModulusCorrelation_product_norm (a b : ι → A)
    (ha : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i})))
    (hb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {b i})))
    (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    [Fintype (Residue (∏ i, a i))] [Fintype (Residue (∏ i, b i))]
    [∀ i, Fintype (Residue (a i))] [∀ i, Fintype (Residue (b i))]
    (χ : ∀ i, MulChar (Residue (a i)) ℂ) (ψ : ∀ i, MulChar (Residue (b i)) ℂ) (h : A) :
    ‖fullModulusCorrelation (∏ i, a i) (∏ i, b i)
      (crtCharacter (productCRT a ha) χ) (crtCharacter (productCRT b hb) ψ) h‖ =
      ∏ i, ‖fullModulusCorrelation (a i) (b i) (χ i) (ψ i) h‖ := by
  rw [fullModulusCorrelation_product a b ha hb hab χ ψ h, norm_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact local_cuspPrimeCofactor_norm a b hab χ ψ h i

section Eisenstein
open Eisenstein  CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentSupportedCorrelation
local notation "O" => Eisenstein.O

omit [DecidableEq ι] in
theorem supported_character_product (a : ι → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hprod : Supported (Ideal.span {∏ i, a i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i}))) :
    supportedModulusCharacter (∏ i, a i) hprod =
      crtCharacter (productCRT a hcop) (fun i => supportedModulusCharacter (a i) (ha i)) := by
  apply DFunLike.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [crtCharacter_apply, productCRT_mk, supportedModulusCharacter_mk]
  rw [← Ideal.prod_span_singleton Finset.univ a, map_prod]

theorem actualCorrelation_product_norm (a b : ι → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hb : ∀ i, Supported (Ideal.span {b i}))
    (hA : Supported (Ideal.span {∏ i, a i}))
    (hB : Supported (Ideal.span {∏ i, b i}))
    (hca : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i})))
    (hcb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {b i})))
    (hcab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i}))) (h : O) :
    ‖actualCorrelation (∏ i, a i) (∏ i, b i) hA hB h‖ =
      ∏ i, ‖actualCorrelation (a i) (b i) (ha i) (hb i) h‖ := by
  let : ∀ i, Finite (Residue (a i)) := fun i => finiteEisensteinQuotientOfNonzero (supported_element_ne_zero (a i) (ha i))
  let : ∀ i, Finite (Residue (b i)) := fun i => finiteEisensteinQuotientOfNonzero (supported_element_ne_zero (b i) (hb i))
  let : ∀ i, Fintype (Residue (a i)) := fun i => Fintype.ofFinite _
  let : ∀ i, Fintype (Residue (b i)) := fun i => Fintype.ofFinite _
  let := finiteEisensteinQuotientOfNonzero (supported_element_ne_zero _ hA)
  let := finiteEisensteinQuotientOfNonzero (supported_element_ne_zero _ hB)
  let : Fintype (Residue (∏ i, a i)) := Fintype.ofFinite _
  let : Fintype (Residue (∏ i, b i)) := Fintype.ofFinite _
  change ‖fullModulusCorrelation _ _ (supportedModulusCharacter _ hA)
    (supportedModulusCharacter _ hB) h‖ =
    ∏ i, ‖fullModulusCorrelation _ _ (supportedModulusCharacter _ (ha i))
      (supportedModulusCharacter _ (hb i)) h‖
  rw [supported_character_product a ha hA hca, supported_character_product b hb hB hcb]
  exact fullModulusCorrelation_product_norm a b hca hcb hcab _ _ h

end Eisenstein

end CenteredMomentProductCRT

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentPartition
open CenteredMomentCorrelation CenteredMomentCommonSupport

section Domain
variable {A : Type*} [CommRing A]
theorem fullModulusCorrelation_swap (u v h : A)
    [Fintype (Residue u)] [Fintype (Residue v)]
    (χ : MulChar (Residue u) ℂ) (ψ : MulChar (Residue v) ℂ) :
    fullModulusCorrelation u v χ ψ h = star (fullModulusCorrelation v u ψ χ (-h)) := by
  simp only [fullModulusCorrelation, fullCorrelation, star_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have he : u * v ∣ v * x - u * y - h ↔ v * u ∣ u * y - v * x - (-h) := by
    rw [mul_comm v u, show u * y - v * x - (-h) = -(v * x - u * y - h) by ring,
      dvd_neg]
  simp only [scaledResidue_congruence]
  by_cases hc : u * v ∣ v * x - u * y - h
  · simp only [hc, he.mp hc, ite_true, star_mul, star_star]
  · simp only [hc, (not_congr he).mp hc, ite_false, star_zero]
end Domain

open Eisenstein  CanonicalQuadraticSieve
open CenteredMomentSupportedCorrelation CenteredMomentUnequal CenteredMomentLocal
open CenteredMomentProductCRT

local notation "O" => Eisenstein.O

theorem actualCorrelation_norm_swap (u v : O)
    (hu : Supported (Ideal.span {u})) (hv : Supported (Ideal.span {v})) (h : O) :
    ‖actualCorrelation u v hu hv h‖ = ‖actualCorrelation v u hv hu (-h)‖ := by
  let := finiteEisensteinQuotientOfNonzero (supported_element_ne_zero u hu)
  let := finiteEisensteinQuotientOfNonzero (supported_element_ne_zero v hv)
  let : Fintype (Residue u) := Fintype.ofFinite _
  let : Fintype (Residue v) := Fintype.ofFinite _
  change ‖fullModulusCorrelation u v _ _ h‖ = ‖fullModulusCorrelation v u _ _ (-h)‖
  rw [fullModulusCorrelation_swap, norm_star]

theorem prime_power_norm_le_min (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d) (k : O) :
    ‖actualCorrelation (p ^ c) (p ^ d) (supported_power p hp c) (supported_power p hp d)
      (p ^ min c d * k)‖ ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ min c d := by
  rcases lt_trichotomy c d with hcd | heq | hdc
  · have he : c + (d - c) = d := Nat.add_sub_of_le hcd.le
    have h := unequal_prime_power_norm_le p hp hg hc (show 1 ≤ d - c by omega) (-k)
    rw [actualCorrelation_norm_swap]
    simpa only [← pow_add, he, min_eq_left hcd.le, mul_neg] using h
  · subst d
    simpa only [min_self] using equal_prime_power_norm_le p hp hg hchar hc k
  · have he : d + (c - d) = c := Nat.add_sub_of_le hdc.le
    have h := unequal_prime_power_norm_le p hp hg hd (show 1 ≤ c - d by omega) k
    simpa only [← pow_add, he, min_eq_right hdc.le] using h

theorem prime_power_partition_norm_le (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d) (k : O) (save : Prop) [Decidable save]
    (hsave : save → c = d ∧ ¬ 6 ∣ c ∧ ¬ p ∣ k) :
    ‖actualCorrelation (p ^ c) (p ^ d) (supported_power p hp c) (supported_power p hp d)
      (p ^ min c d * k)‖ ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (min c d - if save then 1 else 0) := by
  by_cases hs : save
  · obtain ⟨rfl, hc6, hk⟩ := hsave hs
    simp only [min_self, if_pos hs]
    exact (equal_prime_power_unit_norm p hp hg hchar hc hc6 k hk).le
  · simpa only [if_neg hs, Nat.sub_zero] using prime_power_norm_le_min p hp hg hchar hc hd k

section Product
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem supported_product (a : ι → O) (ha : ∀ i, Supported (Ideal.span {a i})) :
    Supported (Ideal.span {∏ i, a i}) := by
  have hs (S : Finset ι) : Supported (Ideal.span {∏ i ∈ S, a i}) := by
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Ideal.span_singleton_one]
      rw [← Ideal.one_eq_top]
      change Supported (1 : Ideal O)
      refine ⟨one_ne_zero, ?_⟩
      intro P hP
      simp only [UniqueFactorizationMonoid.normalizedFactors_one,
        Multiset.notMem_zero] at hP
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi]
      exact supported_mul_elements _ _ (ha i) ih
  exact hs Finset.univ

def partitionNormalizer (p : ι → O) (c d : ι → ℕ) (U : Finset ι) : ℝ :=
  ∏ i, (Ideal.absNorm (Ideal.span {p i}) : ℝ) ^ (min (c i) (d i) - if i ∈ U then 1 else 0)

def dividedFrequency (p : ι → O) (c d : ι → ℕ) (w : O) (i : ι) : O :=
  CenteredMomentProductCRT.cuspPrimeCofactor (fun j => p j ^ min (c j) (d j)) i * w

theorem commonFrequency_factor (p : ι → O) (c d : ι → ℕ) (w : O) (i : ι) :
    (∏ j, p j ^ min (c j) (d j)) * w = p i ^ min (c i) (d i) * dividedFrequency p c d w i := by
  rw [dividedFrequency, ← mul_assoc, factor_mul_cuspPrimeCofactor (fun j => p j ^ min (c j) (d j)) i]

theorem actual_partition_norm_le (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, Supported (Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime p))
    (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (U : Finset ι) (w : O)
    (hU : ∀ i ∈ U, c i = d i ∧ ¬ 6 ∣ c i ∧ ¬ p i ∣ dividedFrequency p c d w i) :
    ‖actualCorrelation (∏ i, p i ^ c i) (∏ i, p i ^ d i)
      (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
      (supported_product _ (fun i => supported_power (p i) (hp i) (d i)))
      ((∏ i, p i ^ min (c i) (d i)) * w)‖ ≤ partitionNormalizer p c d U := by
  have hca : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i ^ c i})) := by
    intro i j hij
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    exact (hcop hij).pow
  have hcb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i ^ d i})) := by
    intro i j hij
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    exact (hcop hij).pow
  have hcab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i ^ c i * p i ^ d i})) := by
    intro i j hij
    dsimp only [Function.onFun]
    rw [← pow_add, ← pow_add]
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    exact (hcop hij).pow
  rw [actualCorrelation_product_norm (fun i => p i ^ c i) (fun i => p i ^ d i)
    (fun i => supported_power (p i) (hp i) (c i))
    (fun i => supported_power (p i) (hp i) (d i))
    (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
    (supported_product _ (fun i => supported_power (p i) (hp i) (d i))) hca hcb hcab]
  unfold partitionNormalizer
  apply Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => ?_)
  rw [commonFrequency_factor p c d w i]
  exact prime_power_partition_norm_le (p i) (hp i) (hg i) (hchar i) (hc i) (hd i)
    (dividedFrequency p c d w i) (i ∈ U) (hU i)

theorem normalized_partition_norm_le_one (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, Supported (Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime p))
    (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (U : Finset ι) (part : O → Prop) (w : O)
    (hpart : part w → ∀ i ∈ U, c i = d i ∧ ¬ 6 ∣ c i ∧ ¬ p i ∣ dividedFrequency p c d w i) :
    ‖if part w then
      actualCorrelation (∏ i, p i ^ c i) (∏ i, p i ^ d i)
        (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
        (supported_product _ (fun i => supported_power (p i) (hp i) (d i)))
        ((∏ i, p i ^ min (c i) (d i)) * w) / (partitionNormalizer p c d U : ℂ)
      else 0‖ ≤ 1 := by
  by_cases hw : part w
  · rw [if_pos hw, norm_div, Complex.norm_real]
    have hN : 0 < partitionNormalizer p c d U := by
      unfold partitionNormalizer
      apply Finset.prod_pos
      intro i hi
      apply pow_pos
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)
    rw [Real.norm_of_nonneg hN.le]
    exact (div_le_one hN).mpr (actual_partition_norm_le p hp hg hchar hcop c d hc hd U w (hpart hw))
  · simp only [if_neg hw, norm_zero, zero_le_one]

end Product

end CenteredMomentPartition

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentPartitionNorm
open CenteredMomentPartition CanonicalQuadraticSieve
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def commonIdeal (p : ι → O) (c d : ι → ℕ) : Ideal O :=
  ∏ i, Ideal.span {p i} ^ min (c i) (d i)

def unitIdeal (p : ι → O) (U : Finset ι) : Ideal O := ∏ i ∈ U, Ideal.span {p i}

omit [DecidableEq ι] in
theorem commonIdeal_norm_pos (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (c d : ι → ℕ) : 0 < (Ideal.absNorm (commonIdeal p c d) : ℝ) := by
  simp only [commonIdeal, map_prod, map_pow, Nat.cast_prod, Nat.cast_pow]
  apply Finset.prod_pos
  intro i hi
  apply pow_pos
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)

omit [Fintype ι] [DecidableEq ι] in
theorem unitIdeal_norm_pos (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (U : Finset ι) : 0 < (Ideal.absNorm (unitIdeal p U) : ℝ) := by
  simp only [unitIdeal, map_prod, Nat.cast_prod]
  apply Finset.prod_pos
  intro i hi
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)

theorem partitionNormalizer_mul_unit_norm (p : ι → O) (c d : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i) (U : Finset ι) :
    partitionNormalizer p c d U * (Ideal.absNorm (unitIdeal p U) : ℝ) =
      (Ideal.absNorm (commonIdeal p c d) : ℝ) := by
  simp only [unitIdeal, commonIdeal, map_prod, map_pow, Nat.cast_prod, Nat.cast_pow]
  have hU : (∏ i ∈ U, (Ideal.absNorm (Ideal.span {p i}) : ℝ)) =
      ∏ i, if i ∈ U then (Ideal.absNorm (Ideal.span {p i}) : ℝ) else 1 := by simp
  rw [hU, partitionNormalizer, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hmem : i ∈ U
  · simp only [if_pos hmem]
    rw [← pow_succ, Nat.sub_add_cancel (le_min (hc i) (hd i))]
  · simp only [if_neg hmem, Nat.sub_zero, mul_one]

theorem partitionNormalizer_eq_norm_ratio (p : ι → O)
    (hp : ∀ i, Supported (Ideal.span {p i})) (c d : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i) (U : Finset ι) :
    partitionNormalizer p c d U =
      (Ideal.absNorm (commonIdeal p c d) : ℝ) / Ideal.absNorm (unitIdeal p U) := by
  apply (eq_div_iff (unitIdeal_norm_pos p hp U).ne').mpr
  exact partitionNormalizer_mul_unit_norm p c d hc hd U

theorem partitionNormalizer_eq_log_scale (p : ι → O)
    (hp : ∀ i, Supported (Ideal.span {p i})) (c d : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i) (U : Finset ι)
    (Z : ℝ) (hZ : 1 < Z) :
    partitionNormalizer p c d U =
      Z ^ (Real.logb Z (Ideal.absNorm (commonIdeal p c d)) -
        Real.logb Z (Ideal.absNorm (unitIdeal p U))) := by
  rw [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (commonIdeal_norm_pos p hp c d),
    Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (unitIdeal_norm_pos p hp U)]
  exact partitionNormalizer_eq_norm_ratio p hp c d hc hd U

end CenteredMomentPartitionNorm

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentForcing
open UniqueFactorizationMonoid CenteredExceptionalCount CanonicalQuadraticSieve
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def movingIdeal (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) : Ideal O :=
  (∏ i, P i ^ min (c i) (d i)) * ∏ i ∈ V, P i

def forcingSet (c d : ι → ℕ) (V : Finset ι) : Finset ι :=
  V.filter (fun i => c i = 1 ∧ d i = 1)

def forcingIdeal (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) : Ideal O :=
  ∏ i ∈ forcingSet c d V, P i

omit [Fintype ι] in
theorem valuation_product (S : Finset ι) (I : ι → Ideal O)
    (hI : ∀ i ∈ S, I i ≠ 0) (Q : Ideal O) :
    valuation (∏ i ∈ S, I i) Q = ∑ i ∈ S, valuation (I i) Q := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,Finset.sum_empty,valuation,normalizedFactors_one,Multiset.count_zero]
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      valuation_mul _ _ _ (hI i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hI j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hI j (Finset.mem_insert_of_mem hj))]

theorem valuation_prime (P Q : Ideal O) (hP : Prime P) :
    valuation P Q = if P = Q then 1 else 0 := by
  have hf : normalizedFactors P = {P} := by
    simpa using (normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal O)))
      (by intro R hR; simpa only [Multiset.mem_singleton.mp hR] using hP))
  simp only [valuation,hf,Multiset.count_singleton]
  simp only [eq_comm]

omit [Fintype ι] in
theorem valuation_prime_product (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (S : Finset ι) (i : ι) :
    valuation (∏ j ∈ S, P j) (P i) = if i ∈ S then 1 else 0 := by
  rw [valuation_product S P (fun j _ => (hp j).ne_zero)]
  simp only [valuation_prime _ _ (hp _), hinj.eq_iff]
  simp

theorem valuation_prime_power_product (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (n : ι → ℕ) (i : ι) :
    valuation (∏ j, P j ^ n j) (P i) = n i := by
  rw [valuation_product Finset.univ _ (fun j _ => pow_ne_zero _ (hp j).ne_zero)]
  simp only [valuation_pow,valuation_prime _ _ (hp _),hinj.eq_iff,mul_ite,mul_one,mul_zero]
  simp

omit [DecidableEq ι] in
theorem movingIdeal_ne_zero (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (c d : ι → ℕ) (V : Finset ι) : movingIdeal P c d V ≠ 0 := by
  unfold movingIdeal
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hp i).ne_zero))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero))

theorem movingIdeal_valuation (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (c d : ι → ℕ) (V : Finset ι) (i : ι) :
    valuation (movingIdeal P c d V) (P i) = min (c i) (d i) + if i ∈ V then 1 else 0 := by
  rw [movingIdeal,valuation_mul _ _ _
    (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hp i).ne_zero))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)),
    valuation_prime_power_product P hp hinj, valuation_prime_product P hp hinj]

theorem forcing_valuation_two (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (c d : ι → ℕ) (V : Finset ι)
    (i : ι) (hi : i ∈ forcingSet c d V) : valuation (movingIdeal P c d V) (P i) = 2 := by
  obtain ⟨hiV,hc,hd⟩ := Finset.mem_filter.mp hi
  rw [movingIdeal_valuation P hp hinj c d V i,hc,hd,if_pos hiV]
  norm_num

omit [Fintype ι] [DecidableEq ι] in
theorem forcingIdeal_squarefree (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (c d : ι → ℕ) (V : Finset ι) :
    Squarefree (forcingIdeal P c d V) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    let : (P i).IsMaximal := (Ideal.isPrime_of_prime (hp i)).isMaximal (hp i).ne_zero
    let : (P j).IsMaximal := (Ideal.isPrime_of_prime (hp j)).isMaximal (hp j).ne_zero
    exact (Ideal.isCoprime_of_isMaximal (hinj.ne hij)).isRelPrime
  · intro i hi
    exact (hp i).squarefree

omit [Fintype ι] [DecidableEq ι] in
theorem forcing_prime_mem (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (c d : ι → ℕ) (V : Finset ι) (Q : Ideal O)
    (hQ : Q ∈ normalizedFactors (forcingIdeal P c d V)) :
    ∃ i ∈ forcingSet c d V, Q = P i := by
  have hf : normalizedFactors (forcingIdeal P c d V) =
      (forcingSet c d V).val.map P := by
    apply normalizedFactors_prod_of_prime
    intro R hR
    obtain ⟨i,hi,rfl⟩ := Multiset.mem_map.mp hR
    exact hp i
  rw [hf] at hQ
  obtain ⟨i,hi,hPi⟩ := Multiset.mem_map.mp hQ
  exact ⟨i,hi,hPi.symm⟩

omit [Fintype ι] [DecidableEq ι] in
theorem forcing_norm_scale (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (c d : ι → ℕ) (V : Finset ι) (Z : ℝ) (hZ : 1 < Z) :
    Z ^ ((2 * Real.logb Z (Ideal.absNorm (forcingIdeal P c d V))) / 2) =
      (Ideal.absNorm (forcingIdeal P c d V) : ℝ) := by
  rw [show (2 * Real.logb Z (Ideal.absNorm (forcingIdeal P c d V))) / 2 =
    Real.logb Z (Ideal.absNorm (forcingIdeal P c d V)) by ring]
  exact Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
    (norm_pos (Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)))

def movingElement (p : ι → O) (c d : ι → ℕ) (V : Finset ι) : O :=
  (∏ i, p i ^ min (c i) (d i)) * ∏ i ∈ V, p i

omit [DecidableEq ι] in
theorem movingElement_span (p : ι → O) (c d : ι → ℕ) (V : Finset ι) :
    Ideal.span {movingElement p c d V} = movingIdeal (fun i => Ideal.span {p i}) c d V := by
  simp only [movingElement,movingIdeal,Ideal.span_singleton_pow,
    Ideal.prod_span_singleton,Ideal.span_singleton_mul_span_singleton]

theorem actual_forcing_exceptional_count (p : ι → O)
    (hp : ∀ i, Prime (Ideal.span {p i})) (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (c d : ι → ℕ) (V : Finset ι)
    (η : HeckeFamily.Character) (χ : RayFourExpansion.RayCharacter)
    (Q : Ideal O) (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m e : O) (hm : m ≠ 0) (hmLam : lambda ∣ m) (hm2 : (2 : O) ∣ m)
    (he : HeckeFamily.elementCoeff η e ≠ 0) (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, CenteredExceptionalProfile.FixedInducingRow
      (CenteredMomentChildRows.childCharacter η χ) Q m (movingElement p c d V) z)
    (hgood : ∀ i ∈ forcingSet c d V,
      lambda ∉ Ideal.span {p i} ∧ (2 : O) ∉ Ideal.span {p i} ∧
      IsCoprime Q (Ideal.span {p i}) ∧ Ideal.span {p i} ∣ Ideal.span {e})
    (Z C M : ℝ) (hZ : 1 < Z) (hC : 0 ≤ C)
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ M) :
    (T.card : ℝ) ≤ 768 * (6 : ℝ) ^ (normalizedFactors Q).toFinset.card *
      C ^ (1 / 6 : ℝ) *
        Z ^ ((M - 4 * Real.logb Z (Ideal.absNorm (forcingIdeal (fun i => Ideal.span {p i}) c d V))) / 6) := by
  have hA : movingElement p c d V ≠ 0 := by
    apply Ideal.span_singleton_eq_bot.not.mp
    rw [movingElement_span]
    exact movingIdeal_ne_zero _ hp c d V
  have hb := CenteredMomentChildRows.separated_exceptional_count η χ Q hQ0 hQ hQ72
    m (movingElement p c d V) e hm hA hmLam hm2 he T hT hex
    (forcingIdeal (fun i => Ideal.span {p i}) c d V)
    (forcingIdeal_squarefree _ hp hinj c d V) (by
      intro P hP
      obtain ⟨i,hi,rfl⟩ := forcing_prime_mem _ hp c d V P hP
      obtain ⟨hg,h2,hQP,hPe⟩ := hgood i hi
      refine ⟨hg,h2,hQP,hPe,?_⟩
      rw [movingElement_span,forcing_valuation_two _ hp hinj c d V i hi])
    Z C M (2 * Real.logb Z (Ideal.absNorm (forcingIdeal (fun i => Ideal.span {p i}) c d V)))
    (zero_lt_one.trans hZ) hC (forcing_norm_scale _ hp c d V Z hZ).le hN
  convert hb using 1 ; congr 1 ; ring_nf

end CenteredMomentForcing

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentSecondLedger
open CanonicalQuadraticSieve CenteredMomentSupportedCorrelation CenteredMomentUnequal
open CenteredMomentPartition CenteredMomentProductCRT 
local notation "O" => Eisenstein.O

theorem nonzero_unequal_min_six (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (c d : ℕ) (hc : 1 ≤ c) (hd : 1 ≤ d) (hcd : c ≠ d) (k : O)
    (hne : actualCorrelation (p^c) (p^d) (supported_power p hp c) (supported_power p hp d)
      (p^min c d*k) ≠ 0) : 6 ∣ min c d := by
  by_contra h6
  rcases lt_or_gt_of_ne hcd with hlt | hgt
  · have hz := unequal_prime_power_zero_of_not_six p hp hg hchar hc
      (show 1 ≤ d-c by omega) (by simpa only [min_eq_left hlt.le] using h6) (-k)
    have he : c+(d-c)=d := Nat.add_sub_of_le hlt.le
    have hn := norm_ne_zero_iff.mpr hne
    rw [actualCorrelation_norm_swap] at hn
    have hz' : actualCorrelation (p^d) (p^c) (supported_power p hp d) (supported_power p hp c)
        (-(p^min c d*k)) = 0 := by
      simpa only [← pow_add,he,min_eq_left hlt.le,mul_neg] using hz
    exact hn (by rw [hz',norm_zero])
  · have hz := unequal_prime_power_zero_of_not_six p hp hg hchar hd
      (show 1 ≤ c-d by omega) (by simpa only [min_eq_right hgt.le] using h6) k
    have he : d+(c-d)=c := Nat.add_sub_of_le hgt.le
    exact hne (by simpa only [← pow_add,he,min_eq_right hgt.le] using hz)

def localSaving (c d : ℕ) (nonunit : Prop) : ℝ :=
  (c+d : ℝ) - 5*(min c d : ℝ)/6 - 1 +
    (if c=d ∧ ¬6∣c ∧ ¬nonunit then 1 else 0) +
    (if c=d ∧ ¬6∣c ∧ nonunit then 1/6 else 0) +
    (if c=d ∧ c=1 ∧ nonunit then 1/3 else 0)

theorem localSaving_lower (c d : ℕ) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (huneq : c ≠ d → 6 ∣ min c d) (nonunit : Prop) :
    ((c:ℝ)+d)/3 ≤ localSaving c d nonunit := by
  by_cases hcd : c=d
  · subst d
    by_cases h6 : 6∣c
    · have hc6 : 6 ≤ c := Nat.le_of_dvd (by omega) h6
      have hn1 : c ≠ 1 := by omega
      simp only [localSaving,min_self,h6,not_true_eq_false,false_and,and_false,
        ite_false,hn1,add_zero]
      have hcr : (6:ℝ) ≤ c := by exact_mod_cast hc6
      linarith
    · by_cases hu : nonunit
      · by_cases hc1 : c=1
        · subst c
          norm_num [localSaving,hu]
        · have hc2 : 2 ≤ c := by omega
          simp only [localSaving,min_self,h6,not_false_eq_true,hu,not_true_eq_false,
            and_self,and_false,false_and,ite_false,ite_true,hc1,add_zero]
          have hcr : (2:ℝ) ≤ c := by exact_mod_cast hc2
          linarith
      · simp only [localSaving,min_self,h6,not_false_eq_true,hu,and_false,
          and_true,ite_false,ite_true,add_zero]
        have hcr : (1:ℝ) ≤ c := by exact_mod_cast hc
        linarith
  · have hmin : 6 ≤ min c d := Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one (le_min hc hd)) (huneq hcd)
    have hmr : (6:ℝ) ≤ min c d := by exact_mod_cast hmin
    have hmc : ((min c d : ℕ) : ℝ) ≤ c := by exact_mod_cast min_le_left c d
    have hmd : ((min c d : ℕ) : ℝ) ≤ d := by exact_mod_cast min_le_right c d
    simp only [Nat.cast_min] at hmr hmc hmd
    simp only [localSaving,hcd,false_and,ite_false,add_zero]
    linarith

theorem actual_localSaving_lower (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : lambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (c d : ℕ) (hc : 1 ≤ c) (hd : 1 ≤ d) (k : O)
    (hne : actualCorrelation (p^c) (p^d) (supported_power p hp c) (supported_power p hp d)
      (p^min c d*k) ≠ 0) :
    ((c:ℝ)+d)/3 ≤ localSaving c d (p ∣ k) :=
  localSaving_lower c d hc hd (fun hcd => nonzero_unequal_min_six p hp hg hchar c d hc hd hcd k hne) _

section Global
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem local_nonzero_of_global (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, Supported (Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime p)) (c d : ι → ℕ) (w : O)
    (hne : actualCorrelation (∏ i, p i^c i) (∏ i, p i^d i)
      (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
      (supported_product _ (fun i => supported_power (p i) (hp i) (d i)))
      ((∏ i, p i^min (c i) (d i))*w) ≠ 0) (i : ι) :
    actualCorrelation (p i^c i) (p i^d i) (supported_power (p i) (hp i) (c i))
      (supported_power (p i) (hp i) (d i))
      (p i^min (c i) (d i)*dividedFrequency p c d w i) ≠ 0 := by
  have hca : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i^c i})) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr (hcop hij).pow
  have hcb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i^d i})) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr (hcop hij).pow
  have hcab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i^c i*p i^d i})) := by
    intro i j hij
    dsimp only [Function.onFun]
    rw [← pow_add,← pow_add]
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr (hcop hij).pow
  have hn := norm_ne_zero_iff.mpr hne
  rw [actualCorrelation_product_norm (fun i => p i^c i) (fun i => p i^d i)
    (fun i => supported_power (p i) (hp i) (c i))
    (fun i => supported_power (p i) (hp i) (d i))
    (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
    (supported_product _ (fun i => supported_power (p i) (hp i) (d i))) hca hcb hcab] at hn
  have hi := (Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ i)
  rw [commonFrequency_factor p c d w i] at hi
  exact norm_ne_zero_iff.mp hi

omit [DecidableEq ι] in
theorem log_norm_power_product (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (c : ι → ℕ) (Z : ℝ) :
    Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^c i) : ℝ) =
      ∑ i, (c i : ℝ)*Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) := by
  simp only [map_prod,map_pow,Nat.cast_prod,Nat.cast_pow]
  rw [Real.logb_prod _ _ (fun i _ => pow_ne_zero _ (Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)))]
  simp only [Real.logb_pow]

def secondSaving (p : ι → O) (c d : ι → ℕ) (w : O) (Z : ℝ) : ℝ :=
  ∑ i, Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) *
    localSaving (c i) (d i) (p i ∣ dividedFrequency p c d w i)

def actualUnitSet (p : ι → O) (c d : ι → ℕ) (w : O) : Finset ι :=
  Finset.univ.filter (fun i => c i=d i ∧ ¬6∣c i ∧ ¬p i∣dividedFrequency p c d w i)

def actualNonunitSet (p : ι → O) (c d : ι → ℕ) (w : O) : Finset ι :=
  Finset.univ.filter (fun i => c i=d i ∧ ¬6∣c i ∧ p i∣dividedFrequency p c d w i)

omit [Fintype ι] [DecidableEq ι] in
theorem log_norm_radical (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (S : Finset ι) (Z : ℝ) :
    Real.logb Z (Ideal.absNorm (∏ i ∈ S, Ideal.span {p i}) : ℝ) =
      ∑ i ∈ S, Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) := by
  simp only [map_prod,Nat.cast_prod]
  exact Real.logb_prod _ _ (fun i _ => Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1))

theorem secondSaving_eq_norm_ledger (p : ι → O)
    (hp : ∀ i, Supported (Ideal.span {p i})) (c d : ι → ℕ) (w : O) (Z : ℝ) :
    secondSaving p c d w Z =
      Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^c i) : ℝ) +
      Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^d i) : ℝ) -
      5*Real.logb Z (Ideal.absNorm (CenteredMomentPartitionNorm.commonIdeal p c d) : ℝ)/6 -
      Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}) : ℝ) +
      Real.logb Z (Ideal.absNorm (CenteredMomentPartitionNorm.unitIdeal p (actualUnitSet p c d w)) : ℝ) +
      Real.logb Z (Ideal.absNorm (CenteredMomentPartitionNorm.unitIdeal p (actualNonunitSet p c d w)) : ℝ)/6 +
      Real.logb Z (Ideal.absNorm (CenteredMomentForcing.forcingIdeal
        (fun i => Ideal.span {p i}) c d (actualNonunitSet p c d w)) : ℝ)/3 := by
  rw [log_norm_power_product p hp c,log_norm_power_product p hp d]
  simp only [CenteredMomentPartitionNorm.commonIdeal,CenteredMomentPartitionNorm.unitIdeal,
    CenteredMomentForcing.forcingIdeal]
  rw [log_norm_power_product p hp,log_norm_radical p hp,log_norm_radical p hp,
    log_norm_radical p hp,log_norm_radical p hp]
  simp only [actualUnitSet,actualNonunitSet,CenteredMomentForcing.forcingSet,
    Finset.filter_filter,Finset.sum_filter,]
  unfold secondSaving
  have hf (i : ι) :
      (if (c i=d i ∧ ¬6∣c i ∧ p i∣dividedFrequency p c d w i) ∧ c i=1 ∧ d i=1
       then Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) else 0) =
      (if c i=d i ∧ c i=1 ∧ p i∣dividedFrequency p c d w i
       then Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) else 0) := by
    have he : ((c i=d i ∧ ¬6∣c i ∧ p i∣dividedFrequency p c d w i) ∧ c i=1 ∧ d i=1) ↔
        (c i=d i ∧ c i=1 ∧ p i∣dividedFrequency p c d w i) := by
      constructor
      · rintro ⟨⟨hcd,h6,hn⟩,hc,hd⟩
        exact ⟨hcd,hc,hn⟩
      · rintro ⟨hcd,hc,hn⟩
        exact ⟨⟨hcd,by omega,hn⟩,hc,by omega⟩
    simp only [he]
  simp_rw [hf]
  rw [show (∑ i, (c i:ℝ)*Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ)) +
      (∑ i, (d i:ℝ)*Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ)) =
      ∑ i, ((c i:ℝ)+(d i:ℝ))*Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) by
      simp only [add_mul,Finset.sum_add_distrib]]
  simp only [Finset.mul_sum,Finset.sum_div]
  rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [localSaving,Nat.cast_min]
  split_ifs <;> ring

theorem actual_secondSaving_lower (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, Supported (Ideal.span {p i})) (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime p)) (c d : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i) (w : O) (Z : ℝ) (hZ : 1 < Z)
    (hne : actualCorrelation (∏ i, p i^c i) (∏ i, p i^d i)
      (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
      (supported_product _ (fun i => supported_power (p i) (hp i) (d i)))
      ((∏ i, p i^min (c i) (d i))*w) ≠ 0) :
    (Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^c i) : ℝ) +
      Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^d i) : ℝ))/3 ≤ secondSaving p c d w Z := by
  calc
    _ = ∑ i, Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ)*(((c i:ℝ)+d i)/3) := by
      rw [log_norm_power_product p hp c,log_norm_power_product p hp d,
        ← Finset.sum_add_distrib,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left
        (actual_localSaving_lower (p i) (hp i) (hg i) (hchar i) (c i) (d i) (hc i) (hd i)
          (dividedFrequency p c d w i) (local_nonzero_of_global p hp hcop c d w hne i))
      apply Real.logb_nonneg hZ
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)

end Global

end CenteredMomentSecondLedger

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
